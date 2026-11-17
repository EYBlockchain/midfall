import Lean
import Midfall.LoweringV2.Blocks.TraceReturn
import Midfall.Instances.PoseidonV2
import Midfall.Instances.PoseidonValid

set_option autoImplicit false

/-!
PROPOSED `Midfall/Tools/Done.lean` (scratch prototype, PLAN-V3 design area "done-tooling").

Style and conventions of `Midfall/Tools/ConeSorries.lean`: plain `elab` commands, verdicts as `info`
messages, violations as `error` messages (so `lake build` / `lake env lean` exit non-zero).

* `#assert_axioms thm [a₁, …] native [d₁, …]`   the axiom half of DONE as a build error.
* `#replay_native thm`                          re-evaluates every native axiom of `thm` (the only
                                                check that is not name-based; expensive).
* `#cone_report root`                           the progress report: per-leaf status of every sorried
                                                declaration of the cone (OPEN / REFUTED / VACUOUS),
                                                and the axioms of the root, classified.
* `#assert_no_refuted_sorry Prefix`             error if a sorried declaration of the tree has a proved
                                                negation in the tree (J-4).
* `#sorry_sweep Prefix`                         the environment scan: every declaration of the project
                                                whose own type or value uses `sorryAx`, by NAME.
* `#axiom_sweep Prefix`                         every `axiom` constant of the project, classified, and
                                                every `extern` / `implemented_by` / `unsafe` constant.
* `#closure_fingerprint [r₁, …] under [P₁, …]`  the statement-closure fingerprint (J-6).
* `#cone_avoids_decls root [c₁, …]`             error if the cone of `root` uses any listed constant.
-/

namespace Midfall.Tools.Done
open Lean Elab Command Meta

/-! ## 0. Shared helpers -/

def resolve (id : TSyntax `ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

def sortNames (xs : Array Name) : Array Name := xs.qsort (fun a b => toString a < toString b)

def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

/-- Is `n` declared in a module whose name starts with one of `prefixes`? Declarations of the file
    being elaborated count as project declarations. -/
def inProject (env : Environment) (prefixes : Array Name) (n : Name) : Bool :=
  match moduleOf? env n with
  | none => true
  | some m => prefixes.any fun p => p.isPrefixOf m

/-- Every constant declared in a project module (plus those of the file being elaborated), read
    from the per-module name tables: the sweeps never walk the 600k constants of mathlib. -/
def projectConstants (env : Environment) (prefixes : Array Name) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let names := env.header.moduleNames
  for i in [0:names.size] do
    if prefixes.any fun p => p.isPrefixOf names[i]! then
      if let some md := env.header.moduleData[i]? then
        out := out ++ md.constNames
  return env.constants.foldStage2 (fun acc n _ => acc.push n) out

/-- The constants a declaration's own type and value mention. -/
def usedBy (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]

def usesSorryDirectly (ci : ConstantInfo) : Bool := (usedBy ci).contains ``sorryAx

/-- The user-facing declaration an auxiliary constant belongs to: strip trailing internal
    components (`_proof_3`, `match_1`, `_native.native_decide.ax_1_1`, `eq_1`, …) and the private
    prefix. `foo._proof_2` and `foo` are one register row. -/
partial def userDecl (env : Environment) (n : Name) : Name :=
  let rec go (m : Name) : Name :=
    match m with
    | .str p s =>
      if (s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
          s.startsWith "eq_" || s.startsWith "ax_" || s == "native_decide" ||
          s.startsWith "omega_") && !p.isAnonymous && env.contains p then go p
      else if (s.startsWith "_" || s.startsWith "ax_" || s == "native_decide") &&
          !p.isAnonymous then go p
      else m
    | .num p _ => if p.isAnonymous then m else go p
    | .anonymous => m
  (privateToUserName? (go n)).getD (go n)

/-! ## 1. `#assert_axioms` — the axiom half of DONE as a build error -/

/-- `owner._native.<tactic>.ax_*` ↦ `(owner, tactic)`: the name `Lean.Meta.nativeEqTrue` generates
    (toolchain `Lean/Meta/Native.lean:75`, `mkAuxDeclName (`_native ++ tacticName ++ `ax)`). -/
def nativeAxiomOwner? : Name → Option (Name × String)
  | .str (.str (.str owner "_native") tac) ax =>
      if ax.startsWith "ax_" then some (owner, tac) else none
  | _ => none

/-- The only statement a native axiom may make: `(e : Bool) = true` with `e` closed. A forged
    `axiom X._native.native_decide.ax_1_1 : False` fails here. -/
def isNativeShape (ty : Expr) : Bool :=
  match ty.eq? with
  | some (α, e, rhs) =>
      α.isConstOf ``Bool && rhs.isConstOf ``Bool.true && !e.hasFVar && !e.hasMVar &&
        !e.hasLooseBVars
  | none => false

inductive AxVerdict where
  | named
  | generated (owner : Name)
  | bad (why : String)

/-- Was `ax` generated INSIDE `owner`? `nativeEqTrue` records the tactic's own syntax range as the
    axiom's declaration range, so a generated axiom's range lies inside its owner's range and its
    selection range is the same range. A hand-written `axiom` command cannot sit inside another
    declaration. Measured at this commit: `poseidonModel_isOk` 96:0-101:74, its axiom 101:61-101:74. -/
def generatedInside (owner ax : Name) : CoreM Bool := do
  let some ro ← findDeclarationRanges? owner | return false
  let some ra ← findDeclarationRanges? ax | return false
  let le (a b : Position) : Bool := a.line < b.line || (a.line == b.line && a.column ≤ b.column)
  return le ro.range.pos ra.range.pos && le ra.range.endPos ro.range.endPos &&
    ra.range.pos == ra.selectionRange.pos && ra.range.endPos == ra.selectionRange.endPos &&
    !(ro.range.pos == ra.range.pos && ro.range.endPos == ra.range.endPos)

/-- The structural test for a native axiom, shared by `#assert_axioms` and `#axiom_sweep`: the
    owner exists and is not an axiom, owner and axiom share a module, the statement is
    `closed Bool = true`, and the axiom was generated inside the owner. `none` means well-formed. -/
def nativeDefect? (owner ax : Name) : CoreM (Option String) := do
  let env ← getEnv
  match env.find? owner, env.find? ax with
  | some oci, some aci =>
      if oci matches .axiomInfo _ then return some s!"owner `{owner}` is itself an axiom"
      if moduleOf? env owner != moduleOf? env ax then
        return some s!"declared in a different module than its owner `{owner}`"
      if !isNativeShape aci.type then
        return some "has the generated NAME but not the generated STATEMENT (closed Bool = true)"
      if !(← generatedInside owner ax) then
        return some s!"was not generated inside `{owner}` (a hand-written `axiom` with a generated name)"
      return none
  | _, _ => return some s!"owner `{owner}` is not a declaration"

/-- Classify one axiom against the two allow-lists. -/
def classifyAxiom (allowed nativeOwners : Array Name) (ax : Name) : CoreM AxVerdict := do
  if allowed.contains ax then return .named
  match nativeAxiomOwner? ax with
  | none =>
      if ax == ``sorryAx then return .bad "an unproved obligation is in the cone"
      else return .bad "not in the allow-list"
  | some (owner, tac) =>
      if tac != "native_decide" then
        return .bad s!"generated by `{tac}`, only native_decide is allowed"
      if !nativeOwners.contains owner then
        return .bad s!"native_decide axiom of `{owner}`, which is not in the native list"
      match ← nativeDefect? owner ax with
      | some why => return .bad why
      | none => return .generated owner

/-- The check behind `#assert_axioms`. -/
def assertAxioms (id : TSyntax `ident) (axs ds : Array (TSyntax `ident)) : CommandElabM Unit := do
  let n ← resolve id
  let env ← getEnv
  let allowed ← axs.mapM resolve
  let owners ← ds.mapM resolve
  for a in allowed do
    unless (env.find? a matches some (.axiomInfo _)) do
      throwError "assert_axioms {n}: `{a}` is in the allow-list but is not an axiom"
  let used ← liftCoreM <| collectAxioms n
  let mut bad : Array String := #[]
  let mut named : Array Name := #[]
  let mut gen : Array Name := #[]
  let mut ownersUsed : Array Name := #[]
  for a in used do
    match ← liftCoreM <| classifyAxiom allowed owners a with
    | .named => named := named.push a
    | .generated o => gen := gen.push a; ownersUsed := ownersUsed.push o
    | .bad why => bad := bad.push s!"  {a}: {why}"
  let unusedNamed := allowed.filter fun a => !named.contains a
  let unusedOwners := owners.filter fun o => !ownersUsed.contains o
  if bad.isEmpty then
    let note := if unusedNamed.isEmpty && unusedOwners.isEmpty then "" else
      s!"\n  unused allowances: {unusedNamed ++ unusedOwners}"
    logInfo m!"assert_axioms {n}: ok ({named.size} named, {gen.size} native){note}"
  else
    logError m!"assert_axioms {n}: {bad.size} axiom(s) outside the allow-list\n{"\n".intercalate bad.toList}"

/-- `#assert_axioms thm [a₁, …]` or `#assert_axioms thm [a₁, …] native [d₁, …]`.
    ERROR unless every axiom `thm` depends on is one of the `aᵢ`, or a `native_decide` axiom
    generated inside one of the `dⱼ`. Unused allowances are reported (info), so the list cannot rot. -/
elab "#assert_axioms " id:ident " [" axs:ident,* "]" : command =>
  assertAxioms id axs.getElems #[]

@[inherit_doc Midfall.Tools.Done.assertAxioms]
elab "#assert_axioms " id:ident " [" axs:ident,* "]" &" native " "[" ds:ident,* "]" : command =>
  assertAxioms id axs.getElems ds.getElems

/-- `#replay_native thm`: for every axiom of `thm` with the generated native shape, compile and
    evaluate its Bool again (exactly what `native_decide` did) and ERROR if it is not `true`.
    This is the only check that does not trust a NAME. It costs what the original proofs cost. -/
elab "#replay_native " id:ident : command => do
  let n ← resolve id
  let env ← getEnv
  let used ← liftCoreM <| collectAxioms n
  let mut bad : Array String := #[]
  let mut ok : Nat := 0
  for a in used do
    if (nativeAxiomOwner? a).isNone then continue
    let some ci := env.find? a | continue
    unless isNativeShape ci.type && ci.levelParams.isEmpty do
      bad := bad.push s!"  {a}: not of the form `closed Bool = true`"
      continue
    let some (_, e, _) := ci.type.eq? | continue
    let r ← liftTermElabM <| withoutModifyingEnv <|
      (do
        match (← Lean.Meta.nativeEqTrue `native_decide e) with
        | .success _ => pure (some true)
        | .notTrue => pure (some false)) <|> pure none
    match r with
    | some true => ok := ok + 1
    | some false => bad := bad.push s!"  {a}: its Bool evaluates to FALSE (forged or stale)"
    | none => bad := bad.push s!"  {a}: could not be evaluated"
  if bad.isEmpty then logInfo m!"replay_native {n}: ok ({ok} native axiom(s) re-evaluated to true)"
  else logError m!"replay_native {n}: {bad.size} failure(s)\n{"\n".intercalate bad.toList}"

/-! ## 2. The cone, as `Lean.collectAxioms` walks it (constructors included: J-3) -/

structure Cone where
  all : Array Name := #[]
  sorries : Array Name := #[]
  axioms : Array Name := #[]

partial def coneGo (env : Environment) : List Name → NameSet → Cone → Cone
  | [], _, acc => acc
  | n :: rest, seen, acc =>
    if seen.contains n then coneGo env rest seen acc
    else
      let seen := seen.insert n
      match env.find? n with
      | none => coneGo env rest seen acc
      | some ci =>
        let used : Array Name := usedBy ci ++
          (match ci with | .inductInfo v => v.ctors.toArray | _ => #[])
        let acc := { acc with
          all := acc.all.push n
          sorries := if usesSorryDirectly ci then acc.sorries.push n else acc.sorries
          axioms := if ci matches .axiomInfo _ then acc.axioms.push n else acc.axioms }
        coneGo env (used.foldl (fun l c => if seen.contains c then l else c :: l) rest) seen acc

def cone (env : Environment) (root : Name) : Cone := coneGo env [root] {} {}

/-- `#cone_avoids_decls root [c₁, …]`: error if the cone of `root` uses any listed constant. The
    constant-level form of `#cone_avoids`; it is what "no artifact-derived part" needs (I-7). -/
elab "#cone_avoids_decls " id:ident " [" cs:ident,* "]" : command => do
  let n ← resolve id
  let avoid ← cs.getElems.mapM resolve
  let c := cone (← getEnv) n
  let hit := avoid.filter c.all.contains
  if hit.isEmpty then logInfo m!"cone_avoids_decls {n}: ok ({avoid.size} constants)"
  else logError m!"cone_avoids_decls {n}: uses {", ".intercalate (hit.toList.map toString)}"

/-! ## 3. Per-leaf status: OPEN / REFUTED / VACUOUS, registry-free -/

/-- A proved negation: `thm : ∀ ys, ¬ Q ys` (or `∀ ys, Q ys → False`) with no `sorryAx`. -/
structure Refuter where
  name : Name
  /-- number of leading binders BEFORE the negated proposition -/
  arity : Nat
  /-- head constant of the negated proposition (a cheap pre-filter); `none` when the negated
      proposition is itself a `∀` (the `¬ type_of% @leaf` form) -/
  head : Option Name

/-- Peel `∀`s syntactically: binder types (innermost last) and the body. -/
def peel : Expr → Array Expr → Array Expr × Expr
  | .forallE _ d b _, acc => peel b (acc.push d)
  | .mdata _ e, acc => peel e acc
  | e, acc => (acc, e)

def headConst? (e : Expr) : Option Name :=
  if e.isForall then none else e.getAppFn.constName?

/-- Recognise a negation theorem by the syntactic shape of its type. -/
def refuterOf? (n : Name) (ty : Expr) : Option Refuter :=
  let (ds, body) := peel ty #[]
  if body.isAppOfArity ``Not 1 then
    some { name := n, arity := ds.size, head := headConst? body.appArg! }
  else if body.isConstOf ``False && ds.size ≥ 1 then
    some { name := n, arity := ds.size - 1, head := headConst? ds.back! }
  else none

/-- Every sorry-free negation theorem of the project. -/
def refuters (prefixes : Array Name) : CoreM (Array Refuter) := do
  let env ← getEnv
  let mut out := #[]
  for n in projectConstants env prefixes do
    let some ci := env.find? n | continue
    unless ci matches .thmInfo _ do continue
    if userDecl env n != n then continue  -- an auxiliary lemma: its parent is the refuter
    let some r := refuterOf? n ci.type | continue
    if (← collectAxioms n).contains ``sorryAx then continue
    out := out.push r
  return out

/-- The proposition a refuter negates, with its `arity` leading binders as fresh metavariables. -/
def negatedProp (r : Refuter) : MetaM Expr := do
  let ci ← getConstInfo r.name
  let lvls ← mkFreshLevelMVarsFor ci
  let ty := ci.type.instantiateLevelParams ci.levelParams lvls
  let (_, _, body) ← forallMetaBoundedTelescope ty r.arity
  let body ← whnfR body
  if body.isAppOfArity ``Not 1 then return body.appArg!
  match body with
  | .forallE _ d _ _ => return d
  | _ => throwError "negatedProp: unexpected shape for {r.name}"

inductive LeafStatus where
  | open_
  | refuted (by_ : Name)
  | vacuous (by_ : Name) (hyp : Nat)

/-- Does `r` negate `prop`? One-sided: the refuter's binders are the unknowns. -/
def negates (r : Refuter) (prop : Expr) : MetaM Bool :=
  withoutModifyingState do
    try withReducible <| isDefEq (← negatedProp r) prop catch _ => pure false

/-- REFUTED, form 1: a proved theorem negates the leaf's WHOLE statement (`¬ type_of% @leaf`).
    REFUTED, form 2: the leaf has no hypothesis, and a proved theorem negates its conclusion at
    some instance of its data binders, every one of which the match determines.
    VACUOUS: some hypothesis of the leaf is negated by a proved theorem for EVERY value of the
    leaf's binders (the refuter's binders are the only unknowns), so the leaf is true ex falso. -/
def leafStatus (rs : Array Refuter) (leaf : Name) : MetaM LeafStatus := do
  let ci ← getConstInfo leaf
  let ty := ci.type.instantiateLevelParams ci.levelParams (← mkFreshLevelMVarsFor ci)
  -- REFUTED, form 1
  for r in rs do
    if r.head.isNone && ty.isForall then
      if ← negates r ty then return .refuted r.name
    if !ty.isForall && r.head == headConst? ty then
      if ← negates r ty then return .refuted r.name
  -- REFUTED, form 2
  let refuted? ← withoutModifyingState do
    let (xs, _, concl) ← forallMetaTelescope ty
    if xs.isEmpty then return none
    if ← xs.anyM fun x => do isProp (← inferType x) then return none
    let some h := headConst? concl | return none
    for r in rs do
      if r.head != some h then continue
      let ok ← withoutModifyingState do
        try
          if ← withReducible <| isDefEq (← negatedProp r) concl then
            xs.allM fun x => do return !(← instantiateMVars x).isMVar
          else pure false
        catch _ => pure false
      if ok then return some r.name
    return none
  if let some r := refuted? then return .refuted r
  -- VACUOUS
  let vac? ← forallTelescope ty fun xs _ => do
    let mut i : Nat := 0
    for x in xs do
      let hx ← inferType x
      if ← isProp hx then
        for r in rs do
          if r.head != headConst? hx then continue
          if ← negates r hx then return some (r.name, i)
      i := i + 1
    return none
  match vac? with
  | some (r, i) => return .vacuous r i
  | none => return .open_

def statusLine (leaf : Name) : LeafStatus → String
  | .open_ => s!"  OPEN     {leaf}"
  | .refuted r => s!"  REFUTED  {leaf}   (negation proved: {r})"
  | .vacuous r i => s!"  VACUOUS  {leaf}   (hypothesis #{i} is refuted for every instance by {r})"

/-- `#cone_report root under [P₁, …]`: THE PROGRESS REPORT.
    Line 1: the sorried leaves of the cone by status. Then one line per leaf. Then the axioms of
    the root, classified. A REFUTED leaf makes the count meaningless, and the report says so. -/
elab "#cone_report " id:ident &" under " "[" ps:ident,* "]" : command => do
  let n ← resolve id
  let env ← getEnv
  let prefixes := ps.getElems.map (·.getId)
  let c := cone env n
  let leaves := sortNames c.sorries
  let rs ← liftCoreM <| refuters prefixes
  let mut lines : Array String := #[]
  let mut nOpen : Nat := 0
  let mut nRef : Nat := 0
  let mut nVac : Nat := 0
  for l in leaves do
    let st ← liftTermElabM <| leafStatus rs l
    match st with
    | .open_ => nOpen := nOpen + 1
    | .refuted _ => nRef := nRef + 1
    | .vacuous _ _ => nVac := nVac + 1
    lines := lines.push (statusLine l st)
  let rootNote ← do
    match (← liftTermElabM <| leafStatus rs n) with
    | .vacuous r i => pure s!"\n  ROOT IS VACUOUS: hypothesis #{i} of {n} is refuted for every instance by {r}"
    | .refuted r => pure s!"\n  ROOT IS REFUTED by {r}"
    | .open_ => pure ""
  let axs ← liftCoreM <| collectAxioms n
  let gens := axs.filter fun a => (nativeAxiomOwner? a).isSome
  let other := axs.filter fun a => (nativeAxiomOwner? a).isNone
  let verdict :=
    if nRef > 0 then "UNREACHABLE (a leaf is refuted: False is derivable, the count is not a distance)"
    else if leaves.isEmpty then "CLOSED" else "OPEN"
  logInfo m!"cone_report {n}: {leaves.size} sorried leaves = {nOpen} OPEN + {nRef} REFUTED + {nVac} VACUOUS  [{verdict}]{rootNote}\n{"\n".intercalate lines.toList}\n  axioms: {other.toList}\n  native axioms: {gens.size} {gens.toList}"

/-- `#assert_no_refuted_sorry [P₁, …]`: ERROR if any declaration of the project that uses `sorryAx`
    directly has a proved negation in the project (J-4: such a sorry proves `False`). -/
elab "#assert_no_refuted_sorry " "[" ps:ident,* "]" : command => do
  let env ← getEnv
  let prefixes := ps.getElems.map (·.getId)
  let rs ← liftCoreM <| refuters prefixes
  let mut hits : Array String := #[]
  let mut scanned : Nat := 0
  for n in projectConstants env prefixes do
    let some ci := env.find? n | continue
    unless usesSorryDirectly ci do continue
    unless ci matches .thmInfo _ do continue
    scanned := scanned + 1
    match (← liftTermElabM <| leafStatus rs n) with
    | .refuted r => hits := hits.push s!"  {n} is refuted by {r}"
    | _ => pure ()
  if hits.isEmpty then
    logInfo m!"assert_no_refuted_sorry: ok ({scanned} sorried theorems, {rs.size} proved negations scanned)"
  else
    logError m!"assert_no_refuted_sorry: {hits.size} registered sorry statement(s) are provably false\n{"\n".intercalate hits.toList}"

/-- `#leaf_status decl under [P₁, …]`: the status of one declaration, sorried or not. -/
elab "#leaf_status " id:ident &" under " "[" ps:ident,* "]" : command => do
  let n ← resolve id
  let rs ← liftCoreM <| refuters (ps.getElems.map (·.getId))
  logInfo m!"{(statusLine n (← liftTermElabM <| leafStatus rs n)).trimAscii}"

/-! ## 3b. Block coverage: which blocks have a contract, and of what quality -/

/-- `#block_coverage Row Partial at R under [P₁, …]`: for each constructor `q` of `Partial`, the
    best theorem of the project whose conclusion is `Row _ _ q`:
    * INTEGRATED    no `sorryAx`, no hypothesis beyond the row's own binders, and stated for every
                    render or for `R`: the block is covered AT THE DEPLOYMENT;
    * CONDITIONAL   no `sorryAx`, but it carries hypotheses the deployment has not discharged;
    * SORRY         a row is stated and its cone still contains `sorryAx`;
    * NONE          no row is stated. -/
elab "#block_coverage " row:ident ppSpace part:ident &" at " r:ident &" under " "[" ps:ident,* "]" : command => do
  let rowN ← resolve row
  let partN ← resolve part
  let rN ← resolve r
  let env ← getEnv
  let prefixes := ps.getElems.map (·.getId)
  let some (.inductInfo pi) := env.find? partN | throwError "{partN} is not an inductive type"
  let mut lines : Array String := #[]
  let mut counts : Array Nat := #[0, 0, 0, 0]
  for q in pi.ctors do
    -- rank: 3 INTEGRATED, 2 CONDITIONAL, 1 SORRY, 0 NONE
    let mut best : Nat := 0
    let mut bestBy : String := ""
    for n in projectConstants env prefixes do
      let some ci := env.find? n | continue
      unless ci matches .thmInfo _ do continue
      let (ds, body) := peel ci.type #[]
      unless body.getAppFn.isConstOf rowN do continue
      let args := body.getAppArgs
      unless args.any (·.isConstOf q) do continue
      let sorry_ := (← collectAxioms n).contains ``sorryAx
      -- hypotheses: binders whose type is not a plain type / instance; decided in MetaM
      let nHyps ← liftTermElabM <| forallTelescope ci.type fun xs _ => do
        let mut k : Nat := 0
        for x in xs do
          if ← isProp (← inferType x) then
            unless (← isClass? (← inferType x)).isSome do k := k + 1
        return k
      let atR := args.any (·.isConstOf rN)
      let generic := args.any fun a => a.isBVar
      let rank : Nat :=
        if sorry_ then 1 else if nHyps == 0 && (atR || generic) then 3 else 2
      if rank > best then
        best := rank
        bestBy := s!"{n}" ++ (if rank == 2 then s!" ({nHyps} undischarged hypothesis/es, {ds.size} binders)" else "")
    counts := counts.modify best (· + 1)
    let tag := #["NONE       ", "SORRY      ", "CONDITIONAL", "INTEGRATED "][best]!
    lines := lines.push s!"  {tag} {q}  {bestBy}"
  logInfo m!"block_coverage {rowN} at {rN}: {counts[3]!} INTEGRATED, {counts[2]!} CONDITIONAL, {counts[1]!} SORRY, {counts[0]!} NONE of {pi.ctors.length}\n{"\n".intercalate lines.toList}"

/-! ## 3c. A structural hash of statements and definitions -/

/-- A 64-bit structural hash of an expression: binder names and binder info are NOT hashed (alpha
    equivalence), constants are hashed by NAME, literals by value. Memoised on shared subterms. -/
partial def hashExpr (e : Expr) : StateM (Std.HashMap Expr UInt64) UInt64 := do
  if let some h := (← get)[e]? then return h
  let h ← match e with
    | .bvar i => pure (mixHash 11 (hash i))
    | .fvar f => pure (mixHash 13 (hash f.name))
    | .mvar m => pure (mixHash 17 (hash m.name))
    | .sort u => pure (mixHash 19 (hash u))
    | .const n us => pure (mixHash 23 (mixHash (hash n) (hash us)))
    | .app f a => do pure (mixHash 29 (mixHash (← hashExpr f) (← hashExpr a)))
    | .lam _ d b _ => do pure (mixHash 31 (mixHash (← hashExpr d) (← hashExpr b)))
    | .forallE _ d b _ => do pure (mixHash 37 (mixHash (← hashExpr d) (← hashExpr b)))
    | .letE _ t v b _ => do
        pure (mixHash 41 (mixHash (← hashExpr t) (mixHash (← hashExpr v) (← hashExpr b))))
    | .lit (.natVal n) => pure (mixHash 43 (hash n))
    | .lit (.strVal s) => pure (mixHash 47 (hash s))
    | .mdata _ b => hashExpr b
    | .proj s i b => do pure (mixHash 53 (mixHash (hash s) (mixHash (hash i) (← hashExpr b))))
  modify fun m => m.insert e h
  return h

def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-! ## 3d. Executable exhibits: present or missing (their VALUE is the KAT gate's business) -/

/-- `#exhibits [n₁, …]`: one line per named exhibit, `PRESENT` if a declaration of that name
    exists and `MISSING` otherwise. The names are the outcome-level KATs of EXECUTION section 4
    ("the fixture calldata runs the program to return(abiTrue)"); each is ALSO an
    `#eval … -- expect true` line that `kat_gate.py` evaluates. The report only refuses to be
    silent about an exhibit nobody has written. -/
elab "#exhibits " "[" ns:ident,* "]" : command => do
  let env ← getEnv
  let lines := ns.getElems.map fun i =>
    s!"  {if env.contains i.getId then "PRESENT" else "MISSING"}  {i.getId}"
  let missing := (ns.getElems.filter fun i => !env.contains i.getId).size
  logInfo m!"exhibits: {ns.getElems.size - missing} PRESENT, {missing} MISSING of {ns.getElems.size}\n{"\n".intercalate lines.toList}"

/-! ## 4. Environment sweeps (J-2, J-10, J-14) -/

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"
  | .defnInfo _ => if Lean.Meta.isInstanceCore env n then "instance" else "def"

/-- The body of `#sorry_sweep`. One row per user-facing declaration whose own type or value (or
    that of one of its auxiliary declarations) uses `sorryAx`:
    `SORRY <decl> <module> <kind> <OPEN|REFUTED|VACUOUS> <ROOT|-> <statement hash>`. -/
def sorrySweep (prefixes : Array Name) (root? : Option Name) : CommandElabM Unit := do
  let env ← getEnv
  let rs ← liftCoreM <| refuters prefixes
  let coneSet : NameSet := match root? with
    | some r => (cone env r).sorries.foldl (fun s n => s.insert (userDecl env n)) {}
    | none => {}
  let mut rows : Std.HashMap Name String := {}
  let mut transitive : Nat := 0
  let mut total : Nat := 0
  let mut nRef : Nat := 0
  let mut nRoot : Nat := 0
  for n in projectConstants env prefixes do
    let some ci := env.find? n | continue
    total := total + 1
    if (← collectAxioms n).contains ``sorryAx then transitive := transitive + 1
    unless usesSorryDirectly ci do continue
    let u := userDecl env n
    if rows.contains u then continue
    let uci := (env.find? u).getD ci
    let st : LeafStatus ← liftTermElabM (leafStatus rs u)
    let tag := match st with
      | .open_ => "OPEN" | .refuted _ => "REFUTED" | .vacuous _ _ => "VACUOUS"
    if st matches .refuted _ then nRef := nRef + 1
    let inRoot := coneSet.contains u
    if inRoot then nRoot := nRoot + 1
    let (h, _) := (hashExpr uci.type).run {}
    rows := rows.insert u
      s!"SORRY {u} {(moduleOf? env n).getD `current} {kindOf env u uci} {tag} {if inRoot then "ROOT" else "-"} {hex h}"
  let lines := (sortNames (rows.toArray.map (·.1))).map fun u => rows.getD u ""
  let rootNote := match root? with
    | some r => s!"; {nRoot} in the cone of {r}"
    | none => ""
  logInfo m!"sorry_sweep: {lines.size} declarations use sorryAx directly ({nRef} REFUTED){rootNote}; {transitive} of {total} project constants depend on it\n{"\n".intercalate lines.toList}"

/-- `#sorry_sweep [P₁, …]` / `#sorry_sweep [P₁, …] root thm`: THE ENVIRONMENT SCAN. It reads the
    elaborated terms, so it sees `sorry`, `admit`, `stop`, a direct `sorryAx`, and any macro that
    expands to one; the register is keyed by the names it prints, not by file:line. -/
elab "#sorry_sweep " "[" ps:ident,* "]" : command =>
  sorrySweep (ps.getElems.map (·.getId)) none

@[inherit_doc Midfall.Tools.Done.sorrySweep]
elab "#sorry_sweep " "[" ps:ident,* "]" &" root " id:ident : command => do
  sorrySweep (ps.getElems.map (·.getId)) (some (← resolve id))

/-- `#axiom_sweep [P₁, …] allow [a₁, …] nativeModules [M₁, …]`: every `axiom` constant of the
    project. ERROR if one is neither in `allow` nor a well-formed native axiom whose module name
    starts with one of the `Mᵢ`. Also lists the constants native evaluation trusts beyond the
    compiler: `@[extern]`, `@[implemented_by]`, `unsafe`. -/
elab "#axiom_sweep " "[" ps:ident,* "]" &" allow " "[" axs:ident,* "]" &" nativeModules " "[" ms:ident,* "]" : command => do
  let env ← getEnv
  let prefixes := ps.getElems.map (·.getId)
  let allowed ← axs.getElems.mapM resolve
  let mods := ms.getElems.map (·.getId)
  let mut named : Array Name := #[]
  let mut gen : Nat := 0
  let mut bad : Array String := #[]
  let mut trusted : Array String := #[]
  for n in projectConstants env prefixes do
    let some ci := env.find? n | continue
    if ci matches .opaqueInfo _ then trusted := trusted.push s!"  opaque          {n}"
    if (Lean.isExtern env n) then trusted := trusted.push s!"  extern          {n}"
    if (Lean.Compiler.getImplementedBy? env n).isSome then
      trusted := trusted.push s!"  implemented_by  {n}"
    if ci.isUnsafe then trusted := trusted.push s!"  unsafe          {n}"
    unless ci matches .axiomInfo _ do continue
    if allowed.contains n then named := named.push n
    else match nativeAxiomOwner? n with
      | some (owner, "native_decide") =>
          let m := (moduleOf? env n).getD .anonymous
          if !(mods.any fun p => p.isPrefixOf m) then
            bad := bad.push s!"  {n}: native_decide outside the allowed modules (in {m})"
          else match ← liftCoreM <| nativeDefect? owner n with
            | some why => bad := bad.push s!"  {n}: {why}"
            | none => gen := gen + 1
      | _ => bad := bad.push s!"  {n}: an axiom outside the allow-list"
  let tl := "\n".intercalate (trusted.qsort (· < ·)).toList
  if bad.isEmpty then
    logInfo m!"axiom_sweep: ok ({named.size} named axioms {sortNames named}, {gen} native_decide axioms)\nopaque / extern / implemented_by / unsafe constants of the project ({trusted.size}):\n{tl}"
  else
    logError m!"axiom_sweep: {bad.size} axiom(s) outside the allow-list\n{"\n".intercalate (bad.qsort (· < ·)).toList}"

/-! ## 5. Statement-closure fingerprint (J-6) -/

/-- The MEANING closure of a set of roots: what a statement says depends on the TYPE of every
    constant it reaches, and on the VALUE of every non-theorem (definitions, instances, matchers,
    structure projections) and on the constructors of every inductive. A theorem's PROOF is not
    part of any statement's meaning, so theorems contribute their type only. Constants outside the
    project are leaves (pinned by `lake-manifest.json` and `lean-toolchain`). -/
partial def closureGo (env : Environment) (prefixes : Array Name) :
    List Name → NameSet → Array Name → Nat → Array Name × Nat
  | [], _, acc, ext => (acc, ext)
  | n :: rest, seen, acc, ext =>
    if seen.contains n then closureGo env prefixes rest seen acc ext
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closureGo env prefixes rest seen acc ext
      | some ci =>
        if !inProject env prefixes n then closureGo env prefixes rest seen acc (ext + 1)
        else
          let used : Array Name := ci.type.getUsedConstants ++
            (match ci with
              | .thmInfo _ => #[]
              | .inductInfo v => v.ctors.toArray
              | _ => ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])
          closureGo env prefixes
            (used.foldl (fun l c => if seen.contains c then l else c :: l) rest) seen (acc.push n) ext

/-- `#closure_fingerprint [r₁, …] under [P₁, …]` prints
    `closure_fingerprint: N project declarations, E external leaves, digest D`, then one line
    `DECL <module> <name> <kind> <type hash> <value hash>` per declaration, sorted by module. The
    lines, filtered by module prefix and hashed with sha256sum, are the pin: any edit to any
    definition a frozen statement reaches changes a line, and the diff NAMES the definition. -/
elab "#closure_fingerprint " "[" rs:ident,* "]" &" under " "[" ps:ident,* "]" : command => do
  let env ← getEnv
  let roots ← rs.getElems.mapM resolve
  let prefixes := ps.getElems.map (·.getId)
  let (decls, ext) := closureGo env prefixes roots.toList {} #[] 0
  let decls := sortNames decls
  let mut cache : Std.HashMap Expr UInt64 := {}
  let mut lines : Array String := #[]
  let mut digest : UInt64 := 7
  for n in decls do
    let some ci := env.find? n | continue
    let (ht, c1) := (hashExpr ci.type).run cache
    cache := c1
    let hv ← match ci with
      | .thmInfo _ => pure (0 : UInt64)
      | _ => match ci.value? (allowOpaque := true) with
        | some v => do
            let (h, c2) := (hashExpr v).run cache
            cache := c2
            pure h
        | none => pure (0 : UInt64)
    digest := mixHash digest (mixHash (hash n) (mixHash ht hv))
    lines := lines.push s!"DECL {(moduleOf? env n).getD `current} {n} {kindOf env n ci} {hex ht} {hex hv}"
  lines := lines.qsort (· < ·)
  logInfo m!"closure_fingerprint {roots.toList}: {decls.size} project declarations, {ext} external leaves, digest {hex digest}\n{"\n".intercalate lines.toList}"

end Midfall.Tools.Done

open Midfall.Tools.Done

/-! ### (a) PASS: a proved block contract on the three standard axioms. -/
/-- info: assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound: ok (3 named, 0 native) -/
#guard_msgs in
#assert_axioms Midfall.LoweringV2.Blocks.TraceReturn.tr_blockSound [propext, Classical.choice, Quot.sound]

/-! ### (b) FAIL: the headline, with the full PLAN-V2 section 6 allow-list. The only offender is sorryAx. -/
/--
error: assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: 1 axiom(s) outside the allow-list
  sorryAx: an unproved obligation is in the cone
-/
#guard_msgs in
#assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon
  [propext, Classical.choice, Quot.sound, Midfall.Assumptions.blsGT, Midfall.Assumptions.blsGT_group,
   Midfall.Assumptions.blsGT_primeOrder, Midfall.Assumptions.blsGT_module,
   Midfall.Assumptions.bls12_381Pairing]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]

/-! ### (c) A native axiom is rejected unless its owner is listed; accepted when it is. -/
/--
error: assert_axioms Midfall.Instances.PoseidonV2.poseidonModel_isOk: 1 axiom(s) outside the allow-list
  Midfall.Instances.PoseidonV2.poseidonModel_isOk._native.native_decide.ax_1_1: native_decide axiom of `Midfall.Instances.PoseidonV2.poseidonModel_isOk`, which is not in the native list
-/
#guard_msgs in
#assert_axioms Midfall.Instances.PoseidonV2.poseidonModel_isOk [propext, Classical.choice, Quot.sound]

#assert_axioms Midfall.Instances.PoseidonV2.poseidonModel_isOk [propext, Classical.choice, Quot.sound]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]

/-! ### (d) J-1's counterexample: a user axiom in place of the sorry. Every script is green; this is red. -/
axiom poseidon_valid_ax : Midfall.Instances.PoseidonV2.poseidonRender.Valid
theorem uses_user_axiom : Midfall.Instances.PoseidonV2.poseidonRender.Valid := poseidon_valid_ax
/--
error: assert_axioms uses_user_axiom: 1 axiom(s) outside the allow-list
  poseidon_valid_ax: not in the allow-list
-/
#guard_msgs in
#assert_axioms uses_user_axiom
  [propext, Classical.choice, Quot.sound, Midfall.Assumptions.blsGT, Midfall.Assumptions.blsGT_group,
   Midfall.Assumptions.blsGT_primeOrder, Midfall.Assumptions.blsGT_module,
   Midfall.Assumptions.bls12_381Pairing]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]

/-! ### (e) J-14's counterexample: a hand-written axiom with a generated NAME. -/
axiom Forged._native.native_decide.ax_1_1 : False
theorem Forged : False := Forged._native.native_decide.ax_1_1
/--
error: assert_axioms Forged: 1 axiom(s) outside the allow-list
  Forged._native.native_decide.ax_1_1: has the generated NAME but not the generated STATEMENT (closed Bool = true)
-/
#guard_msgs in
#assert_axioms Forged [] native [Forged]

/-! ### (f) the same with the generated STATEMENT shape too: caught by the declaration-range test,
    and independently by the replay. -/
axiom Forged2._native.native_decide.ax_1_1 : decide (1 = 2) = true
theorem Forged2 : False := by have := Forged2._native.native_decide.ax_1_1; simp at this
/--
error: assert_axioms Forged2: 1 axiom(s) outside the allow-list
  Forged2._native.native_decide.ax_1_1: was not generated inside `Forged2` (a hand-written `axiom` with a generated name)
-/
#guard_msgs in
#assert_axioms Forged2 [propext] native [Forged2]

/--
error: replay_native Forged2: 1 failure(s)
  Forged2._native.native_decide.ax_1_1: its Bool evaluates to FALSE (forged or stale)
-/
#guard_msgs in
#replay_native Forged2

/-! ### (g) an honest native_decide: accepted by both. -/
theorem Honest : 2 ^ 10 = 1024 := by native_decide
/-- info: assert_axioms Honest: ok (1 named, 1 native) -/
#guard_msgs in
#assert_axioms Honest [propext] native [Honest]
/-- info: replay_native Honest: ok (1 native axiom(s) re-evaluated to true) -/
#guard_msgs in
#replay_native Honest

/-! ### (h) an allow-list entry that is not an axiom is an error (the list cannot rot by typo). -/
/-- error: assert_axioms Honest: `Honest` is in the allow-list but is not an axiom -/
#guard_msgs in
#assert_axioms Honest [Honest]

/-! ### (i) THE OPEN-PHASE GATE, as it would sit in ConeReport.lean today: `sorryAx` is allowed BY NAME,
    everything else is already pinned. DONE is the commit that deletes that one token (then (b) is the gate). -/
/-- info: assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon: ok (9 named, 1 native) -/
#guard_msgs in
#assert_axioms Midfall.Instances.PoseidonV2.lowering_equivalence_poseidon
  [propext, Classical.choice, Quot.sound, sorryAx, Midfall.Assumptions.blsGT,
   Midfall.Assumptions.blsGT_group, Midfall.Assumptions.blsGT_primeOrder,
   Midfall.Assumptions.blsGT_module, Midfall.Assumptions.bls12_381Pairing]
  native [Midfall.Instances.PoseidonV2.poseidonModel_isOk]
