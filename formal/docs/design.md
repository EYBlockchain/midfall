# Design decisions (signed off)

This file records decisions that change the *meaning* of the plan. Section 0 of
the plan requires sign-off for any such change; each entry names the approver
and the date.

## D-P1 - Abstract over the pairing instead of constructing BLS12-381

Approved by: Julian, 2026-10-23 (just use pairing from mathlib or arklib,
abstract over curve, as long as it admits pairing).

Why. The Phase 1 inventory (docs/ecosystem.md) establishes, with file:line
evidence, that none of ArkLib, VCVio, CompPoly or mathlib contains a BLS12-381
base field, Fp2, Fp12, G1, G2, GT or a pairing:

* CompPoly has only BLS12_381.ScalarField = ZMod r
  (CompPoly/Fields/BLS12_381/Basic.lean:25, primality by Pratt certificate)
  plus a Montgomery form BLS12_381.Fast.ScalarField.
* ArkLib has zero hits for bls; its only curve is an experimental BN254.
* mathlib (rev 56a0058..., 10790 paths) has no bls, no bn254, no miller, and
  no elliptic-curve Weil pairing.
* ArkLib KZG is already fully abstract:
  ArkLib/Commitments/Functional/KZG/Basic.lean:47-52 takes G1 G2 GT with
  [Group _], PrimeOrderWith _ p, Module (ZMod p) (Additive _) and a pairing
  *parameter*

      (pairing : (Additive G1) -[ZMod p]> (Additive G2) -[ZMod p]> (Additive GT))

  i.e. bilinearity is carried by the type (a curried LinearMap) and
  non-degeneracy is the hypothesis hpair : pairing g1 g2 != 0.

Decision. Midfall is formalised generically over an admissible pairing
(Midfall.PairingData, in Midfall/Common/Curve.lean), shaped so that ArkLib
KZG theorems apply to it unchanged. Section 9.1 of the plan becomes: instead
of abbrev Fr := BLS12_381.ScalarField etc., every statement is universally
quantified over an admissible pairing, and the BLS12-381 instantiation is a
named hypothesis in Assumptions/Pairing.lean.

Consequences, all deliberate:

1. The theorems are *more* general than Section 9: they hold for every
   admissible pairing, BLS12-381 being one candidate instance.
2. Nothing in the security proof depends on BLS12-381 concrete arithmetic. The
   concrete curve only enters the execution layer (Halo2/Exec) and the
   EIP-2537 / modexp external-call relations, where it is validated
   differentially against revm (Phase 3/5). That is where the trust that this
   really is BLS12-381 lives, and it is validated rather than proven - exactly
   as the plan already prescribes for the Rust port.
3. To keep the abstraction non-vacuous we exhibit at least one *constructed*
   model of Midfall.PairingData inside Lean (a small model built from mathlib
   primitives), so Assumptions/Pairing.lean stays the only place a
   curve-specific hypothesis is ever discharged.

Not changed by this decision. The mathematical content of the statements - the
group law used by G1ADD having no subgroup check, the frOfDigest reduction,
the DualMSM pairing orientation, the alpha-batching preimage - is unchanged.
Only the presentation moves from a named curve to a class.

## D-P2 - yul-semantics is vendored, not git-required

The plan asks for a pinned fork of powdr-labs/yul-semantics. We cannot push a
fork from here, so formal/vendor/yul-semantics is a byte copy of upstream rev
c9914c13df47efe026376723acd632bc33bc16e3 with exactly the three changes listed
in vendor/yul-semantics/lakefile.toml (toolchain bump to v4.35.0, Batteries
lint driver and placeholder exe dropped, warningAsError off). Library sources
are untouched. All Midfall-specific Yul work lives in Midfall/Yul/ and stays
upstreamable.

## D-P3 - ArkLib URL

The plan names ArkLib generically; the authoritative home is
https://github.com/Verified-zkEVM/ArkLib (arkworks-rs/ArkLib is a 404).
Pinned rev d023c5d31d7611ad772588b2da3286a7f3f0628b (Lean v4.35.0).

## D-P4 - what the ecosystem does not give us (planning impact)

| plan item | reality | our response |
|---|---|---|
| ArkLib AGM | AGM.Adversary.run is sorry (ArkLib/AGM/Basic.lean:189), no AGM theorem | write Security/AGM.lean ourselves (the plan already allows this) |
| ArkLib Fiat-Shamir | only fiatShamir_completeness, and it is sorry; no soundness theorem | our own Security/FiatShamir.lean (S4) specialised to the Keccak chain |
| ArkLib rbrKnowledgeSoundness | exists (Security/RoundByRound.lean:457) but the glue theorems (knowledgeSoundness_implies_soundness, rbrKnowledgeSoundness_implies_knowledgeSoundness, all liftContext_*, all append_*) are sorry | S2 must avoid the admitted glue: prove the rbrKS -> KS -> game steps we need, or state S2 in the rbrKS form only |
| ArkLib KZG function_binding | proved, sorry-free, from ARSDH | use it for S3 (alternative instantiation) |
| VCVio probability notation | the notation is Pr{ do }[ ev ] over noncomputable prEvent | use it as-is in Security/Games.lean |
| VCVio keccak256 | executable pure-Lean Keccak-f[1600] (VCVio/Algorithms/Keccak.lean:127), never wired to an OracleSpec | wire it ourselves in Common/Keccak.lean plus known-answer tests |
| yul-semantics precompiles | none (no gas, no precompiles); keccak256 is an opaque env oracle; gas() is nondeterministic | Midfall/Yul/Externals.lean defines the ExternalCalls relation for EIP-2537/modexp, as the plan says |
| toolchain | ArkLib/VCVio/CompPoly/mathlib = v4.35.0, yul-semantics = v4.33.0 | v4.35.0 everywhere (D-P2) |

## D-P5 - fc42518 is an implied dependency of listed item 4

**Approved by:** Julian, 2026-10-23 ("use recommended choice for the question").

Listed curated item 4 (f1840bd) contains two halves. Its H-1 SRS tau binding
calls srs_tau_is_consistent(g_lagrange, ...), and g_lagrange only comes into
scope in generate_base_vk via fc42518 "Validate the SRS G1 base equals the
canonical generator" - a misc-fixes commit the plan does not enumerate. Listed
item 10 (ed9f455) then reuses the same Pippenger helper for the BUILD_ID SRS
fingerprint, so it is blocked on the same thing.

Decision: treat fc42518 as an implied prerequisite of item 4 and land it, then
4b, then 10, so all ten listed items complete. This adds a commit to the curation
list rather than changing any statement's meaning, which is why it needed
sign-off rather than being done silently.

Independent reason to want it: without fc42518 a params file whose SRS base is
c*G (c != 1) builds without error, and the generated verifier then computes the
-v*G term of the KZG combination from G while every proof and VK commitment is
over c*G - so the on-chain pairing check enforces a scaled statement that
differs from the reference Rust verifier, silently at build time. That is
exactly the class of gap the plan says to stop and report rather than paper over.

## D-P6 - the plan 9.1 point codecs become G1Codec fields, not sorry defs

**Approved by:** pending (self-approved as a presentation change forced by
D-P1; flag if you disagree). Date raised: 2026-10-23.

Why. Plan 9.1 writes four plain defs - `G1.ofCompressed?`, `E1.ofEip?`,
`G1.ofEip?`, `E1.toEip` - over a concrete BLS12-381. D-P1 established that no
Lean library has BLS12-381, so as plain defs they can only be `sorry`, and a
`sorry` *definition* is worse than a missing proof: it is an axiom-shaped hole
in the computational layer that every downstream `#print axioms` inherits, and
it makes `verifyNative` non-computable rather than merely unproven. The Phase 1
gap policy says a missing proof becomes a named hypothesis structure; the same
reasoning applied to a missing *computation* is rule R9, which the plan already
invites for traits: a family of functions becomes a structure of functions.

Decision. `Midfall/Common/Codec.lean` declares
`structure G1Codec (G₁ : Type)` with fields `ofCompressed?`, `toCompressed`,
`toEip`, `ofEip?`, and the transcript instantiates `Hashable` from it. The
concrete BLS12-381 codec is then one inhabitant of that structure, supplied
once in `Assumptions/Pairing.lean` together with the two round-trip properties
already stated there (`eipRoundtrip`, `compressedRoundtrip`). The three
`sorry` defs are deleted; the sorry register shrinks by three.

What is *not* changed. The distinction the plan draws between all-Fp-points
(`E1.ofEip?`, no subgroup check) and r-torsion (`G1.ofEip?`) is preserved:
`ofEip?` is documented as the subgroup-checked decode, which is the one the
transcript and the contract use, and L4 (plan 9.5) is still the statement that
every proof point reaches a subgroup-checking call. The byte layouts are
unchanged (48-byte compressed wire, 128-byte padded absorb, identity = 128
zero bytes). No statement in `Statements.lean` mentions these names, so the
frozen file is untouched.

Related, no sign-off needed: `IoErrorKind` gains `notFound`. Rust
`CircuitTranscript::assert_empty` fails with `ErrorKind::NotFound
(transcript/mod.rs:150-159), which is a different kind from the
`UnexpectedEof` a short read gives, and the plan maps
`Transcript(io::Error)` to `transcript (k : IoErrorKind)`. Dropping the
distinction would have merged two observable error classes.

## D-P7 - Gₜ is an outParam of AdmissiblePairing, and DualMSM carries it

**Approved by:** pending (an elaboration consequence of D-P1 and D-P6, not a
mathematical change). Date raised: 2026-10-23.

Found while porting msm.rs, and recorded because it will bite every later
declaration that touches the pairing:

1. The pairing target group Gₜ appears in no data-carrying type: `MSMKZG`
   holds scalars and G₁ points, `ParamsVerifierKZG G₁ G₂` holds G₂ points.
   So `DualMSM.check : Bool` - which the plan fixes - cannot determine Gₜ from
   its arguments, and type-class resolution refuses to even look for an
   `AdmissiblePairing G₁ G₂ ?Gₜ` while ?Gₜ (and the parent instances that
   depend on it) are metavariables.
2. Fix, part one: `DualMSM (F G₁ G₂ Gₜ : Type)` carries G₂ and Gₜ as phantom
   parameters. The Rust `DualMSM<E>` has no G₂ or Gₜ component, so these are
   purely presentational, but without them nothing downstream can name the
   pairing.
3. Fix, part two: `Gₜ : outParam Type*` in the class header. Even with the
   phantom parameter, a *use site* such as the frozen `Statements.lean`
   writes `verifyNative F params vk inst π` and must still invent a Gₜ. With
   Gₜ as an outParam the instance head is indexed on (G₁, G₂) alone, so
   resolution proceeds and the local `[P : AdmissiblePairing G₁ G₂ Gₜ]
   hypothesis pins it. Without the outParam the frozen file does not elaborate
   at all - which is how this was caught.
4. `AdmissiblePairing` also gained `decEqG₁` and `decEqGₜ` fields (see
   Common/Curve.lean): plan 9.2 types the checks as `Bool`, and over an
   abstract group the equation is a bare Prop. They are fields rather than
   `[DecidableEq _]` variables precisely so that no use site - including the
   frozen file - has to supply anything new.

Consequence for the statements: none. No declaration in `Statements.lean`
changed, its hash is unchanged, and the theorems still quantify over an
arbitrary admissible pairing (now one with decidable equality on G₁ and Gₜ,
which any concrete curve has).

## D-P9: re-pin the §9.2 interface with a bundled environment

**Status: adopted.** `Midfall/Statements.lean` is re-pinned and its SHA-256
updated. `VerifierEnv` bundles the G1 codec, scalar-field constants, permutation
delta, and runtime fewer-point-sets switch. `prepare` and `verifyNative` use this
record; `decodeRust` additionally takes the instance vector so the Solidity
single-proof evaluation schedule is determined; the message-level APIs receive
the environment and hash explicitly.

The re-pin removes the missing-arity blocker, but is **not** the conformance
harness by itself. `decodeRust` still needs the KZG leaf's internal reads exposed,
and `prepareMsgs` needs a hash-parameterised transcript to honour arbitrary `H`.
Those remain tracked implementation work. In particular, no claim is made that
actual Rust proofs can yet be fed through all four APIs.

## D-P10 (ADOPTED, round 8): Y-3 resolved by an internal open-dialect Run, not by upstreaming

**Decision.** Do not wait on powdr-labs/yul-semantics accepting a
dialect-parameterised `RunCommitted`. Define `Midfall.Yul.Bridge.Run` ourselves: a
committed-run predicate parameterised by the external-call relation and the keccak
oracle, with the functionality and determinism lemmas we actually need proved in
`Midfall/Yul/`. Upstream it later as a contribution once it is stable and named.

**Why.** An external review's constraint is the operative one: a generic
external-call relation is NOT automatically deterministic, so the run layer needs
explicit conditions that preserve determinism rather than a bare parameterisation.
That is a design task we own regardless of whose repo it lands in, and gating M4 on
an upstream acceptance puts a third-party review queue on our critical path. The
vendored fork already exists, so the cost is ours either way.

**Consequences.** (1) `lowering_equivalence` is stated over `Midfall.Yul.Bridge.Run`,
with `EVM.RunCommitted` used only inside the lemmas connecting it to the vendored
interpreter. (2) The determinism conditions become named fields of a hypothesis
structure in `Assumptions/`, per the gap policy, not an implicit assumption.
(3) Phase 5's generic shell/IR work can start now; only the concrete deployment
integration waits on Phase 6.

## D-P11 (ADOPTED, round 8): the instance model is flat-with-explicit-view

**Decision.** Keep plan 9.3's `inst : Array Fr` unchanged. The two instance columns
required by 9.5's `Supported.instShape` are expressed by a stated mapping, not a
type change: column `c` occupies the `n` entries starting at `c * n`, in column
order, so the supported shape is [committed column, public column] concatenated -
exactly what the deployment passes as public inputs. `instanceAt` implements the
mapping, `instLen` states the well-formedness condition, and `evalRow` and `cell`
both route through it.

**Why.** The plan's signature is normative, and the reviewer's diagnosis was that the
old code read column 0 for every query - a silent misread, not a type error. Widening
the type would churn the frozen statements and the spec for no gain; the defect was a
missing mapping, and that is what was added.

**Open, flagged rather than assumed.** Whether `format_instance` for a given relation
actually emits `[committed..., public...]` in that order is a fact about the Rust,
and it is what the poseidon replay is currently blocked on. If the order differs,
`instanceAt` must take the column layout as data. Owner: the exporter (D-P12).

## D-P12 (ADOPTED, round 8): M0 freezes what is reproducible; the exporter never touches proofs/src

**Decision, two parts.**

1. **Freeze now, scope honestly.** Tag `formal-baseline-v1` over the current commits
   with the committed fixtures and their SHA-256s, and record the Moonlight
   regeneration as an explicitly deferred item with a named blocker (the SRS asset
   and the pinned solc), rather than holding M0 open indefinitely. A freeze that
   waits for an unavailable asset is not a freeze, it is a stall, and every
   downstream phase is currently paying for it.

2. **`conformance-rs` is a NEW workspace member that depends on `proofs` and
   `zk_stdlib` and modifies neither.** This dissolves the conflict escalated earlier:
   the exporter needs data FROM the verifier, not edits TO it. A separate crate can
   call the public API and serialise whatever it needs, so no baseline bump is
   required and the frozen-hash discipline is untouched. The one exception is
   raw-digest recording at each squeeze: if `solidity_trace` cannot already emit it,
   that IS a change to `proofs/src`, so prefer deriving digests on the Lean side from
   a complete absorb stream instead.

**Consequence for the replay.** The poseidon blocker is the instance shape, which the
exporter can answer by dumping `nb_public_inputs` and `pi` directly from the harness
it already sits next to. That is cheaper than reverse-engineering `format_instance`
from fixture bytes, and it is the same code we need anyway.

## D-P2 amendment (round 8): the Yul AST is the vendored one, not a new one

**Rule.** `YulSemantics.Ast` is the AST of record for the whole project: `Literal`,
`Expr Op`, `Stmt Op`, `Block Op`, `Object Op`, `Data`, dialect-parameterised by
`Op : Type` with `YulSemantics.Dialect.EVM` supplying `EVM.Op` and `opName`.
`Midfall/Generator/**` emits those types. It does not define a parallel AST.

**Why this needed stating.** A Phase 6 package brief asked an agent to create
`Midfall/Generator/YulAst.lean`, and it did, before anyone noticed the conflict. The
plan already mandates reuse in two places: D-P2 (yul-semantics is vendored) and
Section 7, which says `ImportSolcIR.lean` imports solc IR "into the yul-semantics
AST". A second AST would fork the dialect silently and force every later proof -
`irCheck`, `ObsEquiv`, the per-partial contracts - to state a translation in both
directions, which is where drift and unsound coercions live.

**What is legitimately ours.** A byte-exact renderer, if one is needed. The vendored
`YulSemantics.PrettyPrint` is a semantic pretty-printer (4-space pad, its own spacing
and casing choices); the Rust renderer's bytes are determined by Jinja templates and
literal text, so they will probably not agree. The rule is to MEASURE FIRST: build the
AST for a real slice of the committed `Halo2Verifier.sol` via the `yul%` DSL, print
with the vendored printer, and diff against the committed bytes. Only a demonstrated
mismatch justifies `Midfall/Generator/Render.lean`, and it must operate on the
vendored types.

**Also note** `YulSemantics.Syntax` is an elaborator DSL (`yul% { ... }`), not a
runtime text parser, so it cannot parse a committed `.sol` at build time. Round-trip
gates must therefore take their expected bytes from the committed artifact and their
AST from hand-written `yul%` quotations - never from a printer feeding itself.

## D-P13 (ADOPTED, round 8): generator identity is structural, not textual

**Decision (user).** The generator port's equality criterion excludes formatting
**and comments**. The obligation is structural equality of Yul ASTs, decided by the
vendored `YulSemantics.Ast.stmtsBeq` / `exprBeq` / `casesBeq`, not byte equality of
rendered text.

**What this removes.** The comment/layout channel that Phase 6 package 1 had to
invent (`Line.text` alongside `Line.code`) is no longer part of the correctness
claim, because `Stmt Op` has no comment constructor and `Halo2Verifier.sol` carries
971 comment lines. The pasted committed-text oracle blocks become a source for
building expected ASTs, not an equality target. Four divergence findings the agent
had to document as blockers (hex literal casing, brace policy, empty braces, spread
formatting) are no longer blockers - they are formatting.

**What it aligns.** Plan Section 7 already requires `irCheck` to establish that the
embedded assembly blocks are **alpha-equivalent** to `L.headGuard` and `L.main`. So
M3's criterion and Phase 5's central relation become the same decidable structural
equality over one AST type. One relation, one proof obligation, and the generator
output feeds the semantics directly instead of through a text round-trip.

**What it costs, and the mitigation.** Byte equality was a blunt but very broad
tripwire: it would have caught any divergence at all, including ones that are
semantically irrelevant. Structural equality is precise but narrower, so the
conformance signal must be compensated elsewhere - widen semantic coverage instead:
more fixtures, the mutation corpus, and the revm differential (M4) which checks
behaviour rather than text.

**M11 is NOT weakened.** `deployed_equivalence` keeps its force because two of its
three conjuncts were already AST-level (`Supported`, `irCheck`), and the link from
the deployed artifact to its *bytecode* is established by the revm differential
(M4), not by text equality. What changes is that we no longer claim to reproduce the
deployed file's bytes - only its semantics, which is what the theorems need anyway.

**Still required: a canonical renderer.** Not for equality, but because solc takes
text. `render` must emit well-formed, compilable Yul for any AST the generator
produces; its formatting is now free. This keeps `render g o = (lower g o).map print
by construction` meaningful as a structural statement.
## D-P16 (ADOPTED, round 12): two AccumulatorEncoding types - which one 9.5 means

**Problem (P-06 finding F-5).** `Midfall/Halo2/Exec/Accumulator.lean:167-261` already
ported api.rs:35-188 as a deliberate working stand-in: it masks the api.rs:104 panic
behind a `max 1`, returns `Bool` from `validFor` instead of carrying the five-field
payload and three reason strings, returns `Option` with truncated `Nat` subtraction
where the reference wraps, and skips the length check in
`fullyCollapsedPublicInputWords`. P-06 landed the faithful port as
`Midfall.Generator.AccumulatorEncoding`. So the tree has two types for one Rust type,
and `Statements.lean` and `Lowering/Types.lean` see the **Exec** one while PLAN 9.5's
`Supported.acc` quantifies over `g.cfg.accumulator`, a **generator** field.

**Decision.**
1. PLAN 9.5's `Supported.acc`, `decodeAcc` and `encodeAccInstances` refer to the
   **Generator** type. It is the faithful port, and the field it construes is a generator
   config field. Any statement written against the Exec stand-in is about a different
   object and must be re-pointed.
2. The Exec copy stays, because the obvious fix is the wrong one: Exec is L0 and
   Generator imports Exec, so Exec cannot import the faithful type without inverting the
   layering.
3. **Owed obligation, named so it cannot be forgotten:** a lemma that the two agree on
   the domain the theorems quantify over - for every encoding the generator actually
   accepts, `validFor` (Bool) is true exactly when `validateForNumInstances` returns
   `ok`, and the word counts agree. Until that lemma exists, no §9.5 statement may be
   proved against the Exec type and cited as being about the deployment.
4. The Exec stand-in's masked panic is an **R-30-class defect in our own tree**, not just
   a simplification: where the reference aborts, it answers. Not on a reachable path
   today, but the same shape as the bug R-30 recorded. Fix it when the reconciliation
   lemma is done.

**Owner:** the orchestrator, before `Spec.accepts` or any §9.5 accumulator statement is
written. Recorded here because P-06 was the package meant to unblock exactly this
question, and it correctly refused to pick silently.

## D-P17 (ADOPTED, round 14): a port file may import Instances/ for KATs, never for proofs

**Question (raised by P-08).** `Vk.lean` imports `Midfall.Instances.ExponentModel`
because that is the only runnable `AdmissiblePairing` in the tree (R-28), and the
SRS-binding gates need to actually compute a pairing. Is a Generator file allowed to
depend on a model?

**Decision: yes for computation, no for proof.** An import cannot pollute axioms by
itself, and forbidding it would force either hand-built toy groups in every package that
touches a pairing check, or no gates at all on the τ-binding path. The real hazard is
different and narrower: a *theorem* stated in a file that imports a concrete model
silently acquires a dependence on that model, and the boundary PLAN 3 draws (Instances/
is where the model lives, `native_decide` is confined there) would erode one import at a
time.

**Enforcement, not prose.** `scripts/checks.sh` now has an "Instances/ import
confinement" gate: any `.lean` outside `Midfall/Instances/` that both imports
`Midfall.Instances.*` and contains a top-level `theorem` or `lemma` fails CI. Files that
only `#eval` are allowed through. The gate was tested before being trusted: a planted
violation reddens it (exit 1, naming the file) and removing it goes green again.

**Consequence for later packages.** If a package needs to state a theorem about
`generateBaseVk` or `srsTauIsConsistent`, the statement must live in a file that does
not import `Instances/` - which is also what `plans/P-4a-roots.md` assumes, since the
root-of-unity lemmas are stated over a general field. This makes the boundary explicit
instead of leaving it to be discovered by a reviewer.
## D-P18 (OPEN - needs sign-off): PLAN 9.5's `Supported.layout` claims more than the predicate delivers

**Not adopted.** Recorded because P-03e proved the plan text is wrong and PLAN 12 forbids
weakening a statement silently - but here the honest fix is a *strengthening*, which still
changes a normative sentence.

PLAN 9.5 writes:

    layout : g.plan.memory.WellFormed     -- disjoint, aligned, above solc spill window

Measured (P-03e, gates 13-15 of LayoutMemory.lean):

* **disjoint** - true, but only read lifetime-relatively. `WellFormed` conjoins
  `memoryLifetimeIntersects` exactly as MEM:274 does, and that is correct: the Rust
  phase-scopes low-memory regions, and the poseidon-shaped layout has **54 same-byte,
  different-phase region pairs**. A naive global byte-disjointness predicate is FALSE on
  the real layout. So the word is fine only if the reader understands it as per-lifetime.
* **above solc spill window** - NOT delivered by `WellFormed`. It bounds starts by
  `SOLIDITY_RESERVED_MEMORY_BYTES` (0x80), because that is what `MemoryMap::validate`
  checks (MEM:239). The 0x1000 via-IR guard lives one level up, in
  `VerifierMemoryLayout::validate` (MEM:1028-1036). Demonstrated directly: a layout at
  `vk_mptr = 0x180` is `WellFormed` **and** rejected by `validate`, simultaneously.
* **aligned** - also NOT delivered. `WellFormed` omits the length-alignment arm
  (MEM:262-267), and `new` can violate it through the public `FinalMsmShape.input_bytes`
  field. Gated with a real 0x21 length: `WellFormed` accepts, `validate` rejects.

**Options.**
1. `layout : g.plan.memory.WellFormed ∧ g.plan.memory.validate = .ok ()` - matches what
   the reference actually treats as a legal layout, keeps all three clauses of the
   comment true, and costs nothing since `validate` is already ported. **Recommended.**
2. Keep `WellFormed` alone and delete "aligned, above solc spill window" from the
   comment. Weaker, and it would make `Supported` easier to satisfy than the Rust itself
   is, which is the direction PLAN 12 says not to go.

**Why it must be decided now rather than at M5:** `Supported` is a hypothesis of
`lowering_equivalence`, so every theorem downstream inherits whichever reading is
chosen. Choosing option 2 later would mean the headline theorem was proved about a
strictly larger set of layouts than the contract is safe for, and discovering that after
M7 would be expensive.

**Owner:** you. Until it is decided, P-03e's `WellFormed` stands as ported and no
downstream package should quietly pick a reading.
## D-P19 (ADOPTED, round 16): gates should read the artifact at #eval time, not compare pasted strings

**Decision.** Where a gate's expectation lives in a build artifact - a `.yul` template,
a `.sol` dump, a fixture - the gate opens the file with `IO.FS.readFile` at `#eval` time
and derives its expectation from the bytes. Pasting the expected text into a Lean string
literal is a last resort, and when used it must be paired with an external script that
re-derives the paste from the artifact.

**Why.** This is the direct fix for R-38 finding 1, the defect that `YulGolden.lean`
compares an AST against a hand-typed string and nothing in Lean ever opens the `.sol`.
The mitigation there is `scripts/check_golden_provenance.py`, which re-reads the cited
line ranges and asserts the pinned string - a second program doing the checking that the
gate should have done. It works, and it is fragile in a way the direct approach is not:
the pins, the script's parse of them, and the Lean gate are three artefacts that must
agree, and the script has to be kept in step with the file by hand.

P-09a landed the better pattern first: six gates that parse
`templates/partials/quotient_numerator/QuotientNumeratorBlock.yul` at `#eval` time and
assert the opcode table against the template's own `case 0x..` arms, plus a dedicated
`templateArtifactReachable_ok` so a missing file fails loudly instead of reading as an
empty match. It also went beyond the reference: the Rust test iterates only the table, so
it cannot see a template arm with no table entry; the Lean gate checks coverage in both
directions.

**Consequences.**
1. `kat_gate.py` runs each KAT file standalone, so `IO.FS.readFile` resolves relative to
   the `formal/` directory - the same cwd `checks.sh` uses. Paths must be written that
   way, and the reachability gate must be the first `#eval` in the section so a wrong
   path is diagnosed rather than silently matched.
2. `lake build` caches, so a template edit does not re-trigger a dependent gate during a
   warm build. `checks.sh` re-runs every KAT file every time, which is what makes the
   pattern load-bearing in CI rather than only after a clean build. Say this in the
   header, as P-09a did.
3. **Owed upgrade:** `YulGolden.lean`'s nine pinned slices should move to reading the
   dump directly. That retires a class of drift `check_golden_provenance.py` currently
   has to police by hand. Not free - the tokenisation rules would have to move into
   Lean - so it is queued, not scheduled.
4. New packages should prefer this pattern by default. Recorded in
   `docs/plans/README.md` standing notes.

## D-P20 (OPEN - needs sign-off): two PLAN 9.5 statements are not statable as written

**Not adopted.** P-09b landed the interpreter that PLAN 9.5's `QVM.run` names, and found
that the named function does not exist in the reference. This is a statement-surface
problem, so per PLAN 12 it is reported rather than fixed by choosing a convenient reading.

### 1. `QVM.run (prog) (f) : Except QVM.Fault QVM.Output` - no such granularity

The reference's entry point is `eval_quotient_identity`, called on
`&bytes[cursor..expr_end]` - **one identity's expression subprogram**, up to but excluding
its fold. There is no whole-stream entry point, no `Frame`, and no `Output` object. Only
`QuotientProgramItem::Identity` reaches the interpreter. `plan.inlineIdentities`,
`plan.structuredTailIdentities` and the three native markers never enter it - they are
checked positionally and `identity_values` pushes `Fq::ZERO` for them. **The fold is not
modelled at all**: `FOLD_MAIN`/`FOLD_SELECTOR`/`NATIVE_*` are hard errors inside an
identity expression, and the y-batch accumulation and the negation written to
`QUOTIENT_EVAL_MPTR` are Yul-side.
### 1. `QVM.run (prog) (f) : Except QVM.Fault QVM.Output` - no such granularity

**PARTLY RETRACTED by P-10 (round 31), and the retraction matters more than the original.**
The claim that the fold is "modelled NOWHERE" was **wrong as stated**. P-10 established
from the source that the fold is portable in three distinct senses, two of them in
shipped Rust and one in the reference's test module:

* **structurally** - `direct/folds.rs::check` (FD:336-497) expands every fold site and
  proves each identity is folded exactly once, with the right weight, into the bucket its
  manifest names, no weight reused, none unused. Its own doc scopes it precisely: it
  checks *where and how* a value is folded, not how the value is computed.
* **as emitted text** - `direct_quotient_block`, `push_quotient_trace`,
  `push_quotient_eval_numer_add`, `push_structured_fold_advance`, `push_structured_fold`
  y^(m-1-j)` with `quotient_expected_eval = -main_numerator` (the negation this item
  called "Yul-side"), and `tests.rs:4325` is a **whole-stream fold executor over the
  physical bytecode** that actually runs `FOLD_MAIN` and `FOLD_SELECTOR`. `tests.rs:1289`
  is the reference's own exhaustive proof that the sparse gap form equals the naive
  global-power form.

  **The negation specifically, closed by P-13c (round 40).** It is emitted at
  `QuotientNumeratorBlock.yul:1393` in the compact arm the deployed profile takes (the
  `:1439` form lives in the untaken `when None` legacy arm - an earlier framing of this
  note called `:1439` "the" deployed negation and was wrong). It is **modelled** as Fr
  arithmetic independently of any template: `qvmFrNeg` at `VmReference.lean:266`, used as
  `quotientExpectedEval := qvmFrNeg mainAcc` at `FoldCompute.lean:860`, `:891`, `:952`.
  What did not exist until P-13c was any **link** between that arithmetic and the shipped
  bytes; `VerifierPartials` gate 55 now takes the statement out of the render, feeds it to
  P-09h's independent Yul text reader, and requires the reader's value to equal
  `qvmFrNeg v` for the same memory word, with a negative control. **Still open, and named
  so nobody over-reads that gate:** it is a `#eval` over one concrete memory, not a
  theorem; there is no `forall x` tying the rendered statement to `qvmFrNeg`; and there is
  still no `Frame`/`Output` object to state such a theorem against.

  global-power form.

What **is** correct in the original: no shipped Rust function *evaluates* the fold, and
`QVM.Program`/`Frame`/`Output` still have no reference counterpart at any granularity.
So the honest position, which P-10 states and I adopt, is that PLAN 9.5's
`qvm_compile_correct` should be **two claims**, not one:

1. a **per-stream fold-agreement** claim over `evalQuotientProgramArtifacts` vs
   `expectedLinearizationArtifacts` - statable today modulo `L.plan.qprog`;
2. a **per-identity compile-correctness** claim over `evalQuotientIdentity` - statable
   since P-09d.

The gap between them is named, not papered: the segment-evaluator seam (the test module's
third interpreter uses a `HashMap` memory where P-09b's uses a PRNG - a real mismatch,
not plumbing), and the native markers plus inline prefix, which enter no Lean fold at all
and are covered only by the certifier's positional check.

**Ruling on the two scope errors P-10 reported.**

* **Five unowned `vm/mod.rs` Yul-text helpers** (QVM:4122-4244: `u256_string`,
  `parse_usize_literal`, `yul_let_assignment`, `yul_const_value`, `yul_mulmod_assignment`,
  `yul_addmod_assignment`, `yul_mload_literal_expr`) fell between packages - P-09c stopped
  at 4120, P-09f at 4081 - and `quotient.rs` depends on them. P-10 ported them with their
  `QVM:` cites rather than importing around the cut, which was right. **Ruling: they stay
  where they are.** Moving them back to a Quotient module is churn with no gain, and the
  alternative - leaving `quotient.rs` unbuildable - is worse. Recorded as a hole in the
  P-09 split, not as a defect in P-10.
* **`folds.rs::check` has no shipped producer of a non-degenerate `FoldRecord`** until
  `direct/emit.rs` lands in M10, because `push_structured_fold` creates every `Weighted`
  site with an empty function name and `emit.rs` fills in the names and call counts. P-10
  hand-built the record the way `emit.rs` would and said so plainly. **Ruling: accepted**,
  and it is a genuine limit on what M6 can claim about the `Weighted` arm until M10 - it
  must be restated when `direct/emit.rs` lands, not quietly dropped.

### 2. `qvm_validated_noOOB`'s `.oob` fault cannot arise — RESTATED by P-09e (see below)

The plan asserts that a validated program with a well-formed frame never faults
out-of-bounds. But verifier memory in the certifier is a **PRNG over the whole u32
address space** - every address read succeeds by construction. The only out-of-range
faults that exist are reads past the end of the *program* and constant slots past the end
of the *table*.

**RESOLVED by P-09e - a reconciliation, not a reversal.** Both readings were correct
about **different memories**. The validator bounds the program against the *deployed*
`VerifierMemoryLayout` (plan.rs:570-643, which states plainly that "the interpreter has
no runtime pointer clamp"), and there an out-of-window read is silent corruption rather
than a revert. So `qvm_validated_noOOB` IS about this layer, but as a **layout
property** - *validated program + layout model implies no pointer the program loads lies
outside the populated windows* - quantified over the layout model, not over a memory
object and not as an interpreter fault. **Item 2 is closed on this basis.** Items 1 and 3
remain open, as does D-P18.

### 3. `qvm_compile_correct` cannot be *stated* until the compiler lands

The certifier's seed is `derive_certify_seed(&[build], &exprs, &vk_payload)` - Keccak over
the **finalized bytecode**, the constant table, the hashed expression trees and the VK
payload. The finalized bytecode is exactly what the builder emits, so the theorem's
hypothesis quantifies over an artifact nothing currently in the tree can regenerate. This
blocks the *statement*, not just the proof, and it makes P-09c (the VM compiler) the
critical path for M6 rather than a later convenience.

What is now reproducible and byte-exactly gated is the half the soundness argument turns
on: **given a seed, the assignment is identical to the Rust's.**

### 4. `qvm_yul_refines` and `direct_correct` have no Rust proof structure

`reference.rs`'s own doc assigns the reference-interpreter-to-Yul leg to the opcode and
memory-token conformance tests plus a per-identity trace differential. So these are
theorems we originate. That was already suspected in `plans/P-09-quotient-vm.md`; it is
now confirmed from the source, and no Rust-side argument should be invented to hang them
on.

**Owner:** you, for items 1-2 (they change normative text). Item 3 is a scheduling
**Addendum after P-09d (round 19).** Two of item 3's named blockers are gone: a
**per-identity** `qvm_compile_correct` over a real multi-identity program is now statable
- every object it quantifies over exists. The literal PLAN 9.5 form still is not, and the
remaining gaps are now precisely named:

* `QVM.Program` / `Frame` / `Output` - no reference counterpart at all. Either the
  statement is per-identity, or these three are invented and the reference gives no
  warrant for them.
* `L.plan.qprog` - needs `LoweringPlan`, which is P-11.
* **The fold.** P-09d's F-6 is the sharpest statement of this: three packages now touch
  `FOLD_MAIN`/`FOLD_SELECTOR` - the builder emits them, the reference interpreter rejects
  them inside an identity expression, the certifier inspects their bytes positionally -
  and **none of them executes a fold.** The y-batch accumulation and the negation written
  to `QUOTIENT_EVAL_MPTR` are Yul-side. So the fold must either enter the statement via
  the Yul emitter (P-09e) or be explicitly excluded from `qvm_compile_correct`'s scope,
  with the exclusion named rather than implied. This is now the largest single gap in
  M6's statement, and it is not in any file ported so far.
* `Supported.qvm` names `validateQuotientProgramOperands` - the validator, next package.

consequence I have applied: P-09c moves ahead of P-10.



## D-P14 (ADOPTED, round 9): R-22 - keep truncated challenges; re-derive the x1/x4 rows

**Decision.** The supported profile keeps `truncatedChallenges = true`. R-22 option (b):
the x1 and x4 rows of plan 9.4's `roundErr` are re-derived for truncated powers rather
than dropped, and the deployed configuration stays inside the scope of S1 and S3.

**What was decided against.** Option (a), dropping the feature from the supported
profile, would have been the cheapest proof but would exclude the Moonlight deployment -
i.e. it would make D1 and M11 provable only about a configuration nobody runs. Option
(c), stating S1/S3 only under `truncatedChallenges = false`, is retained as the
*fallback*, not the plan: if the re-derivation resists, S1/S3 get the hypothesis and
deployed knowledge soundness is marked unresolved in writing. Neither option changes the
generator or the deployment: truncation is preserved for output compatibility, which was
the binding constraint.

**Consequences, all of them costs.** (1) `docs/security.tex` does not exist yet and now
has a mandatory section it was not written for: a soundness bound for
`sum_j truncate(x^j) * C_j = 0` where `truncate` is the low-128-bit re-embedding of
arithmetic.rs:247-252. This is not a degree argument; the expected shape is a per-test
bound over the truncation image, and `maxPolysPerSet` / `numPointSets` are the wrong
quantities in it. (2) `Spec/Degrees.lean` currently defines `degX1`-shaped counts that
the new argument will not use; they stay (they are faithful to the code) but the rows
that feed `roundErr .x1` and `roundErr .x4` must be redefined, not reused. (3) M9 cannot
start until that paper section exists, so this decision does not unblock M9 - it fixes
which proof M9 needs. (4) Nothing in M2-M8 changes: the port, the lowering proofs and
the byte-conformance work are indifferent to this.

**Owner:** the paper proof, before any Lean formalisation of S1/S3.

## D-P15 (ADOPTED, round 9): R-42 - import the textual via-ir IR via generated yul% quotes

**Decision.** R-42 option A. `Midfall/Yul/ImportSolcIR.lean` does not read
`solc --ir-ast-json` (which is the legacy pipeline's artifact and describes a program
that cannot be compiled to bytecode at all - see R-42). Instead a script extracts the
`ir` artifact from `--standard-json` with `viaIR: true` and the deployment's optimizer
settings, emits it as a Lean source file of `yul%` quotations, and lets the **elaborator
be the checker**: if the generated file elaborates, the IR is in the vendored AST; if it
does not, the import fails loudly rather than silently mis-parsing. A runtime Yul parser
is not written.

**Measured feasibility, against the tracked poseidon dump** (via-ir `ir` artifact:
140,357 chars, 2,245 lines; extracted with the pinned solc through standard-json,
viaIR true, evmVersion cancun, optimizer runs 200, metadata bytecodeHash none):

* the DSL's two documented gaps barely occur: **zero** `: u256` annotations, **zero**
  `-> u256` return annotations, **zero** typed function parameters, and exactly **one**
  `hex"..."` data literal.
* 76 user-defined functions and 40 dialect builtins resolve cleanly; the dialect already
  knows `mcopy` (59 sites), `datasize` (25), `loadimmutable` (2), `dataoffset` (1).
* **exactly two names do not resolve: `memoryguard` (2 sites) and `setimmutable` (1
  site).** Everything else my first scan flagged was solc's own embedded `//` source
  comments, not calls.

**So the decision carries one prerequisite:** the vendored EVM dialect must gain
`memoryguard` and `setimmutable`. That is not incidental work - plan 7's IRCheck is
required to reason about exactly those two things ("the memoryguard and spill region are
disjoint from L.plan.memory"; "immutables come from `loadimmutable`, which equals
constructor-set values", whose constructor side *is* `setimmutable`). Adding them to the
dialect is small and upstreamable, which is what plan 7 anticipated for our additions.

**Also settled by this:** the IR of record is the **via-ir** IR, and it is
optimizer-setting sensitive (the `ir` artifact differs between `optimizer.enabled` false
and true: `e3f04cfc1c05d699` vs `e9465b3433265c3f`). So the import must pin the full
setting triple - viaIR, optimizer enabled, runs 200 - not just the compiler version.
BASELINE.md's toolchain table carries the measurements.

### D-P15 LANDED (P-IR): what was pinned, and the two decisions the import had to make

The import exists: `formal/scripts/gen_import_solc_ir.py` generates
`Midfall/Yul/ImportSolcIR.lean` (4,221 lines) from the `ir` artifact of the two
tracked deployed sources, and commits the artifact text verbatim beside it
(`Midfall/Yul/solc-ir-Halo2Verifier.yul`, 2,898 lines / 192,150 bytes, sha256
`a3e3923e...`; `solc-ir-Halo2VerifyingKey.yul`, 604 lines / 64,329 bytes, sha256
`af3ccbdb...`). The pin is the same triple `extract_ir_builtins.py` enforces - solc
0.8.30 commit 73712a01, sha256 `738dcdc6...dd683`, `viaIR: true`, optimizer enabled
runs 200, `evmVersion: cancun`, `metadata.bytecodeHash: none` - and the script refuses
to run against a compiler whose digest differs. Ten gates at the bottom of the generated file
re-derive the digest, the artifact shape, the rename mapping, the per-name call-site counts and
the literal and identifier aggregates of the elaborated AST at `#eval` time (D-P19), so the
import is reproducible and drift is a build failure rather than a discovery.

**Decision 1 - `ir`, not `irOptimized`.** PLAN section 7 says `irCheck` validates the
*unoptimised* IR, and the Yul-optimizer hop is in the trusted base: differentially tested against
the compiler, not proved. So the import pins `ir`. The consequence is measured and stated
rather than left to be rediscovered: `memoryguard` survives both artifacts with a different
*argument* - the `ir` runtime object says `memoryguard(128)`, `irOptimized` says
`memoryguard(0x08e0)`, and the deployed bytecode begins `PUSH2 0x08e0 PUSH1 0x40 MSTORE`,
which is what `Generator/Evm.lean:129` reads back. The shipped bytes therefore agree with
`irOptimized` and not with the imported `ir`. That is a memory-layout difference, not an
observable one: `Bridge.ObsView` excludes memory deliberately, so `lowering_equivalence` can
be stated at view level over both sides. `verifierRuntime_head_is_memoryguard` pins the 128
propositionally (`rfl`), so switching artifacts becomes a decision and a build failure. In the
VK contract the optimizer folds `memoryguard` out entirely - its `irOptimized` has zero
occurrences - which is why "memoryguard always disappears" was measured per artifact rather than
assumed.

**Decision 2 - the two alpha-renames are applied at emit time, not in the lexer.** Lean's
`ident` lexeme rejects `$` and `end` is reserved, so the artifact cannot be quoted as it
stands. Extending the vendored DSL lexer was rejected: it is in `vendor/` (outside this
package's authorisation), it would make the DSL accept programs upstream rejects, and either way
the imported names differ from the artifact text - so the rename must be documented either way,
and only the emit-time rename can be *gated* from the artifact. The rule is
`x |-> "solc_" ++ x.replace "$" "_"` for a name containing `$` or in the reserved list, and
identity otherwise. The reserved list is exactly `[end]`, and that is a measurement: every
identifier of both artifacts (2,246 distinct) was fed to `yulE%` one at a time and the
rejections collected - 517 needed the rename, and the only non-`$` one was `end`. (One
identifier per Lean process matters: batched, the command parser swallows following lines after a
parse error and under-reported 97 of 514.) The other Lean keywords occurring in the artifacts -
`if let for switch case default function leave object code data` - sit in grammar positions the
DSL already handles, and `return` only in the `return(...)` statement, which has its own
production; renaming them would break the quotation. `irRename_ok` re-derives the mapping from
the committed artifact with an independent Lean lexer and asserts injectivity, disjointness from
## D-P23 (ADOPTED, round 60): every stated theorem carries a standing non-vacuity obligation

**Decision (human).** Extra review passes on the statements are mandatory, not optional:
every stated theorem and every structure field must be shown to be **non-vacuous** and to
**prove something**. This supersedes the earlier deferral of reviews for statement work -
per-task code reviews stay deferred until the semantic-equivalence results land, but
**statement reviews now run repeatedly and indefinitely.**

### Why the evidence justified it

The first statement-only review (R-58) found ten defects, six demonstrated in Lean, in
work that had already passed every mechanical gate. Two patterns explain why ports cannot
catch this:

* **A field can be satisfied for a reason unrelated to its subject.**
  `points_subgroup_checked`'s conclusion held with *no hypotheses at all* - the existential
  call was not tied to the run, and `permissive` admits any failed call to any target.
  `accFixedBases_producer` held for the empty table. A Surface with
  `irCheck := fun _ => false` satisfied `ir_refines` trivially.
* **A Lean record can admit a state the Rust cannot.** `PlanView.hasAccumulator` was a free
  Bool, so 11 of 13 `PartialSpecs` fields discharged on a one-Bool lie. Same class:
  `numInstances`, `evaluator`, `encG2`, and the `quotient`/`direct` pair - the last one
  introduced by the orchestrator while fixing a different vacuity.

### The obligation, stated so it is checkable

For every theorem, and for every field of a structure that a theorem consumes, a package
must provide **both**:

1. **A satisfiability witness** - a concrete object meeting the hypotheses. If no witness
   exists in the tree, the statement is vacuous and must say so. (Counterexample that
   passed every gate: the fixture set `encG2 := fun _ => Bytes.empty`, so *no*
   `Eip2537.Holds` was satisfiable at the only Surface in the tree, and every field
   carrying `Holds` was unexhibited.)
2. **A falsifiability demonstration** - a perturbation that breaks the conclusion while
   keeping the hypotheses true. If no such perturbation exists, the field cannot fail and
   is decorative: defer it with its blocker rather than ship it.

### What does NOT satisfy the obligation

* **Text-fragment gates.** `scripts/check_statement_fingerprints.py` pins 42 fragments of
  `LoweringCorrect` against the plan sketch. It catches paraphrase and nothing else - F1,
  F7 and F8 all passed it. A gate over fragments is not a gate over meaning.
* **Prose claims of non-vacuity.** A doc comment saying the statement is meaningful is not
  a witness.
* **A `True` or trivially-discharged field.** Attack.md already rejects `True := trivial`
  placeholders; the same applies to any field whose proof does not depend on its subject.

### Standing practice

1. Every statement-bearing package brief carries this obligation verbatim.
2. After any batch of statements lands, run a **statement-only adversarial review** -
   read-only, hunting vacuity, wrong-direction, wrong-reason, arity drift, decorative
   fields, and duplicated-fact-without-a-pin. R-58 is the model for the report shape.
3. Repeat after each repair round, because a repair can introduce a new vacuity - it has
   happened here.
4. Prefer **deferring a field with a named blocker** to stating one that cannot fail. The
   deferred trio is the precedent.

the untouched names, that no image is a keyword, that every renamed name occurs in the imported
AST, and that no original name survives anywhere in it.

**Nothing was dropped.** The transform is a 1:1 token rewrite over the whole artifact, comments
stripped (48 + 9 lines) and strings preserved (they carry the object names `dataoffset` resolves
and the `setimmutable`/`loadimmutable` key). Measured and reported rather than hoped: zero
`: u256` and zero `-> u256` annotations in either artifact, so the DSL's documented
type-annotation gap is not reached; the single `hex"...` literal per artifact is a `data`
segment, which the DSL does support. Gate 6 compares the elaborated AST's per-name builtin and
user call-site counts against a call-site manifest the generator measures from the artifact text
by regex - two independent routes to the same number, so a deleted statement changes only one and
the gate goes red. Gates 8 and 10 additionally pin the node count, the digest of every identifier
in order, and the literal aggregates, so an edited variable name or an edited constant reddens
something too (`scripts/perturb_import_ir.py` runs those controls).

**Finding F-IR-1 (P-VEND's manifest is not a measurement of the deployed verifier).**
`scripts/extract_ir_builtins.py` keys its standard-json source dict by *basename*, and two of
its three tracked sources are named `Halo2Verifier.sol` (the deployed one and
`target/poseidon-fixture-dump/Halo2Verifier.sol`), so the later entry overwrites the earlier and
the rows labelled `Halo2Verifier` in the tracked `Midfall/Yul/ir-builtins.tsv` were computed
from the poseidon dump. The deployed artifact has no `xor` site at all; the manifest claims 3,
and 28 of 42 builtin rows disagree with the deployed object. This package did not edit that script
or its manifest (they are P-VEND's), and the conclusion P-VEND drew from them survives: the two
names that mattered, `memoryguard` (2 sites) and `setimmutable` (1 site), agree either way -
`irBuiltinsManifestDiverges_ok` pins exactly that. The import's own anti-drop gate uses a fresh
manifest, `Midfall/Yul/solc-ir-callsites.tsv`, measured from the committed artifacts.

**Hazard 3 discharged: `RunContractIR` has a witness.** `Midfall/Instances/ImportedIR.lean`
exhibits, for *every* `ExternalCalls` and *every* `ExternalGas`, a committed run of the imported
runtime block from the entry frame an empty calldata produces: prologue, dispatcher skipped
(`iszero(lt(calldatasize(), 4))` is zero), fall-through to the user function
`revert_error_42b3...()`, whose body is `revert(0, 0)` - three steps of the real 28-statement
top-level block, ending in a revert. It lives in `Instances/` because a `Surface` needs an
`AdmissiblePairing` and D-P17 keeps that import out of theorem-bearing files. It is proved
non-vacuous in both directions: the observation is a `HaltKind.revert` (not a stop, not a
return), the free-memory pointer the run leaves is the artifact's 0x80, and a `Surface` whose
`runtimeName` does not name the imported sub-object has *no* witness at all.

**Consequence for stage 6.** `ir_refines` and `lowering_equivalence` can now be STATED with a
real, inhabited `RunContractIR` hypothesis over an object that exists in the tree. What is still
missing is named in the P-IR report: the shell side needs a `Surface` built from the P-11 plan
and the P-13 AST emitter (the fixture's `blk` is a placeholder), and
`Bridge.dialect_deterministic` plus the other stage-1 proof obligations are still `sorry`, so the
equivalence can be stated but not yet proved.

## D-P21 (ADOPTED, round 51): R-51/F5 - split `chalMass` per round; the uniform x3 mass is unsound

**Decision (human: use the recommendation).** `chalMass` currently applies
`s / 2^128` uniformly to every round under `truncatedChallenges`. That is **wrong in
different directions for different rounds**, and one function cannot be both:

* For the six untruncated rounds (`theta`, `beta`, `gamma`, `trash`, `y`, `x`) the digest is
  reduced into the field and NOT truncated, so the true mass is `3s/2^256`. Using
  `s/2^128` there is **pessimistic but sound** - it throws away ~127 bits of budget for free.
* For `x3`, Rust does `squeeze_challenge()` (reduce into the field) and THEN `truncate`
  (`kzg/mod.rs`, `arithmetic.rs:247-252`, `nb_bytes = 16`). The image is `[0, 2^128)` but
  not uniform: each truncated value is hit by about `r/2^128 ~ 2^127` field elements, so
  the per-value mass is about `3*ceil(r/2^128)/2^256 ~ 1.5/2^128`. **`s/2^128` is too
  small there - unsound.**

**Adopted shape:** `chalMass F round s` takes the round, and returns the truncated mass
only for the rounds Rust actually truncates, with the `ceil(r/2^128)` factor made explicit
rather than folded into a constant. `Spec/Degrees.lean`'s `x3` row (`maxSetSize * n`) is
corrected in the same change, since R-23 already recorded that its comment describes
truncation as happening before field reduction, which is the wrong order.

**Constraint that does NOT change:** truncation is preserved for output compatibility
(D-P14). We do not alter the deployment to make the proof easier.

**EXECUTED (P-CHALMASS).** `chalMass F round s` is per-round in
`Midfall/Security/Challenges.lean` (ENNReal) and `Midfall/Halo2/Spec/Degrees.lean`
(`ℝ≥0`): `Chal.truncatedValue` names the rounds whose VALUE the Rust truncates
(`x3` only), `truncPreimageCount = ⌈r/2^128⌉` is a named Nat factor outside the
division rather than a folded constant, and every mass is stated over the common
denominator `2^256`. The unsoundness is exhibited both ways:
`chalMassUniform_lt_x3_mass` (witness - the per-round mass is strictly larger than
the uniform one) and `uniform_admits_new_refuses` (falsification - at the KAT
index's `x3` count of 48 a budget of `50/2^128` is admitted by the old bound and
refused by the new). `Spec/Degrees`'s `x3` row and comment now say
reduce-then-truncate, and the row count is `max (maxSetSize * n) badPointsX3Count`.
Two corrections to the decision text itself: the exact factor is
`3⌈r/2^128⌉/2^128 = 1.3585351690…`, not `\approx 1.5` (the shortfall is 0.442 bits,
not half a bit), and the six untruncated rounds gain `2^126.42`, not `\sim 127`.
**Recorded so the failure mode is visible:** D-P29 (docs/design.md:1054, round 68)
already said "D-P21 is implemented at last", and it was not - `chalMass` still had
its old two arguments and the same uniform body at the head of this branch, and the
same sentence went on to call the x3 row "currently unsound" in the next clause. A
decision annotated as done is not a decision done.

## D-P22 (ADOPTED, round 51): R-51/F6 - carry ARSDH for S3; deployed knowledge-soundness is scoped

**Decision (human: use the recommendation).** Two entangled choices, now settled:

1. **S3 (KZG multi-open binding) is stated against ARSDH, not q-DLOG.** ArkLib's
   `KZG.CommitmentScheme.function_binding` is *proved* under ARSDH
   (`FunctionBinding/Basic.lean:635`, hypotheses `p >= n+2`, `pairing g1 g2 != 0`,
   `SampleableType G1`). PLAN 9.4 stated S3 against a q-DLOG game and called it "largely a
   freebie"; that wording obscured a real choice. Adopted: **carry the ARSDH term** and
   prove the multi-open bridge ourselves, rather than claim a reduction between the
   assumptions we do not have.
2. **S1 and S3 for the DEPLOYED profile are explicitly unresolved**, because of R-22: the
   truncated powers `truncate(x^j)` used for `x1`/`x4` are not low-degree polynomials in
   the challenge, so no root-count argument bounds their bad set. Until a bound is proved
   for the deployed coefficients, `halo2_knowledgeSound` and `kzgMultiOpen_binding` are
   stated for the **untruncated** profile, and `docs/PLAN.md` section 13 records the
   deployed case as open. **This is a scope decision, not a gap in the port** - it does not
   touch byte-conformance work or the lowering theorems, which are hash-agnostic and
   profile-agnostic.

Note also, so nobody re-derives it: `rbrKnowledgeSoundness_implies_knowledgeSoundness` is
`sorry` in ArkLib, and **no Fiat-Shamir soundness or knowledge-soundness theorem exists
there at all** - S4 is entirely ours.

## D-P24 (ADOPTED, round 68): scope is per-deployment first; generic is a stated follow-on

**Decision (human: recommended option taken).** PLAN section 0 promised
`lowering_equivalence` generic over every supported VK and config. **Adopted: per-deployment
translation validation over a real-curve Surface first**, with the generic theorem recorded
as a follow-on rather than the deliverable.

* **Why:** the code already points this way, and a generic proof requires induction over the
  generator AST-building functions - a different order of work. AST emission (D-P25) makes
## D-P30 (ADOPTED, round 72): no raw string expressions - all Yul emission goes through the vendored AST

**Decision (human), extending D-P25.** Every Lean generator function that produces Yul must
build `Block/Stmt/Expr EVM.Op` from `vendor/yul-semantics`. **The text port is a reference,
not the deliverable.** PLAN section 8's required equation - `render g o = (lower g o).map
print` holding **by construction** - is the definition of done, and that is not the
structure of the code today.

### Measured starting point

| site | state |
|---|---|
| `GenAst.emittedPartials` | `[.finalPairing]` - the other six partials fall through to `emitPlaceholder` |
| `Quotient/Evaluator.lean` | entirely text: `abbrev Lines := List String`, `letLine v rhs := "let " ++ v ++ " := " ++ rhs`, `assignLine`, `u256String`, `columnEvalVar : String`; builders like `lookupSharedPrefixFPlusBeta` return `E F (Option (List String))` and concatenate loop headers and `0x` pointer renderings. **18 string-machinery sites.** |
| `VerifierPartials.lean` | `renderX : PartialCtx -> String` throughout - **68 String-returning sites** |
| `Contracts.lean` | assembles the contract from string fragments |
| `Kzg.computations` (`:1320`) | emits text; already flagged as a prerequisite for `pcs_spec` |

**Expressions must not be string-concatenated.** Numbers become `Literal.number`, variables
become `Expr.ident` / `Stmt.assign`, calls become `Stmt` forms - no
`"mload(add(" ++ ... ++ "))"`.

### Explicitly out of scope

The **Solidity** wrapper - `Constructors.sol`, `Constants.sol`, `PrecompileSmoke.sol`, and
the three contract shells. That is not Yul, has no AST, and stays text with the line-based
normaliser. **Say so in the header of each such file so nobody "fixes" it.**

### Acceptance, and why each clause is there

1. **Per slice: `stmtsBeq` against the text port parsed output - not token comparison alone.**
   P-AST measured that spelling every `mcopy` as a USER call left all four token gates green
   while the `stmtsBeq` gates reddened. The token comparator is a tripwire; `stmtsBeq` is the
   check of record (D-P13, D-P25).
2. **Keep the text port and its byte-exact gates** as the cross-check, so each converted slice
   is validated against something the converter does not control.
3. **Numeric spelling is a documented divergence, not a failure.** The AST stores
   `Literal.number (n : Nat)` and prints decimal while the Rust emits hex. Pin the mapping
   explicitly rather than normalising it away - this is one of the two reasons "compare
   modulo comments" reports differences on identical code (the other being line breaks).
4. **`emitPlaceholder` must end up unreachable, or total with a proof of its emptiness.** A
   `Partial` that silently yields a placeholder is the R-62 defect class returning.
5. **No `yul%` DSL extension and no fork edit for this.** Constructor helpers sufficed for
   FinalPairing. If a slice genuinely cannot be built without splicing values into `yul%`,
   **stop and report it** as a tooling finding.
6. **Re-check the `blkPinBites*` family** after each slice becomes real, and add the equivalent
   non-vacuity gate for each newly real slice. `BlkIsEmitter` already pins `blk` and `L.main`;
   after this it pins them to a generator that is real for all seven slices.

### Ordering

This gates **P7, P9 and P10** - `quotientLin` and `pcs` are what the quotient and PCS specs
need. **P5 can proceed in parallel**, since FinalPairing's AST is real. **Split per partial
(or per pair) rather than one large package**, given the interruption pattern and that each
slice is independently checkable.

  the generic form reachable, so this is a deferral with a route, not an abandonment.
* **Consequence for the `blk` defect (R-62):** `blk` is pinned to the generator AST function
  as a hypothesis of each `*_spec` theorem. That is what makes the ten currently
  false-as-stated theorems true.
* **PLAN section 0 must be amended** so the promise matches the deliverable.

## D-P25 (ADOPTED, round 68): the generator emits Yul ASTs; text is the reference, not the deliverable

**Decision (human).** Three-part design, now explicit in PLAN and D-P13:

1. **Emission.** The generator builds the vendored Yul AST (D-P2).
2. **Comparison.** Structural AST equality via `YulSemantics.SyntaxEq.stmtsBeq` is the
   **check of record** for M3. It is insensitive to comments and formatting.
3. **Tripwire.** Token-level comparison (comments dropped, hex reduced to values) is the CI
   tripwire for the Yul blocks; **line-based normalisation is used only for the Solidity
   wrapper**, which is not Yul.

**Why the naive version fails, measured:** comparing printed text reports differences on
code known to be identical - `normalise_sol.py` calls Lagrange different (73 vs 60 lines)
and FinalPairing different (6 vs 3), purely from line breaks and decimal-vs-hex number
spelling, while the token comparator calls both equal. **A tripwire that fires on identical
input is worse than none**, because it trains people to ignore it.

**Status correction this decision settles:** `VerifierPartials.lean` is a TEXT port and
treated byte equality as M3 acceptance, contradicting PLAN section 11. The design was right;
the implementation drifted and no document caught it. The text port stays as a Lean-side
reference - each converted part is checked against it without re-running Rust.

## D-P26 (ADOPTED, round 68): AST construction uses constructor helpers first; no DSL extension yet

**Decision (human).** `yul%` cannot splice Lean values - only literal numbers, strings and
identifiers - so a generator cannot inject computed constants or loop-generated statements.
**Adopted: build ASTs with constructor helpers**, starting with `FinalPairing` and its
`ec_pairing`/`fail` helpers. **Extend the vendored DSL for splicing only if the helper route
proves painful**, and only as a separately authorised fork edit like `memoryguard`.

* **Why:** keeps the fork minimal and produces a real data point before committing to a DSL
  change that every later package would depend on.
* **Third option on record:** write templates with named placeholders and substitute after
  (`substConsts`, already in P-SE step P2). Not chosen first.

## D-P27 (ADOPTED round 68, **EXECUTED** by P-REPIN): re-pin `Statements.lean`; a freeze must not protect a false statement

**Decision (human).** The frozen file currently holds `verifyNative_iff_msgs`, which is
**known false** for a degenerate codec, and `verifyMsgs_iff_spec`, which cannot hold for
every verifier environment. Both facts existed only as comments elsewhere and never reached
the open-decisions list - a reporting failure by the orchestrator, since P-SE instructed that
they be reported.

* **Action:** re-pin the SHA-256 with (a) the codec-law hypothesis added to
  `verifyNative_iff_msgs`, (b) `verifyMsgs_iff_spec` made environment-dependent or scoped,
  and (c) `contractRef_noAcc` marked superseded by the proved
  `contractRef_noAcc_of_semanticEquivalence`.
* **Principle recorded:** a hash freeze protects against silent drift. It is not a licence to
  leave a known falsehood frozen.

**EXECUTED (P-REPIN), 26 rounds late.** The digest moved `d4984965…a3f3` →
**`40d97dc75466f0640746ec6ad5e7d5e273e46bd76fdac06efca7b0e38f54dc6e`**, which is what
`Midfall/Statements.sha256` and the `checks.sh` hash section now check. All three authorised
actions landed, and nothing false was deleted:

* `verifyNative_iff_msgs` carries `hc : E.g1.compressedRoundtrip` **and nothing else** -
  attack.md line 107 FIX shows `p ≤ 2^256` decorative there, so this is a targeted repair and
  not a hypothesis pile-up.
* `verifyMsgs_iff_spec`'s right-hand side is `Spec.accepts E H F params vk inst ms`: the
  environment is threaded into the spec, which required `Spec.accepts` to gain `E` as its
  first argument. Arity only - it is still the registered Phase 4 hole, and the Exec-tautology
  ban at `Spec/Piop.lean:22-30` is intact.
* `contractRef_noAcc` is **marked SUPERSEDED** by the proved
  `Lowering.contractRef_noAcc_of_semanticEquivalence` and kept, `sorry` and all, because what
  this file freezes is the shape of the obligation and the shape is now known to be right.

D-P23's both halves for all three live in `Midfall/Instances/StatementsRepair.lean`:
witnesses `repair1_satisfiable`, `repair2_new_shape_inhabited`, `repair3_rederived`; retained
refutations `repair1_old_false_at_degEnv`, `repair1_old_universal_refuted`,
`repair2_old_refuted`, with the old texts pinned as named propositions
(`verifyNative_iff_msgsOld`, `verifyMsgs_iff_specOld`) rather than deleted.

**Two decisions this leaves open, recorded rather than taken (P-STATGATE):**

1. `contractRef_noAcc` is **derivable** - `repair3_rederived` is a one-line re-export of a
   proved lemma with no `sorryAx` in its dependencies - and still carries a `sorry`, so
   `SORRY.md` counts one hole that is not open. Filling it is a statement-surface change
   needing a re-pin, and the spec surface deliberately holds statements rather than proofs.
   Say which you want. `scripts/check_frozen_axioms.py` reddens if it is filled silently, so
   this cannot drift either way without being noticed.
2. The two dead imports in the frozen file (`Midfall.Security.SRS`,
   `Midfall.Security.Challenges`) widen its trusted surface for no reason. Removing them is
   also a statement-surface change and D-P27 was deliberately narrow. They are now pinned as
   `STATEMENTS_IMPORTS` in `scripts/check_statement_fingerprints.py`, so the surface is at
   least visible and any change to it reddens a gate with a reason attached.

**Corollary, added by P-STATGATE.** A hash proves the file *is the file*, never that the file
is *correct*. Deleting the codec law from the repaired statement left the build and all three
structural gates green, so the frozen normative file had no semantic coverage at all. It now
has a two-sided pin in `scripts/check_statement_fingerprints.py` - repaired shape required,
refuted shape refused, plus exact text, binder context, trusted surface and doc-string
provenance - and the axiom probe in `scripts/checks.sh` is a gate
(`scripts/check_frozen_axioms.py`), not a print.

## D-P28 (ADOPTED, round 68): M0 baseline - regenerate, re-pin, and delete the unread fixtures

**Decision (human).** Per R-57 the committed poseidon fixture was stale on arrival and fails
the current verifier.

1. Regenerate the six live poseidon artefacts under the profile `BASELINE.md` already records
   - `outerFewerPointSets = false`, the 2,640-byte proof.
2. Re-pin the SHA-256 rows at `BASELINE.md:211-228`.
3. **Delete the 12 of 18 files in `fixtures/poseidon/` that have zero code references**
   (verified: `pairing_fixture` and friends appear only in `BASELINE.md`), with a commit
   message recording that they had no generator in this tree.
4. Reconcile the recorded profile so G0 and `BASELINE.md` name the same one.

* **Principle:** keeping unverifiable artefacts in a frozen baseline is worse than removing
  them. A SHA-256 table that pins files nothing reads implies coverage that does not exist.

## D-P29 (ADOPTED, round 68): security moves to the ArkLib Interaction framework; PROOF-PLAN stays alive

**Decision (human).** Supersedes parts of **D-P22**, which was signed on a false premise.

* **Verified:** the pinned ArkLib `Interaction` layer (39 files, 0 `sorry`, 0 `admit`, 0
  `native_decide`) proves `stateRestoration_knowledge_soundness` and a per-round-error
  variant whose shape matches `roundErr`, with a tighter `Q*max + Sum` bound, plus sequential
  composition in `KnowledgeComposition.lean`. `#print axioms` on the five key theorems shows
  only `propext, Classical.choice, Quot.sound`.
* **Therefore:** S4 is NOT entirely ours - it reduces to showing the Keccak hash chain
  simulates the Interaction layer oracle up to collisions. S1-S5 are restated in that
  framework. **D-P21 is implemented at last** (per-round `chalMass`; the x3 row is currently
  unsound).
* **`PROOF-PLAN.md` is NOT retired.** It is re-pointed at `Interaction`, and an explicit owner
  is assigned to the S7 bridge - composing `lowering_equivalence` with the
  `verifyMsgs_iff_spec` refinement, which P-SE finding 2 says is unprovable as written and
  which nothing currently schedules.
* **Deployed-profile knowledge soundness stays explicitly unresolved** (the second half of
  D-P22 stands): truncated powers are not low-degree in the challenge. Adopted shape: state
  the truncation bound as a **named, parameterised assumption**, so deployed KS becomes a
  theorem conditional on one precise conjecture, with the non-vacuity checks recorded
  (`B = r` satisfies it; `c = (1,-1)` refutes any `B` below about 2^126).

## D-P31 (ADOPTED, round 73): RAM is a budgeted resource - a package that evaluates in the VM states a peak, runs under `ram_guard.sh`, and reports the measurement

**Decision (human), from P-RAM (`docs/plans/P-RAM.md`).** The cost of VM evaluation was
known, measured, and correctly acted on - and it lived as comments inside
`Midfall/Lowering/RunEmitted.lean`. Comments do not bind the next package, so the next
package could repeat the crash exactly. Two crashes are on the record:

| moment | peak lean RSS | outcome |
|---|---|---|
| pre-crash session | **8.7 GB** (six `native_decide` in one process) | session killed |
| per-unit `native_decide` | **16.8 GB** on a 32 GB host | **host went down**, 52-72 GB swap |
| per-unit `#eval` | 3.8-4.6 GB | killed by the package own watchdog |
| P-EXEC as shipped | **2.34 GB** | green |

**Root cause is structural, not a leak.** `EvmState.memory` is `Nat -> UInt8`, so every
`mstore` wraps the previous function and a deep run builds a long closure chain that is
both slow and memory-heavy. Compounding it, each unit re-spelled the emitted helper block
until P-EXEC shared it (`RunEmitted.lean:215-220`, `runnableHelpers`): fourteen live
copies of one block was a 4.2 GB process. Sharing was a memory fix, not a semantic one.

### The rule

Any package that evaluates in the VM - `#eval`, `native_decide`, a KAT that runs the
interpreter - must:

1. **state an expected peak** in its plan or module header BEFORE running it;
2. **run under the guard**: `scripts/ram_guard.sh --limit 6G -- lake build`;
3. **report the measured peak RSS** in its results, taken from the guard own output.

A gate that cannot run within budget is **narrowed or dropped, with the reason recorded**
- exactly what P-EXEC did when it withdrew the `Instances` theorem form and left the
lifting lemma in a header for a later, narrower unit set. **A gate that kills the session
is not a pass**, and withdrawing with a named blocker is the sanctioned response rather
than a failure.

### The tool

`scripts/ram_guard.sh` - bash 3.2, no dependencies beyond `ps`, `awk`, `sysctl`,
`vm_stat`. Report mode prints physical memory, bytes free, swap used, the RSS of
**this process tree**, and a verdict `OK / TIGHT / DANGER`. Wrapper mode launches a
command, samples its tree, and kills **only that subtree** when a budget is crossed.
Two budgets, because two shapes fail differently:

* `--limit` - the whole tree summed. Right for a single heavy evaluation.
* `--proc-limit` - the largest single process. Right for a parallel build, which
  legitimately sums to a lot while no one worker is dangerous.

**Scoping is by process tree, never by process name.** An earlier watchdog summed every
process named `lean` and charged this session for two unrelated `lean` processes already
running on the host (~660 MB each). The guard walks the `ppid` closure from a pid it owns,
so foreign work is neither counted nor killed.

### Measured baseline on this host (32 GB physical, 10 logical CPUs)

Never measured before; every future budget is set against these rows. All three are the
guard own output, tree-scoped, nothing else running.

| run | peak tree RSS | largest single process | wall |
|---|---|---|---|
| `lake build` warm (5154 jobs replayed) | **0.74 GiB** | 754 MiB (`lake`) | 2.4 s |
| `lake build` cold: all 107 `Midfall` modules recompiled, deps cached | **16.86 GiB** | 4.28 GiB (`lean`, kernel maxrss) | 112 s |
| `scripts/checks.sh` (all 13 sections) | **4.94 GiB** | 4.27 GiB (`lean`) | 480 s |

**The cold-build row is the one that changes behaviour.** An ordinary cold build of this
project own modules - no `native_decide`, nothing exotic - already sums to 16.86 GiB
across ten concurrent `lean` workers, the same magnitude as the number that took the
host down. The difference is shape, not size: a build is ten processes at 2-4 GB each for
two minutes, while both crashes were ONE process climbing alone. Consequences:

* `--limit 6G -- lake build` would kill a cold build at 16.86 GiB. For a build use
  `--proc-limit 6G --limit 24G`; for a single heavy evaluation the tree budget is the
  right one. The default `--limit 6G` is chosen for the crash signature, not for the
  build, and that is why `checks.sh` only *reports* against it.
* a package adding a per-unit `native_decide` is adding to 16.86 GiB, not starting from
  zero, if it runs alongside a cold build.
* a warm `lake build` costs 0.74 GiB and 2.4 s, so wrapping the routine build is free.
* `checks.sh` at 4.94 GiB tree / 4.27 GiB single means the shipped gate already sits
  just under a 6 GiB budget with ~1 GiB of margin. That margin is the number to watch.

### Why the gate line is a report and not a gate

`checks.sh` prints one memory line and cannot fail on it. A memory report that reddens a
green tree teaches people to delete the report; enforcement belongs to whoever wraps the
run, where the budget was stated deliberately. The line costs 0.07 s per call; the gate
ran 480 s before the line was added and 451 s after it - the difference is KAT-section
variance, not the report - and it exits 0 whatever it finds (`|| true` covers even a
broken guard).

### Non-vacuity of the tool itself (D-P23 / R-41 applied to tooling)

A guard that has never been observed to fire is decoration. `ram_guard.sh --selftest`
demonstrates three things and is re-runnable:

1. a runaway climbing past a 300 MB budget inside the tree **is killed** (exit 137);
2. a well-behaved child under budget **passes untouched** (exit 0);
3. a foreign allocator outside the guarded tree **survives** - the mis-crediting
   regression test, which a name-matching watchdog would fail.

**Demonstrated on real workloads, not just a toy allocator:**

* `lake env lean Midfall/Lowering/RunEmitted.lean` under `--proc-limit 1G` - **killed,**
  exit 137, "single-process 1.81 GiB > proc-limit 1.00 GiB", the whole 3-process tree
  (lake + lean + worker) died, nothing outside it touched.
* the SAME command under `--proc-limit 6G` - **passed untouched,** exit 0, peak tree
  2.81 GiB, largest single `lean` 2.15 GiB, kernel maxrss 2.17 GiB. That last number
  independently confirms the 2.34 GB the `RunEmitted.lean` header claims: the guard
  measures what the comment asserts.
* `lake build` under a 6G budget - passed untouched, exit 0, peak tree 0.74 GiB.
* a 4 GB runaway killed at a 1 GB budget while a 670 MB bystander outside the tree grew
  undisturbed.

**Recorded failure mode.** Sampling is not tracing: a spike that starts and ends between
two polls survives the guard. `--kernel` closes that gap for the largest single process
by reading the kernel own maxrss, and the measured kill latency at a 0.2 s poll was under
one sampling interval plus the grace period. A run that can OOM the host inside 200 ms is
not caught by any sampler; both recorded crashes climbed over minutes and are caught.

## D-P32 (ADOPTED, round 102): the baseline is pinned to `2d52f24`; drift on `main` is a known divergence

**Decision (human).** `formal-baseline-v1` stays pinned to the commit it forked from. The
divergence is **recorded, not reconciled now**, and reconciliation is deferred.

### The fork point, verified

`git merge-base formal/baseline origin/main` = **`2d52f24426ceafed7c663b3ef6372d38a0128fec`**
(`2d52f24`, "Merge pull request #15 from EYBlockchain/id_point_fix"). `origin/main` is now
`33281c5` (PR #18, `midfall-cleanup`) — **25 commits ahead** of the fork.

### Why this is material, not cosmetic — measured

The drift is **not** confined to Rust-side clean-up. Across `templates/` and `src/`:

* **10 of 10 `.yul` verifier templates changed** — i.e. **every partial the AST emitter is
  ported from**:
  `QuotientHelpers.yul`, `QuotientNumeratorBlock.yul` (±235), `AccumulatorHelpers.yul` (±122),
  `AssemblyHelpers.yul` (±110 — this is where `batch_invert`, `scalar_inv`, `squeeze_to` live),
  `FinalPairing.yul` (±21), `Lagrange.yul` (±28), `QuotientAndLinearization.yul` (±42),
  `TraceReturn.yul` (−15), `TranscriptProofParser.yul` (±10), `VkLoading.yul` (±17).
* **`Constants.sol` ±96** and **`PrecompileSmoke.sol` ±174** — the Solidity wrapper, which
  D-P30 keeps as text with the line normaliser.
* **The generator `src/` changed**: `api.rs`, `render.rs`, `artifacts.rs`, `calldata.rs`,
  `proof.rs`, `diagnostics.rs`, `mod.rs`, `lib.rs`, `evm.rs`.
* Named behaviour changes: **`46d28d2` checks the quotient certificate hash on-chain** (changes
  the contract), **`7a363e0` reports point-pair word count on trailing inputs** (changes
  verifier behaviour on malformed input — exactly the `assertEmpty` / trailing-bytes territory
  the codec lemma depends on), `f429456` re-models fewer-point-sets and single-h-commitment
  proof sizes.
* Overall diff stat: 56 files, +1204 / −18928 (the deletions are largely the removed May IVC
  fixtures and Moonlight demo scripts).

### What is therefore pinned, and for how long it is trustworthy

| artifact | pinned to |
|---|---|
| `formal-baseline-v1` tag | `df7e607` on `formal/baseline`, whose Rust reference is `2d52f24` |
| golden `.sol` / `.yul` artifacts and the 9 provenance pins | `2d52f24` |
| the regenerated poseidon fixture (2,640 B) | `2d52f24`, features `evm,rust-verifier-trace` |
| the 30 tracked baseline SHA pins | `2d52f24` |
| **every AST emitter in `GenAst*.lean`** | the `2d52f24` template text |

**The port is faithful to `2d52f24`. It is not currently a port of `main`.** Every statement,
gate and KAT remains internally consistent — the gates compare the emitter against the pinned
templates, so nothing is *wrong* — but the deployed contract on `main` has moved.

### Consequences to carry until reconciliation

1. **Do not claim the formal artifact verifies the `main` contract.** It verifies the `2d52f24`
   contract. Phrase every result accordingly.
2. **Reconciliation will not be a rebase.** It requires: re-porting the ten changed templates,
   re-running M0 (the fixture may change size or content under `f429456` and `46d28d2`),
   re-pinning the golden artifacts and the 30 baseline SHAs, and re-checking every `stmtsBeq`
   gate against the new template text. Budget it as a milestone, not a merge.
3. **New work should keep targeting the pinned baseline.** Proofs about `verifyNative`, the
   transcript and the lowering are statements over the pinned model and stay valid; only the
   *template-text* layer is pinned.
4. **If `main` moves further, the drift grows.** Re-check
   `git diff --stat formal/baseline..origin/main -- proofs/solidity-verifier/templates`
   periodically rather than assuming `2d52f24..33281c5` is the whole gap.

### Deferred, not dropped

Reconciliation is a **future milestone**. It is not blocking the current proof work (section Q,
the codec lemma, the `Bridge` step lemmas), and nothing in the current queue depends on the
newer templates. Recorded here so the choice is explicit rather than drift nobody noticed —
which is the same failure class as the stale poseidon fixture that cost M0 a package.

## D-P34 (DECIDED by the orchestrator, round 113): do NOT assume the r-torsion count — derive it from a cyclic subgroup

**Choice: derive, with a named assumption only as a documented fallback.**

I had been telling the human this was research-grade and needed an assumption. **That was
wrong.** `PrimeOrderWith G₁ p` is `Nat.card G₁ = p` (noted at `Eip2537.lean:230`). The
research-grade statement is about the **full r-torsion subgroup** `E(Fp)[r]`. Nothing requires
`G₁` to be that subgroup. Taking `G₁ := Subgroup.zpowers G` for the standard generator:

```
Nat.card ⟨G⟩ = orderOf G
orderOf G = r     from:  r • G = 0,  G ≠ 0,  r prime
```

Elementary group theory. **And `r • G = 0` is already computed in the tree** — P-CURVE's
`g1GenFrame_valid` (`Bls12_381G1.lean:217`) is a kernel `decide` of exactly that, by the same
affine double-and-add the precompile model uses.

**Rationale for choosing derive over assume:** every assumption we avoid is worth more than the
same assumption made early. The trusted base already carries the pairing, the EIP-2537
semantics, `p = r`, and the solc hop; adding a fifth when the fourth was unnecessary would have
been a permanent cost for a temporary convenience. If the derivation fails, the failure is
recorded with its cause and the assumption can be revisited **with a reason** rather than as a
default.

**Instruction issued:** P-HOLDS2 was told mid-flight to attempt the derivation and to report a
concrete failure mode rather than silently falling back. Watch for the codec-direction subtlety:
`g1Valid` quantifies over every `Q : G₁`, so the codec must be defined on the subgroup and
`g1Add` must land back inside it.

## D-P35 (DECIDED by the orchestrator, round 113): widen the world projection rather than narrow the evaluator

**Choice: introduce a named `CalleeView` = the `CallWorld` fields plus `address` and
`keccakOf`, and state `rel_worldLocal` against that.**

P-BRIDGE proved `Evaluator.rel_worldLocal` is **false as stated**, with no axioms at all:
`calleeState` (`Bridge.lean:797`) reads `st.env.address` and needs `env.keccakOf`, but
`CallWorld` (`vendor/.../EVMExec.lean:445`) has exactly 11 fields and contains neither. A
runtime that calls `caller()` or `keccak256` separates two states the hypothesis declares
equal.

**Why widen rather than narrow:** the evaluator genuinely needs `keccakOf` — the transcript *is*
its job — so "stop `calleeState` reading those fields" is not available. Widening is a
**stronger hypothesis on callers**, and it is trivially satisfiable: within one contract
execution the address and the hash function do not change. So it costs nothing real.

**Why a named projection rather than bolting two fields onto the existing relation:** the defect
was that a projection silently under-described what the callee reads. A named `CalleeView`
makes the gap a **structure** rather than a comment — the next field `calleeState` learns to
read must be added there or the statement goes false again, and a false statement is what we
just spent a package discovering.

**Consequences to carry:**
* `honestCalls_worldLocal` becomes applicable to the honest fold once `Evaluator.rel` is
  restated against `CalleeView`.
* **`attack.md` line 36's FIX does not hold for the evaluator slot as sketched** — a
  plan-level correction, not a local one. Recorded here so the plan and the code do not
  silently disagree.
* Any other `rel_*`-style hypothesis built on `CallWorld` should be audited for the same
  under-description; this class — *a projection that quietly omits a field the code reads* — is
  a sibling of the vacuity class and is probably not unique to this one hypothesis.

## D-P36 (DECIDED by the orchestrator, round 114): assume `AdmissiblePairing` on the exhibited real groups

**Choice: named hypothesis, not a constructed pairing.**

P-HOLDS2 identified this as the **one** remaining human decision, and it is genuinely about the
pairing — not about point counts, which D-P34 retired.

Two options:
* **(a) Assume** `AdmissiblePairing G₁ G₂ Gₜ` for the exhibited real groups, as a named
  hypothesis in `Assumptions/`.
* **(b) Construct** Fp12 and a real ate pairing in Lean.

**(b) is genuinely research-grade.** mathlib has no pairing implementation at all, and building
Fp12 + a provably-bilinear non-degenerate pairing is a project larger than this one. Unlike the
torsion count, where I mistook an elementary fact for research, **this one really is out of
scope** — the difference is that `pairingProductOf` has already shown we do not need any
*properties* of the pairing beyond `P.e` existing and decidable equality on `Gₜ`.

**Why (a) is right rather than a shortcut:** D-P1 already established the design principle —
statements are quantified over `AdmissiblePairing` precisely because no Lean library has
BLS12-381, and "if bilinearity or non-degeneracy is unproven, it becomes a named hypothesis".
The verifier's *spec* is written against the assumed pairing; the `Holds` clause is about the
**precompile agreeing with that assumed pairing**, and `pairingProductOf` proves that agreement
by definition. So assuming the class does not weaken any claim we are trying to make — the claim
was always relative to an admissible pairing.

**Conditions attached:**
1. The hypothesis must be **named and gate-enforced**, not a bare `sorry` — same policy as every
   other gap in this project.
2. It must be recorded as **the single pairing assumption in the trusted base**, listed alongside
   the EIP-2537 semantics, `p = r`, and the solc hop.
3. The exhibit must state explicitly that it assumes the pairing **and** derives everything else
   (group law, order, precompile agreement) — so the assumption is one line, not a shield for
   work not done.

**Consequence for the human-decision list:** the torsion count is struck entirely (D-P34), and
this decision is now taken. **Nothing on the critical path to `lowering_equivalence` is waiting
on a human any more** — what remains is construction: `modexpInv_correct` → the agreement
theorem → `g1Add`/`g1Msm1`, plus a G2 frame codec for `g2Valid`.

## D-P37 (ADOPTED, round 115): estimates are recorded with their actuals, and revised in public

**Decision (human, round 115): "continuously refine the estimates/ETA for the milestones as you
complete sessions."**

Implemented as **`docs/ETA.md`**, a living ledger rather than a number quoted per report.

**The rule:**

1. Every package completion, the orchestrator records in `docs/ETA.md`: what was **estimated**
   before the package, what **actually** happened, and the **variance**.
2. Milestone estimates carry a **confidence** and a stated reason for it, not just a range.
3. **Revisions are visible.** When an estimate moves, the old number stays in the calibration
   table with its lesson. Silently replacing a bad estimate with a good one destroys the only
   evidence that would make the next estimate better.
4. **Errors of kind are logged separately from errors of degree.** The ledger's most useful
   column is not the size of the miss but the reason: of seven recorded items, **four were errors
   of kind** — a blocker recorded as large when it was a different shape entirely, almost always
   because a premise was inherited rather than re-verified.

**Why this exists rather than just "estimate better":** the project's estimates have been wrong
in a consistent direction and for a consistent reason. `pairing2` was called blocked on a
pairing implementation three times and was one definition. The r-torsion count was called
research-grade and was two elementary lemmas. `Array.foldl` transfer was called impossible and
the lemma existed under a synonym. A single point estimate hides exactly this pattern; a ledger
exposes it.

**Current headline, recorded so a future revision is visible:** **18–31 sessions to the landmark
`lowering_equivalence`**, revised **up** from 17–27 because the earlier figure counted only
packages that closed a sorry and ignored the 0-output sessions. 6–12 calendar weeks, dominated
by uptime rather than difficulty.
