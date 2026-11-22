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

### D-P38 - follow Fable's plan for M8: build the two missing prerequisite files, do not assume the hop

**Human decision, this session.** R-65 established that `IRCheck.lean` and `ShellModel.lean` are named
as required deliverables in `docs/PLAN.md` §7 and neither exists; `ir_refines` was transcribed
faithfully but its hypothesis cites `Surface.irCheck`, a decidable placeholder introduced by R-60 S1
for an unrelated reason. `M8-SCOPE.md` had recommended option (A) — name the solc hop as a trusted-
base assumption — and dismissed (B) as unestimable. That recommendation is **withdrawn**: it treated
our omission as a design choice.

**Fable's spec, verbatim:**
- `ShellModel.lean`: "a Yul model of solc's dispatcher for `verifyProof(bytes,uint256[])`, covering
  selector `0x1e8e1e13`, the callvalue check, ABI bounds checks, and binding the locals `vk` and
  `quotientEvaluator` from immutables."
- `IRCheck.lean` is a **verified checker**: `irCheck ir L = true → ObsEquiv ir (ShellModel.wrap L)`.
- P11 index row: `irCheck` = **"α-equivalence modulo constant substitution and solc renames,
  fuel-based"**; `ir_refines` = **"view-level simulation"**; falsification requirement = **"planted
  rename must fail `irCheck`"**; cost = **unestimated**.

**Consequences.**
1. **No new trusted-base row.** The only assumption left is the genuinely external one — solc's
   optimizer hop from `ir` to deployed bytecode (DECISION 1). The `ir` ↔ shell relation becomes a
   theorem, which is what Fable asked for.
2. **`ShellModel.lean` also closes the `shell_unfolds` gap** — the wrong-selector calldata that
   reverts in the artifact but runs the verifier in our model. One file, two problems.
3. **`irCheck` must be rebuilt to Fable's definition**, not patched: α-equivalence modulo constant
   substitution and solc renames, fuel-bounded. Note the tension with `IrCheckBlindness.lean`: a full
   alpha-rename currently PASSES `Surface.irCheck`, and Fable wants alpha-equivalence to pass — so
   the blindness finding is partly *consistent* with the spec. What must fail is a **planted rename**
   (one that changes which local a name binds to), and what must be proved is the `ObsEquiv`
   implication. `IrCheckBlindness` should be re-read against this distinction rather than treated as
   a refutation of the whole approach.
4. **Revised M8 cost: 6–12 sessions**, replacing 8–16. Fable marked it "unestimated"; this is our
   estimate, and it should be re-cut after `ShellModel.lean` lands.

**Standing lesson.** When a plan names a file and a property, **check the file exists** before
treating a same-named function elsewhere as its fulfilment. This is the third distinct way a recorded
premise has failed: R-63 was an unsatisfiable statement, R-65's predecessor was a false annotated
reason, and this is a silently substituted deliverable.

## Q-OPEN-1 — awaiting human decision: Fable's `irCheck` relation is too narrow for solc's output

**Raised:** round 147, after P-M8-IRCHECK (`e8fe473`). **Blocks:** M8's headline obligation
`ir_refines`. **Does not block:** M-C (running), M-B, the model track.

### The measurement

`IRCheck.lean` landed with `irCheck_sound` proving Fable's stated `ObsEquiv` conclusion unchanged.
But **the pinned artifact cannot satisfy the checker's hypothesis**, and this is a property of
`irCheck`'s *definition*, not a bug:

- solc duplicates every binding through a fresh temporary — measured in the artifact:
  `let _2 := loadimmutable("5"); let expr_287 := _2; let var_vk_286 := expr_287`, where the model
  has **one** binding.
- the artifact routes every abort and arm through **declared helpers**
  (`shift_right_224_unsigned`, `revert_error_42b3…`, `external_fun_verifyProof_291`,
  `allocate_unbounded`, `solc_abi_decode_tuple_…`) where the model **inlines**.

> **An inlining is a simulation, not a rename.**

`artifact_alpha_self = TRUE` (the artifact's own dispatcher head α-matches itself), so the matcher is
not broken — the shape difference is real. `artifact_verdict = mismatch`, first divergence at the
dispatcher's third statement.

### Why Fable's spec has this limit

`PLAN.md` §7 line 228 requires a *decidable* checker implying `ObsEquiv`. α-equivalence modulo
constant substitution and solc renames (P11 row) was a guess at how coarse a decidable relation
could be. The measurement says it is **too fine**: it can never fire on real solc output.

### The three options

| | option | cost | risk |
|---|---|---|---|
| **1** | **Coarsen the checker** to a decidable simulation handling inlining and binding duplication | 3–6 sessions | deviates from Fable's wording; a coarser decidable relation is harder to prove sound |
| **2** | **Make the model match solc's shape** — declared helpers, duplicated bindings | 1–2 sessions | the "model" becomes a copy of the artifact and stops modelling anything |
| **3** | **Keep α-equivalence**, accept `ir_refines` unprovable for the artifact | 0 | leaves M8's headline obligation permanently open |

**Orchestrator recommendation: option 1**, because Fable's *intent* was a decidable sufficient
condition for a behavioural relation, and α-equivalence was a guess at its coarseness that the
evidence now refutes. **Option 2 is a trap** — it would make the theorem true and the model useless,
which is the vacuity failure class this project has measured twenty times.

**Not decided unilaterally** because it redefines a named deliverable in the plan. Until it is
decided, M8's remaining work is: α-transport lemma (1–2 sessions, needed under every option), then
the run leg (2–4), then whichever body relation option 1/2/3 implies.

### D-P39 (ORCHESTRATOR DECISION, human delegated) - `ir_refines`: specify the constant-inlining embedding

**Chosen: option (iii), implemented as a specified inlining transform in Lean.** The emitted Yul
is a *fragment* whose free identifiers are the Solidity wrapper's `uint256 internal constant`
declarations. In the real build, **solc inlines those constants at every use site**, inside
function bodies as well as the top level. So the embedding is not an invention - it describes
what the reference pipeline does.

**Decision:**
1. Define `inlineContractConstants : List (String x Nat) -> YulBlock -> YulBlock` in Lean -
   substitute each contract-level constant's literal at every *use site*, **including inside
   `funDef` bodies**, threading parameters so a shadowing binder is not substituted. Values
   come from the same table `RunEmitted.shellLets` already uses - no new numbers.
2. `RunShell`'s program becomes `inlineContractConstants consts (armBody S)`. **A signature
   change to a sketched definition, permitted because the sketched form is false as written**
   (`runShell_curveSurface_empty`).
3. `shell_unfolds` restated to the ARM form in the same commit, fingerprint registry moved
   together (D-P27). `Surface.lean:257-261` already assigns that restatement.

**Rejected:** (i) changing the Rust emitter - it would break M3's golden AST equality against a
reference that emits Solidity-with-declarations. (ii) an unbounded closure transform - invents
semantics the reference lacks. **Test of this decision: after inlining, `RunShell` must be
inhabited.** If not, the embedding is wrong and this is revisited.

### D-P40 (ORCHESTRATOR DECISION) - `identityCorrespondence_of_bridge`: add the fourth hypothesis

P-QVM proved the three sketched hypotheses pin `exprs`' **first** projection (bucket tag) while
the conclusion needs the **second** (value), and nothing pins it - the statement is false as
written, with both halves landed as counterexample theorems.

**Decision: add the missing hypothesis** - the verifier-side value of each `exprs` entry equals
the QVM-side value the bridge is about. This strengthens the hypothesis set and narrows the
claim; permitted because the alternative is a false theorem. Record in `P-SE-statements.md` as
a deviation from the sketch with the counterexample theorems as evidence.

### D-P41 (ORCHESTRATOR DECISION) - `readScheduleAgrees`: require Surface coherence

P-SCHED refuted the field at the deployment: the fixture's `vk` has an 8-read schedule while its
`plan` is the 72-slot poseidon layout. `Surface.vk` and `Surface.plan` are independent free
fields with nothing relating them, so the field is not derivable and is false at the only
exhibited pair.

**Decision: add a `Surface` pin requiring `vk` and `plan` to come from one render** - a
coherence condition, not a slot-equality assertion. `readScheduleAgrees` then becomes derivable
from coherence plus the existing decode lemmas rather than a bare hypothesis.

**Consequence, and it is the real cost: the fixture is incoherent and must be rebuilt** so its
`vk` and `plan` derive from one render. That is a genuine finding, not an obstacle - an
incoherent fixture is why the mismatch was invisible. The P-SCHED repair already changed the VK
hash and every derived challenge stream, so this is a second fixture change of the same kind.

**Rejected:** deleting the field, or weakening its conclusion to the 8-slot schedule. Both would
hide a real vk/layout disagreement.

### D-P42 (DECIDED by P-DET, from P-INLINE's evidence) - `ir_refines`: the right-hand side should have been `wrap`, and `RunShell` is a DIFFERENT program

P-INLINE found that `RunShell` (bare arm) and `ShellModel.wrap` (dispatcher) disagree on empty
calldata, and named a fork: **F1** - make `Surface.shell` BE the dispatcher, so the two sides run one
program; **F2** - accept that they are different programs and restate the field's right-hand side.
P-DET decides **F2**, and the reason is that F1 is both unimplementable and self-defeating.

**THE DIFFERENCE IS CONSTRUCTIVE, NOT ACCIDENTAL.** `RunShell S W H cd c g` runs
`S.shell.codeBlock` from `callState W S.shellLayout H cd`; `wrap` runs
`ShellModel.dispatcherCode S = prologue ++ [cond calldatasizeTest [selectorDecl, selectorSwitch
(armBody S)], revert00]` from the same frame. The shell has NO ENTRY PATH: no `memoryguard`
prologue, no size test, no selector switch, no fall-through abort. On a calldata shorter than four
bytes the dispatcher's size test skips the switch entirely and falls through to `revert(0, 0)`,
while the bare arm's first executed non-definition statement is the VK gate, which fails and
reverts with a four-byte selector. `RunShellInhabited.shell_run_is_not_the_wrap_run` pins the
payload difference and `RunShellInhabited.ir_refines_refuted_at_curveSurface` - UNCONDITIONAL since
P-DET closed `Bridge.dialect_deterministic` - turns it into `not ObsEquiv`. So this is not a
modelling slip that a better fixture would repair: the two relations are about two different blocks.

**F1 IS NOT EVEN EXPRESSIBLE AS A PIN.** `ShellModel` imports `Midfall.Lowering.Surface` (it needs
`Surface`, `ExecEnv`, `Hash`, `Bytes` to state `wrap`), so a `Surface` field that pointed at
`ShellModel.dispatcherCode` would close a cycle. The cycle is STRUCTURAL, not an import-ordering
accident: the dispatcher model is defined in terms of the record it would have to live in. Nothing
in `Surface.lean` can name `dispatcherCode`, so there is no pin to write - which is why D-P39's
embedding went the other way and pinned `shell.codeBlock` to the ARM instead.

**F1 WOULD ALSO DESTROY THE FIELD.** `ir_refines` exists to say something non-trivial: that the
via-IR artifact refines the hand-written shell model. If the shell model WERE the dispatcher, the
two sides of the equivalence would be one program and the field would be `ObsEquiv R R` - a
tautology wearing a theorem's clothes. The distinction the field tests is precisely the distinction
between an imported solc object and the modelled entry path, and F1 deletes the second term.

**CONSEQUENCE, and it is the substantive part of the decision: `ir_refines`'s right-hand side should
have been `wrap` all along.** That is exactly what P-LOWEQ already did to the headline:
`lowering_equivalence` concludes about `ShellModel.wrap S W H cd ...` and reads `hc.ir_refines` at
`ShellModel.modelIr S`, whose runtime sub-object IS `dispatcherCode S`
(`ShellModel.wrap_iff_modelRunContractIR`). So the headline is stated at the pair that can be
equivalent, and the registered field - whose right-hand side is `RunShell` - is refuted at the curve
Surface by a difference that is a specification artefact and not a lowering bug.

**AND IT IS UNAVOIDABLE, NOT A PREFERENCE, BECAUSE THE FIELD IS NOW REFUTED - NOT MERELY UNPROVED.**
`ir_refines` quantifies over EVERY `ir` with `S.irCheck ir = true`. `ShellModel.modelIr curveSurface`
passes that check by proof (`modelIr_irCheck`), and at that single instantiation the conclusion is
FALSE. Therefore `LoweringCorrect curveSurface product` has NO INSTANCE FOR ANY `product` - landed as
`RunShellInhabited.curveSurface_not_LoweringCorrect`. That is the conclusion P-RUNSHELL reached from
shell EMPTINESS and P-INLINE retracted along with six other theorems when D-P39 made the shell
inhabited; it is now back on a better-founded route, because both sides HAVE runs and they disagree.
So the honest summary of P-INLINE plus P-DET is: **the curve Surface cannot discharge
`LoweringCorrect`, not because its shell is empty (that was fixed by D-P39) but because `RunShell` and
`wrap` differ BY CONSTRUCTION on unroutable calldata - the field as sketched compares the wrong two
things.** Restating its right-hand side to `wrap` is therefore not one option among two; it is the
only consistent reading, and F1 is not available at all.

**HOW THIS DECISION CAN BE FALSIFIED, stated so the next package can attack it rather than trust it.**
D-P42 stands or falls on `ir_refines_refuted_at_curveSurface`. Three findings would overturn it: (i) a
proof that `RunShell curveSurface` and `wrap curveSurface` DO have a common view at some frame where
the calldata routes, which would make the disagreement an artefact of the empty calldata rather than
of the entry path; (ii) a demonstration that `curveSurface.shell.codeBlock` was itself mis-pinned, so
that the shell SHOULD carry the dispatcher and the pin - not the field - is what is wrong; or (iii) a
route to `LoweringCorrect curveSurface product` that does not need `ir_refines`, which cannot exist
since it is a structure field, so (iii) would in fact be a change to the field list. (i) is the live
one: the refutation is at the UNROUTABLE input, and a routed-calldata refutation or agreement is what
would decide whether the mechanism generalises.

**WHAT WAS NOT DONE, deliberately.** `LoweringCorrect.ir_refines` was NOT edited. Restating its
right-hand side from `RunShell` to `wrap` is a change to a frozen obligation-bundle field, and the
refutation above is the evidence that the change is needed - not authority to make it silently.
The field stays as registered, stays refuted at the exhibited Surface, and the orchestrator decides
whether to restate it. `curveSurface` therefore cannot be a `LoweringCorrect` instance as long as
the field keeps `RunShell` on the right: that is what the refutation means, and it is reported
rather than repaired by editing the statement.


**ADDENDUM - D-P42 TESTED BY P-RUNLEG (the falsifiability paragraph executed).** The routed-calldata
attack this decision named as item (i) has now been run, and the answer is SPLIT, so the decision is
amended rather than overturned. `RunLegRouted.ir_refines_refuted_at_curveSurface_routed` refutes
`ir_refines` at `curveSurface` on a calldata the dispatcher DOES route (`ShellModel.cdWellFormed`,
228 B, `bytesTake cd 0 4 = some fnSigVerifyProof`, all sixteen entry-path tests passing at the
deployment frame), so the disagreement is NOT an artefact of the empty calldata and D-P42 stands.
But the mechanism D-P42 recorded is the mechanism of the UNROUTABLE input only:
`RunLegRouted.wrap_routed_uninhabited` proves that on routed input `wrap curveSurface` has **no
observation at all** - the dispatcher enters the arm and gets stuck at the VK gate, because
`ShellModel.armBody S = S.L.headGuard ++ S.bindLocals ++ S.L.main` is the UN-INLINED fragment and
its contract-level constants `EXPECTED_VK_LENGTH`/`EXPECTED_VK_CODEHASH_WORD` are bound by nothing
in the entry path (`bindLocalsFromImmutables` binds `vk` and `quotientEvaluator` and nothing else).
So there are TWO mechanisms, and `RunLegRouted.the_two_mechanisms_are_distinct` states the
inhabitation pattern that separates them: at the empty calldata both sides run and their halt
PAYLOADS differ (zero bytes against four); at the routed calldata the shell runs and the model side
is empty. The control settles which half of the entry path matters: the dispatcher over the CLOSED
(inlined) arm reverts with the same four bytes as the bare arm (`control_of_arm_block_run`, plus the
interpreter gate `routed_comparison_ok`), so the prologue, the size test, the switch and the thirteen
ABI bounds tests contribute NO halt of their own. **CONSEQUENCE FOR THE RECOMMENDATION, AND IT IS A
CORRECTION: F2 does not repair anything at `curveSurface`.** Restating `ir_refines`'s right-hand
side to `wrap` would swap a side that disagrees for a side that is empty on routed input, and
`gap_runLeg_unexhibited` would survive the restatement. The repair the evidence points at is to make
the model's arm the closed program - which is what D-P39 declined to do when it restated the pin - and
that is a statement change requiring its own decision (D-P43, orchestrator's to write). Nothing was
edited here: `ir_refines`, `ShellModel.armBody`, `RunShell` and `wrap` are untouched.
`ir_refines_refuted_at_the_imported_artifact`, retracted by P-INLINE and never re-established, IS
back: `RunLegRouted.ir_refines_refuted_at_the_imported_artifact`, at the real solc artifact,
unconditionally, with both sides inhabited and each side's view unique.

### D-P43 (ORCHESTRATOR DECISION) - close the model arm: armBody must be the inlined program

Prompted by P-RUNLEG. wrap_routed_uninhabited proves the model side has NO OBSERVATION AT ALL on routed
calldata, because ShellModel.armBody S is the un-inlined fragment.

Why this is mine to decide: D-P39 explicitly declined to touch armBody, on the grounds that changing it
would change ShellModel.wrap. P-RUNLEG shows that was backwards - changing it is exactly what is
required, and the control proves the entry path is innocent: the dispatcher over the CLOSED arm reverts
with the same four bytes as the bare closed arm.

Decision:
1. ShellModel.armBody S := armProgram S - the inlined, closed program. Contract constants are already
   inlined by D-P39's transform; the two locals are already bound by bindLocals. Nothing new is
   invented - the same embedding applied one place further out.
2. Restate every pin citing armBody in the same commit, fingerprint and duplicate-fact registries moved
   together (D-P27). Expect the FrameWalk and FrameWalkWitness theorems to need re-checking, since the
   block they walked changes.
3. Then re-run the routed comparison. Both outcomes are informative:
   - Agree: M2 is gone, ir_refines is no longer refuted that way, and F2 becomes live on its merits
     rather than as a repair.
   - Still disagree: the cause is the ABORT ENCODING - the artifact revert_error is revert(0,0), zero
     bytes, while the emitted fail(sel) is revert(0,4). Name it and stop; that is D-P44 decision.

Evidence this is the right repair: P-RUNLEG perturbation P4 - extending the locals to bind
EXPECTED_VK_LENGTH and EXPECTED_VK_CODEHASH_WORD makes gate_no_stmts no longer apply. The repair was
simulated at the environment before being made in the spec.

Also fixed: RunShellInversion.lean lines 27-32 still say curveSurface.bindLocals is empty and list vk as
free. Since D-P39 it is shellLocalLets and the free names are the 59 contract constants. Stale prose is
a false premise waiting for the next agent.

Falsifiability: D-P43 stands or falls on the re-run routed comparison. If the sides agree, M2 is gone.
If not, the abort encoding is the real mechanism and D-P43 was a partial fix - still progress, recorded
as such.

## D-P44 — **D-V2 (approved by the human via the `/goal` prompt): V2 scope decision**

> Recorded verbatim from `docs/plans/PLAN-V2.md` §2, per QUEUE T0.3.
>
> **Numbering note:** PLAN-V2 §2 expected D-V2 to land as D-P43, on the reasoning that P-DET took
> D-P42 and P-RUNLEG had only *reserved* D-P43 for an `ir_refines` edit that D-V2 makes moot. That
> reservation was spent before the cut-over: **D-P43 is already recorded above as the `armBody`
> closing decision** (commit `daf2243`), which was an executed v1 repair, not a reservation. D-V2
> therefore takes the next free number, **D-P44**. It supersedes D-P38, Q-OPEN-1, and the pending
> `ir_refines` edit that D-P42/D-P43 were working toward. Nothing in D-P43's content is invalidated —
> `armBody` closure is retired along with the rest of the `ir_refines` chain by clause 3 below.

1. **Object of the theorem:** the Yul of the two `verifyProof` assembly blocks as printed by the Lean
   text port (`Generator/Contracts.renderHalo2Verifier`), parsed by construction through the `GenAst`
   emitter and tied to the text by token equality (`CodegenAgrees`), with contract-level constants
   substituted (`Inline.inlineContractConstants`) — Solidity's own constant semantics.
2. **Trusted base:** delete the two solc rows of PLAN §1 (the "checked Solidity→IR" row and the
   "trusted optimizer" row) and add ONE row: *"Solidity entry semantics of the generated wrapper:
   `EntryFrame` (`LoweringV2/Statements.lean` §3) — selector routing, `view` ⇒ zero call value, ABI
   decoding only reads calldata, solc's free-memory prologue leaves `mload(0x40) ≤ TRANSCRIPT_MPTR`,
   fresh frame. Trusted; validated by the revm differential (M4), not in Lean."* Everything solc adds
   before the assembly can only revert, so soundness and two-outcomes do not depend on it.
3. **Retired** (stop work; keep building until WP-X6 deletes them): `LoweringCorrect`,
   `Lowering.lowering_equivalence`, `end_to_end_noAcc`/`end_to_end_acc_complete` (v1),
   `RunContractIR`, `Surface.irCheck`, `ir_refines`, `Yul/ImportSolcIR.lean`, `Yul/IRCheck.lean`,
   `Instances/ImportedIR.lean`, `Instances/IrCheckBlindness.lean`, `Instances/RunShellInversion.lean`,
   `Instances/RunShellInhabited.lean`, `scripts/gen_import_solc_ir.py`, `scripts/perturb_import_ir.py`,
   `Yul/solc-ir-*.yul`, milestone M8, P-DET. `Yul/ShellModel.lean` is kept only as raw material for
   optional WP-X5.
4. **Per-deployment first** (D-P24 stands). The claimed headline is
   `lowering_equivalence_poseidon (product : PairingProduct) :
   LoweringEquivalence poseidonRender product`.
   - It is stated for **every** pairing product. `LoweringEquivalence` already takes
     `Eip2537.Holds … product` as a hypothesis, so no pairing implementation is ever needed.
   - The one concrete product, `HoldsFinal`'s exhibited `poseidonProduct`, is used only for
     non-vacuity (`HypothesesInhabited`).
   - The ∀-render theorem is WP-X4.
5. **Trusted evaluation.** Decidable facts about the deployment (`poseidon_valid` clauses, codegen
   agreement, fixture KATs) may be closed by `native_decide`, only in `Instances/` (D-P17).
   - The headline's axiom list may therefore contain the compiler-trust axiom(s) `native_decide` adds.
     Q0.3 records their exact names in this toolchain.
   - A kernel-only re-check is optional, as WP-X8.

## D-P45 — **Approved (amended): repair the non-vacuity gate (R-72) — the witness must decode, parse and replay**

> Was QUEUE Q0.5, blocked on a decision. First recorded on 2026-11-17 as approved under a "standing
> delegation" the human did not give (W2); reclassified PROPOSED by the review. **Status: APPROVED
> AS AMENDED below.** Signed off: human (repository owner), 2026-11-17, in session after `4b525ef`
> (instruction "make best choices for remaining decisions"; choices drafted by the assistant for the
> human, see D-P53). The original proposal is kept below for the record; it is NOT what was approved.

**Approved text.** `HypothesesInhabited` (frozen, `Statements.lean:317` at `4b525ef`) gains two
conjuncts; the exact text may differ only in elaboration annotations (`(p := p)`, `(Gₜ := Gₜ)`):

```lean
def HypothesesInhabited (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr ∧ EntryFrame R W Lyt H cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ SoundSide R H cd ∧ CompleteSide R H cd ∧
      (∃ ms instW inst Snap,
        decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
        instOfWords? (p := p) instW = some inst ∧
        snapshotOf R.E H R.vk inst ms none = .ok Snap) ∧
      G1CodecLaws R.E.g1
```

**Why this and not `LeanAccepts`.** The new conjunct is exactly the antecedent chain of `SoundSide`
and `CompleteSide`, so at the witness both side conditions bite instead of holding vacuously, and
`gate_weak` dies (`sel_nondecode`: the bare selector never decodes). `LeanAccepts` was NOT adopted:
at any render whose SRS is a real setup, `verifyMsgs … = .ok ()` reduces through bilinearity and
non-degeneracy to a G1 equation `P₁ + s·P₂ = 0` between computed points, `s` the setup secret.
Proving it means computing with `s`, which KZG's binding assumption says no one can do, so the
conjunct could never be discharged at a real deployment and PLAN-V2:355's DONE test would be
unmeetable (F.2-G3 measured the witness NOT-COMPUTABLE). No run-existence conjunct either: it is
redundant given the headline (DECISIONS-PENDING §3).

**Stated limit, to go in the English statement.** Headline ∧ gate certify that the side conditions are
non-vacuous at a real calldata. They do NOT certify that some calldata is accepted at the deployment;
the protection against a Lean verifier that rejects everything is structural (`Valid.slots`, D-P46's
base pins after D-P55), not a witness.

**Original proposal (not adopted as written).** `HypothesesInhabited` (`Statements.lean:269`, frozen) is amended to require, in
addition to the existing conjuncts, **a calldata that actually decodes and a run that actually exists**:
at least `∃ ms instW, decodeCalldata … = some (ms, instW)` **and** `LeanAccepts R H cd`, plus a
run-existence conjunct. Rationale: the clause exists solely to certify the headline's hypothesis set is
non-vacuous, and R-72 showed it is satisfiable with no accepting calldata and no runs at all —
`SoundSide`/`CompleteSide` are themselves universals over `decodeCalldata = some`, and the bare
4-byte selector never decodes. **A gate that cannot fail is not a gate.** `PLAN-V2:355` makes this
clause part of the §6 DONE test, so leaving it weak would let a green gate certify nothing.

**Required of the repair, per the card's own acceptance: it must be demonstrated to have teeth** — the
probe `gate_weak` must NO LONGER type-check. A repair that merely compiles is not accepted.

**Consequence accepted:** this edits a frozen file and re-hashes `Frozen.sha256`. The freeze exists to
prevent silent change, not authorised change; the change is recorded here and the hash is re-pinned in
the same commit so the diff is auditable.

## D-P46 — **Approved (extended, sequenced): restore the VK base-slot pins v1 had and V2 dropped — all three, after Gap B**

> Raised by FP.0. **Status: APPROVED** with the review's extension. Signed off: human (repository
> owner), 2026-11-17, in session after `4b525ef` (see D-P45's note and D-P53).

**Approved.** One `Render.Valid` clause with three conjuncts, as drafted in DECISIONS-PENDING §4
(G1 base, G2 base, NEG_S_G2 base; G1 half spelled for V2 by the card):
`baseSlots : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip <G1 generator> ∧ vkG2Words R.pv vkG2BaseSlot =
R.encG2 (R.params.nG2Prepared)⁻¹ ∧ vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹`.
- **Sequencing.** It lands in ONE `Statements.lean` re-hash AFTER R.4 (D-P55). F.2-G2 measured the G1
  and G2_BASE halves already TRUE at the payload, but the NEG_S_G2 half is FALSE as modelled
  (`poseidonSG2 := g₂`); adding a clause known false at the deployment adds a refutation, not
  information. After R.4 the third half holds by `choose_spec`.
- **Same re-hash:** `Valid`'s "decided by computation" docstring (`Statements.lean:170`) gets the
  recorded exception: a clause may be discharged at the deployment by proof (as `vkPins` already is,
  and `baseSlots` will be), provided it is a fact about the render and not a semantic obligation
  about the program.
- **Then** `fp_finalPairing_contracts`'s `fpG2Slots R` hypothesis is discharged from `R.Valid`.

**Original proposal (two pins; extended above):** add the two clauses to `Render.Valid` §2, pinning `G2_BASE_MPTR` and
`NEG_S_G2_BASE_MPTR` in the VK payload to `encG2` of `params.nG2Prepared⁻¹` and `sG2Prepared⁻¹`.
**Rationale: this is not a new requirement — v1 already had it** as `VkSlotsAgree.g2BaseWords` /
`negSG2Words` (`Inv.lean:623-624`). V2's `Valid` has no `VkSlotsAgree` at all, so the check was
**dropped in the rewrite rather than considered and rejected.** `ec_pairing` copies its G2 arguments
from exactly those bytes, so without the pin nothing connects the staticcall's operands to the
verifying key. Restoring a dropped check is the low-risk direction: it can only make `Valid` harder to
satisfy, never easier, so it cannot make a false headline true.

`fp_finalPairing_contracts` currently carries `fpG2Slots R` as an explicit hypothesis; after this
decision that hypothesis becomes a derived consequence of `R.Valid` and should be discharged from it.

## D-P47 — **Approved (ratified after the fact): fix the fixture before porting the generator**

> Raised by D.3 and C.4. **Status: APPROVED — ratified.** Signed off: human (repository owner),
> 2026-11-17, in session after `4b525ef` (see D-P53). R.1 (run as "F.1", `2041977`) already executed
> it as a measurement card: Rust CAN export the constraint system, D.1's byte gate still passes, and
> `Valid` went to 8 proved / 4 refuted / 1 sorry. The same export-first rule now governs clauses 2/3:
> QUEUE R.8 probes whether the post-constructor PCS sizing can be exported before any WP-G4 port.
> Reproducibility of the export is D-P58.

**Decision: attempt to re-export the deployment fixture with the full constraint-system data BEFORE
any work to port `LoweringPlan::new`.** Rationale, three findings that point the same way:
1. The missing data (`gates`, `lookups`, `trashcans`, `permutation.columns`) **is present in the Rust
   generator's own output** — it is what produced the deployed verifier. It is absent from `vk.json`,
   which is an export choice, not an absence of the data.
2. **D.2 already proved the route works**: `Midfall.Generator.poseidonCtx` had zero lines in all five
   generated-code regions, so the pure `poseidonCtx` was **sliced from the verifier dump instead**,
   with a gate requiring the regions non-empty so the fallback cannot be silently load-bearing.
3. **D.3 found the bundle is not the committed fixture anyway** — `trace.json` `fixture_match` records
   `committed_proof_len 4752` vs `exported_proof_len 2640`, `proof=false`, `instance=false`. **A
   fixture refresh is needed regardless of the CS-data question**, and doing both at once is cheaper.

**Why this order matters:** porting `LoweringPlan::new` is a large GEN effort that reproduces in Lean
what the Rust side already computed and could simply export. If the export succeeds, C.4's clauses 1,
2, 3 and 8 — all one root cause — may close from data rather than proof. **If the export is shown
impossible, the port becomes the plan and this decision is revisited.** A NEGATIVE on the export is a
deliverable, not a detour.

**Not decided, deliberately.** Two open items are recorded as investigation cards rather than decisions
because guessing on them risks a soundness error, not a delay:
- **`Rejects`/`SoundSide` (C.2's finding).** Conjunct 3 of the frozen headline carries no `SoundSide`,
  while `Rejects` demands it. Dropping `SoundSide` from `Rejects` would make the rejection lemma a
  one-liner and cut the cone by 1 — but it would also assert rejection inside the logup-panic bad
  set, which has not been checked. **Investigate first; do not weaken a hypothesis to move a number.**
- **`g1CodecZ.ofCompressed? := fun _ => none`.** A real decode needs `X in zpowers g1`, a discrete log
  as literally typed, so it may be unfixable rather than unfinished. **Determine whether `end_to_end`
  is dischargeable at all while it is a placeholder** before choosing between retyping the codec and
  changing what `end_to_end` is about.

## D-P48 — **Approved: add the `RETURN_MPTR` pin to `Render.Valid` (same rationale as D-P46)**

> Raised by T.1, confirmed as load-bearing by M.1. **Status: APPROVED.** Signed off: human
> (repository owner), 2026-11-17, in session after `4b525ef` (see D-P53). Lands in Q0.5's single
> `Statements.lean` re-hash together with D-P45; F.2 measured `trRetMptr` PROVED at the deployment
> (`RETURN_MPTR = some 4096`), so the clause is discharged in the same card.

**Decision: add a `returnMptr` clause to `Render.Valid` §2**, pinning `∃ m, R.consts.lookup
"RETURN_MPTR" = some m` (the deployment value is 4096, present in `pinnedConstants`).
**Rationale, and it is the same argument as D-P46:** adding a clause to `Valid` can only make it
*harder* to satisfy, never easier, so it cannot make a false headline true. **And M.1 established this
is not optional:** `tr_blockProgress` requires `trRetMptr R`, so without it the TraceReturn row cannot
be discharged from `R.Valid` at all — the pin sits on the critical path to the hinge, not off in a
corner. `Valid` currently carries `transcriptMptr` only (`Statements.lean:169`), which is why T.1 hit
it and why the asymmetry exists: **progress asserts existence and so inherits a data obligation
soundness does not.**

## D-P49 — **Approved: gate `BlockSound`'s poisoned arm on `q ≠ .traceReturn` (S.1's §6 refinement)**

> S.1 asked for sign-off because this exceeds Q0.3's 'add fields to `Frame`/`Clean` only'
> convention, even though §6 is listed as refinable. **Status: APPROVED.** Signed off: human (repository owner), 2026-11-17, in session after the review merge `6481731`.
> Ratified after the fact: S.3 had already applied it (`d0aabba`). Its condition held there — the
> arm-free restatements landed as `tr_sound_clean_noarm`/`tr_poison_walk_noarm`, with no `sorryAx`,
> and every cone root was unchanged.

**Proposed decision: approve the §6 gate**, at `Blocks.lean:96-97` and `:100-101`:
  BEFORE  `∨ (o = .normal ∧ Poisoned R H vkAddr cd V' st')`
  AFTER   `∨ (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')`
**Why this is safe, and it is the same argument as D-P46/D-P48: it STRENGTHENS a hypothesis, never
weakens one.** `BlockSound` feeds `BlockContractsAt`, which is a *hypothesis* of
`lowering_equivalence_of_blocks`. Making a hypothesis harder to satisfy can only make the composition
harder to apply — **it cannot make a false headline true.** And S.1 verified sorry-free that the
strengthened claims hold at `.traceReturn`: `tr_sound_clean'` (clean → revert ∨ exitOk) and
`tr_poison_walk'` (poisoned → revert, always) both elaborate on `[propext, Classical.choice,
Quot.sound]`. **The arm is vacuous in the existing proofs — a hypothesis-strength gap, not a semantic
one.**

**Why not the §7 alternative.** Threading an extra `hlast` through `slices_seq_sound`,
`lowering_equivalence_of_blocks` and `end_to_end` spreads one local fact across three signatures and
leaves §6 stating something weaker than the truth. **The gate makes the shape honest at the place it
belongs:** at `traceReturn` a poisoned run genuinely cannot end `normal` — it reverts. Smaller, local,
and it does not leak into the headline's hypotheses.

**Rejected: option (a)** (add the arm to `slices_seq_sound`'s post). S.1 showed it would break the
frozen consumer — `LoweringEquivalence` conjunct 3 demands every permissive run satisfies
`view = returnView st₀ ∨ isRevertOrHalt`, and a normal fall-through is neither. **Recorded so nobody
retries it.**

**Scope condition on the card that applies it:** changing §6 invalidates the already-sorry-free
`tr_blockRow`/`fp_blockRow`, which cite `tr_blockSound` *with* the arm. **The card must repair them in
the same commit** from the arm-free restatements, and must show `cone_sorries` unchanged at every
existing root — a shape change that silently breaks a landed proof is the failure mode here.

## D-P50 — **Approved: add the six `vkLoading` pins to `Render.Valid`, and land S.8's proved deployment discharge**

> S.8 measured all six TRUE and PROVED them at the deployment, sorry-free. **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after the review merge `6481731`. Ratified after the fact: S.9 executed it (`fece4c7`) citing a delegation the
> human had not given (EXECUTION-V2 W2); the human has now approved the change as landed.

**Decision: add `vkPins` and `vkProgressPins` as fields of `Render.Valid` (§2), and land S.8's two
proved structure terms in `Instances/`.** Rationale:

1. **It is structurally required, not cosmetic.** `blockContracts_of_valid` takes `hR : R.Valid` and
   must yield a row for every `Partial`. S.4 established that `BlockSound R .vkLoading` is **false**
   without the pins. So if the pins are not reachable from `R.Valid`, **the hinge cannot be proved from
   its own stated hypothesis** — it would need extra hypotheses, which changes a cone member's
   signature and ripples into C.2's composition. Putting them in `Valid` is the contained fix.
2. **They are exactly the kind of fact `Valid` exists to pin** — 'this render is the generator's output
   for THIS verifying key'. A render whose VK window is not the table's VK window is not that render.
3. **They are proved, not guessed.** S.8 printed both sides of all six and constructed
   `vkPins poseidonRender` and `vkProgressPins poseidonRender` with **no `sorryAx`**. This is what
   distinguishes D-P50 from the guess I refused last round: **the evidence exists before the frozen
   edit, not after.** Same direction as D-P46/D-P48 — adding clauses only strengthens `Valid`, so it
   cannot make a false headline true.

**Cost accepted, stated plainly:** each pin is discharged at the deployment by `native_decide`, so
`poseidon_valid` will carry **six more compiler-trusted axioms** (`<decl>._native.native_decide.ax_1_1`
per pin, on top of the existing `poseidonModel_isOk` one). §6's DONE test permits 'the `native_decide`
compiler-trust axiom(s) that Q0.3 records', so this is within scope — **but the headline's trusted base
grows by six decisions, and STATUS must say so rather than bury it.** Discharges live in `Instances/`
(`check_frozen_axioms.py` probes only `Statements.lean`).

**What this does NOT fix, and the card said so unprompted.** True pins do not make
`poseidonRender.Valid` reachable — **C.4 refutes 6 of its 11 clauses** (`circuitMeta`, `layout`,
`invariants`, `codegen`, `slots`, `supported`). D-P50 removes the *guessed-premise* objection to the
hinge; it does not move `cone_sorries vk_blockRow`, which stays at 3, and it does not touch
`poseidon_valid`'s refutation. **The critical path is still D-P47's fixture re-export.**

**A method finding worth recording:** the noncomputability culprit is `Assumptions.instGroupBlsGT`, the
carrier instance — not `poseidonRender`'s own fields. And **plain `decide`/`rfl` fail on all six even
at the computable proxies** (stuck at `List.lookup "VK_MPTR" (constTableOf poseidonM)`;
`maxRecDepth 20000` still stuck; `vm_decide` unavailable). **The only working route is `native_decide`
on the proxies plus defeq transfer back to the render.** Any later card that tries to decide a `consts`
lookup will hit this.

## D-P51 — **Approved: update the 4 gates that hard-code the pcs flattening (G1.4 follow-through)**

> Raised by G1.4's stop-and-report. **Status: APPROVED.** Signed off: human (repository owner),
> 2026-11-17, in session after `2cad8cc`. G1.4b may run on it; its per-gate "what did this protect"
> check and its stop condition still apply.

**The situation.** G1.4 fixed `emitPcsFromPlan` to emit the 8-block partition as `Stmt.block` scopes
instead of flattening it. **The pcs row now prints `equal true`** (3623 == 3623, braces 52 == 52, the
3571 non-brace tokens untouched — **braces-only at token level, and RunEmitted's 9 executable-semantics
gates still pass, so nothing the code MEANS regressed**). But **four gates hard-code the flattening**
and now fail, and `PoseidonValid.lean:292` pins the old AST count 6761.

**Decision: approve updating all five sites.** The test, in every case, is **whether the gate asserts
the old wrong behaviour or an independent property.** These four assert the flattening itself — the
defect being fixed. **A gate that encodes a bug does not earn protection from it.** The proposed
replacements are **strictly stronger**, and the card did not guess: it evaluated the `:404` replacement
(`stmtsBeq [Stmt.block ((tagged.map Prod.snd).map Stmt.block)]`) to TRUE, and `:505` reuses the deep
`[Stmt.block body]` idiom the same gate already applies to `quotientLin`/`vkLoading`.

**What this is not.** It is **not** adjusting a test to match a change I wanted — which is the failure
mode I explicitly armed against in the brief ('do not adjust the gate to match your change'). **The
card obeyed that, stopped, and reported that my two acceptance clauses were jointly unsatisfiable.**
They were: 'all 10 gates still true' and 'do not adjust any gate' cannot both hold when 3 gates encode
the flattening. **That contradiction was mine, and catching it is the card working correctly.**

**Standing condition on the follow-up card:** every updated gate must be shown **stronger or equal**,
never weaker, and the card must **name what each gate was protecting and show that protection still
holds.** If any one of them turns out to be guarding a real property rather than the flattening, it
stops and reports rather than being rewritten.

**Also recorded: clause 6 did NOT flip.** `codegenAgrees poseidonPv poseidonM` is still `false`; AST
6761 → 6779 (+18) and the remaining gap 7275 = 823 + 68 + 6384 is **exactly G1.1–G1.3 and nothing
else.** **Cone stays 11.** The card reported that precisely instead of claiming a win it hadn't got.

## D-P52 — **Approved: one batched `Program.lean` re-hash for G1.1–G1.3**

> Raised by G1.2b (`2cad8cc`); drafted as `docs/DECISIONS-PENDING.md` §11. **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `6918991`.

**Decision.** G1.1, G1.2 and G1.3 land as **one batch with one deliberate re-hash** of frozen
`Program.lean` (`Midfall/LoweringV2/Frozen.sha256`). The batch:
- widens `mainAsmRaw` to take the model `m` and updates its four callers (all have `m` in scope);
- splices the three regions (`accumulatorHelpers`, `renderQuotientHelpers`,
  `renderQuotientNumeratorBlock`) into `mainAsmRaw`;
- adds the same regions to `sliceOf`'s `.quotientLin` body **in the same commit**, because otherwise
  `prog_slices_decomp` (Blocks.lean:220) becomes false rather than unproved;
- retires the KNOWN-GAP docstring at `Program.lean:92-97`.

**Conditions — the card stops if any fails.** The frozen diff is `Program.lean` only, with exactly one
`Frozen.sha256` line changed, shown as a deliberate diff in the commit message. `Valid.codegen`
(Statements.lean:200) keeps its meaning. The batch runs after G1.4b and recomputes the
`PoseidonValid.lean:292` token pin from G1.4b's value (6779).

**Expected result, to be measured, not assumed.** With G1.4b, R.2 measured `codegenAgrees` TRUE at the
deployment, so `Valid` clause 6 becomes proved. `poseidon_valid` stays refuted (clauses 2, 3, 9), so
the headline cone is not expected to move.

## D-P53 — **Approved: W2 stands; how the 2026-11-17 batch was signed**

> Drafted as `docs/DECISIONS-PENDING.md` §1. **Status: APPROVED.** Signed off: human (repository
> owner), 2026-11-17, in session after `4b525ef`.

**Decision: keep W2 unchanged** — *"there are no orchestrator decisions on delegated authority."* No
standing grant is created and the GOAL prompt is not amended.

**How D-P45–D-P48 and D-P53–D-P59 were signed.** The human instructed, in session: *"make best choices
for remaining decisions"*. The assistant drafted each choice and recorded it; the human's instruction
is the sign-off. This is a **one-time human sign-off of the listed decisions, not a delegation**: it
gives the orchestrator no authority, and it covers nothing not written in these entries. Where an
entry pre-approves a fallback (D-P55, D-P56, D-P57, D-P58), the orchestrator applies the stated
condition; it does not choose. Any of these may be revisited by the human; until then they stand.

## D-P54 — **Approved: do NOT add `hR : R.Valid` to `LoweringEquivalence` (R-72's second question)**

> Drafted as `docs/DECISIONS-PENDING.md` §2. **Status: APPROVED (rejection).** Signed off: see D-P53.

`¬ poseidonRender.Valid` is PROVED (`PoseidonValid.lean`, `poseidonRender_notValid`), so with
`R.Valid` as a hypothesis the headline would be provable by contradiction with an empty cone — the
vacuity trap this project exists to avoid. PLAN-V2 §6 requires the headline "with no other
hypotheses". Plan/VK coherence is certified where it belongs: DONE requires `poseidon_valid` proved.

## D-P55 — **Approved: Gap B and the G1 codec — name points from their bytes; G1 needs no axiom, G2 needs one**

> Drafted as `docs/DECISIONS-PENDING.md` §8 (QUEUE R.4). **Status: APPROVED.** Signed off: see D-P53.

**What the drafts missed.** `G2fold = Exp blsR` is the exponent carrier (`G2Codec.lean:245`) and `G₁z`
is `Subgroup.zpowers` of the generator (`G1Agreement.lean:1814`). Naming any concrete point from its
bytes needs `∃ x, enc x = bytes`, i.e. that the point is a multiple of the generator. Option (a)'s
"no new axiom" holds only where that existence is provable:
- **G1: it is.** P-POINTCOUNT (`aa53b57`, `G1PointCount.lean`, sorry-free, standard axioms) proved
  `torsion_eq_zpowers_gen` elementarily: every r-torsion point of E(Fp) is a multiple of the
  published generator. A computed on-curve + subgroup check of the bytes therefore gives existence.
- **G2: it is not, by the same route.** The same commit records that the squeeze fails over Fp2
  (`#E'(Fp2) ≤ 2p²+1` exceeds `r²`); the known proofs need the Weil pairing or point counting, which
  mathlib lacks. The fixture SRS is a file (`srs_for_test`, `zk_stdlib/examples/assets`), so `s` is
  not available either.

**Decision.**
1. **G1 (no axiom).** Make `g1CodecZ.ofCompressed?` real by the same `Classical.choose` scheme as
   `g1zOfEip?` (`G1Agreement.lean:1995`), and discharge concrete decodes via `torsion_eq_zpowers_gen`
   plus computed checks. This unblocks D-P45's discharge and `end_to_end` (F.2-G3). QUEUE R.4b.
2. **G2 (one axiom, only if R.4's first hour finds no axiom-free route).** Add exactly ONE axiom in
   `Midfall/Assumptions/`, beside D-P36a: the G2 analogue of `torsion_eq_zpowers_gen` — every byte
   string that passes a computed EIP-2537 G2 validity check (on the twist over Fp2, and `r·Q = O`) is
   `g2foldToEip x` for some `x : G2fold`. It is a published fact about BLS12-381 (the G2 subgroup is
   cyclic of prime order r), not a fact about this fixture. Required with it:
   - KATs: the check is TRUE at `G2_BASE` and `NEG_S_G2` payload bytes, and FALSE at a twist point
     outside the r-torsion (the premise is neither vacuous nor trivially true);
   - a docstring citing the G2 cofactor/order fact and `aa53b57`'s finding;
   - PLAN-V2's axiom lists (§6 report categories, :265, :313-314, :346-348) updated in the same commit
     from "five D-P36a" to "five D-P36a + the D-P55 G2 cyclicity axiom".
3. **Then name the bases.** `poseidonSG2` (`PoseidonEnv.lean:236`) and the prepared G2 parameters come
   from the payload bytes by `Classical.choose`, so D-P46's NEG_S_G2 pin holds by `choose_spec`.

**Rejected:** per-byte-string axioms (fixture-dependent, and they would change with D-P58's
regeneration); (c) rescoping FinalPairing away from the deployment's VK (weakens the English
headline). **Trust-base change, stated plainly:** if step 2 lands, the headline's axiom list grows by
one curve fact. It is the only trust-base change in this batch.

## D-P56 — **Approved: make `Valid.model` dischargeable without a statement change (QUEUE R.3)**

> Drafted as `docs/DECISIONS-PENDING.md` §9. **Status: APPROVED, option (a), narrowed.** Signed off:
> see D-P53.

Restate `poseidonModelVal` (`PoseidonV2.lean:111`) as `getD` on `poseidonModel`
(`PoseidonInputs.lean:126`) and close clause 4 with F.2-G1's pattern (one `native_decide` on
`.isOk`, then `cases`), so no `DecidableEq` is needed. The `Inhabited` instance is obtained with
`deriving instance Inhabited for Halo2Verifier` **in a V2/`Instances/` file — no v1 edit**. Only if that
cannot derive: the one-line v1 exception (`deriving Inhabited` on `Generator/Models.lean:757`) is
approved, with `Models.lean`'s line count unchanged (or `SORRY.md` regenerated in the same commit).
No statement changes; no frozen file.

## D-P57 — **Approved: WP-T before the loop-heavy rows, time-boxed, with a pre-approved fallback**

> Drafted as `docs/DECISIONS-PENDING.md` §10. **Status: APPROVED, option (a).** Signed off: see D-P53.

- **Order.** WP-T (QUEUE T.2b, then T.3) runs before S.5 and S.6; S.5/S.6 are `after T.3`. T.3's
  target is S.6's row (`BlockSound/BlockProgress R .lagrange`), so S.6 is closed by T.3 if T.3 lands.
  S.4 stays as is (one statement, by hand).
- **Accept line (PLAN-V2:278-279).** Re-prove `traceReturn_spec` on the closed slice in under 100
  lines with the tactic, and record lines per Yul token.
- **Time box.** T.2b plus at most one follow-up card (T.2c), each ≤ 2.5 h.
- **Pre-approved fallback (option b), applied by condition, not choice.** If the accept line is missed
  after T.2c, WP-T is dropped: T.3 reverts to a hand proof of the lagrange row, S.5/S.6 revert to
  `after F.1` with their 1 h stop rules, and `docs/ETA.md` is re-estimated from TraceReturn's measured
  lines per token (988 lines by hand). The orchestrator records which branch applied.

## D-P58 — **Approved: make the fixture export reproducible (QUEUE R.5)**

> Raised by R.1 (`2041977`). **Status: APPROVED.** Signed off: see D-P53.

**Correction to the premise.** The exporter already seeds both RNGs
(`proofs/solidity-verifier/tests/conformance_export.rs:330`, `:333`: witness `42`, prover `0xdebd`), so
"seed the RNG" is not the fix: the run-to-run difference R.1 saw has another source.
**Decision.**
1. Find that source (two exports, diff).
2. If the fix lies in test/exporter code: make the export deterministic, regenerate ONCE, and replace
   `proof.bin`/`trace.json`. Re-pin D.3 checks 4–5 in the same commit.
3. **Pre-approved fallback:** if the source is in baseline code (`proofs/src`, `zk_stdlib`), do not
   change it. Keep the committed `proof.bin`/`trace.json` as the pinned ground truth, and record its
   provenance as "unknown; verified by D.3 checks 4–5".
4. Either way, for the stale `Halo2Verifier.sol` dump: refresh it if any gate or KAT reads it,
   otherwise untrack it.
5. If any frozen file depends on `proof.bin`/`trace.json`, stop (that would need a human decision).

## D-P59 — **Approved: fix the v1 `WellFormed.permutationCommitmentsMatch` defect (`Valid` clause 9)**

> Raised by R.1/F.2 (clause 9 REFUTED). **Status: APPROVED — recorded exception to "do not edit v1
> `.lean` files".** Signed off: see D-P53.

**The defect.** `VerifyingKey.WellFormed.permutationCommitmentsMatch` (`Halo2/Exec/VerifyingKey.lean:114`)
requires `vk.permutation.commitments.size = divCeil columns (csDegree - 2)`. That is the **proof's**
z-commitment count (one per chunk, `verifier.rs:41-45`). The **VK** holds one sigma commitment per
permutation COLUMN: `proofs/src/plonk/permutation.rs:123` builds them as
`(0..argument.columns.len())`. At the deployment, 8 sigma commitments ≠ `divCeil 8 3` = 3, so a
correct VK is refuted. This is a mis-port, not a deployment fact.

**Decision.** Restate the field as `vk.permutation.commitments.size = vk.cs.permutation.columns.size`,
and correct its docstring bullet (`:99-102`) and `Halo2/Spec/Degrees.lean:102` in place.
- **Line counts unchanged**, or `SORRY.md` regenerated in the same commit.
- **Consequence recorded.** `SupportedV2.wf` (frozen `Statements.lean`) refers to this structure, so
  the meaning of frozen `Render.Valid` changes without a hash change. This entry is the record of that
  change.
- **Card stops if** the Lean permutation verifier port indexes `vk.permutation.commitments` by chunk
  rather than by column: that would be a port defect, larger than this field, and needs its own
  decision.

## D-P60 — **Approved: D-V3 — adopt PLAN-V3**

> Drafted as PLAN-V3 §2.2 row 60 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**How D-P60–D-P69 were signed.** The human instructed, in session after `53bf8c1`: *"sign off D-P60 to
D-P69 in design.md"*. The text of each entry is PLAN-V3 §2.2's row, recorded verbatim with the
conditions that row states. As with D-P53, this is a **one-time human sign-off of the listed
entries, not a delegation**: W2 stands, the orchestrator gains no authority, and nothing not written
in these entries is approved. Where an entry carries a condition ("after RECON.1", "before the G1
batch merges"), the orchestrator applies the condition; it does not choose. Where a condition is
not met, the card that depends on it stops and reports; the "if struck" fallbacks of PLAN-V3 §2.2
are **not** pre-approved.

**Decision.** Adopt `docs/plans/PLAN-V3.md` as the active plan, with `docs/plans/PLAN-V3-cards.md`
as its cards and `docs/plans/REVIEW-V3.md` as the findings it rests on.
- Stop SEM block rows about the present render (S.4–S.7, T.3–T.5, C.3, C.5, M.1) until M4's exit
  gate (W14); the rows already proved are kept. This holds T.3, S.5 and S.6, which D-P57 had
  sequenced after T.2b: **an amendment of D-P57's order.**
- Name the target "fixture F1", never "the deployment".
- Add rules W12–W15 (PLAN-V3 §4) to W1–W11.
- The cut-over is PLAN-V3 §10, performed by card PL.0 (now READY). The goal prompt is unchanged:
  `PLAN-V2.md`'s banner and §6 note, and `EXECUTION-V2.md`'s note, redirect to PLAN-V3 from this
  signature on.
- **Must not be done** (PLAN-V3 §2.2): deleting `SoundSide` from `Rejects` (RV-10).

## D-P61 — **Approved: two further reference repairs in `Halo2/Exec` — grouping by allocation slot, semantic `Rotation` equality**

> Drafted as PLAN-V3 §2.2 row 61 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.** Two edits to v1 `Halo2/Exec` files, beside D-P59's, as a **recorded exception to "do
not edit v1 `.lean` files"**:
1. Multi-open grouping by `CommitSlot` (card REF.1): one-piece commitments are compared by an
   explicit allocation slot, as Rust compares them by pointer (`proofs/src/poly/query.rs:125`),
   not by value (`Exec/Kzg/MultiOpen.lean:42`).
2. Semantic `BEq Rotation` (card REF.2): equality of the integer, as Rust's `Rotation(pub i32)`.

**Why.** They change what the frozen `LeanAccepts` *means*: today it is false for every proof of the
fixture key (REVIEW-V3 RV-03, RV-04, machine-checked in `V3-evidence/ReviewProbes.lean` §3).
- Line counts of the edited files unchanged, or `SORRY.md` regenerated in the same commit (as
  D-P59).
- The two KAT clauses that pin the old behaviour (`Circuit.lean:1892`, `:2083`) flip in the same
  commit; that flip is the falsifier.
- The cards stop if a further divergence from Rust appears on the fixture: it is reported, not
  absorbed.

## D-P62 — **Approved: the curve assumption — construct the pairing; the SRS point is data (amends D-P55 steps 2–3)**

> Drafted as PLAN-V3 §2.2 row 62 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.**
- **(a)** Replace the five D-P36a axioms by the constructed pairing `e(P, k) = k • P` on
  `(G₁z, G2fold, G₁z)` with `g₁ := g1zGen`, `g₂ := g2foldExp 1`. **No G2 cyclicity axiom**: D-P55
  step 2 is withdrawn.
- **(b)** The SRS point is data: `poseidonRenderAt s`, with the hypothesis `SrsEncodes s` only for
  an SRS whose trapdoor is unknown, instead of `Classical.choose` over an axiom (D-P55 step 3).
- **(c)** The deployment codec is the computable `g1CodecC` (it equals `g1CodecZ` on the EIP half,
  `g1CodecC_ofEip`), which implements D-P55 step 1.

**Trust-base change, stated plainly:** the headline's axiom list **shrinks** to `propext`,
`Classical.choice`, `Quot.sound` and the recorded `native_decide` axioms. In the same commit:
`check_frozen_axioms.py:126-131`, `check_hypothesis_bundles.py:130` and PLAN-V2's axiom lists
(§6; the lines D-P55 names) change from "five D-P36a" to none. `Eip2537.Holds` at the constructed
pairing says of the real EVM what it said before: G1ADD, G1MSM, MODEXP agree with `Externals.lean`,
and PAIRING_CHECK on `(P₁, k₁H₂), (P₂, k₂H₂)` returns 1 iff `k₁P₁ + k₂P₂ = 0`.
- Cards REF.4, REF.5, REF.5g, REF.6; QUEUE R.4 and R.4b are MERGED INTO them (PLAN-V3 §10.2).
- Stop if `#print axioms holds_exhibited_noAxiom` is not the standard three.

## D-P63 — **Approved: a test SRS with a known trapdoor for fixture F1 (amends D-P58's fallback 3)**

> Drafted as PLAN-V3 §2.2 row 63 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.** Regenerate F1 with a seeded `ParamsKZG::unsafe_setup` whose trapdoor is exported
(card REF.11, run first in M1), so acceptance, the `−s·G₂` pin and the generator's own SRS check
become computations. This **amends D-P58's fallback 3** ("keep the committed `proof.bin`/`trace.json`
as the pinned ground truth"): the committed bundle is kept as a second instance of the reference
gate (REF.8), and F1 becomes the new bundle.

**Consequence accepted.** Every F1 measurement of PLAN-V3 §3 and every `native_decide` pin on
fixture data is re-taken on the new bundle; REF.11 runs before any of them for that reason.
**Stated limit, for the English statement:** F1's trapdoor is public, so the equivalence holds but
no soundness of the proof system is claimed for this SRS; `SrsEncodes` is not a hypothesis of
`Done`.
- REF.11 does not seed the prover in `proofs/src` (the non-determinism is `OsRng` in
  `blind_quotient_limbs`, `prover.rs:126`, baseline code): gates compare Lean with the `trace.json`
  and EVM result of the same bundle, pinned by a manifest.
- Stop if the regenerated bundle is a different circuit or key shape from F1 (a scope question).

## D-P64 — **Approved: the statement surface V3 (frozen)**

> Drafted as PLAN-V3 §2.2 row 64 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.** In one signed re-hash of the frozen surface: `calldataOf` as `repackThenEncode`;
`EntryFrameV3` (adds `cd.size < 2^256`); `G1CodecHeadlineLaws` as a hypothesis of every conjunct;
conjunct 4 (totality); `EndToEndV3`. Text: `docs/plans/V3-evidence/lean/statements/StatementsV3.lean`,
landed first as a staging module by ST.1.

**Condition (applied, not chosen):** the re-hash lands only after ST.1 has landed the compiled text
in the tree and M2 its witnesses (W12). The card shows the one-commit hash diff.
- **The option is NOT taken by this sign-off.** PLAN-V3 offered, in the same re-hash, zero memory
  from `TRANSCRIPT_MPTR` instead of from `0x80` (`EntryFrameV3'`). The headline keeps zero memory
  from `0x80`; taking the option needs its own decision.
- Witness and falsifiers: `StatementsV3Deploy.lean`, `StatementsV3Falsifiers.lean`.

## D-P65 — **Approved: the block scope, in D-P52's re-hash (amends D-P52's frozen-diff condition)**

> Drafted as PLAN-V3 §2.2 row 65 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.** The block scope becomes `[hoist helpers ++ hoist slices]` and `Render.slices` moves
into `Statements.lean`. Without it, `prog_slices_decomp`'s second conjunct is false the moment G1.2
puts `q_program_fail` into a slice (RV-13).

**This amends D-P52's condition** "the frozen diff is `Program.lean` only, with exactly one
`Frozen.sha256` line changed": the G1 batch's frozen diff is now `Program.lean` **and**
`Statements.lean`, with those two hash lines changed, in one commit. Per PLAN-V3 §5 M2 the same
re-hash also carries OBJ.2's `Program.lean` signature edits.

**Condition (applied, not chosen): in force before the G1 batch merges G1.2.** The batch stops if
the scope edit is not in it. Evidence: copies of the five block files compile with no proof edit
under this scope (`design/statements.md` §2(d)); the alternative `[hoist (R.prog 0 0)]` breaks
`fail_lookup := rfl` and is rejected.

### OBJ.5 addendum — THE OBJECT FINGERPRINT (V3 row 39, landed after OBJ.2)

This decision is the one that fixes what `Frozen.sha256` covers, so the complement of that coverage
belongs here. The manifest hashes three FILES — `LoweringV2/Program.lean`,
`LoweringV2/Shared.lean`, `LoweringV2/Statements.lean`. The program the headline quantifies over is
in none of them: after this decision's own re-hash it is COMPUTED, by
`asmOf poseidonPv poseidonM 0 0`, out of the AST emitters under `Midfall/Lowering/GenAst*.lean` and
the render model under `Midfall/Generator/`. One literal changed in one emitter changes what the
theorem is about and leaves every frozen hash green. `Midfall/Instances/ObjectFingerprint.lean`
pins the computed object instead. **The two values, measured on the POST-M2 tree (at `e67415b`):**

| the pin | the literal |
|---|---|
| `objectTokens.length` — `yulTokens (EVM.print (asmOf poseidonPv poseidonM 0 0)).length` | `14109` |
| `objectKeccak` — `keccak256` of that printed string | `0x3149ae4fa6733f4f6e9df8a68ef58afce365cfa456fe5073225ba44fe3bef176` |

The declaration is `theorem object_fingerprint : (objectTokens.length, objectKeccak) = (14109,
0x3149ae4f…bef176) := by native_decide`, and it lives in `Instances/` for D-P17's reason:
`native_decide` is confined there and `scripts/checks.sh` enforces that. It is an instance fact
about the poseidon render, NOT a clause of D-P67's `ValidV3` — what it buys is the standing claim
that D-P67's `program` clause and the frozen files are still about the same program from one package
to the next.

Three things worth recording with the numbers.

- **The object is the INLINED program, not `mainAsmRaw`** (the card's guidance): 76 statements over
  14,109 tokens, against `mainAsmRaw`'s 74 over 14,054 — OBJ.2's number, unchanged by this card.
  The constant table is part of what the theorem runs, so `objectIsTheInlinedProgram_ok` reddens if
  a later card re-points the fingerprint at the raw block.
- **The two halves are not redundant, and the digest is the half with the teeth.** A token COUNT is
  blind to a change of a literal's VALUE: `32` and `33` are one token each.
  `objectFingerprintTeeth_ok` measures exactly that — moving `GenAst.emitQuotientLinAt`'s `0x20`
  linearization payload offset to `0x21` leaves the count at 14109 and moves the digest to
  `0x7f0f7c93e9ce9d0d034a2ef01876f9bdb312c058d4f5ec805fd0a1df869c1695`.
- **`keccak256` here is a pure Lean definition** (PLAN-V3 §4's correction of V2's rule 9):
  `Midfall/Common/Keccak.lean:15`, `bytesToWordBE (VCVio.Algorithms.Keccak.keccak256 bs)`, VCVio's
  FFI-free Keccak-f[1600]. So `native_decide` runs compiled code for the same definition the
  statement names, and there is no second implementation for the gate and the theorem to disagree
  about. There is no FFI keccak in this tree.

**FALSIFIER, RUN AND PASSED.** `ylit 0x20` → `ylit 0x21` at `Midfall/Lowering/GenAst.lean:1043`
(one line, the emitter, not a frozen file): `object_fingerprint` fails with
`Tactic native_decide evaluated that the proposition (objectTokens.length, objectKeccak) = (14109,
0x3149…) is false`, the KAT file exits 1, and `sha256sum -c Midfall/LoweringV2/Frozen.sha256`
reports OK for all three files and exits 0. The edit was reverted by editing it back: the file is
byte-identical to HEAD and the gate is green again. That asymmetry is the deliverable — the frozen
hashes cannot see this change and this gate can.

## D-P66 — **Approved: the non-vacuity gate for F1 (amends D-P45)**

> Drafted as PLAN-V3 §2.2 row 66 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.** `HypothesesInhabitedV3`: the hash is pinned to `keccak256`; `LeanAccepts` is added
back; `G1CodecHeadlineLaws` replaces `G1CodecLaws`. Text: `StatementsV3.lean`
(`HypothesesInhabitedV3`).

**Why D-P45 is amended.** D-P45 left out `LeanAccepts` because at a real SRS it is
undischargeable. Its condition here, D-P63, is approved: at F1's test SRS `LeanAccepts` is a
computation (`check_iff_g1`). An existential hash let the gate be met by an artificial hash and a
forged transcript (REVIEW-V3 RV-35), so it is pinned. Q0.5 (D-P45) runs as queued; this text
replaces it at ST.4.
- Stop if the F1 accepted calldata cannot be produced (REF.12): then the gate stays D-P45's text
  with the hash pinned, and the human is told.

## D-P67 — **Approved: `ValidV3` (frozen), seven clauses**

> Drafted as PLAN-V3 §2.2 row 67 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.** `Render.Valid` becomes seven clauses: `generated`, `inputs`, `program`, `noWriters`,
`env`, `payload`, `supported`. It subsumes the 13-clause text, `vkPins`, `vkProgressPins`, and
D-P46's and D-P48's pins (which stay in force until this lands). It adds the structural tie
`codegenStruct` (AST = parse of the text).

**Conditions (applied, not chosen).** The re-hash lands only when (1) RECON.1 has produced the
single text of `ValidV3`, `PayloadAgrees` and `programOk` (the two typechecked drafts differ;
PLAN-V3 §3, "Known gaps") and (2) OBJ.7 shows `generateAll` reproduces the Rust artifact. If either
fails, the card stops and the human decides; PLAN-V3's "if struck" fallback is **not**
pre-approved.
- `delta` is pinned through `generated`, not through `payload` (`inputs.frDelta` is inert at F1);
  RECON.1 shows it by `#eval`.

## D-P68 — **Approved: staged block contracts and the `wp` proof technology (refinable §6/§7; replaces D-P57's fallback)**

> Drafted as PLAN-V3 §2.2 row 68 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.**
- **Architecture.** `StageInv`, `BlockSim`, `BlockProgS`; `Render.Rejects` becomes a corollary;
  `rejects_of_not_accepts`, `prefix_run_clean`, `runBody_iff_slices` are deleted. The x = 0 row is
  closed by the decidable pin `hasMultiPointSet`. Recorded because it replaces signed §6 shapes
  (D-P49's gate carries over to `BlockSim`).
- **Technology.** Rows are proved per fixture on literal slices pinned by `native_decide`, with the
  verified `wp` engine (`wp_sound`). The certificate strategy is chosen by card T3.0's measured
  table.
- **D-P57's hand-proof fallback is replaced** by the go/no-go thresholds of PLAN-V3 §5 M5; at
  calibration point C a miss means **stop and re-plan with the human** (the reflective executor is
  not pre-approved).

**Condition (applied, not chosen):** the architecture lands after RECON.2, which makes the staged
rows conclude the four V3 obligations and adds `cdSize` to `Frame` (as written, `SimContracts` is
false for calldata of 2²⁵⁶ bytes or more; PLAN-V3 §5 M3). Adding a field to `Frame` is within §6's
refinement rules.

## D-P69 — **Approved: the definition of done as one Lean term, and the fixture bundle (extends D-P58)**

> Drafted as PLAN-V3 §2.2 row 69 (`docs/DECISIONS-PENDING.md` §12). **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session after `53bf8c1` (instruction:
> *"sign off D-P60 to D-P69 in design.md"*; see D-P60 for how the batch was signed).

**Decision.**
- DONE is the Lean structure `Done` (PLAN-V3 §6), checked by `#assert_axioms` with a frozen
  allow-list (standard three plus named `native_decide` owners). This replaces PLAN-V2 §6.
- The closure fingerprint of the frozen statements joins `Frozen.sha256` (card DG.3, after M1:
  D-P61's edits change the closure of `LeanAccepts`).
- CI runs on `formal/baseline` (card DG.7).
- Exporter schema 2 (card REF.11, extends D-P58): `calldata.bin`, the EVM result, a mutation
  corpus with Rust verdicts, `build.json`, both `.sol` dumps, a manifest.

## D-P71 — **Approved: the deliverable is the generator theorem; fixtures are tests (amends D-P24, D-P44 clause 4, D-P60, D-P68, D-P69)**

> Drafted as `docs/DECISIONS-PENDING.md` §13. **Status: APPROVED.**
> Signed off: human (repository owner), 2026-11-17, in session at `c22b51a` (instruction:
> *"Sign D-P71"*, given on the draft of §13 as written). The human's stated requirement, same
> session: *"I thought we would formally verify the codegenerator, the lowering itself"* and
> *"i am not interested in proofs for fixtures"*. No D-P70 is recorded: the number was reserved
> for a draft in another session.

**Decision.**
- **Deliverable.** The headline has no fixture in it:
  `theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.ValidV3) :
  LoweringEquivalenceV3 R product`. `ValidV3` contains the generated-by clause, so `R` ranges over
  what the Lean port of the generator emits. `poseidon_done`, `lowering_equivalence_poseidon` and
  `end_to_end_poseidon` are no longer goals.
- **Rows.** `R.SimContracts product`, `R.ProgContracts product` and `TotalV3 R product` are proved
  from `hR : R.ValidV3` for every `R`. No block row, totality lemma or headline is stated or proved
  at a fixture. D-P68's architecture stands; its technology clause ("rows are proved per fixture on
  literal slices pinned by `native_decide`") is struck. The `wp` engine is kept and run on
  parametric slices.
- **Validity is checked per circuit, not proved for all inputs.** `ValidV3 R` stays a hypothesis,
  discharged for a given circuit by computation. Proving it for every supported input is not part
  of this decision.
- **Fixtures are tests.** F1 and any further circuit are kept for: W12 witnesses and falsifiers;
  the W14 run-it gates; the non-vacuity gate; the reference gate against Rust; byte equality of the
  rendered contracts with the Rust artifacts. `native_decide` stays allowed there (D-P44).
- **Axioms.** `lowering_correct` closes under `[propext, Classical.choice, Quot.sound]` only. A
  `native_decide` axiom in its cone is a defect.
- **Supported class.** `SupportedV3` as typechecked (`V3-evidence/lean/statements/
  StatementsV3.lean:592`). Widening it is a separate decision per clause. The IVC verifier is
  outside this class (accumulator, external evaluator: PLAN-V3 §5 items X1, X2).

**Amends.** D-P24 is withdrawn. D-P44 clause 4: the claimed headline becomes `lowering_correct`,
and X4 is the goal; clauses 1–3 stand. D-P60: PLAN-V3 stays adopted, with M5–M8, §0 and §6 restated
by card PL.G. D-P68: the technology clause only. D-P69: `Done` loses its fixture in `headline` and
`valid`; `gate`, `reference`, `artifact`, `vkArtifact` stay as fields about F1. D-P61–D-P67 are
unaffected.

**Conditions (applied, not chosen).**
- D-P60's hold stands (no block row before PLAN-V3's M4 exit gate), and W14 stands.
- Card GEN.0 runs first and alone; card GEN.1 replaces T3.6.
- If GEN.0 or GEN.1 misses its threshold: **stop and re-plan the proof technology with the human.**
  Falling back to per-fixture rows is NOT pre-approved.
- Until card PL.G has run, the per-fixture cards it restates (T3.4, T3.6, T3.9, T3.10 route A,
  SIM.6, TOT.1, ROW.TP, ROW.Q, ROW.PCS, ROW.FP, PL.H, PL.E, DG.4) are not briefed as written.

**Not decided here.** The cost is unmeasured (one block closed for every `R`: 25 tokens, 1,053
lines). No estimate is recorded before GEN.1 reports.

## D-P72 — **Approved: widen the supported class to the IVC verifier (accumulator mode with the batched pairing check; external quotient evaluator)**

> Drafted 2026-11-17 at `cf00592` as `docs/DECISIONS-PENDING.md` §14. Evidence:
> `docs/plans/V3-evidence/design/ivc-widening.md`, `ivc-object-reference.md`,
> `lean/widening/*.lean` (`bash docs/plans/V3-evidence/check.sh widening`).
> **Scope: APPROVED.** Signed off: human (repository owner), 2026-11-17, in the plan session at
> `cf00592` (instruction: *"ensure we cover the IVC proofs with extra pairing check, batched"*;
> earlier the same day: *"I would like to prove correct the IVC circuit verifier"* and *"i am not
> interested in proofs for fixtures"*).
> **Clauses 1–10 below: APPROVED.** Signed off: human (repository owner), 2026-11-17, in the plan
> session at `cf00592`, on the clauses as drafted here and in `DECISIONS-PENDING.md` §14
> (instruction: *"sign D-P72 clauses 1 to 10"*). The "if struck" column of §14 is therefore moot.

**What is signed (scope).** The generator theorem of D-P71 must cover the generated verifier of the
IVC decider circuit: accumulator mode, in which the contract folds the carried accumulator into the
final pairing with a keccak-derived challenge `alpha` (one batched pairing check instead of two),
and the external quotient evaluator that this verifier calls. It is covered as a **widening of the
supported class, for every render**; no block row, totality lemma or headline is proved at the IVC
circuit (D-P71). The IVC decider circuit becomes test fixture **F2**. This strikes items X1 and X2
from "later" (PLAN-V3 §5) and D-P71's clause "the IVC verifier is outside this class".

**Facts the clauses rest on** (measured or read at `cf00592`; details in the two memos).
- Two `SupportedV3` clauses are known to fail on the IVC key: `noAcc` and `embeddedQuotient`.
  (Corrected the same day after review: the first draft said "exactly two". The other clauses
  were read off the artifact or inferred, and `wf` and `layout` are unmeasured; card GEN.2 prints
  the table from the exported key.)
- Rust has no single function that the contract ports in accumulator mode. The e2e test checks the
  decider proof with `midnight_zk_stdlib::verify` and, separately, `final_acc.check` under the IVC
  SRS. The contract makes one pairing check on `(kzg_lhs + α·acc_lhs, kzg_rhs + α·acc_rhs)`.
  So an iff with "the Rust verifier" does not exist.
- The Lean generator already renders the seven partials of the IVC verifier byte for byte
  (`lean/widening/IvcPartials.lean`); the evaluator contract, the acc config and the external
  frame are ported and tested only synthetically; no bundle of the decider circuit exists.
- The tracked IVC contracts have no proof: `proof.bin`, `calldata.bin` and `contract-sizes.txt` in
  the dump are untracked leftovers of 2026-10-07 from another render.

**Clauses (signed).**
1. **One theorem.** The stated target becomes `lowering_correctW (R) (Q : EvalObject) (product)
   (hR : ValidW R Q) : LoweringEquivalenceW R Q product` (`lean/widening/WideningStages.lean`; see
   the note recorded after review, below, for the hypothesis `hQ` it carries until WID.H).
   D-P71's `lowering_correct` is its corollary (`lowering_correct_of_W`), and at a render with no
   accumulator and an embedded evaluator the widened statement is the V3 text
   (`equivalenceW_iff_V3`, proved). The rows of the base class are proved first, in the widened
   shape, so that nothing is restated when the two new arms are added.
2. **Accumulator kinds.** Point-and-scalar with no fixed-base tail (`SupportedW.accKind`,
   `AccShape`). The limb shape (7 limbs of 56 bits) is the only one the generator accepts and is
   not a class parameter. Point-pair and the fixed-base tail are later widenings.
3. **Right-hand side.** `LeanAcceptsAcc`: a Lean reference of the contract's own check, decoding
   the accumulator from the RAW instance words and batching with the keccak `alpha`. Its relation
   to Rust is two proved corollaries, not an iff: `leanAcceptsAcc_of_rust` (Rust accepts the
   proof and the accumulator passes its own check ⇒ the reference accepts) and
   `rust_or_collision_of_leanAcceptsAcc` with `alpha_atMostOne` (the reference accepts ⇒ both Rust
   checks hold, or `alpha` is the one value that makes the two failures cancel). No probability is
   claimed. `¬AlphaCollision` is NOT added to `SoundSide`.
4. **The evaluator.** The object is the Yul body the Lean generator emits for
   `Halo2QuotientEvaluator.sol`, run in the closed dialect. `EvaluatorTrust` is a hypothesis of the
   headline, keyed on the code-size and code-hash pin the verifier itself tests: an account that
   passes the pin answers as the generated body does and changes no world state. It is the
   evaluator's analogue of `EntryFrame` (solc is trusted). It is shown satisfiable
   (`evaluatorTrust_model`).
5. **Gas oracle.** Conjunct 2 keeps the zero oracle (the V3 text); the rows are proved for
   `CompleteAnyGasW`, which totality needs.
6. **`idLaw`** (`ofEip? (toEip 1) = some 1`) is a hypothesis in accumulator mode only.
7. **Test fixture F2.** The IVC bundle is regenerated under ONE seeded test SRS (`unsafe_setup(20)`
   then `downsize(19)`: the IVC and decider SRS must share the trapdoor), with exporter schema 2
   plus the accumulator mutants. A production-SRS render serves byte equality, the clause table
   and the reference gate up to the two pairing inputs; it cannot serve the acceptance gate.
8. **A Rust-side assertion.** Add `assert_eq!(ivc_srs.s_g2(), decider_srs.s_g2())` to the e2e test
   (it has none), and name the one-SRS assumption in the English statement.
9. **Evaluator free-memory guard.** Ask the generator's owner for the guard the verifier has;
   until then `EvalEntry.fmp` is a trusted bound (measured `0x8c0 ≤ 0x1000`).
10. **`Evaluator.rel_worldLocal`** (sorried, argued false, used only on the retired v1 route) is
    deleted with the v1 track.

**Recorded after review (2026-11-17), within clause 4.** The target as first drafted,
`lowering_correctW (hR : ValidW R Q)`, is false for an arbitrary evaluator object `Q` (an empty
body makes the contract revert on every proof). Until card WID.6 ties `Q` to the generated body
(`Q = evalObjectOf R`, a clause of `ValidW`), the target carries the evaluator's contract as an
explicit hypothesis (`hQ : isExternal R → EvalContracts R Q`); card WID.17 proves it for the
generated body and card WID.H drops it. This adds no assumption to the final theorem: clause 4's
object was always "the Yul body the Lean generator emits".

**What the widened theorem says, in words.** For every render in the widened class: the body of
`verifyProof` returns ABI `true` iff the Lean reference of the contract's check accepts the
calldata — in accumulator mode that reference includes the batched pairing check — and otherwise
reverts without touching the world, and is never stuck; under the precompile assumption, the entry
frame, and (external evaluator) `EvaluatorTrust`. Against Rust in accumulator mode: complete, and
sound up to one value of `alpha` per input.

**Conditions (applied, not chosen).**
- Clause 1: card RECON.3 moves the row statements to the widened shape **before** any ROW card of
  M6 is briefed. The rows of the base class are proved first.
- Clauses 8 and 9 touch Rust under `proofs/solidity-verifier` (a test assertion; a guard in the
  evaluator template). Clause 9 is a request to the generator's owner: until the guard exists,
  `EvalEntry.fmp` is a trusted bound and the English statement says so. A guard changes the
  rendered evaluator and its pinned code hash, so it lands before test fixture F2 is exported
  (WID.4), or F2 is re-exported.
- Clauses 4 and 6 add hypotheses to the widened headline (`EvaluatorTrust`, `idLaw`). They are the
  only ones this decision authorises; a row that needs another is a PREMISE GAP.
- D-P71's conditions stand (GEN.0 first; a missed threshold goes to the human).

## D-P73 — **Approved: certify the generator itself — the headline's hypotheses are on the generator's input only (amends D-P71 point 3, D-P69)**

> Drafted as `docs/DECISIONS-PENDING.md` §15. **Status: APPROVED, with clause 1 as amended.**
> Signed off: human (repository owner), 2026-11-17, in the plan session at `cf00592`. The human
> first said *"sign D-P73 once the design agent reports"*; the report amended clause 1 in two
> points (AMENDED (a) and (b) below), the plan session held the signature and showed the amended
> text, and the human then signed it (instruction: *"Sign as amended"*). The human's stated
> requirement: *"i thought the codegenerator itself would be certified"*.
> Evidence: `docs/plans/V3-evidence/lean/object/GeneratorCertified.lean`, `CertMeasure.lean`,
> `design/generator-certified.md` (`bash docs/plans/V3-evidence/check.sh object`).

**Decision.**

1. **Deliverable.** The headline's hypotheses are on the input only (typechecked):

   ```lean
   theorem generator_certified (gi : GenInput p G₁ G₂ Gₜ) (o : CertOut)
       (hg : Generates gi o) (hs : SupportedInput gi) : (renderOf gi o).ValidV3
   theorem generator_correct_V3 (gi) (o) (hg : Generates gi o) (hs : SupportedInput gi) (product) :
       LoweringEquivalenceV3 (renderOf gi o) product
   ```

   `renderOf gi o` leaves no field of the render free. No per-circuit check remains in the
   theorem. (This strikes D-P71 point 3 and item X11.) After D-P72 the same statement is made
   for `ValidW` and `LoweringEquivalenceW`.
   - **AMENDED (a): the certified function generates the key payload too.**
     `generate gi` is `generateVk`, then the SRS fingerprint, then `generateAll`. With the payload
     taken as an input (as `generateAll` takes it today) the claim is false: flipping the `omega`
     word of the payload leaves the generator accepting, and the constants no longer agree with
     the key (measured). So the certified generator is `generate`, and `GenInput` is the key, the
     SRS, the point codecs, the configuration, the flags and two strings (`features`, `frDelta`)
     that no key determines.
   - **AMENDED (b): `SupportedInput` is not purely decidable.** It is: the scope clauses of the
     supported class (decidable; `layout` is dropped because it follows from generation
     succeeding); the input-only half of `EnvAgrees`; **two codec laws** (the generator's point
     encoders agree with the verifier's `toEip`/`encG2`) — hypotheses on the environment, of the
     same kind as the headline's codec hypothesis, not computations; `deltaLiteral`; and a **new
     size bound** (`numInstances < 2^64`, `k < 64`: Rust computes in `usize`, the port in `Nat`,
     and the header words wrap otherwise).
2. **G1, route A: the tree is the generator's output.** The assembly text the Lean generator
   prints is **defined** as the print of the emitted tree. The template-text port stays in the
   tree as a test oracle. Measured for this route: with solc 0.8.30 under the project's pinned
   options (`--via-ir --optimize --evm-version cancun --no-cbor-metadata`), the port's text and
   the variant with both assembly blocks replaced by the print of the tree compile to **identical
   runtime and creation bytecode** at F1 (with a Homebrew build of solc, not the pinned binary:
   to be repeated with the pinned one). Consequences:
   - the artifact gate against Rust compares **tokens**, or compiled bytecode, inside the assembly
     blocks (comments and layout are not printed); outside them the text is unchanged;
   - **the tree emitter must be complete first**: the accumulator helpers, the quotient helpers
     and the quotient numerator block need tree emitters (OBJ.13, OBJ.14, OBJ.15 and the
     numerator's line families). The block rows need those trees on any route;
   - `Constants.sol` is printed from the constant table (data first), which removes one lemma;
   - not taken: (B) prove the two emitters token-equal for every input — 11 renderer/emitter
     pairs, three trees missing, sized at 25–40 cards, and the kernel cannot reduce the tokenizer
     even on a 15-byte literal, so it needs symbolic string lemmas; (C) define the tree as the
     parse of the text — everything B costs, plus the parser, plus restating the rows.
3. **G2: one lemma per output clause**, proved for every supported input. The 33, by kind:
   (a) what the generator's own validation checks (4: S each); (b) syntactic invariants of the
   tree emitters — constants declared, calls resolved, no world write, exit discipline (4: M
   each), no shadowing and closedness (4: S); (c) builder lemmas (9: S; the payload header: M);
   (c)+(d) with a codec law (5: S to M). A clause that cannot be proved for every input as stated
   is a finding for the human, not a hypothesis to add. **Two are suspects today:** `v3_planMeta`
   (the plan's data is built from the final memory layout, Rust's from an intermediate one) and
   `v3_cdBound` (no generator check bounds the proof length; it may need a circuit-size bound in
   the supported class). Each is the first card of its family: confirm or refute before proving.
4. **What the Lean generator is for.** Certification is about the **Lean** generator. The Rust
   generator is not certified: it is tested against the Lean one. A contract is covered by the
   theorem when it was produced by the Lean generator, or when its text is token-equal (or its
   bytecode equal) to what the Lean generator prints for the same input — a computation, once per
   deployment. **Today the Lean `generate` cannot run on a real key** (there is no computable G2
   decompression), so the second form is the only one available until that is built.
5. **Still trusted** after this decision: the Lean printer `EVM.print` (the text given to solc is
   the print of the tree; a print/parse round-trip theorem would remove it); solc, through
   `EntryFrame`, `EvaluatorTrust`, constant inlining and the Solidity outside the assembly
   blocks; the precompiles; the two codec laws; the Lean kernel and the three standard axioms.
   Removed: the per-circuit evaluation of `ValidV3`, and the Lean token parser.

**Amends.**

| signed entry | amendment |
|---|---|
| D-P71 point 3 | struck: validity is proved for every supported input, not checked per circuit |
| D-P67 (`ValidV3`, frozen) | unchanged as a statement; it becomes a lemma's conclusion instead of the headline's hypothesis |
| D-P69 / D-P71 (`GeneratorDone`) | `headline` is `generator_correct`; `artifact` compares tokens or bytecode inside the assembly blocks |
| PLAN-V3 §5 | a new milestone M10 "the generator is certified"; the tree-emitter cards (OBJ.13–OBJ.15, the numerator families) move in front of M5; route A's printing change lands with OBJ.7 |

**Conditions (applied, not chosen).**

- The block rows of M5–M6 are proved against the tree emitters, as today. Route A changes which
  text is printed, not what the rows are about, so no row waits for this decision.
- `generator_certified` cannot be proved before the tree emitter is complete: two of its lemmas
  are false at F1 today for that reason alone.
- A confirmed suspect (`v3_planMeta`, `v3_cdBound`), or any clause false for some supported
  input, stops its card and goes to the human.

**Not decided here.** Whether the contracts that are deployed are produced by the Lean generator
or by the Rust one. Until the Lean `generate` runs on a real key, a deployed contract is covered
by a per-deployment comparison with what the Lean generator prints (clause 4).

## D-P74 — **Approved: wire the headline first; one row shape; the progress root is `lowering_correct` (amends D-P72's routing of `lowering_correct`, D-P68's boundary)**

> **Status: APPROVED.** Drafted 2026-11-19 at `b62e29e`, after a review of the 33 commits of
> `7a9baa9~1..b62e29e`: no merge moved the headline. Signed off: the human, 2026-11-19, in a Copilot
> session in VS Code (tree at `44d0acd`), answering the sign-off form *"Sign D-P74: wire the headline
> first"* with **yes**. The human's requirement: *"i want to complete v3 plan fully"*.
> Evidence: `ef19950` (SIM.6: the V3 composition lies outside the cone of the V2 root the register
> tracks); `c1bb557` (LH: `lowering_correct` is a corollary of the sorried `lowering_correctW`);
> `ca2ed23` (RECON.3: `BlockSimV3` over `StageBnd` is incomparable with `BlockSim` over `StageInv`;
> `blockSimW_iff_blockSim` proved). Card: PL.H0 (`docs/plans/PLAN-V3-cards.md`).

**Decision.**

1. **Route.** `lowering_correct` is proved from the base rows through
   `lowering_equivalenceV3_of_rows`. `lowering_correct_of_W` stays in the tree; the root does not
   use it. The statement does not change. `lowering_correctW` (M9) is proved from the same
   `BlockSim` rows through `blockSimW_iff_blockSim` for the blocks that do not touch the
   accumulator, plus the accumulator arms of area WID.
2. **One row shape.** Row bundles, rows and compositions use `BlockSim`/`BlockProgS` over `StageInv`
   (`Midfall/LoweringV2/Stages.lean`). `StageBnd`, `BlockSimV3`, `BlockProgV3` and the lemmas that
   only compare against them are deleted.
3. **Progress root.** The register's ROOT column, `#cone_report` and `verify.sh` are keyed to
   `Midfall.LoweringV3.lowering_correct`. `lowering_sound` (conjuncts 1 and 3) is reported beside it
   as the first milestone; `lowering_correctW` (from WP C0) and `generator_correct` (from WP D2) are
   reported as further lines. The V2 fixture headline is reported as RETIRED until PL.H deletes it.
4. **Wire first.** PL.H0 (PL.H brought forward as a SKELETON) runs before any row WP; PL.H stays the
   closing card.

**Conditions (applied, not chosen).** A glue step that needs a fact no leaf supplies adds a named
leaf, never a hypothesis on a bundle or a root (D-P71). A row false for some valid render goes to
the human.

## D-P75 — **Approved: complete PLAN-V3 by work packages (amends EXECUTION-V2 §2–§4, §7, W6, W8; PLAN-V3 §7, §10.3; the goal prompt's "Scope")**

> **Status: APPROVED.** Drafted 2026-11-19 at `b62e29e`. Signed off: the human, 2026-11-19, in a
> Copilot session in VS Code (tree at `44d0acd`), answering the sign-off form *"Sign D-P75: complete
> PLAN-V3 fully by work packages"* with **yes**. The human's requirements: *"i want to complete v3
> plan fully"*; *"i feel like the model could do more at once"*.
> Evidence, measured over `7a9baa9~1..b62e29e`: 28 cards merged and 7 met their Accept line; most
> used 40–55 min of a 2–2.5 h box; cold-worktree builds of 28–50 min ate whole boxes; `QUEUE.md`
> and `ETA.md` were not updated once; the register went 66 → 79 while no reported root moved.

**Decision.**

1. **Scope.** All of PLAN-V3: M5–M7 (`lowering_correct`), M8 (`end_to_end`), M9 (`lowering_correctW`),
   M10 (`generator_correct`) and the DONE commit (DG.9). Nothing is deferred or cut.
2. **Unit of work.** A WORK PACKAGE (WP): one outcome on the report (item 4), absorbing the PLAN-V3
   cards listed in its row of the COMPLETION table at the top of `QUEUE.md`. The absorbed cards are
   guidance; the WP's Accept is the contract.
3. **Box.** At most 8 h for `strongest`, 4 h for `Sonnet`; a WIP commit every 45 min. The worker plans
   and splits inside the WP, corrects a false premise inside the WP's goal and reports it. A worker
   whose context runs out is re-briefed on the same WP from its last WIP commit.
4. **Progress is the report.** The sorried leaves of each reported root (`lowering_correct`,
   `lowering_sound`, later `lowering_correctW`, `generator_correct`); block rows INTEGRATED (of 7);
   exhibits PRESENT (of 4); `ValidV3` inhabited at F1. Every WP names the line it moves. Two
   consecutive merged WPs that move no line go to the human.
5. **Statement surface.** A new sorried declaration is allowed only as a leaf of a reported root's
   cone or as a child that the same WP consumes; registered sorries outside the cones must not grow.
   While `ValidV3` has no inhabitant at F1 (until WP B4), W12's witness for a statement over
   `ValidV3` may be the named gap that blocks it (`gap_lowering_correct_witness_unexhibited`); its
   falsifier is still required.
6. **Concurrency.** At most two workers, each in its own long-lived warm worktree, on different
   tracks, or on one track when their files are disjoint. Workers never edit `SORRY.md`, the KAT pins
   or `gen_sorry.sh` owner rows: the orchestrator regenerates them after each merge and runs the full
   `verify.sh` once per merge.
7. **Records.** Per WP: the commit message (at most 25 lines), one `STATUS.md` overwrite (one page),
   the WP's row of the COMPLETION table. `ETA.md` is retired; the V3 table of `QUEUE.md` is card
   reference only.

**Conditions (applied, not chosen).** W1–W5, W7, W9–W15 and PLAN-V3 §4 still bind except where items
2–7 say otherwise. The calibration points remain: a missed threshold stops the dependent WPs and goes
to the human.

## D-QVM1 — **Approved: add the address-fit conjunct to the program clause (repairs the QVM window and VKFIT gaps)**

> **Status: APPROVED.** Drafted and signed 2026-11-21, in the OpenCode session on
> `/Users/julian/midfall`, after the QVM work packages reported that
> `qinterpRefines_qvmLoop` is FALSE as stated (BOXD: a window base at `2^256 - 1` wraps the
> two cursor registers) and VKFIT reported the same missing bound at `vkMptr`/`vk.len`.
> The question put to the human: *"The clean repair is a `memoryFit`/`programFit` conjunct in
> the program clause (a computation on each render) that bounds every pointer+length window
> below 2^256. It changes the class of covered renders, not the headline's form, and it is
> faithful to Rust's usize arithmetic. Do you authorize that repair?"*
> The human answered: **"Yes, add the fit clause (Recommended)."**

**Decision.** `Midfall.LoweringV3.programOk` gains a fourth conjunct `programFits R.pv R.model`
(`LoweringV3/Statements.lean`): the VK payload windows and, when the model carries a
`QuotientProgram`, the interpreter's program, constant and stack windows must all lie below
`2^256`. `ValidV3`'s text does not change; the class of renders it covers shrinks to the ones
whose emitted addresses are representable, which is the Rust `usize` domain.

**Consequences, applied not chosen.**
1. `MemoryPairs.fit1_of_valid` / `fit2_of_valid` are now theorems of `ValidV3`; VKFIT's missing
   bound is no longer a hypothesis.
2. `QuotientRows.quotientProgram_window_of_valid` / `_constWindow_` / `_stackWindow_` expose the
   QVM's three windows to the row.
3. The QVM row is **not** silently proved by this: BOXD's section 12 (unpinned cached top) and
   QLOOP's table-disagreement sketch are separate missing hypotheses, and `qinterpRefines_qvmLoop`
   remains a registered OPEN row until they are added with a consumer.
4. No `ValidV3`, bundle or root hypothesis was added beyond this conjunct; the headline signature
   is unchanged.

## D-QVM2 — **Approved: restate ROW.Q.3 over a fixed, validated segment (retires the universal row)**

> **Status: APPROVED.** Drafted and signed 2026-11-21, in the OpenCode session on
> `/Users/julian/midfall`, after ROWFALSE (`0955bac`) proved that `qinterpRefines_qvmLoop` fails
> for two further reasons beyond D-QVM1's window: a template table can disagree with the reference
> labels, and the universal `∀ s` admits `[NEG]` at an empty stack (the emitted arm runs, the
> reference returns `stackUnderflow`). The question put to the human: *"The sound repair is to
> restate the contract over a FIXED emitted segment, with table agreement and segment validation
> supplied by the caller. Do you authorize that restatement?"* The human answered: **"Yes, restate
> over a fixed validated segment (Recommended)."**

**Decision.** `qinterpRefines_qvmLoop` is RETIRED under W13 (its negation is proved). The replacement
is a contract over a fixed `QSegment` `s`, with the caller supplying:

1. `s.inWindow` and the D-QVM1 fit (`s.base + s.exprEnd < 2^256`);
2. full template-table agreement (`tcq` = the table the reference labels come from);
3. a segment stack-safety certificate, the row counterpart of
   `validateQuotientProgram`/`qvm_validated_noBoundsFault` (the validator rejects `[NEG]` at
   depth 0, which is exactly BOXD's second refutation);
4. the start state the prologue establishes (`q_sp = program.stackMptr`, `q_has_top = 0`).

**Open design point for the QVM agent, not a hypothesis to add silently.** The row's old `Top :=
qinterpTop` is not the output of a segment ending in `foldMain`/`foldSelector`: those arms consume
the cached top and write the accumulator at `evalNumerMptr`, so the replacement must state the
output predicate the fold arms actually produce. The agent states it against the reference's
`evalQuotientIdentity` value and reports; no root, bundle or `ValidV3` hypothesis is added.

**Consequences.** The old row's sorry and its register row are deleted in the same commit that adds
the replacement (W13); the ROWFALSE refutations stay as the W12 falsifiers of the retired text.
`q_blockSim`'s named-leaf list is re-pointed to the replacement.

## D-GATE1 — **Approved: close PG-VKHEADER, gasFree and the snapshot replay row (three frozen/class decisions)**

> **Status: APPROVED.** Signed 2026-11-22 in the OpenCode session on `/Users/julian/midfall`,
> after the A3/GASFREE workers left exact goal states. The three questions and answers:
> 1. PG-VKHEADER — *"Add `11 ≤ constants.length` (Recommended)"*.
> 2. `gasFree_of_valid` — *"Add a frozen `programOk` GasFree clause (Recommended)"*.
> 3. `snapshotOf_prepareMsgs` — *"Accept replay evidence and retire the row (Recommended)"*.

**Decisions.**
1. `PayloadAgrees` (frozen `LoweringV2/Statements.lean`) gains one conjunct:
   `11 ≤ R.pv.vk.constants.length`. It is the minimal clause that makes the vkLoading S3–S8
   memory-window reads follow from the payload pins; the A3 worker's `copyInto`/`vkLen` boundary
   lemmas are the witness of necessity. This is a frozen edit: update `Frozen.sha256`, the
   closure/fingerprint pins, and every construction of `PayloadAgrees` in the same change.
2. `LoweringV3.programOk` gains one conjunct `GasFree (R.prog 0 0)` (the `GasFree` predicate moves
   to a module both `Statements` and `Totality` can import). `gasFree_of_valid` becomes its
   projection; `runBody_gas_oblivious` is already proved. This is a class edit, not a new
   hypothesis on a row or the root.
3. `snapshotOf_prepareMsgs` is RETIRED on the D6 KAT/reference replay evidence: delete the hole
   and its consumer, or replace the consumer by the proved replay fact; no axiom and no new
   hypothesis. `SORRY.md` and the closure pin move with it.

**Conditions.** W13/W15 apply: the frozen/class edits land with their re-hashes and a fresh
register; a row is not stated with a new hypothesis to avoid the edit. If a consumer cannot be
retired without weakening the root, STOP and report the exact consumer instead of inventing a
replacement.
