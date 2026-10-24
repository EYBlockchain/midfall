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
