-- |
-- Midfall.Halo2.Exec.Kzg.Params
--
-- The verifier parameters (rust: proofs/src/poly/kzg/params.rs:280-321).

import Midfall.Common.Curve

namespace Midfall.Halo2

/-- rust: proofs/src/poly/kzg/params.rs:280-284
    ParamsVerifierKZG { s_g2, n_g2_prepared, s_g2_prepared }.

    G2Prepared is a straight-line program precomputed from a point: it adds no
    mathematical content, so the port stores the points and keeps the field
    names. G₁ is a phantom parameter: the Rust type is ParamsVerifierKZG<E>
    and the plan 9.2 interface writes it with both groups, but the struct has
    no G1 field (unlike ParamsKZG). -/
structure ParamsVerifierKZG (G₁ G₂ : Type) where
  /-- rust: s_g2 -/
  sG2 : G₂
  /-- rust: n_g2_prepared -/
  nG2Prepared : G₂
  /-- rust: s_g2_prepared -/
  sG2Prepared : G₂

/-- rust: proofs/src/poly/kzg/params.rs:313-321
    ParamsKZG::verifier_params. The prover side is out of scope (plan
    Section 1), but this constructor is what pins the relationship the
    pairing check relies on: n_g2 is the negation of the *loaded* g2. -/
def ParamsVerifierKZG.ofParams {G₁ G₂ : Type} [Group G₂] (g2 sG2 : G₂) :
    ParamsVerifierKZG G₁ G₂ :=
  { sG2, nG2Prepared := g2⁻¹, sG2Prepared := sG2 }

/-- rust: proofs/src/poly/kzg/params.rs:297-307 ParamsVerifierKZG::read.

    HAZARD, and it is a real one: read builds n_g2_prepared from
    -G2Affine::generator() while verifier_params builds it from -self.g2. The
    two agree only when the params file g2 *is* the canonical generator. A
    params file with g2 = c*G2 (c != 1) therefore behaves differently
    depending on how the verifier parameters were obtained, and the DualMSM
    check would enforce a different equation. This is the G2 twin of the G1
    base-point gap that fc42518 closed (docs/design.md D-P5). The port keeps
    both constructors so the difference stays visible; the conformance
    harness must pin which one produced the exported params.json. -/
def ParamsVerifierKZG.read {G₁ G₂ : Type} [Group G₂] (g2Gen sG2 : G₂) :
    ParamsVerifierKZG G₁ G₂ :=
  { sG2, nG2Prepared := g2Gen⁻¹, sG2Prepared := sG2 }

end Midfall.Halo2
