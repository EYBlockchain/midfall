import Midfall.Generator.SplitOnLines
import Midfall.Generator.ConstText

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000000
set_option maxHeartbeats 20000000
open Midfall Midfall.Generator

namespace Midfall.Generator.ConstLines

/-- A chunk of the constant template: a literal segment (which may contain newlines).
    Interpolated values are represented as one-element literal chunks; the line split
    treats them exactly like any other text and therefore needs no newline-freeness
    hypothesis for the generic round trip. -/
inductive Chunk where
  | lit (s : String)
deriving Repr

def Chunk.text : Chunk → String
  | .lit s => s

def Chunk.pieces : Chunk → List String
  | .lit s => s.splitOn "\n"

/-- Merge two line lists: the last line of `xs` and the first line of `ys` are the
    same rendered line, so concatenate them and keep the rest. -/
def prepend : List String → List String → List String
  | [], ys => ys
  | [x], [] => [x]
  | [x], y :: ys => (x ++ y) :: ys
  | x :: xs, ys => x :: prepend xs ys

def linesOfChunks : List Chunk → List String
  | [] => [""]
  | .lit s :: cs => prepend (s.splitOn "\n") (linesOfChunks cs)

theorem prepend_ne_nil (xs ys : List String) (hy : ys ≠ []) : prepend xs ys ≠ [] := by
  induction xs with
  | nil => simpa [prepend]
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => contradiction
          | cons y ys => simp [prepend]
      | cons x' xs' => simp [prepend, ih]

theorem prepend_intercalate (xs ys : List String) (hx : xs ≠ []) (hy : ys ≠ []) :
    String.intercalate "\n" (prepend xs ys) =
      String.intercalate "\n" xs ++ String.intercalate "\n" ys := by
  induction xs generalizing ys with
  | nil => contradiction
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => contradiction
          | cons y ys => simp [prepend, String.intercalate_cons_cons]
      | cons x' xs' =>
          cases ys with
          | nil => contradiction
          | cons y ys =>
              simp only [prepend]
              rw [String.intercalate_cons_of_ne_nil]
              rw [ih (y :: ys) (by simp) (by simp)]
              rw [String.intercalate_cons_cons]
              simp [String.append_assoc]
              exact prepend_ne_nil (x' :: xs') (y :: ys) (by simp)

theorem prepend_no_nl : ∀ (xs ys : List String),
    (∀ l ∈ xs, '\n' ∉ l.toList) → (∀ l ∈ ys, '\n' ∉ l.toList) →
    ∀ l ∈ prepend xs ys, '\n' ∉ l.toList
  | [], ys, _, hy => by simpa [prepend] using hy
  | [x], [], hx, _ => by simpa [prepend] using hx x (by simp)
  | [x], y :: ys, hx, hy => by
      simp only [prepend]
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · intro hc
        simp only [String.toList_append, List.mem_append] at hc
        rcases hc with hc | hc
        · exact hx x (by simp) hc
        · exact hy y (by simp) hc
      · exact hy a (List.mem_cons_of_mem y ha)
  | x :: x' :: xs, ys, hx, hy => by
      simp only [prepend]
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx a (by simp)
      · exact prepend_no_nl (x' :: xs) ys
          (fun b hb => hx b (List.mem_cons_of_mem x hb)) hy a ha

theorem linesOfChunks_ne_nil (cs : List Chunk) : linesOfChunks cs ≠ [] := by
  induction cs with
  | nil => simp [linesOfChunks]
  | cons c cs ih =>
      cases c with
      | lit s => exact prepend_ne_nil _ _ ih

def lit1 : String := "\n    /// @notice Verifying-key contract address authorized for this verifier.\n    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.\n    address public immutable AUTHORIZED_VK;\n    // Expected VK runtime metadata. The deployed VK runtime is\n    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than\n    // EXPECTED_VK_PAYLOAD_LENGTH.\n    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = "
@[simp] theorem lit1_eq : lit1 = "\n    /// @notice Verifying-key contract address authorized for this verifier.\n    /// @dev The runtime length and codehash are pinned by generated constants and checked at construction time.\n    address public immutable AUTHORIZED_VK;\n    // Expected VK runtime metadata. The deployed VK runtime is\n    // INVALID || payload, hence EXPECTED_VK_LENGTH is one byte longer than\n    // EXPECTED_VK_PAYLOAD_LENGTH.\n    uint256 internal constant EXPECTED_VK_PAYLOAD_LENGTH = " := rfl
def lit3 : String := ";\n    uint256 internal constant EXPECTED_VK_LENGTH = "
@[simp] theorem lit3_eq : lit3 = ";\n    uint256 internal constant EXPECTED_VK_LENGTH = " := rfl
def lit5 : String := ";\n    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = "
@[simp] theorem lit5_eq : lit5 = ";\n    uint256 internal constant EXPECTED_VK_CODEHASH_WORD = " := rfl
def lit7 : String := ";\n    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);"
@[simp] theorem lit7_eq : lit7 = ";\n    bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD);" := rfl
def lit9 : String := ""
@[simp] theorem lit9_eq : lit9 = "" := rfl
def lit11 : String := "\n    /// @notice Quotient evaluator contract authorized for split quotient reconstruction.\n    /// @dev The evaluator returns the linearization expected scalar and selector buckets; its runtime may be pinned by generated constants.\n    address public immutable AUTHORIZED_QUOTIENT;"
@[simp] theorem lit11_eq : lit11 = "\n    /// @notice Quotient evaluator contract authorized for split quotient reconstruction.\n    /// @dev The evaluator returns the linearization expected scalar and selector buckets; its runtime may be pinned by generated constants.\n    address public immutable AUTHORIZED_QUOTIENT;" := rfl
def lit13 : String := "\n    // Expected split evaluator runtime metadata. It is checked at deployment\n    // and again immediately before each external quotient reconstruction.\n    uint256 internal constant EXPECTED_QUOTIENT_LENGTH = "
@[simp] theorem lit13_eq : lit13 = "\n    // Expected split evaluator runtime metadata. It is checked at deployment\n    // and again immediately before each external quotient reconstruction.\n    uint256 internal constant EXPECTED_QUOTIENT_LENGTH = " := rfl
def lit15 : String := ";\n    uint256 internal constant EXPECTED_QUOTIENT_CODEHASH_WORD = "
@[simp] theorem lit15_eq : lit15 = ";\n    uint256 internal constant EXPECTED_QUOTIENT_CODEHASH_WORD = " := rfl
def lit17 : String := ";\n    bytes32 internal constant EXPECTED_QUOTIENT_CODEHASH = bytes32(EXPECTED_QUOTIENT_CODEHASH_WORD);"
@[simp] theorem lit17_eq : lit17 = ";\n    bytes32 internal constant EXPECTED_QUOTIENT_CODEHASH = bytes32(EXPECTED_QUOTIENT_CODEHASH_WORD);" := rfl
def lit19 : String := ""
@[simp] theorem lit19_eq : lit19 = "" := rfl
def lit21 : String := ""
@[simp] theorem lit21_eq : lit21 = "" := rfl
def lit23 : String := "\n\n    // Solidity ABI calldata cursors. The generated verifier accepts exactly\n    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`\n    // bytes itself in the same order as the Rust verifier transcript.\n    uint256 internal constant    PROOF_LEN_CPTR = "
@[simp] theorem lit23_eq : lit23 = "\n\n    // Solidity ABI calldata cursors. The generated verifier accepts exactly\n    // verifyProof(bytes proof, uint256[] instances), then parses the `proof`\n    // bytes itself in the same order as the Rust verifier transcript.\n    uint256 internal constant    PROOF_LEN_CPTR = " := rfl
def lit25 : String := ";\n    uint256 internal constant        PROOF_CPTR = "
@[simp] theorem lit25_eq : lit25 = ";\n    uint256 internal constant        PROOF_CPTR = " := rfl
def lit27 : String := ";\n    uint256 internal constant NUM_INSTANCE_CPTR = "
@[simp] theorem lit27_eq : lit27 = ";\n    uint256 internal constant NUM_INSTANCE_CPTR = " := rfl
def lit29 : String := ";\n    uint256 internal constant     INSTANCE_CPTR = "
@[simp] theorem lit29_eq : lit29 = ";\n    uint256 internal constant     INSTANCE_CPTR = " := rfl
def lit31 : String := ";\n    // First general-purpose memory words reserved by the generated verifier.\n    // RETURN_MPTR is a single word set to 1 on success.\n    uint256 internal constant    TRANSCRIPT_MPTR = "
@[simp] theorem lit31_eq : lit31 = ";\n    // First general-purpose memory words reserved by the generated verifier.\n    // RETURN_MPTR is a single word set to 1 on success.\n    uint256 internal constant    TRANSCRIPT_MPTR = " := rfl
def lit33 : String := ";\n    uint256 internal constant        RETURN_MPTR = "
@[simp] theorem lit33_eq : lit33 = ";\n    uint256 internal constant        RETURN_MPTR = " := rfl
def lit35 : String := ";\n\n    // ----------------------------------------------------------------------\n    // Verifying-key memory map. The VK header lives at VK_MPTR, followed\n    // by the quotient VM payload and commitments. After the full VK\n    // runtime comes the challenge slots (challenge_mptr..) and the\n    // per-stage scratch (theta_mptr..).\n    // ----------------------------------------------------------------------\n    uint256 internal constant                VK_MPTR = "
@[simp] theorem lit35_eq : lit35 = ";\n\n    // ----------------------------------------------------------------------\n    // Verifying-key memory map. The VK header lives at VK_MPTR, followed\n    // by the quotient VM payload and commitments. After the full VK\n    // runtime comes the challenge slots (challenge_mptr..) and the\n    // per-stage scratch (theta_mptr..).\n    // ----------------------------------------------------------------------\n    uint256 internal constant                VK_MPTR = " := rfl
def lit37 : String := ";\n    uint256 internal constant         VK_DIGEST_MPTR = "
@[simp] theorem lit37_eq : lit37 = ";\n    uint256 internal constant         VK_DIGEST_MPTR = " := rfl
def lit39 : String := ";\n    uint256 internal constant     NUM_INSTANCES_MPTR = "
@[simp] theorem lit39_eq : lit39 = ";\n    uint256 internal constant     NUM_INSTANCES_MPTR = " := rfl
def lit41 : String := ";\n    uint256 internal constant                 K_MPTR = "
@[simp] theorem lit41_eq : lit41 = ";\n    uint256 internal constant                 K_MPTR = " := rfl
def lit43 : String := ";\n    uint256 internal constant             N_INV_MPTR = "
@[simp] theorem lit43_eq : lit43 = ";\n    uint256 internal constant             N_INV_MPTR = " := rfl
def lit45 : String := ";\n    uint256 internal constant             OMEGA_MPTR = "
@[simp] theorem lit45_eq : lit45 = ";\n    uint256 internal constant             OMEGA_MPTR = " := rfl
def lit47 : String := ";\n    uint256 internal constant         OMEGA_INV_MPTR = "
@[simp] theorem lit47_eq : lit47 = ";\n    uint256 internal constant         OMEGA_INV_MPTR = " := rfl
def lit49 : String := ";\n    uint256 internal constant    OMEGA_INV_TO_L_MPTR = "
@[simp] theorem lit49_eq : lit49 = ";\n    uint256 internal constant    OMEGA_INV_TO_L_MPTR = " := rfl
def lit51 : String := ";\n    uint256 internal constant   HAS_ACCUMULATOR_MPTR = "
@[simp] theorem lit51_eq : lit51 = ";\n    uint256 internal constant   HAS_ACCUMULATOR_MPTR = " := rfl
def lit53 : String := ";\n    uint256 internal constant        ACC_OFFSET_MPTR = "
@[simp] theorem lit53_eq : lit53 = ";\n    uint256 internal constant        ACC_OFFSET_MPTR = " := rfl
def lit55 : String := ";\n    uint256 internal constant     NUM_ACC_LIMBS_MPTR = "
@[simp] theorem lit55_eq : lit55 = ";\n    uint256 internal constant     NUM_ACC_LIMBS_MPTR = " := rfl
def lit57 : String := ";\n    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = "
@[simp] theorem lit57_eq : lit57 = ";\n    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = " := rfl
def lit59 : String := ";\n    uint256 internal constant            G1_BASE_MPTR = "
@[simp] theorem lit59_eq : lit59 = ";\n    uint256 internal constant            G1_BASE_MPTR = " := rfl
def lit61 : String := ";\n    uint256 internal constant            G2_BASE_MPTR = "
@[simp] theorem lit61_eq : lit61 = ";\n    uint256 internal constant            G2_BASE_MPTR = " := rfl
def lit63 : String := ";\n    uint256 internal constant      NEG_S_G2_BASE_MPTR = "
@[simp] theorem lit63_eq : lit63 = ";\n    uint256 internal constant      NEG_S_G2_BASE_MPTR = " := rfl
def lit65 : String := ";\n\n    uint256 internal constant CHALLENGE_MPTR = "
@[simp] theorem lit65_eq : lit65 = ";\n\n    uint256 internal constant CHALLENGE_MPTR = " := rfl
def lit67 : String := ";\n\n    // Challenge layout. Squeeze order in midnight-proofs:\n    //   user_phase challenges (variable count)\n    //   theta -> beta, gamma -> trash_challenge -> y -> x ->\n    //   x1, x2 -> x3 -> x4\n    uint256 internal constant            THETA_MPTR = "
@[simp] theorem lit67_eq : lit67 = ";\n\n    // Challenge layout. Squeeze order in midnight-proofs:\n    //   user_phase challenges (variable count)\n    //   theta -> beta, gamma -> trash_challenge -> y -> x ->\n    //   x1, x2 -> x3 -> x4\n    uint256 internal constant            THETA_MPTR = " := rfl
def lit69 : String := ";\n    uint256 internal constant             BETA_MPTR = "
@[simp] theorem lit69_eq : lit69 = ";\n    uint256 internal constant             BETA_MPTR = " := rfl
def lit71 : String := ";\n    uint256 internal constant            GAMMA_MPTR = "
@[simp] theorem lit71_eq : lit71 = ";\n    uint256 internal constant            GAMMA_MPTR = " := rfl
def lit73 : String := ";\n    uint256 internal constant TRASH_CHALLENGE_MPTR = "
@[simp] theorem lit73_eq : lit73 = ";\n    uint256 internal constant TRASH_CHALLENGE_MPTR = " := rfl
def lit75 : String := ";\n    uint256 internal constant                Y_MPTR = "
@[simp] theorem lit75_eq : lit75 = ";\n    uint256 internal constant                Y_MPTR = " := rfl
def lit77 : String := ";\n    uint256 internal constant                X_MPTR = "
@[simp] theorem lit77_eq : lit77 = ";\n    uint256 internal constant                X_MPTR = " := rfl
def lit79 : String := ";\n    uint256 internal constant               X1_MPTR = "
@[simp] theorem lit79_eq : lit79 = ";\n    uint256 internal constant               X1_MPTR = " := rfl
def lit81 : String := ";\n    uint256 internal constant               X2_MPTR = "
@[simp] theorem lit81_eq : lit81 = ";\n    uint256 internal constant               X2_MPTR = " := rfl
def lit83 : String := ";\n    uint256 internal constant               X3_MPTR = "
@[simp] theorem lit83_eq : lit83 = ";\n    uint256 internal constant               X3_MPTR = " := rfl
def lit85 : String := ";\n    uint256 internal constant               X4_MPTR = "
@[simp] theorem lit85_eq : lit85 = ";\n    uint256 internal constant               X4_MPTR = " := rfl
def lit87 : String := ";\n\n    // Batch-open commitments live in 4-word EIP-2537 padded slots.\n    uint256 internal constant             F_COM_MPTR = "
@[simp] theorem lit87_eq : lit87 = ";\n\n    // Batch-open commitments live in 4-word EIP-2537 padded slots.\n    uint256 internal constant             F_COM_MPTR = " := rfl
def lit89 : String := ";\n    uint256 internal constant                PI_MPTR = "
@[simp] theorem lit89_eq : lit89 = ";\n    uint256 internal constant                PI_MPTR = " := rfl
def lit91 : String := ";\n\n    // Accumulator (KZG IVC).\n    uint256 internal constant          ACC_LHS_MPTR = "
@[simp] theorem lit91_eq : lit91 = ";\n\n    // Accumulator (KZG IVC).\n    uint256 internal constant          ACC_LHS_MPTR = " := rfl
def lit93 : String := ";\n    uint256 internal constant          ACC_RHS_MPTR = "
@[simp] theorem lit93_eq : lit93 = ";\n    uint256 internal constant          ACC_RHS_MPTR = " := rfl
def lit95 : String := ";\n\n    // Lagrange / linearization scratch.\n    uint256 internal constant              X_N_MPTR = "
@[simp] theorem lit95_eq : lit95 = ";\n\n    // Lagrange / linearization scratch.\n    uint256 internal constant              X_N_MPTR = " := rfl
def lit97 : String := ";\n    uint256 internal constant  X_N_MINUS_1_INV_MPTR = "
@[simp] theorem lit97_eq : lit97 = ";\n    uint256 internal constant  X_N_MINUS_1_INV_MPTR = " := rfl
def lit99 : String := ";\n    uint256 internal constant           L_LAST_MPTR = "
@[simp] theorem lit99_eq : lit99 = ";\n    uint256 internal constant           L_LAST_MPTR = " := rfl
def lit101 : String := ";\n    uint256 internal constant          L_BLIND_MPTR = "
@[simp] theorem lit101_eq : lit101 = ";\n    uint256 internal constant          L_BLIND_MPTR = " := rfl
def lit103 : String := ";\n    uint256 internal constant              L_0_MPTR = "
@[simp] theorem lit103_eq : lit103 = ";\n    uint256 internal constant              L_0_MPTR = " := rfl
def lit105 : String := ";\n    uint256 internal constant     INSTANCE_EVAL_MPTR = "
@[simp] theorem lit105_eq : lit105 = ";\n    uint256 internal constant     INSTANCE_EVAL_MPTR = " := rfl
def lit107 : String := ";\n    // Legacy name: this is not h(x). It stores the expected opening\n    // scalar for the linearized commitment, i.e. the negated y-batched\n    // identity numerator reconstructed from the alleged evals at x.\n    uint256 internal constant     QUOTIENT_EVAL_MPTR = "
@[simp] theorem lit107_eq : lit107 = ";\n    // Legacy name: this is not h(x). It stores the expected opening\n    // scalar for the linearized commitment, i.e. the negated y-batched\n    // identity numerator reconstructed from the alleged evals at x.\n    uint256 internal constant     QUOTIENT_EVAL_MPTR = " := rfl
def lit109 : String := ";\n    uint256 internal constant         QUOTIENT_MPTR = "
@[simp] theorem lit109_eq : lit109 = ";\n    uint256 internal constant         QUOTIENT_MPTR = " := rfl
def lit111 : String := ";   // 4 words\n    uint256 internal constant            F_EVAL_MPTR = "
@[simp] theorem lit111_eq : lit111 = ";   // 4 words\n    uint256 internal constant            F_EVAL_MPTR = " := rfl
def lit113 : String := ";\n    uint256 internal constant                 V_MPTR = "
@[simp] theorem lit113_eq : lit113 = ";\n    uint256 internal constant                 V_MPTR = " := rfl
def lit115 : String := ";\n    uint256 internal constant         FINAL_COM_MPTR = "
@[simp] theorem lit115_eq : lit115 = ";\n    uint256 internal constant         FINAL_COM_MPTR = " := rfl
def lit117 : String := ";   // 4 words\n    uint256 internal constant      PAIRING_LHS_MPTR = "
@[simp] theorem lit117_eq : lit117 = ";   // 4 words\n    uint256 internal constant      PAIRING_LHS_MPTR = " := rfl
def lit119 : String := ";   // 4 words\n    uint256 internal constant      PAIRING_RHS_MPTR = "
@[simp] theorem lit119_eq : lit119 = ";   // 4 words\n    uint256 internal constant      PAIRING_RHS_MPTR = " := rfl
def lit121 : String := ";   // 4 words\n\n    // Multi-prepare scratch (sized at codegen time).\n    uint256 internal constant       ROT_POINTS_MPTR = "
@[simp] theorem lit121_eq : lit121 = ";   // 4 words\n\n    // Multi-prepare scratch (sized at codegen time).\n    uint256 internal constant       ROT_POINTS_MPTR = " := rfl
def lit123 : String := ";\n    uint256 internal constant       X1_POWERS_MPTR = "
@[simp] theorem lit123_eq : lit123 = ";\n    uint256 internal constant       X1_POWERS_MPTR = " := rfl
def lit125 : String := ";\n    // Q_COM materialization is currently fused into the final MSM scratch,\n    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero\n    // reserved capacity until a future emitter starts writing Q_COM_MPTR.\n    uint256 internal constant            Q_COM_MPTR = "
@[simp] theorem lit125_eq : lit125 = ";\n    // Q_COM materialization is currently fused into the final MSM scratch,\n    // so this marker intentionally aliases Q_EVAL_SET_MPTR and has zero\n    // reserved capacity until a future emitter starts writing Q_COM_MPTR.\n    uint256 internal constant            Q_COM_MPTR = " := rfl
def lit127 : String := ";\n    uint256 internal constant      Q_EVAL_SET_MPTR = "
@[simp] theorem lit127_eq : lit127 = ";\n    uint256 internal constant      Q_EVAL_SET_MPTR = " := rfl
def lit129 : String := ";\n\n    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals\n    // block of the proof; we keep it as a memory slot for symmetry.\n    uint256 internal constant         Q_EVAL_CPTR_MPTR = "
@[simp] theorem lit129_eq : lit129 = ";\n\n    // Q_EVAL_CPTR is set at runtime once the verifier reaches the q_evals\n    // block of the proof; we keep it as a memory slot for symmetry.\n    uint256 internal constant         Q_EVAL_CPTR_MPTR = " := rfl
def lit131 : String := ";\n\n    // Reserved 4-word slot for the G1 identity (point at infinity) in\n    // EIP-2537 padded form. EVM memory is zero-initialised, and the verifier\n    // never writes to this region, so any read of this slot (the PCS\n    // emitters `mcopy` from it when staging identity commitments) yields\n    // 0,0,0,0 -- exactly the identity encoding the EIP-2537 precompiles\n    // accept. Artifacts whose PCS plan never stages an identity commitment\n    // still emit the constant; it costs no runtime bytes beyond the\n    // declaration and keeps the emitters' pointer model uniform.\n    uint256 internal constant       G1_IDENTITY_MPTR = "
@[simp] theorem lit131_eq : lit131 = ";\n\n    // Reserved 4-word slot for the G1 identity (point at infinity) in\n    // EIP-2537 padded form. EVM memory is zero-initialised, and the verifier\n    // never writes to this region, so any read of this slot (the PCS\n    // emitters `mcopy` from it when staging identity commitments) yields\n    // 0,0,0,0 -- exactly the identity encoding the EIP-2537 precompiles\n    // accept. Artifacts whose PCS plan never stages an identity commitment\n    // still emit the constant; it costs no runtime bytes beyond the\n    // declaration and keeps the emitters' pointer model uniform.\n    uint256 internal constant       G1_IDENTITY_MPTR = " := rfl
def lit133 : String := ";\n\n    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain\n    // Solidity proof shim rewrites proof scalars into canonical BE words,\n    // so `calldataload` gives the field element directly. The transcript-\n    // side `evaluations` loop range-checks and spills that value here so\n    // downstream eval references (gate evaluator + PCS q_eval Horner)\n    // become 3-gas `mload(...)` instead of calldata reads.\n    uint256 internal constant     REVERSED_EVALS_MPTR = "
@[simp] theorem lit133_eq : lit133 = ";\n\n    // Decoded polynomial-eval buffer (Optimisation H3). The off-chain\n    // Solidity proof shim rewrites proof scalars into canonical BE words,\n    // so `calldataload` gives the field element directly. The transcript-\n    // side `evaluations` loop range-checks and spills that value here so\n    // downstream eval references (gate evaluator + PCS q_eval Horner)\n    // become 3-gas `mload(...)` instead of calldata reads.\n    uint256 internal constant     REVERSED_EVALS_MPTR = " := rfl
def lit135 : String := ";\n    uint256 internal constant      SELECTOR_ACC_MPTR = "
@[simp] theorem lit135_eq : lit135 = ";\n    uint256 internal constant      SELECTOR_ACC_MPTR = " := rfl
def lit137 : String := ";\n    uint256 internal constant   QUOTIENT_RETURN_MPTR = "
@[simp] theorem lit137_eq : lit137 = ";\n    uint256 internal constant   QUOTIENT_RETURN_MPTR = " := rfl
def lit139 : String := ";\n    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = "
@[simp] theorem lit139_eq : lit139 = ";\n    uint256 internal constant  BATCH_INV_SCRATCH_MPTR = " := rfl
def lit141 : String := ";\n    uint256 internal constant   LAGRANGE_DENOMS_MPTR = "
@[simp] theorem lit141_eq : lit141 = ";\n    uint256 internal constant   LAGRANGE_DENOMS_MPTR = " := rfl
def lit143 : String := ";\n    uint256 internal constant        TRACE_U256_MPTR = "
@[simp] theorem lit143_eq : lit143 = ";\n    uint256 internal constant        TRACE_U256_MPTR = " := rfl
def lit145 : String := ";\n\n    // ----------------------------------------------------------------------\n    // Per-category bases for EIP-2537 padded G1 commitments. The proof\n    // calldata carries 128-byte uncompressed/padded G1s after the off-chain\n    // proof shim repacks midnight-proofs' native compressed stream; this\n    // region stores the 4-word slots used by PCS / quotient-fold sections.\n    //\n    // Cumulative offsets (in words from `comms_mptr_base`):\n    //   ADVICE_COMMS_MPTR_BASE          + 0\n    //   LOOKUP_M_COMMS_MPTR_BASE        + 4*total_advices\n    //   PERM_Z_COMMS_MPTR_BASE          + 4*total_advices + 4*num_lookups\n    //   LOOKUP_HELPER_COMMS_MPTR_BASE   + ... + 4*num_permutation_zs\n    //   LOOKUP_Z_COMMS_MPTR_BASE        + ... + 4*lookup_helper_chunks_total\n    //   TRASHCAN_COMMS_MPTR_BASE        + ... + 4*num_lookups\n    //   QUOTIENT_LIMB_COMMS_MPTR_BASE   + ... + 4*num_trashcans\n    // ----------------------------------------------------------------------\n    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = "
@[simp] theorem lit145_eq : lit145 = ";\n\n    // ----------------------------------------------------------------------\n    // Per-category bases for EIP-2537 padded G1 commitments. The proof\n    // calldata carries 128-byte uncompressed/padded G1s after the off-chain\n    // proof shim repacks midnight-proofs' native compressed stream; this\n    // region stores the 4-word slots used by PCS / quotient-fold sections.\n    //\n    // Cumulative offsets (in words from `comms_mptr_base`):\n    //   ADVICE_COMMS_MPTR_BASE          + 0\n    //   LOOKUP_M_COMMS_MPTR_BASE        + 4*total_advices\n    //   PERM_Z_COMMS_MPTR_BASE          + 4*total_advices + 4*num_lookups\n    //   LOOKUP_HELPER_COMMS_MPTR_BASE   + ... + 4*num_permutation_zs\n    //   LOOKUP_Z_COMMS_MPTR_BASE        + ... + 4*lookup_helper_chunks_total\n    //   TRASHCAN_COMMS_MPTR_BASE        + ... + 4*num_lookups\n    //   QUOTIENT_LIMB_COMMS_MPTR_BASE   + ... + 4*num_trashcans\n    // ----------------------------------------------------------------------\n    uint256 internal constant         ADVICE_COMMS_MPTR_BASE = " := rfl
def lit147 : String := ";\n    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = "
@[simp] theorem lit147_eq : lit147 = ";\n    uint256 internal constant       LOOKUP_M_COMMS_MPTR_BASE = " := rfl
def lit149 : String := ";\n    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = "
@[simp] theorem lit149_eq : lit149 = ";\n    uint256 internal constant         PERM_Z_COMMS_MPTR_BASE = " := rfl
def lit151 : String := ";\n    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = "
@[simp] theorem lit151_eq : lit151 = ";\n    uint256 internal constant  LOOKUP_HELPER_COMMS_MPTR_BASE = " := rfl
def lit153 : String := ";\n    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = "
@[simp] theorem lit153_eq : lit153 = ";\n    uint256 internal constant       LOOKUP_Z_COMMS_MPTR_BASE = " := rfl
def lit155 : String := ";\n    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = "
@[simp] theorem lit155_eq : lit155 = ";\n    uint256 internal constant     TRASHCAN_COMMS_MPTR_BASE = " := rfl
def lit157 : String := ";\n    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = "
@[simp] theorem lit157_eq : lit157 = ";\n    uint256 internal constant QUOTIENT_LIMB_COMMS_MPTR_BASE = " := rfl
def lit159 : String := ";\n\n    // ----------------------------------------------------------------------\n    // Precompile gas bounds: the scheduled EIP-2537 costs, and for modexp the\n    // maximum over the EIP-2565 and EIP-7883 schedules.\n    //\n    // A failing EIP-2537 or modexp call consumes ALL gas supplied to the\n    // STATICCALL, so every generated call site forwards the exact scheduled\n    // cost instead of gas(). A malformed proof point then burns at most the\n    // scheduled cost of the single failing call instead of 63/64 of the\n    // transaction budget. The schedule is the spec-guaranteed worst case\n    // (EIP-2537 \"DDoS protection\" rationale), so these bounds are sufficient\n    // by construction on any conformant chain.\n    //\n    // MODEXP_GAS covers both live modexp schedules: EIP-2565 prices this\n    // frame at 1360, EIP-7883 (Osaka/Fusaka) removes the /3 divisor and\n    // prices it at 4080, so the larger bound is rendered. Forwarding the\n    // EIP-7883 bound on a pre-Osaka chain is free on success -- unused gas is\n    // returned -- while forwarding the EIP-2565 bound on a repriced chain\n    // reverts every proof.\n    //\n    // Liveness caveat: if a future fork reprices these precompiles above the\n    // bounds below, this verifier must be regenerated and redeployed. The\n    // constructor smoke probes forward the same bounds for EVERY precompile\n    // the runtime calls, modexp included, so deployment onto an\n    // already-repriced chain fails fast instead of bricking at proof time.\n    // ----------------------------------------------------------------------\n    uint256 internal constant          G1ADD_GAS = "
@[simp] theorem lit159_eq : lit159 = ";\n\n    // ----------------------------------------------------------------------\n    // Precompile gas bounds: the scheduled EIP-2537 costs, and for modexp the\n    // maximum over the EIP-2565 and EIP-7883 schedules.\n    //\n    // A failing EIP-2537 or modexp call consumes ALL gas supplied to the\n    // STATICCALL, so every generated call site forwards the exact scheduled\n    // cost instead of gas(). A malformed proof point then burns at most the\n    // scheduled cost of the single failing call instead of 63/64 of the\n    // transaction budget. The schedule is the spec-guaranteed worst case\n    // (EIP-2537 \"DDoS protection\" rationale), so these bounds are sufficient\n    // by construction on any conformant chain.\n    //\n    // MODEXP_GAS covers both live modexp schedules: EIP-2565 prices this\n    // frame at 1360, EIP-7883 (Osaka/Fusaka) removes the /3 divisor and\n    // prices it at 4080, so the larger bound is rendered. Forwarding the\n    // EIP-7883 bound on a pre-Osaka chain is free on success -- unused gas is\n    // returned -- while forwarding the EIP-2565 bound on a repriced chain\n    // reverts every proof.\n    //\n    // Liveness caveat: if a future fork reprices these precompiles above the\n    // bounds below, this verifier must be regenerated and redeployed. The\n    // constructor smoke probes forward the same bounds for EVERY precompile\n    // the runtime calls, modexp included, so deployment onto an\n    // already-repriced chain fails fast instead of bricking at proof time.\n    // ----------------------------------------------------------------------\n    uint256 internal constant          G1ADD_GAS = " := rfl
def lit161 : String := ";\n    uint256 internal constant   G1MSM_GAS_1PAIR = "
@[simp] theorem lit161_eq : lit161 = ";\n    uint256 internal constant   G1MSM_GAS_1PAIR = " := rfl
def lit163 : String := ";\n    uint256 internal constant PAIRING_GAS_2PAIR = "
@[simp] theorem lit163_eq : lit163 = ";\n    uint256 internal constant PAIRING_GAS_2PAIR = " := rfl
def lit165 : String := ";\n    uint256 internal constant        MODEXP_GAS = "
@[simp] theorem lit165_eq : lit165 = ";\n    uint256 internal constant        MODEXP_GAS = " := rfl
def lit167 : String := ";\n    // Exact cost of the deployment-time worst-case G1MSM smoke probe.\n    uint256 internal constant G1MSM_GAS_SMOKE = "
@[simp] theorem lit167_eq : lit167 = ";\n    // Exact cost of the deployment-time worst-case G1MSM smoke probe.\n    uint256 internal constant G1MSM_GAS_SMOKE = " := rfl
def lit169 : String := ";"
@[simp] theorem lit169_eq : lit169 = ";" := rfl
def lit171 : String := "\n    // Worst-case accumulator RHS MSM: carried RHS point plus every generated\n    // fixed-base tail scalar nonzero. Zero tail scalars are omitted at\n    // runtime, which only lowers the actual cost below this bound.\n    uint256 internal constant ACC_RHS_MSM_GAS = "
@[simp] theorem lit171_eq : lit171 = "\n    // Worst-case accumulator RHS MSM: carried RHS point plus every generated\n    // fixed-base tail scalar nonzero. Zero tail scalars are omitted at\n    // runtime, which only lowers the actual cost below this bound.\n    uint256 internal constant ACC_RHS_MSM_GAS = " := rfl
def lit173 : String := ";"
@[simp] theorem lit173_eq : lit173 = ";" := rfl
def lit175 : String := ""
@[simp] theorem lit175_eq : lit175 = "" := rfl
def lit177 : String := "\n\n    /// @notice Build identity for this generated artifact (P10/L-8).\n    /// @dev keccak256 over: the domain tag \"halo2-solidity-verifier-build-v1\",\n    ///      the u64-length-prefixed generator feature profile, the vk_digest,\n    ///      the expected VK runtime codehash (zero when the VK is embedded),\n    ///      the SRS fingerprint keccak(\"halo2-solidity-verifier-srs-v1\" || n\n    ///      || G2 || s_g2 || [tau]G1), and an optional 32-byte deployment\n    ///      provenance tag (0x00 marker when absent, 0x01 || tag when set).\n    ///      The deployment record must publish these preimage components so\n    ///      third parties can recompute the id; see\n    ///      docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md.\n    bytes32 public constant BUILD_ID = "
@[simp] theorem lit177_eq : lit177 = "\n\n    /// @notice Build identity for this generated artifact (P10/L-8).\n    /// @dev keccak256 over: the domain tag \"halo2-solidity-verifier-build-v1\",\n    ///      the u64-length-prefixed generator feature profile, the vk_digest,\n    ///      the expected VK runtime codehash (zero when the VK is embedded),\n    ///      the SRS fingerprint keccak(\"halo2-solidity-verifier-srs-v1\" || n\n    ///      || G2 || s_g2 || [tau]G1), and an optional 32-byte deployment\n    ///      provenance tag (0x00 marker when absent, 0x01 || tag when set).\n    ///      The deployment record must publish these preimage components so\n    ///      third parties can recompute the id; see\n    ///      docs/reference/DEPLOYMENT_AND_INCIDENT_RESPONSE.md.\n    bytes32 public constant BUILD_ID = " := rfl
def lit179 : String := ";\n\n    // ----------------------------------------------------------------------\n    // Typed-error selectors (P4/L-3): bytes4(keccak256(\"Name()\")) of the\n    // errors declared on the contract, as Yul-readable constants. The\n    // `fail(sel)` helper in AssemblyHelpers.yul writes the selector to\n    // scratch 0x00 and reverts with 4 bytes. Pinned by\n    // `p4_error_selectors_match_declared_errors` in src/lowering/tests.rs.\n    // ----------------------------------------------------------------------\n    uint256 internal constant ERR_BAD_CALLDATA_SHAPE      = 0x1b99e37c;\n    uint256 internal constant ERR_VK_MISMATCH             = 0xa447d73e;\n    uint256 internal constant ERR_NON_CANONICAL_SCALAR    = 0x77530042;\n    uint256 internal constant ERR_BAD_POINT_ENCODING      = 0xf27905ec;\n    uint256 internal constant ERR_PRECOMPILE_FAILED       = 0x84e81692;\n    uint256 internal constant ERR_PROOF_REJECTED          = 0xc3b0d8cd;\n    uint256 internal constant ERR_QUOTIENT_PROGRAM_INVALID = 0x3cc81b89;\n    uint256 internal constant ERR_MEMORY_LAYOUT_VIOLATED   = 0xc9888d23;\n\n    // BLS12-381 scalar-field modulus, used for transcript challenges and all\n    // Halo2 verifier arithmetic.\n    uint256 internal constant FR_MODULUS        = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;\n\n    // BLS12-381 Fp modulus minus one, split like an EIP-2537 coordinate:\n    // high word = 16 zero bytes || top 16 coordinate bytes, low word =\n    // bottom 32 coordinate bytes.\n    uint256 internal constant BLS_P_HI             = 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7;\n    uint256 internal constant BLS_P_MINUS_ONE_LO   = 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;\n    // Packed public-accumulator sentinels for the shifted coordinate codec.\n    // The `_WITH_ID_FLAG` variant is used only for the first x-coordinate word.\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0 = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa;\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_1 = 0x0000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84;"
@[simp] theorem lit179_eq : lit179 = ";\n\n    // ----------------------------------------------------------------------\n    // Typed-error selectors (P4/L-3): bytes4(keccak256(\"Name()\")) of the\n    // errors declared on the contract, as Yul-readable constants. The\n    // `fail(sel)` helper in AssemblyHelpers.yul writes the selector to\n    // scratch 0x00 and reverts with 4 bytes. Pinned by\n    // `p4_error_selectors_match_declared_errors` in src/lowering/tests.rs.\n    // ----------------------------------------------------------------------\n    uint256 internal constant ERR_BAD_CALLDATA_SHAPE      = 0x1b99e37c;\n    uint256 internal constant ERR_VK_MISMATCH             = 0xa447d73e;\n    uint256 internal constant ERR_NON_CANONICAL_SCALAR    = 0x77530042;\n    uint256 internal constant ERR_BAD_POINT_ENCODING      = 0xf27905ec;\n    uint256 internal constant ERR_PRECOMPILE_FAILED       = 0x84e81692;\n    uint256 internal constant ERR_PROOF_REJECTED          = 0xc3b0d8cd;\n    uint256 internal constant ERR_QUOTIENT_PROGRAM_INVALID = 0x3cc81b89;\n    uint256 internal constant ERR_MEMORY_LAYOUT_VIOLATED   = 0xc9888d23;\n\n    // BLS12-381 scalar-field modulus, used for transcript challenges and all\n    // Halo2 verifier arithmetic.\n    uint256 internal constant FR_MODULUS        = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;\n\n    // BLS12-381 Fp modulus minus one, split like an EIP-2537 coordinate:\n    // high word = 16 zero bytes || top 16 coordinate bytes, low word =\n    // bottom 32 coordinate bytes.\n    uint256 internal constant BLS_P_HI             = 0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7;\n    uint256 internal constant BLS_P_MINUS_ONE_LO   = 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;\n    // Packed public-accumulator sentinels for the shifted coordinate codec.\n    // The `_WITH_ID_FLAG` variant is used only for the first x-coordinate word.\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0 = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa;\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG = 0x00000000f38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa;\n    uint256 internal constant BLS_P_MINUS_ONE_PACKED_1 = 0x0000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84;" := rfl
def lit183 : String := ""
@[simp] theorem lit183_eq : lit183 = "" := rfl

def vkSeg (ctx : PartialCtx) : List Chunk :=
  match ctx.expectedVkCodehash with
  | some expectedVkCodehash =>
      [Chunk.lit lit1,
       Chunk.lit (toString (ctx.vkLen)),
       Chunk.lit lit3,
       Chunk.lit (toString (ctx.vkLen + 1)),
       Chunk.lit lit5,
       Chunk.lit (hexPaddedFilter 64 (expectedVkCodehash.toNat)),
       Chunk.lit lit7]
  | none => []

def vkText (ctx : PartialCtx) : String :=
  match ctx.expectedVkCodehash with
  | some expectedVkCodehash => lit1 ++ (toString (ctx.vkLen)) ++ lit3 ++ (toString (ctx.vkLen + 1)) ++ lit5 ++ (hexPaddedFilter 64 (expectedVkCodehash.toNat)) ++ lit7
  | none => ""

def qeSeg (ctx : PartialCtx) : List Chunk :=
  (match ctx.quotientExternal with
   | some _ =>
       [Chunk.lit lit11] ++
       (match ctx.expectedQuotientCodehash with
        | some expectedQuotientCodehash =>
            [Chunk.lit lit13,
             Chunk.lit (toString (ctx.expectedQuotientLen.getD 0)),
             Chunk.lit lit15,
             Chunk.lit (hexPaddedFilter 64 (expectedQuotientCodehash.toNat)),
             Chunk.lit lit17]
        | none => [])
   | none => [])

def qeText (ctx : PartialCtx) : String :=
  match ctx.quotientExternal with
  | some _ =>
      lit11 ++
      (match ctx.expectedQuotientCodehash with
       | some expectedQuotientCodehash => lit13 ++ (toString (ctx.expectedQuotientLen.getD 0)) ++ lit15 ++ (hexPaddedFilter 64 (expectedQuotientCodehash.toNat)) ++ lit17
       | none => "")
  | none => ""

def fixedSeg (ctx : PartialCtx) : List Chunk :=
  [Chunk.lit lit23,
  Chunk.lit (printPtr ((Ptr.sub ctx.proofCptr 1).value)),
  Chunk.lit lit25,
  Chunk.lit (printPtr (ctx.proofCptr.value)),
  Chunk.lit lit27,
  Chunk.lit (hexPaddedFilter 2 (ctx.numInstanceCptr)),
  Chunk.lit lit29,
  Chunk.lit (hexPaddedFilter 2 (ctx.instanceCptr)),
  Chunk.lit lit31,
  Chunk.lit (hexFilter (ctx.memory.transcriptMptr)),
  Chunk.lit lit33,
  Chunk.lit (hexFilter (ctx.memory.verifierReturnMptr)),
  Chunk.lit lit35,
  Chunk.lit (printPtr (ctx.memory.vkMptr.value)),
  Chunk.lit lit37,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.vkDigest).value)),
  Chunk.lit lit39,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numInstances).value)),
  Chunk.lit lit41,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.k).value)),
  Chunk.lit lit43,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.nInv).value)),
  Chunk.lit lit45,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omega).value)),
  Chunk.lit lit47,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omegaInv).value)),
  Chunk.lit lit49,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omegaInvToL).value)),
  Chunk.lit lit51,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.hasAccumulator).value)),
  Chunk.lit lit53,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.accOffset).value)),
  Chunk.lit lit55,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numAccLimbs).value)),
  Chunk.lit lit57,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numAccLimbBits).value)),
  Chunk.lit lit59,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.g1Base).value)),
  Chunk.lit lit61,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.g2Base).value)),
  Chunk.lit lit63,
  Chunk.lit (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.negSG2Base).value)),
  Chunk.lit lit65,
  Chunk.lit (printPtr (ctx.memory.challengeMptr.value)),
  Chunk.lit lit67,
  Chunk.lit (printPtr (ctx.memory.thetaMptr.value)),
  Chunk.lit lit69,
  Chunk.lit (printPtr (ctx.memory.betaMptr.value)),
  Chunk.lit lit71,
  Chunk.lit (printPtr (ctx.memory.gammaMptr.value)),
  Chunk.lit lit73,
  Chunk.lit (printPtr (ctx.memory.trashChallengeMptr.value)),
  Chunk.lit lit75,
  Chunk.lit (printPtr (ctx.memory.yMptr.value)),
  Chunk.lit lit77,
  Chunk.lit (printPtr (ctx.memory.xMptr.value)),
  Chunk.lit lit79,
  Chunk.lit (printPtr (ctx.memory.x1Mptr.value)),
  Chunk.lit lit81,
  Chunk.lit (printPtr (ctx.memory.x2Mptr.value)),
  Chunk.lit lit83,
  Chunk.lit (printPtr (ctx.memory.x3Mptr.value)),
  Chunk.lit lit85,
  Chunk.lit (printPtr (ctx.memory.x4Mptr.value)),
  Chunk.lit lit87,
  Chunk.lit (printPtr (ctx.memory.fComMptr.value)),
  Chunk.lit lit89,
  Chunk.lit (printPtr (ctx.memory.piMptr.value)),
  Chunk.lit lit91,
  Chunk.lit (printPtr (ctx.memory.accLhsMptr.value)),
  Chunk.lit lit93,
  Chunk.lit (printPtr (ctx.memory.accRhsMptr.value)),
  Chunk.lit lit95,
  Chunk.lit (printPtr (ctx.memory.xNMptr.value)),
  Chunk.lit lit97,
  Chunk.lit (printPtr (ctx.memory.xNMinus1InvMptr.value)),
  Chunk.lit lit99,
  Chunk.lit (printPtr (ctx.memory.lLastMptr.value)),
  Chunk.lit lit101,
  Chunk.lit (printPtr (ctx.memory.lBlindMptr.value)),
  Chunk.lit lit103,
  Chunk.lit (printPtr (ctx.memory.l0Mptr.value)),
  Chunk.lit lit105,
  Chunk.lit (printPtr (ctx.memory.instanceEvalMptr.value)),
  Chunk.lit lit107,
  Chunk.lit (printPtr (ctx.memory.quotientEvalMptr.value)),
  Chunk.lit lit109,
  Chunk.lit (printPtr (ctx.memory.quotientMptr.value)),
  Chunk.lit lit111,
  Chunk.lit (printPtr (ctx.memory.fEvalMptr.value)),
  Chunk.lit lit113,
  Chunk.lit (printPtr (ctx.memory.vMptr.value)),
  Chunk.lit lit115,
  Chunk.lit (printPtr (ctx.memory.finalComMptr.value)),
  Chunk.lit lit117,
  Chunk.lit (printPtr (ctx.memory.pairingLhsMptr.value)),
  Chunk.lit lit119,
  Chunk.lit (printPtr (ctx.memory.pairingRhsMptr.value)),
  Chunk.lit lit121,
  Chunk.lit (printPtr (ctx.memory.rotPointsMptr.value)),
  Chunk.lit lit123,
  Chunk.lit (printPtr (ctx.memory.x1PowersMptr.value)),
  Chunk.lit lit125,
  Chunk.lit (printPtr (ctx.memory.qComMptr.value)),
  Chunk.lit lit127,
  Chunk.lit (printPtr (ctx.memory.qEvalSetMptr.value)),
  Chunk.lit lit129,
  Chunk.lit (printPtr (ctx.memory.qEvalCptrMptr.value)),
  Chunk.lit lit131,
  Chunk.lit (printPtr (ctx.memory.g1IdentityMptr.value)),
  Chunk.lit lit133,
  Chunk.lit (printPtr (ctx.memory.reversedEvalsMptr.value)),
  Chunk.lit lit135,
  Chunk.lit (hexFilter (ctx.memory.selectorAccMptr)),
  Chunk.lit lit137,
  Chunk.lit (hexFilter (ctx.memory.quotientReturnMptr)),
  Chunk.lit lit139,
  Chunk.lit (hexFilter (ctx.memory.batchInvertScratchMptr)),
  Chunk.lit lit141,
  Chunk.lit (hexFilter (ctx.memory.lagrangeDenomsMptr)),
  Chunk.lit lit143,
  Chunk.lit (hexFilter (ctx.memory.traceU256Mptr)),
  Chunk.lit lit145,
  Chunk.lit (printPtr (ctx.memory.adviceCommsMptrBase.value)),
  Chunk.lit lit147,
  Chunk.lit (printPtr (ctx.memory.lookupMCommsMptrBase.value)),
  Chunk.lit lit149,
  Chunk.lit (printPtr (ctx.memory.permZCommsMptrBase.value)),
  Chunk.lit lit151,
  Chunk.lit (printPtr (ctx.memory.lookupHelperCommsMptrBase.value)),
  Chunk.lit lit153,
  Chunk.lit (printPtr (ctx.memory.lookupZCommsMptrBase.value)),
  Chunk.lit lit155,
  Chunk.lit (printPtr (ctx.memory.trashcanCommsMptrBase.value)),
  Chunk.lit lit157,
  Chunk.lit (printPtr (ctx.memory.quotientLimbCommsMptrBase.value)),
  Chunk.lit lit159,
  Chunk.lit (toString (ctx.templateConstants.gas.g1add)),
  Chunk.lit lit161,
  Chunk.lit (toString (ctx.templateConstants.gas.g1msmOnePair)),
  Chunk.lit lit163,
  Chunk.lit (toString (ctx.templateConstants.gas.pairingTwoPair)),
  Chunk.lit lit165,
  Chunk.lit (toString (ctx.templateConstants.gas.modexp)),
  Chunk.lit lit167,
  Chunk.lit (toString (ctx.constructorG1msmSmokeGas)),
  Chunk.lit lit169]

def fixedText (ctx : PartialCtx) : String :=
  lit23 ++ (printPtr ((Ptr.sub ctx.proofCptr 1).value)) ++ lit25 ++ (printPtr (ctx.proofCptr.value)) ++ lit27 ++ (hexPaddedFilter 2 (ctx.numInstanceCptr)) ++ lit29 ++ (hexPaddedFilter 2 (ctx.instanceCptr)) ++ lit31 ++ (hexFilter (ctx.memory.transcriptMptr)) ++ lit33 ++ (hexFilter (ctx.memory.verifierReturnMptr)) ++ lit35 ++ (printPtr (ctx.memory.vkMptr.value)) ++ lit37 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.vkDigest).value)) ++ lit39 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numInstances).value)) ++ lit41 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.k).value)) ++ lit43 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.nInv).value)) ++ lit45 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omega).value)) ++ lit47 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omegaInv).value)) ++ lit49 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.omegaInvToL).value)) ++ lit51 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.hasAccumulator).value)) ++ lit53 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.accOffset).value)) ++ lit55 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numAccLimbs).value)) ++ lit57 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.numAccLimbBits).value)) ++ lit59 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.g1Base).value)) ++ lit61 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.g2Base).value)) ++ lit63 ++ (printPtr ((Ptr.add ctx.memory.vkMptr ctx.vkHeader.negSG2Base).value)) ++ lit65 ++ (printPtr (ctx.memory.challengeMptr.value)) ++ lit67 ++ (printPtr (ctx.memory.thetaMptr.value)) ++ lit69 ++ (printPtr (ctx.memory.betaMptr.value)) ++ lit71 ++ (printPtr (ctx.memory.gammaMptr.value)) ++ lit73 ++ (printPtr (ctx.memory.trashChallengeMptr.value)) ++ lit75 ++ (printPtr (ctx.memory.yMptr.value)) ++ lit77 ++ (printPtr (ctx.memory.xMptr.value)) ++ lit79 ++ (printPtr (ctx.memory.x1Mptr.value)) ++ lit81 ++ (printPtr (ctx.memory.x2Mptr.value)) ++ lit83 ++ (printPtr (ctx.memory.x3Mptr.value)) ++ lit85 ++ (printPtr (ctx.memory.x4Mptr.value)) ++ lit87 ++ (printPtr (ctx.memory.fComMptr.value)) ++ lit89 ++ (printPtr (ctx.memory.piMptr.value)) ++ lit91 ++ (printPtr (ctx.memory.accLhsMptr.value)) ++ lit93 ++ (printPtr (ctx.memory.accRhsMptr.value)) ++ lit95 ++ (printPtr (ctx.memory.xNMptr.value)) ++ lit97 ++ (printPtr (ctx.memory.xNMinus1InvMptr.value)) ++ lit99 ++ (printPtr (ctx.memory.lLastMptr.value)) ++ lit101 ++ (printPtr (ctx.memory.lBlindMptr.value)) ++ lit103 ++ (printPtr (ctx.memory.l0Mptr.value)) ++ lit105 ++ (printPtr (ctx.memory.instanceEvalMptr.value)) ++ lit107 ++ (printPtr (ctx.memory.quotientEvalMptr.value)) ++ lit109 ++ (printPtr (ctx.memory.quotientMptr.value)) ++ lit111 ++ (printPtr (ctx.memory.fEvalMptr.value)) ++ lit113 ++ (printPtr (ctx.memory.vMptr.value)) ++ lit115 ++ (printPtr (ctx.memory.finalComMptr.value)) ++ lit117 ++ (printPtr (ctx.memory.pairingLhsMptr.value)) ++ lit119 ++ (printPtr (ctx.memory.pairingRhsMptr.value)) ++ lit121 ++ (printPtr (ctx.memory.rotPointsMptr.value)) ++ lit123 ++ (printPtr (ctx.memory.x1PowersMptr.value)) ++ lit125 ++ (printPtr (ctx.memory.qComMptr.value)) ++ lit127 ++ (printPtr (ctx.memory.qEvalSetMptr.value)) ++ lit129 ++ (printPtr (ctx.memory.qEvalCptrMptr.value)) ++ lit131 ++ (printPtr (ctx.memory.g1IdentityMptr.value)) ++ lit133 ++ (printPtr (ctx.memory.reversedEvalsMptr.value)) ++ lit135 ++ (hexFilter (ctx.memory.selectorAccMptr)) ++ lit137 ++ (hexFilter (ctx.memory.quotientReturnMptr)) ++ lit139 ++ (hexFilter (ctx.memory.batchInvertScratchMptr)) ++ lit141 ++ (hexFilter (ctx.memory.lagrangeDenomsMptr)) ++ lit143 ++ (hexFilter (ctx.memory.traceU256Mptr)) ++ lit145 ++ (printPtr (ctx.memory.adviceCommsMptrBase.value)) ++ lit147 ++ (printPtr (ctx.memory.lookupMCommsMptrBase.value)) ++ lit149 ++ (printPtr (ctx.memory.permZCommsMptrBase.value)) ++ lit151 ++ (printPtr (ctx.memory.lookupHelperCommsMptrBase.value)) ++ lit153 ++ (printPtr (ctx.memory.lookupZCommsMptrBase.value)) ++ lit155 ++ (printPtr (ctx.memory.trashcanCommsMptrBase.value)) ++ lit157 ++ (printPtr (ctx.memory.quotientLimbCommsMptrBase.value)) ++ lit159 ++ (toString (ctx.templateConstants.gas.g1add)) ++ lit161 ++ (toString (ctx.templateConstants.gas.g1msmOnePair)) ++ lit163 ++ (toString (ctx.templateConstants.gas.pairingTwoPair)) ++ lit165 ++ (toString (ctx.templateConstants.gas.modexp)) ++ lit167 ++ (toString (ctx.constructorG1msmSmokeGas)) ++ lit169

def accSeg (ctx : PartialCtx) : List Chunk :=
  if ctx.expectedHasAccumulator then
    [Chunk.lit lit171,
     Chunk.lit (toString (ctx.accRhsMsmGas)),
     Chunk.lit lit173]
  else []

def accText (ctx : PartialCtx) : String :=
  if ctx.expectedHasAccumulator then lit171 ++ (toString (ctx.accRhsMsmGas)) ++ lit173 else ""

def buildSeg (ctx : PartialCtx) : List Chunk :=
  [Chunk.lit lit177,
   Chunk.lit (hexPaddedFilter 64 (ctx.buildId.toNat)),
   Chunk.lit lit179]

def buildText (ctx : PartialCtx) : String :=
  lit177 ++ (hexPaddedFilter 64 (ctx.buildId.toNat)) ++ lit179

def directSeg (ctx : PartialCtx) : List Chunk :=
  match ctx.quotientDirect with
  | some qdirect =>
      [Chunk.lit (jinjaFor qdirect.constants (fun line loop =>
        "\n    " ++ line))]
  | none => []

def directText (ctx : PartialCtx) : String :=
  match ctx.quotientDirect with
  | some qdirect =>
      jinjaFor qdirect.constants (fun line loop =>
        "\n    " ++ line)
  | none => ""

def renderConstantsChunks (ctx : PartialCtx) : List Chunk :=
  vkSeg ctx ++ qeSeg ctx ++ fixedSeg ctx ++ accSeg ctx ++ buildSeg ctx ++ directSeg ctx

theorem foldl_append_eq (s : String) (ss : List String) :
    List.foldl (· ++ ·) s ss = s ++ List.foldl (· ++ ·) "" ss := by
  induction ss generalizing s with
  | nil => simp [List.foldl]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (s ++ x), ih ("" ++ x)]
      simp [String.append_assoc]

theorem join_cons (s : String) (ss : List String) :
    String.join (s :: ss) = s ++ String.join ss := by
  simp only [String.join_eq_foldl, List.foldl_cons]
  rw [foldl_append_eq]
  simp

theorem linesOfChunks_spec (cs : List Chunk) :
    String.intercalate "\n" (linesOfChunks cs) = String.join (cs.map Chunk.text) := by
  induction cs with
  | nil => simp [linesOfChunks, String.join, List.foldl]
  | cons c cs ih =>
      cases c with
      | lit s =>
          simp only [linesOfChunks, Chunk.text, List.map_cons, join_cons]
          rw [prepend_intercalate]
          · rw [Midfall.Generator.SplitOnLines.intercalate_splitOn_newline, ih]
          · exact Midfall.Generator.SplitOnLines.splitOn_newline_ne_nil s
          · exact linesOfChunks_ne_nil cs

theorem linesOfChunks_no_nl (cs : List Chunk) :
    ∀ l ∈ linesOfChunks cs, '\n' ∉ l.toList := by
  induction cs with
  | nil => simp [linesOfChunks]
  | cons c cs ih =>
      cases c with
      | lit s =>
          simp only [linesOfChunks]
          apply prepend_no_nl
          · exact Midfall.Generator.SplitOnLines.splitOn_newline_no_nl s
          · exact ih

theorem splitOn_newline_chunks (cs : List Chunk) :
    (String.join (cs.map Chunk.text)).splitOn "\n" = linesOfChunks cs := by
  rw [← linesOfChunks_spec]
  exact Midfall.Generator.SplitOnLines.splitOn_intercalate_newline _
    (linesOfChunks_ne_nil _) (linesOfChunks_no_nl _)

theorem vk_eq (ctx : PartialCtx) :
    vkText ctx = String.join ((vkSeg ctx).map Chunk.text) := by
  unfold vkText vkSeg
  cases ctx.expectedVkCodehash <;> rfl

theorem qe_eq (ctx : PartialCtx) :
    qeText ctx = String.join ((qeSeg ctx).map Chunk.text) := by
  unfold qeText qeSeg
  cases ctx.quotientExternal <;> cases ctx.expectedQuotientCodehash <;> rfl

theorem fixed_eq (ctx : PartialCtx) :
    fixedText ctx = String.join ((fixedSeg ctx).map Chunk.text) := by
  rfl

theorem acc_eq (ctx : PartialCtx) :
    accText ctx = String.join ((accSeg ctx).map Chunk.text) := by
  unfold accText accSeg
  cases ctx.expectedHasAccumulator <;> rfl

theorem build_eq (ctx : PartialCtx) :
    buildText ctx = String.join ((buildSeg ctx).map Chunk.text) := by
  rfl

theorem direct_eq (ctx : PartialCtx) :
    directText ctx = String.join ((directSeg ctx).map Chunk.text) := by
  unfold directText directSeg
  cases ctx.quotientDirect <;> rfl

def renderConstantsLines (ctx : PartialCtx) : List String :=
  linesOfChunks (renderConstantsChunks ctx)

theorem renderConstantsLines_ne_nil (ctx : PartialCtx) :
    renderConstantsLines ctx ≠ [] :=
  linesOfChunks_ne_nil _

theorem renderConstantsLines_no_nl (ctx : PartialCtx) :
    ∀ l ∈ renderConstantsLines ctx, '\n' ∉ l.toList :=
  linesOfChunks_no_nl _

/-- The line list of the template chunks is the split of their concatenation.
    This is the generic half of the `renderConstants` split equality; the other
    half is the definitional reassociation `renderConstants = join chunks`. -/
theorem splitOn_renderConstantsChunks (ctx : PartialCtx) :
    (String.join ((renderConstantsChunks ctx).map Chunk.text)).splitOn "\n" =
      renderConstantsLines ctx :=
  splitOn_newline_chunks _

end Midfall.Generator.ConstLines