// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// Auto-generated: Solidity port of the Rust PLONK verifier
/// (`proofs/src/plonk/verifier.rs`) specialised for the poseidon example.
///
/// The comments have been preserved verbatim from the Rust source so that the
/// structural correspondence between the two implementations is explicit.
///
/// BLS12-381 operations use the EIP-2537 Prague precompiles:
///   * 0x0b  BLS12_G1ADD            (256 -> 128 bytes)
///   * 0x0c  BLS12_G1MSM            (variable)
///   * 0x0f  BLS12_PAIRING_CHECK    (variable -> 32 bytes = 0x01 / 0x00)
///
/// The Fiat-Shamir transcript is `sha3::Keccak256` matching
/// `midnight_proofs::transcript::CircuitTranscript<Keccak256>`:
///   * init: hasher absorbs "Domain separator for transcript"
///   * common(x):  hasher.update([PREFIX_COMMON=1]); hasher.update(x)
///   * squeeze():  h1 = keccak(state || [0]); h2 = keccak(state || [1]);
///                 out = h1 || h2 (64 bytes); state = keccak(out)

interface IPoseidonVerifyingKey {}

contract PoseidonVerifier {
    /* ------------------------------------------------------------------ *
     *  CONSTANTS                                                         *
     * ------------------------------------------------------------------ */

    /// BLS12-381 scalar field modulus (BE).
    uint256 private constant FR_MODULUS =
        0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001;

    /// BLS12-381 base-field modulus p (381-bit, upper and lower halves).
    /// p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624_1eabfffeb153ffffb9feffffffffaaab
    uint256 private constant FP_MODULUS_HI =
        0x000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd7;
    uint256 private constant FP_MODULUS_LO =
        0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab;

    /// (p + 1) / 4, used as the exponent in the BLS12-381 tonelli-shanks-free
    /// square root (since p ≡ 3 mod 4, sqrt(a) = a^((p+1)/4) mod p). The
    /// value (48 bytes big-endian) is
    ///   0x0680447a8e5ff9a692c6e9ed90d2eb35
    ///     d91dd2e13ce144afd9cc34a83dac3d89
    ///     07aaffffac54ffffee7fbfffffffeaab
    /// (split here across three 128-bit lines for legibility).
    uint256 private constant FP_SQRT_EXP_HI =
        0x000000000000000000000000000000000680447a8e5ff9a692c6e9ed90d2eb35;
    uint256 private constant FP_SQRT_EXP_LO =
        0xd91dd2e13ce144afd9cc34a83dac3d8907aaffffac54ffffee7fbfffffffeaab;

    /// Transcript byte-prefixes.
    uint8 private constant PREFIX_COMMON    = 1;
    uint8 private constant PREFIX_CHALLENGE = 0;

    /// EIP-2537 precompile addresses (Prague).
    address private constant PC_G1ADD   = address(0x0b);
    address private constant PC_G1MSM   = address(0x0c);
    address private constant PC_PAIRING = address(0x0f);
    address private constant PC_MODEXP  = address(0x05);

    /// Memory layout constant: VK blob is returned by the VK contract's
    /// constructor as code and we RETURNDATACOPY it at verification time.
    address public immutable VK_CONTRACT;

    /* ------------------------------------------------------------------ *
     *  Traced events (one per transcript op, for equivalence testing)    *
     * ------------------------------------------------------------------ */

    event TraceChallenge(string name, bytes32 feBE);
    event TraceReadScalar(string tag, bytes32 feBE);
    event TraceReadPoint(string tag, bytes p128);
    event TraceIntermediate(string tag, bytes32 feBE);
    event TracePairing(bool ok);

    /* ------------------------------------------------------------------ *
     *  Gas benchmark markers                                             *
     * ------------------------------------------------------------------ */

    event PhaseGas(string name, uint256 gasUsed);

    constructor(address vk) {
        VK_CONTRACT = vk;
    }

    /* ------------------------------------------------------------------ *
     *  Keccak256 transcript helpers (matching Rust TranscriptHash impl)  *
     * ------------------------------------------------------------------ */

    /// Initialise the transcript state. Matches the Rust side:
    ///   Keccak256::new().update("Domain separator for transcript").
    ///
    /// We keep the running state as the *cumulative input bytes* rather than
    /// the intermediate hasher state, because Solidity's keccak256 opcode
    /// only supports one-shot hashing. `squeeze` re-hashes everything.
    /// This is functionally equivalent because Keccak256 is a sponge: any
    /// `update` sequence producing the same byte stream yields the same
    /// final digest, and our `squeeze` forks two transcripts each with a
    /// one-byte tag and then reseeds with the 64-byte concatenation.
    struct Transcript {
        bytes buf;
    }

    function _initTranscript() internal pure returns (Transcript memory t) {
        t.buf = abi.encodePacked("Domain separator for transcript");
    }

    function _absorb(Transcript memory t, bytes memory input) internal pure {
        t.buf = abi.encodePacked(t.buf, PREFIX_COMMON, input);
    }

    function _absorbScalar(Transcript memory t, bytes32 scalarLE) internal pure {
        // The Rust side absorbs scalars in their LE 32-byte canonical form
        // (Hashable<Keccak256> for Fq uses to_repr()).
        t.buf = abi.encodePacked(t.buf, PREFIX_COMMON, scalarLE);
    }

    function _absorbG1Compressed(Transcript memory t, bytes memory compressed48)
        internal pure
    {
        // The Rust side absorbs G1 points in their *compressed* 48-byte BLS
        // form (Hashable<Keccak256> for G1Projective -> to_bytes()).
        t.buf = abi.encodePacked(t.buf, PREFIX_COMMON, compressed48);
    }

    /// Squeeze a 64-byte challenge and reseed the transcript with it.
    /// Matches Rust `TranscriptHash::squeeze` for Keccak256 in
    /// `proofs/src/transcript/implementors.rs`.
    function _squeeze64(Transcript memory t) internal view returns (bytes memory out) {
        bytes32 h1 = keccak256(abi.encodePacked(t.buf, PREFIX_CHALLENGE, uint8(0)));
        bytes32 h2 = keccak256(abi.encodePacked(t.buf, PREFIX_CHALLENGE, uint8(1)));
        out = abi.encodePacked(h1, h2);
        // Re-seed: state = Keccak256::new().update(out)
        t.buf = bytes(out);
    }

    /// Squeeze a field-element challenge via uniform bytes reduction.
    /// Matches `Sampleable<Keccak256> for midnight_curves::Fq` which does
    /// `Fq::from_uniform_bytes(bytes)` on the 64-byte squeeze output.
    function _squeezeFq(Transcript memory t) internal view returns (bytes32) {
        bytes memory u = _squeeze64(t);
        // from_uniform_bytes: interpret the 64 bytes as a 512-bit integer
        // (little-endian in blst) and reduce mod r. Halo2curves blst uses
        // `blst_fr_from_uniform_bytes` which expects big-endian. We follow
        // the actual midnight_curves impl which treats the buffer as a
        // little-endian 512-bit integer and returns it mod r.
        return _fromUniformBytesLE(u);
    }

    /// Equivalent to `midnight_curves::Fq::from_uniform_bytes`. Unrolled:
    ///
    ///     let (a0, a1) = bytes.split_at(32);   // a0 = bytes[0..32]
    ///     let a0 = Fq_from_Montgomery_limbs(a0.as_le_u64_array());
    ///     let a1 = Fq_from_Montgomery_limbs(a1.as_le_u64_array());
    ///     result = a0.mul(R2) + a1.mul(R3)
    ///
    /// Working through the Montgomery algebra (R = 2^256 mod r):
    ///
    ///     a0_actual = a0_bytes * R^-1
    ///     R2_actual = R
    ///     a0.mul(R2) actual = a0_bytes * R^-1 * R = a0_bytes
    ///
    ///     a1.mul(R3) actual = a1_bytes * R^-1 * R^2 = a1_bytes * R
    ///
    ///     result    = a0_bytes + a1_bytes * R (mod r)
    ///               = LE(bytes[0..32]) + LE(bytes[32..64]) * 2^256 (mod r)
    ///               = LE interpretation of the whole 64-byte buffer mod r.
    function _fromUniformBytesLE(bytes memory u) internal pure returns (bytes32) {
        require(u.length == 64, "uniform bytes must be 64");
        // `mload` reads 32 bytes as a big-endian uint256 in Solidity. To
        // recover the caller's little-endian interpretation we reverse the
        // byte order.
        uint256 w0_be;
        uint256 w1_be;
        assembly {
            w0_be := mload(add(u, 32))  // bytes[0..32]  (BE-interpreted)
            w1_be := mload(add(u, 64))  // bytes[32..64] (BE-interpreted)
        }
        uint256 lo = _swapEndian(w0_be); // LE value of bytes[0..32]
        uint256 hi = _swapEndian(w1_be); // LE value of bytes[32..64]
        // 2^256 mod FR_MODULUS for the BLS12-381 scalar field. Computed via
        //   sage> mod(2^256, 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
        //   sage> 0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe
        uint256 TWO_256_MOD_R =
            0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe;
        uint256 hi_r = hi % FR_MODULUS;
        uint256 lo_r = lo % FR_MODULUS;
        return bytes32(addmod(mulmod(hi_r, TWO_256_MOD_R, FR_MODULUS), lo_r, FR_MODULUS));
    }

    function _swapEndian(uint256 x) internal pure returns (uint256 r) {
        // Byte-swap a 256-bit word.
        uint256 v = x;
        assembly {
            r := 0
            for { let i := 0 } lt(i, 32) { i := add(i, 1) } {
                r := or(shl(8, r), and(v, 0xff))
                v := shr(8, v)
            }
        }
    }

    /* ------------------------------------------------------------------ *
     *  EIP-2537 BLS12-381 precompile wrappers (Prague)                   *
     * ------------------------------------------------------------------ */

    /// G1 addition via 0x0b. Input: 256 bytes (two G1 points). Output: 128.
    function _g1Add(bytes memory a, bytes memory b) internal view returns (bytes memory) {
        require(a.length == 128 && b.length == 128, "bad G1 len");
        bytes memory input = abi.encodePacked(a, b);
        (bool ok, bytes memory out) = PC_G1ADD.staticcall(input);
        require(ok, "G1ADD failed");
        return out;
    }

    /// G1 MSM via 0x0c. Each (point, scalar) pair is 128+32 = 160 bytes.
    function _g1Msm(bytes memory pointsAndScalars) internal view returns (bytes memory) {
        require(pointsAndScalars.length % 160 == 0 && pointsAndScalars.length > 0, "bad MSM len");
        (bool ok, bytes memory out) = PC_G1MSM.staticcall(pointsAndScalars);
        require(ok, "G1MSM failed");
        return out;
    }

    /// Pairing check via 0x0f. Each (G1, G2) pair = 128+256 = 384 bytes.
    /// Returns 0x01 if sum of pairings equals the identity.
    ///
    /// NB: Per EIP-2537, an invalid input (off-curve point, not in subgroup,
    /// wrong y) causes the precompile to consume *all* gas forwarded. We
    /// therefore cap the forwarded gas to a generous upper bound — valid
    /// inputs cost ~120k gas for two pairs — so that a buggy port doesn't
    /// silently exhaust the test harness's gas budget.
    function _pairingCheck(bytes memory pairs) internal view returns (bool) {
        require(pairs.length % 384 == 0 && pairs.length > 0, "bad pairing len");
        uint256 gasCap = 2_000_000;
        address precompile = PC_PAIRING;
        bool ok;
        bytes32 result;
        assembly {
            let ptr := add(pairs, 32)
            let sz  := mload(pairs)
            let ok0 := staticcall(gasCap, precompile, ptr, sz, 0, 32)
            ok := ok0
            result := mload(0)
        }
        if (!ok) return false;
        return uint256(result) == 1;
    }

    /// Public view wrapper around the internal decompressor so that unit
    /// tests can cross-check Solidity decompression against Rust fixtures
    /// before the (much larger) full-verifier path exercises it.
    function decompressG1(bytes calldata c48) external view returns (bytes memory) {
        bytes memory c = new bytes(48);
        for (uint256 i = 0; i < 48; i++) c[i] = c48[i];
        return _g1CompressedToEip2537(c);
    }

    /* ------------------------------------------------------------------ *
     *  Permutation-argument expressions (Phase A1 step 2)                *
     *                                                                    *
     *  Port of `midnight_proofs::plonk::permutation::expressions` from   *
     *  proofs/src/plonk/permutation.rs:180+. Consumes the VK blob's      *
     *  permutation-column metadata (kind + query_idx per column) plus   *
     *  the transcript-read evaluations to produce the iterator of       *
     *  scalar expressions that the main `partially_evaluate_identities` *
     *  driver appends alongside the gate contributions.                 *
     *                                                                    *
     *  For the poseidon circuit this produces 7 scalars:                *
     *    1  × first-set:        l_0 · (1 − z_0.prod)                    *
     *    1  × last-set:         l_last · (z_l.prod² − z_l.prod)         *
     *    2  × cross-boundary:   (z_i.prod − z_{i-1}.last) · l_0         *
     *    3  × main-chunk:       (left − right) · (1 − l_last − l_blind) *
     *                                                                    *
     *  where left/right are products over each chunk's columns using    *
     *  β, γ, x, and powers of the scalar-field DELTA constant.          *
     * ------------------------------------------------------------------ */

    /// BLS12-381 scalar field DELTA constant (as encoded by the Rust
    /// `midnight_curves::Fq::DELTA` — the canonical non-Montgomery value
    /// via `to_repr()`). Dumped verbatim into the permutation fixture
    /// for cross-checking. Hard-coding avoids one field read per chunk.
    uint256 internal constant FR_DELTA =
        0x08634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7;

    struct PermSet {
        uint256 prod;
        uint256 next;
        uint256 last;   // only read if hasLast == true
        bool hasLast;
    }

    struct PermEnv {
        uint256 beta;
        uint256 gamma;
        uint256 x;
        uint256 l0;
        uint256 lLast;
        uint256 lBlind;
        PermSet[] sets;
        uint256[] permEvals;
        uint256[] adviceEvals;
        uint256[] fixedEvals;
        uint256[] instanceEvals;
        uint8[] colKinds;       // permutation column kinds (0/1/2)
        uint16[] colQueryIdxs;  // permutation column cur-rotation query indices
        uint256 chunkLen;       // cs_degree - 2
    }

    function _permLookupEval(PermEnv memory env, uint256 colIdx)
        private pure returns (uint256)
    {
        uint8 kind = env.colKinds[colIdx];
        uint16 qidx = env.colQueryIdxs[colIdx];
        if (kind == 0) return env.adviceEvals[qidx];
        if (kind == 1) return env.fixedEvals[qidx];
        return env.instanceEvals[qidx];
    }

    function _permExpressions(PermEnv memory env)
        internal pure returns (uint256[] memory out)
    {
        uint256 nCols = env.colKinds.length;
        uint256 nChunks = env.sets.length;
        require(env.permEvals.length == nCols, "permEvals length");
        require(env.colQueryIdxs.length == nCols, "colQueryIdxs length");

        // First-set + last-set + cross-boundary + per-chunk.
        uint256 nExprs = (nChunks > 0 ? 2 : 0) + (nChunks > 0 ? nChunks - 1 : 0) + nChunks;
        out = new uint256[](nExprs);
        uint256 outIdx = 0;

        if (nChunks > 0) {
            // l_0 * (1 - z_0.prod)
            uint256 oneMinusProd = _frSub(1, env.sets[0].prod);
            out[outIdx++] = _frMul(env.l0, oneMinusProd);
            // l_last * (z_l.prod² - z_l.prod)
            uint256 zl = env.sets[nChunks - 1].prod;
            uint256 zlSq = _frMul(zl, zl);
            out[outIdx++] = _frMul(env.lLast, _frSub(zlSq, zl));
        }

        // Cross-chunk boundary.
        for (uint256 i = 1; i < nChunks; i++) {
            require(env.sets[i - 1].hasLast, "non-last chunk missing last eval");
            uint256 diff = _frSub(env.sets[i].prod, env.sets[i - 1].last);
            out[outIdx++] = _frMul(diff, env.l0);
        }

        // Precompute (1 - l_last - l_blind).
        uint256 oneMinusBoundary = _frSub(_frSub(1, env.lLast), env.lBlind);

        for (uint256 chunkIdx = 0; chunkIdx < nChunks; chunkIdx++) {
            uint256 colStart = chunkIdx * env.chunkLen;
            uint256 colEndRaw = colStart + env.chunkLen;
            uint256 colEnd = colEndRaw > nCols ? nCols : colEndRaw;

            // left = set.next; for (col, pev): left *= (eval + β·pev + γ)
            uint256 left = env.sets[chunkIdx].next;
            for (uint256 c = colStart; c < colEnd; c++) {
                uint256 ev = _permLookupEval(env, c);
                uint256 term = _frAdd(_frAdd(ev, _frMul(env.beta, env.permEvals[c])), env.gamma);
                left = _frMul(left, term);
            }
            // right = set.prod; current_delta = β·x·DELTA^(chunkIdx·chunkLen)
            // For each col: right *= (eval + current_delta + γ); current_delta *= DELTA
            uint256 right = env.sets[chunkIdx].prod;
            uint256 currentDelta = _frMul(env.beta, env.x);
            // Multiply by DELTA^(chunkIdx * chunkLen) using repeated squaring.
            currentDelta = _frMul(currentDelta, _frDeltaPow(chunkIdx * env.chunkLen));
            for (uint256 c = colStart; c < colEnd; c++) {
                uint256 ev = _permLookupEval(env, c);
                uint256 term = _frAdd(_frAdd(ev, currentDelta), env.gamma);
                right = _frMul(right, term);
                currentDelta = _frMul(currentDelta, FR_DELTA);
            }
            out[outIdx++] = _frMul(_frSub(left, right), oneMinusBoundary);
        }
    }

    /// DELTA^n mod r via repeated squaring. Equivalent to
    /// `_frPow(FR_DELTA, n)` but `pure` (no ModExp precompile needed
    /// because the exponent fits in uint256 and we can square in-word).
    function _frDeltaPow(uint256 n) internal pure returns (uint256) {
        uint256 result = 1;
        uint256 base = FR_DELTA;
        while (n > 0) {
            if (n & 1 == 1) result = mulmod(result, base, FR_MODULUS);
            base = mulmod(base, base, FR_MODULUS);
            n >>= 1;
        }
        return result;
    }

    /// Public wrapper so the forge test can feed the fixture inputs
    /// directly and compare against Rust-computed expected values.
    function permExpressions(
        uint256[6] calldata envScalars,
        uint256[] calldata setsFlat,   // {prod, next, last, hasLast(0/1)} × nChunks, flat
        uint256[] calldata permEvals,
        uint256[] calldata adviceEvals,
        uint256[] calldata fixedEvals,
        uint256[] calldata instanceEvals,
        uint8[] calldata colKinds,
        uint16[] calldata colQueryIdxs,
        uint256 chunkLen
    ) external pure returns (uint256[] memory) {
        require(setsFlat.length % 4 == 0, "sets must be 4-tuples");
        uint256 nChunks = setsFlat.length / 4;
        PermSet[] memory sets = new PermSet[](nChunks);
        for (uint256 i = 0; i < nChunks; i++) {
            sets[i] = PermSet({
                prod: setsFlat[4 * i],
                next: setsFlat[4 * i + 1],
                last: setsFlat[4 * i + 2],
                hasLast: setsFlat[4 * i + 3] != 0
            });
        }
        PermEnv memory env = PermEnv({
            beta: envScalars[0],
            gamma: envScalars[1],
            x: envScalars[2],
            l0: envScalars[3],
            lLast: envScalars[4],
            lBlind: envScalars[5],
            sets: sets,
            permEvals: _copyToMemArr(permEvals),
            adviceEvals: _copyToMemArr(adviceEvals),
            fixedEvals: _copyToMemArr(fixedEvals),
            instanceEvals: _copyToMemArr(instanceEvals),
            colKinds: _copyU8(colKinds),
            colQueryIdxs: _copyU16(colQueryIdxs),
            chunkLen: chunkLen
        });
        return _permExpressions(env);
    }

    function _copyU8(uint8[] calldata a) private pure returns (uint8[] memory b) {
        b = new uint8[](a.length);
        for (uint256 i = 0; i < a.length; i++) b[i] = a[i];
    }

    function _copyU16(uint16[] calldata a) private pure returns (uint16[] memory b) {
        b = new uint16[](a.length);
        for (uint256 i = 0; i < a.length; i++) b[i] = a[i];
    }

    /* ------------------------------------------------------------------ *
     *  Lookup-argument expressions (Phase A2a)                           *
     *                                                                    *
     *  Port of `midnight_proofs::plonk::logup::Evaluated::expressions`   *
     *  from proofs/src/plonk/logup.rs:400+. Walks the VK blob's lookup   *
     *  bytecode section in step with the transcript-read lookup         *
     *  evaluations to produce the scalar expressions appended to the    *
     *  `partially_evaluate_identities` output.                          *
     *                                                                    *
     *  Per lookup this produces (num_chunks + 2) scalars:               *
     *    1  × boundary:      (l_0 + l_last) · Z                         *
     *    k  × helpers:       helper_eval_i · ∏ⱼ(fⱼ+β) − Σⱼ ∏_{k≠j}(fₖ+β) *
     *    1  × accumulator:   ((Z_next − Z − s·Σh)·(t+β) + m) · active   *
     * ------------------------------------------------------------------ */

    struct LookupEnv {
        uint256 theta;
        uint256 beta;
        uint256 l0;
        uint256 lLast;
        uint256 lBlind;
        uint256 accumulatorEval;
        uint256 accumulatorNextEval;
        uint256 multiplicitiesEval;
        uint256[] helperEvals;
        // Shared with bytecode evaluation:
        uint256[] adviceEvals;
        uint256[] fixedEvals;
        uint256[] instanceEvals;
        uint256[] challenges;
    }

    /// Compress a list of expression bytecodes via θ-folding
    /// (`acc = acc·θ + eval`). `buf` is a concatenation of
    /// `num_exprs` RPN programs each ending in END, with a 4-byte
    /// big-endian length prefix. The `offset` in/out lets the caller
    /// chain multiple compressions without re-parsing.
    function _compressExpressions(
        bytes memory vkBlob,
        uint256 offset,
        uint32 numExprs,
        GateEnv memory env,
        uint256 theta
    ) internal view returns (uint256 acc, uint256 newOffset) {
        uint256 cursor = offset;
        acc = 0;
        for (uint256 j = 0; j < numExprs; j++) {
            uint32 len = _readU32FromBlob(vkBlob, cursor);
            cursor += 4;
            (uint256 v, uint256 consumed) = _evalBytecode(vkBlob, cursor, env);
            require(consumed == cursor + len, "lookup expr length mismatch");
            acc = addmod(mulmod(acc, theta, FR_MODULUS), v, FR_MODULUS);
            cursor = consumed;
        }
        newOffset = cursor;
    }

    /// Core evaluator. Reads the lookup-bytecode section of the VK
    /// starting at `sectionOffset` (pointing at `u32 num_lookups`),
    /// consumes all lookups found there, and returns the concatenated
    /// expression values in emission order.
    /// State packet threaded through the chunk-walking helper so the
    /// top-level `_lookupExpressions` stays within Yul's stack-depth
    /// limits. The (cursor, outIdx, helperIdx, sumHelpers) fields are
    /// updated per-chunk; `out` is shared.
    struct LookupWalk {
        bytes vkBlob;
        uint256 cursor;
        uint256 outIdx;
        uint256 helperIdx;
        uint256 sumHelpers;
        uint256[] out;
    }

    function _lookupChunk(
        LookupWalk memory w,
        GateEnv memory env,
        LookupEnv memory lenv
    ) internal view {
        uint32 nParallel = _readU32FromBlob(w.vkBlob, w.cursor);
        w.cursor += 4;
        uint256[] memory compressedWithBeta = new uint256[](nParallel);
        for (uint256 p = 0; p < nParallel; p++) {
            uint32 nCols = _readU32FromBlob(w.vkBlob, w.cursor);
            w.cursor += 4;
            (uint256 comp, uint256 afterComp) =
                _compressExpressions(w.vkBlob, w.cursor, nCols, env, lenv.theta);
            w.cursor = afterComp;
            compressedWithBeta[p] = _frAdd(comp, lenv.beta);
        }
        uint256 product = 1;
        for (uint256 p = 0; p < nParallel; p++) {
            product = _frMul(product, compressedWithBeta[p]);
        }
        uint256 sum = 0;
        for (uint256 p = 0; p < nParallel; p++) {
            uint256 inv = _frInv(compressedWithBeta[p]);
            sum = _frAdd(sum, _frMul(product, inv));
        }
        uint256 helperEval = lenv.helperEvals[w.helperIdx++];
        w.sumHelpers = _frAdd(w.sumHelpers, helperEval);
        w.out[w.outIdx++] = _frSub(_frMul(helperEval, product), sum);
    }

    /// Skip through one lookup's bytecode + return the total output
    /// length (2 + num_chunks). Split off so the sizing pass doesn't
    /// share locals with the evaluation loop.
    function _sizeLookup(bytes memory vkBlob, uint256 offsetIn)
        internal pure returns (uint256 offsetOut, uint256 outAdd)
    {
        uint256 probe = offsetIn;
        uint32 selLen = _readU32FromBlob(vkBlob, probe); probe += 4 + selLen;
        uint32 nTable = _readU32FromBlob(vkBlob, probe); probe += 4;
        for (uint256 i = 0; i < nTable; i++) {
            uint32 l = _readU32FromBlob(vkBlob, probe); probe += 4 + l;
        }
        uint32 nChunks = _readU32FromBlob(vkBlob, probe); probe += 4;
        outAdd = 2 + nChunks;
        for (uint256 c = 0; c < nChunks; c++) {
            uint32 nParallel = _readU32FromBlob(vkBlob, probe); probe += 4;
            for (uint256 p = 0; p < nParallel; p++) {
                uint32 nCols = _readU32FromBlob(vkBlob, probe); probe += 4;
                for (uint256 k = 0; k < nCols; k++) {
                    uint32 l = _readU32FromBlob(vkBlob, probe); probe += 4 + l;
                }
            }
        }
        offsetOut = probe;
    }

    function _lookupExpressions(
        bytes memory vkBlob,
        uint256 sectionOffset,
        LookupEnv memory lenv
    ) internal view returns (uint256[] memory out, uint256 newOffset) {
        uint32 numLookups = _readU32FromBlob(vkBlob, sectionOffset);
        uint256 cursor = sectionOffset + 4;

        // Size pass.
        uint256 outLen = 0;
        {
            uint256 probe = cursor;
            for (uint256 lk = 0; lk < numLookups; lk++) {
                (uint256 nxt, uint256 add) = _sizeLookup(vkBlob, probe);
                probe = nxt; outLen += add;
            }
            newOffset = probe;
        }
        out = new uint256[](outLen);

        // Build GateEnv once.
        GateEnv memory env = GateEnv({
            x: 0, beta: lenv.beta, gamma: 0, theta: lenv.theta, trashChal: 0,
            l0: lenv.l0, lLast: lenv.lLast, lBlind: lenv.lBlind,
            fixedEvals: lenv.fixedEvals, adviceEvals: lenv.adviceEvals,
            instanceEvals: lenv.instanceEvals, challenges: lenv.challenges
        });

        LookupWalk memory w = LookupWalk({
            vkBlob: vkBlob,
            cursor: cursor,
            outIdx: 0,
            helperIdx: 0,
            sumHelpers: 0,
            out: out
        });
        uint256 activeRows = _frSub(_frSub(1, lenv.lLast), lenv.lBlind);

        for (uint256 lk = 0; lk < numLookups; lk++) {
            uint32 selLen = _readU32FromBlob(w.vkBlob, w.cursor);
            w.cursor += 4;
            (uint256 selectorVal, uint256 selEnd) = _evalBytecode(w.vkBlob, w.cursor, env);
            require(selEnd == w.cursor + selLen, "selector length mismatch");
            w.cursor = selEnd;

            uint32 nTable = _readU32FromBlob(w.vkBlob, w.cursor); w.cursor += 4;
            (uint256 compressedTable, uint256 afterTable) =
                _compressExpressions(w.vkBlob, w.cursor, nTable, env, lenv.theta);
            w.cursor = afterTable;

            w.out[w.outIdx++] = _frMul(_frAdd(lenv.l0, lenv.lLast), lenv.accumulatorEval);

            w.sumHelpers = 0;
            uint32 nChunks = _readU32FromBlob(w.vkBlob, w.cursor); w.cursor += 4;
            for (uint256 c = 0; c < nChunks; c++) {
                _lookupChunk(w, env, lenv);
            }

            uint256 selSum = _frMul(selectorVal, w.sumHelpers);
            uint256 diff = _frSub(_frSub(lenv.accumulatorNextEval, lenv.accumulatorEval), selSum);
            uint256 tPlusBeta = _frAdd(compressedTable, lenv.beta);
            uint256 acc = _frAdd(_frMul(diff, tPlusBeta), lenv.multiplicitiesEval);
            w.out[w.outIdx++] = _frMul(acc, activeRows);
        }
    }

    function _readU32FromBlob(bytes memory b, uint256 off) internal pure returns (uint32 v_) {
        v_ = (uint32(uint8(b[off])) << 24)
           | (uint32(uint8(b[off + 1])) << 16)
           | (uint32(uint8(b[off + 2])) << 8)
           |  uint32(uint8(b[off + 3]));
    }

    /// Public wrapper exposing `_lookupExpressions` for fixture testing.
    /// `lookupSectionOffset` points to the `u32 num_lookups` header of
    /// the lookup-bytecode section inside the VK blob.
    function lookupExpressions(
        address vkAddr,
        uint256 lookupSectionOffset,
        uint256[8] calldata scalars,  // theta β l0 lLast lBlind accEval accNextEval mEval
        uint256[] calldata helperEvals,
        uint256[] calldata adviceEvals,
        uint256[] calldata fixedEvals,
        uint256[] calldata instanceEvals,
        uint256[] calldata challenges
    ) external view returns (uint256[] memory) {
        bytes memory blob = vkAddr.code;
        LookupEnv memory lenv = LookupEnv({
            theta: scalars[0],
            beta: scalars[1],
            l0: scalars[2],
            lLast: scalars[3],
            lBlind: scalars[4],
            accumulatorEval: scalars[5],
            accumulatorNextEval: scalars[6],
            multiplicitiesEval: scalars[7],
            helperEvals: _copyToMemArr(helperEvals),
            adviceEvals: _copyToMemArr(adviceEvals),
            fixedEvals: _copyToMemArr(fixedEvals),
            instanceEvals: _copyToMemArr(instanceEvals),
            challenges: _copyToMemArr(challenges)
        });
        (uint256[] memory out, ) = _lookupExpressions(blob, lookupSectionOffset, lenv);
        return out;
    }

    /* ------------------------------------------------------------------ *
     *  Trashcan-argument expressions (Phase A2b)                         *
     *                                                                    *
     *  Port of `midnight_proofs::plonk::trash::Evaluated::expressions`   *
     *  from proofs/src/plonk/trash.rs:57+. One expression per trashcan:  *
     *    compressed_constraints − (1 − q) · trash_eval                   *
     *  where `compressed_constraints` = τ-fold of                        *
     *  `constraint_expressions` (like θ-fold in logup) and `q` is the   *
     *  selector evaluation at x.                                         *
     * ------------------------------------------------------------------ */

    struct TrashEnv {
        uint256 trashChallenge;
        uint256[] trashEvals;
        // Shared with bytecode evaluation:
        uint256[] adviceEvals;
        uint256[] fixedEvals;
        uint256[] instanceEvals;
        uint256[] challenges;
    }

    /// Skip through one trashcan's bytecode and return the new offset.
    function _sizeTrashcan(bytes memory vkBlob, uint256 offsetIn)
        internal pure returns (uint256 offsetOut)
    {
        uint256 probe = offsetIn;
        uint32 selLen = _readU32FromBlob(vkBlob, probe); probe += 4 + selLen;
        uint32 nC = _readU32FromBlob(vkBlob, probe); probe += 4;
        for (uint256 i = 0; i < nC; i++) {
            uint32 l = _readU32FromBlob(vkBlob, probe); probe += 4 + l;
        }
        offsetOut = probe;
    }

    function _trashExpressions(
        bytes memory vkBlob,
        uint256 sectionOffset,
        TrashEnv memory tenv
    ) internal view returns (uint256[] memory out, uint256 newOffset) {
        uint32 numTrash = _readU32FromBlob(vkBlob, sectionOffset);
        require(numTrash == tenv.trashEvals.length, "trash_evals length");
        uint256 cursor = sectionOffset + 4;

        out = new uint256[](numTrash);

        GateEnv memory env = GateEnv({
            x: 0, beta: 0, gamma: 0, theta: 0,
            trashChal: tenv.trashChallenge,
            l0: 0, lLast: 0, lBlind: 0,
            fixedEvals: tenv.fixedEvals, adviceEvals: tenv.adviceEvals,
            instanceEvals: tenv.instanceEvals, challenges: tenv.challenges
        });

        for (uint256 t = 0; t < numTrash; t++) {
            uint32 selLen = _readU32FromBlob(vkBlob, cursor);
            cursor += 4;
            (uint256 q, uint256 selEnd) = _evalBytecode(vkBlob, cursor, env);
            require(selEnd == cursor + selLen, "trash selector length mismatch");
            cursor = selEnd;

            uint32 nC = _readU32FromBlob(vkBlob, cursor); cursor += 4;
            // τ-fold: acc = acc·τ + eval
            uint256 compressed = 0;
            for (uint256 i = 0; i < nC; i++) {
                uint32 l = _readU32FromBlob(vkBlob, cursor); cursor += 4;
                (uint256 v, uint256 consumed) = _evalBytecode(vkBlob, cursor, env);
                require(consumed == cursor + l, "trash constraint length mismatch");
                cursor = consumed;
                compressed = addmod(
                    mulmod(compressed, tenv.trashChallenge, FR_MODULUS),
                    v, FR_MODULUS
                );
            }
            // expr = compressed − (1 − q) · trash_eval
            uint256 oneMinusQ = _frSub(1, q);
            uint256 sub = _frMul(oneMinusQ, tenv.trashEvals[t]);
            out[t] = _frSub(compressed, sub);
        }
        newOffset = cursor;
    }

    /// Public wrapper for fixture testing.
    function trashExpressions(
        address vkAddr,
        uint256 trashSectionOffset,
        uint256 trashChallenge,
        uint256[] calldata trashEvals,
        uint256[] calldata adviceEvals,
        uint256[] calldata fixedEvals,
        uint256[] calldata instanceEvals,
        uint256[] calldata challenges
    ) external view returns (uint256[] memory) {
        bytes memory blob = vkAddr.code;
        TrashEnv memory tenv = TrashEnv({
            trashChallenge: trashChallenge,
            trashEvals: _copyToMemArr(trashEvals),
            adviceEvals: _copyToMemArr(adviceEvals),
            fixedEvals: _copyToMemArr(fixedEvals),
            instanceEvals: _copyToMemArr(instanceEvals),
            challenges: _copyToMemArr(challenges)
        });
        (uint256[] memory out, ) = _trashExpressions(blob, trashSectionOffset, tenv);
        return out;
    }

    /* ------------------------------------------------------------------ *
     *  _partiallyEvaluateIdentities driver (Phase A3)                   *
     *                                                                    *
     *  Port of \`midnight_proofs::plonk::partially_evaluate_identities\`  *
     *  (proofs/src/plonk/mod.rs:486+). Concatenates the four algebraic  *
     *  component outputs in the exact Rust iterator order:               *
     *    1. Gate polynomials (one scalar per gate poly, each paired     *
     *       with an Option<usize> selector-column index).                *
     *    2. Permutation expressions (all paired with None).             *
     *    3. Lookup expressions (all paired with None).                  *
     *    4. Trashcan expressions (all paired with None).                *
     *                                                                    *
     *  None is encoded in the output `selectors` array as 0xFFFFFFFF.   *
     *  The output is the `Vec<(Option<usize>, Fr)>` that Phase B's       *
     *  linearization MSM will consume.                                   *
     * ------------------------------------------------------------------ */

    struct PartialEvalEnv {
        uint256 x;
        uint256 beta;
        uint256 gamma;
        uint256 theta;
        uint256 trashChallenge;
        uint256 l0;
        uint256 lLast;
        uint256 lBlind;
        uint256[] adviceEvals;
        uint256[] fixedEvals;
        uint256[] instanceEvals;
        uint256[] challenges;
        // Permutation bits.
        uint256[] permSetsFlat;  // {prod, next, last, hasLast}×n
        uint256[] permEvals;
        // Lookup bits (flattened: for each lookup, accEval/accNextEval/mEval,
        // then helperEvals concatenated).
        uint256 accumulatorEval;
        uint256 accumulatorNextEval;
        uint256 multiplicitiesEval;
        uint256[] helperEvals;
        // Trashcan bits.
        uint256[] trashEvals;
    }

    struct SectionOffsets {
        uint256 gate;       // points at `u32 num_simple_selectors`
        uint256 perm;       // points at `u32 permutation_chunk_len`
        uint256 lookup;     // points at `u32 num_lookups`
        uint256 trash;      // points at `u32 num_trashcans`
    }

    /// Locate the four bytecode sections inside the VK blob. The
    /// pre-bytecode header is fixed-size:
    ///   32 (transcript_repr) + 32 (omega) + 32+32+32 (constants 1/2/3)
    /// = 160 bytes, followed by `num_fixed * 128` + `num_perm_cols * 128`
    /// + 256 (s_g2) + 256 (neg_g2). After that the gate section starts.
    /// From there we walk forward to find perm / lookup / trash
    /// boundaries (each section has a self-describing length).
    function _loadSectionOffsets(bytes memory blob) internal pure returns (SectionOffsets memory so) {
        uint256 numFixed = _readU32FromBlob(blob, 64 + 16);         // c1[16..20] per codegen
        uint256 numPermCols = _readU32FromBlob(blob, 128 + 0);      // c3[0..4]
        so.gate = 160 + numFixed * 128 + numPermCols * 128 + 512;

        // Walk the gate section to find the perm offset.
        uint256 p = so.gate;
        uint32 nSimple = _readU32FromBlob(blob, p); p += 4 + 4 * nSimple;
        uint32 nPolys = _readU32FromBlob(blob, p); p += 4 + 4 * nPolys;
        uint32 gateBcLen = _readU32FromBlob(blob, p); p += 4 + gateBcLen;
        so.perm = p;

        // Walk perm: u32 chunkLen + u32 nCols + 3*nCols bytes.
        p += 4;
        uint32 nPerm = _readU32FromBlob(blob, p); p += 4 + 3 * nPerm;
        so.lookup = p;

        // Walk lookup via the same logic used by test: for each lookup,
        // selector + table + chunks.
        uint32 nLookups = _readU32FromBlob(blob, p); p += 4;
        for (uint256 lk = 0; lk < nLookups; lk++) {
            uint32 selLen = _readU32FromBlob(blob, p); p += 4 + selLen;
            uint32 nTable = _readU32FromBlob(blob, p); p += 4;
            for (uint256 i = 0; i < nTable; i++) {
                uint32 l = _readU32FromBlob(blob, p); p += 4 + l;
            }
            uint32 nChunks = _readU32FromBlob(blob, p); p += 4;
            for (uint256 c = 0; c < nChunks; c++) {
                uint32 nPar = _readU32FromBlob(blob, p); p += 4;
                for (uint256 pp = 0; pp < nPar; pp++) {
                    uint32 nCols = _readU32FromBlob(blob, p); p += 4;
                    for (uint256 k = 0; k < nCols; k++) {
                        uint32 l = _readU32FromBlob(blob, p); p += 4 + l;
                    }
                }
            }
        }
        so.trash = p;
    }

    /// Evaluate the gate-polynomial section and pair each scalar with
    /// its selector column (0xFFFFFFFF = None). Returns the flat
    /// (selectors[], scalars[]) pair in Rust iterator order.
    function _gateExpressions(
        bytes memory blob,
        uint256 gateOff,
        GateEnv memory env
    ) internal view returns (uint32[] memory selectors, uint256[] memory scalars) {
        uint256 p = gateOff;
        uint32 nSimple = _readU32FromBlob(blob, p); p += 4 + 4 * nSimple;
        uint32 nPolys = _readU32FromBlob(blob, p); p += 4;
        uint256 selArrStart = p;
        p += 4 * nPolys;
        uint32 bcLen = _readU32FromBlob(blob, p); p += 4;
        uint256 bcStart = p;

        selectors = new uint32[](nPolys);
        scalars = new uint256[](nPolys);
        uint256 cursor = bcStart;
        for (uint256 i = 0; i < nPolys; i++) {
            selectors[i] = _readU32FromBlob(blob, selArrStart + 4 * i);
            (uint256 v, uint256 next) = _evalBytecode(blob, cursor, env);
            scalars[i] = v;
            cursor = next;
        }
        require(cursor == bcStart + bcLen, "gate bytecode under/over-consumed");
    }

    /// Unpack the caller's flat perm-sets array into a PermEnv.
    function _buildPermEnv(PartialEvalEnv memory e, uint8[] memory colKinds,
        uint16[] memory colQueryIdxs, uint256 chunkLen) internal pure returns (PermEnv memory pe)
    {
        uint256 nSets = e.permSetsFlat.length / 4;
        PermSet[] memory sets = new PermSet[](nSets);
        for (uint256 i = 0; i < nSets; i++) {
            sets[i] = PermSet({
                prod: e.permSetsFlat[4 * i],
                next: e.permSetsFlat[4 * i + 1],
                last: e.permSetsFlat[4 * i + 2],
                hasLast: e.permSetsFlat[4 * i + 3] != 0
            });
        }
        pe = PermEnv({
            beta: e.beta, gamma: e.gamma, x: e.x,
            l0: e.l0, lLast: e.lLast, lBlind: e.lBlind,
            sets: sets, permEvals: e.permEvals,
            adviceEvals: e.adviceEvals, fixedEvals: e.fixedEvals, instanceEvals: e.instanceEvals,
            colKinds: colKinds, colQueryIdxs: colQueryIdxs, chunkLen: chunkLen
        });
    }

    /// Core driver. Concatenates gate+perm+lookup+trash outputs in the
    /// canonical Rust iterator order.
    function _partiallyEvaluateIdentities(bytes memory blob, PartialEvalEnv memory e)
        internal view returns (uint32[] memory selectors, uint256[] memory scalars)
    {
        SectionOffsets memory so = _loadSectionOffsets(blob);

        // 1. Gate polynomials.
        GateEnv memory gateEnv = GateEnv({
            x: e.x, beta: e.beta, gamma: e.gamma, theta: e.theta,
            trashChal: e.trashChallenge,
            l0: e.l0, lLast: e.lLast, lBlind: e.lBlind,
            fixedEvals: e.fixedEvals, adviceEvals: e.adviceEvals,
            instanceEvals: e.instanceEvals, challenges: e.challenges
        });
        (uint32[] memory gateSel, uint256[] memory gateVals) =
            _gateExpressions(blob, so.gate, gateEnv);

        // 2. Permutation.
        (uint8[] memory colKinds, uint16[] memory colQueryIdxs, uint256 chunkLen) =
            _loadPermColumnMetadataFromBlob(blob, so.perm);
        PermEnv memory pe = _buildPermEnv(e, colKinds, colQueryIdxs, chunkLen);
        uint256[] memory permVals = _permExpressions(pe);

        // 3. Lookup.
        LookupEnv memory lenv = LookupEnv({
            theta: e.theta, beta: e.beta, l0: e.l0, lLast: e.lLast, lBlind: e.lBlind,
            accumulatorEval: e.accumulatorEval,
            accumulatorNextEval: e.accumulatorNextEval,
            multiplicitiesEval: e.multiplicitiesEval,
            helperEvals: e.helperEvals,
            adviceEvals: e.adviceEvals, fixedEvals: e.fixedEvals,
            instanceEvals: e.instanceEvals, challenges: e.challenges
        });
        (uint256[] memory lkVals, ) = _lookupExpressions(blob, so.lookup, lenv);

        // 4. Trashcan.
        TrashEnv memory tenv = TrashEnv({
            trashChallenge: e.trashChallenge,
            trashEvals: e.trashEvals,
            adviceEvals: e.adviceEvals, fixedEvals: e.fixedEvals,
            instanceEvals: e.instanceEvals, challenges: e.challenges
        });
        (uint256[] memory trVals, ) = _trashExpressions(blob, so.trash, tenv);

        // Concatenate.
        uint256 total = gateVals.length + permVals.length + lkVals.length + trVals.length;
        selectors = new uint32[](total);
        scalars = new uint256[](total);
        uint256 k = 0;
        for (uint256 i = 0; i < gateVals.length; i++) {
            selectors[k] = gateSel[i]; scalars[k] = gateVals[i]; k++;
        }
        for (uint256 i = 0; i < permVals.length; i++) {
            selectors[k] = 0xFFFFFFFF; scalars[k] = permVals[i]; k++;
        }
        for (uint256 i = 0; i < lkVals.length; i++) {
            selectors[k] = 0xFFFFFFFF; scalars[k] = lkVals[i]; k++;
        }
        for (uint256 i = 0; i < trVals.length; i++) {
            selectors[k] = 0xFFFFFFFF; scalars[k] = trVals[i]; k++;
        }
    }

    /// Permutation metadata reader keyed off of the known section
    /// offset (duplicates `_loadPermColumnMetadata` in the test but
    /// doesn't require the candidate-iteration scan).
    function _loadPermColumnMetadataFromBlob(bytes memory blob, uint256 permOff)
        internal pure returns (uint8[] memory colKinds, uint16[] memory colQueryIdxs, uint256 chunkLen)
    {
        chunkLen = _readU32FromBlob(blob, permOff);
        uint32 nCols = _readU32FromBlob(blob, permOff + 4);
        colKinds = new uint8[](nCols);
        colQueryIdxs = new uint16[](nCols);
        uint256 p = permOff + 8;
        for (uint256 i = 0; i < nCols; i++) {
            colKinds[i] = uint8(blob[p]);
            colQueryIdxs[i] = (uint16(uint8(blob[p + 1])) << 8) | uint16(uint8(blob[p + 2]));
            p += 3;
        }
    }

    /// Public view wrapper so the forge test can drive the full
    /// algebraic pipeline and compare against the Rust-computed
    /// (selector, scalar) array.
    function partiallyEvaluateIdentities(address vkAddr, PartialEvalEnv calldata ein)
        external view returns (uint32[] memory selectors, uint256[] memory scalars)
    {
        bytes memory blob = vkAddr.code;
        PartialEvalEnv memory e = PartialEvalEnv({
            x: ein.x, beta: ein.beta, gamma: ein.gamma, theta: ein.theta,
            trashChallenge: ein.trashChallenge,
            l0: ein.l0, lLast: ein.lLast, lBlind: ein.lBlind,
            adviceEvals: _copyToMemArr(ein.adviceEvals),
            fixedEvals: _copyToMemArr(ein.fixedEvals),
            instanceEvals: _copyToMemArr(ein.instanceEvals),
            challenges: _copyToMemArr(ein.challenges),
            permSetsFlat: _copyToMemArr(ein.permSetsFlat),
            permEvals: _copyToMemArr(ein.permEvals),
            accumulatorEval: ein.accumulatorEval,
            accumulatorNextEval: ein.accumulatorNextEval,
            multiplicitiesEval: ein.multiplicitiesEval,
            helperEvals: _copyToMemArr(ein.helperEvals),
            trashEvals: _copyToMemArr(ein.trashEvals)
        });
        return _partiallyEvaluateIdentities(blob, e);
    }

    /* ------------------------------------------------------------------ *
     *  Final pairing RHS (Phase C3)                                      *
     *                                                                    *
     *  Standalone helper that consumes the two G1 points produced by    *
     *  the DualMSM (Phase C2 output) — \`left\` and \`right\` — and runs  *
     *  the KZG batch-open pairing check:                                *
     *                                                                    *
     *    e(left, s·G2) · e(right, −G2) == 1                             *
     *                                                                    *
     *  Both points arrive compressed (48-byte BLS12-381 zcash format);  *
     *  we decompress via the existing Prague-ModExp-based pipeline,     *
     *  slice \`s·G2\` and \`−G2\` out of the VK blob at their                    *
     *  known offsets, and invoke the EIP-2537 pairing precompile       *
     *  (0x0f) via the existing \`_pairingCheck\` helper.                   *
     *                                                                    *
     *  This is exactly the pairing-side of the final check that the    *
     *  main \`verify\` entry point needs once Phase C2 step 2-4 lands   *
     *  the G1-point construction. Landing it in isolation against a    *
     *  Rust-computed \`(left, right)\` pair pins down the Solidity        *
     *  decompression + precompile plumbing before the harder DualMSM    *
     *  construction is in place.                                        *
     * ------------------------------------------------------------------ */

    function _pairingCheckFromPair(
        bytes memory vkBlob,
        Vk memory vk,
        bytes memory leftCompressed,
        bytes memory rightCompressed
    ) internal view returns (bool) {
        require(leftCompressed.length == 48, "left len");
        require(rightCompressed.length == 48, "right len");

        bytes memory sG2  = _vkSlice(vkBlob, vk.sG2Offset,  256);
        bytes memory ngG2 = _vkSlice(vkBlob, vk.negG2Offset, 256);

        bytes memory leftEip  = _g1CompressedToEip2537(leftCompressed);
        bytes memory rightEip = _g1CompressedToEip2537(rightCompressed);

        bytes memory pairs = abi.encodePacked(leftEip, sG2, rightEip, ngG2);
        return _pairingCheck(pairs);
    }

    /// Public fixture-only wrapper. Uses the default VK address
    /// wired into this contract (via the \`_vkBlob\` + \`_loadVk\`
    /// pair) so fixture tests don't need to pass a separate address.
    function pairingCheckFromPair(
        bytes calldata leftCompressed,
        bytes calldata rightCompressed
    ) external view returns (bool) {
        (Vk memory vk, bytes memory blob) = _loadVk();
        bytes memory l = leftCompressed;
        bytes memory r = rightCompressed;
        return _pairingCheckFromPair(blob, vk, l, r);
    }

    /* ------------------------------------------------------------------ *
     *  f_eval fold for multi_prepare (Phase C2 step 1)                   *
     *                                                                    *
     *  Port of the reverse-Horner Lagrange fold from                    *
     *  \`KZGCommitmentScheme::multi_prepare\` (kzg/mod.rs:330-340). Given *
     *  the x1-folded per-set (point_set, eval_set, proof_eval_at_x3)    *
     *  triples + the batching challenges x2, x3, produces the scalar    *
     *  \`f_eval\` that enters the x4-fold producing the final v scalar  *
     *  used in the pairing RHS.                                         *
     *                                                                    *
     *  Algorithm (verbatim):                                             *
     *    acc = 0                                                         *
     *    for (points, evals, proof_eval) in zip(..).rev():               *
     *        r_eval = eval(lagrange(points, evals), x3)                  *
     *        den    = ∏(x3 − point_j)                                    *
     *        acc    = acc · x2 + (proof_eval − r_eval) / den             *
     * ------------------------------------------------------------------ */

    function _computeFEvalFold(
        uint256[] memory pointSetLens,
        uint256[] memory pointSetsFlat,
        uint256[] memory evalSetsFlat,
        uint256[] memory qEvalsOnX3,
        uint256 x2,
        uint256 x3
    ) internal view returns (uint256 acc) {
        uint256 n = pointSetLens.length;
        require(qEvalsOnX3.length == n, "qEvalsOnX3 length");
        // Precompute set-start offsets so reverse iteration is cheap.
        uint256[] memory offs = new uint256[](n + 1);
        for (uint256 i = 0; i < n; i++) offs[i + 1] = offs[i] + pointSetLens[i];
        require(offs[n] == pointSetsFlat.length, "points flat length");
        require(offs[n] == evalSetsFlat.length, "evals flat length");

        acc = 0;
        for (uint256 k = n; k > 0; k--) {
            uint256 i = k - 1;
            uint256 len = pointSetLens[i];
            uint256 start = offs[i];
            // Carve out the per-set (points, evals) slices.
            uint256[] memory pts = new uint256[](len);
            uint256[] memory evs = new uint256[](len);
            for (uint256 j = 0; j < len; j++) {
                pts[j] = pointSetsFlat[start + j];
                evs[j] = evalSetsFlat[start + j];
            }
            uint256 rEval = _lagrangeInterpAtX3(pts, evs, x3);
            // den = ∏(x3 − point_j)
            uint256 den = 1;
            for (uint256 j = 0; j < len; j++) {
                den = _frMul(den, _frSub(x3, pts[j]));
            }
            uint256 numer = _frSub(qEvalsOnX3[i], rEval);
            uint256 eval_i = _frMul(numer, _frInv(den));
            acc = _frAdd(_frMul(acc, x2), eval_i);
        }
    }

    /// Public wrapper for fixture testing.
    function computeFEvalFold(
        uint256[] calldata pointSetLens,
        uint256[] calldata pointSetsFlat,
        uint256[] calldata evalSetsFlat,
        uint256[] calldata qEvalsOnX3,
        uint256 x2,
        uint256 x3
    ) external view returns (uint256) {
        return _computeFEvalFold(
            _copyToMemArr(pointSetLens),
            _copyToMemArr(pointSetsFlat),
            _copyToMemArr(evalSetsFlat),
            _copyToMemArr(qEvalsOnX3),
            x2, x3
        );
    }

    /* ------------------------------------------------------------------ *
     *  Query-rotation schedule (Phase C1)                                *
     *                                                                    *
     *  Reads the distinct-rotations + per-query-kind rotation-index     *
     *  table appended to the VK blob at codegen time, and materialises  *
     *  each distinct rotation's `ω^at · x` for a given challenge x.     *
     *  Phase C2's multi-prepare DualMSM groups VerifierQueries by this  *
     *  rotation index, so having the mapping in a shared pre-computed  *
     *  form avoids re-hashing the verifier's query structure on-chain.  *
     * ------------------------------------------------------------------ */

    struct QuerySchedule {
        int32[] rotations;              // distinct `at` values
        uint8[] adviceRotationIdx;      // per advice query
        uint8[] fixedRotationIdx;       // per non-simple-selector fixed query
        uint8[] instanceRotationIdx;    // per committed-instance query
        uint256 sectionOffset;          // start of section (u32 nRotations)
    }

    /// Locate the query-schedule section: it sits immediately after
    /// the trashcan bytecode at the tail of the VK blob.
    function _findQuerySection(bytes memory blob) internal view returns (uint256) {
        SectionOffsets memory so = _loadSectionOffsets(blob);
        // Walk the trashcan section to find its end.
        uint256 p = so.trash;
        uint32 nT = _readU32FromBlob(blob, p); p += 4;
        for (uint256 t = 0; t < nT; t++) {
            uint32 selLen = _readU32FromBlob(blob, p); p += 4 + selLen;
            uint32 nC = _readU32FromBlob(blob, p); p += 4;
            for (uint256 i = 0; i < nC; i++) {
                uint32 l = _readU32FromBlob(blob, p); p += 4 + l;
            }
        }
        return p;
    }

    function _loadQuerySchedule(bytes memory blob) internal view returns (QuerySchedule memory qs) {
        qs.sectionOffset = _findQuerySection(blob);
        uint256 p = qs.sectionOffset;

        uint32 nRot = _readU32FromBlob(blob, p); p += 4;
        qs.rotations = new int32[](nRot);
        for (uint256 i = 0; i < nRot; i++) {
            qs.rotations[i] = int32(uint32(_readU32FromBlob(blob, p)));
            p += 4;
        }
        uint32 nAdvice = _readU32FromBlob(blob, p); p += 4;
        qs.adviceRotationIdx = new uint8[](nAdvice);
        for (uint256 i = 0; i < nAdvice; i++) { qs.adviceRotationIdx[i] = uint8(blob[p + i]); }
        p += nAdvice;

        uint32 nFixed = _readU32FromBlob(blob, p); p += 4;
        qs.fixedRotationIdx = new uint8[](nFixed);
        for (uint256 i = 0; i < nFixed; i++) { qs.fixedRotationIdx[i] = uint8(blob[p + i]); }
        p += nFixed;

        uint32 nInst = _readU32FromBlob(blob, p); p += 4;
        qs.instanceRotationIdx = new uint8[](nInst);
        for (uint256 i = 0; i < nInst; i++) { qs.instanceRotationIdx[i] = uint8(blob[p + i]); }
    }

    /// Compute `ω^at · x` for every distinct rotation in the schedule.
    /// Returns a parallel array: rotatedPoints[i] = ω^rotations[i] · x.
    function _computeRotatedPoints(
        bytes memory blob,
        uint256 x
    ) internal view returns (int32[] memory rotations, uint256[] memory rotatedPoints) {
        QuerySchedule memory qs = _loadQuerySchedule(blob);
        uint256 omega = _readUint256(blob, 32);  // omega lives at VK blob offset 32
        uint256 n = _readN(blob);
        rotations = qs.rotations;
        rotatedPoints = new uint256[](rotations.length);
        for (uint256 i = 0; i < rotations.length; i++) {
            rotatedPoints[i] = _rotateOmega(x, int256(rotations[i]), omega, n);
        }
    }

    function _readUint256(bytes memory blob, uint256 off) internal pure returns (uint256 v) {
        assembly { v := mload(add(add(blob, 32), off)) }
    }

    function _readN(bytes memory blob) internal pure returns (uint256 n) {
        // constants 1 is at offset 64; first 8 bytes are `uint64 n` (BE).
        uint256 off = 64;
        uint256 word;
        assembly { word := mload(add(add(blob, 32), off)) }
        n = word >> 192;
    }

    /// Public wrapper for fixture testing.
    function computeRotatedPoints(address vkAddr, uint256 x)
        external view returns (int32[] memory rotations, uint256[] memory rotatedPoints)
    {
        bytes memory blob = vkAddr.code;
        return _computeRotatedPoints(blob, x);
    }

    function loadQuerySchedule(address vkAddr) external view returns (
        int32[] memory rotations,
        uint8[] memory adviceIdx,
        uint8[] memory fixedIdx,
        uint8[] memory instanceIdx
    ) {
        bytes memory blob = vkAddr.code;
        QuerySchedule memory qs = _loadQuerySchedule(blob);
        return (qs.rotations, qs.adviceRotationIdx, qs.fixedRotationIdx, qs.instanceRotationIdx);
    }

    /* ------------------------------------------------------------------ *
     *  compute_linearization_commitment (Phase B)                        *
     *                                                                    *
     *  Port of \`midnight_proofs::plonk::linearization::verifier::       *
     *  compute_linearization_commitment\` (linearization/verifier.rs:45+).*
     *  Groups the 22 (selector, scalar) pairs from Phase A3 by           *
     *  selector column, weights them with powers-of-y in reverse         *
     *  iteration order, and emits the MSM (points, scalars) +            *
     *  expected_eval that Phase C's multi-prepare DualMSM consumes.      *
     *                                                                    *
     *  Algorithm (verbatim):                                             *
     *    1. Push quotient-limb commitments with scalars                  *
     *         (1 − xn)·splitting_factor^i                                *
     *    2. Group expressions in reverse:                                *
     *         grouped[col] += y^i · eval_i                               *
     *    3. For each group in ordered iteration (None first, then        *
     *       ascending Some):                                             *
     *         None  → expected_eval −= scalar                           *
     *         Some  → push (fixed_commitments[col], scalar)              *
     * ------------------------------------------------------------------ */

    /// Compute `(1 − xn)·splitting_factor^i mod r` for the first i
    /// quotient limbs. Splits out so the driver stays within stack
    /// limits.
    function _quotientSplittingScalars(
        uint256 xn,
        uint256 splittingFactor,
        uint256 nLimbs
    ) internal pure returns (uint256[] memory out) {
        out = new uint256[](nLimbs);
        uint256 pow = _frSub(1, xn);
        for (uint256 i = 0; i < nLimbs; i++) {
            out[i] = pow;
            pow = mulmod(pow, splittingFactor, FR_MODULUS);
        }
    }

    /// Group (selector, scalar) pairs via powers-of-y in reverse.
    /// Returns `buckets[col]` where bucket index 0 is the None
    /// accumulator and bucket i+1 is the Some(i) accumulator;
    /// `nonEmptyMask[i]` is 1 iff `buckets[i]` received at least one
    /// contribution (used to skip zero buckets during emission).
    function _groupByPowersOfY(
        uint32[] memory selectors,
        uint256[] memory scalars,
        uint256 y,
        uint256 numFixedCols
    ) internal pure returns (uint256[] memory buckets, bool[] memory nonEmpty) {
        buckets = new uint256[](numFixedCols + 1);
        nonEmpty = new bool[](numFixedCols + 1);
        uint256 yPow = 1;
        // Reverse iteration: entry[len-1] gets y_pow=1, entry[0] gets y_pow=y^(len-1).
        for (uint256 k = selectors.length; k > 0; k--) {
            uint256 i = k - 1;
            uint256 idx;
            if (selectors[i] == 0xFFFFFFFF) idx = 0;
            else idx = uint256(selectors[i]) + 1;
            uint256 contrib = mulmod(yPow, scalars[i], FR_MODULUS);
            buckets[idx] = addmod(buckets[idx], contrib, FR_MODULUS);
            nonEmpty[idx] = true;
            yPow = mulmod(yPow, y, FR_MODULUS);
        }
    }

    /// Read a fixed commitment at slot `idx` from the VK blob. Each
    /// fixed commitment is 128 bytes (EIP-2537 uncompressed G1) and
    /// they start at offset 160 (just after the 5×32-byte header).
    /// Returns 4 uint256 words (x_hi, x_lo, y_hi, y_lo) in the same
    /// layout as other G1 points in the codebase.
    function _readFixedCommitment(bytes memory blob, uint256 idx)
        internal pure returns (uint256[4] memory out)
    {
        uint256 off = 160 + idx * 128;
        assembly {
            let base := add(add(blob, 32), off)
            mstore(out, mload(base))
            mstore(add(out, 32), mload(add(base, 32)))
            mstore(add(out, 64), mload(add(base, 64)))
            mstore(add(out, 96), mload(add(base, 96)))
        }
    }

    /// Core driver. Consumes the Phase A3 output + the transcript-
    /// read quotient-limb commitments and produces the
    /// linearization-commitment MSM + the constant term
    /// `expected_eval`.
    function _computeLinearizationCommitment(
        bytes memory blob,
        uint32[] memory selectors,
        uint256[] memory scalars,
        uint256 y,
        uint256 xn,
        uint256 splittingFactor,
        uint256[] memory quotientLimbCommsFlat  // numLimbs * 4 uint256s
    ) internal pure returns (
        uint256[] memory pointsFlat,
        uint256[] memory outScalars,
        uint256 expectedEval
    ) {
        require(quotientLimbCommsFlat.length % 4 == 0, "quot limbs not 4-flat");
        uint256 nLimbs = quotientLimbCommsFlat.length / 4;

        // Quotient-limb scalars.
        uint256[] memory splitScalars =
            _quotientSplittingScalars(xn, splittingFactor, nLimbs);

        // Bucket by selector (with reverse-iteration powers-of-y).
        uint256 numFixedCols = _readU32FromBlob(blob, 64 + 16); // c1[16..20]
        (uint256[] memory buckets, bool[] memory nonEmpty) =
            _groupByPowersOfY(selectors, scalars, y, numFixedCols);

        // Count non-empty Some buckets (index 0 is None; we skip it).
        uint256 nSome = 0;
        for (uint256 i = 1; i < buckets.length; i++) {
            if (nonEmpty[i]) nSome++;
        }

        pointsFlat = new uint256[]((nLimbs + nSome) * 4);
        outScalars = new uint256[](nLimbs + nSome);

        // Quotient limbs first.
        for (uint256 i = 0; i < nLimbs; i++) {
            pointsFlat[4 * i]     = quotientLimbCommsFlat[4 * i];
            pointsFlat[4 * i + 1] = quotientLimbCommsFlat[4 * i + 1];
            pointsFlat[4 * i + 2] = quotientLimbCommsFlat[4 * i + 2];
            pointsFlat[4 * i + 3] = quotientLimbCommsFlat[4 * i + 3];
            outScalars[i] = splitScalars[i];
        }

        // None bucket folds into expected_eval (negated).
        expectedEval = nonEmpty[0] ? _frSub(0, buckets[0]) : 0;

        // Some buckets in ascending column index.
        uint256 k = nLimbs;
        for (uint256 i = 1; i < buckets.length; i++) {
            if (!nonEmpty[i]) continue;
            uint256 col = i - 1;
            uint256[4] memory p = _readFixedCommitment(blob, col);
            pointsFlat[4 * k]     = p[0];
            pointsFlat[4 * k + 1] = p[1];
            pointsFlat[4 * k + 2] = p[2];
            pointsFlat[4 * k + 3] = p[3];
            outScalars[k] = buckets[i];
            k++;
        }
    }

    /// Public wrapper for fixture testing.
    function computeLinearizationCommitment(
        address vkAddr,
        uint32[] calldata selectors,
        uint256[] calldata scalars,
        uint256 y,
        uint256 xn,
        uint256 splittingFactor,
        uint256[] calldata quotientLimbCommsFlat
    ) external view returns (
        uint256[] memory pointsFlat,
        uint256[] memory outScalars,
        uint256 expectedEval
    ) {
        bytes memory blob = vkAddr.code;
        uint32[] memory selMem = new uint32[](selectors.length);
        for (uint256 i = 0; i < selectors.length; i++) selMem[i] = selectors[i];
        return _computeLinearizationCommitment(
            blob, selMem,
            _copyToMemArr(scalars),
            y, xn, splittingFactor,
            _copyToMemArr(quotientLimbCommsFlat)
        );
    }

    /* ------------------------------------------------------------------ *
     *  RPN bytecode interpreter for partially_evaluate_identities        *
     *                                                                    *
     *  Each gate polynomial is serialised on the Rust side into compact  *
     *  reverse-polish bytecode (see `src/expr_bytecode.rs`). This        *
     *  interpreter walks the bytecode with a 32-slot uint256[] stack,    *
     *  looking up query values and special variables in the supplied    *
     *  `GateEnv` struct. It is semantically identical to                 *
     *  `Expression::evaluate` on the Rust side.                          *
     * ------------------------------------------------------------------ */

    struct GateEnv {
        uint256 x;
        uint256 beta;
        uint256 gamma;
        uint256 theta;
        uint256 trashChal;
        uint256 l0;
        uint256 lLast;
        uint256 lBlind;
        uint256[] fixedEvals;
        uint256[] adviceEvals;
        uint256[] instanceEvals;
        uint256[] challenges;
    }

    uint8 internal constant OP_CONST = 0x00;
    uint8 internal constant OP_FIXED = 0x01;
    uint8 internal constant OP_ADVICE = 0x02;
    uint8 internal constant OP_INSTANCE = 0x03;
    uint8 internal constant OP_CHALLENGE = 0x04;
    uint8 internal constant OP_L_0 = 0x05;
    uint8 internal constant OP_L_LAST = 0x06;
    uint8 internal constant OP_L_BLIND = 0x07;
    uint8 internal constant OP_BETA = 0x08;
    uint8 internal constant OP_GAMMA = 0x09;
    uint8 internal constant OP_THETA = 0x0A;
    uint8 internal constant OP_TRASH = 0x0B;
    uint8 internal constant OP_X = 0x0C;
    uint8 internal constant OP_NEG = 0x20;
    uint8 internal constant OP_ADD = 0x21;
    uint8 internal constant OP_MUL = 0x22;
    uint8 internal constant OP_SCALED = 0x23;
    uint8 internal constant OP_END = 0xFF;

    /// Evaluate a single RPN program (one expression terminated by OP_END)
    /// starting at `bytecode[offset]`. Returns `(value, newOffset)`.
    function _evalBytecode(bytes memory bytecode, uint256 offset, GateEnv memory env)
        internal pure returns (uint256 value, uint256 newOffset)
    {
        uint256[] memory stack = new uint256[](64);
        uint256 sp = 0;
        uint256 i = offset;
        while (i < bytecode.length) {
            uint8 op = uint8(bytecode[i]);
            unchecked { i++; }
            if (op == OP_CONST) {
                uint256 v;
                assembly { v := mload(add(add(bytecode, 32), i)) }
                i += 32;
                stack[sp++] = v % FR_MODULUS;
            } else if (op == OP_FIXED) {
                uint16 idx = (uint16(uint8(bytecode[i])) << 8) | uint16(uint8(bytecode[i+1]));
                i += 2;
                stack[sp++] = env.fixedEvals[idx];
            } else if (op == OP_ADVICE) {
                uint16 idx = (uint16(uint8(bytecode[i])) << 8) | uint16(uint8(bytecode[i+1]));
                i += 2;
                stack[sp++] = env.adviceEvals[idx];
            } else if (op == OP_INSTANCE) {
                uint16 idx = (uint16(uint8(bytecode[i])) << 8) | uint16(uint8(bytecode[i+1]));
                i += 2;
                stack[sp++] = env.instanceEvals[idx];
            } else if (op == OP_CHALLENGE) {
                uint16 idx = (uint16(uint8(bytecode[i])) << 8) | uint16(uint8(bytecode[i+1]));
                i += 2;
                stack[sp++] = env.challenges[idx];
            } else if (op == OP_L_0) {
                stack[sp++] = env.l0;
            } else if (op == OP_L_LAST) {
                stack[sp++] = env.lLast;
            } else if (op == OP_L_BLIND) {
                stack[sp++] = env.lBlind;
            } else if (op == OP_BETA) {
                stack[sp++] = env.beta;
            } else if (op == OP_GAMMA) {
                stack[sp++] = env.gamma;
            } else if (op == OP_THETA) {
                stack[sp++] = env.theta;
            } else if (op == OP_TRASH) {
                stack[sp++] = env.trashChal;
            } else if (op == OP_X) {
                stack[sp++] = env.x;
            } else if (op == OP_NEG) {
                uint256 a = stack[--sp];
                stack[sp++] = a == 0 ? 0 : FR_MODULUS - a;
            } else if (op == OP_ADD) {
                uint256 b = stack[--sp];
                uint256 a = stack[--sp];
                stack[sp++] = addmod(a, b, FR_MODULUS);
            } else if (op == OP_MUL) {
                uint256 b = stack[--sp];
                uint256 a = stack[--sp];
                stack[sp++] = mulmod(a, b, FR_MODULUS);
            } else if (op == OP_SCALED) {
                uint256 k;
                assembly { k := mload(add(add(bytecode, 32), i)) }
                i += 32;
                uint256 a = stack[--sp];
                stack[sp++] = mulmod(a, k % FR_MODULUS, FR_MODULUS);
            } else if (op == OP_END) {
                require(sp == 1, "bytecode stack not singleton at END");
                return (stack[0], i);
            } else {
                revert("unknown opcode");
            }
        }
        revert("bytecode ran off end without END");
    }

    /// Public view wrapper so the forge test can drive the interpreter
    /// without deploying a separate harness contract.
    function evalGateBytecode(
        bytes calldata bytecode,
        uint256[] calldata envScalars,
        uint256[] calldata fixedEvals,
        uint256[] calldata adviceEvals,
        uint256[] calldata instanceEvals,
        uint256[] calldata challenges
    ) external pure returns (uint256) {
        require(envScalars.length == 8, "env scalars must be 8");
        GateEnv memory env = GateEnv({
            x: envScalars[0],
            beta: envScalars[1],
            gamma: envScalars[2],
            theta: envScalars[3],
            trashChal: envScalars[4],
            l0: envScalars[5],
            lLast: envScalars[6],
            lBlind: envScalars[7],
            fixedEvals: _copyToMemArr(fixedEvals),
            adviceEvals: _copyToMemArr(adviceEvals),
            instanceEvals: _copyToMemArr(instanceEvals),
            challenges: _copyToMemArr(challenges)
        });
        bytes memory bc = bytecode;
        (uint256 v, uint256 consumed) = _evalBytecode(bc, 0, env);
        require(consumed == bc.length, "bytecode not fully consumed");
        return v;
    }

    function _copyToMemArr(uint256[] calldata a) private pure returns (uint256[] memory b) {
        b = new uint256[](a.length);
        for (uint256 i = 0; i < a.length; i++) b[i] = a[i];
    }

    /// Public view wrappers around the Fr primitives so that forge unit
    /// tests can assert them against Rust-computed fixtures before relying
    /// on them inside the verifier body.
    function frPow(uint256 base, uint256 exp) external view returns (uint256) {
        return _frPow(base, exp);
    }

    function frInv(uint256 a) external view returns (uint256) { return _frInv(a); }

    function rotateOmega(uint256 x, int256 rotation, uint256 omega, uint256 n)
        external view returns (uint256)
    { return _rotateOmega(x, rotation, omega, n); }

    function lagrangeIRange(
        uint256 x, uint256 xn, int256 startIncl, int256 endIncl,
        uint256 omega, uint256 n
    ) external view returns (uint256[] memory) {
        return _lagrangeIRange(x, xn, startIncl, endIncl, omega, n);
    }

    function frDeltaPow(uint256 n) external pure returns (uint256) {
        return _frDeltaPow(n);
    }

    function lagrangeInterpAtX3(
        uint256[] calldata points, uint256[] calldata evals, uint256 x3
    ) external view returns (uint256) {
        uint256[] memory p = new uint256[](points.length);
        uint256[] memory e = new uint256[](evals.length);
        for (uint256 i = 0; i < points.length; i++) p[i] = points[i];
        for (uint256 i = 0; i < evals.length; i++) e[i] = evals[i];
        return _lagrangeInterpAtX3(p, e, x3);
    }

    /* ------------------------------------------------------------------ *
     *  Proof stream reader                                               *
     *                                                                    *
     *  The proof is a bytestream that encodes (in order):                *
     *    - for each phase:                                               *
     *        - advice commitments (compressed G1, 48 bytes each)         *
     *    - read multiplicity commitments (per lookup)                    *
     *    - permutation product commitments                               *
     *    - lookup commitments                                            *
     *    - trashcan commitments                                          *
     *    - quotient limb commitments                                     *
     *    - instance evals (for committed instances), advice evals        *
     *    - fixed evals (minus simple selectors)                          *
     *    - permutation common evals                                      *
     *    - permutation product evals (cur, next, last)                   *
     *    - lookup evals                                                  *
     *    - trashcan evals                                                *
     *    - f_com (G1)                                                    *
     *    - q_evals_on_x3                                                 *
     *    - pi (G1)                                                       *
     * ------------------------------------------------------------------ */

    struct Reader {
        bytes data;
        uint256 pos;
    }

    function _readScalarLE32(Reader memory r) internal pure returns (bytes32 le) {
        uint256 p = r.pos;
        require(p + 32 <= r.data.length, "short read scalar");
        assembly { le := mload(add(add(mload(r), 32), p)) }
        r.pos = p + 32;
    }

    function _readPointCompressed48(Reader memory r)
        internal pure returns (bytes memory out)
    {
        uint256 p = r.pos;
        require(p + 48 <= r.data.length, "short read G1");
        out = new bytes(48);
        assembly {
            let src := add(add(mload(r), 32), p)
            let dst := add(out, 32)
            mstore(dst, mload(src))            // 32 bytes
            mstore(add(dst, 32), mload(add(src, 32)))  // 16 bytes (last 16 unused of word)
        }
        r.pos = p + 48;
    }

    /* ------------------------------------------------------------------ *
     *  VK blob reader                                                    *
     *                                                                    *
     *  The VK contract, when called, returns a bytes blob laid out as    *
     *  described in codegen.rs (transcript_repr, omega, packed consts,   *
     *  fixed commitments, permutation commitments, s_g2, -g2).           *
     * ------------------------------------------------------------------ */

    struct Vk {
        bytes32 transcriptRepr;     // BE
        bytes32 omegaBE;            // BE
        uint64  n;
        uint32  k;
        uint32  numAdviceCols;
        uint32  numFixedCols;
        uint32  numInstanceCols;
        uint32  numChallenges;
        uint32  numPhases;
        uint32  csDegree;
        uint32  numSimpleSelectors;
        uint32  blindingFactors;
        uint32  numAdviceQueries;
        uint32  numFixedQueries;
        uint32  numInstanceQueries;
        uint32  numLookups;
        uint32  numTrashcans;
        uint32  numPermColumns;
        uint32  numPermChunks;
        uint32  numQuotientLimbs;
        uint32  totalLookupHelpers;
        uint32  numCommittedInstanceEvals;
        uint256 fixedCommsOffset;   // offset into blob
        uint256 permCommsOffset;
        uint256 sG2Offset;
        uint256 negG2Offset;
    }

    function _loadVk() internal view returns (Vk memory vk, bytes memory blob) {
        blob = _vkBlob();
        require(blob.length >= 160, "vk blob too short");
        assembly {
            let p := add(blob, 32)
            mstore(vk, mload(p))                // transcriptRepr
            mstore(add(vk,  32), mload(add(p, 32)))  // omega
        }
        // constants 1
        uint256 c1 = _word(blob, 64);
        vk.n               = uint64 (c1 >> (256 -  64));
        vk.k               = uint32((c1 >> (256 -  96)) & 0xffffffff);
        vk.numAdviceCols   = uint32((c1 >> (256 - 128)) & 0xffffffff);
        vk.numFixedCols    = uint32((c1 >> (256 - 160)) & 0xffffffff);
        vk.numInstanceCols = uint32((c1 >> (256 - 192)) & 0xffffffff);
        vk.numChallenges   = uint32((c1 >> (256 - 224)) & 0xffffffff);
        vk.numPhases       = uint32( c1                 & 0xffffffff);
        // constants 2
        uint256 c2 = _word(blob, 96);
        vk.csDegree           = uint32((c2 >> (256 -  32)) & 0xffffffff);
        vk.numSimpleSelectors = uint32((c2 >> (256 -  64)) & 0xffffffff);
        vk.blindingFactors    = uint32((c2 >> (256 -  96)) & 0xffffffff);
        vk.numAdviceQueries   = uint32((c2 >> (256 - 128)) & 0xffffffff);
        vk.numFixedQueries    = uint32((c2 >> (256 - 160)) & 0xffffffff);
        vk.numInstanceQueries = uint32((c2 >> (256 - 192)) & 0xffffffff);
        vk.numLookups         = uint32((c2 >> (256 - 224)) & 0xffffffff);
        vk.numTrashcans       = uint32( c2                 & 0xffffffff);
        // constants 3
        uint256 c3 = _word(blob, 128);
        vk.numPermColumns    = uint32((c3 >> (256 -  32)) & 0xffffffff);
        vk.numPermChunks     = uint32((c3 >> (256 -  64)) & 0xffffffff);
        vk.numQuotientLimbs  = uint32((c3 >> (256 -  96)) & 0xffffffff);
        vk.totalLookupHelpers = uint32((c3 >> (256 - 128)) & 0xffffffff);
        vk.numCommittedInstanceEvals = uint32((c3 >> (256 - 160)) & 0xffffffff);

        vk.fixedCommsOffset = 160;
        vk.permCommsOffset  = vk.fixedCommsOffset + uint256(vk.numFixedCols) * 128;
        vk.sG2Offset        = vk.permCommsOffset + uint256(vk.numPermColumns) * 128;
        vk.negG2Offset      = vk.sG2Offset + 256;
    }

    function _word(bytes memory b, uint256 o) internal pure returns (uint256 w) {
        assembly { w := mload(add(add(b, 32), o)) }
    }

    function _vkBlob() internal view returns (bytes memory) {
        // The VK contract's runtime code IS the blob (it's returned by the
        // constructor). We read it via EXTCODECOPY for gas efficiency.
        address vk = VK_CONTRACT;
        uint256 size;
        assembly { size := extcodesize(vk) }
        bytes memory out = new bytes(size);
        assembly {
            extcodecopy(vk, add(out, 32), 0, size)
        }
        return out;
    }

    /* ------------------------------------------------------------------ *
     *  MAIN VERIFIER                                                     *
     *                                                                    *
     *  Mirrors `proofs/src/plonk/verifier.rs::prepare`, which in turn    *
     *  calls `parse_trace` and `verify_algebraic_constraints`. For this  *
     *  port we fuse both into one pass to minimise memory churn on the  *
     *  EVM.                                                              *
     *                                                                    *
     *  Inputs:                                                           *
     *    - `instance`: the single public input Fq (BE 32 bytes).         *
     *    - `proof`: raw proof bytestream produced by the Rust prover     *
     *      with a `CircuitTranscript<Keccak256>`.                        *
     *                                                                    *
     *  Returns true iff the pairing check passes.                        *
     * ------------------------------------------------------------------ */

    function verify(bytes32 instance, bytes calldata proof)
        external
        returns (bool)
    {
        uint256 gStart;
        uint256 gEnd;

        (Vk memory vk, bytes memory vkBlob) = _loadVk();
        Reader memory rd = Reader({data: proof, pos: 0});
        Transcript memory t = _initTranscript();

        /* --- Hash verification key into transcript ---------------- */
        // transcript.common(&vk.transcript_repr)
        gStart = gasleft();
        {
            // The Rust side stores transcript_repr as Fq; Hashable<Keccak256>
            // uses its canonical LE 32-byte form.
            bytes memory reprLE = new bytes(32);
            bytes32 reprBE = vk.transcriptRepr;
            for (uint256 i = 0; i < 32; i++) {
                reprLE[i] = reprBE[31 - i];
            }
            _absorb(t, reprLE);
        }
        gEnd = gasleft();
        emit PhaseGas("hash_vk", gStart - gEnd);

        /* --- Hash instances --------------------------------------- */
        //   for committed_instances in committed_instances.iter() {
        //       for commitment in committed_instances.iter() { transcript.common(commitment) }
        //   }
        //   for instance in instances.iter() {
        //       for instance in instance.iter() {
        //           transcript.common(&F::from_u128(instance.len() as u128))?;
        //           for value in instance.iter() { transcript.common(value)? }
        //       }
        //   }
        //
        // `zk_stdlib::verify` always passes exactly one committed instance
        // column per proof, defaulting to `G1Affine::identity()` when no
        // actual committed instance is supplied. The compressed encoding of
        // the identity point is 48 bytes with the infinity flag set
        // (0xc0 || zeros).
        gStart = gasleft();
        {
            bytes memory identity = new bytes(48);
            identity[0] = 0xc0; // compressed + infinity flag
            _absorbG1Compressed(t, identity);

            _absorbU128(t, 1);
            bytes memory instLE = new bytes(32);
            for (uint256 i = 0; i < 32; i++) instLE[i] = instance[31 - i];
            _absorb(t, instLE);
        }
        gEnd = gasleft();
        emit PhaseGas("hash_instances", gStart - gEnd);

        /* --- Read advice commitments & squeeze challenges --------- */
        //
        //   for current_phase in vk.cs.phases() {
        //       for advice_commitments in advice_commitments.iter_mut() {
        //           for (phase, commitment) in vk.cs.advice_column_phase
        //               .iter().zip(advice_commitments.iter_mut()) {
        //               if current_phase == *phase {
        //                   *commitment = transcript.read()?;
        //               }
        //           }
        //       }
        //       for (phase, challenge) in ...
        //       { if current_phase == *phase { *challenge = transcript.squeeze_challenge(); } }
        //   }
        gStart = gasleft();
        for (uint256 p = 0; p < vk.numAdviceCols; p++) {
            bytes memory c = _readPointCompressed48(rd);
            emit TraceReadPoint("advice", c);
            _absorbG1Compressed(t, c);
        }
        // Challenges (none in the poseidon example, but we emit for debug).
        for (uint256 c = 0; c < vk.numChallenges; c++) {
            bytes32 ch = _squeezeFq(t);
            emit TraceChallenge("advice_challenge", ch);
        }
        gEnd = gasleft();
        emit PhaseGas("advice_phase", gStart - gEnd);

        /* --- Sample theta ---------------------------------------- */
        gStart = gasleft();
        bytes32 theta = _squeezeFq(t);
        emit TraceChallenge("theta", theta);
        gEnd = gasleft();
        emit PhaseGas("theta", gStart - gEnd);

        /* --- Read lookup multiplicities -------------------------- */
        // (one G1 per lookup per proof in the basic configuration).
        gStart = gasleft();
        for (uint256 l = 0; l < vk.numLookups; l++) {
            bytes memory c = _readPointCompressed48(rd);
            emit TraceReadPoint("lookup_mult", c);
            _absorbG1Compressed(t, c);
        }
        gEnd = gasleft();
        emit PhaseGas("lookup_mult", gStart - gEnd);

        /* --- Sample beta, gamma ----------------------------------- */
        gStart = gasleft();
        bytes32 beta  = _squeezeFq(t);  emit TraceChallenge("beta", beta);
        bytes32 gamma = _squeezeFq(t);  emit TraceChallenge("gamma", gamma);
        gEnd = gasleft();
        emit PhaseGas("beta_gamma", gStart - gEnd);

        /* --- Read permutation product commitments ----------------- */
        gStart = gasleft();
        for (uint256 i = 0; i < vk.numPermChunks; i++) {
            bytes memory c = _readPointCompressed48(rd);
            emit TraceReadPoint("perm_product", c);
            _absorbG1Compressed(t, c);
        }
        gEnd = gasleft();
        emit PhaseGas("perm_products", gStart - gEnd);

        /* --- Read lookup commitments ------------------------------ */
        gStart = gasleft();
        // Each lookup contributes `num_chunks` helper commitments plus 1
        // accumulator commitment. `totalLookupHelpers` == sum(num_chunks).
        {
            uint256 totalCommits = uint256(vk.totalLookupHelpers) + uint256(vk.numLookups);
            for (uint256 i = 0; i < totalCommits; i++) {
                bytes memory c = _readPointCompressed48(rd);
                emit TraceReadPoint("lookup", c);
                _absorbG1Compressed(t, c);
            }
        }
        gEnd = gasleft();
        emit PhaseGas("lookup_commits", gStart - gEnd);

        /* --- Sample trash_challenge ------------------------------- */
        gStart = gasleft();
        bytes32 trashCh = _squeezeFq(t);
        emit TraceChallenge("trash_challenge", trashCh);
        gEnd = gasleft();
        emit PhaseGas("trash_challenge", gStart - gEnd);

        /* --- Read trashcan commitments ---------------------------- */
        gStart = gasleft();
        for (uint256 i = 0; i < vk.numTrashcans; i++) {
            bytes memory c = _readPointCompressed48(rd);
            emit TraceReadPoint("trashcan", c);
            _absorbG1Compressed(t, c);
        }
        gEnd = gasleft();
        emit PhaseGas("trashcans", gStart - gEnd);

        /* --- Sample y --------------------------------------------- */
        gStart = gasleft();
        bytes32 y = _squeezeFq(t);
        emit TraceChallenge("y", y);
        gEnd = gasleft();
        emit PhaseGas("y", gStart - gEnd);

        /* --- Read quotient limb commitments ----------------------- */
        gStart = gasleft();
        for (uint256 i = 0; i < vk.numQuotientLimbs; i++) {
            bytes memory c = _readPointCompressed48(rd);
            emit TraceReadPoint("quotient_limb", c);
            _absorbG1Compressed(t, c);
        }
        gEnd = gasleft();
        emit PhaseGas("quotient_limbs", gStart - gEnd);

        /* --- Sample x --------------------------------------------- */
        gStart = gasleft();
        bytes32 x = _squeezeFq(t);
        emit TraceChallenge("x", x);
        gEnd = gasleft();
        emit PhaseGas("x", gStart - gEnd);

        /* --- Read evaluations ------------------------------------- */
        // instance_evals (for every instance query on a committed-instance
        // column), advice_evals, fixed_evals (minus simple selectors),
        // permutation common evals, permutation set evals
        // (cur/next/last), lookup evals, trashcan evals.
        gStart = gasleft();
        for (uint256 i = 0; i < vk.numCommittedInstanceEvals; i++) {
            bytes32 e = _readScalarLE32(rd);
            emit TraceReadScalar("committed_instance_eval", _leToBe(e));
            _absorbScalar(t, e);
        }
        for (uint256 i = 0; i < vk.numAdviceQueries; i++) {
            bytes32 e = _readScalarLE32(rd);
            emit TraceReadScalar("advice_eval", _leToBe(e));
            _absorbScalar(t, e);
        }
        for (uint256 i = 0; i < vk.numFixedQueries; i++) {
            bytes32 e = _readScalarLE32(rd);
            emit TraceReadScalar("fixed_eval", _leToBe(e));
            _absorbScalar(t, e);
        }
        for (uint256 i = 0; i < vk.numPermColumns; i++) {
            bytes32 e = _readScalarLE32(rd);
            emit TraceReadScalar("perm_common_eval", _leToBe(e));
            _absorbScalar(t, e);
        }
        // Per permutation chunk: (cur, next, and last if not the last chunk).
        for (uint256 i = 0; i < vk.numPermChunks; i++) {
            bytes32 eCur = _readScalarLE32(rd);  emit TraceReadScalar("perm_cur", _leToBe(eCur));
            _absorbScalar(t, eCur);
            bytes32 eNxt = _readScalarLE32(rd);  emit TraceReadScalar("perm_next", _leToBe(eNxt));
            _absorbScalar(t, eNxt);
            if (i + 1 != vk.numPermChunks) {
                bytes32 eLst = _readScalarLE32(rd);
                emit TraceReadScalar("perm_last", _leToBe(eLst));
                _absorbScalar(t, eLst);
            }
        }
        // Lookup evals: for each lookup, read:
        //   - m_eval                    (1)
        //   - helper_evals[num_chunks]  (num_chunks)
        //   - accumulator_eval          (1)
        //   - accumulator_next_eval     (1)
        // Total = sum(num_chunks) + 3 * num_lookups.
        {
            uint256 totalEvals =
                uint256(vk.totalLookupHelpers) + uint256(vk.numLookups) * 3;
            for (uint256 i = 0; i < totalEvals; i++) {
                bytes32 e = _readScalarLE32(rd);
                emit TraceReadScalar("lookup_eval", _leToBe(e));
                _absorbScalar(t, e);
            }
        }
        // Trashcan evals: per trashcan, 1 value.
        for (uint256 i = 0; i < vk.numTrashcans; i++) {
            bytes32 e = _readScalarLE32(rd);
            emit TraceReadScalar("trash_eval", _leToBe(e));
            _absorbScalar(t, e);
        }
        gEnd = gasleft();
        emit PhaseGas("evaluations", gStart - gEnd);

        /* --- KZG multi-open (multi_prepare) ----------------------- */
        //   let x1: Fr = transcript.squeeze_challenge();
        //   let x2: Fr = transcript.squeeze_challenge();
        //   ...
        //   let f_com = transcript.read()?;
        //   let x3 = transcript.squeeze_challenge();
        //   for _ in point_sets { q_evals.push(transcript.read()?); }
        //   let x4 = transcript.squeeze_challenge();
        //   let pi = transcript.read()?;
        gStart = gasleft();
        bytes32 x1 = _squeezeFq(t);  emit TraceChallenge("x1", x1);
        bytes32 x2 = _squeezeFq(t);  emit TraceChallenge("x2", x2);
        bytes memory fCom = _readPointCompressed48(rd);
        emit TraceReadPoint("f_com", fCom);
        _absorbG1Compressed(t, fCom);
        bytes32 x3 = _squeezeFq(t);  emit TraceChallenge("x3", x3);
        // The number of q_evals equals the number of distinct point-sets in
        // the multi-open argument. We derive it from the remaining proof
        // byte length: after this block we must still have exactly 48 bytes
        // left to read the final pi point.
        {
            uint256 remaining = rd.data.length - rd.pos;
            require(remaining >= 48 && (remaining - 48) % 32 == 0, "bad q_eval tail");
            uint256 numQEvals = (remaining - 48) / 32;
            for (uint256 i = 0; i < numQEvals; i++) {
                bytes32 e = _readScalarLE32(rd);
                emit TraceReadScalar("q_eval", _leToBe(e));
                _absorbScalar(t, e);
            }
        }
        bytes32 x4 = _squeezeFq(t);  emit TraceChallenge("x4", x4);
        bytes memory pi = _readPointCompressed48(rd);
        emit TraceReadPoint("pi", pi);
        _absorbG1Compressed(t, pi);
        gEnd = gasleft();
        emit PhaseGas("multi_prepare", gStart - gEnd);

        /* --- Final pairing check --------------------------------- *
         *                                                           *
         *  e(π, s·G2) · e(C − v·G + x3·π, -G2) = 1                  *
         *                                                           *
         *  The left-hand G1 is `pi`.                                *
         *  The right-hand G1 is the MSM computed by the Rust        *
         *  `DualMSM.right` (full algebraic constraint check). For   *
         *  this port we verify the *structural* pairing check using *
         *  the points read from the proof; a complete port of the   *
         *  MSM assembly is left for a follow-up.                    *
         * --------------------------------------------------------- */
        gStart = gasleft();
        bool ok = _finalPairing(vkBlob, vk, pi, fCom);
        emit TracePairing(ok);
        gEnd = gasleft();
        emit PhaseGas("pairing", gStart - gEnd);

        return ok;
    }

    /* --- helpers --------------------------------------------------- */

    function _absorbU128(Transcript memory t, uint128 v) internal pure {
        // Matches `transcript.common(&F::from_u128(instance.len() as u128))`.
        // The Rust side converts the u128 to Fq and absorbs its 32-byte LE
        // canonical form.
        bytes memory le = new bytes(32);
        for (uint256 i = 0; i < 16; i++) {
            le[i] = bytes1(uint8(v >> (8 * i)));
        }
        _absorb(t, le);
    }

    function _leToBe(bytes32 le) internal pure returns (bytes32 be) {
        for (uint256 i = 0; i < 32; i++) {
            be |= bytes32(uint256(uint8(le[i])) << (8 * i));
        }
    }

    function _finalPairing(
        bytes memory vkBlob,
        Vk memory vk,
        bytes memory pi,
        bytes memory /*fCom*/
    ) internal returns (bool) {
        // Perform the structural pairing check with *real* decompressed
        // points. The full 1:1 port of
        // `KZGCommitmentScheme::multi_prepare` still needs to build the
        // `C − v·G + x3·π` right-hand side via the linearization/multi-open
        // MSM (see TODO in this contract's docstring). Until that lands,
        // this function exercises the EIP-2537 pairing precompile with the
        // decompressed π, the VK's s·G2 and −G2, and emits a
        // `TraceIntermediate` event with the decompressed π so the Rust
        // harness can cross-check that side of the equivalence.
        bytes memory sG2  = _vkSlice(vkBlob, vk.sG2Offset,  256);
        bytes memory ngG2 = _vkSlice(vkBlob, vk.negG2Offset, 256);

        bytes memory piEip = _g1CompressedToEip2537(pi);

        // Emit the decompressed π coordinates as two scalar events so that
        // the Rust-side tracer can reconstruct the exact bytes the
        // precompile received. Each coordinate is a 48-byte Fp element
        // zero-padded to 64 bytes; we hash the two halves so a single
        // bytes32 event is sufficient.
        bytes32 piDigest = keccak256(piEip);
        emit TraceIntermediate("pi_decompressed_digest", piDigest);

        bytes memory pairs = abi.encodePacked(piEip, sG2, piEip, ngG2);
        return _pairingCheck(pairs);
    }

    function _vkSlice(bytes memory blob, uint256 o, uint256 len)
        internal pure returns (bytes memory out)
    {
        out = new bytes(len);
        for (uint256 i = 0; i < len; i++) out[i] = blob[o + i];
    }

    /// Decompress a BLS12-381 compressed G1 point (48 bytes, big-endian) to
    /// the 128-byte EIP-2537 uncompressed format (`pad16 || x || pad16 || y`).
    ///
    /// Compressed encoding (zcash BLS12-381 format, as produced by
    /// midnight-curves `G1Projective::to_bytes`):
    ///   * byte 0, bit 7 (0x80): compressed flag (always 1 for compressed)
    ///   * byte 0, bit 6 (0x40): infinity flag (all other bits must be 0)
    ///   * byte 0, bit 5 (0x20): y-parity flag ("sort bit"): 1 iff y is the
    ///                           lexicographically greater of (y, p - y)
    ///   * remaining 381 bits   : x coordinate (BE)
    ///
    /// Decompression follows:
    ///   y² = x³ + 4  (BLS12-381 short Weierstrass b = 4)
    ///   y  = y² ^ ((p+1)/4) mod p    (since p ≡ 3 mod 4)
    ///   if sort_flag xor (y > p/2): y = p - y
    ///
    /// Field arithmetic is performed via the Prague ModExp precompile (0x05):
    /// cubing uses B^3 mod p directly, the "add 4" step is folded into the
    /// ModExp reduction by appending a one-bit prefix to the cube bytes.
    function _g1CompressedToEip2537(bytes memory c48)
        internal view returns (bytes memory out)
    {
        require(c48.length == 48, "bad compressed len");

        // Read flags from the most significant byte.
        uint8 flags = uint8(c48[0]);
        bool isCompressed = (flags & 0x80) != 0;
        bool isInfinity   = (flags & 0x40) != 0;
        bool sortFlag     = (flags & 0x20) != 0;
        require(isCompressed, "not compressed");

        // The 128-byte EIP-2537 encoding of the identity is all zeros.
        if (isInfinity) {
            return new bytes(128);
        }

        // Clear the top 3 flag bits to recover x (still 48 bytes, BE).
        bytes memory xBytes = new bytes(48);
        for (uint256 i = 0; i < 48; i++) xBytes[i] = c48[i];
        xBytes[0] = bytes1(uint8(xBytes[0]) & 0x1f);

        // Compute x³ mod p via ModExp (B=48 bytes, E=0x03, M=p=48 bytes).
        bytes memory cube = _modExpFp(xBytes, hex"03");

        // Compute (cube + 4) mod p. Since cube < p, (cube + 4) fits in 49
        // bytes; we run it through ModExp with E=1 to reduce canonically.
        bytes memory cubePlus4 = new bytes(49);
        for (uint256 i = 0; i < 48; i++) cubePlus4[i + 1] = cube[i];
        {
            uint256 i = 48;
            uint16 carry = 4;
            while (carry != 0 && i > 0) {
                uint16 v = uint16(uint8(cubePlus4[i])) + carry;
                cubePlus4[i] = bytes1(uint8(v & 0xff));
                carry = v >> 8;
                unchecked { i--; }
            }
            if (carry != 0) cubePlus4[0] = bytes1(uint8(uint16(uint8(cubePlus4[0])) + carry));
        }
        bytes memory ySquared = _modExpReduce(cubePlus4);

        // Compute y = ySquared ^ ((p+1)/4) mod p.
        bytes memory expBytes = _fpSqrtExpBytes();
        bytes memory y = _modExpFp(ySquared, expBytes);

        // Parity canonicalisation: `sortFlag` is set iff the "larger" root
        // was chosen by the prover. Compute whether our y is in the upper
        // half (y > (p-1)/2). If that mismatches, replace y with p - y.
        bool yIsLarger = _fpIsGreaterThanHalf(y);
        if (sortFlag != yIsLarger) {
            y = _fpNegate(y);
        }

        // Pack into EIP-2537 128-byte layout: 16 zero bytes || x(48) || 16
        // zero bytes || y(48).
        out = new bytes(128);
        for (uint256 i = 0; i < 48; i++) {
            out[16 + i]  = xBytes[i];
            out[80 + i]  = y[i];
        }
    }

    /// Big-endian 48-byte encoding of the BLS12-381 base-field modulus p.
    function _fpModulusBytes() internal pure returns (bytes memory m) {
        m = new bytes(48);
        uint256 hi = FP_MODULUS_HI;
        uint256 lo = FP_MODULUS_LO;
        // Hi contributes the top 16 bytes (bytes 0..16); lo the bottom 32.
        for (uint256 i = 0; i < 16; i++) {
            m[15 - i] = bytes1(uint8(hi >> (i * 8)));
        }
        for (uint256 i = 0; i < 32; i++) {
            m[47 - i] = bytes1(uint8(lo >> (i * 8)));
        }
    }

    /// Big-endian 48-byte encoding of (p+1)/4.
    function _fpSqrtExpBytes() internal pure returns (bytes memory e) {
        e = new bytes(48);
        uint256 hi = FP_SQRT_EXP_HI;
        uint256 lo = FP_SQRT_EXP_LO;
        for (uint256 i = 0; i < 16; i++) {
            e[15 - i] = bytes1(uint8(hi >> (i * 8)));
        }
        for (uint256 i = 0; i < 32; i++) {
            e[47 - i] = bytes1(uint8(lo >> (i * 8)));
        }
    }

    /// Call the Prague ModExp precompile (0x05) with the given base bytes
    /// (variable length), exponent bytes (big-endian), and the BLS12-381 Fp
    /// modulus. Returns a 48-byte big-endian canonical Fp element.
    function _modExpFp(bytes memory base, bytes memory exp)
        internal view returns (bytes memory)
    {
        bytes memory m = _fpModulusBytes();
        bytes memory input = abi.encodePacked(
            uint256(base.length),
            uint256(exp.length),
            uint256(48),
            base,
            exp,
            m
        );
        (bool ok, bytes memory out) = PC_MODEXP.staticcall(input);
        require(ok && out.length == 48, "ModExp failed");
        return out;
    }

    /// Convenience wrapper: ModExp with exponent = 1 (i.e. reduce modulo p).
    function _modExpReduce(bytes memory base) internal view returns (bytes memory) {
        return _modExpFp(base, hex"01");
    }

    /// Returns true iff y (big-endian 48-byte Fp element, already canonical)
    /// satisfies y > (p-1)/2 i.e. lies in the upper half of Fp. Used by the
    /// compressed-point sort flag canonicalisation.
    function _fpIsGreaterThanHalf(bytes memory y) internal pure returns (bool) {
        // (p - 1) / 2 = 0x0d008...d555 (48 bytes BE). Compute on the fly by
        // halving the modulus; p is odd so (p-1)/2 = p >> 1 with the bottom
        // bit cleared.
        uint256 half_hi = FP_MODULUS_HI >> 1;
        uint256 half_lo = (FP_MODULUS_LO >> 1) | (FP_MODULUS_HI << 255);
        // The top 16 bytes of y.
        uint256 y_hi;
        uint256 y_lo;
        assembly {
            y_hi := shr(128, mload(add(y, 32)))
            y_lo := mload(add(y, 48))
        }
        if (y_hi != half_hi) return y_hi > half_hi;
        return y_lo > half_lo;
    }

    /// Compute p - y for y a canonical Fp element encoded big-endian in 48
    /// bytes. Result is also big-endian 48 bytes.
    function _fpNegate(bytes memory y) internal pure returns (bytes memory r) {
        r = new bytes(48);
        uint16 borrow = 0;
        bytes memory m = _fpModulusBytes();
        for (uint256 i = 47; ; ) {
            int32 diff = int32(uint32(uint8(m[i]))) - int32(uint32(uint8(y[i]))) - int32(int16(borrow));
            if (diff < 0) {
                diff += 256;
                borrow = 1;
            } else {
                borrow = 0;
            }
            r[i] = bytes1(uint8(uint32(diff)));
            if (i == 0) break;
            unchecked { i--; }
        }
    }

    /* ------------------------------------------------------------------ *
     *  Fr (scalar field) arithmetic                                      *
     *                                                                    *
     *  The BLS12-381 scalar field fits in one 256-bit word, so we can    *
     *  use the EVM's native `addmod` / `mulmod` for basic arithmetic.    *
     *  For inversion and arbitrary exponentiation we reuse the ModExp    *
     *  precompile (0x05) with the 32-byte scalar modulus `r = FR_MODULUS`*
     *  and Fermat's little theorem: a^{-1} ≡ a^{r-2} (mod r).            *
     * ------------------------------------------------------------------ */

    function _frAdd(uint256 a, uint256 b) internal pure returns (uint256) {
        return addmod(a, b, FR_MODULUS);
    }

    function _frSub(uint256 a, uint256 b) internal pure returns (uint256) {
        return addmod(a, FR_MODULUS - b, FR_MODULUS);
    }

    function _frNeg(uint256 a) internal pure returns (uint256) {
        return a == 0 ? 0 : FR_MODULUS - a;
    }

    function _frMul(uint256 a, uint256 b) internal pure returns (uint256) {
        return mulmod(a, b, FR_MODULUS);
    }

    /// Compute `base^exp mod r` via the Prague ModExp precompile.
    function _frPow(uint256 base, uint256 exp) internal view returns (uint256 result) {
        bytes32 b = bytes32(base);
        bytes32 e = bytes32(exp);
        bytes32 m = bytes32(FR_MODULUS);
        bytes memory input = abi.encodePacked(
            uint256(32), uint256(32), uint256(32), b, e, m
        );
        (bool ok, bytes memory out) = PC_MODEXP.staticcall(input);
        require(ok && out.length == 32, "Fr ModExp failed");
        assembly { result := mload(add(out, 32)) }
    }

    function _frInv(uint256 a) internal view returns (uint256) {
        require(a != 0, "inverse of zero");
        return _frPow(a, FR_MODULUS - 2);
    }

    /// Returns `x * omega^rotation` where `rotation` is a signed offset in
    /// the evaluation domain, mirroring `EvaluationDomain::rotate_omega`.
    /// Matches the Rust helper `Rotation(k)` where negative rotations are
    /// handled via multiplication by `omega^{-k}`.
    function _rotateOmega(uint256 x, int256 rotation, uint256 omega, uint256 n)
        internal view returns (uint256)
    {
        if (rotation == 0) return x;
        if (rotation > 0) {
            return _frMul(x, _frPow(omega, uint256(rotation)));
        } else {
            // x * omega^{-|r|} = x * omega^{n - |r|}  (since omega^n = 1).
            uint256 absR = uint256(-rotation);
            return _frMul(x, _frPow(omega, n - (absR % n)));
        }
    }

    /// Batch-compute the Lagrange basis evaluations `L_i(x)` for a
    /// contiguous range of integer indices. Mirrors
    /// `EvaluationDomain::l_i_range(x, xn, range)` on the Rust side.
    ///
    /// Uses the closed-form:
    ///
    ///     L_i(x) = ω^i · (x^n − 1) / (n · (x − ω^i))
    ///
    /// which is valid for any `i` in the domain's index ring when `x` is
    /// outside the domain (the verifier's `x` always is, with overwhelming
    /// probability). The `xn = x^n` argument is passed separately since
    /// callers (e.g. `verify_algebraic_constraints`) already compute it.
    function _lagrangeIRange(
        uint256 x,
        uint256 xn,
        int256 startInclusive,
        int256 endInclusive,
        uint256 omega,
        uint256 n
    ) internal view returns (uint256[] memory out) {
        require(endInclusive >= startInclusive, "empty range");
        uint256 len = uint256(endInclusive - startInclusive + 1);
        out = new uint256[](len);

        // Common numerator: (x^n - 1).
        uint256 numer = _frSub(xn, 1);
        // Common denominator factor: n (as an Fr element).
        uint256 nInv = _frInv(n % FR_MODULUS);

        // For efficiency, compute omega^start and walk through the range.
        uint256 wI = _rotateOmega(1, startInclusive, omega, n);
        uint256 wStep = omega; // multiply by ω to advance i by +1

        for (uint256 k = 0; k < len; k++) {
            // denominator = n * (x - ω^i)
            uint256 xMinusWi = _frSub(x, wI);
            uint256 invXMinusWi = _frInv(xMinusWi);
            // L_i(x) = ω^i · (x^n - 1) / (n · (x - ω^i))
            uint256 li = _frMul(wI, _frMul(numer, _frMul(nInv, invXMinusWi)));
            out[k] = li;
            wI = _frMul(wI, wStep);
        }
    }

    /// Compute the evaluation of an instance column at point `x` given the
    /// public-input values by taking the inner product with the Lagrange
    /// basis at `x`, exactly as the Rust verifier does for non-committed
    /// instance columns.
    ///
    /// For the poseidon example there is exactly one non-committed
    /// instance column with a single value. `lagrangeSlice` is the
    /// pre-computed L_i(x) values over the rotation range required by
    /// `cs.instance_queries()`.
    function _instanceEvalFromLagrange(
        uint256[] memory instance,
        uint256[] memory lagrangeSlice
    ) internal pure returns (uint256 acc) {
        require(instance.length <= lagrangeSlice.length, "short L slice");
        acc = 0;
        for (uint256 i = 0; i < instance.length; i++) {
            acc = addmod(acc, mulmod(instance[i], lagrangeSlice[i], FR_MODULUS), FR_MODULUS);
        }
    }

    /* ------------------------------------------------------------------ *
     *  EIP-2537 G1MSM wrapper                                            *
     *                                                                    *
     *  The G1MSM precompile expects `(point, scalar)` pairs where the    *
     *  point is EIP-2537 128-byte uncompressed and the scalar is 32      *
     *  bytes big-endian. Returns a single 128-byte G1 point.             *
     * ------------------------------------------------------------------ */

    function _g1MsmSingle(bytes memory point, uint256 scalar)
        internal view returns (bytes memory)
    {
        require(point.length == 128, "msm bad point");
        bytes memory input = abi.encodePacked(point, bytes32(scalar));
        return _g1Msm(input);
    }

    /// Compute `sum_i scalars[i] * points[i]` via the G1MSM precompile in a
    /// single call. `points` is a concatenation of 128-byte EIP-2537 G1
    /// encodings and must be the same length (in entries) as `scalars`.
    function _g1MsmBatch(bytes[] memory points, uint256[] memory scalars)
        internal view returns (bytes memory)
    {
        require(points.length == scalars.length, "msm len mismatch");
        require(points.length > 0, "msm empty");
        bytes memory input = new bytes(points.length * 160);
        uint256 dst = 0;
        for (uint256 i = 0; i < points.length; i++) {
            require(points[i].length == 128, "msm bad point");
            for (uint256 j = 0; j < 128; j++) input[dst + j] = points[i][j];
            dst += 128;
            bytes32 s = bytes32(scalars[i]);
            for (uint256 j = 0; j < 32; j++) input[dst + j] = s[j];
            dst += 32;
        }
        return _g1Msm(input);
    }

    /// Lagrange interpolation at `x3`: given a set of (point, eval) pairs
    /// `(z_i, y_i)`, returns `r(x3)` where `r` is the unique degree-<n
    /// polynomial satisfying `r(z_i) = y_i`. Used by `multi_prepare` to
    /// reconstruct `f_eval` from the prover's `q_evals_on_x3`.
    ///
    /// Implementation follows the barycentric form:
    ///     r(x3) = sum_i  y_i *  prod_{j ≠ i} (x3 - z_j) / (z_i - z_j)
    function _lagrangeInterpAtX3(
        uint256[] memory points,
        uint256[] memory evals,
        uint256 x3
    ) internal view returns (uint256 result) {
        require(points.length == evals.length, "lagrange len");
        uint256 n_ = points.length;
        result = 0;
        for (uint256 i = 0; i < n_; i++) {
            uint256 num = 1;
            uint256 den = 1;
            for (uint256 j = 0; j < n_; j++) {
                if (j == i) continue;
                num = _frMul(num, _frSub(x3, points[j]));
                den = _frMul(den, _frSub(points[i], points[j]));
            }
            uint256 term = _frMul(evals[i], _frMul(num, _frInv(den)));
            result = _frAdd(result, term);
        }
    }
}
