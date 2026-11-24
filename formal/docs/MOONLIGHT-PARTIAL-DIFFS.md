# Moonlight partial diffs (measured)

Source of record: `proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol`.
Probe: `formal/Midfall/Generator/MoonlightPartialKats.lean`, `MoonlightPartialCtx`.

The KAT measures raw `occ` and `includeBoundary` on the unmodified deployed
source. This file records the exact line-level content differences. The
deployed artifact is an older generator output; its Askama include wrapper
prefixes an extra four spaces to the first output line of five partials, so
the line comparison below strips leading whitespace. The raw byte verdict is
in the KAT and repeated per section: six partials occur 0 times; the quotient
linearization tail occurs once and is byte-identical, but it is an interior
sub-block of the larger quotient include, so `includeBoundary = false`.
Line numbers are absolute in the deployed source and in the current render;
a blank number means the line has no counterpart in that file.

## Summary

| partial | deployed lines | current lines | changed lines | hunks | current bytes | raw occ | raw boundary |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| `AssemblyHelpers` | 232 | 304 | 104 | 13 | 16226 | 0 | false |
| `AccumulatorHelpers` | 331 | 297 | 154 | 17 | 17009 | 0 | false |
| `VkLoading` | 87 | 93 | 16 | 4 | 5821 | 0 | false |
| `TranscriptProofParser` | 334 | 334 | 10 | 5 | 17968 | 0 | false |
| `Lagrange` | 80 | 90 | 28 | 7 | 4745 | 0 | false |
| `QuotientAndLinearization (linearization tail)` | 40 | 40 | 0 | 0 | 1901 | 1 | false |
| `FinalPairing` | 73 | 76 | 25 | 7 | 4221 | 0 | false |

The exact statuses are pinned by `moonlight_recordedStatus_ok` in the KAT
module; this file is the human-readable line record.

## AssemblyHelpers

Deployed lines 317-548 (232 lines after trimming blank edges); current render 304 lines, 16226 UTF-8 bytes; raw `occ = 0`, raw `includeBoundary = false`.

```diff
@@ deployed 317-317 / current 1-9 @@
+           1 |             // Revert with a 4-byte custom-error selector (P4/L-3). Writing at
+           2 |             // 0x00 is Solidity's legal scratch space and never touches the
+           3 |             // generated layout, which starts at TRANSCRIPT_MPTR.
+           4 |             function fail(sel) {
+           5 |                 mstore(0x00, shl(224, sel))
+           6 |                 revert(0x00, 0x04)
+           7 |             }
+           8 | 
    317     9 |                 // Inverse of a Fr scalar via modexp(x, r-2, r). The verifier
@@ deployed 323-326 / current 15-24 @@
    323    15 |                 // Zero has no multiplicative inverse in Fr; callers rely on a
-   324       |                 // revert here rather than a bogus modexp result.
-   325       |                 if iszero(x) { revert(0, 0) }
+          16 |                 // revert here rather than a bogus modexp result. Check the
+          17 |                 // full canonical range, not just the literal word 0: for any
+          18 |                 // x congruent to 0 mod r (x = r, say) modexp returns 0, which
+          19 |                 // downstream mulmod chains would silently absorb. Every
+          20 |                 // current call site feeds addmod/mulmod output, so this only
+          21 |                 // guards against a future emitter passing a raw scalar.
+          22 |                 if iszero(lt(x, FR_MODULUS)) { fail(ERR_NON_CANONICAL_SCALAR) }
+          23 |                 if iszero(x) { fail(ERR_NON_CANONICAL_SCALAR) }
    326    24 |                 let p := 0x2600
@@ deployed 334-337 / current 32-35 @@
    334    32 |                 mstore(add(p, 0xa0), FR_MODULUS)
-   335       |                 if iszero(staticcall(gas(), 0x05, p, 0xc0, p, 0x20)) { revert(0, 0) }
-   336       |                 if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
+          33 |                 if iszero(staticcall(MODEXP_GAS, 0x05, p, 0xc0, p, 0x20)) { fail(ERR_PRECOMPILE_FAILED) }
+          34 |                 if iszero(eq(returndatasize(), 0x20)) { fail(ERR_PRECOMPILE_FAILED) }
    337    35 |                 inv := mload(p)
@@ deployed 395-398 / current 93-96 @@
    395    93 |                 let y_lo := calldataload(add(cptr, 0x60))
-   396       |                 if shr(128, x_hi_word) { revert(0, 0) }
-   397       |                 if shr(128, y_hi_word) { revert(0, 0) }
+          94 |                 if shr(128, x_hi_word) { fail(ERR_BAD_POINT_ENCODING) }
+          95 |                 if shr(128, y_hi_word) { fail(ERR_BAD_POINT_ENCODING) }
    398    96 | 
@@ deployed 401-406 / current 99-104 @@
    401    99 |                 if iszero(or(lt(x_hi, BLS_P_HI), and(eq(x_hi, BLS_P_HI), iszero(gt(x_lo, BLS_P_MINUS_ONE_LO))))) {
-   402       |                     revert(0, 0)
+         100 |                     fail(ERR_BAD_POINT_ENCODING)
    403   101 |                 }
    404   102 |                 if iszero(or(lt(y_hi, BLS_P_HI), and(eq(y_hi, BLS_P_HI), iszero(gt(y_lo, BLS_P_MINUS_ONE_LO))))) {
-   405       |                     revert(0, 0)
+         103 |                     fail(ERR_BAD_POINT_ENCODING)
    406   104 |                 }
@@ deployed 442-444 / current 140-151 @@
    442   140 |             // boundary decides whether to fail closed.
-   443       |             function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret {
+         141 |             //
+         142 |             // MF-4: the second return value separates a FAILED PRECOMPILE
+         143 |             // (staticcall reverted / OOG'd / returned the wrong size -- a
+         144 |             // chain or gas-schedule fault) from a REJECTED INPUT (a zero or
+         145 |             // non-canonical denominator, which for the Lagrange batch means
+         146 |             // the squeezed x landed on a domain point). Both fail closed at
+         147 |             // the section boundary, but they are different incidents and used
+         148 |             // to surface under the same PrecompileFailed selector, pointing
+         149 |             // responders at the node when the transcript was the cause.
+         150 |             function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret, precompile_failed {
    444   151 |                 ret := success
@@ deployed 460-461 / current 167-175 @@
    460   167 |                     let x := mload(mptr_start)
+         168 |                     // Reject anything congruent to zero mod r, not just the
+         169 |                     // literal word 0: modexp would return 0 for those too, and
+         170 |                     // the caller would take it for a valid inverse.
+         171 |                     if iszero(lt(x, r)) {
+         172 |                         ret := 0
+         173 |                         leave
+         174 |                     }
    461   175 |                     if iszero(x) {
@@ deployed 472-475 / current 186-190 @@
    472   186 |                     mstore(add(single_scratch, 0xa0), r)
-   473       |                     ret := staticcall(gas(), 0x05, single_scratch, 0xc0, single_scratch, 0x20)
+         187 |                     ret := staticcall(MODEXP_GAS, 0x05, single_scratch, 0xc0, single_scratch, 0x20)
    474   188 |                     ret := and(ret, eq(returndatasize(), 0x20))
+         189 |                     precompile_failed := iszero(ret)
    475   190 |                     if ret { mstore(mptr_start, mload(single_scratch)) }
@@ deployed 480-486 / current 195-214 @@
    480   195 |                 // including, the final element. `gp` becomes the total product.
+         196 |                 //
+         197 |                 // Match the single-element path: reject non-canonical words
+         198 |                 // (x >= r) instead of letting mulmod reduce them silently, so
+         199 |                 // accept/reject semantics do not depend on batch length.
    481   200 |                 let gp_mptr := scratch_mptr
    482   201 |                 let gp := mload(mptr_start)
+         202 |                 if iszero(lt(gp, r)) {
+         203 |                     ret := 0
+         204 |                     leave
+         205 |                 }
    483   206 |                 let mptr := add(mptr_start, 0x20)
    484   207 |                 for {} lt(mptr, sub(mptr_end, 0x20)) {} {
-   485       |                     gp := mulmod(gp, mload(mptr), r)
+         208 |                     let x := mload(mptr)
+         209 |                     if iszero(lt(x, r)) {
+         210 |                         ret := 0
+         211 |                         leave
+         212 |                     }
+         213 |                     gp := mulmod(gp, x, r)
    486   214 |                     mstore(gp_mptr, gp)
@@ deployed 489-491 / current 217-224 @@
    489   217 |                 }
-   490       |                 gp := mulmod(gp, mload(mptr), r)
+         218 |                 let x_last := mload(mptr)
+         219 |                 if iszero(lt(x_last, r)) {
+         220 |                     ret := 0
+         221 |                     leave
+         222 |                 }
+         223 |                 gp := mulmod(gp, x_last, r)
    491   224 |                 // A zero total product means at least one denominator was
@@ deployed 504-507 / current 237-247 @@
    504   237 |                 mstore(add(gp_mptr, 0xa0), r)
-   505       |                 ret := staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20)
+         238 |                 ret := staticcall(MODEXP_GAS, 0x05, gp_mptr, 0xc0, gp_mptr, 0x20)
    506   239 |                 ret := and(ret, eq(returndatasize(), 0x20))
+         240 |                 precompile_failed := iszero(ret)
+         241 |                 // Leave before the backward pass on a failed modexp. A failed
+         242 |                 // staticcall writes no output, so `mload(gp_mptr)` would read
+         243 |                 // back the stale frame header and the pass below would
+         244 |                 // overwrite every denominator in [mptr_start, mptr_end) with
+         245 |                 // garbage products before returning ret = 0.
+         246 |                 if iszero(ret) { leave }
    507   247 |                 let all_inv := mload(gp_mptr)
@@ deployed 530-531 / current 270-276 @@
    530   270 |                 ret := success
+         271 |                 // `leave` (not a revert) keeps the trace render able to return
+         272 |                 // `false`; the terminal guard in TraceReturn.yul now reverts
+         273 |                 // with ProofRejected in a production render, so no path hands
+         274 |                 // control back to a caller that would report success for an
+         275 |                 // unverified proof.
    531   276 |                 if iszero(ret) { leave }
@@ deployed 542-547 / current 287-303 @@
    542   287 |                 mcopy(add(scratch, 0x200),  NEG_S_G2_BASE_MPTR,       0x100)
-   543       |                 ret := staticcall(gas(), 0x0f, scratch, 0x0300, scratch, 0x20)
+         288 |                 // MF-4: separate "the chain could not run the pairing" from
+         289 |                 // "the pairing ran and rejected this proof". Both fail closed,
+         290 |                 // but they are different incidents: the first points at the
+         291 |                 // node/fork (a missing, repriced, or short-returning
+         292 |                 // precompile), the second at the proof. Collapsing them into
+         293 |                 // ProofRejected sent every responder looking at the wrong one.
+         294 |                                 ret := staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 0x0300, scratch, 0x20)
    544   295 |                 ret := and(ret, eq(returndatasize(), 0x20))
-   545       |                 ret := and(ret, mload(scratch))
-   546       |                 if iszero(ret) { revert(0, 0) }
+         296 |                 if iszero(ret) { fail(ERR_PRECOMPILE_FAILED) }
+         297 |                 // Compare against 1 rather than truncating to the low bit:
+         298 |                 // `and(ret, word)` would accept any odd result word. EIP-2537
+         299 |                 // only ever returns 0 or 1, so this matches the strict form
+         300 |                 // the constructor smoke test already uses.
+         301 |                 ret := and(ret, eq(mload(scratch), 1))
+         302 |                 if iszero(ret) { fail(ERR_PROOF_REJECTED) }
    547   303 |                 ret := 1
```

## AccumulatorHelpers

Deployed lines 550-880 (331 lines after trimming blank edges); current render 297 lines, 17009 UTF-8 bytes; raw `occ = 0`, raw `includeBoundary = false`.

```diff
@@ deployed 554-557 / current 5-8 @@
    554     5 |             // (coord - 1) are packed four-at-a-time into native field elements.
-   555       |             // The x coordinate's first packed word carries the identity flag by
-   556       |             // adding one raw radix base. Rebuild EIP-2537 padded
+           6 |             // The point's identity flag follows the y coordinate as its own
+           7 |             // public-input word. Rebuild EIP-2537 padded
    557     8 |             // (x_hi, x_lo, y_hi, y_lo) words from that encoding.
@@ deployed 561-562 / current 12-16 @@
    561    12 |             //   word 1: next limbs, if any
+          13 |             //
+          14 |             // Public-input layout for one point:
+          15 |             //   x coordinate words, y coordinate words, identity flag word
    562    16 |             //
@@ deployed 567-569 / current 21-23 @@
    567    21 |             // representation expected by the BLS12-381 precompiles.
-   568       |             function load_acc_coord_shifted(src, bits, n, base, limbs_per_word, first_adjust) -> hi, lo {
+          22 |             function load_acc_coord_shifted(src, bits, n, base, limbs_per_word) -> hi, lo {
    569    23 |                 // Mask for one radix limb, e.g. 2^56 - 1 for the current
@@ deployed 573-580 / current 27-30 @@
    573    27 |                     // Limb words are little-endian packed inside each Fr
-   574       |                     // public input. `first_adjust` removes the identity flag
-   575       |                     // base from the first x word when present.
+          28 |                     // public input.
    576    29 |                     let packed := calldataload(add(src, mul(div(i, limbs_per_word), 0x20)))
-   577       |                     if and(iszero(div(i, limbs_per_word)), first_adjust) {
-   578       |                         packed := sub(packed, first_adjust)
-   579       |                     }
    580    30 |                     // Select limb i from its packed field word. The mod/div
@@ deployed 606-628 / current 56-57 @@
    606    56 |                 yes := and(eq(hi, BLS_P_HI), eq(lo, BLS_P_MINUS_ONE_LO))
-   607       |             }
-   608       | 
-   609       |             // Canonical encoded accumulator identity:
-   610       |             //   x = p-1 plus the identity flag in the first packed word,
-   611       |             //   y = p-1 with no identity flag.
-   612       |             // It decodes to the EIP-2537 point-at-infinity slot (all zeros).
-   613       |             //
-   614       |             // This fast path is deliberately stricter than "decodes to zero":
-   615       |             // the point at infinity has exactly one accepted public-input
-   616       |             // encoding. Non-canonical zero-like encodings are rejected later.
-   617       |             function is_acc_encoded_identity(src) -> yes {
-   618       |                 yes := and(
-   619       |                     and(
-   620       |                         eq(calldataload(src), BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG),
-   621       |                         eq(calldataload(add(src, 0x20)), BLS_P_MINUS_ONE_PACKED_1)
-   622       |                     ),
-   623       |                     and(
-   624       |                         eq(calldataload(add(src, 0x40)), BLS_P_MINUS_ONE_PACKED_0),
-   625       |                         eq(calldataload(add(src, 0x60)), BLS_P_MINUS_ONE_PACKED_1)
-   626       |                     )
-   627       |                 )
    628    57 |             }
@@ deployed 655-674 / current 84-89 @@
    655    84 | 
-   656       |             // Decode one shifted coordinate. `allow_id` is true only for x,
-   657       |             // because the identity flag lives in x's first packed word.
-   658       |             function load_acc_coord(src, allow_id, bits, n, base, limbs_per_word) -> ok, hi, lo, is_id {
+          85 |             // Decode one shifted coordinate of a non-identity point.
+          86 |             function load_acc_coord(src, bits, n, base, limbs_per_word) -> ok, hi, lo {
    659    87 |                 ok := check_acc_coord_packing(src, bits, n, limbs_per_word)
-   660       |                 if and(allow_id, iszero(lt(calldataload(src), base))) {
-   661       |                     // Probe the x identity flag by removing one radix base and
-   662       |                     // checking whether the adjusted coordinate is p-1.
-   663       |                     //
-   664       |                     // `calldataload(src) >= base` is a cheap prefilter: only x
-   665       |                     // can carry this flag, and adding one radix base must make
-   666       |                     // the first packed word at least base.
-   667       |                     let adj_hi, adj_lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word, base)
-   668       |                     is_id := is_bls_p_minus_one(adj_hi, adj_lo)
-   669       |                 }
-   670       | 
-   671       |                 // Decode again with the identity adjustment applied only when
-   672       |                 // the canonical identity flag was actually detected.
-   673       |                 hi, lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word, mul(is_id, base))
+          88 |                 hi, lo := load_acc_coord_shifted(src, bits, n, base, limbs_per_word)
    674    89 |                 ok := and(
@@ deployed 704-714 / current 119-137 @@
    704   119 |             function load_acc_point(dst, src, bits, n, base) -> ok, is_id {
-   705       |                 // Prefer the canonical all-coordinate identity encoding before
-   706       |                 // attempting coordinate-level shifted decoding. This accepts
-   707       |                 // the point at infinity only in the exact form generated by the
-   708       |                 // circuit's public-input codec.
-   709       |                 is_id := is_acc_encoded_identity(src)
+         120 |                 // x and y occupy coord_words packed public-input words each;
+         121 |                 // the identity flag word immediately follows y.
+         122 |                 let limbs_per_word := 4
+         123 |                 let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
+         124 |                 let flag := calldataload(add(src, mul(mul(2, coord_words), 0x20)))
+         125 |                 // The circuit constrains the flag as a bit. Anything else is a
+         126 |                 // malformed public input rather than a non-identity point.
+         127 |                 ok := lt(flag, 2)
+         128 |                 is_id := eq(flag, 1)
+         129 | 
    710   130 |                 if is_id {
-   711       |                     ok := 1
-   712       |                     // EIP-2537 encodes G1 identity as four zero words:
-   713       |                     // x_hi = x_lo = y_hi = y_lo = 0.
+         131 |                     // When the flag is set the circuit leaves x and y
+         132 |                     // unconstrained ("can be anything"), so they carry no
+         133 |                     // meaning and must not be decoded or range-checked here.
+         134 |                     // The proof itself still binds whatever words were
+         135 |                     // supplied. EIP-2537 encodes G1 identity as four zero
+         136 |                     // words: x_hi = x_lo = y_hi = y_lo = 0.
    714   137 |                     mstore(dst, 0)
@@ deployed 719-730 / current 142-146 @@
    719   142 |                 if iszero(is_id) {
-   720       |                     // x occupies coord_words packed public-input words; y
-   721       |                     // starts immediately after x.
-   722       |                     let limbs_per_word := 4
-   723       |                     let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
-   724       |                     // Only x may carry the identity flag. y must decode as a
-   725       |                     // normal shifted coordinate.
-   726       |                     let x_ok, x_hi, x_lo, x_is_id := load_acc_coord(src, 1, bits, n, base, limbs_per_word)
-   727       |                     let y_ok, y_hi, y_lo, y_id := load_acc_coord(
+         143 |                     let x_ok, x_hi, x_lo := load_acc_coord(src, bits, n, base, limbs_per_word)
+         144 |                     let y_ok, y_hi, y_lo := load_acc_coord(
    728   145 |                         add(src, mul(coord_words, 0x20)),
-   729       |                         0,
    730   146 |                         bits,
@@ deployed 734-757 / current 150-156 @@
    734   150 |                     )
-   735       |                     // y_id is always zero because allow_id was false, but the
-   736       |                     // tuple shape is shared with x decoding.
-   737       |                     pop(y_id)
-   738       |                     ok := and(x_ok, y_ok)
-   739       |                     is_id := x_is_id
-   740       | 
-   741       |                     if is_id {
-   742       |                         // If x carried the identity flag, both decoded
-   743       |                         // coordinates must be zero after shifting. Any other y
-   744       |                         // value would be a malformed infinity encoding.
-   745       |                         ok := and(ok, iszero(or(or(x_hi, x_lo), or(y_hi, y_lo))))
-   746       |                         mstore(dst, 0)
-   747       |                         mstore(add(dst, 0x20), 0)
-   748       |                         mstore(add(dst, 0x40), 0)
-   749       |                         mstore(add(dst, 0x60), 0)
-   750       |                     }
-   751       |                     if iszero(is_id) {
+         151 |                     ok := and(ok, and(x_ok, y_ok))
    752   152 |                         // The coordinate codec maps encoded p-1 to decoded
-   753       |                         // zero. EIP-2537 reserves affine (0,0) for the point
-   754       |                         // at infinity, so a decoded infinity is only valid
-   755       |                         // when the canonical accumulator identity encoding
-   756       |                         // was used above.
+         153 |                     // zero. EIP-2537 reserves affine (0,0) for the point at
+         154 |                     // infinity, so a decoded infinity is only valid when the
+         155 |                     // identity flag word is set.
    757   156 |                         let decoded_zero := iszero(or(or(x_hi, x_lo), or(y_hi, y_lo)))
@@ deployed 766-768 / current 165-166 @@
    766   165 |                 }
-   767       |             }
    768   166 |             // Validate and prepare the public accumulator equation before the
@@ deployed 779-781 / current 177-189 @@
    779   177 |             //      randomized batching in FinalPairing.yul.
-   780       |             function validate_public_accumulator(success, r) -> out {
+         178 |             // `r` is consumed only by the canonicality guards in the
+         179 |             // carried-scalar and fixed-base-tail arms; renders whose
+         180 |             // accumulator layout has neither (e.g. point_pair with no tail)
+         181 |             // legally leave it unused.
+         182 |             // MF-4: `precompile_failed` separates a G1MSM staticcall that
+         183 |             // could not run (chain/gas fault) from a public-input point this
+         184 |             // verifier decoded and rejected (bad packing, out-of-field
+         185 |             // coordinate, non-canonical identity encoding, or a point the
+         186 |             // precompile found off-curve/out-of-subgroup). Both fail closed at
+         187 |             // the call site; only the second is a BadPointEncoding.
+         188 |             function validate_public_accumulator(success, r) -> out, precompile_failed {
    781   189 |                 out := success
@@ deployed 788-789 / current 196-200 @@
    788   196 |                 let coord_words := div(add(n, sub(limbs_per_word, 1)), limbs_per_word)
+         197 |                 // One public point is its x and y coordinate words followed
+         198 |                 // by the identity flag word.
+         199 |                 let point_words := add(mul(2, coord_words), 1)
    789   200 |                 // acc_offset is generated from the VK/protocol shape and
@@ deployed 792-799 / current 203-210 @@
    792   203 | 
-   793       |                 // LHS layout: point limbs (x,y), then either an explicit
-   794       |                 // scalar word or an implicit unit scalar for already-collapsed
-   795       |                 // point-pair public inputs.
+         204 |                 // LHS layout: point limbs (x,y), identity flag, then either an
+         205 |                 // explicit scalar word or an implicit unit scalar for
+         206 |                 // already-collapsed point-pair public inputs.
    796   207 |                 // The scalar pointer is computed unconditionally; the rendered
    797   208 |                 // branch below decides whether to read it or use scalar 1.
-   798       |                 let lhs_scalar_ptr := add(acc_instance_ptr, mul(mul(2, coord_words), 0x20))
+         209 |                 let lhs_scalar_ptr := add(acc_instance_ptr, mul(point_words, 0x20))
    799   210 |                 let lhs_ok, lhs_is_id := load_acc_point(ACC_LHS_MPTR, acc_instance_ptr, bits, n, limb_base)
@@ deployed 821-824 / current 232-236 @@
    821   232 |                         // is also a curve/subgroup validation round-trip.
-   822       |                         out := staticcall(gas(), 0x0c, acc_scratch, 0xa0, ACC_LHS_MPTR, 0x80)
+         233 |                         out := staticcall(G1MSM_GAS_1PAIR, 0x0c, acc_scratch, 0xa0, ACC_LHS_MPTR, 0x80)
    823   234 |                         out := and(out, eq(returndatasize(), 0x80))
+         235 |                         precompile_failed := iszero(out)
    824   236 |                     }
@@ deployed 831-834 / current 243-247 @@
    831   243 |                 // RHS scalar, when present, immediately follows the RHS point
-   832       |                 // limbs. The fixed-base scalar tail starts after it.
-   833       |                 let rhs_scalar_ptr := add(rhs_instance_ptr, mul(mul(2, coord_words), 0x20))
+         244 |                 // limbs and identity flag. The fixed-base scalar tail starts
+         245 |                 // after it.
+         246 |                 let rhs_scalar_ptr := add(rhs_instance_ptr, mul(point_words, 0x20))
    834   247 |                 let rhs_ok, rhs_is_id := load_acc_point(ACC_RHS_MPTR, rhs_instance_ptr, bits, n, limb_base)
@@ deployed 866-869 / current 279-285 @@
    866   279 |                         // base embedded by codegen and the carried RHS point.
+         280 |                         // ACC_RHS_MSM_GAS is the compile-time worst case
+         281 |                         // (every tail scalar nonzero); acc_msm_len can only
+         282 |                         // select a same-size-or-smaller MSM at runtime.
    867   283 |                         out := staticcall(
-   868       |                             gas(),
+         284 |                             ACC_RHS_MSM_GAS,
    869   285 |                             0x0c,
@@ deployed 875-876 / current 291-293 @@
    875   291 |                         out := and(out, eq(returndatasize(), 0x80))
+         292 |                         precompile_failed := iszero(out)
    876   293 |                     }
```

## VkLoading

Deployed lines 889-975 (87 lines after trimming blank edges); current render 93 lines, 5821 UTF-8 bytes; raw `occ = 0`, raw `includeBoundary = false`.

```diff
@@ deployed 917-919 / current 31-33 @@
    917    31 |                     eq(extcodehash(vk), EXPECTED_VK_CODEHASH_WORD)
-   918       |                 )) { revert(0, 0) }
+          32 |                 )) { fail(ERR_VK_MISMATCH) }
    919    33 |                 // Runtime byte 0 is INVALID so direct calls cannot execute the
@@ deployed 934-936 / current 48-50 @@
    934    48 |                 success := and(success, eq(mload(NUM_ACC_LIMB_BITS_MPTR), 56))
-   935       |                 if iszero(success) { revert(0, 0) }
+          49 |                 if iszero(success) { fail(ERR_VK_MISMATCH) }
    936    50 |                 //
@@ deployed 958-960 / current 72-74 @@
    958    72 |                 // is not exactly the generated one.
-   959       |                 if iszero(success) { revert(0, 0) }
+          73 |                 if iszero(success) { fail(ERR_BAD_CALLDATA_SHAPE) }
    960    74 |             }
@@ deployed 973-975 / current 87-95 @@
    973    87 |             // where the verifier converts failure to a revert.
-   974       |             success := validate_public_accumulator(success, r)
-   975       |             if iszero(success) { revert(0, 0) }
+          88 |             let acc_precompile_failed := 0
+          89 |             success, acc_precompile_failed := validate_public_accumulator(success, r)
+          90 |             if iszero(success) {
+          91 |                 // MF-4: a G1MSM that could not run at all is a chain fault,
+          92 |                 // not a malformed accumulator point.
+          93 |                 if acc_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
+          94 |                 fail(ERR_BAD_POINT_ENCODING)
+          95 |             }
```

## TranscriptProofParser

Deployed lines 977-1310 (334 lines after trimming blank edges); current render 334 lines, 17968 UTF-8 bytes; raw `occ = 0`, raw `includeBoundary = false`.

```diff
@@ deployed 1043-1045 / current 67-69 @@
   1043    67 |                 }
-  1044       |                 if iszero(success) { revert(0, 0) }
+          68 |                 if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }
   1045    69 |             }
@@ deployed 1226-1228 / current 250-252 @@
   1226   250 |                     // reconstruction.
-  1227       |                     if iszero(lt(eval, r)) { revert(0, 0) }
+         251 |                     if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }
   1228   252 |                     // Spill for quotient numerator and PCS codegen.
@@ deployed 1279-1281 / current 303-305 @@
   1279   303 |                 // Canonical Fr check before transcript absorption.
-  1280       |                 if iszero(lt(eval, r)) { revert(0, 0) }
+         304 |                 if iszero(lt(eval, r)) { fail(ERR_NON_CANONICAL_SCALAR) }
   1281   305 |                 buf_len := common_word(buf_len, eval)
@@ deployed 1305-1307 / current 329-331 @@
   1305   329 |             // some section was under-read or over-read.
-  1306       |             if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { revert(0, 0) }
+         330 |             if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }
   1307   331 | 
@@ deployed 1309-1310 / current 333-334 @@
   1309   333 |             // instance reads. G1/proof scalar helpers revert immediately.
-  1310       |             if iszero(success) { revert(0, 0) }
+         334 |             if iszero(success) { fail(ERR_NON_CANONICAL_SCALAR) }
```

## Lagrange

Deployed lines 1312-1391 (80 lines after trimming blank edges); current render 90 lines, 4745 UTF-8 bytes; raw `occ = 0`, raw `includeBoundary = false`.

```diff
@@ deployed 1314-1315 / current 3-8 @@
   1314     3 |             // ===============================================================
+           4 |             // MF-4: hoisted so the section boundary below can tell a failed
+           5 |             // modexp (chain fault) from a rejected denominator (x landed on a
+           6 |             // domain point) instead of reporting both as PrecompileFailed.
+           7 |             let lagrange_precompile_failed := 0
   1315     8 |             {
@@ deployed 1329-1331 / current 22-24 @@
   1329    22 |                 // modexp call.
-  1330       |                 let mptr := X_N_MPTR
+          23 |                 let mptr := LAGRANGE_DENOMS_MPTR
   1331    24 |                 let mptr_end := add(mptr, 0x03a0)
@@ deployed 1339-1341 / current 32-34 @@
   1339    32 |                 mstore(mptr_end, x_n_minus_1)
-  1340       |                 success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)
+          33 |                 success, lagrange_precompile_failed := batch_invert(success, LAGRANGE_DENOMS_MPTR, add(mptr_end, 0x20), BATCH_INV_SCRATCH_MPTR, r)
   1341    34 | 
@@ deployed 1343-1345 / current 36-38 @@
   1343    36 |                 // L_i(x) = (x^n - 1) * n^-1 * omega_i / (x - omega_i).
-  1344       |                 mptr := X_N_MPTR
+          37 |                 mptr := LAGRANGE_DENOMS_MPTR
   1345    38 |                 let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
@@ deployed 1354-1358 / current 47-51 @@
   1354    47 |                 // used by the midnight-proofs blinding identity.
-  1355       |                 let l_blind := mload(add(X_N_MPTR, 0x20))
-  1356       |                 let l_i_cptr := add(X_N_MPTR, 0x40)
-  1357       |                 for { let l_i_cptr_end := add(X_N_MPTR, 0x0140) }
+          48 |                 let l_blind := mload(add(LAGRANGE_DENOMS_MPTR, 0x20))
+          49 |                 let l_i_cptr := add(LAGRANGE_DENOMS_MPTR, 0x40)
+          50 |                 for { let l_i_cptr_end := add(LAGRANGE_DENOMS_MPTR, 0x0140) }
   1358    51 |                     lt(l_i_cptr, l_i_cptr_end)
@@ deployed 1379-1382 / current 72-75 @@
   1379    72 |                 let x_n_minus_1_inv := mload(mptr_end)
-  1380       |                 let l_last := mload(X_N_MPTR)
-  1381       |                 let l_0 := mload(add(X_N_MPTR, 0x0140))
+          73 |                 let l_last := mload(LAGRANGE_DENOMS_MPTR)
+          74 |                 let l_0 := mload(add(LAGRANGE_DENOMS_MPTR, 0x0140))
   1382    75 | 
@@ deployed 1390-1391 / current 83-90 @@
   1390    83 | 
-  1391       |             if iszero(success) { revert(0, 0) }
+          84 |             if iszero(success) {
+          85 |                 // A zero or non-canonical denominator is a rejected input,
+          86 |                 // not a broken chain: the only way to reach it is a squeezed
+          87 |                 // x that coincides with a domain point (probability ~n/r).
+          88 |                 if lagrange_precompile_failed { fail(ERR_PRECOMPILE_FAILED) }
+          89 |                 fail(ERR_PROOF_REJECTED)
+          90 |             }
```

## QuotientAndLinearization (linearization tail)

Deployed lines 2822-2861 (40 lines after trimming blank edges); current render 40 lines, 1901 UTF-8 bytes; raw `occ = 1`, raw `includeBoundary = false`.

```diff
(no content differences after leading-whitespace normalization)
```

## FinalPairing

Deployed lines 3491-3563 (73 lines after trimming blank edges); current render 76 lines, 4221 UTF-8 bytes; raw `occ = 0`, raw `includeBoundary = false`.

```diff
@@ deployed 3506-3513 / current 16-26 @@
   3506    16 | 
-  3507       |                 // Domain || KZG rhs/lhs || accumulator rhs/lhs.
+          17 |                 // Domain || vk_digest || KZG rhs/lhs || accumulator rhs/lhs.
+          18 |                 // vk_digest makes alpha's binding to the verifying key local
+          19 |                 // instead of transitive-through-the-points (audit I-7).
   3508    20 |                 mstore(batch_ptr, 0x70616972696e672d62617463682d6163632d6b7a670000000000000000)
-  3509       |                 mcopy(add(batch_ptr, 0x20),  PAIRING_RHS_MPTR, 0x80)
-  3510       |                 mcopy(add(batch_ptr, 0xa0),  PAIRING_LHS_MPTR, 0x80)
-  3511       |                 mcopy(add(batch_ptr, 0x0120), ACC_RHS_MPTR,     0x80)
-  3512       |                 mcopy(add(batch_ptr, 0x01a0), ACC_LHS_MPTR,     0x80)
+          21 |                 mstore(add(batch_ptr, 0x20), mload(VK_DIGEST_MPTR))
+          22 |                 mcopy(add(batch_ptr, 0x40),  PAIRING_RHS_MPTR, 0x80)
+          23 |                 mcopy(add(batch_ptr, 0xc0),  PAIRING_LHS_MPTR, 0x80)
+          24 |                 mcopy(add(batch_ptr, 0x0140), ACC_RHS_MPTR,     0x80)
+          25 |                 mcopy(add(batch_ptr, 0x01c0), ACC_LHS_MPTR,     0x80)
   3513    26 |                 // alpha is Fiat-Shamir over the fully materialized pairing
@@ deployed 3515-3517 / current 28-30 @@
   3515    28 |                 // accumulator equation cannot be accidentally dropped.
-  3516       |                 let acc_pair_alpha := mod(keccak256(batch_ptr, 0x0220), r)
+          29 |                 let acc_pair_alpha := mod(keccak256(batch_ptr, 0x0240), r)
   3517    30 |                 if iszero(acc_pair_alpha) { acc_pair_alpha := 1 }
@@ deployed 3524-3526 / current 37-39 @@
   3524    37 |                 if success {
-  3525       |                     success := staticcall(gas(), 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
+          38 |                     success := staticcall(G1MSM_GAS_1PAIR, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
   3526    39 |                     success := and(success, eq(returndatasize(), 0x80))
@@ deployed 3529-3531 / current 42-44 @@
   3529    42 |                 if success {
-  3530       |                     success := staticcall(gas(), 0x0b, batch_ptr, 0x0100, PAIRING_RHS_MPTR, 0x80)
+          43 |                     success := staticcall(G1ADD_GAS, 0x0b, batch_ptr, 0x0100, PAIRING_RHS_MPTR, 0x80)
   3531    44 |                     success := and(success, eq(returndatasize(), 0x80))
@@ deployed 3538-3540 / current 51-53 @@
   3538    51 |                 if success {
-  3539       |                     success := staticcall(gas(), 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
+          52 |                     success := staticcall(G1MSM_GAS_1PAIR, 0x0c, batch_ptr, 0xa0, batch_ptr, 0x80)
   3540    53 |                     success := and(success, eq(returndatasize(), 0x80))
@@ deployed 3543-3545 / current 56-58 @@
   3543    56 |                 if success {
-  3544       |                     success := staticcall(gas(), 0x0b, batch_ptr, 0x0100, PAIRING_LHS_MPTR, 0x80)
+          57 |                     success := staticcall(G1ADD_GAS, 0x0b, batch_ptr, 0x0100, PAIRING_LHS_MPTR, 0x80)
   3545    58 |                     success := and(success, eq(returndatasize(), 0x80))
@@ deployed 3561-3563 / current 74-76 @@
   3561    74 |             // pairing argument order. Pass them swapped to ec_pairing.
-  3562       |             if iszero(success) { revert(0, 0) }
+          75 |             if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
   3563    76 |             success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)
```

