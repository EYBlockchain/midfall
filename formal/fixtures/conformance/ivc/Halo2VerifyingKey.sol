// SPDX-License-Identifier: CC0-1.0

// Pinned to match the verifier, so both halves of a deployment are provably
// built by one toolchain. (This contract's runtime is pure returned data, so
// its codehash is compiler-independent -- the pin is for the pair, not for it.)
pragma solidity 0.8.30;

/// @title Halo2 BLS12-381 verifying-key payload.
/// @notice Contract whose deployed runtime is `INVALID || generated verifier-key payload`.
/// @dev Byte 0 is an unconditional INVALID opcode so direct calls cannot execute payload bytes as code. The linked verifier pins the full runtime by length/codehash and copies the payload starting at byte 1.
/// @dev The layout follows the verifier inputs derived from
/// `midfall/proofs/src/plonk/mod.rs::VerifyingKey` and the transcript
/// `vk.hash_into` behavior used by `midfall/proofs/src/plonk/verifier.rs`.
///
/// Layout (in 32-byte words, big-endian). The header slots are generated from
/// Rust's `VkHeaderLayout`; the byte offsets are absolute from the start of the
/// VK payload, not from byte 0 of the runtime. Runtime byte 0 is the INVALID
/// prefix; the verifier loads the payload via
/// `extcodecopy(vk, VK_MPTR, 0x01, vk_payload_len)` and then references each
/// slot by `VK_MPTR + i`.
///
///   word  0  : vk_digest                    (Fq, transcript_repr of the CS)
///   word  1  : num_instances
///   word  2  : k                            (log2 of the domain size)
///   word  3  : n_inv                        (1/n in Fr)
///   word  4  : omega                        (n-th primitive root of unity)
///   word  5  : omega_inv
///   word  6  : omega_inv_to_l               (omega_inv ^ |rotation_last|)
///   word  7  : has_accumulator              (0 or 1)
///   word  8  : acc_offset                   (instance index of the accumulator)
///   word  9  : num_acc_limbs
///   word 10  : num_acc_limb_bits
///   word 11..14 : G1_BASE                   (4 words, EIP-2537 padded)
///   word 15..22 : G2_BASE                   (8 words, EIP-2537 padded)
///   word 23..30 : NEG_S_G2_BASE             (8 words, EIP-2537 padded)
///   word 31..30 + Q_PAYLOAD      : quotient VM constants + packed bytecode
///   word 31 + Q_PAYLOAD ..       : fixed_comms (4 words each)
///   word 31 + Q_PAYLOAD + 4*N_FIXED ..
///                                : permutation_comms (4 words each)
///
/// Notes:
/// - `extcodehash` of this contract is pinned by the linked verifier via
///   `EXPECTED_VK_CODEHASH`, so any byte tweak is detected at deploy time.
/// - The quotient identity interpreter's static program is stored in this
///   pinned VK runtime. The verifier reads it from memory after `extcodecopy`,
///   avoiding verifier-side PUSH32/mstore immediates while keeping the program
///   covered by `EXPECTED_VK_CODEHASH`.
/// - The midnight-proofs migration bakes the per-lookup chunk counts, trashcan
///   structure, and `num_simple_selectors` into the generated verifier code.
contract Halo2VerifyingKey {
    /// @notice Deploy the verifying-key payload as this contract's runtime bytecode.
    /// @dev The constructor writes an INVALID byte followed by generated words into memory and returns that prefixed runtime.
    /// @dev The transient construction buffer starts at `0x80`, preserving Solidity's reserved memory words.
    constructor() {
        assembly {
            // Runtime layout:
            //   byte 0      : INVALID, so the payload cannot be executed
            //   byte 1..end : generated VK payload copied by Halo2Verifier
            //
            // `runtime` includes the INVALID prefix; `payload` points to word
            // zero of the verifier-key data described in the contract NatSpec.
            let runtime := 0x80
            let payload := add(runtime, 0x01)
            mstore8(runtime, 0xfe)
            // Header, base-point, and quotient-program words generated from
            // VkPayloadLayout. The inline names on each mstore identify the
            // exact slot in the rendered source.
            mstore(add(payload, 0x0000), 0x39e6dda9e589ea59d362b137fbdd4ee60d639c67def2489c975514e7a68252d3) // vk_digest
            mstore(add(payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000010) // num_instances
            mstore(add(payload, 0x0040), 0x0000000000000000000000000000000000000000000000000000000000000014) // k
            mstore(add(payload, 0x0060), 0x73eda0144f284aae5b6554d46c21576b363d4ec725be2bff1a400fff00001001) // n_inv
            mstore(add(payload, 0x0080), 0x03e1c54bcb947035a57a6e07cb98de4a2f69e02d265e09d9fece7e0e39898d4b) // omega
            mstore(add(payload, 0x00a0), 0x6c39442eade0092768ac033fa6f608750624a1bb17dbc026ef97c3573a28fc8c) // omega_inv
            mstore(add(payload, 0x00c0), 0x2a0ccbaa0613f093f2bb6e97859513f0b613d8587eaa92db9e5604b8d6b68d45) // omega_inv_to_l
            mstore(add(payload, 0x00e0), 0x0000000000000000000000000000000000000000000000000000000000000001) // has_accumulator
            mstore(add(payload, 0x0100), 0x0000000000000000000000000000000000000000000000000000000000000004) // acc_offset
            mstore(add(payload, 0x0120), 0x0000000000000000000000000000000000000000000000000000000000000007) // num_acc_limbs
            mstore(add(payload, 0x0140), 0x0000000000000000000000000000000000000000000000000000000000000038) // num_acc_limb_bits
            mstore(add(payload, 0x0160), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f) // g1_x_hi
            mstore(add(payload, 0x0180), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb) // g1_x_lo
            mstore(add(payload, 0x01a0), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4) // g1_y_hi
            mstore(add(payload, 0x01c0), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1) // g1_y_lo
            mstore(add(payload, 0x01e0), 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051) // g2_x_c0_hi
            mstore(add(payload, 0x0200), 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8) // g2_x_c0_lo
            mstore(add(payload, 0x0220), 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65) // g2_x_c1_hi
            mstore(add(payload, 0x0240), 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e) // g2_x_c1_lo
            mstore(add(payload, 0x0260), 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a) // g2_y_c0_hi
            mstore(add(payload, 0x0280), 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801) // g2_y_c0_lo
            mstore(add(payload, 0x02a0), 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99) // g2_y_c1_hi
            mstore(add(payload, 0x02c0), 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be) // g2_y_c1_lo
            mstore(add(payload, 0x02e0), 0x0000000000000000000000000000000007acb569b3187c0fd1993980aa52a6e9) // neg_s_g2_x_c0_hi
            mstore(add(payload, 0x0300), 0xe2080b9697fab96abd5c5f1c3b988256f2d99366f1bbccf13cf0e20702fee18c) // neg_s_g2_x_c0_lo
            mstore(add(payload, 0x0320), 0x0000000000000000000000000000000004bbe1a24fcc4f988c6ef268d0c1160e) // neg_s_g2_x_c1_hi
            mstore(add(payload, 0x0340), 0xac0a0c4f53d80bd74f3d2e4667be27408625a83825354e27c70859883102eb43) // neg_s_g2_x_c1_lo
            mstore(add(payload, 0x0360), 0x00000000000000000000000000000000091f5fc856da557cdb852412d3fd2cef) // neg_s_g2_y_c0_hi
            mstore(add(payload, 0x0380), 0x9034c9a66ce38bf356c49f6a012109440035923a9cd6c71ca0c8efa5b6badf52) // neg_s_g2_y_c0_lo
            mstore(add(payload, 0x03a0), 0x000000000000000000000000000000000af8fa5434d3fdd8c90fe8e532246c49) // neg_s_g2_y_c1_hi
            mstore(add(payload, 0x03c0), 0x9926d8d728ccbb4ac40381158e8da573b4895782bfdb788c8ff40ba22032eab3) // neg_s_g2_y_c1_lo
            mstore(add(payload, 0x03e0), 0x0000000000000000000000000000000000000000000000000000000000000001) // quotient_const
            mstore(add(payload, 0x0400), 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140) // quotient_const
            mstore(add(payload, 0x0420), 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a) // quotient_const
            mstore(add(payload, 0x0440), 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db) // quotient_const
            mstore(add(payload, 0x0460), 0x00bbe1fbe9ef1e2d62490b03a82bf9ef10f5e9b2323033669cf6c50481f63e05) // quotient_const
            mstore(add(payload, 0x0480), 0x0000000000000000000000000000000000000000000000000100000000000000) // quotient_const
            mstore(add(payload, 0x04a0), 0x0000000000000000000000000000000000010000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x04c0), 0x0000000000000000000000000000000000000000000000000000000400000000) // quotient_const
            mstore(add(payload, 0x04e0), 0x0000000000000000000000000000000000000000040000000000000000000000) // quotient_const
            mstore(add(payload, 0x0500), 0x0000000000000000000000000000000000000000000000000000000000001000) // quotient_const
            mstore(add(payload, 0x0520), 0x0000000000000000000000000000000000000000000000100000000000000000) // quotient_const
            mstore(add(payload, 0x0540), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000) // quotient_const
            mstore(add(payload, 0x0560), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefeffffff00000001) // quotient_const
            mstore(add(payload, 0x0580), 0x73eda753299d7d483339d80809a1d80553bca402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x05a0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffb00000001) // quotient_const
            mstore(add(payload, 0x05c0), 0x73eda753299d7d483339d80809a1d80553bda402fbfe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x05e0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffefffff001) // quotient_const
            mstore(add(payload, 0x0600), 0x73eda753299d7d483339d80809a1d80553bda402fffe5beeffffffff00000001) // quotient_const
            mstore(add(payload, 0x0620), 0x00000000000000000000000000000010ff0726c5de281020ad8016cf6f691213) // quotient_const
            mstore(add(payload, 0x0640), 0x0000000000000000000000000000002c64068790f917282347187665718b04c8) // quotient_const
            mstore(add(payload, 0x0660), 0x00000000000000000000000000000027241bb5338dce8a77499428839473bf3a) // quotient_const
            mstore(add(payload, 0x0680), 0x0000000000000000000000000000002b7c4a26a1c7ae6fc4b499d04e4a463c4b) // quotient_const
            mstore(add(payload, 0x06a0), 0x000000000000000000000000000000274bc40fcf526be95333a8c22c79465298) // quotient_const
            mstore(add(payload, 0x06c0), 0x0000000000000000000000000000002a5ee6db49930276e2939d1c43ac82f744) // quotient_const
            mstore(add(payload, 0x06e0), 0x73eda753299d7d483339d80809a1d7edd77e26c51c38afb5debf8afa00c15cc3) // quotient_const
            mstore(add(payload, 0x0700), 0x73eda753299d7d483339d80809a1d7c553bda402fffe5bfeffffffff00000002) // quotient_const
            mstore(add(payload, 0x0720), 0x73eda753299d7d483339d80809a1d80553bda402fffe53ebc627fffef6280001) // quotient_const
            mstore(add(payload, 0x0740), 0x0000000000000000000001000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0760), 0x0000000100000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0780), 0x6bc66e553973f396854f5626172ba135587d41e37a68209402355093fdcaaf6c) // quotient_const
            mstore(add(payload, 0x07a0), 0x63f31e3f446953960c9d6964474300df43ab29179970f642a28e39d6c883c74b) // quotient_const
            mstore(add(payload, 0x07c0), 0x73eda753299d7d483339d70809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x07e0), 0x73eda752299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x0800), 0x082738fdf02989b1adea81e1f27636cffb40621f85963b6afdcaaf6b02355095) // quotient_const
            mstore(add(payload, 0x0820), 0x0ffa8913e53429b2269c6ea3c25ed72610127aeb668d65bc5d71c628377c38b6) // quotient_const
            mstore(add(payload, 0x0840), 0x01ec1c0519185dfe86132d479c76d0786e1e037d0b05ca47648a1c5d29492c9b) // quotient_const
            mstore(add(payload, 0x0860), 0x1e179025ca2470882b34e63940ccbd7ad9090bf414d43b696e093b5a8782528f) // quotient_const
            mstore(add(payload, 0x0880), 0x4298bfee9a84c8ef8e83702075cb1abeb576f146636342e3db9ea6b0a4adf29d) // quotient_const
            mstore(add(payload, 0x08a0), 0x3c83b078e9abed278d042acc8f3bd21e228716f04be96af8025da860e2d1bba9) // quotient_const
            mstore(add(payload, 0x08c0), 0x427868260f487d1ef07edaadf37f5dbe705bd1318290f2577ae756b009c24f11) // quotient_const
            mstore(add(payload, 0x08e0), 0x03020e6a35e595abd22838beeadc45cfcb0545d85ca0ab2c59d44c203fac84a7) // quotient_const
            mstore(add(payload, 0x0900), 0x000000000000000000000000000000000000000000000000d201000000010000) // quotient_const
            mstore(add(payload, 0x0920), 0x0000000100001b7c3f8d3fe3c5b448f1bdeb2ae34698b72d6ce966fc208c05ed) // quotient_const
            mstore(add(payload, 0x0940), 0x73eda753299d7d483339d80809a1d7fd4057a4c12f26d1c1778e3360a6820001) // quotient_const
            mstore(add(payload, 0x0960), 0x057797fa7060856f215654ff11006fe0acf6a437e9477bf6f782dfac86f2cf75) // quotient_const
            mstore(add(payload, 0x0980), 0x0000000000000000000000000000000000000000000000000000000000000002) // quotient_const
            mstore(add(payload, 0x09a0), 0x0000000000000000000000000000000000000000000000000200000000000000) // quotient_const
            mstore(add(payload, 0x09c0), 0x0000000000000000000000000000000000020000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x09e0), 0x73eda753299d7d483339d80809a1d7e13511a4044eaa5bff4600ffff00005556) // quotient_const
            mstore(add(payload, 0x0a00), 0x73eda753299d7d483339d80809a1d7c553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x0a20), 0x73eda753299d7d483339d80809a1d7d340dd972492de594de627fffefcb80349) // quotient_const
            mstore(add(payload, 0x0a40), 0x73eda753299d7d483339d80809a1d7dbdc391ab4d8ac003bbd48021b82456c9b) // quotient_const
            mstore(add(payload, 0x0a60), 0x73eda753299d7d483339d80809a1d7d1448ee5caf5eefcffbc9fabc57759e23f) // quotient_const
            mstore(add(payload, 0x0a80), 0x73eda753299d7d483339d80809a1d80418c74cc18bb28443d3978d1fd47ffce1) // quotient_const
            mstore(add(payload, 0x0aa0), 0x0000000000000000000000000000006425c019bcda40056233b00000068ff970) // quotient_const
            mstore(add(payload, 0x0ac0), 0x00000000000000000000000000000052ef09129c4ea4b786856ffbc6fb7526cc) // quotient_const
            mstore(add(payload, 0x0ae0), 0x73eda753299d7d483339d80809a1d7d89a085d30fc8a7106a170ac2377c34ab9) // quotient_const
            mstore(add(payload, 0x0b00), 0x73eda753299d7d483339d80809a1d7f8ce65bb936f2d836012914aca65f077e1) // quotient_const
            mstore(add(payload, 0x0b20), 0x000000000000000000000000000000681e5d7c70141ebdfe86c0a873114c3b84) // quotient_const
            mstore(add(payload, 0x0b40), 0x000000000000000000000000000000297784894e27525bc342b7fde37dba9366) // quotient_const
            mstore(add(payload, 0x0b60), 0x0000000000000000000000000000000275ecae82e897af7658d0e5be57000640) // quotient_const
            mstore(add(payload, 0x0b80), 0x000000000000000000000000000000013af65741744bd7bb2c6872df2b800320) // quotient_const
            mstore(add(payload, 0x0ba0), 0x00000000000000000000000000000059736a8da406e7d5f0bd1ea7b710796a90) // quotient_const
            mstore(add(payload, 0x0bc0), 0x0000000000000000000000000000000c8557e86f90d0d89eed6eb5349a0f8820) // quotient_const
            mstore(add(payload, 0x0be0), 0x0453ae02a5f228d8f956b5eab4fc92bbeea5eb26b6ae4b42b4fdfcfdf026aa22) // quotient_const
            mstore(add(payload, 0x0c00), 0x0000000000000000000000000000000000000000000000000000000800000000) // quotient_const
            mstore(add(payload, 0x0c20), 0x0000000000000000000000000000000000000000080000000000000000000000) // quotient_const
            mstore(add(payload, 0x0c40), 0x0000000000000000000000000000000000000000000000000000000000002000) // quotient_const
            mstore(add(payload, 0x0c60), 0x0000000000000000000000000000000000000000000000200000000000000000) // quotient_const
            mstore(add(payload, 0x0c80), 0x73eda753299d7d483339d80809a1d7f454b67d3d21d64bde527fe92f9096edee) // quotient_const
            mstore(add(payload, 0x0ca0), 0x73eda753299d7d483339d80809a1d7d8efb71c7206e733dbb8e789998e74fb39) // quotient_const
            mstore(add(payload, 0x0cc0), 0x73eda753299d7d483339d80809a1d7de2fa1eecf722fd187b66bd77b6b8c40c7) // quotient_const
            mstore(add(payload, 0x0ce0), 0x73eda753299d7d483339d80809a1d7d9d7737d61384fec3a4b662fb0b5b9c3b6) // quotient_const
            mstore(add(payload, 0x0d00), 0x73eda753299d7d483339d80809a1d7de07f99433ad9272abcc573dd286b9ad69) // quotient_const
            mstore(add(payload, 0x0d20), 0x73eda753299d7d483339d80809a1d7daf4d6c8b96cfbe51c6c62e3bb537d08bd) // quotient_const
            mstore(add(payload, 0x0d40), 0x00000000000000000000000000000021fe0e4d8bbc5020415b002d9eded22426) // quotient_const
            mstore(add(payload, 0x0d60), 0x00000000000000000000000000000058c80d0f21f22e50468e30eccae3160990) // quotient_const
            mstore(add(payload, 0x0d80), 0x0000000000000000000000000000004e48376a671b9d14ee9328510728e77e74) // quotient_const
            mstore(add(payload, 0x0da0), 0x00000000000000000000000000000056f8944d438f5cdf896933a09c948c7896) // quotient_const
            mstore(add(payload, 0x0dc0), 0x0000000000000000000000000000004e97881f9ea4d7d2a667518458f28ca530) // quotient_const
            mstore(add(payload, 0x0de0), 0x73eda753299d7d4833351088b4af7508df8b737010b26e15294bfcbb9194fffd) // quotient_const
            mstore(add(payload, 0x0e00), 0x0000000000000000000002000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0e20), 0x0000000200000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0e40), 0x639f3557494a69e4d764d44424b56a655d3cdfc3f4d1e529046aa128fb955ed7) // quotient_const
            mstore(add(payload, 0x0e60), 0x53f8952b5f3529e3e600fac084e429b93398ae2c32e39086451c73ae91078e95) // quotient_const
            mstore(add(payload, 0x0e80), 0x72018b4e10851f49ad26aac06d2b078ce59fa085f4f891b79b75e3a1d6b6d366) // quotient_const
            mstore(add(payload, 0x0ea0), 0x55d6172d5f790cc00804f1cec8d51a8a7ab4980eeb2a209591f6c4a4787dad72) // quotient_const
            mstore(add(payload, 0x0ec0), 0x3154e7648f18b458a4b667e793d6bd469e46b2bc9c9b191b2461594e5b520d64) // quotient_const
            mstore(add(payload, 0x0ee0), 0x3769f6da3ff19020a635ad3b7a6605e731368d12b414f106fda2579e1d2e4458) // quotient_const
            mstore(add(payload, 0x0f00), 0x31753f2d1a55002942bafd5a16227a46e361d2d17d6d69a78518a94ef63db0f0) // quotient_const
            mstore(add(payload, 0x0f20), 0x70eb98e8f3b7e79c61119f491ec5923588b85e2aa35db0d2a62bb3dec0537b5a) // quotient_const
            mstore(add(payload, 0x0f40), 0x03d8380a3230bbfd0c265a8f38eda0f0dc3c06fa160b948ec91438ba52925936) // quotient_const
            mstore(add(payload, 0x0f60), 0x3c2f204b9448e1105669cc7281997af5b21217e829a876d2dc1276b50f04a51e) // quotient_const
            mstore(add(payload, 0x0f80), 0x1143d88a0b6c1496e9cd0838e1f45d7817303e89c6c829c8b73d4d62495be539) // quotient_const
            mstore(add(payload, 0x0fa0), 0x0519b99ea9ba5d06e6ce7d9114d5cc36f15089dd97d479f104bb50c2c5a37751) // quotient_const
            mstore(add(payload, 0x0fc0), 0x110328f8f4f37cf5adc3dd53dd5ce3778cf9fe60052388aff5cead6113849e21) // quotient_const
            mstore(add(payload, 0x0fe0), 0x057797fa7060856f215655ff11006fee9a1697597c277945ddaadfac83aad2c0) // quotient_const
            mstore(add(payload, 0x1000), 0x0000000000000000000000000000003212e00cde6d2002b119d800000347fcb8) // quotient_const
            mstore(add(payload, 0x1020), 0x000000000000000000000000000000340f2ebe380a0f5eff4360543988a61dc2) // quotient_const
            mstore(add(payload, 0x1040), 0x0000000000000000000000000000002cb9b546d20373eaf85e8f53db883cb548) // quotient_const
            mstore(add(payload, 0x1060), 0x0453ae02a5f228d8f956b6eab50092aaff9ec460d8863b22077de62a80bd8812) // quotient_const
            mstore(add(payload, 0x1080), 0x73eda753299d7d4833351088b4af7508df8b737010b26601ef73fcbb87bd0000) // quotient_const
            mstore(add(payload, 0x10a0), 0x0aef2ff4e0c10ade42aca9fe2200e00159ed486fd28ef7edef05bf590de59ef3) // quotient_const
            mstore(add(payload, 0x10c0), 0x0000000000000000000000000000000000000000000000000000000000000006) // quotient_const
            mstore(add(payload, 0x10e0), 0x0000000000000000000000000000000000000000000000000600000000000000) // quotient_const
            mstore(add(payload, 0x1100), 0x0000000000000000000000000000000000060000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x1120), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff) // quotient_const
            mstore(add(payload, 0x1140), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefdffffff00000001) // quotient_const
            mstore(add(payload, 0x1160), 0x73eda753299d7d483339d80809a1d80553bba402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1180), 0x0000000000000000000000000000000000000000000000000000000000000003) // quotient_const
            mstore(add(payload, 0x11a0), 0x0000000000000000000000000000000000030000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x11c0), 0x0000000000000000000000000000012c71404d368ec010269b10000013afec50) // quotient_const
            mstore(add(payload, 0x11e0), 0x000000000000000000000000000000f8cd1b37d4ebee2693904ff354f25f7464) // quotient_const
            mstore(add(payload, 0x1200), 0x000000000000000000000000000001385b1875503c5c39fb9441f95933e4b28c) // quotient_const
            mstore(add(payload, 0x1220), 0x0000000000000000000000000000007c668d9bea75f71349c827f9aa792fba32) // quotient_const
            mstore(add(payload, 0x1240), 0x0000000000000000000000000000000761c60b88b9c70e630a72b13b050012c0) // quotient_const
            mstore(add(payload, 0x1260), 0x73eda753299d7d483339d80809a1d7a12dfd8a4625be569ccc4ffffef9700691) // quotient_const
            mstore(add(payload, 0x1280), 0x73eda753299d7d483339d80809a1d7b264b49166b159a4787a900438048ad935) // quotient_const
            mstore(add(payload, 0x12a0), 0x00000000000000000000000000000003b0e305c45ce387318539589d82800960) // quotient_const
            mstore(add(payload, 0x12c0), 0x0000000000000000000000000000010c5a3fa8ec14b781d2375bf725316c3fb0) // quotient_const
            mstore(add(payload, 0x12e0), 0x000000000000000000000000000000259007b94eb27289dcc84c1f9dce2e9860) // quotient_const
            mstore(add(payload, 0x1300), 0x73eda753299d7d483339d80809a1d79d35602792ebdf9e00793f578beeb3c47d) // quotient_const
            mstore(add(payload, 0x1320), 0x73eda753299d7d483339d80809a1d802ddd0f5801766ac88a72f1a40a8fff9c1) // quotient_const
            mstore(add(payload, 0x1340), 0x73eda753299d7d483339d80809a1d7abe053165ef916860e42e15847ef869571) // quotient_const
            mstore(add(payload, 0x1360), 0x73eda753299d7d483339d80809a1d7ec490dd323de5caac125229595cbe0efc1) // quotient_const
            mstore(add(payload, 0x1380), 0x08a75c054be451b1f2ad6bd569f92577dd4bd64d6d5c968569fbf9fbe04d544d) // quotient_const
            mstore(add(payload, 0x13a0), 0x0000000000000000000000000000000000000000000000000000001800000000) // quotient_const
            mstore(add(payload, 0x13c0), 0x0000000000000000000000000000000000000000180000000000000000000000) // quotient_const
            mstore(add(payload, 0x13e0), 0x0000000000000000000000000000000000000000000000000000000000006000) // quotient_const
            mstore(add(payload, 0x1400), 0x0000000000000000000000000000000000000000000000600000000000000000) // quotient_const
            mstore(add(payload, 0x1420), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffff700000001) // quotient_const
            mstore(add(payload, 0x1440), 0x73eda753299d7d483339d80809a1d80553bda402f7fe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1460), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffe001) // quotient_const
            mstore(add(payload, 0x1480), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bdeffffffff00000001) // quotient_const
            mstore(add(payload, 0x14a0), 0x73eda753299d7d483339d80809a1d7e355af567743ae3bbda4ffd260212ddbdb) // quotient_const
            mstore(add(payload, 0x14c0), 0x73eda753299d7d483339d80809a1d7ac8bb094e10dd00bb871cf13341ce9f671) // quotient_const
            mstore(add(payload, 0x14e0), 0x73eda753299d7d483339d80809a1d7b70b86399be46147106cd7aef7d718818d) // quotient_const
            mstore(add(payload, 0x1500), 0x73eda753299d7d483339d80809a1d7ae5b2956bf70a17c7596cc5f626b73876b) // quotient_const
            mstore(add(payload, 0x1520), 0x73eda753299d7d483339d80809a1d7b6bc3584645b26895898ae7ba60d735ad1) // quotient_const
            mstore(add(payload, 0x1540), 0x73eda753299d7d483339d80809a1d7b095efed6fd9f96e39d8c5c777a6fa1179) // quotient_const
            mstore(add(payload, 0x1560), 0x00000000000000000000000000000065fa2ae8a334f060c4110088dc9c766c72) // quotient_const
            mstore(add(payload, 0x1580), 0x00000000000000000000000000000000000000000c0000000000000000000000) // quotient_const
            mstore(add(payload, 0x15a0), 0x0000000000000000000000000000010a58272d65d68af0d3aa92c660a9421cb0) // quotient_const
            mstore(add(payload, 0x15c0), 0x0000000000000000000000000000000000000000000000300000000000000000) // quotient_const
            mstore(add(payload, 0x15e0), 0x000000000000000000000000000000ead8a63f3552d73ecbb978f3157ab67b5c) // quotient_const
            mstore(add(payload, 0x1600), 0x000000000000000000000000000000852c1396b2eb457869d549633054a10e58) // quotient_const
            mstore(add(payload, 0x1620), 0x00000000000000000000000000000104e9bce7caae169e9c3b9ae1d5bda569c2) // quotient_const
            mstore(add(payload, 0x1640), 0x0000000000000000000000000000008274de73e5570b4f4e1dcd70eaded2b4e1) // quotient_const
            mstore(add(payload, 0x1660), 0x000000000000000000000000000000ebc6985edbee8777f335f48d0ad7a5ef90) // quotient_const
            mstore(add(payload, 0x1680), 0x0000000000000000000000000000007f1cb491dcb90764a7bad754cb0588e5cc) // quotient_const
            mstore(add(payload, 0x16a0), 0x73eda753299d7d48333049095fbd120c6b5942dd2166802b5297f978232a0002) // quotient_const
            mstore(add(payload, 0x16c0), 0x0000000000000000000006000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x16e0), 0x0000000600000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x1700), 0x4302515f88a4431e1fbaccbc5adc8f25703b5745de78f77d0d3fe37cf2c01c83) // quotient_const
            mstore(add(payload, 0x1720), 0x140e70dbca64831b4b8f40317b68cd20f34ec27e98adf994cf555b0db316abbd) // quotient_const
            mstore(add(payload, 0x1740), 0x73eda753299d7d483339d60809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1760), 0x73eda751299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1780), 0x104e71fbe05313635bd503c3e4ec6d9ff680c43f0b2c76d5fb955ed6046aa12a) // quotient_const
            mstore(add(payload, 0x17a0), 0x1ff51227ca6853644d38dd4784bdae4c2024f5d6cd1acb78bae38c506ef8716c) // quotient_const
            mstore(add(payload, 0x17c0), 0x70156f48f76cc14b27137d78d0b4371477819d08e9f2c77036ebc744ad6da6cb) // quotient_const
            mstore(add(payload, 0x17e0), 0x37be870795549c37dcd00b9588085d0fa1ab8c1ad655e52c23ed8949f0fb5ae3) // quotient_const
            mstore(add(payload, 0x1800), 0x62a9cec91e3168b1496ccfcf27ad7a8d3c8d65793936323648c2b29cb6a41ac8) // quotient_const
            mstore(add(payload, 0x1820), 0x6ed3edb47fe320414c6b5a76f4cc0bce626d1a256829e20dfb44af3c3a5c88b0) // quotient_const
            mstore(add(payload, 0x1840), 0x62ea7e5a34aa00528575fab42c44f48dc6c3a5a2fadad34f0a31529dec7b61e0) // quotient_const
            mstore(add(payload, 0x1860), 0x6de98a7ebdd251f08ee9668a33e94c65bdb3185246bd05a64c5767be80a6f6b3) // quotient_const
            mstore(add(payload, 0x1880), 0x0b88a81e969233f724730fadaac8e2d294b414ee4222bdac5b3caa2ef7b70ba2) // quotient_const
            mstore(add(payload, 0x18a0), 0x0000000300000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x18c0), 0x409fb98f933d25e8d0038d4f7b2a98dbc278a3b57cfb0879943764202d0def59) // quotient_const
            mstore(add(payload, 0x18e0), 0x43fe0c177a010031bf648c1cc285529323863340cc562ac9e7aaad86598b55df) // quotient_const
            mstore(add(payload, 0x1900), 0x33cb899e22443dc4bd6718aaa5dd18684590bb9d54587d5a25b7e826dc13afab) // quotient_const
            mstore(add(payload, 0x1920), 0x5a46b0715e6d5198819eb2abc26638708b1b23dc3e7cb23c4a1bb20f9686f7ad) // quotient_const
            mstore(add(payload, 0x1940), 0x0f4d2cdbfd2f1714b46b78b33e8164a4d3f19d98c77d6dd30e31f24850ea65f3) // quotient_const
            mstore(add(payload, 0x1960), 0x419d6a1793664a2e73d2a85da4119e5513d7a0cde3bde4e90718f923a87532fa) // quotient_const
            mstore(add(payload, 0x1980), 0x33097aeadeda76e1094b97fb9816aa66a6edfb200f6a9a0fe16c08233a8dda63) // quotient_const
            mstore(add(payload, 0x19a0), 0x09062b3ea1b0c1037678aa3cc094d16f610fd18915e201850d7ce460bf058df5) // quotient_const
            mstore(add(payload, 0x19c0), 0x0456a29a706afacf2158850711006fe0acf6a437e9477bf6f782dfac86f2cf7b) // quotient_const
            mstore(add(payload, 0x19e0), 0x0397cc06bc030aab970dabe70cd498bbeea8daaea65607bb6a872125fec74a10) // quotient_const
            mstore(add(payload, 0x1a00), 0x73eda753299d7d4833351088b4af7508df8b737010b26e15294bfcbb91950003) // quotient_const
            mstore(add(payload, 0x1a20), 0x0594e0109a0005958008060d000b0200010594a01194a01194a005950008060d) // quotient_program
            mstore(add(payload, 0x1a40), 0x000b0300000594c01194c01194c005952008060d000b0300010594e01194e011) // quotient_program
            mstore(add(payload, 0x1a60), 0x94e00595a008060d000b0300011b00001b000105958008109aa00594a01194a0) // quotient_program
            mstore(add(payload, 0x1a80), 0x1195000d01060594c01194c01195200d02060594e01194e01195a00d03060d00) // quotient_program
            mstore(add(payload, 0x1aa0), 0x0b0300011b000221020403070002000094a00594c00694e00795000895200095) // quotient_program
            mstore(add(payload, 0x1ac0), 0x400595600695800995a00a95c00b95e00c96000d96200e96400f966010968011) // quotient_program
            mstore(add(payload, 0x1ae0), 0x96a00796c00896e00997000a972094a00095400595600695800796c00896e009) // quotient_program
            mstore(add(payload, 0x1b00), 0x97000a972094c00595400695600795800896c00996e00a970012972094e00695) // quotient_program
            mstore(add(payload, 0x1b20), 0x400795600895800996c00a96e012970013972095000795400895600995800a96) // quotient_program
            mstore(add(payload, 0x1b40), 0xc01296e013970014972095200895400995600a95801296c01396e01497001597) // quotient_program
            mstore(add(payload, 0x1b60), 0x2095a00995400a95601295801396c01496e015970016972095c00a9540129560) // quotient_program
            mstore(add(payload, 0x1b80), 0x1395801496c01596e01697001797201897401997800b04000121021a03070001) // quotient_program
            mstore(add(payload, 0x1ba0), 0x000094a00594c00694e01b95001c95200095400595600695801d95a01e95c00b) // quotient_program
            mstore(add(payload, 0x1bc0), 0x95e00c96000d96201f96402096602196802296a01b96c01c96e01d97001e9720) // quotient_program
            mstore(add(payload, 0x1be0), 0x94a00095400595600695801b96c01c96e01d97001e972094c00595400695601b) // quotient_program
            mstore(add(payload, 0x1c00), 0x95801c96c01d96e01e970023972094e00695401b95601c95801d96c01e96e023) // quotient_program
            mstore(add(payload, 0x1c20), 0x970024972095001b95401c95601d95801e96c02396e024970025972095201c95) // quotient_program
            mstore(add(payload, 0x1c40), 0x401d95601e95802396c02496e025970026972095a01d95401e95602395802496) // quotient_program
            mstore(add(payload, 0x1c60), 0xc02596e026970027972095c01e95402395602495802596c02696e02797002897) // quotient_program
            mstore(add(payload, 0x1c80), 0x202997400b0400011b000321022a01000009000995a00a95c00b95e00c96000d) // quotient_program
            mstore(add(payload, 0x1ca0), 0x96200e96400f96600094a00594c00694e00795000895201096801196a0189740) // quotient_program
            mstore(add(payload, 0x1cc0), 0x1997800b05000121022b01000008001d95a01e95c00b95e00c96000d96201f96) // quotient_program
            mstore(add(payload, 0x1ce0), 0x402096600094a00594c00694e01b95001c95202196802296a02997400b050001) // quotient_program
            mstore(add(payload, 0x1d00), 0x210397a02c0000000b2b0b94a00c94c00d94e02d95402e95602f95800b95e00c) // quotient_program
            mstore(add(payload, 0x1d20), 0x96000d96203097403197600b94a095e00c94a096000d94a096200c94c095e00d) // quotient_program
            mstore(add(payload, 0x1d40), 0x94c096003294c096a00d94e095e03294e096803394e096a03295009660339500) // quotient_program
            mstore(add(payload, 0x1d60), 0x968034950096a032952096403395209660349520968035952096a00095409540) // quotient_program
            mstore(add(payload, 0x1d80), 0x2e954095602f9540958006956095603695609720369580970037958097203295) // quotient_program
            mstore(add(payload, 0x1da0), 0xa096203395a096403495a096603595a096803895a096a03295c096003395c096) // quotient_program
            mstore(add(payload, 0x1dc0), 0x203495c096403595c096603895c096803995c096a03696c096e03796c097003a) // quotient_program
            mstore(add(payload, 0x1de0), 0x96c097203b96e096e03a96e097003c96e097203d970097003e970097203f9720) // quotient_program
            mstore(add(payload, 0x1e00), 0x97200d000b060000210397a04003080002150b94a00c94c00d94e00e95000f95) // quotient_program
            mstore(add(payload, 0x1e20), 0x202d95402e95602f95801095a01195c00b95e00c96000d96200e96400f966010) // quotient_program
            mstore(add(payload, 0x1e40), 0x96801196a04196c04296e043970044972094a00b95e00c96000d96200e96400f) // quotient_program
            mstore(add(payload, 0x1e60), 0x96601096801196a094c00c95e00d96000e96200f96401096601196804596a094) // quotient_program
            mstore(add(payload, 0x1e80), 0xe00d95e00e96000f96201096401196604596804696a095000e95e00f96001096) // quotient_program
            mstore(add(payload, 0x1ea0), 0x201196404596604696804796a095200f95e01096001196204596404696604796) // quotient_program
            mstore(add(payload, 0x1ec0), 0x804896a095400095402e95602f95804196c04296e043970044972095a01095e0) // quotient_program
            mstore(add(payload, 0x1ee0), 0x1196004596204696404796604896804996a095c01195e0459600469620479640) // quotient_program
            mstore(add(payload, 0x1f00), 0x4896604996804a96a01897401997800695609560419560958042956096c04395) // quotient_program
            mstore(add(payload, 0x1f20), 0x6096e044956097004b95609720089580958043958096c044958096e04b958097) // quotient_program
            mstore(add(payload, 0x1f40), 0x004c958097200a96c096c04b96c096e04c96c097004d96c097201396e096e04d) // quotient_program
            mstore(add(payload, 0x1f60), 0x96e097004e96e0972015970097004f9700972017972097200d000b0600012103) // quotient_program
            mstore(add(payload, 0x1f80), 0x97a05003080001150b94a00c94c00d94e01f95002095202d95402e95602f9580) // quotient_program
            mstore(add(payload, 0x1fa0), 0x2195a02295c00b95e00c96000d96201f96402096602196802296a05196c05296) // quotient_program
            mstore(add(payload, 0x1fc0), 0xe053970054972094a00b95e00c96000d96201f96402096602196802296a094c0) // quotient_program
            mstore(add(payload, 0x1fe0), 0x0c95e00d96001f96202096402196602296805596a094e00d95e01f9600209620) // quotient_program
            mstore(add(payload, 0x2000), 0x2196402296605596805696a095001f95e0209600219620229640559660569680) // quotient_program
            mstore(add(payload, 0x2020), 0x5796a095202095e02196002296205596405696605796805896a095400095402e) // quotient_program
            mstore(add(payload, 0x2040), 0x95602f95805196c05296e053970054972095a02195e022960055962056964057) // quotient_program
            mstore(add(payload, 0x2060), 0x96605896805996a095c02295e05596005696205796405896605996805a96a029) // quotient_program
            mstore(add(payload, 0x2080), 0x97400695609560519560958052956096c053956096e054956097005b95609720) // quotient_program
            mstore(add(payload, 0x20a0), 0x1c9580958053958096c054958096e05b958097005c958097201e96c096c05b96) // quotient_program
            mstore(add(payload, 0x20c0), 0xc096e05c96c097005d96c097202496e096e05d96e097005e96e0972026970097) // quotient_program
            mstore(add(payload, 0x20e0), 0x005f9700972028972097200d000b060001210397a0600000000c390b94a00c94) // quotient_program
            mstore(add(payload, 0x2100), 0xc00d94e03097403197600097a00097c00597e00698000b98a00c98c00d98e000) // quotient_program
            mstore(add(payload, 0x2120), 0x954097c005954097e006954098000b954098a00c954098c00d954098e0059560) // quotient_program
            mstore(add(payload, 0x2140), 0x97c006956097e061956098800c956098a00d956098c0329560996006958097c0) // quotient_program
            mstore(add(payload, 0x2160), 0x61958098603b958098800d958098a0329580994033958099600095e097a00596) // quotient_program
            mstore(add(payload, 0x2180), 0x0097a006962097a06196c098403b96c098606296c098803296c099203396c099) // quotient_program
            mstore(add(payload, 0x21a0), 0x403496c099606196e098203b96e098406296e098603d96e098803296e0990033) // quotient_program
            mstore(add(payload, 0x21c0), 0x96e099203496e099403596e0996061970098003b9700982062970098403d9700) // quotient_program
            mstore(add(payload, 0x21e0), 0x9860639700988032970098e03397009900349700992035970099403897009960) // quotient_program
            mstore(add(payload, 0x2200), 0x61972097e03b9720980062972098203d9720984063972098603f972098803297) // quotient_program
            mstore(add(payload, 0x2220), 0x2098c033972098e034972099003597209920389720994039972099600d000b07) // quotient_program
            mstore(add(payload, 0x2240), 0x0000210397a064020f000a001997800097a00097c00597e00698000798200898) // quotient_program
            mstore(add(payload, 0x2260), 0x400998600a98800b98a00c98c00d98e00e99000f992097a00095e00596000696) // quotient_program
            mstore(add(payload, 0x2280), 0x200796400896600996800a96a097c00095400595600695800796c00896e00997) // quotient_program
            mstore(add(payload, 0x22a0), 0x000a972097e00595400695600795800896c00996e00a97001297209800069540) // quotient_program
            mstore(add(payload, 0x22c0), 0x0795600895800996c00a96e012970013972098200795400895600995800a96c0) // quotient_program
            mstore(add(payload, 0x22e0), 0x1296e013970014972098400895400995600a95801296c01396e0149700159720) // quotient_program
            mstore(add(payload, 0x2300), 0x98600995400a95601295801396c01496e015970016972098800a954012956013) // quotient_program
            mstore(add(payload, 0x2320), 0x95801496c01596e016970017972095400b98a00c98c00d98e00e99000f992010) // quotient_program
            mstore(add(payload, 0x2340), 0x994011996095600c98a00d98c00e98e00f990010992011994045996095800d98) // quotient_program
            mstore(add(payload, 0x2360), 0xa00e98c00f98e010990011992045994046996096c00e98a00f98c01098e01199) // quotient_program
            mstore(add(payload, 0x2380), 0x0045992046994047996096e00f98a01098c01198e04599004699204799404899) // quotient_program
            mstore(add(payload, 0x23a0), 0x6097001098a01198c04598e046990047992048994049996097201198a04598c0) // quotient_program
            mstore(add(payload, 0x23c0), 0x4698e04799004899204999404a99600b94a00c94c00d94e00e95000f95201095) // quotient_program
            mstore(add(payload, 0x23e0), 0xa01195c01897401099401199600d000b070001210397a065020f0009000097a0) // quotient_program
            mstore(add(payload, 0x2400), 0x0097c00597e00698001b98201c98401d98601e98800b98a00c98c00d98e01f99) // quotient_program
            mstore(add(payload, 0x2420), 0x0020992021994097a00095e00596000696201b96401c96601d96801e96a097c0) // quotient_program
            mstore(add(payload, 0x2440), 0x0095400595600695801b96c01c96e01d97001e972097e00595400695601b9580) // quotient_program
            mstore(add(payload, 0x2460), 0x1c96c01d96e01e970023972098000695401b95601c95801d96c01e96e0239700) // quotient_program
            mstore(add(payload, 0x2480), 0x24972098201b95401c95601d95801e96c02396e024970025972098401c95401d) // quotient_program
            mstore(add(payload, 0x24a0), 0x95601e95802396c02496e025970026972098601d95401e95602395802496c025) // quotient_program
            mstore(add(payload, 0x24c0), 0x96e026970027972098801e95402395602495802596c02696e027970028972095) // quotient_program
            mstore(add(payload, 0x24e0), 0x400b98a00c98c00d98e01f990020992021994022996095600c98a00d98c01f98) // quotient_program
            mstore(add(payload, 0x2500), 0xe020990021992022994055996095800d98a01f98c02098e02199002299205599) // quotient_program
            mstore(add(payload, 0x2520), 0x4056996096c01f98a02098c02198e022990055992056994057996096e02098a0) // quotient_program
            mstore(add(payload, 0x2540), 0x2198c02298e055990056992057994058996097002198a02298c05598e0569900) // quotient_program
            mstore(add(payload, 0x2560), 0x57992058994059996097202298a05598c05698e05799005899205999405a9960) // quotient_program
            mstore(add(payload, 0x2580), 0x0b94a00c94c00d94e01f95002095202195a02295c02997402299600d000b0700) // quotient_program
            mstore(add(payload, 0x25a0), 0x01210397a0660000000b2b6794a06894c06994e06a95406b95606c95806a95e0) // quotient_program
            mstore(add(payload, 0x25c0), 0x6b96006c96203097403197606d94a094a06894a094c06994a094e06e94c094c0) // quotient_program
            mstore(add(payload, 0x25e0), 0x6f94c095c06f94e095a07094e095c06f9500952070950095a071950095c07295) // quotient_program
            mstore(add(payload, 0x2600), 0x20952071952095a073952095c06a954095e06b954096006c954096206b956095) // quotient_program
            mstore(add(payload, 0x2620), 0xe06c9560960074956096a06c958095e0749580968075958096a07695a095a077) // quotient_program
            mstore(add(payload, 0x2640), 0x95a095c07895c095c074960097207496209700759620972074964096e0759640) // quotient_program
            mstore(add(payload, 0x2660), 0x9700799640972074966096c075966096e079966097007a9660972075968096c0) // quotient_program
            mstore(add(payload, 0x2680), 0x79968096e07a968097007b968097207996a096c07a96a096e07b96a097007c96) // quotient_program
            mstore(add(payload, 0x26a0), 0xa097200d000b080000210397a07d03080002156794a06894c06994e07e95007f) // quotient_program
            mstore(add(payload, 0x26c0), 0x95206a95406b95606c95808095a08195c06a95e06b96006c9620829640839660) // quotient_program
            mstore(add(payload, 0x26e0), 0x8496808596a08296c08396e084970085972094a06d94a06894c06994e07e9500) // quotient_program
            mstore(add(payload, 0x2700), 0x7f95208095a08195c095406a95e06b96006c96208296408396608496808596a0) // quotient_program
            mstore(add(payload, 0x2720), 0x95606b95e06c96008296208396408496608596808696a095806c95e082960083) // quotient_program
            mstore(add(payload, 0x2740), 0x96208496408596608696808796a096c08295e083960084962085964086966087) // quotient_program
            mstore(add(payload, 0x2760), 0x96808896a096e08395e08496008596208696408796608896808996a097008495) // quotient_program
            mstore(add(payload, 0x2780), 0xe08596008696208796408896608996808a96a097208595e08696008796208896) // quotient_program
            mstore(add(payload, 0x27a0), 0x408996608a96808b96a01897401997806e94c094c07e94c094e07f94c0950080) // quotient_program
            mstore(add(payload, 0x27c0), 0x94c095208194c095a08c94c095c08d94e094e08094e095008194e095208c94e0) // quotient_program
            mstore(add(payload, 0x27e0), 0x95a08e94e095c08f950095008c950095208e950095a090950095c09195209520) // quotient_program
            mstore(add(payload, 0x2800), 0x90952095a092952095c09395a095a09495a095c09595c095c00d000b08000121) // quotient_program
            mstore(add(payload, 0x2820), 0x0397a09603080001156794a06894c06994e09795009895206a95406b95606c95) // quotient_program
            mstore(add(payload, 0x2840), 0x809995a09a95c06a95e06b96006c96209b96409c96609d96809e96a09b96c09c) // quotient_program
            mstore(add(payload, 0x2860), 0x96e09d97009e972094a06d94a06894c06994e09795009895209995a09a95c095) // quotient_program
            mstore(add(payload, 0x2880), 0x406a95e06b96006c96209b96409c96609d96809e96a095606b95e06c96009b96) // quotient_program
            mstore(add(payload, 0x28a0), 0x209c96409d96609e96809f96a095806c95e09b96009c96209d96409e96609f96) // quotient_program
            mstore(add(payload, 0x28c0), 0x80a096a096c09b95e09c96009d96209e96409f9660a09680a196a096e09c95e0) // quotient_program
            mstore(add(payload, 0x28e0), 0x9d96009e96209f9640a09660a19680a296a097009d95e09e96009f9620a09640) // quotient_program
            mstore(add(payload, 0x2900), 0xa19660a29680a396a097209e95e09f9600a09620a19640a29660a39680a496a0) // quotient_program
            mstore(add(payload, 0x2920), 0x2997406e94c094c09794c094e09894c095009994c095209a94c095a0a594c095) // quotient_program
            mstore(add(payload, 0x2940), 0xc0a694e094e09994e095009a94e09520a594e095a0a794e095c0a895009500a5) // quotient_program
            mstore(add(payload, 0x2960), 0x95009520a7950095a0a9950095c0aa95209520a9952095a0ab952095c0ac95a0) // quotient_program
            mstore(add(payload, 0x2980), 0x95a0ad95a095c0ae95c095c00d000b080001210397a0af0000000e100094a005) // quotient_program
            mstore(add(payload, 0x29a0), 0x94c00694e06a95406b95606c95800095e00596000696203097403197600097c0) // quotient_program
            mstore(add(payload, 0x29c0), 0x0597e00698000b954095406b954095606c954095800d95609560749560972074) // quotient_program
            mstore(add(payload, 0x29e0), 0x9580970075958097207496c096e07596c097007996c097203396e096e07996e0) // quotient_program
            mstore(add(payload, 0x2a00), 0x97007a96e0972035970097007b9700972039972097200d000b090000210397a0) // quotient_program
            mstore(add(payload, 0x2a20), 0xb004010002150094a00594c00694e00795000895206a95406b95606c95800995) // quotient_program
            mstore(add(payload, 0x2a40), 0xa00a95c00095e00596000696200796400896600996800a96a08296c08396e084) // quotient_program
            mstore(add(payload, 0x2a60), 0x97008597200097c00597e00698000798200898400998600a988095400b95406b) // quotient_program
            mstore(add(payload, 0x2a80), 0x95606c95808296c08396e08497008597201897401997800d9560956082956095) // quotient_program
            mstore(add(payload, 0x2aa0), 0x8083956096c084956096e0859560970086956097200f9580958084958096c085) // quotient_program
            mstore(add(payload, 0x2ac0), 0x958096e0869580970087958097201196c096c08696c096e08796c097008896c0) // quotient_program
            mstore(add(payload, 0x2ae0), 0x97204696e096e08896e097008996e0972048970097008a970097204a97209720) // quotient_program
            mstore(add(payload, 0x2b00), 0x0d000b090001210397a0b104010001150094a00594c00694e01b95001c95206a) // quotient_program
            mstore(add(payload, 0x2b20), 0x95406b95606c95801d95a01e95c00095e00596000696201b96401c96601d9680) // quotient_program
            mstore(add(payload, 0x2b40), 0x1e96a09b96c09c96e09d97009e97200097c00597e00698001b98201c98401d98) // quotient_program
            mstore(add(payload, 0x2b60), 0x601e988095400b95406b95606c95809b96c09c96e09d97009e97202997400d95) // quotient_program
            mstore(add(payload, 0x2b80), 0x6095609b956095809c956096c09d956096e09e956097009f9560972020958095) // quotient_program
            mstore(add(payload, 0x2ba0), 0x809d958096c09e958096e09f95809700a0958097202296c096c09f96c096e0a0) // quotient_program
            mstore(add(payload, 0x2bc0), 0x96c09700a196c097205696e096e0a196e09700a296e097205897009700a39700) // quotient_program
            mstore(add(payload, 0x2be0), 0x97205a972097200d000b090001191f0000000000000000000000000000000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2c00), 0x00000000000000000000000000000000027edeb6cb53bebf636d32f580c64522) // fixed_comms[0].x_hi
            mstore(add(payload, 0x2c20), 0x890ddce64ce75094b02fc29b587b0808b6af78e3f11ea3c1c125f0985291e854) // fixed_comms[0].x_lo
            mstore(add(payload, 0x2c40), 0x0000000000000000000000000000000010b0c8ce5f0978e6c9f76b6f61213764) // fixed_comms[0].y_hi
            mstore(add(payload, 0x2c60), 0x58c9b24a9bc319ccae335f5f8cfaf54a447c65ebc0b5b0954c8750ed72bdf891) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2c80), 0x000000000000000000000000000000000815390329a004b20aa17178b73fbc5b) // fixed_comms[1].x_hi
            mstore(add(payload, 0x2ca0), 0xc75cf38543e2dba99f423624135187f4f7515a3b8efc9b37a5b4d54e62529d25) // fixed_comms[1].x_lo
            mstore(add(payload, 0x2cc0), 0x0000000000000000000000000000000009469fefcccaea25b4cf3c42eda1bee7) // fixed_comms[1].y_hi
            mstore(add(payload, 0x2ce0), 0x5edc149cfad91515baf07466ef60748a85f3a83c9826d6b6a95142173c2a13a3) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2d00), 0x00000000000000000000000000000000165292276c3511d63dbf61179246c633) // fixed_comms[2].x_hi
            mstore(add(payload, 0x2d20), 0xec1cbf9b8382eba32e35f8907edc09259a2d308c8604c210c63d59923327ad83) // fixed_comms[2].x_lo
            mstore(add(payload, 0x2d40), 0x00000000000000000000000000000000046c8c282ed0c22d69b105f80d1c1c24) // fixed_comms[2].y_hi
            mstore(add(payload, 0x2d60), 0xc6f22dc821e69569b63159e44890c09931b246e1b0a1b11f72a0b17af2c17226) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2d80), 0x0000000000000000000000000000000002a23b4f1ebe7f57e7492b90cb4e9e4e) // fixed_comms[3].x_hi
            mstore(add(payload, 0x2da0), 0x497de52bce2458ac72f14feb8152d93837fc00b69d0a92d5d89c12e742116cb8) // fixed_comms[3].x_lo
            mstore(add(payload, 0x2dc0), 0x0000000000000000000000000000000000a2437b01a59b7f1463550d8747be3b) // fixed_comms[3].y_hi
            mstore(add(payload, 0x2de0), 0x686e22150b83975aac8a5ac57959611b0354b2a33d4ca8cff415cfcba0ed75cf) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2e00), 0x000000000000000000000000000000000f1cb5eb5320547862bf553c3822fc78) // fixed_comms[4].x_hi
            mstore(add(payload, 0x2e20), 0x764bad62d640aebca2154c0c9c02bc4db2cd5113d78f1ad8f366446df2017658) // fixed_comms[4].x_lo
            mstore(add(payload, 0x2e40), 0x0000000000000000000000000000000008ca33a0d542933ab145c67bc0c5d206) // fixed_comms[4].y_hi
            mstore(add(payload, 0x2e60), 0x2c415087078eda5fd6c83f17ff21b133c67a1c8b733e0ff9a3cbf83ffd817f09) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2e80), 0x000000000000000000000000000000000acfc1d2842e61b5e7c02808b26aa75e) // fixed_comms[5].x_hi
            mstore(add(payload, 0x2ea0), 0xcf8b7c5f18f8c487754dee3335c4a0af0a5ebd6ec1633366e4e6a3fb29d88f05) // fixed_comms[5].x_lo
            mstore(add(payload, 0x2ec0), 0x000000000000000000000000000000001108005ff4f769969595621b212bdf98) // fixed_comms[5].y_hi
            mstore(add(payload, 0x2ee0), 0x41ff6104f2c90e4e4f908b07bc6e000d9f5809b2941d258abc6d16bbe00b15e6) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2f00), 0x0000000000000000000000000000000006b4d595e229a98c69e491eca33a7581) // fixed_comms[6].x_hi
            mstore(add(payload, 0x2f20), 0xd62662a3bad01216ff4f8615833ed398e46925a9bd9ae6dc6d834465093986d8) // fixed_comms[6].x_lo
            mstore(add(payload, 0x2f40), 0x0000000000000000000000000000000002d2529a239b715407c38a18b056c6c2) // fixed_comms[6].y_hi
            mstore(add(payload, 0x2f60), 0x712b512d0e206d2cb4eb4709cd5a6348e44af92e21d35ea9411e8993005a8265) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2f80), 0x00000000000000000000000000000000019164d42b9c987f9ba16af31327d95f) // fixed_comms[7].x_hi
            mstore(add(payload, 0x2fa0), 0xff0da911b853294b0845afe85bd6bb2f11ce89373172ec378b567b067b65062c) // fixed_comms[7].x_lo
            mstore(add(payload, 0x2fc0), 0x000000000000000000000000000000000e1a3b30b349e690629043ab4cd56557) // fixed_comms[7].y_hi
            mstore(add(payload, 0x2fe0), 0xd27031dc258fc3e644938f63bdbf1f814f2e55d8ebbe48654856bca400f6b11d) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3000), 0x0000000000000000000000000000000002a95feec8a51dae29ec960db7a65f92) // fixed_comms[8].x_hi
            mstore(add(payload, 0x3020), 0xc31852271694b5a5725d9c20777f4a44f566e0a41633e6579003e3ba2e940677) // fixed_comms[8].x_lo
            mstore(add(payload, 0x3040), 0x0000000000000000000000000000000018b0ddeeb33cba4c14a6dfdf3936c701) // fixed_comms[8].y_hi
            mstore(add(payload, 0x3060), 0xeee4e9d448fe04c2891e2c1c14d2f18388b03f7586cc82cb719bd5393c2ffe7c) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3080), 0x0000000000000000000000000000000018d8949fa81872c49008a22f299092cc) // fixed_comms[9].x_hi
            mstore(add(payload, 0x30a0), 0x2c732bf017af44e582c0bf748d841352ad86cef5060d659ae4772ce144f05254) // fixed_comms[9].x_lo
            mstore(add(payload, 0x30c0), 0x0000000000000000000000000000000006d61e921fe0322cd8852ef1ce45976c) // fixed_comms[9].y_hi
            mstore(add(payload, 0x30e0), 0x7cebfef671f8090de83ba66a2344b94a801f92de1252b191fce9155f354d0d22) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3100), 0x0000000000000000000000000000000000b05f07364fa6e34d1531c1210f25ee) // fixed_comms[10].x_hi
            mstore(add(payload, 0x3120), 0x2161123a8df7c9b1ef096ae841df15ddbf72051278f772762561f6588bada9e5) // fixed_comms[10].x_lo
            mstore(add(payload, 0x3140), 0x0000000000000000000000000000000013bf43990e56b5b790fd6e01461ccdd9) // fixed_comms[10].y_hi
            mstore(add(payload, 0x3160), 0xe88c97b6aef7fe905ca2113d10cd00106307a7cec084d292c805921ddd266379) // fixed_comms[10].y_lo
            // Fixed-column commitment 11, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3180), 0x00000000000000000000000000000000085b6410030ecdc020942851047cf237) // fixed_comms[11].x_hi
            mstore(add(payload, 0x31a0), 0x9c9c9bb218540241434381109f505f21842aadb79e1290bf15d09779052c830e) // fixed_comms[11].x_lo
            mstore(add(payload, 0x31c0), 0x0000000000000000000000000000000001662c17e52c0576a1daf532fd9b5d44) // fixed_comms[11].y_hi
            mstore(add(payload, 0x31e0), 0xa3b693810486d8cc2b3231928889a5901b11f8de1ea0a8d7da54719bb1bacb39) // fixed_comms[11].y_lo
            // Fixed-column commitment 12, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3200), 0x000000000000000000000000000000001842a8cec63398e3cd72495091717037) // fixed_comms[12].x_hi
            mstore(add(payload, 0x3220), 0xed2687fe07e288a66dbddadb866eab042e668795097a24350329af3a2faa15e8) // fixed_comms[12].x_lo
            mstore(add(payload, 0x3240), 0x000000000000000000000000000000000cee59973fde1d885353d9f171f17c99) // fixed_comms[12].y_hi
            mstore(add(payload, 0x3260), 0xfd88d67302f6cec5cbcd7d8430f17485f2bbaa4a092e725824499b3fc0cf01bd) // fixed_comms[12].y_lo
            // Fixed-column commitment 13, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3280), 0x000000000000000000000000000000000bc13cf9c2ca9c1f9580396ab49accc9) // fixed_comms[13].x_hi
            mstore(add(payload, 0x32a0), 0xa59f313f4b8fb07f49e94a94d92b3e43a072f1699b28c1d2a20821ce6fb0f9b7) // fixed_comms[13].x_lo
            mstore(add(payload, 0x32c0), 0x0000000000000000000000000000000011332bcf31c12984a8203dd36b9d07a8) // fixed_comms[13].y_hi
            mstore(add(payload, 0x32e0), 0x4d738b411376f8549cc9eb50ebc1f2c4ab08d9e7a3c66f3314dcf2a576a06df2) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3300), 0x0000000000000000000000000000000017cf809a3994c83dd1b6936c60abe485) // fixed_comms[14].x_hi
            mstore(add(payload, 0x3320), 0x7c95db3e37d4afe261e970ce15c6e534ef5ffc4d669585c7611c98887002aeb7) // fixed_comms[14].x_lo
            mstore(add(payload, 0x3340), 0x00000000000000000000000000000000128a022045ddf5b9cd9f3f763a644dd1) // fixed_comms[14].y_hi
            mstore(add(payload, 0x3360), 0x23939f9eb3ea9b5bdd65fef708f65bcd26bcd98df4695508a6ce0fb75d3b5667) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3380), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x_hi
            mstore(add(payload, 0x33a0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x_lo
            mstore(add(payload, 0x33c0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y_hi
            mstore(add(payload, 0x33e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3400), 0x000000000000000000000000000000001177fcb80f59ee7879011aaa431d79de) // fixed_comms[16].x_hi
            mstore(add(payload, 0x3420), 0x98dff9ee46b668f3f29bc4d4892ec8510d355a08ba4f9a1d4e700153b223d458) // fixed_comms[16].x_lo
            mstore(add(payload, 0x3440), 0x0000000000000000000000000000000007ea0ef47801c579487e8449cd57a5ad) // fixed_comms[16].y_hi
            mstore(add(payload, 0x3460), 0x320fa55b7c61f1f5e3313bf6400bb4306bb3e4795fff1870831fe642378dccab) // fixed_comms[16].y_lo
            // Fixed-column commitment 17, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3480), 0x0000000000000000000000000000000011acfea52284cb289f07c847aa50aa05) // fixed_comms[17].x_hi
            mstore(add(payload, 0x34a0), 0x845813693a743e808d48c8b6490ebd104db1845347b8f83120da6b7a36081585) // fixed_comms[17].x_lo
            mstore(add(payload, 0x34c0), 0x00000000000000000000000000000000111ff99c3d684d2742d28db112fd72ac) // fixed_comms[17].y_hi
            mstore(add(payload, 0x34e0), 0xd85588bb0bebb5007410319683f18d4e1f134fe74f2005fbfc66d54430f8795e) // fixed_comms[17].y_lo
            // Fixed-column commitment 18, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3500), 0x0000000000000000000000000000000002fad9181895f66bbb41c04bd127b86c) // fixed_comms[18].x_hi
            mstore(add(payload, 0x3520), 0x89a1b5709ec24df2d56036902f3196d418b5a3277cc908cede5bdabb00f6daa4) // fixed_comms[18].x_lo
            mstore(add(payload, 0x3540), 0x000000000000000000000000000000000f36d47343a29153c696f88676a0af6f) // fixed_comms[18].y_hi
            mstore(add(payload, 0x3560), 0x5fd662d030504b22549a645b8e4429551ff43adfc2a3e620a4ba8de187701e1d) // fixed_comms[18].y_lo
            // Fixed-column commitment 19, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3580), 0x0000000000000000000000000000000004cdedcde78f20dc3ceb28113122a98c) // fixed_comms[19].x_hi
            mstore(add(payload, 0x35a0), 0xf7b8a957113b4de93050cb8c6923a676a65a5c275483fa130368c6e0ecec04d8) // fixed_comms[19].x_lo
            mstore(add(payload, 0x35c0), 0x0000000000000000000000000000000003e1359b4315663a412bac7995377f5b) // fixed_comms[19].y_hi
            mstore(add(payload, 0x35e0), 0x0eab81500698a8a6b8c8e6825186f308be132dc13b54eb7986a3b44f8cbc3e9a) // fixed_comms[19].y_lo
            // Fixed-column commitment 20, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3600), 0x00000000000000000000000000000000040a34d0f0a20de35a43c3c430ceeed6) // fixed_comms[20].x_hi
            mstore(add(payload, 0x3620), 0x9e926c496160c3ca0fd8a8da907fcbe46c658fb8d889490aaec58c181d31dfca) // fixed_comms[20].x_lo
            mstore(add(payload, 0x3640), 0x0000000000000000000000000000000016a0d1be434e519da934b962b24f1ecb) // fixed_comms[20].y_hi
            mstore(add(payload, 0x3660), 0x685af302d8b4a178633f7251ee02a9981c3c177c6705d4c68faecdb7437c4285) // fixed_comms[20].y_lo
            // Fixed-column commitment 21, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3680), 0x000000000000000000000000000000001881c6bd8858bd8b97665133b6973c19) // fixed_comms[21].x_hi
            mstore(add(payload, 0x36a0), 0x8ee2888dd97caf3dd6887c6ae8f8f54c5a2b8aa20faa23a2faf9cb87f090680b) // fixed_comms[21].x_lo
            mstore(add(payload, 0x36c0), 0x000000000000000000000000000000000a9881752fd39399965c724de4bda545) // fixed_comms[21].y_hi
            mstore(add(payload, 0x36e0), 0xc080aee16c1777ac33ecbf7a5b4cc7e829e6f2183e1f24cac7b07e4f5feab530) // fixed_comms[21].y_lo
            // Fixed-column commitment 22, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3700), 0x000000000000000000000000000000000af966e41ea9239d086facb6231e36c6) // fixed_comms[22].x_hi
            mstore(add(payload, 0x3720), 0x375c693ef10fd08f679ef6192a4b6436e4d514ad88fa3b245e97016e24004f09) // fixed_comms[22].x_lo
            mstore(add(payload, 0x3740), 0x00000000000000000000000000000000002a683832b9e3e6bf9c35aea88aa47c) // fixed_comms[22].y_hi
            mstore(add(payload, 0x3760), 0xa764fd4a2078d72b92c83f465ca275ba7e6c343c53bae46b94d903ae3c70e731) // fixed_comms[22].y_lo
            // Fixed-column commitment 23, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3780), 0x0000000000000000000000000000000014fe3fd785df4b2960c8913451e08633) // fixed_comms[23].x_hi
            mstore(add(payload, 0x37a0), 0x65a6ccad0237b71908d5cfd1a6cb7156f5b6975c455ee63a28a5b4f6eaa36243) // fixed_comms[23].x_lo
            mstore(add(payload, 0x37c0), 0x00000000000000000000000000000000089f84a01b078917127088904a86d4f8) // fixed_comms[23].y_hi
            mstore(add(payload, 0x37e0), 0x14036752a7fbff115bf7863795daa8b9b3c80b071afdcde2d364a997a1c6d6fb) // fixed_comms[23].y_lo
            // Fixed-column commitment 24, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3800), 0x0000000000000000000000000000000007f469889f896d47a2bc3b4bdee08c95) // fixed_comms[24].x_hi
            mstore(add(payload, 0x3820), 0xcc7e3a9515557945499f91a2c7d8d66d037762c43ccc712fbc481730307eccac) // fixed_comms[24].x_lo
            mstore(add(payload, 0x3840), 0x0000000000000000000000000000000005d55aa6584065b70142666046dc3aa7) // fixed_comms[24].y_hi
            mstore(add(payload, 0x3860), 0x229e1e50aa10c56b787f4d7cc562d6a299a34c23b1fd0b120fcc5da53cb36b86) // fixed_comms[24].y_lo
            // Fixed-column commitment 25, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3880), 0x000000000000000000000000000000000feeaf3400fdce99f07322763518f5b1) // fixed_comms[25].x_hi
            mstore(add(payload, 0x38a0), 0xb872256290dd7f9a5f249ad8175d9f83f26e29ae0d8cea1c551d24473d17db3c) // fixed_comms[25].x_lo
            mstore(add(payload, 0x38c0), 0x000000000000000000000000000000000bebd9af3b4b707a6c524d883b08c50a) // fixed_comms[25].y_hi
            mstore(add(payload, 0x38e0), 0x4f7cd6c9e4e2473e73e8ea8ace59d778d9f663281e8ead039f1ea022a7619f4a) // fixed_comms[25].y_lo
            // Fixed-column commitment 26, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3900), 0x00000000000000000000000000000000159078118c901ed72545178529af5fe0) // fixed_comms[26].x_hi
            mstore(add(payload, 0x3920), 0x37c7b2b6b22b29ca3c8dfb13f404b21b566aedffc8aca0f0e8371b022ba01495) // fixed_comms[26].x_lo
            mstore(add(payload, 0x3940), 0x000000000000000000000000000000000dfd0364654adf170fe1a7afc40f573c) // fixed_comms[26].y_hi
            mstore(add(payload, 0x3960), 0xe6b479672ac927f338c3d083b3387bc90b6eb60c758697e2c147efc78948af58) // fixed_comms[26].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3980), 0x0000000000000000000000000000000012ac3f3991c25df7626c1348ca20bdbc) // permutation_comms[0].x_hi
            mstore(add(payload, 0x39a0), 0xed766899c1cf3ff3506010165b5f8fab54fb3fe1beb56f9166f66c180b1a9ca7) // permutation_comms[0].x_lo
            mstore(add(payload, 0x39c0), 0x00000000000000000000000000000000002438f6b167685292f8586bfacb805a) // permutation_comms[0].y_hi
            mstore(add(payload, 0x39e0), 0x664f295b3572425bd3c819d247da7c728420b517f5affb75bbecbdc505990347) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3a00), 0x0000000000000000000000000000000018d0daacd88f6a6d6881104c834b52f1) // permutation_comms[1].x_hi
            mstore(add(payload, 0x3a20), 0xf31c7257deb12da5ea5a52b324df13f6e25be59031ca96eaba4a20ffcb4aa299) // permutation_comms[1].x_lo
            mstore(add(payload, 0x3a40), 0x0000000000000000000000000000000003110564adfe5ba20e33892ba8b42a24) // permutation_comms[1].y_hi
            mstore(add(payload, 0x3a60), 0x69ff3c221edcea7c84c5e29ee4169340ab94166681471d6202e0aa2f34a58a3f) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3a80), 0x000000000000000000000000000000000c7a1ed9d86199f9fd10bc37dfe68f7e) // permutation_comms[2].x_hi
            mstore(add(payload, 0x3aa0), 0x41b06d67e26d32e76dd5aa91cfb8e9d2dddd19917ce725ecd5fa31892e40a09e) // permutation_comms[2].x_lo
            mstore(add(payload, 0x3ac0), 0x00000000000000000000000000000000174e7aa2baaa6b5b3d6cf3f2a28fcb7b) // permutation_comms[2].y_hi
            mstore(add(payload, 0x3ae0), 0x9c2899c633120ad28ff9db1741594e2269e44f7cbb8febe2ecefff2db90cc473) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3b00), 0x000000000000000000000000000000000fc4b14d2e3c92766e691e89d7d5420d) // permutation_comms[3].x_hi
            mstore(add(payload, 0x3b20), 0x5184c99a579d64ef3558a00dc5c9ba6e61f703576c398ac81c9b56bb287842b8) // permutation_comms[3].x_lo
            mstore(add(payload, 0x3b40), 0x0000000000000000000000000000000015c2e0a004863442f3897d04d7185e88) // permutation_comms[3].y_hi
            mstore(add(payload, 0x3b60), 0xd5b50c5ffebad189a4c0dec574a1f238f6e9e1560e3cbbe5a67d2fe52fdcda0e) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3b80), 0x0000000000000000000000000000000011d0471ed498902807470f368eb9848a) // permutation_comms[4].x_hi
            mstore(add(payload, 0x3ba0), 0x346e49391654a1baa122a30bdc35ffe102617dbaf5bb254e93109ebff52c5933) // permutation_comms[4].x_lo
            mstore(add(payload, 0x3bc0), 0x0000000000000000000000000000000014c6aca94ac2863c90dd9b1ffbc0f3f8) // permutation_comms[4].y_hi
            mstore(add(payload, 0x3be0), 0x0adad63bf5fed4f3c5dc53ed1094ade314e3709cf0807029d9ab7f90926091af) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3c00), 0x000000000000000000000000000000000fd08d0b24484f6fabcad175b645382d) // permutation_comms[5].x_hi
            mstore(add(payload, 0x3c20), 0x1f7662a2d23e88151cd9e1e7d378000e2755a51832cedc5f11a4d3aaa8716be0) // permutation_comms[5].x_lo
            mstore(add(payload, 0x3c40), 0x00000000000000000000000000000000099180301ee6a18931e999a019014065) // permutation_comms[5].y_hi
            mstore(add(payload, 0x3c60), 0xa588f4c62c572685cd06ba45014fae3b8e770987ea22cc92464cd69a4fece97f) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3c80), 0x0000000000000000000000000000000000986f7215a9b5e4bc69608acaeb755c) // permutation_comms[6].x_hi
            mstore(add(payload, 0x3ca0), 0xc0ed4dd7bd88976da07e9c47756f1c9b90ef494c5cc3031ac6c9b5570fe5c45d) // permutation_comms[6].x_lo
            mstore(add(payload, 0x3cc0), 0x0000000000000000000000000000000003658180fe0ac3ab217301cc34d2f9aa) // permutation_comms[6].y_hi
            mstore(add(payload, 0x3ce0), 0x04b19a3be7154ad43d1737fd1668783a7069648dfb24de83a6b13d7261001032) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3d00), 0x0000000000000000000000000000000007fbc806a6091debd94a272e0f8912d0) // permutation_comms[7].x_hi
            mstore(add(payload, 0x3d20), 0xea4e50d28d2358893f82f9e7fe238ae18b5dcd80f3c48c799e1d008b8528faad) // permutation_comms[7].x_lo
            mstore(add(payload, 0x3d40), 0x00000000000000000000000000000000037e3a2dbdd3db563e256abd9f2a7cd8) // permutation_comms[7].y_hi
            mstore(add(payload, 0x3d60), 0xf8c500ab684abbc66c6d2d70b5868abe8b7e5687d78294f1ee929dbd38dedcce) // permutation_comms[7].y_lo
            // Permutation commitment 8, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3d80), 0x00000000000000000000000000000000140d8858cc561fd6afcbccfeedd5dc76) // permutation_comms[8].x_hi
            mstore(add(payload, 0x3da0), 0x20dd7a435855772fac8557a9584d4fd4893080fba0a2803d9a1fd103340bf564) // permutation_comms[8].x_lo
            mstore(add(payload, 0x3dc0), 0x00000000000000000000000000000000136c5f72ec819316102706ed6c11a33e) // permutation_comms[8].y_hi
            mstore(add(payload, 0x3de0), 0x1ad01a10a736b291b58a68e53d0307ecb80f77dd592a86c297bd05caccb0af41) // permutation_comms[8].y_lo
            // Permutation commitment 9, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3e00), 0x0000000000000000000000000000000015729cefbcc59141c9692c20e8453fcb) // permutation_comms[9].x_hi
            mstore(add(payload, 0x3e20), 0x4e62c3f3f1bc1589ab5a7e23578dd50a95c4bdbe6d195bf4982bd6d3dc0fe4b4) // permutation_comms[9].x_lo
            mstore(add(payload, 0x3e40), 0x000000000000000000000000000000000123b3ce875e0a1b4fe55920ce321100) // permutation_comms[9].y_hi
            mstore(add(payload, 0x3e60), 0x022cf7f7040d9ce1890bdf9c7cfb814e83108c4f2e92e7244d157a2d9b2b00bf) // permutation_comms[9].y_lo
            // Permutation commitment 10, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3e80), 0x000000000000000000000000000000001888bad3ba90802d54a0937805007049) // permutation_comms[10].x_hi
            mstore(add(payload, 0x3ea0), 0x1cdd8f30f9e23cf5c9e453c12022ec87ab87cfb34daf555f5a5c522b7ce8f1bc) // permutation_comms[10].x_lo
            mstore(add(payload, 0x3ec0), 0x000000000000000000000000000000000de916c0b775cb4eb98bfeb3dfad4967) // permutation_comms[10].y_hi
            mstore(add(payload, 0x3ee0), 0x58f8f1d29a7fa2d00f8fb1eb5753a548da8d75ae986c789d39da5ac2dae02a53) // permutation_comms[10].y_lo
            // Permutation commitment 11, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3f00), 0x00000000000000000000000000000000053762fc34a47bbe32d6fad79a9ea896) // permutation_comms[11].x_hi
            mstore(add(payload, 0x3f20), 0xb9638b617e16565b4a4558d09029cf7d96d6e8ab0f836215dbc82c102b155432) // permutation_comms[11].x_lo
            mstore(add(payload, 0x3f40), 0x000000000000000000000000000000000487f86403f09dc8d5df1d75f4101fd0) // permutation_comms[11].y_hi
            mstore(add(payload, 0x3f60), 0x97999483a9048868583d82ff6e4b6361ea2fe06d8e26c0f6e426aa22d0bda09d) // permutation_comms[11].y_lo
            // Permutation commitment 12, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3f80), 0x00000000000000000000000000000000050f008e185c195727754b694c000bd4) // permutation_comms[12].x_hi
            mstore(add(payload, 0x3fa0), 0xe7c7913d32906f924fe1f7eee842905cde425696e5a806cf8911a93e79e630b9) // permutation_comms[12].x_lo
            mstore(add(payload, 0x3fc0), 0x0000000000000000000000000000000017595272f221df8bea12df29dd9af257) // permutation_comms[12].y_hi
            mstore(add(payload, 0x3fe0), 0x5ddd466530e0daf1a64ce08dce1cdf459abde6c0c3fc1362219d5a1dc2364497) // permutation_comms[12].y_lo
            // Permutation commitment 13, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4000), 0x000000000000000000000000000000000d79ba73856c257ef12f910759d89be3) // permutation_comms[13].x_hi
            mstore(add(payload, 0x4020), 0x0ece14dca2a34d81ec196cd53b53532238fe0b1c53a21c752b8c15222cf7ca91) // permutation_comms[13].x_lo
            mstore(add(payload, 0x4040), 0x000000000000000000000000000000000e97dd50c8c8e708f28f1a49cae1bca8) // permutation_comms[13].y_hi
            mstore(add(payload, 0x4060), 0x986b74b25e15c4070613d2114ed26bcbb5265962c7daa46c006846bb72094987) // permutation_comms[13].y_lo
            // Permutation commitment 14, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4080), 0x000000000000000000000000000000001907b1ea8b50437251c2f6c5c8f65fca) // permutation_comms[14].x_hi
            mstore(add(payload, 0x40a0), 0xc7ede522e9608f63a30417e6db49f6a458b20ebbf0bfbb26e8949080446ad45a) // permutation_comms[14].x_lo
            mstore(add(payload, 0x40c0), 0x000000000000000000000000000000000f2a06c357ba6525f1c2181f46c1a6da) // permutation_comms[14].y_hi
            mstore(add(payload, 0x40e0), 0xa7d45b89925016f4b17350f281ca93fb4d164d432a9f0f6419e613e64e7a6de7) // permutation_comms[14].y_lo
            // Permutation commitment 15, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4100), 0x0000000000000000000000000000000006f40a2b9f0177cb6be6c5d46bcbc586) // permutation_comms[15].x_hi
            mstore(add(payload, 0x4120), 0x0cfdffd0db8cf2a9be3637689dc883abd4a6b0cc23226354b4d8b1f36e084ccc) // permutation_comms[15].x_lo
            mstore(add(payload, 0x4140), 0x0000000000000000000000000000000004e277867ebee679d6937e134b31d623) // permutation_comms[15].y_hi
            mstore(add(payload, 0x4160), 0x54004b36223d0cd437966d91b2aec628114db8f1f8c4719effdd687fa554c07e) // permutation_comms[15].y_lo
            // Permutation commitment 16, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4180), 0x00000000000000000000000000000000026f1a1cb3133c63d253ae68312f83df) // permutation_comms[16].x_hi
            mstore(add(payload, 0x41a0), 0xa0ac92b7e22e896a8e15730129f9e39fd0dd4d74c9b531736b2fb17c857f5ee1) // permutation_comms[16].x_lo
            mstore(add(payload, 0x41c0), 0x00000000000000000000000000000000169947370b2df78d4e6066ab4bd2e28f) // permutation_comms[16].y_hi
            mstore(add(payload, 0x41e0), 0x49dcf9f7b2cbd0b6ac5c13b59fa78eea62d787fdc6bd13a417939292cdb0e93c) // permutation_comms[16].y_lo
            // Permutation commitment 17, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4200), 0x000000000000000000000000000000000985088cf2983bdb3d92e867278320f6) // permutation_comms[17].x_hi
            mstore(add(payload, 0x4220), 0xeaaf915109cea032c18ac23a369f5dc2f996e661592c063453710ac4a226901f) // permutation_comms[17].x_lo
            mstore(add(payload, 0x4240), 0x00000000000000000000000000000000133cf65a7c89b8a6f0ef41dd1966bc30) // permutation_comms[17].y_hi
            mstore(add(payload, 0x4260), 0xb7951c76a5bd9057c0d16581bb5d302327c24caf331a3c7caa6fc162965fb2c3) // permutation_comms[17].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x4281)
        }
    }
}