// SPDX-License-Identifier: CC0-1.0

pragma solidity ^0.8.24;

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
            mstore(add(payload, 0x0000), 0x04d431b03dc86a4ddf0aef1f258576d6df8e1b884a7aa7564fea2df1b04a0f86) // vk_digest
            mstore(add(payload, 0x0020), 0x000000000000000000000000000000000000000000000000000000000000000e) // num_instances
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
            mstore(add(payload, 0x1a20), 0x058560108a8005860008060d000b02000105852011852011852005858008060d) // quotient_program
            mstore(add(payload, 0x1a40), 0x000b0300000585401185401185400585a008060d000b03000105856011856011) // quotient_program
            mstore(add(payload, 0x1a60), 0x856005862008060d000b0300011b00001b000105860008108b20058520118520) // quotient_program
            mstore(add(payload, 0x1a80), 0x1185800d01060585401185401185a00d02060585601185601186200d03060d00) // quotient_program
            mstore(add(payload, 0x1aa0), 0x0b0300011b000221020403070002000085200585400685600785800885a00085) // quotient_program
            mstore(add(payload, 0x1ac0), 0xc00585e00686000986200a86400b86600c86800d86a00e86c00f86e010870011) // quotient_program
            mstore(add(payload, 0x1ae0), 0x87200787400887600987800a87a085200085c00585e006860007874008876009) // quotient_program
            mstore(add(payload, 0x1b00), 0x87800a87a085400585c00685e00786000887400987600a87801287a085600685) // quotient_program
            mstore(add(payload, 0x1b20), 0xc00785e00886000987400a87601287801387a085800785c00885e00986000a87) // quotient_program
            mstore(add(payload, 0x1b40), 0x401287601387801487a085a00885c00985e00a86001287401387601487801587) // quotient_program
            mstore(add(payload, 0x1b60), 0xa086200985c00a85e01286001387401487601587801687a086400a85c01285e0) // quotient_program
            mstore(add(payload, 0x1b80), 0x1386001487401587601687801787a01887c01988000b04000121021a03070001) // quotient_program
            mstore(add(payload, 0x1ba0), 0x000085200585400685601b85801c85a00085c00585e00686001d86201e86400b) // quotient_program
            mstore(add(payload, 0x1bc0), 0x86600c86800d86a01f86c02086e02187002287201b87401c87601d87801e87a0) // quotient_program
            mstore(add(payload, 0x1be0), 0x85200085c00585e00686001b87401c87601d87801e87a085400585c00685e01b) // quotient_program
            mstore(add(payload, 0x1c00), 0x86001c87401d87601e87802387a085600685c01b85e01c86001d87401e876023) // quotient_program
            mstore(add(payload, 0x1c20), 0x87802487a085801b85c01c85e01d86001e87402387602487802587a085a01c85) // quotient_program
            mstore(add(payload, 0x1c40), 0xc01d85e01e86002387402487602587802687a086201d85c01e85e02386002487) // quotient_program
            mstore(add(payload, 0x1c60), 0x402587602687802787a086401e85c02385e02486002587402687602787802887) // quotient_program
            mstore(add(payload, 0x1c80), 0xa02987c00b0400011b000321022a01000009000986200a86400b86600c86800d) // quotient_program
            mstore(add(payload, 0x1ca0), 0x86a00e86c00f86e00085200585400685600785800885a01087001187201887c0) // quotient_program
            mstore(add(payload, 0x1cc0), 0x1988000b05000121022b01000008001d86201e86400b86600c86800d86a01f86) // quotient_program
            mstore(add(payload, 0x1ce0), 0xc02086e00085200585400685601b85801c85a02187002287202987c00b050001) // quotient_program
            mstore(add(payload, 0x1d00), 0x210388202c0000000b2b0b85200c85400d85602d85c02e85e02f86000b86600c) // quotient_program
            mstore(add(payload, 0x1d20), 0x86800d86a03087c03187e00b852086600c852086800d852086a00c854086600d) // quotient_program
            mstore(add(payload, 0x1d40), 0x8540868032854087200d856086603285608700338560872032858086e0338580) // quotient_program
            mstore(add(payload, 0x1d60), 0x870034858087203285a086c03385a086e03485a087003585a087200085c085c0) // quotient_program
            mstore(add(payload, 0x1d80), 0x2e85c085e02f85c086000685e085e03685e087a0368600878037860087a03286) // quotient_program
            mstore(add(payload, 0x1da0), 0x2086a033862086c034862086e035862087003886208720328640868033864086) // quotient_program
            mstore(add(payload, 0x1dc0), 0xa034864086c035864086e038864087003986408720368740876037874087803a) // quotient_program
            mstore(add(payload, 0x1de0), 0x874087a03b876087603a876087803c876087a03d878087803e878087a03f87a0) // quotient_program
            mstore(add(payload, 0x1e00), 0x87a00d000b060000210388204003080002150b85200c85400d85600e85800f85) // quotient_program
            mstore(add(payload, 0x1e20), 0xa02d85c02e85e02f86001086201186400b86600c86800d86a00e86c00f86e010) // quotient_program
            mstore(add(payload, 0x1e40), 0x87001187204187404287604387804487a085200b86600c86800d86a00e86c00f) // quotient_program
            mstore(add(payload, 0x1e60), 0x86e010870011872085400c86600d86800e86a00f86c01086e011870045872085) // quotient_program
            mstore(add(payload, 0x1e80), 0x600d86600e86800f86a01086c01186e045870046872085800e86600f86801086) // quotient_program
            mstore(add(payload, 0x1ea0), 0xa01186c04586e046870047872085a00f86601086801186a04586c04686e04787) // quotient_program
            mstore(add(payload, 0x1ec0), 0x0048872085c00085c02e85e02f86004187404287604387804487a08620108660) // quotient_program
            mstore(add(payload, 0x1ee0), 0x1186804586a04686c04786e048870049872086401186604586804686a04786c0) // quotient_program
            mstore(add(payload, 0x1f00), 0x4886e04987004a87201887c01988000685e085e04185e086004285e087404385) // quotient_program
            mstore(add(payload, 0x1f20), 0xe087604485e087804b85e087a00886008600438600874044860087604b860087) // quotient_program
            mstore(add(payload, 0x1f40), 0x804c860087a00a874087404b874087604c874087804d874087a013876087604d) // quotient_program
            mstore(add(payload, 0x1f60), 0x876087804e876087a015878087804f878087a01787a087a00d000b0600012103) // quotient_program
            mstore(add(payload, 0x1f80), 0x88205003080001150b85200c85400d85601f85802085a02d85c02e85e02f8600) // quotient_program
            mstore(add(payload, 0x1fa0), 0x2186202286400b86600c86800d86a01f86c02086e02187002287205187405287) // quotient_program
            mstore(add(payload, 0x1fc0), 0x605387805487a085200b86600c86800d86a01f86c02086e02187002287208540) // quotient_program
            mstore(add(payload, 0x1fe0), 0x0c86600d86801f86a02086c02186e022870055872085600d86601f86802086a0) // quotient_program
            mstore(add(payload, 0x2000), 0x2186c02286e055870056872085801f86602086802186a02286c05586e0568700) // quotient_program
            mstore(add(payload, 0x2020), 0x57872085a02086602186802286a05586c05686e057870058872085c00085c02e) // quotient_program
            mstore(add(payload, 0x2040), 0x85e02f86005187405287605387805487a086202186602286805586a05686c057) // quotient_program
            mstore(add(payload, 0x2060), 0x86e058870059872086402286605586805686a05786c05886e05987005a872029) // quotient_program
            mstore(add(payload, 0x2080), 0x87c00685e085e05185e086005285e087405385e087605485e087805b85e087a0) // quotient_program
            mstore(add(payload, 0x20a0), 0x1c86008600538600874054860087605b860087805c860087a01e874087405b87) // quotient_program
            mstore(add(payload, 0x20c0), 0x4087605c874087805d874087a024876087605d876087805e876087a026878087) // quotient_program
            mstore(add(payload, 0x20e0), 0x805f878087a02887a087a00d000b06000121038820600000000c390b85200c85) // quotient_program
            mstore(add(payload, 0x2100), 0x400d85603087c03187e00088200088400588600688800b89200c89400d896000) // quotient_program
            mstore(add(payload, 0x2120), 0x85c088400585c088600685c088800b85c089200c85c089400d85c089600585e0) // quotient_program
            mstore(add(payload, 0x2140), 0x88400685e088606185e089000c85e089200d85e089403285e089e00686008840) // quotient_program
            mstore(add(payload, 0x2160), 0x61860088e03b860089000d8600892032860089c033860089e000866088200586) // quotient_program
            mstore(add(payload, 0x2180), 0x8088200686a0882061874088c03b874088e0628740890032874089a033874089) // quotient_program
            mstore(add(payload, 0x21a0), 0xc034874089e061876088a03b876088c062876088e03d87608900328760898033) // quotient_program
            mstore(add(payload, 0x21c0), 0x876089a034876089c035876089e061878088803b878088a062878088c03d8780) // quotient_program
            mstore(add(payload, 0x21e0), 0x88e063878089003287808960338780898034878089a035878089c038878089e0) // quotient_program
            mstore(add(payload, 0x2200), 0x6187a088603b87a088806287a088a03d87a088c06387a088e03f87a089003287) // quotient_program
            mstore(add(payload, 0x2220), 0xa089403387a089603487a089803587a089a03887a089c03987a089e00d000b07) // quotient_program
            mstore(add(payload, 0x2240), 0x00002103882064020f000a001988000088200088400588600688800788a00888) // quotient_program
            mstore(add(payload, 0x2260), 0xc00988e00a89000b89200c89400d89600e89800f89a088200086600586800686) // quotient_program
            mstore(add(payload, 0x2280), 0xa00786c00886e00987000a872088400085c00585e00686000787400887600987) // quotient_program
            mstore(add(payload, 0x22a0), 0x800a87a088600585c00685e00786000887400987600a87801287a088800685c0) // quotient_program
            mstore(add(payload, 0x22c0), 0x0785e00886000987400a87601287801387a088a00785c00885e00986000a8740) // quotient_program
            mstore(add(payload, 0x22e0), 0x1287601387801487a088c00885c00985e00a86001287401387601487801587a0) // quotient_program
            mstore(add(payload, 0x2300), 0x88e00985c00a85e01286001387401487601587801687a089000a85c01285e013) // quotient_program
            mstore(add(payload, 0x2320), 0x86001487401587601687801787a085c00b89200c89400d89600e89800f89a010) // quotient_program
            mstore(add(payload, 0x2340), 0x89c01189e085e00c89200d89400e89600f89801089a01189c04589e086000d89) // quotient_program
            mstore(add(payload, 0x2360), 0x200e89400f89601089801189a04589c04689e087400e89200f89401089601189) // quotient_program
            mstore(add(payload, 0x2380), 0x804589a04689c04789e087600f89201089401189604589804689a04789c04889) // quotient_program
            mstore(add(payload, 0x23a0), 0xe087801089201189404589604689804789a04889c04989e087a0118920458940) // quotient_program
            mstore(add(payload, 0x23c0), 0x4689604789804889a04989c04a89e00b85200c85400d85600e85800f85a01086) // quotient_program
            mstore(add(payload, 0x23e0), 0x201186401887c01089c01189e00d000b0700012103882065020f000900008820) // quotient_program
            mstore(add(payload, 0x2400), 0x0088400588600688801b88a01c88c01d88e01e89000b89200c89400d89601f89) // quotient_program
            mstore(add(payload, 0x2420), 0x802089a02189c088200086600586800686a01b86c01c86e01d87001e87208840) // quotient_program
            mstore(add(payload, 0x2440), 0x0085c00585e00686001b87401c87601d87801e87a088600585c00685e01b8600) // quotient_program
            mstore(add(payload, 0x2460), 0x1c87401d87601e87802387a088800685c01b85e01c86001d87401e8760238780) // quotient_program
            mstore(add(payload, 0x2480), 0x2487a088a01b85c01c85e01d86001e87402387602487802587a088c01c85c01d) // quotient_program
            mstore(add(payload, 0x24a0), 0x85e01e86002387402487602587802687a088e01d85c01e85e023860024874025) // quotient_program
            mstore(add(payload, 0x24c0), 0x87602687802787a089001e85c02385e02486002587402687602787802887a085) // quotient_program
            mstore(add(payload, 0x24e0), 0xc00b89200c89400d89601f89802089a02189c02289e085e00c89200d89401f89) // quotient_program
            mstore(add(payload, 0x2500), 0x602089802189a02289c05589e086000d89201f89402089602189802289a05589) // quotient_program
            mstore(add(payload, 0x2520), 0xc05689e087401f89202089402189602289805589a05689c05789e08760208920) // quotient_program
            mstore(add(payload, 0x2540), 0x2189402289605589805689a05789c05889e08780218920228940558960568980) // quotient_program
            mstore(add(payload, 0x2560), 0x5789a05889c05989e087a02289205589405689605789805889a05989c05a89e0) // quotient_program
            mstore(add(payload, 0x2580), 0x0b85200c85400d85601f85802085a02186202286402987c02289e00d000b0700) // quotient_program
            mstore(add(payload, 0x25a0), 0x0121038820660000000b2b6785206885406985606a85c06b85e06c86006a8660) // quotient_program
            mstore(add(payload, 0x25c0), 0x6b86806c86a03087c03187e06d85208520688520854069852085606e85408540) // quotient_program
            mstore(add(payload, 0x25e0), 0x6f854086406f8560862070856086406f858085a0708580862071858086407285) // quotient_program
            mstore(add(payload, 0x2600), 0xa085a07185a086207385a086406a85c086606b85c086806c85c086a06b85e086) // quotient_program
            mstore(add(payload, 0x2620), 0x606c85e086807485e087206c8600866074860087007586008720768620862077) // quotient_program
            mstore(add(payload, 0x2640), 0x86208640788640864074868087a07486a087807586a087a07486c087607586c0) // quotient_program
            mstore(add(payload, 0x2660), 0x87807986c087a07486e087407586e087607986e087807a86e087a07587008740) // quotient_program
            mstore(add(payload, 0x2680), 0x79870087607a870087807b870087a079872087407a872087607b872087807c87) // quotient_program
            mstore(add(payload, 0x26a0), 0x2087a00d000b080000210388207d03080002156785206885406985607e85807f) // quotient_program
            mstore(add(payload, 0x26c0), 0x85a06a85c06b85e06c86008086208186406a86606b86806c86a08286c08386e0) // quotient_program
            mstore(add(payload, 0x26e0), 0x8487008587208287408387608487808587a085206d85206885406985607e8580) // quotient_program
            mstore(add(payload, 0x2700), 0x7f85a080862081864085c06a86606b86806c86a08286c08386e0848700858720) // quotient_program
            mstore(add(payload, 0x2720), 0x85e06b86606c86808286a08386c08486e085870086872086006c866082868083) // quotient_program
            mstore(add(payload, 0x2740), 0x86a08486c08586e086870087872087408286608386808486a08586c08686e087) // quotient_program
            mstore(add(payload, 0x2760), 0x870088872087608386608486808586a08686c08786e088870089872087808486) // quotient_program
            mstore(add(payload, 0x2780), 0x608586808686a08786c08886e08987008a872087a08586608686808786a08886) // quotient_program
            mstore(add(payload, 0x27a0), 0xc08986e08a87008b87201887c01988006e854085407e854085607f8540858080) // quotient_program
            mstore(add(payload, 0x27c0), 0x854085a081854086208c854086408d85608560808560858081856085a08c8560) // quotient_program
            mstore(add(payload, 0x27e0), 0x86208e856086408f858085808c858085a08e8580862090858086409185a085a0) // quotient_program
            mstore(add(payload, 0x2800), 0x9085a086209285a086409386208620948620864095864086400d000b08000121) // quotient_program
            mstore(add(payload, 0x2820), 0x0388209603080001156785206885406985609785809885a06a85c06b85e06c86) // quotient_program
            mstore(add(payload, 0x2840), 0x009986209a86406a86606b86806c86a09b86c09c86e09d87009e87209b87409c) // quotient_program
            mstore(add(payload, 0x2860), 0x87609d87809e87a085206d85206885406985609785809885a09986209a864085) // quotient_program
            mstore(add(payload, 0x2880), 0xc06a86606b86806c86a09b86c09c86e09d87009e872085e06b86606c86809b86) // quotient_program
            mstore(add(payload, 0x28a0), 0xa09c86c09d86e09e87009f872086006c86609b86809c86a09d86c09e86e09f87) // quotient_program
            mstore(add(payload, 0x28c0), 0x00a0872087409b86609c86809d86a09e86c09f86e0a08700a1872087609c8660) // quotient_program
            mstore(add(payload, 0x28e0), 0x9d86809e86a09f86c0a086e0a18700a2872087809d86609e86809f86a0a086c0) // quotient_program
            mstore(add(payload, 0x2900), 0xa186e0a28700a3872087a09e86609f8680a086a0a186c0a286e0a38700a48720) // quotient_program
            mstore(add(payload, 0x2920), 0x2987c06e854085409785408560988540858099854085a09a85408620a5854086) // quotient_program
            mstore(add(payload, 0x2940), 0x40a68560856099856085809a856085a0a585608620a785608640a885808580a5) // quotient_program
            mstore(add(payload, 0x2960), 0x858085a0a785808620a985808640aa85a085a0a985a08620ab85a08640ac8620) // quotient_program
            mstore(add(payload, 0x2980), 0x8620ad86208640ae864086400d000b08000121038820af0000000e1000852005) // quotient_program
            mstore(add(payload, 0x29a0), 0x85400685606a85c06b85e06c86000086600586800686a03087c03187e0008840) // quotient_program
            mstore(add(payload, 0x29c0), 0x0588600688800b85c085c06b85c085e06c85c086000d85e085e07485e087a074) // quotient_program
            mstore(add(payload, 0x29e0), 0x8600878075860087a07487408760758740878079874087a03387608760798760) // quotient_program
            mstore(add(payload, 0x2a00), 0x87807a876087a035878087807b878087a03987a087a00d000b09000021038820) // quotient_program
            mstore(add(payload, 0x2a20), 0xb004010002150085200585400685600785800885a06a85c06b85e06c86000986) // quotient_program
            mstore(add(payload, 0x2a40), 0x200a86400086600586800686a00786c00886e00987000a872082874083876084) // quotient_program
            mstore(add(payload, 0x2a60), 0x87808587a00088400588600688800788a00888c00988e00a890085c00b85c06b) // quotient_program
            mstore(add(payload, 0x2a80), 0x85e06c86008287408387608487808587a01887c01988000d85e085e08285e086) // quotient_program
            mstore(add(payload, 0x2aa0), 0x008385e087408485e087608585e087808685e087a00f86008600848600874085) // quotient_program
            mstore(add(payload, 0x2ac0), 0x86008760868600878087860087a0118740874086874087608787408780888740) // quotient_program
            mstore(add(payload, 0x2ae0), 0x87a04687608760888760878089876087a048878087808a878087a04a87a087a0) // quotient_program
            mstore(add(payload, 0x2b00), 0x0d000b09000121038820b104010001150085200585400685601b85801c85a06a) // quotient_program
            mstore(add(payload, 0x2b20), 0x85c06b85e06c86001d86201e86400086600586800686a01b86c01c86e01d8700) // quotient_program
            mstore(add(payload, 0x2b40), 0x1e87209b87409c87609d87809e87a00088400588600688801b88a01c88c01d88) // quotient_program
            mstore(add(payload, 0x2b60), 0xe01e890085c00b85c06b85e06c86009b87409c87609d87809e87a02987c00d85) // quotient_program
            mstore(add(payload, 0x2b80), 0xe085e09b85e086009c85e087409d85e087609e85e087809f85e087a020860086) // quotient_program
            mstore(add(payload, 0x2ba0), 0x009d860087409e860087609f86008780a0860087a022874087409f87408760a0) // quotient_program
            mstore(add(payload, 0x2bc0), 0x87408780a1874087a05687608760a187608780a2876087a05887808780a38780) // quotient_program
            mstore(add(payload, 0x2be0), 0x87a05a87a087a00d000b090001191f0000000000000000000000000000000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2c00), 0x00000000000000000000000000000000055f7961345dce7ce57401dd993cc81a) // fixed_comms[0].x_hi
            mstore(add(payload, 0x2c20), 0xb4a8bb072416d10d143dbceefaa489acea245ef19b9b96fef5bf433eb3a11715) // fixed_comms[0].x_lo
            mstore(add(payload, 0x2c40), 0x00000000000000000000000000000000123e8a257be057ec25558c37e4b17ce9) // fixed_comms[0].y_hi
            mstore(add(payload, 0x2c60), 0x8e3b8e47d06f0961e4194860938f70e8f8f29e6c09dc697cb5c3486879220eaf) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2c80), 0x000000000000000000000000000000000dc17ef381e9c195813396905a4c7619) // fixed_comms[1].x_hi
            mstore(add(payload, 0x2ca0), 0x326e62da20d14e245cf995ae353e85749ad599d8859cdf7ff0996b64ad724553) // fixed_comms[1].x_lo
            mstore(add(payload, 0x2cc0), 0x0000000000000000000000000000000004af0ea1ccdc1cd0a2a638aa09f6e2ae) // fixed_comms[1].y_hi
            mstore(add(payload, 0x2ce0), 0xe2fe34ad7bd96fb709c73d2d9705c120c1c78c8702fc136bcecb58a6efc4353d) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2d00), 0x0000000000000000000000000000000018da87ffd53a1cdfc243a1f594c7db5f) // fixed_comms[2].x_hi
            mstore(add(payload, 0x2d20), 0x6a20adfd78c0e9d2dd4a3377189dcaf31f886eecc6bcfd19d7263ff57b36c01e) // fixed_comms[2].x_lo
            mstore(add(payload, 0x2d40), 0x0000000000000000000000000000000001921c576e8a2684cc7521fbf6ec96c3) // fixed_comms[2].y_hi
            mstore(add(payload, 0x2d60), 0xde86625c4429546e64909b0f415e9b7bcff50f6e96df84f795a6bf7c3fd0e085) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2d80), 0x000000000000000000000000000000001390c4b48f0af2e2a9332b1851fbb5d1) // fixed_comms[3].x_hi
            mstore(add(payload, 0x2da0), 0xe13c168e64b12da23a13fb7b449e2f8d38dd385220d9a9cc7af8c1cb5d7e7364) // fixed_comms[3].x_lo
            mstore(add(payload, 0x2dc0), 0x0000000000000000000000000000000019b9ac80c33724396a9da36abc8884bc) // fixed_comms[3].y_hi
            mstore(add(payload, 0x2de0), 0x9adb1d0bf586080efd6ffd8520aab78d8d205c0a11726db029aecc899111d9a9) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2e00), 0x0000000000000000000000000000000015bc72a82a34331b999a01881b5c4b3b) // fixed_comms[4].x_hi
            mstore(add(payload, 0x2e20), 0xb138f213ddd19ae669c32f961811a4164e6eec8fac46a36f5a4e04870f11a3d1) // fixed_comms[4].x_lo
            mstore(add(payload, 0x2e40), 0x00000000000000000000000000000000197b5b9237d51d93dc155332b6330653) // fixed_comms[4].y_hi
            mstore(add(payload, 0x2e60), 0xef5fa3e86ca7b8acaf6cb32697d8ececfbdac8b2ffe2f53e47bdc8ba9e3993b6) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2e80), 0x0000000000000000000000000000000013eb9d933b5284bfef6caf1f9e08ca59) // fixed_comms[5].x_hi
            mstore(add(payload, 0x2ea0), 0x283ea2dbd92fc9a748e3761fff443680718b50347a55be560c0229972f7e0a24) // fixed_comms[5].x_lo
            mstore(add(payload, 0x2ec0), 0x000000000000000000000000000000001100235c0764123ef1a72a76e2abc95c) // fixed_comms[5].y_hi
            mstore(add(payload, 0x2ee0), 0x8af88c99dda9239bf71fca4d07b5fee527d576ad79c679035b5836347686d74b) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2f00), 0x000000000000000000000000000000000563bb1e4b8d6ac080403aa94fe32b7d) // fixed_comms[6].x_hi
            mstore(add(payload, 0x2f20), 0xe1921a07b4a8ade8f03fbf6079d44191250a74ad822758d3f3c76ac1dcf34844) // fixed_comms[6].x_lo
            mstore(add(payload, 0x2f40), 0x000000000000000000000000000000001660e1d7dc487ef2074c1cbcc53f96c4) // fixed_comms[6].y_hi
            mstore(add(payload, 0x2f60), 0x90a10debafc892aa61fc1f5deccbe9e504f860b20ab154069fc7d9db6abd4b8c) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2f80), 0x0000000000000000000000000000000011d8086a3a74772d6977655ec27ea545) // fixed_comms[7].x_hi
            mstore(add(payload, 0x2fa0), 0xb8f93c43434e29d5987c92a14aff1f1eaaf7301c5a7e3089af5e92d1f848d0ca) // fixed_comms[7].x_lo
            mstore(add(payload, 0x2fc0), 0x0000000000000000000000000000000005dad0d11cdc8ea706cfc3def7d4b133) // fixed_comms[7].y_hi
            mstore(add(payload, 0x2fe0), 0xc3589649c58c36b9396e7ba08d2dcce7e9ffc79c05293e88ffdcd779031bd430) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3000), 0x000000000000000000000000000000000c93bd7351261d64a616e0136a9d422b) // fixed_comms[8].x_hi
            mstore(add(payload, 0x3020), 0xb749e19c58376c59582349ad89c4cd137403a5708d9c57caa9aa60a61ebac5eb) // fixed_comms[8].x_lo
            mstore(add(payload, 0x3040), 0x000000000000000000000000000000000cbfb4f76cc2e2dd1cb5c3d5102d3b9a) // fixed_comms[8].y_hi
            mstore(add(payload, 0x3060), 0xd4a9cd56cbcb6df99c181927f6448f16319d629b8e456d7c82888b8ebff6605c) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3080), 0x0000000000000000000000000000000008727a8cb32cb038513549fb17b3ba8d) // fixed_comms[9].x_hi
            mstore(add(payload, 0x30a0), 0xd9695316ca607544e71a5430e6910b8fee65f6ad1a50f524c684c5e957c1c73e) // fixed_comms[9].x_lo
            mstore(add(payload, 0x30c0), 0x000000000000000000000000000000000108a6377aea32a5e3bbce056526f625) // fixed_comms[9].y_hi
            mstore(add(payload, 0x30e0), 0x33a146b087d572d2cdda900fca8baea1863367075e4b606110b6325be4397d52) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3100), 0x0000000000000000000000000000000004757ce24e0add6ba492d720099e2fbd) // fixed_comms[10].x_hi
            mstore(add(payload, 0x3120), 0xc54defd9e931ec5af33e4a92ad1867c2f4d790e30268a97b42e74f65d1d26feb) // fixed_comms[10].x_lo
            mstore(add(payload, 0x3140), 0x0000000000000000000000000000000010f63d4681250b4d2f91725c42a7993b) // fixed_comms[10].y_hi
            mstore(add(payload, 0x3160), 0xaa140dc9f52cc57f62aa46386e696d66b92a24406de6a8dfb053ebf589cd908b) // fixed_comms[10].y_lo
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
            mstore(add(payload, 0x3280), 0x0000000000000000000000000000000019d8a32c4ce7586146ff1ba0ac184d1e) // fixed_comms[13].x_hi
            mstore(add(payload, 0x32a0), 0x8263acc4da9e972d5b111879f60990df5070a38e99c93a8e9f52e94ffc5e889e) // fixed_comms[13].x_lo
            mstore(add(payload, 0x32c0), 0x00000000000000000000000000000000027e571331ef494a3859d52330b48271) // fixed_comms[13].y_hi
            mstore(add(payload, 0x32e0), 0x9386739b55372fd11694634dc2fe32fc5ed8a01fbe87cdbbcfacb4aed4903fc3) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3300), 0x00000000000000000000000000000000017d226d304f23f7f52ffe5adadcaca9) // fixed_comms[14].x_hi
            mstore(add(payload, 0x3320), 0x54a9d37b66adcd661144899193c80d6d365b30bd133f0bd5a60c12da38b4685e) // fixed_comms[14].x_lo
            mstore(add(payload, 0x3340), 0x000000000000000000000000000000000f485636ff7bd4a83beb91de87df7ed4) // fixed_comms[14].y_hi
            mstore(add(payload, 0x3360), 0x4757ccb9b4c2999112e89a82d9c72579b1d0020cdda10f3e0b41bf57aec34686) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3380), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x_hi
            mstore(add(payload, 0x33a0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x_lo
            mstore(add(payload, 0x33c0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y_hi
            mstore(add(payload, 0x33e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3400), 0x0000000000000000000000000000000008fd1060bd58dfc0e828393d62e3aee0) // fixed_comms[16].x_hi
            mstore(add(payload, 0x3420), 0xfe8983d71d04414402f77df4de23f2a73b3c5c48ee85fa51fcd64a3027e0167b) // fixed_comms[16].x_lo
            mstore(add(payload, 0x3440), 0x000000000000000000000000000000001024eab25af80d874e553df0f690d9e3) // fixed_comms[16].y_hi
            mstore(add(payload, 0x3460), 0x634a41f5518caaaeee1dbc993ced1264ade8431a680d202247d83eb8ef1ed620) // fixed_comms[16].y_lo
            // Fixed-column commitment 17, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3480), 0x000000000000000000000000000000000b877a879e46bc947071a221c60797d8) // fixed_comms[17].x_hi
            mstore(add(payload, 0x34a0), 0x0d338c66213b76689a66c79be8734280510aa45f8c79ce0eaaba3d7f2c201c99) // fixed_comms[17].x_lo
            mstore(add(payload, 0x34c0), 0x000000000000000000000000000000000ffcad707a79c0b29c100d2ab1b60935) // fixed_comms[17].y_hi
            mstore(add(payload, 0x34e0), 0x2a2c605009875c39b73bb6d3e2216b305369028923566fc6ef2d22c8b74ce2bf) // fixed_comms[17].y_lo
            // Fixed-column commitment 18, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3500), 0x000000000000000000000000000000000d0d0b7c841523297c824431ffca522d) // fixed_comms[18].x_hi
            mstore(add(payload, 0x3520), 0xb24daa6cbd8c5f783501a4681bf7367e7aa5d71fca25234cd1a8f31ff24b9871) // fixed_comms[18].x_lo
            mstore(add(payload, 0x3540), 0x000000000000000000000000000000001396209d456313b44ec6d4a2fe5f434f) // fixed_comms[18].y_hi
            mstore(add(payload, 0x3560), 0xd5bd61218a04eaee084c376ade74d9bceba17fb9e12c2341581e5279596d7c97) // fixed_comms[18].y_lo
            // Fixed-column commitment 19, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3580), 0x00000000000000000000000000000000136cd0a2afc84eaecd680d24627d704f) // fixed_comms[19].x_hi
            mstore(add(payload, 0x35a0), 0x7e67e5d7fa3094f1aac03b8600277d394817f19fd0b0810dd2087b359429bf11) // fixed_comms[19].x_lo
            mstore(add(payload, 0x35c0), 0x0000000000000000000000000000000015cedd2e0ff3e776d58981915174cb65) // fixed_comms[19].y_hi
            mstore(add(payload, 0x35e0), 0x13bbf7d0f959d6be24d858ac4ae78c6b9ba0c80d69183a84cd73ec4e47693a14) // fixed_comms[19].y_lo
            // Fixed-column commitment 20, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3600), 0x0000000000000000000000000000000010e71146f473749481916e34fff2ba4a) // fixed_comms[20].x_hi
            mstore(add(payload, 0x3620), 0xd3e26bb933c011913f506f7892a36f43f7ba4f88b3f1c632e707bbffede7feb9) // fixed_comms[20].x_lo
            mstore(add(payload, 0x3640), 0x000000000000000000000000000000000982bd3e7a5ba58d468d0835936ad925) // fixed_comms[20].y_hi
            mstore(add(payload, 0x3660), 0xa3d7160336e586296b5e3742251d002e79d8d8d409bf94bafd09719f3ff0b382) // fixed_comms[20].y_lo
            // Fixed-column commitment 21, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3680), 0x00000000000000000000000000000000141c94b0741a3d6471b0dd59b3420d9e) // fixed_comms[21].x_hi
            mstore(add(payload, 0x36a0), 0xa03be602a9ebe7f1567966db7e3ace5a14ae393194015380293d1d995596651c) // fixed_comms[21].x_lo
            mstore(add(payload, 0x36c0), 0x000000000000000000000000000000000185758fd177d9c06fad9502b24ca417) // fixed_comms[21].y_hi
            mstore(add(payload, 0x36e0), 0x9cbb2dd41d7ede5248fb78316c557683f183c083b731a261a7381d45cf930742) // fixed_comms[21].y_lo
            // Fixed-column commitment 22, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3700), 0x0000000000000000000000000000000001e93db65a35232bfd9581766d6c5c59) // fixed_comms[22].x_hi
            mstore(add(payload, 0x3720), 0xa90a6d1906f94fc5643024253805f7a17b6fc2428bbe864add9dd8124518153c) // fixed_comms[22].x_lo
            mstore(add(payload, 0x3740), 0x000000000000000000000000000000001897a8f562cb20282c670eecf5f77249) // fixed_comms[22].y_hi
            mstore(add(payload, 0x3760), 0x4df0f2823207b6a3832a1b0d7987b20827e8416b563efbbfe212f510acf289df) // fixed_comms[22].y_lo
            // Fixed-column commitment 23, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3780), 0x000000000000000000000000000000001141339a865a8fc5477605fae30566b9) // fixed_comms[23].x_hi
            mstore(add(payload, 0x37a0), 0x7bd7c27d8d218efa4eb28c80916844e8ec5d47c7dc2f871545707f004b7bde50) // fixed_comms[23].x_lo
            mstore(add(payload, 0x37c0), 0x000000000000000000000000000000000a728fcbfa5a7a5bfae84b4ab18b83e6) // fixed_comms[23].y_hi
            mstore(add(payload, 0x37e0), 0xb10f17f88be257afb9d981d6516cfd2c4b3e89f5fa5ca13434fd95b24bc0f5c1) // fixed_comms[23].y_lo
            // Fixed-column commitment 24, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3800), 0x0000000000000000000000000000000002a788024d9035e7e40f601bb8082ff8) // fixed_comms[24].x_hi
            mstore(add(payload, 0x3820), 0x53ec39d899cd245ad2ee9ad32549a184d0c5cb4d4d99940a1cda52c4aa50f79d) // fixed_comms[24].x_lo
            mstore(add(payload, 0x3840), 0x0000000000000000000000000000000019a91d8fc2a4d3db45f22db05108197e) // fixed_comms[24].y_hi
            mstore(add(payload, 0x3860), 0x7eac8129c7add70a75761fd1e18fa2f40ea6e687a3f43b41995a2e74bf31ff24) // fixed_comms[24].y_lo
            // Fixed-column commitment 25, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3880), 0x0000000000000000000000000000000001442c60b19c670229debddb76233f20) // fixed_comms[25].x_hi
            mstore(add(payload, 0x38a0), 0x6a6627da0dc462833c112cdb1784e1f5f8a9aec196cf07b4442d408dbdc8de34) // fixed_comms[25].x_lo
            mstore(add(payload, 0x38c0), 0x0000000000000000000000000000000013f3b855645d02a97df448668efd5d7f) // fixed_comms[25].y_hi
            mstore(add(payload, 0x38e0), 0x8d52d302c0337d44e292fff6ae85d5a6dc5a59067e2a4f0925f48080dc521d40) // fixed_comms[25].y_lo
            // Fixed-column commitment 26, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3900), 0x00000000000000000000000000000000190429c7a977675dbb8d96b442fe3eb0) // fixed_comms[26].x_hi
            mstore(add(payload, 0x3920), 0xb466636ed724932185b8820e3f115e95ce19cde31f721358e32beda77fa44c98) // fixed_comms[26].x_lo
            mstore(add(payload, 0x3940), 0x00000000000000000000000000000000058d18d63ff3a3abf337b6edc6a7709a) // fixed_comms[26].y_hi
            mstore(add(payload, 0x3960), 0x36a019565bfbe01076597121c5484c2f3c63a301ed971058d75bb5d61b50bf05) // fixed_comms[26].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3980), 0x00000000000000000000000000000000120ea7ffaddae135109dc68a0169e39e) // permutation_comms[0].x_hi
            mstore(add(payload, 0x39a0), 0x17f95865ea6411611a36d6ee8affde13b3120990c5feff3a2dc32b1b71606512) // permutation_comms[0].x_lo
            mstore(add(payload, 0x39c0), 0x000000000000000000000000000000000d8604c2a5312ba81e5c56ad904e3fd3) // permutation_comms[0].y_hi
            mstore(add(payload, 0x39e0), 0xc73a292e67febcd994e3d882c050e50940bcd0364b49eaf0ea8c838123757e51) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3a00), 0x0000000000000000000000000000000012baec9d926370da0174d2da9125909f) // permutation_comms[1].x_hi
            mstore(add(payload, 0x3a20), 0x51c030289c7267c9173faacb20c43e027ba889a257fc9da7685fe92a1d8e1159) // permutation_comms[1].x_lo
            mstore(add(payload, 0x3a40), 0x00000000000000000000000000000000151c6bdabf6387e09e4ab927a972d0a5) // permutation_comms[1].y_hi
            mstore(add(payload, 0x3a60), 0x93e74bf9513d1d9be31b2d8828eb248d8b76fd529ee3d3343629b1327f47b74c) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3a80), 0x000000000000000000000000000000000502f4f83331ce4fe3b1e618b27af0d4) // permutation_comms[2].x_hi
            mstore(add(payload, 0x3aa0), 0xed1c9014937f4e0c989f42c2a22d0d54e395b1e6d35830f1681e7f7633bd5e48) // permutation_comms[2].x_lo
            mstore(add(payload, 0x3ac0), 0x00000000000000000000000000000000158fff4ecfaf728c449c4f9955fe87b1) // permutation_comms[2].y_hi
            mstore(add(payload, 0x3ae0), 0x8938d2b58f9f4325ad6c56ef82526e5d6bedff11dd4ef4730c55430e7ecc12b7) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3b00), 0x00000000000000000000000000000000157dbf7d9e1605bb29df570e4e4165d2) // permutation_comms[3].x_hi
            mstore(add(payload, 0x3b20), 0xe3af202d72afd27c2516ad10f0ef973f33dddb0fb0e34df741b4385b713cd1a8) // permutation_comms[3].x_lo
            mstore(add(payload, 0x3b40), 0x000000000000000000000000000000001227de928658870ba5ecaeae8dc6272e) // permutation_comms[3].y_hi
            mstore(add(payload, 0x3b60), 0x3c0f65f9d0e0daf9bcae0c8d2f61f4dfe5603cd4f9c2efe24c8bb68df6091f8b) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3b80), 0x00000000000000000000000000000000095679f4757e1699305ce877a6cede75) // permutation_comms[4].x_hi
            mstore(add(payload, 0x3ba0), 0xa7e634400e785e5c802142e6df51aa4b9d707d525cf7a80209699c36020b7971) // permutation_comms[4].x_lo
            mstore(add(payload, 0x3bc0), 0x00000000000000000000000000000000044f9e79c7622ffb279d558f84e0e7ec) // permutation_comms[4].y_hi
            mstore(add(payload, 0x3be0), 0x8355f52668f5832af0d5f80a018da5d9cf622b4ad414ef10eaad16f94ddc8def) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3c00), 0x000000000000000000000000000000000dc0d3a9a27cacb14bf99d6c879fc0f2) // permutation_comms[5].x_hi
            mstore(add(payload, 0x3c20), 0x92f80d3f8becaa901863aa7ca5b046bbe0f61b5da880eb4b1bb5b40ecf735d54) // permutation_comms[5].x_lo
            mstore(add(payload, 0x3c40), 0x00000000000000000000000000000000077a8a36b30f3ba3d444bc0427088640) // permutation_comms[5].y_hi
            mstore(add(payload, 0x3c60), 0x8840d2e5d575557d7495f63d40abf4b7daa04fc2bd662f6e299fc27aca5de4c5) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3c80), 0x0000000000000000000000000000000000986f7215a9b5e4bc69608acaeb755c) // permutation_comms[6].x_hi
            mstore(add(payload, 0x3ca0), 0xc0ed4dd7bd88976da07e9c47756f1c9b90ef494c5cc3031ac6c9b5570fe5c45d) // permutation_comms[6].x_lo
            mstore(add(payload, 0x3cc0), 0x0000000000000000000000000000000003658180fe0ac3ab217301cc34d2f9aa) // permutation_comms[6].y_hi
            mstore(add(payload, 0x3ce0), 0x04b19a3be7154ad43d1737fd1668783a7069648dfb24de83a6b13d7261001032) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3d00), 0x0000000000000000000000000000000001a53f321f3bf6d20af84c660efc018e) // permutation_comms[7].x_hi
            mstore(add(payload, 0x3d20), 0xa56fe987917489d477e3f2ac4da73c5a1e032748de091337870f0d5405473cd7) // permutation_comms[7].x_lo
            mstore(add(payload, 0x3d40), 0x000000000000000000000000000000000cc1da20073f989dd769a6d1003df07d) // permutation_comms[7].y_hi
            mstore(add(payload, 0x3d60), 0x5f354c49e670c02fcd04d732bf1dcf1ea91bf6fda6ccaf7b3884498827925ad7) // permutation_comms[7].y_lo
            // Permutation commitment 8, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3d80), 0x0000000000000000000000000000000006416291ebc77017412205eb4523f2c4) // permutation_comms[8].x_hi
            mstore(add(payload, 0x3da0), 0xfd559ac96201738085b756438d69e28d22d12d42527f26d4d076768379361baf) // permutation_comms[8].x_lo
            mstore(add(payload, 0x3dc0), 0x000000000000000000000000000000000d7c5e9e2123f1a9259e09115e8bcbde) // permutation_comms[8].y_hi
            mstore(add(payload, 0x3de0), 0x993cb20b6226d0b408d9ba2ea78f60939c10a918d0b706c0069e74ba1eeb7587) // permutation_comms[8].y_lo
            // Permutation commitment 9, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3e00), 0x00000000000000000000000000000000155b9dd46792d67982688c923afe6f78) // permutation_comms[9].x_hi
            mstore(add(payload, 0x3e20), 0xf0a9671faf2fbd90216a37854e9cc8f38a4e4e2edfbec79eabb17473cb14233a) // permutation_comms[9].x_lo
            mstore(add(payload, 0x3e40), 0x000000000000000000000000000000001136f0b77aaf0d619c1ab6b1f0dcee68) // permutation_comms[9].y_hi
            mstore(add(payload, 0x3e60), 0x5a362fa96be37353acf9f0ad8061c2da4ea54d0a983b25c140fff64eb5814a43) // permutation_comms[9].y_lo
            // Permutation commitment 10, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3e80), 0x00000000000000000000000000000000190c34b5f99861f6dfcdde40fbfd95d0) // permutation_comms[10].x_hi
            mstore(add(payload, 0x3ea0), 0x95a6bd47b58b054fe90452e3b358cd4dba6dd76fa6d5877d1ad1a6dc5f2c2ad7) // permutation_comms[10].x_lo
            mstore(add(payload, 0x3ec0), 0x00000000000000000000000000000000025a2fa63f92a2b0012325d053fb4dd7) // permutation_comms[10].y_hi
            mstore(add(payload, 0x3ee0), 0xeea7e8f98e3d57f1d404d8c6266072c77e1bf610f1b2d7e66a24c4eb5c7fa858) // permutation_comms[10].y_lo
            // Permutation commitment 11, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3f00), 0x0000000000000000000000000000000006dba7402f78627c2b84e3f197be1ff9) // permutation_comms[11].x_hi
            mstore(add(payload, 0x3f20), 0xe3b778c0de9938ede71f40c70a82c4b21e7f7e17f5ae37d8f431d8c56cb0cb7d) // permutation_comms[11].x_lo
            mstore(add(payload, 0x3f40), 0x0000000000000000000000000000000002f707f86413969433104530051e0e7f) // permutation_comms[11].y_hi
            mstore(add(payload, 0x3f60), 0xef774edc804973bdd3807446ef32363e657593d67b0460a33e76fc23d9feb998) // permutation_comms[11].y_lo
            // Permutation commitment 12, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3f80), 0x00000000000000000000000000000000116f8891da6e5ddfca44225df76baa02) // permutation_comms[12].x_hi
            mstore(add(payload, 0x3fa0), 0x795f3f817116f937e2102b4196eb86112a0d3290a6811fa1e7ada37bdcd91129) // permutation_comms[12].x_lo
            mstore(add(payload, 0x3fc0), 0x0000000000000000000000000000000012b7e92df964086ecd115e6b47daad77) // permutation_comms[12].y_hi
            mstore(add(payload, 0x3fe0), 0xcf396451a41cf55fa02fe68aaea4416953ad112a6608797bcc1f4a06ec6a786f) // permutation_comms[12].y_lo
            // Permutation commitment 13, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4000), 0x000000000000000000000000000000000c92a9011db64f5f7857340d5ecc0e76) // permutation_comms[13].x_hi
            mstore(add(payload, 0x4020), 0x6d6a2f4362053c3253503813a1a4167c6848cdbae2c90b104fc2a05290a24f78) // permutation_comms[13].x_lo
            mstore(add(payload, 0x4040), 0x00000000000000000000000000000000143212478a1a01c12e08520644d09291) // permutation_comms[13].y_hi
            mstore(add(payload, 0x4060), 0x4b417957d5c80179f30c06b68b329aa111de3f613cc66c70fd4841ec26139999) // permutation_comms[13].y_lo
            // Permutation commitment 14, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4080), 0x000000000000000000000000000000000a03f34520ffafc5b6a3f90f70e4e373) // permutation_comms[14].x_hi
            mstore(add(payload, 0x40a0), 0x673b3105b9864666ae11b398378b0648279065fc693c5edc4d42da133102545c) // permutation_comms[14].x_lo
            mstore(add(payload, 0x40c0), 0x00000000000000000000000000000000073205a58fda6d5adfd59e82867a548c) // permutation_comms[14].y_hi
            mstore(add(payload, 0x40e0), 0x80b028b16770d9a79d949f623d043d9aeff1cac440bd1482d1c898d7fc7bbbce) // permutation_comms[14].y_lo
            // Permutation commitment 15, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4100), 0x0000000000000000000000000000000008f70210c58006a3cb8b927287fa0bfb) // permutation_comms[15].x_hi
            mstore(add(payload, 0x4120), 0x55da954a29534ecb479d764e8ca977440dee39b3d09ebbe6b3fbb9c5b92cfe8b) // permutation_comms[15].x_lo
            mstore(add(payload, 0x4140), 0x0000000000000000000000000000000007285c63d0eadb56452c598285dfaa89) // permutation_comms[15].y_hi
            mstore(add(payload, 0x4160), 0x7d569c04ddbe85aa5deb978df472a328eb6db26586db41278f2cddeee55568cf) // permutation_comms[15].y_lo
            // Permutation commitment 16, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4180), 0x0000000000000000000000000000000019e4494289915c32cc82722cdf9cd7f2) // permutation_comms[16].x_hi
            mstore(add(payload, 0x41a0), 0xdc0187db7a50b887b1b5b2003c62effcf00f99c2a920ec56cfee0462655ac108) // permutation_comms[16].x_lo
            mstore(add(payload, 0x41c0), 0x000000000000000000000000000000001933cb285d7f70cc217fdf83c792d776) // permutation_comms[16].y_hi
            mstore(add(payload, 0x41e0), 0x527c8109795e8922038ac6a98e67c92d0fcb6e3a700e7ec2c0fa98cc1df52702) // permutation_comms[16].y_lo
            // Permutation commitment 17, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4200), 0x000000000000000000000000000000000485fd87bac44c42dc3c80fd042cc7d0) // permutation_comms[17].x_hi
            mstore(add(payload, 0x4220), 0xbb99316753b744e151e09c7f07e670300181f2f8e79a8b37c9828ac6be7a9573) // permutation_comms[17].x_lo
            mstore(add(payload, 0x4240), 0x000000000000000000000000000000000fd370bb45717fa6282230adcff6e4b6) // permutation_comms[17].y_hi
            mstore(add(payload, 0x4260), 0xab0ead4db625a61209a55551a96a3b5618f2996e645f09bbfda12ca3881536ac) // permutation_comms[17].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x4281)
        }
    }
}