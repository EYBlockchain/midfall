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
            mstore(add(payload, 0x0000), 0x56c0824fcff237dd8dc7b15f527346d9e1647d191815acb142500b0293e84f66) // vk_digest
            mstore(add(payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000013) // num_instances
            mstore(add(payload, 0x0040), 0x0000000000000000000000000000000000000000000000000000000000000014) // k
            mstore(add(payload, 0x0060), 0x73eda0144f284aae5b6554d46c21576b363d4ec725be2bff1a400fff00001001) // n_inv
            mstore(add(payload, 0x0080), 0x03e1c54bcb947035a57a6e07cb98de4a2f69e02d265e09d9fece7e0e39898d4b) // omega
            mstore(add(payload, 0x00a0), 0x6c39442eade0092768ac033fa6f608750624a1bb17dbc026ef97c3573a28fc8c) // omega_inv
            mstore(add(payload, 0x00c0), 0x2a0ccbaa0613f093f2bb6e97859513f0b613d8587eaa92db9e5604b8d6b68d45) // omega_inv_to_l
            mstore(add(payload, 0x00e0), 0x0000000000000000000000000000000000000000000000000000000000000001) // has_accumulator
            mstore(add(payload, 0x0100), 0x000000000000000000000000000000000000000000000000000000000000000b) // acc_offset
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
            mstore(add(payload, 0x02e0), 0x000000000000000000000000000000000632aaf712568f19c297802268a7ad9d) // neg_s_g2_x_c0_hi
            mstore(add(payload, 0x0300), 0xceea6ef7ab6f75a7d26781c8e90c7432bc5e99dcc219ba64010f3052123983ab) // neg_s_g2_x_c0_lo
            mstore(add(payload, 0x0320), 0x00000000000000000000000000000000191ff4920e077a2f8cb3969ba8f05bc2) // neg_s_g2_x_c1_hi
            mstore(add(payload, 0x0340), 0xaa9da8c95d640b1e051be7cf344ee7f01996df2568bf0e7ccd9eb70978820045) // neg_s_g2_x_c1_lo
            mstore(add(payload, 0x0360), 0x0000000000000000000000000000000005f434ebf45460a864ad5b17497c7903) // neg_s_g2_y_c0_hi
            mstore(add(payload, 0x0380), 0x71820c70c83aa186029536d22dff54373251152c28bc43269f95281eba1b012e) // neg_s_g2_y_c0_lo
            mstore(add(payload, 0x03a0), 0x0000000000000000000000000000000004d1c747141bcac15e77e3e1d3853254) // neg_s_g2_y_c1_hi
            mstore(add(payload, 0x03c0), 0xc8687afdad35345a04f79d9c2759007f6640676eb44aee7011ce5ad80744bb23) // neg_s_g2_y_c1_lo
            mstore(add(payload, 0x03e0), 0x0000000000000000000000000000000000000000000000000000000000000001) // quotient_const
            mstore(add(payload, 0x0400), 0x00bbe1fbe9ef1e2d62490b03a82bf9ef10f5e9b2323033669cf6c50481f63e05) // quotient_const
            mstore(add(payload, 0x0420), 0x0000000000000000000000000000000000000000000000000100000000000000) // quotient_const
            mstore(add(payload, 0x0440), 0x0000000000000000000000000000000000010000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0460), 0x0000000000000000000000000000000000000000000000000000000400000000) // quotient_const
            mstore(add(payload, 0x0480), 0x0000000000000000000000000000000000000000040000000000000000000000) // quotient_const
            mstore(add(payload, 0x04a0), 0x0000000000000000000000000000000000000000000000000000000000001000) // quotient_const
            mstore(add(payload, 0x04c0), 0x0000000000000000000000000000000000000000000000100000000000000000) // quotient_const
            mstore(add(payload, 0x04e0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000) // quotient_const
            mstore(add(payload, 0x0500), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefeffffff00000001) // quotient_const
            mstore(add(payload, 0x0520), 0x73eda753299d7d483339d80809a1d80553bca402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x0540), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffb00000001) // quotient_const
            mstore(add(payload, 0x0560), 0x73eda753299d7d483339d80809a1d80553bda402fbfe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x0580), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffefffff001) // quotient_const
            mstore(add(payload, 0x05a0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5beeffffffff00000001) // quotient_const
            mstore(add(payload, 0x05c0), 0x00000000000000000000000000000010ff0726c5de281020ad8016cf6f691213) // quotient_const
            mstore(add(payload, 0x05e0), 0x0000000000000000000000000000002c64068790f917282347187665718b04c8) // quotient_const
            mstore(add(payload, 0x0600), 0x00000000000000000000000000000027241bb5338dce8a77499428839473bf3a) // quotient_const
            mstore(add(payload, 0x0620), 0x0000000000000000000000000000002b7c4a26a1c7ae6fc4b499d04e4a463c4b) // quotient_const
            mstore(add(payload, 0x0640), 0x000000000000000000000000000000274bc40fcf526be95333a8c22c79465298) // quotient_const
            mstore(add(payload, 0x0660), 0x0000000000000000000000000000002a5ee6db49930276e2939d1c43ac82f744) // quotient_const
            mstore(add(payload, 0x0680), 0x73eda753299d7d483339d80809a1d7edd77e26c51c38afb5debf8afa00c15cc3) // quotient_const
            mstore(add(payload, 0x06a0), 0x73eda753299d7d483339d80809a1d7c553bda402fffe5bfeffffffff00000002) // quotient_const
            mstore(add(payload, 0x06c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe53ebc627fffef6280001) // quotient_const
            mstore(add(payload, 0x06e0), 0x0000000000000000000001000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0700), 0x0000000100000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0720), 0x6bc66e553973f396854f5626172ba135587d41e37a68209402355093fdcaaf6c) // quotient_const
            mstore(add(payload, 0x0740), 0x63f31e3f446953960c9d6964474300df43ab29179970f642a28e39d6c883c74b) // quotient_const
            mstore(add(payload, 0x0760), 0x73eda753299d7d483339d70809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x0780), 0x73eda752299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x07a0), 0x082738fdf02989b1adea81e1f27636cffb40621f85963b6afdcaaf6b02355095) // quotient_const
            mstore(add(payload, 0x07c0), 0x0ffa8913e53429b2269c6ea3c25ed72610127aeb668d65bc5d71c628377c38b6) // quotient_const
            mstore(add(payload, 0x07e0), 0x01ec1c0519185dfe86132d479c76d0786e1e037d0b05ca47648a1c5d29492c9b) // quotient_const
            mstore(add(payload, 0x0800), 0x1e179025ca2470882b34e63940ccbd7ad9090bf414d43b696e093b5a8782528f) // quotient_const
            mstore(add(payload, 0x0820), 0x4298bfee9a84c8ef8e83702075cb1abeb576f146636342e3db9ea6b0a4adf29d) // quotient_const
            mstore(add(payload, 0x0840), 0x3c83b078e9abed278d042acc8f3bd21e228716f04be96af8025da860e2d1bba9) // quotient_const
            mstore(add(payload, 0x0860), 0x427868260f487d1ef07edaadf37f5dbe705bd1318290f2577ae756b009c24f11) // quotient_const
            mstore(add(payload, 0x0880), 0x03020e6a35e595abd22838beeadc45cfcb0545d85ca0ab2c59d44c203fac84a7) // quotient_const
            mstore(add(payload, 0x08a0), 0x000000000000000000000000000000000000000000000000d201000000010000) // quotient_const
            mstore(add(payload, 0x08c0), 0x0000000100001b7c3f8d3fe3c5b448f1bdeb2ae34698b72d6ce966fc208c05ed) // quotient_const
            mstore(add(payload, 0x08e0), 0x73eda753299d7d483339d80809a1d7fd4057a4c12f26d1c1778e3360a6820001) // quotient_const
            mstore(add(payload, 0x0900), 0x057797fa7060856f215654ff11006fe0acf6a437e9477bf6f782dfac86f2cf75) // quotient_const
            mstore(add(payload, 0x0920), 0x0000000000000000000000000000000000000000000000000000000000000002) // quotient_const
            mstore(add(payload, 0x0940), 0x0000000000000000000000000000000000000000000000000200000000000000) // quotient_const
            mstore(add(payload, 0x0960), 0x0000000000000000000000000000000000020000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0980), 0x73eda753299d7d483339d80809a1d7e13511a4044eaa5bff4600ffff00005556) // quotient_const
            mstore(add(payload, 0x09a0), 0x73eda753299d7d483339d80809a1d7c553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x09c0), 0x73eda753299d7d483339d80809a1d7d340dd972492de594de627fffefcb80349) // quotient_const
            mstore(add(payload, 0x09e0), 0x73eda753299d7d483339d80809a1d7dbdc391ab4d8ac003bbd48021b82456c9b) // quotient_const
            mstore(add(payload, 0x0a00), 0x73eda753299d7d483339d80809a1d7d1448ee5caf5eefcffbc9fabc57759e23f) // quotient_const
            mstore(add(payload, 0x0a20), 0x73eda753299d7d483339d80809a1d80418c74cc18bb28443d3978d1fd47ffce1) // quotient_const
            mstore(add(payload, 0x0a40), 0x0000000000000000000000000000006425c019bcda40056233b00000068ff970) // quotient_const
            mstore(add(payload, 0x0a60), 0x00000000000000000000000000000052ef09129c4ea4b786856ffbc6fb7526cc) // quotient_const
            mstore(add(payload, 0x0a80), 0x73eda753299d7d483339d80809a1d7d89a085d30fc8a7106a170ac2377c34ab9) // quotient_const
            mstore(add(payload, 0x0aa0), 0x73eda753299d7d483339d80809a1d7f8ce65bb936f2d836012914aca65f077e1) // quotient_const
            mstore(add(payload, 0x0ac0), 0x000000000000000000000000000000681e5d7c70141ebdfe86c0a873114c3b84) // quotient_const
            mstore(add(payload, 0x0ae0), 0x000000000000000000000000000000297784894e27525bc342b7fde37dba9366) // quotient_const
            mstore(add(payload, 0x0b00), 0x0000000000000000000000000000000275ecae82e897af7658d0e5be57000640) // quotient_const
            mstore(add(payload, 0x0b20), 0x000000000000000000000000000000013af65741744bd7bb2c6872df2b800320) // quotient_const
            mstore(add(payload, 0x0b40), 0x00000000000000000000000000000059736a8da406e7d5f0bd1ea7b710796a90) // quotient_const
            mstore(add(payload, 0x0b60), 0x0000000000000000000000000000000c8557e86f90d0d89eed6eb5349a0f8820) // quotient_const
            mstore(add(payload, 0x0b80), 0x0453ae02a5f228d8f956b5eab4fc92bbeea5eb26b6ae4b42b4fdfcfdf026aa22) // quotient_const
            mstore(add(payload, 0x0ba0), 0x0000000000000000000000000000000000000000000000000000000800000000) // quotient_const
            mstore(add(payload, 0x0bc0), 0x0000000000000000000000000000000000000000080000000000000000000000) // quotient_const
            mstore(add(payload, 0x0be0), 0x0000000000000000000000000000000000000000000000000000000000002000) // quotient_const
            mstore(add(payload, 0x0c00), 0x0000000000000000000000000000000000000000000000200000000000000000) // quotient_const
            mstore(add(payload, 0x0c20), 0x73eda753299d7d483339d80809a1d7f454b67d3d21d64bde527fe92f9096edee) // quotient_const
            mstore(add(payload, 0x0c40), 0x73eda753299d7d483339d80809a1d7d8efb71c7206e733dbb8e789998e74fb39) // quotient_const
            mstore(add(payload, 0x0c60), 0x73eda753299d7d483339d80809a1d7de2fa1eecf722fd187b66bd77b6b8c40c7) // quotient_const
            mstore(add(payload, 0x0c80), 0x73eda753299d7d483339d80809a1d7d9d7737d61384fec3a4b662fb0b5b9c3b6) // quotient_const
            mstore(add(payload, 0x0ca0), 0x73eda753299d7d483339d80809a1d7de07f99433ad9272abcc573dd286b9ad69) // quotient_const
            mstore(add(payload, 0x0cc0), 0x73eda753299d7d483339d80809a1d7daf4d6c8b96cfbe51c6c62e3bb537d08bd) // quotient_const
            mstore(add(payload, 0x0ce0), 0x00000000000000000000000000000021fe0e4d8bbc5020415b002d9eded22426) // quotient_const
            mstore(add(payload, 0x0d00), 0x00000000000000000000000000000058c80d0f21f22e50468e30eccae3160990) // quotient_const
            mstore(add(payload, 0x0d20), 0x0000000000000000000000000000004e48376a671b9d14ee9328510728e77e74) // quotient_const
            mstore(add(payload, 0x0d40), 0x00000000000000000000000000000056f8944d438f5cdf896933a09c948c7896) // quotient_const
            mstore(add(payload, 0x0d60), 0x0000000000000000000000000000004e97881f9ea4d7d2a667518458f28ca530) // quotient_const
            mstore(add(payload, 0x0d80), 0x73eda753299d7d4833351088b4af7508df8b737010b26e15294bfcbb9194fffd) // quotient_const
            mstore(add(payload, 0x0da0), 0x0000000000000000000002000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0dc0), 0x0000000200000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x0de0), 0x639f3557494a69e4d764d44424b56a655d3cdfc3f4d1e529046aa128fb955ed7) // quotient_const
            mstore(add(payload, 0x0e00), 0x53f8952b5f3529e3e600fac084e429b93398ae2c32e39086451c73ae91078e95) // quotient_const
            mstore(add(payload, 0x0e20), 0x72018b4e10851f49ad26aac06d2b078ce59fa085f4f891b79b75e3a1d6b6d366) // quotient_const
            mstore(add(payload, 0x0e40), 0x55d6172d5f790cc00804f1cec8d51a8a7ab4980eeb2a209591f6c4a4787dad72) // quotient_const
            mstore(add(payload, 0x0e60), 0x3154e7648f18b458a4b667e793d6bd469e46b2bc9c9b191b2461594e5b520d64) // quotient_const
            mstore(add(payload, 0x0e80), 0x3769f6da3ff19020a635ad3b7a6605e731368d12b414f106fda2579e1d2e4458) // quotient_const
            mstore(add(payload, 0x0ea0), 0x31753f2d1a55002942bafd5a16227a46e361d2d17d6d69a78518a94ef63db0f0) // quotient_const
            mstore(add(payload, 0x0ec0), 0x70eb98e8f3b7e79c61119f491ec5923588b85e2aa35db0d2a62bb3dec0537b5a) // quotient_const
            mstore(add(payload, 0x0ee0), 0x03d8380a3230bbfd0c265a8f38eda0f0dc3c06fa160b948ec91438ba52925936) // quotient_const
            mstore(add(payload, 0x0f00), 0x3c2f204b9448e1105669cc7281997af5b21217e829a876d2dc1276b50f04a51e) // quotient_const
            mstore(add(payload, 0x0f20), 0x1143d88a0b6c1496e9cd0838e1f45d7817303e89c6c829c8b73d4d62495be539) // quotient_const
            mstore(add(payload, 0x0f40), 0x0519b99ea9ba5d06e6ce7d9114d5cc36f15089dd97d479f104bb50c2c5a37751) // quotient_const
            mstore(add(payload, 0x0f60), 0x110328f8f4f37cf5adc3dd53dd5ce3778cf9fe60052388aff5cead6113849e21) // quotient_const
            mstore(add(payload, 0x0f80), 0x057797fa7060856f215655ff11006fee9a1697597c277945ddaadfac83aad2c0) // quotient_const
            mstore(add(payload, 0x0fa0), 0x0000000000000000000000000000003212e00cde6d2002b119d800000347fcb8) // quotient_const
            mstore(add(payload, 0x0fc0), 0x000000000000000000000000000000340f2ebe380a0f5eff4360543988a61dc2) // quotient_const
            mstore(add(payload, 0x0fe0), 0x0000000000000000000000000000002cb9b546d20373eaf85e8f53db883cb548) // quotient_const
            mstore(add(payload, 0x1000), 0x0453ae02a5f228d8f956b6eab50092aaff9ec460d8863b22077de62a80bd8812) // quotient_const
            mstore(add(payload, 0x1020), 0x73eda753299d7d4833351088b4af7508df8b737010b26601ef73fcbb87bd0000) // quotient_const
            mstore(add(payload, 0x1040), 0x0aef2ff4e0c10ade42aca9fe2200e00159ed486fd28ef7edef05bf590de59ef3) // quotient_const
            mstore(add(payload, 0x1060), 0x0000000000000000000000000000000000000000000000000000000000000006) // quotient_const
            mstore(add(payload, 0x1080), 0x0000000000000000000000000000000000000000000000000600000000000000) // quotient_const
            mstore(add(payload, 0x10a0), 0x0000000000000000000000000000000000060000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x10c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff) // quotient_const
            mstore(add(payload, 0x10e0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefdffffff00000001) // quotient_const
            mstore(add(payload, 0x1100), 0x73eda753299d7d483339d80809a1d80553bba402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1120), 0x0000000000000000000000000000000000000000000000000000000000000003) // quotient_const
            mstore(add(payload, 0x1140), 0x0000000000000000000000000000000000030000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x1160), 0x0000000000000000000000000000012c71404d368ec010269b10000013afec50) // quotient_const
            mstore(add(payload, 0x1180), 0x000000000000000000000000000000f8cd1b37d4ebee2693904ff354f25f7464) // quotient_const
            mstore(add(payload, 0x11a0), 0x000000000000000000000000000001385b1875503c5c39fb9441f95933e4b28c) // quotient_const
            mstore(add(payload, 0x11c0), 0x0000000000000000000000000000007c668d9bea75f71349c827f9aa792fba32) // quotient_const
            mstore(add(payload, 0x11e0), 0x0000000000000000000000000000000761c60b88b9c70e630a72b13b050012c0) // quotient_const
            mstore(add(payload, 0x1200), 0x73eda753299d7d483339d80809a1d7a12dfd8a4625be569ccc4ffffef9700691) // quotient_const
            mstore(add(payload, 0x1220), 0x73eda753299d7d483339d80809a1d7b264b49166b159a4787a900438048ad935) // quotient_const
            mstore(add(payload, 0x1240), 0x00000000000000000000000000000003b0e305c45ce387318539589d82800960) // quotient_const
            mstore(add(payload, 0x1260), 0x0000000000000000000000000000010c5a3fa8ec14b781d2375bf725316c3fb0) // quotient_const
            mstore(add(payload, 0x1280), 0x000000000000000000000000000000259007b94eb27289dcc84c1f9dce2e9860) // quotient_const
            mstore(add(payload, 0x12a0), 0x73eda753299d7d483339d80809a1d79d35602792ebdf9e00793f578beeb3c47d) // quotient_const
            mstore(add(payload, 0x12c0), 0x73eda753299d7d483339d80809a1d802ddd0f5801766ac88a72f1a40a8fff9c1) // quotient_const
            mstore(add(payload, 0x12e0), 0x73eda753299d7d483339d80809a1d7abe053165ef916860e42e15847ef869571) // quotient_const
            mstore(add(payload, 0x1300), 0x73eda753299d7d483339d80809a1d7ec490dd323de5caac125229595cbe0efc1) // quotient_const
            mstore(add(payload, 0x1320), 0x08a75c054be451b1f2ad6bd569f92577dd4bd64d6d5c968569fbf9fbe04d544d) // quotient_const
            mstore(add(payload, 0x1340), 0x0000000000000000000000000000000000000000000000000000001800000000) // quotient_const
            mstore(add(payload, 0x1360), 0x0000000000000000000000000000000000000000180000000000000000000000) // quotient_const
            mstore(add(payload, 0x1380), 0x0000000000000000000000000000000000000000000000000000000000006000) // quotient_const
            mstore(add(payload, 0x13a0), 0x0000000000000000000000000000000000000000000000600000000000000000) // quotient_const
            mstore(add(payload, 0x13c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffff700000001) // quotient_const
            mstore(add(payload, 0x13e0), 0x73eda753299d7d483339d80809a1d80553bda402f7fe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1400), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffe001) // quotient_const
            mstore(add(payload, 0x1420), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bdeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1440), 0x73eda753299d7d483339d80809a1d7e355af567743ae3bbda4ffd260212ddbdb) // quotient_const
            mstore(add(payload, 0x1460), 0x73eda753299d7d483339d80809a1d7ac8bb094e10dd00bb871cf13341ce9f671) // quotient_const
            mstore(add(payload, 0x1480), 0x73eda753299d7d483339d80809a1d7b70b86399be46147106cd7aef7d718818d) // quotient_const
            mstore(add(payload, 0x14a0), 0x73eda753299d7d483339d80809a1d7ae5b2956bf70a17c7596cc5f626b73876b) // quotient_const
            mstore(add(payload, 0x14c0), 0x73eda753299d7d483339d80809a1d7b6bc3584645b26895898ae7ba60d735ad1) // quotient_const
            mstore(add(payload, 0x14e0), 0x73eda753299d7d483339d80809a1d7b095efed6fd9f96e39d8c5c777a6fa1179) // quotient_const
            mstore(add(payload, 0x1500), 0x00000000000000000000000000000065fa2ae8a334f060c4110088dc9c766c72) // quotient_const
            mstore(add(payload, 0x1520), 0x00000000000000000000000000000000000000000c0000000000000000000000) // quotient_const
            mstore(add(payload, 0x1540), 0x0000000000000000000000000000010a58272d65d68af0d3aa92c660a9421cb0) // quotient_const
            mstore(add(payload, 0x1560), 0x0000000000000000000000000000000000000000000000300000000000000000) // quotient_const
            mstore(add(payload, 0x1580), 0x000000000000000000000000000000ead8a63f3552d73ecbb978f3157ab67b5c) // quotient_const
            mstore(add(payload, 0x15a0), 0x000000000000000000000000000000852c1396b2eb457869d549633054a10e58) // quotient_const
            mstore(add(payload, 0x15c0), 0x00000000000000000000000000000104e9bce7caae169e9c3b9ae1d5bda569c2) // quotient_const
            mstore(add(payload, 0x15e0), 0x0000000000000000000000000000008274de73e5570b4f4e1dcd70eaded2b4e1) // quotient_const
            mstore(add(payload, 0x1600), 0x000000000000000000000000000000ebc6985edbee8777f335f48d0ad7a5ef90) // quotient_const
            mstore(add(payload, 0x1620), 0x0000000000000000000000000000007f1cb491dcb90764a7bad754cb0588e5cc) // quotient_const
            mstore(add(payload, 0x1640), 0x73eda753299d7d48333049095fbd120c6b5942dd2166802b5297f978232a0002) // quotient_const
            mstore(add(payload, 0x1660), 0x0000000000000000000006000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x1680), 0x0000000600000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x16a0), 0x4302515f88a4431e1fbaccbc5adc8f25703b5745de78f77d0d3fe37cf2c01c83) // quotient_const
            mstore(add(payload, 0x16c0), 0x140e70dbca64831b4b8f40317b68cd20f34ec27e98adf994cf555b0db316abbd) // quotient_const
            mstore(add(payload, 0x16e0), 0x73eda753299d7d483339d60809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1700), 0x73eda751299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001) // quotient_const
            mstore(add(payload, 0x1720), 0x104e71fbe05313635bd503c3e4ec6d9ff680c43f0b2c76d5fb955ed6046aa12a) // quotient_const
            mstore(add(payload, 0x1740), 0x1ff51227ca6853644d38dd4784bdae4c2024f5d6cd1acb78bae38c506ef8716c) // quotient_const
            mstore(add(payload, 0x1760), 0x70156f48f76cc14b27137d78d0b4371477819d08e9f2c77036ebc744ad6da6cb) // quotient_const
            mstore(add(payload, 0x1780), 0x37be870795549c37dcd00b9588085d0fa1ab8c1ad655e52c23ed8949f0fb5ae3) // quotient_const
            mstore(add(payload, 0x17a0), 0x62a9cec91e3168b1496ccfcf27ad7a8d3c8d65793936323648c2b29cb6a41ac8) // quotient_const
            mstore(add(payload, 0x17c0), 0x6ed3edb47fe320414c6b5a76f4cc0bce626d1a256829e20dfb44af3c3a5c88b0) // quotient_const
            mstore(add(payload, 0x17e0), 0x62ea7e5a34aa00528575fab42c44f48dc6c3a5a2fadad34f0a31529dec7b61e0) // quotient_const
            mstore(add(payload, 0x1800), 0x6de98a7ebdd251f08ee9668a33e94c65bdb3185246bd05a64c5767be80a6f6b3) // quotient_const
            mstore(add(payload, 0x1820), 0x0b88a81e969233f724730fadaac8e2d294b414ee4222bdac5b3caa2ef7b70ba2) // quotient_const
            mstore(add(payload, 0x1840), 0x0000000300000000000000000000000000000000000000000000000000000000) // quotient_const
            mstore(add(payload, 0x1860), 0x409fb98f933d25e8d0038d4f7b2a98dbc278a3b57cfb0879943764202d0def59) // quotient_const
            mstore(add(payload, 0x1880), 0x43fe0c177a010031bf648c1cc285529323863340cc562ac9e7aaad86598b55df) // quotient_const
            mstore(add(payload, 0x18a0), 0x33cb899e22443dc4bd6718aaa5dd18684590bb9d54587d5a25b7e826dc13afab) // quotient_const
            mstore(add(payload, 0x18c0), 0x5a46b0715e6d5198819eb2abc26638708b1b23dc3e7cb23c4a1bb20f9686f7ad) // quotient_const
            mstore(add(payload, 0x18e0), 0x0f4d2cdbfd2f1714b46b78b33e8164a4d3f19d98c77d6dd30e31f24850ea65f3) // quotient_const
            mstore(add(payload, 0x1900), 0x419d6a1793664a2e73d2a85da4119e5513d7a0cde3bde4e90718f923a87532fa) // quotient_const
            mstore(add(payload, 0x1920), 0x33097aeadeda76e1094b97fb9816aa66a6edfb200f6a9a0fe16c08233a8dda63) // quotient_const
            mstore(add(payload, 0x1940), 0x09062b3ea1b0c1037678aa3cc094d16f610fd18915e201850d7ce460bf058df5) // quotient_const
            mstore(add(payload, 0x1960), 0x0456a29a706afacf2158850711006fe0acf6a437e9477bf6f782dfac86f2cf7b) // quotient_const
            mstore(add(payload, 0x1980), 0x0397cc06bc030aab970dabe70cd498bbeea8daaea65607bb6a872125fec74a10) // quotient_const
            mstore(add(payload, 0x19a0), 0x73eda753299d7d4833351088b4af7508df8b737010b26e15294bfcbb91950003) // quotient_const
            mstore(add(payload, 0x19c0), 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140) // quotient_const
            mstore(add(payload, 0x19e0), 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a) // quotient_const
            mstore(add(payload, 0x1a00), 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db) // quotient_const
            mstore(add(payload, 0x1a20), 0x0594e0109a0005958008060d000b0200011b000021020103070002000094a002) // quotient_program
            mstore(add(payload, 0x1a40), 0x94c00394e00495000595200095400295600395800695a00795c00895e0099600) // quotient_program
            mstore(add(payload, 0x1a60), 0x0a96200b96400c96600d96800e96a00496c00596e006970007972094a0009540) // quotient_program
            mstore(add(payload, 0x1a80), 0x0295600395800496c00596e006970007972094c00295400395600495800596c0) // quotient_program
            mstore(add(payload, 0x1aa0), 0x0696e00797000f972094e00395400495600595800696c00796e00f9700109720) // quotient_program
            mstore(add(payload, 0x1ac0), 0x95000495400595600695800796c00f96e0109700119720952005954006956007) // quotient_program
            mstore(add(payload, 0x1ae0), 0x95800f96c01096e011970012972095a00695400795600f95801096c01196e012) // quotient_program
            mstore(add(payload, 0x1b00), 0x970013972095c00795400f95601095801196c01296e013970014972015974016) // quotient_program
            mstore(add(payload, 0x1b20), 0x97800b03000121021703070001000094a00294c00394e0189500199520009540) // quotient_program
            mstore(add(payload, 0x1b40), 0x0295600395801a95a01b95c00895e00996000a96201c96401d96601e96801f96) // quotient_program
            mstore(add(payload, 0x1b60), 0xa01896c01996e01a97001b972094a00095400295600395801896c01996e01a97) // quotient_program
            mstore(add(payload, 0x1b80), 0x001b972094c00295400395601895801996c01a96e01b970020972094e0039540) // quotient_program
            mstore(add(payload, 0x1ba0), 0x1895601995801a96c01b96e020970021972095001895401995601a95801b96c0) // quotient_program
            mstore(add(payload, 0x1bc0), 0x2096e021970022972095201995401a95601b95802096c02196e0229700239720) // quotient_program
            mstore(add(payload, 0x1be0), 0x95a01a95401b95602095802196c02296e023970024972095c01b954020956021) // quotient_program
            mstore(add(payload, 0x1c00), 0x95802296c02396e02497002597202697400b0300011b00012102270100000900) // quotient_program
            mstore(add(payload, 0x1c20), 0x0695a00795c00895e00996000a96200b96400c96600094a00294c00394e00495) // quotient_program
            mstore(add(payload, 0x1c40), 0x000595200d96800e96a01597401697800b04000121022801000008001a95a01b) // quotient_program
            mstore(add(payload, 0x1c60), 0x95c00895e00996000a96201c96401d96600094a00294c00394e0189500199520) // quotient_program
            mstore(add(payload, 0x1c80), 0x1e96801f96a02697400b040001210397a0290000000b2b0894a00994c00a94e0) // quotient_program
            mstore(add(payload, 0x1ca0), 0x2a95402b95602c95800895e00996000a96202d97402e97600894a095e00994a0) // quotient_program
            mstore(add(payload, 0x1cc0), 0x96000a94a096200994c095e00a94c096002f94c096a00a94e095e02f94e09680) // quotient_program
            mstore(add(payload, 0x1ce0), 0x3094e096a02f95009660309500968031950096a02f9520964030952096603195) // quotient_program
            mstore(add(payload, 0x1d00), 0x20968032952096a000954095402b954095602c95409580039560956033956097) // quotient_program
            mstore(add(payload, 0x1d20), 0x20339580970034958097202f95a096203095a096403195a096603295a0968035) // quotient_program
            mstore(add(payload, 0x1d40), 0x95a096a02f95c096003095c096203195c096403295c096603595c096803695c0) // quotient_program
            mstore(add(payload, 0x1d60), 0x96a03396c096e03496c097003796c097203896e096e03796e097003996e09720) // quotient_program
            mstore(add(payload, 0x1d80), 0x3a970097003b970097203c972097200d000b050000210397a03d030800021508) // quotient_program
            mstore(add(payload, 0x1da0), 0x94a00994c00a94e00b95000c95202a95402b95602c95800d95a00e95c00895e0) // quotient_program
            mstore(add(payload, 0x1dc0), 0x0996000a96200b96400c96600d96800e96a03e96c03f96e040970041972094a0) // quotient_program
            mstore(add(payload, 0x1de0), 0x0895e00996000a96200b96400c96600d96800e96a094c00995e00a96000b9620) // quotient_program
            mstore(add(payload, 0x1e00), 0x0c96400d96600e96804296a094e00a95e00b96000c96200d96400e9660429680) // quotient_program
            mstore(add(payload, 0x1e20), 0x4396a095000b95e00c96000d96200e96404296604396804496a095200c95e00d) // quotient_program
            mstore(add(payload, 0x1e40), 0x96000e96204296404396604496804596a095400095402b95602c95803e96c03f) // quotient_program
            mstore(add(payload, 0x1e60), 0x96e040970041972095a00d95e00e96004296204396404496604596804696a095) // quotient_program
            mstore(add(payload, 0x1e80), 0xc00e95e04296004396204496404596604696804796a015974016978003956095) // quotient_program
            mstore(add(payload, 0x1ea0), 0x603e956095803f956096c040956096e041956097004895609720059580958040) // quotient_program
            mstore(add(payload, 0x1ec0), 0x958096c041958096e0489580970049958097200796c096c04896c096e04996c0) // quotient_program
            mstore(add(payload, 0x1ee0), 0x97004a96c097201096e096e04a96e097004b96e0972012970097004c97009720) // quotient_program
            mstore(add(payload, 0x1f00), 0x14972097200d000b050001210397a04d03080001150894a00994c00a94e01c95) // quotient_program
            mstore(add(payload, 0x1f20), 0x001d95202a95402b95602c95801e95a01f95c00895e00996000a96201c96401d) // quotient_program
            mstore(add(payload, 0x1f40), 0x96601e96801f96a04e96c04f96e050970051972094a00895e00996000a96201c) // quotient_program
            mstore(add(payload, 0x1f60), 0x96401d96601e96801f96a094c00995e00a96001c96201d96401e96601f968052) // quotient_program
            mstore(add(payload, 0x1f80), 0x96a094e00a95e01c96001d96201e96401f96605296805396a095001c95e01d96) // quotient_program
            mstore(add(payload, 0x1fa0), 0x001e96201f96405296605396805496a095201d95e01e96001f96205296405396) // quotient_program
            mstore(add(payload, 0x1fc0), 0x605496805596a095400095402b95602c95804e96c04f96e050970051972095a0) // quotient_program
            mstore(add(payload, 0x1fe0), 0x1e95e01f96005296205396405496605596805696a095c01f95e0529600539620) // quotient_program
            mstore(add(payload, 0x2000), 0x5496405596605696805796a026974003956095604e956095804f956096c05095) // quotient_program
            mstore(add(payload, 0x2020), 0x6096e051956097005895609720199580958050958096c051958096e058958097) // quotient_program
            mstore(add(payload, 0x2040), 0x0059958097201b96c096c05896c096e05996c097005a96c097202196e096e05a) // quotient_program
            mstore(add(payload, 0x2060), 0x96e097005b96e0972023970097005c9700972025972097200d000b0500012103) // quotient_program
            mstore(add(payload, 0x2080), 0x97a05d0000000c390894a00994c00a94e02d97402e97600097a00097c00297e0) // quotient_program
            mstore(add(payload, 0x20a0), 0x0398000898a00998c00a98e000954097c002954097e0039540980008954098a0) // quotient_program
            mstore(add(payload, 0x20c0), 0x09954098c00a954098e002956097c003956097e05e9560988009956098a00a95) // quotient_program
            mstore(add(payload, 0x20e0), 0x6098c02f9560996003958097c05e9580986038958098800a958098a02f958099) // quotient_program
            mstore(add(payload, 0x2100), 0x4030958099600095e097a002960097a003962097a05e96c098403896c098605f) // quotient_program
            mstore(add(payload, 0x2120), 0x96c098802f96c099203096c099403196c099605e96e098203896e098405f96e0) // quotient_program
            mstore(add(payload, 0x2140), 0x98603a96e098802f96e099003096e099203196e099403296e099605e97009800) // quotient_program
            mstore(add(payload, 0x2160), 0x38970098205f970098403a9700986060970098802f970098e030970099003197) // quotient_program
            mstore(add(payload, 0x2180), 0x009920329700994035970099605e972097e038972098005f972098203a972098) // quotient_program
            mstore(add(payload, 0x21a0), 0x4060972098603c972098802f972098c030972098e03197209900329720992035) // quotient_program
            mstore(add(payload, 0x21c0), 0x9720994036972099600d000b060000210397a061020f000a001697800097a000) // quotient_program
            mstore(add(payload, 0x21e0), 0x97c00297e00398000498200598400698600798800898a00998c00a98e00b9900) // quotient_program
            mstore(add(payload, 0x2200), 0x0c992097a00095e00296000396200496400596600696800796a097c000954002) // quotient_program
            mstore(add(payload, 0x2220), 0x95600395800496c00596e006970007972097e00295400395600495800596c006) // quotient_program
            mstore(add(payload, 0x2240), 0x96e00797000f972098000395400495600595800696c00796e00f970010972098) // quotient_program
            mstore(add(payload, 0x2260), 0x200495400595600695800796c00f96e010970011972098400595400695600795) // quotient_program
            mstore(add(payload, 0x2280), 0x800f96c01096e011970012972098600695400795600f95801096c01196e01297) // quotient_program
            mstore(add(payload, 0x22a0), 0x0013972098800795400f95601095801196c01296e013970014972095400898a0) // quotient_program
            mstore(add(payload, 0x22c0), 0x0998c00a98e00b99000c99200d99400e996095600998a00a98c00b98e00c9900) // quotient_program
            mstore(add(payload, 0x22e0), 0x0d99200e994042996095800a98a00b98c00c98e00d99000e9920429940439960) // quotient_program
            mstore(add(payload, 0x2300), 0x96c00b98a00c98c00d98e00e990042992043994044996096e00c98a00d98c00e) // quotient_program
            mstore(add(payload, 0x2320), 0x98e042990043992044994045996097000d98a00e98c04298e043990044992045) // quotient_program
            mstore(add(payload, 0x2340), 0x994046996097200e98a04298c04398e04499004599204699404799600894a009) // quotient_program
            mstore(add(payload, 0x2360), 0x94c00a94e00b95000c95200d95a00e95c01597400d99400e99600d000b060001) // quotient_program
            mstore(add(payload, 0x2380), 0x210397a062020f0009000097a00097c00297e00398001898201998401a98601b) // quotient_program
            mstore(add(payload, 0x23a0), 0x98800898a00998c00a98e01c99001d99201e994097a00095e002960003962018) // quotient_program
            mstore(add(payload, 0x23c0), 0x96401996601a96801b96a097c00095400295600395801896c01996e01a97001b) // quotient_program
            mstore(add(payload, 0x23e0), 0x972097e00295400395601895801996c01a96e01b970020972098000395401895) // quotient_program
            mstore(add(payload, 0x2400), 0x601995801a96c01b96e020970021972098201895401995601a95801b96c02096) // quotient_program
            mstore(add(payload, 0x2420), 0xe021970022972098401995401a95601b95802096c02196e02297002397209860) // quotient_program
            mstore(add(payload, 0x2440), 0x1a95401b95602095802196c02296e023970024972098801b9540209560219580) // quotient_program
            mstore(add(payload, 0x2460), 0x2296c02396e024970025972095400898a00998c00a98e01c99001d99201e9940) // quotient_program
            mstore(add(payload, 0x2480), 0x1f996095600998a00a98c01c98e01d99001e99201f994052996095800a98a01c) // quotient_program
            mstore(add(payload, 0x24a0), 0x98c01d98e01e99001f992052994053996096c01c98a01d98c01e98e01f990052) // quotient_program
            mstore(add(payload, 0x24c0), 0x992053994054996096e01d98a01e98c01f98e052990053992054994055996097) // quotient_program
            mstore(add(payload, 0x24e0), 0x001e98a01f98c05298e053990054992055994056996097201f98a05298c05398) // quotient_program
            mstore(add(payload, 0x2500), 0xe05499005599205699405799600894a00994c00a94e01c95001d95201e95a01f) // quotient_program
            mstore(add(payload, 0x2520), 0x95c02697401f99600d000b060001210397a0630000000b2b6494a06594c06694) // quotient_program
            mstore(add(payload, 0x2540), 0xe06795406895606995806795e06896006996202d97402e97606a94a094a06594) // quotient_program
            mstore(add(payload, 0x2560), 0xa094c06694a094e06b94c094c06c94c095c06c94e095a06d94e095c06c950095) // quotient_program
            mstore(add(payload, 0x2580), 0x206d950095a06e950095c06f952095206e952095a070952095c067954095e068) // quotient_program
            mstore(add(payload, 0x25a0), 0x95409600699540962068956095e0699560960071956096a069958095e0719580) // quotient_program
            mstore(add(payload, 0x25c0), 0x968072958096a07395a095a07495a095c07595c095c071960097207196209700) // quotient_program
            mstore(add(payload, 0x25e0), 0x729620972071964096e07296409700769640972071966096c072966096e07696) // quotient_program
            mstore(add(payload, 0x2600), 0x609700779660972072968096c076968096e0779680970078968097207696a096) // quotient_program
            mstore(add(payload, 0x2620), 0xc07796a096e07896a097007996a097200d000b070000210397a07a0308000215) // quotient_program
            mstore(add(payload, 0x2640), 0x6494a06594c06694e07b95007c95206795406895606995807d95a07e95c06795) // quotient_program
            mstore(add(payload, 0x2660), 0xe06896006996207f96408096608196808296a07f96c08096e081970082972094) // quotient_program
            mstore(add(payload, 0x2680), 0xa06a94a06594c06694e07b95007c95207d95a07e95c095406795e06896006996) // quotient_program
            mstore(add(payload, 0x26a0), 0x207f96408096608196808296a095606895e06996007f96208096408196608296) // quotient_program
            mstore(add(payload, 0x26c0), 0x808396a095806995e07f96008096208196408296608396808496a096c07f95e0) // quotient_program
            mstore(add(payload, 0x26e0), 0x8096008196208296408396608496808596a096e08095e0819600829620839640) // quotient_program
            mstore(add(payload, 0x2700), 0x8496608596808696a097008195e08296008396208496408596608696808796a0) // quotient_program
            mstore(add(payload, 0x2720), 0x97208295e08396008496208596408696608796808896a01597401697806b94c0) // quotient_program
            mstore(add(payload, 0x2740), 0x94c07b94c094e07c94c095007d94c095207e94c095a08994c095c08a94e094e0) // quotient_program
            mstore(add(payload, 0x2760), 0x7d94e095007e94e095208994e095a08b94e095c08c9500950089950095208b95) // quotient_program
            mstore(add(payload, 0x2780), 0x0095a08d950095c08e952095208d952095a08f952095c09095a095a09195a095) // quotient_program
            mstore(add(payload, 0x27a0), 0xc09295c095c00d000b070001210397a09303080001156494a06594c06694e094) // quotient_program
            mstore(add(payload, 0x27c0), 0x95009595206795406895606995809695a09795c06795e0689600699620989640) // quotient_program
            mstore(add(payload, 0x27e0), 0x9996609a96809b96a09896c09996e09a97009b972094a06a94a06594c06694e0) // quotient_program
            mstore(add(payload, 0x2800), 0x9495009595209695a09795c095406795e06896006996209896409996609a9680) // quotient_program
            mstore(add(payload, 0x2820), 0x9b96a095606895e06996009896209996409a96609b96809c96a095806995e098) // quotient_program
            mstore(add(payload, 0x2840), 0x96009996209a96409b96609c96809d96a096c09895e09996009a96209b96409c) // quotient_program
            mstore(add(payload, 0x2860), 0x96609d96809e96a096e09995e09a96009b96209c96409d96609e96809f96a097) // quotient_program
            mstore(add(payload, 0x2880), 0x009a95e09b96009c96209d96409e96609f9680a096a097209b95e09c96009d96) // quotient_program
            mstore(add(payload, 0x28a0), 0x209e96409f9660a09680a196a02697406b94c094c09494c094e09594c0950096) // quotient_program
            mstore(add(payload, 0x28c0), 0x94c095209794c095a0a294c095c0a394e094e09694e095009794e09520a294e0) // quotient_program
            mstore(add(payload, 0x28e0), 0x95a0a494e095c0a595009500a295009520a4950095a0a6950095c0a795209520) // quotient_program
            mstore(add(payload, 0x2900), 0xa6952095a0a8952095c0a995a095a0aa95a095c0ab95c095c00d000b07000121) // quotient_program
            mstore(add(payload, 0x2920), 0x0397a0ac0000000e100094a00294c00394e06795406895606995800095e00296) // quotient_program
            mstore(add(payload, 0x2940), 0x000396202d97402e97600097c00297e003980008954095406895409560699540) // quotient_program
            mstore(add(payload, 0x2960), 0x95800a956095607195609720719580970072958097207196c096e07296c09700) // quotient_program
            mstore(add(payload, 0x2980), 0x7696c097203096e096e07696e097007796e09720329700970078970097203697) // quotient_program
            mstore(add(payload, 0x29a0), 0x2097200d000b080000210397a0ad04010002150094a00294c00394e004950005) // quotient_program
            mstore(add(payload, 0x29c0), 0x95206795406895606995800695a00795c00095e0029600039620049640059660) // quotient_program
            mstore(add(payload, 0x29e0), 0x0696800796a07f96c08096e08197008297200097c00297e00398000498200598) // quotient_program
            mstore(add(payload, 0x2a00), 0x4006986007988095400895406895606995807f96c08096e08197008297201597) // quotient_program
            mstore(add(payload, 0x2a20), 0x401697800a956095607f9560958080956096c081956096e08295609700839560) // quotient_program
            mstore(add(payload, 0x2a40), 0x97200c9580958081958096c082958096e0839580970084958097200e96c096c0) // quotient_program
            mstore(add(payload, 0x2a60), 0x8396c096e08496c097008596c097204396e096e08596e097008696e097204597) // quotient_program
            mstore(add(payload, 0x2a80), 0x009700879700972047972097200d000b080001210397a0ae04010001150094a0) // quotient_program
            mstore(add(payload, 0x2aa0), 0x0294c00394e01895001995206795406895606995801a95a01b95c00095e00296) // quotient_program
            mstore(add(payload, 0x2ac0), 0x000396201896401996601a96801b96a09896c09996e09a97009b97200097c002) // quotient_program
            mstore(add(payload, 0x2ae0), 0x97e00398001898201998401a98601b988095400895406895606995809896c099) // quotient_program
            mstore(add(payload, 0x2b00), 0x96e09a97009b97202697400a95609560989560958099956096c09a956096e09b) // quotient_program
            mstore(add(payload, 0x2b20), 0x956097009c956097201d958095809a958096c09b958096e09c958097009d9580) // quotient_program
            mstore(add(payload, 0x2b40), 0x97201f96c096c09c96c096e09d96c097009e96c097205396e096e09e96e09700) // quotient_program
            mstore(add(payload, 0x2b60), 0x9f96e097205597009700a09700972057972097200d000b0800010594a01194a0) // quotient_program
            mstore(add(payload, 0x2b80), 0x1194a005950008060d000b0900000594c01194c01194c005952008060d000b09) // quotient_program
            mstore(add(payload, 0x2ba0), 0x00010594e01194e01194e00595a008060d000b0900011b00021b000305958008) // quotient_program
            mstore(add(payload, 0x2bc0), 0x109aa00594a01194a01195000daf060594c01194c01195200db0060594e01194) // quotient_program
            mstore(add(payload, 0x2be0), 0xe01195a00db1060d000b090001191f0000000000000000000000000000000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2c00), 0x0000000000000000000000000000000016e98a681dca730dcbe651aec5493976) // fixed_comms[0].x_hi
            mstore(add(payload, 0x2c20), 0x11944be61932e7d19a63786871335939b0eefa7e32507b68b4ad6fd89a5c1028) // fixed_comms[0].x_lo
            mstore(add(payload, 0x2c40), 0x0000000000000000000000000000000010e6ae8d3becb251e60db7d788be7029) // fixed_comms[0].y_hi
            mstore(add(payload, 0x2c60), 0x8dbcdfdbb394da2ca9725e07485d6b630569a66ec867aa0d605573ae82d550df) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2c80), 0x000000000000000000000000000000000fb2ef3076aa1a8068bec7ef35167c1c) // fixed_comms[1].x_hi
            mstore(add(payload, 0x2ca0), 0xf1f26a24abaa3b4dc8c6d218021c08429e4c175654b5996eb4de74d17a5c188d) // fixed_comms[1].x_lo
            mstore(add(payload, 0x2cc0), 0x00000000000000000000000000000000000f94fa3dcc144ffe6a4ace1de5f956) // fixed_comms[1].y_hi
            mstore(add(payload, 0x2ce0), 0x76ad02ffc32c0345767b466f064aec3f1101ecd9eaf91ba5d4c145f792d1285a) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2d00), 0x0000000000000000000000000000000016909a26057dec4152b5bd207c37f9a8) // fixed_comms[2].x_hi
            mstore(add(payload, 0x2d20), 0xc3af2c8cfa63dfd83e34704255392445fae3c47d749e435e0291232659a8caeb) // fixed_comms[2].x_lo
            mstore(add(payload, 0x2d40), 0x0000000000000000000000000000000000b9edb176686ec391a3684928dc0842) // fixed_comms[2].y_hi
            mstore(add(payload, 0x2d60), 0x80c60eca091b8a3925e31ef1032793f2ef4e31225ab560bf721f17525dd476c8) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2d80), 0x0000000000000000000000000000000014861e20b064f637d60cc250ff3b8804) // fixed_comms[3].x_hi
            mstore(add(payload, 0x2da0), 0x9b9697b5245d031c784398bdf950e99d7968c86e92c4ec1cb3821a69686dfb09) // fixed_comms[3].x_lo
            mstore(add(payload, 0x2dc0), 0x000000000000000000000000000000000c117b524f84a06b024a40003e1c3aab) // fixed_comms[3].y_hi
            mstore(add(payload, 0x2de0), 0x25253a3cf5b53d2f77d1f9328a9c0b32bea4f591eb470dbb599b5fbdfa7df46b) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2e00), 0x000000000000000000000000000000001420bb2d8c182dda6c982eb820e035f6) // fixed_comms[4].x_hi
            mstore(add(payload, 0x2e20), 0xa4a5c6c69376dfda17ac5588d34a0b313800b8d18ecd818f3e4e2671589ec691) // fixed_comms[4].x_lo
            mstore(add(payload, 0x2e40), 0x0000000000000000000000000000000000855eb6333071d5bb90a0351dbf958c) // fixed_comms[4].y_hi
            mstore(add(payload, 0x2e60), 0x13e5648bcafb55776c78e46031e4620cfda02728e26bb97f067a9a0cdf72aa9f) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2e80), 0x000000000000000000000000000000000707698990b767903c9aaf028c98b46a) // fixed_comms[5].x_hi
            mstore(add(payload, 0x2ea0), 0xc4925e4e30db42105aade1a5cd7dd9b3d2222bd7085071b5c2212709cfcc2d46) // fixed_comms[5].x_lo
            mstore(add(payload, 0x2ec0), 0x000000000000000000000000000000000a88a7d4f1148bd3efffaedb5be62777) // fixed_comms[5].y_hi
            mstore(add(payload, 0x2ee0), 0x27fad92f1005d28d12ef861b5dcf8b580a1322048d469da5f84b26fa7f8d2e4d) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2f00), 0x000000000000000000000000000000001495975f8f8c0cb6c54e1163fe045732) // fixed_comms[6].x_hi
            mstore(add(payload, 0x2f20), 0x2be3eb4af919cb0eb6126028ebeab81d075dff85aa522989166bf6e01880c1be) // fixed_comms[6].x_lo
            mstore(add(payload, 0x2f40), 0x0000000000000000000000000000000018bdd4eef361f4a6d23a6511b48e20fb) // fixed_comms[6].y_hi
            mstore(add(payload, 0x2f60), 0x4080898637660f3f3371adfb48585dd2ad89c29cc260d604ce9cd68a31ff427d) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2f80), 0x00000000000000000000000000000000166c1cd47b07ac0aee553f0b4277cf37) // fixed_comms[7].x_hi
            mstore(add(payload, 0x2fa0), 0xb4822422a23ea90486c60a5b3b9052dff113041d51718304e781a5a7bd93bdc2) // fixed_comms[7].x_lo
            mstore(add(payload, 0x2fc0), 0x00000000000000000000000000000000016c91bfb3ce38ba23df779d69abeaa4) // fixed_comms[7].y_hi
            mstore(add(payload, 0x2fe0), 0x8aaa142a59667ce4eabfaf36c5453af4aaec6e596ad923693a2a7d1483c2fd20) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3000), 0x000000000000000000000000000000001262dde7fc4aeca256572897f5d601ef) // fixed_comms[8].x_hi
            mstore(add(payload, 0x3020), 0x5b8b5586b8593d43cbcd11d2fd80fe2a2214269e5479b5d976cf507d5262c273) // fixed_comms[8].x_lo
            mstore(add(payload, 0x3040), 0x0000000000000000000000000000000012bd810c9b8eaaf899f161e2d8c26762) // fixed_comms[8].y_hi
            mstore(add(payload, 0x3060), 0xc3f299919bfa2b2809a027cc9bcac1799ef2d48b11403ce47a5341f7307d2cd4) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3080), 0x00000000000000000000000000000000096d06362268ed80162468c5e664e2bb) // fixed_comms[9].x_hi
            mstore(add(payload, 0x30a0), 0x1a1a3b60a6c419cb6edb470b646e9ed4e021686e93f82d0c3ee2448368fe81be) // fixed_comms[9].x_lo
            mstore(add(payload, 0x30c0), 0x0000000000000000000000000000000015ceb98a36a3576ad6db1163a0a98d2a) // fixed_comms[9].y_hi
            mstore(add(payload, 0x30e0), 0x0535a28ca330834bb07c6682d32b20cd8171f4c0d9f063d768b6e3185b6ae44e) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3100), 0x0000000000000000000000000000000019731a2f803950b978082f57fdfffb38) // fixed_comms[10].x_hi
            mstore(add(payload, 0x3120), 0x0de3c6bef55492c30e409d77ac9acb523958dea2856b12cb4e87608584ab499a) // fixed_comms[10].x_lo
            mstore(add(payload, 0x3140), 0x0000000000000000000000000000000005f057d8c91984630d36a0df6c2ebb07) // fixed_comms[10].y_hi
            mstore(add(payload, 0x3160), 0x3881713eb294d8cdf7bb0374cb722b7bb5080101a54638216ab4886f0276a475) // fixed_comms[10].y_lo
            // Fixed-column commitment 11, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3180), 0x0000000000000000000000000000000004d63c6ffcf22c5a45cbc67e299c2b3d) // fixed_comms[11].x_hi
            mstore(add(payload, 0x31a0), 0xcfd98199c525785d127006aca0f82774876a94e120b9bde61b9227ee96dc6841) // fixed_comms[11].x_lo
            mstore(add(payload, 0x31c0), 0x0000000000000000000000000000000002385e4a7b9ab571a73f07d9574152e5) // fixed_comms[11].y_hi
            mstore(add(payload, 0x31e0), 0xa45de038325c587523413d98b5feb6d2071c293abbeab53bf941d76b264f3369) // fixed_comms[11].y_lo
            // Fixed-column commitment 12, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3200), 0x000000000000000000000000000000000eea9ee53f693242e50678f2ac4a5053) // fixed_comms[12].x_hi
            mstore(add(payload, 0x3220), 0x6bc4aa60deae574c46e3cf56a8d14af17d603f8c222728fb09300eee5c5b326b) // fixed_comms[12].x_lo
            mstore(add(payload, 0x3240), 0x0000000000000000000000000000000014aa3a043bb1340472428a1756ad82bb) // fixed_comms[12].y_hi
            mstore(add(payload, 0x3260), 0x49fa2fee5ff945799006e851969947efb6351c7642b2683deb31537ea6209643) // fixed_comms[12].y_lo
            // Fixed-column commitment 13, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3280), 0x000000000000000000000000000000000b7028c202ee5b6a74d6ccfe5990dc98) // fixed_comms[13].x_hi
            mstore(add(payload, 0x32a0), 0x4381d45aa22ccb019d848829dd72d16143e5af158899fcc009d5ca17c97c3414) // fixed_comms[13].x_lo
            mstore(add(payload, 0x32c0), 0x0000000000000000000000000000000006c6ca7119058dbb54d5302f125f9cef) // fixed_comms[13].y_hi
            mstore(add(payload, 0x32e0), 0xdc6b68957c7b970427a4b5a3bd0aa7ff5fa033687afdc2a4e150a408b0a5f4d2) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3300), 0x0000000000000000000000000000000008a540ee790774da565637ec30ced988) // fixed_comms[14].x_hi
            mstore(add(payload, 0x3320), 0x563c90d314d01996465fa3f893d5fb010b617a4edcabc5c8f8141584792a0067) // fixed_comms[14].x_lo
            mstore(add(payload, 0x3340), 0x00000000000000000000000000000000071e81991f7c8f62be7df37cd485cb5e) // fixed_comms[14].y_hi
            mstore(add(payload, 0x3360), 0x1f941d942cc15f814350867bcdf1521ef6e7e76b6928827688b0d3d14a6cf1a3) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3380), 0x0000000000000000000000000000000005a4ed142d6c05e535a91ff8244ca5cb) // fixed_comms[15].x_hi
            mstore(add(payload, 0x33a0), 0xdda66355e156c19ea759a1f5aecd1225e16cb3f18397a66b055a2918a2a74d54) // fixed_comms[15].x_lo
            mstore(add(payload, 0x33c0), 0x000000000000000000000000000000000ce5eb9724134cce6feb1c0ff1b66ab3) // fixed_comms[15].y_hi
            mstore(add(payload, 0x33e0), 0x5e79b2b4087200f1d9a76ee4a2b3b5424266da9d518653e9391e9a94196f1d7f) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3400), 0x0000000000000000000000000000000009b07c1df13d348c1ed7cb560fcdd682) // fixed_comms[16].x_hi
            mstore(add(payload, 0x3420), 0x55221aadb75410fa4526857c95cea6bf3a0efa98e31898de56ea7ff30f7c514a) // fixed_comms[16].x_lo
            mstore(add(payload, 0x3440), 0x0000000000000000000000000000000011b2d20f8b12527aba78064c809753e2) // fixed_comms[16].y_hi
            mstore(add(payload, 0x3460), 0x21cebde9bb41aa67abae156e3a179655388e51211ba5614fb696a7f0cc212560) // fixed_comms[16].y_lo
            // Fixed-column commitment 17, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3480), 0x0000000000000000000000000000000010ce280498c90ca7501427caf6bcd6d9) // fixed_comms[17].x_hi
            mstore(add(payload, 0x34a0), 0xb4987380f8d9e8ef710b81034a460c8da32362568e1e9fd6b2cb5297805c98ad) // fixed_comms[17].x_lo
            mstore(add(payload, 0x34c0), 0x000000000000000000000000000000000292967ae2e91be4d3555cddb84538dd) // fixed_comms[17].y_hi
            mstore(add(payload, 0x34e0), 0x0edcb077ce0626f751bee2673ff6b24c182fd2ae99a0cd83881a81a3facfcb6e) // fixed_comms[17].y_lo
            // Fixed-column commitment 18, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3500), 0x0000000000000000000000000000000017cf661d855e771f61cab52918bc03e5) // fixed_comms[18].x_hi
            mstore(add(payload, 0x3520), 0x329761bebc6704041c0430c64bc2d589210a4250f57e9dec51a807d4d6926f31) // fixed_comms[18].x_lo
            mstore(add(payload, 0x3540), 0x000000000000000000000000000000000f50cacb58bf9101f3d7926b2e26675d) // fixed_comms[18].y_hi
            mstore(add(payload, 0x3560), 0x036c7cf34f335946dfc1d1a6e148de3da13cabfe8e7507f10baca11e07231413) // fixed_comms[18].y_lo
            // Fixed-column commitment 19, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3580), 0x0000000000000000000000000000000016caf868eda0aeb753fd8ec3bee96cbe) // fixed_comms[19].x_hi
            mstore(add(payload, 0x35a0), 0x3217eade0bae8e908b6cfe1f144518cbaec5bbbbc6e6641d82702b3dd5997985) // fixed_comms[19].x_lo
            mstore(add(payload, 0x35c0), 0x000000000000000000000000000000000a35da0b540c40574d639e726b9c7e6d) // fixed_comms[19].y_hi
            mstore(add(payload, 0x35e0), 0xb45e6cbefb614f14a1721bdbca2dfcb20aaeb64926032522ba3de23420dc1d87) // fixed_comms[19].y_lo
            // Fixed-column commitment 20, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3600), 0x000000000000000000000000000000000b7f1691be78a38c579c2ac6bef18d54) // fixed_comms[20].x_hi
            mstore(add(payload, 0x3620), 0xf2d63e634590931fda91cce7af80f7c589cc37a98870e127c93e059ff020df07) // fixed_comms[20].x_lo
            mstore(add(payload, 0x3640), 0x0000000000000000000000000000000012582699af0164d4335252425d0251c4) // fixed_comms[20].y_hi
            mstore(add(payload, 0x3660), 0xa1af4e259a3f65f0065b2b05127538a8434de1326c4920ee45da346bbbc7d293) // fixed_comms[20].y_lo
            // Fixed-column commitment 21, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3680), 0x000000000000000000000000000000000e004abc0ac243147c480dca32186a34) // fixed_comms[21].x_hi
            mstore(add(payload, 0x36a0), 0x78642aaafe922adde54e02ae93479fa0ae45b75ed0229c2f358a0473d17c09a5) // fixed_comms[21].x_lo
            mstore(add(payload, 0x36c0), 0x0000000000000000000000000000000013e0dac8358fff676678a7b7d854aee3) // fixed_comms[21].y_hi
            mstore(add(payload, 0x36e0), 0x3fda118cfb39d426f3418966ed06283adbd804fbe8cf51fd89c2f5c410919f48) // fixed_comms[21].y_lo
            // Fixed-column commitment 22, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3700), 0x00000000000000000000000000000000168c0d6883d0d5b67d3a5944ee0616a3) // fixed_comms[22].x_hi
            mstore(add(payload, 0x3720), 0xce7ac537685a26b678bab6b1b50115c32a5f90b6ca56cb8560a40964840893ce) // fixed_comms[22].x_lo
            mstore(add(payload, 0x3740), 0x00000000000000000000000000000000197d467f656fc49a1c5119d7cd826cc2) // fixed_comms[22].y_hi
            mstore(add(payload, 0x3760), 0xbe6345c67f108e7e44f8ebfcebea5366fdee85d69947c8f74f623165dc1029b5) // fixed_comms[22].y_lo
            // Fixed-column commitment 23, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3780), 0x00000000000000000000000000000000133f78d1d5ad537d358f421d115bdb2f) // fixed_comms[23].x_hi
            mstore(add(payload, 0x37a0), 0x44eff93e623017fb4a06006877bd8504b8b614c6c877d73de7cdc2c2e69a8998) // fixed_comms[23].x_lo
            mstore(add(payload, 0x37c0), 0x00000000000000000000000000000000067b406b38e3895daddca2f64de3ee21) // fixed_comms[23].y_hi
            mstore(add(payload, 0x37e0), 0x5c7961f1d2f1904f7e2aa60bc20559610c868810183505527e28eea6089d6bf8) // fixed_comms[23].y_lo
            // Fixed-column commitment 24, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3800), 0x000000000000000000000000000000000bd679e559d6bf9f498928a3074a0709) // fixed_comms[24].x_hi
            mstore(add(payload, 0x3820), 0x23c4cf1d5823b59316852fd6653fe003a4a2da9ba443e4640993524c79a6f56d) // fixed_comms[24].x_lo
            mstore(add(payload, 0x3840), 0x000000000000000000000000000000000821077b092335b9f70fb79a424cca13) // fixed_comms[24].y_hi
            mstore(add(payload, 0x3860), 0x4e823d96a4fdeaf4154ab7c5ef023844695a10e9bfdf314847ccaa40205f980a) // fixed_comms[24].y_lo
            // Fixed-column commitment 25, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3880), 0x00000000000000000000000000000000041f7c88095a1bbf5759d88a7d109853) // fixed_comms[25].x_hi
            mstore(add(payload, 0x38a0), 0x4b1661f3b1b9012866e17c7550a5b52861ac915beba38767c7aeb04c1df330ac) // fixed_comms[25].x_lo
            mstore(add(payload, 0x38c0), 0x000000000000000000000000000000000f2e8cc95c27bf0235efa88fa70bb3eb) // fixed_comms[25].y_hi
            mstore(add(payload, 0x38e0), 0x59a5ef2602a9b70c5af7b0db755f10a8e0ffc380b61a580c3300fda8d6077854) // fixed_comms[25].y_lo
            // Fixed-column commitment 26, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3900), 0x000000000000000000000000000000001983933b9a69c960c9eda1f5942af11a) // fixed_comms[26].x_hi
            mstore(add(payload, 0x3920), 0x22de694e7c8b2a5f8d920b50d6c90aca30d149ace5ff9feebf84a136abdfa9f4) // fixed_comms[26].x_lo
            mstore(add(payload, 0x3940), 0x00000000000000000000000000000000162f68d07437f5dd432392f6a244044d) // fixed_comms[26].y_hi
            mstore(add(payload, 0x3960), 0x4605b4457384fb65577df046c667a744f851fbdb0e8751aaeeb334bf32fbd3e0) // fixed_comms[26].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3980), 0x0000000000000000000000000000000014669fe860d72f984d085b33bfffa399) // permutation_comms[0].x_hi
            mstore(add(payload, 0x39a0), 0x12a9b0d0acb1ff8fd119eee9d0870eab9324293b88df67b9e1ebd180db262c72) // permutation_comms[0].x_lo
            mstore(add(payload, 0x39c0), 0x000000000000000000000000000000000f3292f0f7b5707fe0874c56fdae2e88) // permutation_comms[0].y_hi
            mstore(add(payload, 0x39e0), 0x2a2ba44cc1a14f736d255905838f8438fb8dbfd65ad84bcbca748a749c58955e) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3a00), 0x000000000000000000000000000000000ee7e9d684b203f28dd5424f3a511695) // permutation_comms[1].x_hi
            mstore(add(payload, 0x3a20), 0xff88a9d696976adca8c54262e0f553756ec45b8e103453f8c18a07c3abcef5fd) // permutation_comms[1].x_lo
            mstore(add(payload, 0x3a40), 0x00000000000000000000000000000000177029152e262c258c987bfbeeee14c8) // permutation_comms[1].y_hi
            mstore(add(payload, 0x3a60), 0xe945c114efada4abdeff8610bea0cf199ef3f375cf15f6b437de67f3379c5801) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3a80), 0x000000000000000000000000000000000e2ead1ec1acc411940e7bea5d0f2114) // permutation_comms[2].x_hi
            mstore(add(payload, 0x3aa0), 0x6b39327e36ebab84013dd8f5c2b3f8b576a125db88ff28db45a79a28df414b66) // permutation_comms[2].x_lo
            mstore(add(payload, 0x3ac0), 0x00000000000000000000000000000000199b4ea033c01e1d83627c054ba6f2dc) // permutation_comms[2].y_hi
            mstore(add(payload, 0x3ae0), 0x2a61b1277d07469ad65c413a1970c9cf179bedfc4cf2f61c1ee8ca5e4a01ab90) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3b00), 0x0000000000000000000000000000000011af8f4e99c419588e05414f664ae8f6) // permutation_comms[3].x_hi
            mstore(add(payload, 0x3b20), 0xdded731799d69d8f5a72c124a5c6df33153e15767000ef54648a8dd23687140a) // permutation_comms[3].x_lo
            mstore(add(payload, 0x3b40), 0x0000000000000000000000000000000017ba99d9323e45fe54ec6ac4daaad8d3) // permutation_comms[3].y_hi
            mstore(add(payload, 0x3b60), 0x0c0dbc53d3f5f54c05667eb0e4f28da8973657bf62915fcdfc551698f56aa574) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3b80), 0x000000000000000000000000000000000ed68fa806cd3171cb061afebf65799d) // permutation_comms[4].x_hi
            mstore(add(payload, 0x3ba0), 0xf9014492a08de2420f1234158d2f1d214b5354b7ad8cfc753d2712e6bb9b20a5) // permutation_comms[4].x_lo
            mstore(add(payload, 0x3bc0), 0x0000000000000000000000000000000013f05c6e0393baeec023451082007353) // permutation_comms[4].y_hi
            mstore(add(payload, 0x3be0), 0x55211ac5dd3c2267dcf706d18263fa7b7916e44ab1d5309430542f75717187c4) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3c00), 0x000000000000000000000000000000000a925e4ad4c2d71f096de0e53baea720) // permutation_comms[5].x_hi
            mstore(add(payload, 0x3c20), 0x7a90226e678437d20f2ec9ae630075a12ae88a186bcfba1bc0444e5bc40245e7) // permutation_comms[5].x_lo
            mstore(add(payload, 0x3c40), 0x0000000000000000000000000000000006ff1ce2b5e6c2c3cedd7a8465c5ed3a) // permutation_comms[5].y_hi
            mstore(add(payload, 0x3c60), 0x72e4496eead09ba2cd0ef56fdd94942ed738b42b71caea3d1bd78b0ae3ec3f96) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3c80), 0x000000000000000000000000000000000190af4fe845524352a9f624463ae7ca) // permutation_comms[6].x_hi
            mstore(add(payload, 0x3ca0), 0x406fa14f4319031fe5a7630ab2bd66c107d6cb05fa65b98ee0c5f0234c29d189) // permutation_comms[6].x_lo
            mstore(add(payload, 0x3cc0), 0x0000000000000000000000000000000013036a5f7dca90b530955bf735da2920) // permutation_comms[6].y_hi
            mstore(add(payload, 0x3ce0), 0x29b8759dc69e53d6c830a3bee081165d4d59442dacb50c2a06aded3193e88387) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3d00), 0x0000000000000000000000000000000012b6e22b800c1a2dfde554f3312f4b50) // permutation_comms[7].x_hi
            mstore(add(payload, 0x3d20), 0x1b75400de7c8c476dcc9fd72dcef80d9384da4e4af8f928a07e4a9fa485da8bc) // permutation_comms[7].x_lo
            mstore(add(payload, 0x3d40), 0x00000000000000000000000000000000053da19ebda674bbc95d3d10ad04cb96) // permutation_comms[7].y_hi
            mstore(add(payload, 0x3d60), 0xa410aecead2c7059df1e12a1a56117a830f0008a91551cec88f1ad548a379dfe) // permutation_comms[7].y_lo
            // Permutation commitment 8, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3d80), 0x0000000000000000000000000000000016038223f354e7d7c75614116c58b1c9) // permutation_comms[8].x_hi
            mstore(add(payload, 0x3da0), 0x866a8a39d6b30ea560b263c68da7e78210b2f2a7f9b19564388f2f2370d7cd6a) // permutation_comms[8].x_lo
            mstore(add(payload, 0x3dc0), 0x000000000000000000000000000000000bdb1d40f473070bfa087ff87bc9c86d) // permutation_comms[8].y_hi
            mstore(add(payload, 0x3de0), 0x0d57398e71f45845ebcd0aa24a9ea829718dfce700af80fab46b51ad73fb58f6) // permutation_comms[8].y_lo
            // Permutation commitment 9, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3e00), 0x00000000000000000000000000000000085c579504429306bbf0ec28b07f91a6) // permutation_comms[9].x_hi
            mstore(add(payload, 0x3e20), 0x7326fabf9ec866a45ef4d294f390a7c497c7b990a62b602f5999fcaee0e7e9bc) // permutation_comms[9].x_lo
            mstore(add(payload, 0x3e40), 0x000000000000000000000000000000000b042dab28398e8c0670ee6f04cca93a) // permutation_comms[9].y_hi
            mstore(add(payload, 0x3e60), 0xa41ecc7205c8216513d027b4c1213d0e452c16898d7b2c811027598cf2715dc3) // permutation_comms[9].y_lo
            // Permutation commitment 10, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3e80), 0x00000000000000000000000000000000093b6ec41dd5c2455b9d2dca635c472d) // permutation_comms[10].x_hi
            mstore(add(payload, 0x3ea0), 0x386496c219c45db9f1a5d96c179d1028694626c4a1845aef384efaaa8053284b) // permutation_comms[10].x_lo
            mstore(add(payload, 0x3ec0), 0x000000000000000000000000000000000386d1128886a4a879e8a93aa84b6525) // permutation_comms[10].y_hi
            mstore(add(payload, 0x3ee0), 0x1061026f4dae08952816961f9d6fc0b8153784a5961f831b68f1e2ddc567efb7) // permutation_comms[10].y_lo
            // Permutation commitment 11, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3f00), 0x0000000000000000000000000000000000b6ed6814a099c4e435e42fc8ee4250) // permutation_comms[11].x_hi
            mstore(add(payload, 0x3f20), 0x0e16b88c78069cebe20e4d647c8bb44acd6b9c6712d53a3ebd014e54a1a75e89) // permutation_comms[11].x_lo
            mstore(add(payload, 0x3f40), 0x0000000000000000000000000000000001ae3805b59b2f2d53a59e2c19001e97) // permutation_comms[11].y_hi
            mstore(add(payload, 0x3f60), 0xaace57ac2ba8b58550a740e897ba6278e409291e5c87466a01edd7cbe3b99f88) // permutation_comms[11].y_lo
            // Permutation commitment 12, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x3f80), 0x000000000000000000000000000000000ca3af5a65ec51141f694db29736dd57) // permutation_comms[12].x_hi
            mstore(add(payload, 0x3fa0), 0xa1cdbfa79f45aa80a6cdda8de3d51c4b16c95361b412c6f47e132eae7b69f7f7) // permutation_comms[12].x_lo
            mstore(add(payload, 0x3fc0), 0x0000000000000000000000000000000018dc16284e57fccd755058b259b913c7) // permutation_comms[12].y_hi
            mstore(add(payload, 0x3fe0), 0x7a54da0d0e206b7906878fd3e994ad04c66f48e19cd982d5651f99b48b992064) // permutation_comms[12].y_lo
            // Permutation commitment 13, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4000), 0x00000000000000000000000000000000197560c82bf47486bee750469d626ce4) // permutation_comms[13].x_hi
            mstore(add(payload, 0x4020), 0x2d40ce7489ff61a64a0eb55e6672926a40f06348ab575f926fbe4d87b672fcd7) // permutation_comms[13].x_lo
            mstore(add(payload, 0x4040), 0x0000000000000000000000000000000007b4f39a579a01d4f01f4ab9bc841a7d) // permutation_comms[13].y_hi
            mstore(add(payload, 0x4060), 0xe70541d6b79945e9569fd59388739f5b4ce57794044d287d7b0b58e35198caab) // permutation_comms[13].y_lo
            // Permutation commitment 14, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4080), 0x0000000000000000000000000000000004e1b539a3a123291eaa8c85be3395e7) // permutation_comms[14].x_hi
            mstore(add(payload, 0x40a0), 0x9c6845178d995313daf42680692210e1ec79278ec8b6e2da1d6f289609100404) // permutation_comms[14].x_lo
            mstore(add(payload, 0x40c0), 0x0000000000000000000000000000000010d56b62afe35890b4f98b946daa8936) // permutation_comms[14].y_hi
            mstore(add(payload, 0x40e0), 0xd83e014595585e2892e21bfc5e86f84d404b435dc1a689539d74773aba55dad4) // permutation_comms[14].y_lo
            // Permutation commitment 15, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4100), 0x000000000000000000000000000000000f227bcaef796cabf0a93289fb8321e9) // permutation_comms[15].x_hi
            mstore(add(payload, 0x4120), 0x1d43880fa5fcebab73c77c6bb406cc5e9386a81774635b5a6144b75ef10cd994) // permutation_comms[15].x_lo
            mstore(add(payload, 0x4140), 0x000000000000000000000000000000000a849d95d37e501cc6272f325f88d677) // permutation_comms[15].y_hi
            mstore(add(payload, 0x4160), 0xb25be83ce57eb9c32d382613930bbc0ef7ec349d44ac74a9383c111efcb73783) // permutation_comms[15].y_lo
            // Permutation commitment 16, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4180), 0x000000000000000000000000000000000b77ada25b279742ec75d2014583ad79) // permutation_comms[16].x_hi
            mstore(add(payload, 0x41a0), 0x427bfa99ab8a941648e1a11084fec2a6fdb8192f498cf3e272a5e786597273a1) // permutation_comms[16].x_lo
            mstore(add(payload, 0x41c0), 0x00000000000000000000000000000000056788c108fd40583888b8771a70d3f6) // permutation_comms[16].y_hi
            mstore(add(payload, 0x41e0), 0x364290f978d1fc201c0a76561a4c1cdde7643f7d76448dad2586c3eac2e34104) // permutation_comms[16].y_lo
            // Permutation commitment 17, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x4200), 0x0000000000000000000000000000000002ecf71916494d46153fdd513ead1917) // permutation_comms[17].x_hi
            mstore(add(payload, 0x4220), 0x06401b48839713727c920f4591fe09ac3e8f4140ef1cd9e39b0d0bbe0b5b87d4) // permutation_comms[17].x_lo
            mstore(add(payload, 0x4240), 0x000000000000000000000000000000000e7bab8cc3c714f06826c8f3695dc63c) // permutation_comms[17].y_hi
            mstore(add(payload, 0x4260), 0xe7e931ff0dbe009cbb84fef0b99124905d90cdd6f5356a7ee7673548f6f0692c) // permutation_comms[17].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x4281)
        }
    }
}