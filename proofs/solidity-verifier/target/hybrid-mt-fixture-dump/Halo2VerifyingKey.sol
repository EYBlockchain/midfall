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
            mstore(add(payload, 0x0000), 0x3095964b818e597a714e1e7fcde9bbf98d115ddd9590460a6c5a7519fdfb85e1) // vk_digest
            mstore(add(payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000001) // num_instances
            mstore(add(payload, 0x0040), 0x000000000000000000000000000000000000000000000000000000000000000d) // k
            mstore(add(payload, 0x0060), 0x73ea07e5ef04305c48f83e3949618af693930615dfe65c0c2007ffff00080001) // n_inv
            mstore(add(payload, 0x0080), 0x485d512737b1da3d2ccddea2972e89ed146b58bc434906ac6fdd00bfc78c8967) // omega
            mstore(add(payload, 0x00a0), 0x57e6990d4981b177d548fda262008419204f9476cecef2df68946aad325251ed) // omega_inv
            mstore(add(payload, 0x00c0), 0x482ec10c0dfb6cca3d4067ca08e2b3a4aca02a3a8f443648361e8ea8ae06b126) // omega_inv_to_l
            mstore(add(payload, 0x00e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
            mstore(add(payload, 0x0100), 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
            mstore(add(payload, 0x0120), 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
            mstore(add(payload, 0x0140), 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
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
            mstore(add(payload, 0x02e0), 0x00000000000000000000000000000000050ac27c3527072b81af0fa9a683e226) // neg_s_g2_x_c0_hi
            mstore(add(payload, 0x0300), 0xda79275f2985c9e89a0db969b76e0b6be94fee874c48586737ad5588cf1e1041) // neg_s_g2_x_c0_lo
            mstore(add(payload, 0x0320), 0x00000000000000000000000000000000116010f1b3d33aa5f3f608c385400979) // neg_s_g2_x_c1_hi
            mstore(add(payload, 0x0340), 0xed36dc3fab53d3626f519c74d7e1ebef62c9ad35796404ce2fc3ebb42167b5a1) // neg_s_g2_x_c1_lo
            mstore(add(payload, 0x0360), 0x0000000000000000000000000000000015b237e8c830b11d92578cb44ab0a93f) // neg_s_g2_y_c0_hi
            mstore(add(payload, 0x0380), 0x5176b4898e3a759bb6fba9e6c9375340a8a87557a3943686097db68d914e268e) // neg_s_g2_y_c0_lo
            mstore(add(payload, 0x03a0), 0x00000000000000000000000000000000006d57f79a18220d1e5ef04bd519e995) // neg_s_g2_y_c1_hi
            mstore(add(payload, 0x03c0), 0x9a9cc71553bb761b5422a6b6971b75c8d3695bfa07b861c4b1c958da426efc45) // neg_s_g2_y_c1_lo
            mstore(add(payload, 0x03e0), 0x0000000000000000000000000000000000000000000000000000000000000001) // quotient_const
            mstore(add(payload, 0x0400), 0x0000000000000000000000000000000000000000000000000000000000100000) // quotient_const
            mstore(add(payload, 0x0420), 0x0000000000000000000000000000000000000000000000000000040000000000) // quotient_const
            mstore(add(payload, 0x0440), 0x0000000000000000000000000000000000000000000000000000000000000002) // quotient_const
            mstore(add(payload, 0x0460), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffefff00001) // quotient_const
            mstore(add(payload, 0x0480), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffe00001) // quotient_const
            mstore(add(payload, 0x04a0), 0x0000000000000000000000000000000000000000000000000000000040400001) // quotient_const
            mstore(add(payload, 0x04c0), 0x0000000000000000000000000000000000000000000000004000000010100000) // quotient_const
            mstore(add(payload, 0x04e0), 0x0000000000000000000000000000000000000000000000000001000000004040) // quotient_const
            mstore(add(payload, 0x0500), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000) // quotient_const
            mstore(add(payload, 0x0520), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff) // quotient_const
            mstore(add(payload, 0x0540), 0x0000000000000000000000000000000000000000000000000000040000000101) // quotient_const
            mstore(add(payload, 0x0560), 0x0000000000000000000000000000000000000000000000000000000404000010) // quotient_const
            mstore(add(payload, 0x0580), 0x0000000000000000000000000000000000000000000000000000000101000004) // quotient_const
            mstore(add(payload, 0x05a0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffbff00000001) // quotient_const
            mstore(add(payload, 0x05c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffff7ff00000001) // quotient_const
            mstore(add(payload, 0x05e0), 0x0000000000000000000000000000000000000000000000000100000400000001) // quotient_const
            mstore(add(payload, 0x0600), 0x0000000000000000000000000000000000000000000000000004000010000000) // quotient_const
            mstore(add(payload, 0x0620), 0x0000000000000000000000000000000000000000000000004000000000010004) // quotient_const
            mstore(add(payload, 0x0640), 0x0000000000000000000000000000000000000000000000001000000000004001) // quotient_const
            mstore(add(payload, 0x0660), 0x0000000000000000000000000000000000000000000000000004400000000001) // quotient_const
            mstore(add(payload, 0x0680), 0x0000000000000000000000000000000000000000000000000000110000000000) // quotient_const
            mstore(add(payload, 0x06a0), 0x0000000000000000000000000000000000000000000000000000000000100044) // quotient_const
            mstore(add(payload, 0x06c0), 0x0000000000000000000000000000000000000000000000000000000000040011) // quotient_const
            mstore(add(payload, 0x06e0), 0x0000000000000000000000000000000000000000000000000000001100000000) // quotient_const
            mstore(add(payload, 0x0700), 0x0000000000000000000000000000000000000000000000000000000044000000) // quotient_const
            mstore(add(payload, 0x0720), 0x0000000000000000000000000000000000000000000000000000000000000400) // quotient_const
            mstore(add(payload, 0x0740), 0x0000000000000000000000000000000000000000000000000000000000200000) // quotient_const
            mstore(add(payload, 0x0760), 0x0000000000000000000000000000000000000000000000000000000000000004) // quotient_const
            mstore(add(payload, 0x0780), 0x0000000000000000000000000000000000000000000000000000000000002000) // quotient_const
            mstore(add(payload, 0x07a0), 0x0000000000000000000000000000000000000000000000000000000000400000) // quotient_const
            mstore(add(payload, 0x07c0), 0x0000000000000000000000000000000000000000000000000000000000000010) // quotient_const
            mstore(add(payload, 0x07e0), 0x0000000000000000000000000000000000000000000000000000000004000000) // quotient_const
            mstore(add(payload, 0x0800), 0x0000000000000000000000000000000000000000000000000000100000000000) // quotient_const
            mstore(add(payload, 0x0820), 0x0000000000000000000000000000000000000000000000000000000000000040) // quotient_const
            mstore(add(payload, 0x0840), 0x0000000000000000000000000000000000000000000000000000000000000800) // quotient_const
            mstore(add(payload, 0x0860), 0x0000000000000000000000000000000000000000000000000000000002000000) // quotient_const
            mstore(add(payload, 0x0880), 0x0000000000000000000000000000000000000000000000000000000000001000) // quotient_const
            mstore(add(payload, 0x08a0), 0x0000000000000000000000000000000000000000000000000004000000000000) // quotient_const
            mstore(add(payload, 0x08c0), 0x0000000000000000000000000000000000000000000000000000000000040000) // quotient_const
            mstore(add(payload, 0x08e0), 0x0000000000000000000000000000000000000000000000000000000000000080) // quotient_const
            mstore(add(payload, 0x0900), 0x0000000000000000000000000000000000000000000000000000000000000008) // quotient_const
            mstore(add(payload, 0x0920), 0x0000000000000000000000000000000000000000000000000000000000080000) // quotient_const
            mstore(add(payload, 0x0940), 0x0000000000000000000000000000000000000000000000000000000000020000) // quotient_const
            mstore(add(payload, 0x0960), 0x0000000000000000000000000000000000000000000000000000000100000000) // quotient_const
            mstore(add(payload, 0x0980), 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140) // quotient_const
            mstore(add(payload, 0x09a0), 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a) // quotient_const
            mstore(add(payload, 0x09c0), 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db) // quotient_const
            mstore(add(payload, 0x09e0), 0x056b00106e20056ba008060d000b020001056c20106c40106b200902116c8013) // quotient_program
            mstore(add(payload, 0x0a00), 0x6ae001106b800902116c60136ac001106b600d030608060d000b030000056c20) // quotient_program
            mstore(add(payload, 0x0a20), 0x106c400902116c80136ae001106b800902116c60136ac001106b600d03060806) // quotient_program
            mstore(add(payload, 0x0a40), 0x0d000b040000056b00106b20056b4008060d000b0400011b00001b0001210001) // quotient_program
            mstore(add(payload, 0x0a60), 0x00000700046ac0056ae0066b00076b20086b40096b600a6b800b6ba00c6c200d) // quotient_program
            mstore(add(payload, 0x0a80), 0x6c400e6c600f6c80106ca0116cc00b07000021000100000700046ac0056ae012) // quotient_program
            mstore(add(payload, 0x0aa0), 0x6b00136b20146b40096b600a6b80156ba0166c20176c400e6c600f6c80186ca0) // quotient_program
            mstore(add(payload, 0x0ac0), 0x196cc00b080000091b116ce0136be01a106d00056d2008060d000b090000091e) // quotient_program
            mstore(add(payload, 0x0ae0), 0x116ce0136d401d136be01c106c00056d2008060d000b0a00000921116c60136c) // quotient_program
            mstore(add(payload, 0x0b00), 0x8020136ac01f106ae0056b0008060d000b0a00010924116ce0136d401d136be0) // quotient_program
            mstore(add(payload, 0x0b20), 0x23136c0022106d00056d2008060d000b0b00000926116c60136c8020136ac01e) // quotient_program
            mstore(add(payload, 0x0b40), 0x136ae025106b60056b0008060d000b0b00011c276bc0286be0296c00016ce01a) // quotient_program
            mstore(add(payload, 0x0b60), 0x6d402a6d602b6d80106d00056d2008060d000b0c0000090008106d60116d600d) // quotient_program
            mstore(add(payload, 0x0b80), 0x000b0c0001090008106bc0116bc00d000b0c0001090008106d80116d800d000b) // quotient_program
            mstore(add(payload, 0x0ba0), 0x0c00011c006b20006b40006ba0006c20006c40006ca0006cc0056d20136da02c) // quotient_program
            mstore(add(payload, 0x0bc0), 0x08060d000b0d0000056ac0116ac0116ac0056b2008060d000b0e0000056ae011) // quotient_program
            mstore(add(payload, 0x0be0), 0x6ae0116ae0056b4008060d000b0e0001056b00116b00116b00056bc008060d00) // quotient_program
            mstore(add(payload, 0x0c00), 0x0b0e00011b00021b0003056ba008106ec0056ac0116ac0116b200d2d06056ae0) // quotient_program
            mstore(add(payload, 0x0c20), 0x116ae0116b400d2e06056b00116b00116bc00d2f060d000b0e0001191f000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0c40), 0x0000000000000000000000000000000002586b66bd923976cc5f5c9ff774e3c2) // fixed_comms[0].x_hi
            mstore(add(payload, 0x0c60), 0x4c7d81ebb48c375f60b589dd2a045113d5f9713f050593446cc4eaa25fd33c89) // fixed_comms[0].x_lo
            mstore(add(payload, 0x0c80), 0x0000000000000000000000000000000002eaaa05aba5434574729c11ae5666a5) // fixed_comms[0].y_hi
            mstore(add(payload, 0x0ca0), 0xb72148a9fa9d17d6618863b9f04b14aa377b8825a68b8ae81d5ab8d8d13cb87d) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0cc0), 0x000000000000000000000000000000000d872308c4affeb472e8e9aebbcb4e96) // fixed_comms[1].x_hi
            mstore(add(payload, 0x0ce0), 0xb6e42fc7ce92036f8e99d03e53683805c11cea6424c0e461977a453c0af7cffb) // fixed_comms[1].x_lo
            mstore(add(payload, 0x0d00), 0x00000000000000000000000000000000091958dfe05710bd711509a38c56a1ac) // fixed_comms[1].y_hi
            mstore(add(payload, 0x0d20), 0xc6df3e06ea945e3cc6c9845de6cea4e07d7512631d0aa66a3e29cd63797e4fb3) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0d40), 0x000000000000000000000000000000000adb10dcd9c7aa423ae347e16c4f7964) // fixed_comms[2].x_hi
            mstore(add(payload, 0x0d60), 0x69b2f06c183ea6e84cbbc23e02181a26701459cf2250a769f83b5559d9d8f9be) // fixed_comms[2].x_lo
            mstore(add(payload, 0x0d80), 0x00000000000000000000000000000000190db1f748d53f20c968850f8cc3ec13) // fixed_comms[2].y_hi
            mstore(add(payload, 0x0da0), 0x499cdaac032d4c68527ba52fe2f17bf5e061362bf72a0f9d43b0ee382838c01e) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0dc0), 0x000000000000000000000000000000001489ea7f6dc15c25eeeb5e1c49090263) // fixed_comms[3].x_hi
            mstore(add(payload, 0x0de0), 0x57c5faf5c3186b03bc41d35333119596a918a0ce8ec6ad08918fbd5df8038ba7) // fixed_comms[3].x_lo
            mstore(add(payload, 0x0e00), 0x000000000000000000000000000000001525a1407c4da1d48faf5d67e454cfb3) // fixed_comms[3].y_hi
            mstore(add(payload, 0x0e20), 0x7fe50e5507e74ae67d9c9bcbdddf312adc77b26e60501ffe51531ba0aa98ff0e) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0e40), 0x000000000000000000000000000000000e5ce69bb06ef4063e3729eb0c29c2c8) // fixed_comms[4].x_hi
            mstore(add(payload, 0x0e60), 0x9b0a383e959d28a18704345717dd864ca64b0cd759edc1059d59d314fa22b61d) // fixed_comms[4].x_lo
            mstore(add(payload, 0x0e80), 0x000000000000000000000000000000000f720782ccfafebd68233967d21fcf07) // fixed_comms[4].y_hi
            mstore(add(payload, 0x0ea0), 0xeabdf5f335cc1711c7a3973e86e1a3d9ba6ca84f4aa5d55d446f6739181448df) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ec0), 0x000000000000000000000000000000000b5c788c904a739dc77d865623db6b1d) // fixed_comms[5].x_hi
            mstore(add(payload, 0x0ee0), 0x246530f955e06db6596fd9c87c3adde78ce6426be95abb5ff0b6bdef98297f59) // fixed_comms[5].x_lo
            mstore(add(payload, 0x0f00), 0x00000000000000000000000000000000103903a7ce919f3ecf7f36fdf03ba1bc) // fixed_comms[5].y_hi
            mstore(add(payload, 0x0f20), 0x652e6f52525c6e03588c5a97344b9b64cb982f6f46393bf42b6664d1acd4e52c) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0f40), 0x000000000000000000000000000000000689e5143ff2ed5467eb752f7b9fd6b7) // fixed_comms[6].x_hi
            mstore(add(payload, 0x0f60), 0xeb90412024ce1d23701d35af783b33a74bef98fcb0882ea1d5e276c29aa2d855) // fixed_comms[6].x_lo
            mstore(add(payload, 0x0f80), 0x0000000000000000000000000000000002b1fc6e62f2035ace88d6f14c5bf6ed) // fixed_comms[6].y_hi
            mstore(add(payload, 0x0fa0), 0x355a5c9fb62755a0d5f6c554393f4c0ba9c829e8875a8485f797a7a932e7ac48) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0fc0), 0x000000000000000000000000000000000d66944264ab5aea06ebc45ca12d06bf) // fixed_comms[7].x_hi
            mstore(add(payload, 0x0fe0), 0xb4580b27e4e32510726d659e03c9a7b0b3ec7d8c3bfe63c8d16f7734b7f96f32) // fixed_comms[7].x_lo
            mstore(add(payload, 0x1000), 0x00000000000000000000000000000000181b724bc94ca13fffe48c70af930ffb) // fixed_comms[7].y_hi
            mstore(add(payload, 0x1020), 0x9e78eb1aadeacca4277384f24c7ddb6d9ef0234125d11dc2a6f1aeab3dd7f9e3) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1040), 0x00000000000000000000000000000000076801d76bcca0075faa710cbe2866df) // fixed_comms[8].x_hi
            mstore(add(payload, 0x1060), 0x6d8512c8b10c0a8f3e7e49bec5b68aab6963c02f0bf5ea340861cf39d2e1d380) // fixed_comms[8].x_lo
            mstore(add(payload, 0x1080), 0x000000000000000000000000000000001990c4414d8008924db47345766dca4b) // fixed_comms[8].y_hi
            mstore(add(payload, 0x10a0), 0xabf2c5b4b2f80141ea5d257878b20ac64496f9c0a3499f2ad54a91e5c7b9281a) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x10c0), 0x00000000000000000000000000000000191c0eb4af0682de2cb1a7b15415af68) // fixed_comms[9].x_hi
            mstore(add(payload, 0x10e0), 0x5e110b8450c36629f0838aae3c213956db1c832c89b14bbcc1a8385581440c20) // fixed_comms[9].x_lo
            mstore(add(payload, 0x1100), 0x000000000000000000000000000000000604b3ad28337a2d4a52200aaa9e1580) // fixed_comms[9].y_hi
            mstore(add(payload, 0x1120), 0xf26d100a91e1cfe4b03848a38420dea292b135f3dd614e6099c271b84c5e6d83) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1140), 0x0000000000000000000000000000000013fab537732cd4d7c909df3407ca101e) // fixed_comms[10].x_hi
            mstore(add(payload, 0x1160), 0x59134da62ea6ebb9027238d6c818469daf8eb74defe1862778134c9ba899a260) // fixed_comms[10].x_lo
            mstore(add(payload, 0x1180), 0x0000000000000000000000000000000019e035cae3a430aeac4ef24db368fcd8) // fixed_comms[10].y_hi
            mstore(add(payload, 0x11a0), 0x007fa3dc5274e82c741b3a9baa2469f1977a9e314f9ed4834e125069d2db7ade) // fixed_comms[10].y_lo
            // Fixed-column commitment 11, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x11c0), 0x000000000000000000000000000000000a1d5e2467501774e14ea37009b1f0fc) // fixed_comms[11].x_hi
            mstore(add(payload, 0x11e0), 0xe036861d0edd2800de1897c52427efdd76119313f58702d9f6206f5d919205a6) // fixed_comms[11].x_lo
            mstore(add(payload, 0x1200), 0x000000000000000000000000000000000163e07fe7abc7eefcf10c4fc077ac83) // fixed_comms[11].y_hi
            mstore(add(payload, 0x1220), 0xbcbaeef8510a5414f3852485a1c606ebdcdc1d47479ae672f885b65236cc1178) // fixed_comms[11].y_lo
            // Fixed-column commitment 12, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1240), 0x0000000000000000000000000000000007ea65510f739ba93e197d96fe51315c) // fixed_comms[12].x_hi
            mstore(add(payload, 0x1260), 0x4ff6d08381846cfa7f259a220baec1ac596730b3b3a72777190fd06e9295e898) // fixed_comms[12].x_lo
            mstore(add(payload, 0x1280), 0x00000000000000000000000000000000171f9496628be1c6b2275190355ceabf) // fixed_comms[12].y_hi
            mstore(add(payload, 0x12a0), 0x07dbc6e73f60b4e46996478a0176c5e172d2c8ae09e19e79aa2180f5e355a256) // fixed_comms[12].y_lo
            // Fixed-column commitment 13, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x12c0), 0x0000000000000000000000000000000007a8e5fefc1e2cb2b18457f610373429) // fixed_comms[13].x_hi
            mstore(add(payload, 0x12e0), 0xea2f97565be5f3e624e6f5c7ee6cff2849bf7a467bfba9ed3cb7c04d0d8dea80) // fixed_comms[13].x_lo
            mstore(add(payload, 0x1300), 0x0000000000000000000000000000000010deff2c658634ee66b061b51f8fe06c) // fixed_comms[13].y_hi
            mstore(add(payload, 0x1320), 0x0d44294528465cb93593bc6c916c3f5243bc8cd81b74579b2296d7a865215037) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1340), 0x000000000000000000000000000000000cb5e27e7b6858c023303122953e23cd) // fixed_comms[14].x_hi
            mstore(add(payload, 0x1360), 0x4ad001528d160e8dc98dcc2bd2c0f384fc4805e1d7a937ac8a1dd23b72a12739) // fixed_comms[14].x_lo
            mstore(add(payload, 0x1380), 0x0000000000000000000000000000000016d4b9cc8ccd6d6dc8638a9c37c140ad) // fixed_comms[14].y_hi
            mstore(add(payload, 0x13a0), 0x99d34a70b64ff639e14dbd48bddeb4e7b8c888f13b9564f3ff3ba1999f86f054) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x13c0), 0x0000000000000000000000000000000013099474513438bbf5b4448f5fee5d68) // fixed_comms[15].x_hi
            mstore(add(payload, 0x13e0), 0xfbb1c3ceb876f012e99815d7af288f05f309fbc1fe61d095ad8ea73da21d8c69) // fixed_comms[15].x_lo
            mstore(add(payload, 0x1400), 0x0000000000000000000000000000000019fb64331b26eb7fa8db2e9d10923c52) // fixed_comms[15].y_hi
            mstore(add(payload, 0x1420), 0xed0d0c8eaf654d53b930083eeb5b99042cdeaded3cb4f6bb8be1a762d201b8bd) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1440), 0x00000000000000000000000000000000089255d90fbb43a6dd5721e9ec9a828a) // fixed_comms[16].x_hi
            mstore(add(payload, 0x1460), 0x2253163e79419564123b4f73d6d6fa29a4f8ea183867ac20c2df6e9810ff8e9a) // fixed_comms[16].x_lo
            mstore(add(payload, 0x1480), 0x000000000000000000000000000000000a6ac4c8cd122487bb6b24d76b79a438) // fixed_comms[16].y_hi
            mstore(add(payload, 0x14a0), 0xfcd0ed94a39a18fa11570f4d3c441849f0cadc8e84b3e28cc5f5a51908ebd217) // fixed_comms[16].y_lo
            // Fixed-column commitment 17, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x14c0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x_hi
            mstore(add(payload, 0x14e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x_lo
            mstore(add(payload, 0x1500), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y_hi
            mstore(add(payload, 0x1520), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y_lo
            // Fixed-column commitment 18, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1540), 0x0000000000000000000000000000000001979f8e77bee0edcee0dc906be72961) // fixed_comms[18].x_hi
            mstore(add(payload, 0x1560), 0x01a5f92a06990caf694cb14649e4405c9af8d57d0c97eddf62f1412a159e64fb) // fixed_comms[18].x_lo
            mstore(add(payload, 0x1580), 0x0000000000000000000000000000000019ceb25b824fdd5b4b8217dfd6689f8b) // fixed_comms[18].y_hi
            mstore(add(payload, 0x15a0), 0x5f6e980f683eedd72ef903643cc0ce11d393c090107da144b116ace59941a02f) // fixed_comms[18].y_lo
            // Fixed-column commitment 19, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x15c0), 0x0000000000000000000000000000000019c1f9d11f44fdb0d97f4e4dd47ac71d) // fixed_comms[19].x_hi
            mstore(add(payload, 0x15e0), 0x06a1e646a1217a0fefde98ec31440905f04e75b7c5f804c0dcad3486c0d650f9) // fixed_comms[19].x_lo
            mstore(add(payload, 0x1600), 0x0000000000000000000000000000000014c63467c6f7c0efc081a924879b3b3f) // fixed_comms[19].y_hi
            mstore(add(payload, 0x1620), 0xcbf6ac592336c180f628724ab57405a53a538cdee52d5cde41e4a957bac67c56) // fixed_comms[19].y_lo
            // Fixed-column commitment 20, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1640), 0x00000000000000000000000000000000063cad299ba543710c9c4759acc8d529) // fixed_comms[20].x_hi
            mstore(add(payload, 0x1660), 0x07c61057f5a60fca813219ba15723eea19ae7a254c49eb4f13f2cae06a84562e) // fixed_comms[20].x_lo
            mstore(add(payload, 0x1680), 0x0000000000000000000000000000000012e01d3706f295afe4dc3e0f939b31fc) // fixed_comms[20].y_hi
            mstore(add(payload, 0x16a0), 0xe1c4976e00569e2068dc29901217eac336c20c12b39aff48ee84af01b2642b8b) // fixed_comms[20].y_lo
            // Fixed-column commitment 21, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x16c0), 0x00000000000000000000000000000000032a288cc8ce750bac9a289cb5e193db) // fixed_comms[21].x_hi
            mstore(add(payload, 0x16e0), 0x031752f534765e2d1fa765ebb5d69ae3037d04b6a5815d5e8d016e13318f6277) // fixed_comms[21].x_lo
            mstore(add(payload, 0x1700), 0x000000000000000000000000000000000529f601181bf5930a70f79775086abd) // fixed_comms[21].y_hi
            mstore(add(payload, 0x1720), 0x6912d1e049044feda3c957d6dae5c5c951ce07e7b91d3ebd669a5f9c063e4a34) // fixed_comms[21].y_lo
            // Fixed-column commitment 22, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1740), 0x0000000000000000000000000000000003a836c4089f0a5e7f8200c847b97947) // fixed_comms[22].x_hi
            mstore(add(payload, 0x1760), 0xd7ed9341a1ebd663147ac640f0ac5f67a9b1d10756691947729f48f22ee85832) // fixed_comms[22].x_lo
            mstore(add(payload, 0x1780), 0x000000000000000000000000000000001362fee908356060ea8ac0a072f7555b) // fixed_comms[22].y_hi
            mstore(add(payload, 0x17a0), 0xb7436fe39363a9c33a650a7e7ca69c2f1a4c135e1fc60e548e20f1cbd2f98b98) // fixed_comms[22].y_lo
            // Fixed-column commitment 23, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x17c0), 0x0000000000000000000000000000000013de306919866689e2c223900230ac67) // fixed_comms[23].x_hi
            mstore(add(payload, 0x17e0), 0xc2f2479641d262363a756ce096cdd07302075737d324674f3159a2f4fcb615a0) // fixed_comms[23].x_lo
            mstore(add(payload, 0x1800), 0x0000000000000000000000000000000007300c226a1cda8750a659de2d0f96d6) // fixed_comms[23].y_hi
            mstore(add(payload, 0x1820), 0x9cb7b45faedc7840b254fe1a5dabf60419ccb899c4555662880a65942ffa5c4c) // fixed_comms[23].y_lo
            // Fixed-column commitment 24, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1840), 0x00000000000000000000000000000000094f2a4b1165515420f0bac68fc04c2b) // fixed_comms[24].x_hi
            mstore(add(payload, 0x1860), 0x60ea7c724a55d9bbd95c3016fdf84bc46cb50ea0a7ee840e73a9fd6e5d980f23) // fixed_comms[24].x_lo
            mstore(add(payload, 0x1880), 0x0000000000000000000000000000000002b0989e8f99ec8dfa04826522340c29) // fixed_comms[24].y_hi
            mstore(add(payload, 0x18a0), 0x47b1aa9037e6236a0dd89b0b351812284a4bfbfe20e9eec55d33ed4d5dae58bf) // fixed_comms[24].y_lo
            // Fixed-column commitment 25, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x18c0), 0x0000000000000000000000000000000008d2cdedb6da9191f240f001432118ac) // fixed_comms[25].x_hi
            mstore(add(payload, 0x18e0), 0x178b42300677b64652b5b116b95052a5fe513b4fc73a6e00bdb50c6053c2d046) // fixed_comms[25].x_lo
            mstore(add(payload, 0x1900), 0x000000000000000000000000000000000b1a8ece8cff38a43effa66b514427bf) // fixed_comms[25].y_hi
            mstore(add(payload, 0x1920), 0xe8e81c0ab0a18d0bbbcaea15edc22a22a21276b7ac4c78b7b3e5870bb7e0007e) // fixed_comms[25].y_lo
            // Fixed-column commitment 26, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1940), 0x0000000000000000000000000000000013f270335073f3b0c4e0e6834cc18f4c) // fixed_comms[26].x_hi
            mstore(add(payload, 0x1960), 0xb17c8cd5d3c0580034c831dd8c98b7a41c82a1049db32d47ca034c760ba7f7ba) // fixed_comms[26].x_lo
            mstore(add(payload, 0x1980), 0x0000000000000000000000000000000010e92a121dc6cf469e565442033b2a3c) // fixed_comms[26].y_hi
            mstore(add(payload, 0x19a0), 0x15c08a17731c2b92ce2acacd640fbf23461c5241475c2287e114d0c024b41f99) // fixed_comms[26].y_lo
            // Fixed-column commitment 27, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x19c0), 0x000000000000000000000000000000000d8554de77ef93416e5974b363481659) // fixed_comms[27].x_hi
            mstore(add(payload, 0x19e0), 0x6061398c58bf696781a33535b879cc2f73375d15e0bca947c81b2ec95fc85e75) // fixed_comms[27].x_lo
            mstore(add(payload, 0x1a00), 0x00000000000000000000000000000000036891ac6a88aa0ced2439d412b20468) // fixed_comms[27].y_hi
            mstore(add(payload, 0x1a20), 0x8a05139741e940662f008578ddcc42176668f3ced00b1605a93ab0a859dcd5b9) // fixed_comms[27].y_lo
            // Fixed-column commitment 28, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1a40), 0x0000000000000000000000000000000003cd03f436a492de29c0bad7996111ad) // fixed_comms[28].x_hi
            mstore(add(payload, 0x1a60), 0x0a43e0f468a18d13431d8b3a2968370d360f7dc84e0fd463330ba16b8f364f7f) // fixed_comms[28].x_lo
            mstore(add(payload, 0x1a80), 0x0000000000000000000000000000000001ed1855ac1eb7dc676889f2cb725e5e) // fixed_comms[28].y_hi
            mstore(add(payload, 0x1aa0), 0x590f74b062a7a0cedc3b5d844bb1ff34be3d0e0ea0afe2685790134281a6cdfb) // fixed_comms[28].y_lo
            // Fixed-column commitment 29, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1ac0), 0x00000000000000000000000000000000177e3226acf365ce7c9a1aece0d2cc4d) // fixed_comms[29].x_hi
            mstore(add(payload, 0x1ae0), 0x73fef47966a9e2df5b97c8c043596f3555843d579f423c6c43a30f50fa3b36ec) // fixed_comms[29].x_lo
            mstore(add(payload, 0x1b00), 0x0000000000000000000000000000000016c892ebb591966bce7b656907312370) // fixed_comms[29].y_hi
            mstore(add(payload, 0x1b20), 0x5a7e5ea68503a8c8b7c6285e2c7fd01153a5287d1e61057c137ed58139a327f5) // fixed_comms[29].y_lo
            // Fixed-column commitment 30, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1b40), 0x0000000000000000000000000000000001032229fb49e51729fdcc860de03c34) // fixed_comms[30].x_hi
            mstore(add(payload, 0x1b60), 0x19072a3d6d78180921247907f3ef2a10d73879cec477fdc3ca0478442998cc1c) // fixed_comms[30].x_lo
            mstore(add(payload, 0x1b80), 0x0000000000000000000000000000000017f2831a2df7f210b381668ca82f10c3) // fixed_comms[30].y_hi
            mstore(add(payload, 0x1ba0), 0xde999ad3f24db5fd455aa0f99ca52517689c5f35a04ba33576bcc7ba7734c35b) // fixed_comms[30].y_lo
            // Fixed-column commitment 31, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1bc0), 0x000000000000000000000000000000000c40d2e23d39c15dabb1add27eb3b457) // fixed_comms[31].x_hi
            mstore(add(payload, 0x1be0), 0xca59c188d0fe52a76c85a8b7bf203115ce0ebf851c89028201f7a50ab629891e) // fixed_comms[31].x_lo
            mstore(add(payload, 0x1c00), 0x00000000000000000000000000000000199932c609f22b63d0092405d03be7b1) // fixed_comms[31].y_hi
            mstore(add(payload, 0x1c20), 0x1052832328107a61597d0cc01fd7661d3abfa76b326289009f53c21e5160c74d) // fixed_comms[31].y_lo
            // Fixed-column commitment 32, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1c40), 0x0000000000000000000000000000000002e3b70cc94abd9f6a2e2ee70cd241ea) // fixed_comms[32].x_hi
            mstore(add(payload, 0x1c60), 0x8a206b22e998e1d81b0684e0a2137e32e12094b93f674cb119b01e86f499fd0a) // fixed_comms[32].x_lo
            mstore(add(payload, 0x1c80), 0x0000000000000000000000000000000019cb8541c16185fd8989879a3836d235) // fixed_comms[32].y_hi
            mstore(add(payload, 0x1ca0), 0x037bb212b1ecdd963c2d7999ab2082188ecec03955f7d34a42f0fa5128b87e20) // fixed_comms[32].y_lo
            // Fixed-column commitment 33, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1cc0), 0x0000000000000000000000000000000004c1bc02a31986362e18d5d8989877d3) // fixed_comms[33].x_hi
            mstore(add(payload, 0x1ce0), 0x7eb55cb719d6226c8a3ef2bd2e28136893c068bc89984b33696690ee806fb34d) // fixed_comms[33].x_lo
            mstore(add(payload, 0x1d00), 0x0000000000000000000000000000000014da1253a52c6e760983b32b04bb7c60) // fixed_comms[33].y_hi
            mstore(add(payload, 0x1d20), 0xde40795930a06bf9e47eb13eca56ea562f257676522df22d83beb5897141e202) // fixed_comms[33].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1d40), 0x000000000000000000000000000000000f3f4c59d73d3a62831393103832c2d6) // permutation_comms[0].x_hi
            mstore(add(payload, 0x1d60), 0x2345d35ecc415eac9c8f08389c2b54f949e4fe4db2528ff22d8e0b12dbca545f) // permutation_comms[0].x_lo
            mstore(add(payload, 0x1d80), 0x00000000000000000000000000000000034c6ad1047664d57a551fcbaad7dd7b) // permutation_comms[0].y_hi
            mstore(add(payload, 0x1da0), 0x0d0e67b6605dacb126fe438f2ced6755f392350966271024e75eb817d6341d25) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1dc0), 0x000000000000000000000000000000000e366e632cc6cfef420ca4a41e1f7473) // permutation_comms[1].x_hi
            mstore(add(payload, 0x1de0), 0xccd96459cee144c3ba93d34e65b72e20dd3a56cd3b79eed4efaa1e736445e8b5) // permutation_comms[1].x_lo
            mstore(add(payload, 0x1e00), 0x000000000000000000000000000000000828f44db2c469b837cf253f1ca2562c) // permutation_comms[1].y_hi
            mstore(add(payload, 0x1e20), 0xdd03440599b2be9c4ffb19575fa67c30341ad907c37a3826cd2cc63031167a15) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1e40), 0x00000000000000000000000000000000055b04fb8976c82f5948003ba946ed06) // permutation_comms[2].x_hi
            mstore(add(payload, 0x1e60), 0x6ee0497d58e44d17178651a0fcfb88debdf1b4aef90f36a35f6301553b84ec35) // permutation_comms[2].x_lo
            mstore(add(payload, 0x1e80), 0x0000000000000000000000000000000011b80da55637905c294ea5e5f15d51b3) // permutation_comms[2].y_hi
            mstore(add(payload, 0x1ea0), 0x8421190919118d6b0f273186fb4434974680f505660d5c20aacd100ff766ce14) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1ec0), 0x000000000000000000000000000000000cc57088ec70976350c1c41c88c50536) // permutation_comms[3].x_hi
            mstore(add(payload, 0x1ee0), 0x031bd12207f24285b2bb6e0b879a9aa65bbbe55b6dc5f5786cc02768b0644d6b) // permutation_comms[3].x_lo
            mstore(add(payload, 0x1f00), 0x000000000000000000000000000000000446fdf5f73a7fcc6dce4906479f9c23) // permutation_comms[3].y_hi
            mstore(add(payload, 0x1f20), 0x213149ce7c34157e32ef93edaa02ecce49b502b4c372c23b99047e760d831ff2) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1f40), 0x000000000000000000000000000000001478724c64c34763436f01d7f32d9be8) // permutation_comms[4].x_hi
            mstore(add(payload, 0x1f60), 0x5e17370d05f4bd599db290a756a4191c64b171f1399af24f02a043cb0252a180) // permutation_comms[4].x_lo
            mstore(add(payload, 0x1f80), 0x0000000000000000000000000000000014f780076172f8f408a293ef5c61cf45) // permutation_comms[4].y_hi
            mstore(add(payload, 0x1fa0), 0xa2a1184159a53804590032d1f5475a226c4d20bdd33fbc596acbb43dd6539514) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1fc0), 0x0000000000000000000000000000000002f767a05d0d4c7b3edbaf418fa2d4d3) // permutation_comms[5].x_hi
            mstore(add(payload, 0x1fe0), 0x4437e77cf5526abe74d4f32e5954b367bf8490779704d779b0891c5fb0b9940a) // permutation_comms[5].x_lo
            mstore(add(payload, 0x2000), 0x0000000000000000000000000000000007017384df569e99d64ec7cd6bca931b) // permutation_comms[5].y_hi
            mstore(add(payload, 0x2020), 0x03487cb029c626b5817124d5e26f3b37eb7eb2860041d7afc216c7e0f1aa82cd) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2040), 0x0000000000000000000000000000000019508b48fdb2975eb118421b6a190674) // permutation_comms[6].x_hi
            mstore(add(payload, 0x2060), 0x6abfee37a2564e1467c236d58174d40a090900bdcb6103b0d9709c55193eaf76) // permutation_comms[6].x_lo
            mstore(add(payload, 0x2080), 0x0000000000000000000000000000000003e7d72102d8042da5445b802352e37d) // permutation_comms[6].y_hi
            mstore(add(payload, 0x20a0), 0x6f49027a39ba2a781eed399a95b4987c9dd7703e79bafe4de4ff43325b771139) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x20c0), 0x000000000000000000000000000000001657d945ee77a54b9731debd291af338) // permutation_comms[7].x_hi
            mstore(add(payload, 0x20e0), 0x761946810049cf6a02ef830c1b0909ff10387b9734f4d39ece6bf89030009ee4) // permutation_comms[7].x_lo
            mstore(add(payload, 0x2100), 0x000000000000000000000000000000001080ff480acb473614109994b3ef563a) // permutation_comms[7].y_hi
            mstore(add(payload, 0x2120), 0xa52e4f13d520c20f6fbfd381aa5936a0a5ec52f201965bcb5897793414937796) // permutation_comms[7].y_lo
            // Permutation commitment 8, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x2140), 0x0000000000000000000000000000000018c7630da28b67b14a95ca68c4bf6f65) // permutation_comms[8].x_hi
            mstore(add(payload, 0x2160), 0xcde75f9c023c2d1a67eced253bc191daa40fcb6bae48aaa1f7931500399c42f4) // permutation_comms[8].x_lo
            mstore(add(payload, 0x2180), 0x000000000000000000000000000000000717a171842455bc9a8114af7a108c89) // permutation_comms[8].y_hi
            mstore(add(payload, 0x21a0), 0x51673835abcf3a5e5b421c9039cd504ebd477f2f0e176ba6c5aa5fe5c82c7f8f) // permutation_comms[8].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x21c1)
        }
    }
}