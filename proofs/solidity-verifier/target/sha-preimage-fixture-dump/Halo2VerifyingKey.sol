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
            mstore(add(payload, 0x0000), 0x010fb8e344305a8a01e6320aed0d34d406ad65612face26ac1ebe61d872816e3) // vk_digest
            mstore(add(payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000020) // num_instances
            mstore(add(payload, 0x0040), 0x000000000000000000000000000000000000000000000000000000000000000d) // k
            mstore(add(payload, 0x0060), 0x73ea07e5ef04305c48f83e3949618af693930615dfe65c0c2007ffff00080001) // n_inv
            mstore(add(payload, 0x0080), 0x485d512737b1da3d2ccddea2972e89ed146b58bc434906ac6fdd00bfc78c8967) // omega
            mstore(add(payload, 0x00a0), 0x57e6990d4981b177d548fda262008419204f9476cecef2df68946aad325251ed) // omega_inv
            mstore(add(payload, 0x00c0), 0x587ef47ebaabb080cae9f31d0271872db7fc93ca9fe433364308f6f61fd57922) // omega_inv_to_l
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
            mstore(add(payload, 0x0400), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffefff00001) // quotient_const
            mstore(add(payload, 0x0420), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffe00001) // quotient_const
            mstore(add(payload, 0x0440), 0x0000000000000000000000000000000000000000000000000000000040400001) // quotient_const
            mstore(add(payload, 0x0460), 0x0000000000000000000000000000000000000000000000004000000010100000) // quotient_const
            mstore(add(payload, 0x0480), 0x0000000000000000000000000000000000000000000000000001000000004040) // quotient_const
            mstore(add(payload, 0x04a0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000) // quotient_const
            mstore(add(payload, 0x04c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff) // quotient_const
            mstore(add(payload, 0x04e0), 0x0000000000000000000000000000000000000000000000000000040000000101) // quotient_const
            mstore(add(payload, 0x0500), 0x0000000000000000000000000000000000000000000000000000000404000010) // quotient_const
            mstore(add(payload, 0x0520), 0x0000000000000000000000000000000000000000000000000000000101000004) // quotient_const
            mstore(add(payload, 0x0540), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffbff00000001) // quotient_const
            mstore(add(payload, 0x0560), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffff7ff00000001) // quotient_const
            mstore(add(payload, 0x0580), 0x0000000000000000000000000000000000000000000000000100000400000001) // quotient_const
            mstore(add(payload, 0x05a0), 0x0000000000000000000000000000000000000000000000000004000010000000) // quotient_const
            mstore(add(payload, 0x05c0), 0x0000000000000000000000000000000000000000000000004000000000010004) // quotient_const
            mstore(add(payload, 0x05e0), 0x0000000000000000000000000000000000000000000000001000000000004001) // quotient_const
            mstore(add(payload, 0x0600), 0x0000000000000000000000000000000000000000000000000004400000000001) // quotient_const
            mstore(add(payload, 0x0620), 0x0000000000000000000000000000000000000000000000000000110000000000) // quotient_const
            mstore(add(payload, 0x0640), 0x0000000000000000000000000000000000000000000000000000000000100044) // quotient_const
            mstore(add(payload, 0x0660), 0x0000000000000000000000000000000000000000000000000000000000040011) // quotient_const
            mstore(add(payload, 0x0680), 0x0000000000000000000000000000000000000000000000000000001100000000) // quotient_const
            mstore(add(payload, 0x06a0), 0x0000000000000000000000000000000000000000000000000000000044000000) // quotient_const
            mstore(add(payload, 0x06c0), 0x0000000000000000000000000000000000000000000000000000000000000400) // quotient_const
            mstore(add(payload, 0x06e0), 0x0000000000000000000000000000000000000000000000000000000000200000) // quotient_const
            mstore(add(payload, 0x0700), 0x0000000000000000000000000000000000000000000000000000000000000004) // quotient_const
            mstore(add(payload, 0x0720), 0x0000000000000000000000000000000000000000000000000000000000002000) // quotient_const
            mstore(add(payload, 0x0740), 0x0000000000000000000000000000000000000000000000000000000000400000) // quotient_const
            mstore(add(payload, 0x0760), 0x0000000000000000000000000000000000000000000000000000000000000010) // quotient_const
            mstore(add(payload, 0x0780), 0x0000000000000000000000000000000000000000000000000000000004000000) // quotient_const
            mstore(add(payload, 0x07a0), 0x0000000000000000000000000000000000000000000000000000100000000000) // quotient_const
            mstore(add(payload, 0x07c0), 0x0000000000000000000000000000000000000000000000000000000000000040) // quotient_const
            mstore(add(payload, 0x07e0), 0x0000000000000000000000000000000000000000000000000000000000000800) // quotient_const
            mstore(add(payload, 0x0800), 0x0000000000000000000000000000000000000000000000000000000002000000) // quotient_const
            mstore(add(payload, 0x0820), 0x0000000000000000000000000000000000000000000000000000000000001000) // quotient_const
            mstore(add(payload, 0x0840), 0x0000000000000000000000000000000000000000000000000004000000000000) // quotient_const
            mstore(add(payload, 0x0860), 0x0000000000000000000000000000000000000000000000000000000000040000) // quotient_const
            mstore(add(payload, 0x0880), 0x0000000000000000000000000000000000000000000000000000000000000080) // quotient_const
            mstore(add(payload, 0x08a0), 0x0000000000000000000000000000000000000000000000000000000000000008) // quotient_const
            mstore(add(payload, 0x08c0), 0x0000000000000000000000000000000000000000000000000000000000100000) // quotient_const
            mstore(add(payload, 0x08e0), 0x0000000000000000000000000000000000000000000000000000000000080000) // quotient_const
            mstore(add(payload, 0x0900), 0x0000000000000000000000000000000000000000000000000000000000020000) // quotient_const
            mstore(add(payload, 0x0920), 0x0000000000000000000000000000000000000000000000000000000100000000) // quotient_const
            mstore(add(payload, 0x0940), 0x055860105b8005590008060d000b0200011b00001b00010558601058800558a0) // quotient_program
            mstore(add(payload, 0x0960), 0x08060d000b0400011b00021b0003210001000007000158200258400358600458) // quotient_program
            mstore(add(payload, 0x0980), 0x800558a00658c00758e00859000959800a59a00b59c00c59e00d5a000e5a200b) // quotient_program
            mstore(add(payload, 0x09a0), 0x070000210001000007000158200258400f58601058801158a00658c00758e012) // quotient_program
            mstore(add(payload, 0x09c0), 0x59001359801459a00b59c00c59e0155a00165a200b0800000918115a40135940) // quotient_program
            mstore(add(payload, 0x09e0), 0x17105a60055a8008060d000b090000091b115a40135aa01a1359401910596005) // quotient_program
            mstore(add(payload, 0x0a00), 0x5a8008060d000b0a0000091e1159c01359e01d1358201c10584005586008060d) // quotient_program
            mstore(add(payload, 0x0a20), 0x000b0a00010921115a40135aa01a135940201359601f105a60055a8008060d00) // quotient_program
            mstore(add(payload, 0x0a40), 0x0b0b000009231159c01359e01d1358201b135840221058c005586008060d000b) // quotient_program
            mstore(add(payload, 0x0a60), 0x0b00011c245920255940265960275a40175aa0285ac0295ae0105a60055a8008) // quotient_program
            mstore(add(payload, 0x0a80), 0x060d000b0c0000090008105ac0115ac00d000b0c00010900081059201159200d) // quotient_program
            mstore(add(payload, 0x0aa0), 0x000b0c0001090008105ae0115ae00d000b0c00011c0058800058a00059000059) // quotient_program
            mstore(add(payload, 0x0ac0), 0x800059a0005a00005a20055a80135b002a08060d000b0d0000191f0000000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ae0), 0x000000000000000000000000000000001197f0fef4c3a1846341b3c9bbaf1bab) // fixed_comms[0].x_hi
            mstore(add(payload, 0x0b00), 0x49752a7fc155defcdcd7f1dfa3e2dc8f4bc21d73a29877c49cadbb627f36a4c9) // fixed_comms[0].x_lo
            mstore(add(payload, 0x0b20), 0x00000000000000000000000000000000008bb277a6be485c012029e27ba4a4b2) // fixed_comms[0].y_hi
            mstore(add(payload, 0x0b40), 0x65cc6db298e43536f08b1efedf2772b974869d097a688aefe3238a54bc785b7a) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0b60), 0x00000000000000000000000000000000158014fe0137559123d6f0a7a49e9b10) // fixed_comms[1].x_hi
            mstore(add(payload, 0x0b80), 0xd8afe7c87fbf2a6db4f086bb485ad9687973f521f8e4b26d6cf7fa4df2cea98e) // fixed_comms[1].x_lo
            mstore(add(payload, 0x0ba0), 0x00000000000000000000000000000000080ce29d0c9cb93552519d16cf97b190) // fixed_comms[1].y_hi
            mstore(add(payload, 0x0bc0), 0x9231c2e2dbc3b45751b45e5959f94caa8a68adfe70f5f1e26a1c98c53b556741) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0be0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[2].x_hi
            mstore(add(payload, 0x0c00), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[2].x_lo
            mstore(add(payload, 0x0c20), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[2].y_hi
            mstore(add(payload, 0x0c40), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0c60), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[3].x_hi
            mstore(add(payload, 0x0c80), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[3].x_lo
            mstore(add(payload, 0x0ca0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[3].y_hi
            mstore(add(payload, 0x0cc0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ce0), 0x0000000000000000000000000000000005e144ed46e8acb259c0c6f74fc8db7b) // fixed_comms[4].x_hi
            mstore(add(payload, 0x0d00), 0x93891877bf9ebd8e8f578e2dc227ec229d3992e381ec6e5170ba982ba5132ef4) // fixed_comms[4].x_lo
            mstore(add(payload, 0x0d20), 0x000000000000000000000000000000000a78956bc7b0a586d6556a8aca4b189f) // fixed_comms[4].y_hi
            mstore(add(payload, 0x0d40), 0xa2857bfbd9258dadfb6fbc02f4394f540f9287119af43716d547aaa6b3f0f566) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0d60), 0x0000000000000000000000000000000007ff75e8af4c630f3009c042d633e046) // fixed_comms[5].x_hi
            mstore(add(payload, 0x0d80), 0xbe569abe7fb6cc03a793d7255415ef85d1d5d2c0bcbded65955442bdd6375b0f) // fixed_comms[5].x_lo
            mstore(add(payload, 0x0da0), 0x000000000000000000000000000000000ad2692742b212ab4d3be6ee84e5f596) // fixed_comms[5].y_hi
            mstore(add(payload, 0x0dc0), 0x512d2fdb7060dc286c6e1b09b6f946f582f2d21d1e62b91e6f3801479b0dd29c) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0de0), 0x00000000000000000000000000000000079df097795280bbb4ffc263e8f77348) // fixed_comms[6].x_hi
            mstore(add(payload, 0x0e00), 0x84abda2ba92876118eb74423d0cb8da226349361b1034ae0246e16f8fe11614c) // fixed_comms[6].x_lo
            mstore(add(payload, 0x0e20), 0x000000000000000000000000000000000b5d2a6ff7e40d171ca5bdc09cbd01d3) // fixed_comms[6].y_hi
            mstore(add(payload, 0x0e40), 0x959cc194bd1786c8fb4302fe7c087accf6e797b6f99640bb5fa66bc51e025b6d) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0e60), 0x0000000000000000000000000000000011b8edaa8350563f28496e85da31cefb) // fixed_comms[7].x_hi
            mstore(add(payload, 0x0e80), 0x29588cf618b9de1f1394ba88d98c2850af74578a921fa3b074827ce5d6d79a6e) // fixed_comms[7].x_lo
            mstore(add(payload, 0x0ea0), 0x000000000000000000000000000000000e5f1ff723dff53f443be25db58eab85) // fixed_comms[7].y_hi
            mstore(add(payload, 0x0ec0), 0xdcc8dc992f05d5f2cb621d99627b38d3c035e6da10dbecd7eef9f52d3c71e7e9) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ee0), 0x0000000000000000000000000000000016136718ba0fa52dd8cd9bac70bb1a39) // fixed_comms[8].x_hi
            mstore(add(payload, 0x0f00), 0x3b9eadd178e144fe053829ffaff48bb83f1e87514ce92ac80e24e56ede5ce8be) // fixed_comms[8].x_lo
            mstore(add(payload, 0x0f20), 0x0000000000000000000000000000000004949827d3757ab3bbc7d74ee99b0c94) // fixed_comms[8].y_hi
            mstore(add(payload, 0x0f40), 0xa796eae2db120667f9c73c25f4e7c24e4d76cbc802669f1147e1a155621153cc) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0f60), 0x000000000000000000000000000000001134f2368c46e60f570e5a28114b0430) // fixed_comms[9].x_hi
            mstore(add(payload, 0x0f80), 0x09824a221c8e375acc6c17a79449fa76f7ce0b31d9619c1c2a8e9bb51a01d525) // fixed_comms[9].x_lo
            mstore(add(payload, 0x0fa0), 0x000000000000000000000000000000000330dce7ecc6d2363802df0d1091c061) // fixed_comms[9].y_hi
            mstore(add(payload, 0x0fc0), 0xda8832e130a952204f6d38ae156b92afb636d8ae2ffddbbf1461997818d93fed) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0fe0), 0x00000000000000000000000000000000158f26dde316c845ea799fc321a6f851) // fixed_comms[10].x_hi
            mstore(add(payload, 0x1000), 0xd37fcad756d1890b0a82a3599bae6eb63cc1eb69bd1752c74be5cbc957f6ade4) // fixed_comms[10].x_lo
            mstore(add(payload, 0x1020), 0x000000000000000000000000000000000a692e837bee577c4138e0c0b350f1e2) // fixed_comms[10].y_hi
            mstore(add(payload, 0x1040), 0xd7e99f18686b70090753372a7b3cad96460d97c9cf5cd360074686fdbc02631c) // fixed_comms[10].y_lo
            // Fixed-column commitment 11, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1060), 0x000000000000000000000000000000000a1d5e2467501774e14ea37009b1f0fc) // fixed_comms[11].x_hi
            mstore(add(payload, 0x1080), 0xe036861d0edd2800de1897c52427efdd76119313f58702d9f6206f5d919205a6) // fixed_comms[11].x_lo
            mstore(add(payload, 0x10a0), 0x000000000000000000000000000000000163e07fe7abc7eefcf10c4fc077ac83) // fixed_comms[11].y_hi
            mstore(add(payload, 0x10c0), 0xbcbaeef8510a5414f3852485a1c606ebdcdc1d47479ae672f885b65236cc1178) // fixed_comms[11].y_lo
            // Fixed-column commitment 12, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x10e0), 0x0000000000000000000000000000000007ea65510f739ba93e197d96fe51315c) // fixed_comms[12].x_hi
            mstore(add(payload, 0x1100), 0x4ff6d08381846cfa7f259a220baec1ac596730b3b3a72777190fd06e9295e898) // fixed_comms[12].x_lo
            mstore(add(payload, 0x1120), 0x00000000000000000000000000000000171f9496628be1c6b2275190355ceabf) // fixed_comms[12].y_hi
            mstore(add(payload, 0x1140), 0x07dbc6e73f60b4e46996478a0176c5e172d2c8ae09e19e79aa2180f5e355a256) // fixed_comms[12].y_lo
            // Fixed-column commitment 13, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1160), 0x0000000000000000000000000000000007a8e5fefc1e2cb2b18457f610373429) // fixed_comms[13].x_hi
            mstore(add(payload, 0x1180), 0xea2f97565be5f3e624e6f5c7ee6cff2849bf7a467bfba9ed3cb7c04d0d8dea80) // fixed_comms[13].x_lo
            mstore(add(payload, 0x11a0), 0x0000000000000000000000000000000010deff2c658634ee66b061b51f8fe06c) // fixed_comms[13].y_hi
            mstore(add(payload, 0x11c0), 0x0d44294528465cb93593bc6c916c3f5243bc8cd81b74579b2296d7a865215037) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x11e0), 0x000000000000000000000000000000000cb5e27e7b6858c023303122953e23cd) // fixed_comms[14].x_hi
            mstore(add(payload, 0x1200), 0x4ad001528d160e8dc98dcc2bd2c0f384fc4805e1d7a937ac8a1dd23b72a12739) // fixed_comms[14].x_lo
            mstore(add(payload, 0x1220), 0x0000000000000000000000000000000016d4b9cc8ccd6d6dc8638a9c37c140ad) // fixed_comms[14].y_hi
            mstore(add(payload, 0x1240), 0x99d34a70b64ff639e14dbd48bddeb4e7b8c888f13b9564f3ff3ba1999f86f054) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1260), 0x0000000000000000000000000000000013099474513438bbf5b4448f5fee5d68) // fixed_comms[15].x_hi
            mstore(add(payload, 0x1280), 0xfbb1c3ceb876f012e99815d7af288f05f309fbc1fe61d095ad8ea73da21d8c69) // fixed_comms[15].x_lo
            mstore(add(payload, 0x12a0), 0x0000000000000000000000000000000019fb64331b26eb7fa8db2e9d10923c52) // fixed_comms[15].y_hi
            mstore(add(payload, 0x12c0), 0xed0d0c8eaf654d53b930083eeb5b99042cdeaded3cb4f6bb8be1a762d201b8bd) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x12e0), 0x0000000000000000000000000000000005e144ed46e8acb259c0c6f74fc8db7b) // fixed_comms[16].x_hi
            mstore(add(payload, 0x1300), 0x93891877bf9ebd8e8f578e2dc227ec229d3992e381ec6e5170ba982ba5132ef4) // fixed_comms[16].x_lo
            mstore(add(payload, 0x1320), 0x000000000000000000000000000000000f887c7e71cf411374c63d2b79009437) // fixed_comms[16].y_hi
            mstore(add(payload, 0x1340), 0xc1f1cf891a5f85116bc1169e0277a6d00f1978ed165fc8e8e4b755594c0eb545) // fixed_comms[16].y_lo
            // Fixed-column commitment 17, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1360), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x_hi
            mstore(add(payload, 0x1380), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x_lo
            mstore(add(payload, 0x13a0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y_hi
            mstore(add(payload, 0x13c0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y_lo
            // Fixed-column commitment 18, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x13e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].x_hi
            mstore(add(payload, 0x1400), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].x_lo
            mstore(add(payload, 0x1420), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].y_hi
            mstore(add(payload, 0x1440), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[18].y_lo
            // Fixed-column commitment 19, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1460), 0x000000000000000000000000000000000feb0ce2c3f6d988b686df76d9feb0ef) // fixed_comms[19].x_hi
            mstore(add(payload, 0x1480), 0x478f83173ca8d97b698dbcac2d68dea34c2f70ea80edd0df4e776b1372b2668a) // fixed_comms[19].x_lo
            mstore(add(payload, 0x14a0), 0x0000000000000000000000000000000003903df9c841c7bda6cb254680c341ee) // fixed_comms[19].y_hi
            mstore(add(payload, 0x14c0), 0x723d6e2d29e0af96c6611152406b1447ccaabd738f3fef24fea213ff3ac0f353) // fixed_comms[19].y_lo
            // Fixed-column commitment 20, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x14e0), 0x0000000000000000000000000000000004a50e3a60e489c345289db9cf08155f) // fixed_comms[20].x_hi
            mstore(add(payload, 0x1500), 0x2d13a21d6959f9637313ed7b20f3d82a9e57baa012e9a99a9c67164bcd7dec9e) // fixed_comms[20].x_lo
            mstore(add(payload, 0x1520), 0x0000000000000000000000000000000009f82f1ebfd2819ef739fd561443ddd6) // fixed_comms[20].y_hi
            mstore(add(payload, 0x1540), 0xd58c7be4ac8097d829108899aea05b81054e4b8afe7c2f2f8530e487b73e20d6) // fixed_comms[20].y_lo
            // Fixed-column commitment 21, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1560), 0x000000000000000000000000000000001804bc8c3f122f0d9f675ea36389066c) // fixed_comms[21].x_hi
            mstore(add(payload, 0x1580), 0x0e5c211863d3872ebe41db2bd1862f3c02d9a19b648f081840ec88dcec49e97a) // fixed_comms[21].x_lo
            mstore(add(payload, 0x15a0), 0x0000000000000000000000000000000010687e2acad5c20e07686fbb666dd9e3) // fixed_comms[21].y_hi
            mstore(add(payload, 0x15c0), 0x2194092f4a7fc3167a92af5fd0491ab07f1e9a5024ab368f2234a06d36deeddb) // fixed_comms[21].y_lo
            // Fixed-column commitment 22, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x15e0), 0x000000000000000000000000000000000f034f685137c3f3154917bce86b44ea) // fixed_comms[22].x_hi
            mstore(add(payload, 0x1600), 0x14b05f5602e597281aca7c5268d2886ba6e9ae085d2430771650d0ef9348e9ff) // fixed_comms[22].x_lo
            mstore(add(payload, 0x1620), 0x000000000000000000000000000000000439e182ebcb1049e558c1934f3a1cce) // fixed_comms[22].y_hi
            mstore(add(payload, 0x1640), 0xcdad98de2e195d8c964f91edfb6bedb6e9a65c43d65176c5428f53dcfd4df978) // fixed_comms[22].y_lo
            // Fixed-column commitment 23, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1660), 0x0000000000000000000000000000000014af43b34f25440ab2f14f0d81f29efb) // fixed_comms[23].x_hi
            mstore(add(payload, 0x1680), 0xbdce0a88a322b9ae3eceee655ffbb62a18ff76554e649e94762bcb1599597b76) // fixed_comms[23].x_lo
            mstore(add(payload, 0x16a0), 0x00000000000000000000000000000000039690167b6d2512ba75d335833a6279) // fixed_comms[23].y_hi
            mstore(add(payload, 0x16c0), 0x27fba32e98d5c700ec33d3806084146c377b7281840601070f75ec1e40ebe78d) // fixed_comms[23].y_lo
            // Fixed-column commitment 24, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x16e0), 0x00000000000000000000000000000000170bf5459edf5e3e790010444f4109e3) // fixed_comms[24].x_hi
            mstore(add(payload, 0x1700), 0xbd9b5b800c76949daad86e73fb3020cbeb883b76dcf8e7e16b6151bbf3077c7d) // fixed_comms[24].x_lo
            mstore(add(payload, 0x1720), 0x000000000000000000000000000000000660856ca39584ca02d205040d5ce114) // fixed_comms[24].y_hi
            mstore(add(payload, 0x1740), 0xa24ff617d8418dd440bcc4584344cea4dfb83936c58d67e96f530ec40d34f680) // fixed_comms[24].y_lo
            // Fixed-column commitment 25, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1760), 0x000000000000000000000000000000000b4953f3ed304eddb9fd8d0902d3c988) // fixed_comms[25].x_hi
            mstore(add(payload, 0x1780), 0x2df30741aa09824878083cd0d38a70d0f70301e338c25d5cd5a18b6257c3a561) // fixed_comms[25].x_lo
            mstore(add(payload, 0x17a0), 0x0000000000000000000000000000000005d13bcdca47942483603e57666d779c) // fixed_comms[25].y_hi
            mstore(add(payload, 0x17c0), 0x58a3a454d0781189092ece35297760ee9c1b7966c5d23c01e48289959143ea49) // fixed_comms[25].y_lo
            // Fixed-column commitment 26, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x17e0), 0x0000000000000000000000000000000019ebb040001ad0c934d7559f48280598) // fixed_comms[26].x_hi
            mstore(add(payload, 0x1800), 0x6eca7c92003fddcbb5df11e3869da92a2484712615f29091a3068b5aca930a2e) // fixed_comms[26].x_lo
            mstore(add(payload, 0x1820), 0x000000000000000000000000000000000ba53499ec0eaf35ea4df48c702a4947) // fixed_comms[26].y_hi
            mstore(add(payload, 0x1840), 0x21713fbf273701d90b600f57d60f63c0a0d71e4b88c12454a6c487206618937b) // fixed_comms[26].y_lo
            // Fixed-column commitment 27, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1860), 0x0000000000000000000000000000000011848a69a597757658aec41e07d94d03) // fixed_comms[27].x_hi
            mstore(add(payload, 0x1880), 0xa14624dbe31b81550a9978117077ce066ed9ea5e1f0b91718c596f0aaf2031bc) // fixed_comms[27].x_lo
            mstore(add(payload, 0x18a0), 0x00000000000000000000000000000000047f5053ba24ac2253f9d0e7549866bf) // fixed_comms[27].y_hi
            mstore(add(payload, 0x18c0), 0x9c3bd8a5bf8e7c3b42a7b58f22399675be0bab7187134394b1494a539167bd0b) // fixed_comms[27].y_lo
            // Fixed-column commitment 28, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x18e0), 0x000000000000000000000000000000001643f3a584e4421d9947d7165ec4155b) // fixed_comms[28].x_hi
            mstore(add(payload, 0x1900), 0x28e1185974a7f3cdb06a57a769c67fbd4b6be11147d4b891b401543f8d47c012) // fixed_comms[28].x_lo
            mstore(add(payload, 0x1920), 0x00000000000000000000000000000000076801e381bdf46542d70de7acd53ef6) // fixed_comms[28].y_hi
            mstore(add(payload, 0x1940), 0xf983d85e399f524ce37ad7f8bfab25eb7cc36ccdf81095ea9cdbdaae781df3dc) // fixed_comms[28].y_lo
            // Fixed-column commitment 29, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1960), 0x00000000000000000000000000000000066bb438ffd7a1c3e670363f55472bad) // fixed_comms[29].x_hi
            mstore(add(payload, 0x1980), 0xcd2b1ba3b91052675aea8c95829b5e171f3fba8feca8fbf432043e74d40d9107) // fixed_comms[29].x_lo
            mstore(add(payload, 0x19a0), 0x0000000000000000000000000000000013fb8c8fa091fbe3d39c80e40f57ec74) // fixed_comms[29].y_hi
            mstore(add(payload, 0x19c0), 0xf571abce93a9e251fd1675d67921ecb10f0ed41945993daea312f1af46752d58) // fixed_comms[29].y_lo
            // Fixed-column commitment 30, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x19e0), 0x000000000000000000000000000000000f62e6513b38160dc213d21d3450f4cc) // fixed_comms[30].x_hi
            mstore(add(payload, 0x1a00), 0x074986b4851ecc57244852e51203199e8f5ec7702a6059113e034ab4d7422ae6) // fixed_comms[30].x_lo
            mstore(add(payload, 0x1a20), 0x0000000000000000000000000000000004bd74738a2e8a43fd8055a1cb4f3563) // fixed_comms[30].y_hi
            mstore(add(payload, 0x1a40), 0x200297e4a265ab5594c9ce5b871a81b81992f8843eccf24d1c60c2ad88d9b40c) // fixed_comms[30].y_lo
            // Fixed-column commitment 31, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1a60), 0x00000000000000000000000000000000176fa67b90761829a172021a3dfc85f1) // fixed_comms[31].x_hi
            mstore(add(payload, 0x1a80), 0x2c9a3e7688eeb8e01510d2ceb5ca572f360ddbce6090c8faa1ee864c79124ac7) // fixed_comms[31].x_lo
            mstore(add(payload, 0x1aa0), 0x000000000000000000000000000000000aaf3d9f39efa0997d7700b723d5012c) // fixed_comms[31].y_hi
            mstore(add(payload, 0x1ac0), 0x9db9391e3c498801eb8d6df75398c61783f91ff250d0e50b38be762dd8b333aa) // fixed_comms[31].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1ae0), 0x0000000000000000000000000000000007028ff2fc358f90a9c4e7656ce28120) // permutation_comms[0].x_hi
            mstore(add(payload, 0x1b00), 0x928163f6a99bc34d8133a8ff8b8cd47edaa83ad91f58214dbe1c9aab7860ad55) // permutation_comms[0].x_lo
            mstore(add(payload, 0x1b20), 0x00000000000000000000000000000000131e794d9cfa5df47130e1e462a70be8) // permutation_comms[0].y_hi
            mstore(add(payload, 0x1b40), 0x7b4a0c243773c1c89f15969c73e96ab810563fc7f3ba578dad38122338aec248) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1b60), 0x000000000000000000000000000000000fa03e45660f0c923ea8ede2e16fb8ef) // permutation_comms[1].x_hi
            mstore(add(payload, 0x1b80), 0xbb02174fca3e97a3f7dc5996d0966075a055130b3b167de1b43bc43bc92dbf6d) // permutation_comms[1].x_lo
            mstore(add(payload, 0x1ba0), 0x00000000000000000000000000000000023a6b243059ccf2be4b7bdd906de062) // permutation_comms[1].y_hi
            mstore(add(payload, 0x1bc0), 0x895501b459fb415abe0bcd3c6d56cbcfe295c91ad7885cda3a5e63dbbd14efdc) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1be0), 0x0000000000000000000000000000000008827559387987eda26e4edd11cc244b) // permutation_comms[2].x_hi
            mstore(add(payload, 0x1c00), 0x3130b75ac555621b986c3289b71c7e3ed37cf2791e2e693e8b50810e7538d4d9) // permutation_comms[2].x_lo
            mstore(add(payload, 0x1c20), 0x00000000000000000000000000000000102c92b140a54508c482c338ea76da7c) // permutation_comms[2].y_hi
            mstore(add(payload, 0x1c40), 0x1c7c36a243aceaeac90df3d2e36e61d058c1516dbf98457fb9a7256519731d2c) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1c60), 0x000000000000000000000000000000001042769ac5ebd91f69f37c8a423c483d) // permutation_comms[3].x_hi
            mstore(add(payload, 0x1c80), 0x81608953e574918fca187ad05653bd9926a9870cb094842d971e71e0789fbd5b) // permutation_comms[3].x_lo
            mstore(add(payload, 0x1ca0), 0x000000000000000000000000000000000a782ee1632a4c410307f1843604506f) // permutation_comms[3].y_hi
            mstore(add(payload, 0x1cc0), 0x602e2da68efdba5aebdc5412d84f189df17455679b5c8776e90df17495bb653d) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1ce0), 0x00000000000000000000000000000000122e7c272f5674e7a6d8ec86397b9e15) // permutation_comms[4].x_hi
            mstore(add(payload, 0x1d00), 0x4dae15bdb77c904c3c1a6a7dca1bd1bd264a0a8e8a836105477b6dd721fa0982) // permutation_comms[4].x_lo
            mstore(add(payload, 0x1d20), 0x00000000000000000000000000000000016e5ab6d2b530567455c76c6da9c3fa) // permutation_comms[4].y_hi
            mstore(add(payload, 0x1d40), 0x4d81c9088aeed605ab9a88d2da590221759a02f3290cdf2106399fe0bf44f8bd) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1d60), 0x00000000000000000000000000000000095e014895ec002b23b02df284966542) // permutation_comms[5].x_hi
            mstore(add(payload, 0x1d80), 0x1e2cc7844dd205cfa4a3c26404ffd76ba476d343a8e0bb96a5e0aaa31295405b) // permutation_comms[5].x_lo
            mstore(add(payload, 0x1da0), 0x0000000000000000000000000000000013a5a440d13f7bbb7ee642eb35dd3e26) // permutation_comms[5].y_hi
            mstore(add(payload, 0x1dc0), 0xfdc804ba702a5b6949828ab230cf4b06609a69d4a256bac135b1ffce75c243b2) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1de0), 0x0000000000000000000000000000000019508b48fdb2975eb118421b6a190674) // permutation_comms[6].x_hi
            mstore(add(payload, 0x1e00), 0x6abfee37a2564e1467c236d58174d40a090900bdcb6103b0d9709c55193eaf76) // permutation_comms[6].x_lo
            mstore(add(payload, 0x1e20), 0x0000000000000000000000000000000003e7d72102d8042da5445b802352e37d) // permutation_comms[6].y_hi
            mstore(add(payload, 0x1e40), 0x6f49027a39ba2a781eed399a95b4987c9dd7703e79bafe4de4ff43325b771139) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1e60), 0x000000000000000000000000000000001511727b923bacfdfd25656c6125309b) // permutation_comms[7].x_hi
            mstore(add(payload, 0x1e80), 0x015263d632ea780ea488cdfc2b51d2f247af8eeb9795aaaf7cdd4d3815e9c225) // permutation_comms[7].x_lo
            mstore(add(payload, 0x1ea0), 0x00000000000000000000000000000000121336bff76a8843c4d1a1255c7be9c8) // permutation_comms[7].y_hi
            mstore(add(payload, 0x1ec0), 0x20d87cde5e7b20e16cb3fbc385805e473180520ccffc38ddc7c63a25cd949143) // permutation_comms[7].y_lo
            // Permutation commitment 8, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1ee0), 0x0000000000000000000000000000000005d1a2eac3a6b9f91400a3fae9ff43b8) // permutation_comms[8].x_hi
            mstore(add(payload, 0x1f00), 0xe16f58183026082c0621c73f7b082791b13fd2b425ea91348c5f53815e961737) // permutation_comms[8].x_lo
            mstore(add(payload, 0x1f20), 0x000000000000000000000000000000000fca3abe472ee93f708d2b4c64b78da4) // permutation_comms[8].y_hi
            mstore(add(payload, 0x1f40), 0x484bb0b5753527392551eb8d39a66db4046d3336cd7ee8dc435c6495483828e0) // permutation_comms[8].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x1f61)
        }
    }
}