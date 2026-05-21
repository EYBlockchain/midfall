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
            mstore(add(payload, 0x0000), 0x4cc2e5ac0d3a524691c3723a18e826d6ed01cbf767fdec83fcf3a8f9e7640494) // vk_digest
            mstore(add(payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000001) // num_instances
            mstore(add(payload, 0x0040), 0x0000000000000000000000000000000000000000000000000000000000000006) // k
            mstore(add(payload, 0x0060), 0x721df0b5dcf70753126cf0a7e97b50a53e6ead72f3fe628f03ffffff04000001) // n_inv
            mstore(add(payload, 0x0080), 0x45af6345ec055e4d14a1e27164d8fdbd2d967f4be2f951558140d032f0a9ee53) // omega
            mstore(add(payload, 0x00a0), 0x640d097461a2eeaf4e84b3cd7dc75b61db872ef3dce28e788d28c143168bba2c) // omega_inv
            mstore(add(payload, 0x00c0), 0x68f0ba2461933c32412d801131c542d24eb73f5d9958580573ea3fa3e6fe310f) // omega_inv_to_l
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
            mstore(add(payload, 0x0400), 0x0547401048c00547e008060d000b02000105470011470011470005476008060d) // quotient_program
            mstore(add(payload, 0x0420), 0x000b03000005472011472011472005478008060d000b03000105474011474011) // quotient_program
            mstore(add(payload, 0x0440), 0x474005480008060d000b0300011b00001b00011b0002191f0000000000000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0460), 0x0000000000000000000000000000000016742a8c4f331d1be5bc8622ba92b271) // fixed_comms[0].x_hi
            mstore(add(payload, 0x0480), 0xc798f706f7ed359adb5f2ac650537c84623ab7834d56f8e1d36c8442aea29c13) // fixed_comms[0].x_lo
            mstore(add(payload, 0x04a0), 0x0000000000000000000000000000000013ca2f8530986bc11083da96e5763226) // fixed_comms[0].y_hi
            mstore(add(payload, 0x04c0), 0x07cd6bdb82f308cb42878beaa2f5a0f3d5c62c6c7701d58ee27020e08e9cb8b7) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x04e0), 0x0000000000000000000000000000000013c538f85ca3091a013ab6a943c394cf) // fixed_comms[1].x_hi
            mstore(add(payload, 0x0500), 0xdb4a55805d283af633abd3c03f5a700ee60f921c63dfd268120f7a13cd3bc355) // fixed_comms[1].x_lo
            mstore(add(payload, 0x0520), 0x00000000000000000000000000000000049ef841da32566f73dc39ba90d1386d) // fixed_comms[1].y_hi
            mstore(add(payload, 0x0540), 0x95c92b7204a5400036f4c40eebdbe4ba0642fa2654789f20340038a10835648a) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0560), 0x000000000000000000000000000000000d084585756dbb5703f9c5f156a63cf4) // fixed_comms[2].x_hi
            mstore(add(payload, 0x0580), 0xbec7b8323b6470c1cd0410237136761a3d52ebccab70f8a5cc8c0f78548953ba) // fixed_comms[2].x_lo
            mstore(add(payload, 0x05a0), 0x0000000000000000000000000000000008edfd70c65c5d312c37dc754a862cf1) // fixed_comms[2].y_hi
            mstore(add(payload, 0x05c0), 0x069893b6151b30977eebb406338f37bf47a30e510912b183020a88ea275e9355) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x05e0), 0x000000000000000000000000000000000a3146faad4b6dfd10526e417494857f) // fixed_comms[3].x_hi
            mstore(add(payload, 0x0600), 0x555d39dd09f58f44b4a94034477f00169abf04dc7a1abb92cb06c9fb2abe2e2f) // fixed_comms[3].x_lo
            mstore(add(payload, 0x0620), 0x00000000000000000000000000000000107769de5e57b32ad1bc2f5ed22aa2ee) // fixed_comms[3].y_hi
            mstore(add(payload, 0x0640), 0x0eeba5d4e7c2105b7d872d80d7bcbd0ac018f2ae0aa25084cc205ecb36d584f6) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0660), 0x00000000000000000000000000000000199220c5e9f1f7f71c66c6abebf6b6eb) // fixed_comms[4].x_hi
            mstore(add(payload, 0x0680), 0xa4f8a76ac55dbc2c9b6321a883612aeeee9c6100a0947235b90d4a128b0581ed) // fixed_comms[4].x_lo
            mstore(add(payload, 0x06a0), 0x000000000000000000000000000000000a88a4f6e4302c60014fe494699e83ee) // fixed_comms[4].y_hi
            mstore(add(payload, 0x06c0), 0x36f38f5739eb100abaedf297069e9678848ca55ff0f7e03c9c875f6a41ddb1d9) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x06e0), 0x0000000000000000000000000000000008236a33405bb9043dccb52ca4bc716d) // fixed_comms[5].x_hi
            mstore(add(payload, 0x0700), 0x3394fe1470154f800efe35414be27d5f058a850c0f231693474b54e35cfb2354) // fixed_comms[5].x_lo
            mstore(add(payload, 0x0720), 0x0000000000000000000000000000000002e53544111d5c8d42038cc9c72d3cf4) // fixed_comms[5].y_hi
            mstore(add(payload, 0x0740), 0xd2b9a06e4fae4e07178e5a54a44dcae13e38a320c064ccfbfbf6cdda19652872) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0760), 0x000000000000000000000000000000001981b6b9de116c1458d69beec0eeb2f0) // fixed_comms[6].x_hi
            mstore(add(payload, 0x0780), 0xef7d364a244103aa3cb20da94d19199eb080160b02eeaa06c6fab599f2e59d80) // fixed_comms[6].x_lo
            mstore(add(payload, 0x07a0), 0x00000000000000000000000000000000188fa7f4709e1ad2817917f89083557a) // fixed_comms[6].y_hi
            mstore(add(payload, 0x07c0), 0x6c32d67e6ab2025b7ddccd668bb37890a1c0b2c0a96b3dcffe4c7a593520111e) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x07e0), 0x000000000000000000000000000000000bf2d48390efa617b0594f2b21a9c7ab) // fixed_comms[7].x_hi
            mstore(add(payload, 0x0800), 0x605863c9b61708c6e5bdbfc937441d2cd3479fd5153058e25f0f681e7b283eba) // fixed_comms[7].x_lo
            mstore(add(payload, 0x0820), 0x000000000000000000000000000000001208b23eaec36d5c052bae124a9c7ac1) // fixed_comms[7].y_hi
            mstore(add(payload, 0x0840), 0x15b80d2ff7bd38edaa3cdf15a8f3a8dadfb488ee28abd81b29f7b8b2a96c016a) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0860), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[8].x_hi
            mstore(add(payload, 0x0880), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[8].x_lo
            mstore(add(payload, 0x08a0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[8].y_hi
            mstore(add(payload, 0x08c0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x08e0), 0x00000000000000000000000000000000063bb4970f84b93e0780787604f6dec5) // fixed_comms[9].x_hi
            mstore(add(payload, 0x0900), 0x65d5aa57c8653c5beaa33f39dead5cb4dc471bf1f59a331a56ead4a71f2c97bf) // fixed_comms[9].x_lo
            mstore(add(payload, 0x0920), 0x000000000000000000000000000000000d9cc203641e8d91612d9cc9f9b7fe5f) // fixed_comms[9].y_hi
            mstore(add(payload, 0x0940), 0xf6b577b0d654d75ad98430cbe9a4a9aeec85074d9f8ed87712d1b01be915c24c) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0960), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[10].x_hi
            mstore(add(payload, 0x0980), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[10].x_lo
            mstore(add(payload, 0x09a0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[10].y_hi
            mstore(add(payload, 0x09c0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[10].y_lo
            // Fixed-column commitment 11, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x09e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[11].x_hi
            mstore(add(payload, 0x0a00), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[11].x_lo
            mstore(add(payload, 0x0a20), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[11].y_hi
            mstore(add(payload, 0x0a40), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[11].y_lo
            // Fixed-column commitment 12, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0a60), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[12].x_hi
            mstore(add(payload, 0x0a80), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[12].x_lo
            mstore(add(payload, 0x0aa0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[12].y_hi
            mstore(add(payload, 0x0ac0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[12].y_lo
            // Fixed-column commitment 13, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ae0), 0x0000000000000000000000000000000016f1bf19b3527e94e09c32424dd72f7e) // fixed_comms[13].x_hi
            mstore(add(payload, 0x0b00), 0x3dba6ff87666b0cc04e985f0566dd2a089fa3ff792c323b7f24b140cdbb24017) // fixed_comms[13].x_lo
            mstore(add(payload, 0x0b20), 0x000000000000000000000000000000001447edb53f0747f81b256727982691a0) // fixed_comms[13].y_hi
            mstore(add(payload, 0x0b40), 0xf3ec73d08b05b5fa22e1b5ac5327981c917ccf1307107ed4488d37a725df2958) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0b60), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].x_hi
            mstore(add(payload, 0x0b80), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].x_lo
            mstore(add(payload, 0x0ba0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].y_hi
            mstore(add(payload, 0x0bc0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0be0), 0x0000000000000000000000000000000010aaf649459249c8abfc5fa11b9d5e29) // fixed_comms[15].x_hi
            mstore(add(payload, 0x0c00), 0xa22e93e0d59339adbdc9ccab98eb612af4b1cdc41335dedb77d27328985ed17b) // fixed_comms[15].x_lo
            mstore(add(payload, 0x0c20), 0x000000000000000000000000000000000f6c41cc65ae77af29e7182e80009350) // fixed_comms[15].y_hi
            mstore(add(payload, 0x0c40), 0xbb9483b9d11ad81caad53f7e526c3f280e4a3ee1ad127a74bdbf81d21fd333c3) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0c60), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[16].x_hi
            mstore(add(payload, 0x0c80), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[16].x_lo
            mstore(add(payload, 0x0ca0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[16].y_hi
            mstore(add(payload, 0x0cc0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[16].y_lo
            // Fixed-column commitment 17, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ce0), 0x00000000000000000000000000000000130edfa3129b56b2eaa7e90389723c4e) // fixed_comms[17].x_hi
            mstore(add(payload, 0x0d00), 0x0ce10d8aa4d2e97e09c1a21ea367556ef86a96dd4ee1f6b2543ae86c5c80e8b5) // fixed_comms[17].x_lo
            mstore(add(payload, 0x0d20), 0x0000000000000000000000000000000001eff29762b14505b3a1c2c6b4e2519b) // fixed_comms[17].y_hi
            mstore(add(payload, 0x0d40), 0xd28574a3f35d580a4418e76f9d0f34c41da97aad763d0d1e82a7529fd387c664) // fixed_comms[17].y_lo
            // Fixed-column commitment 18, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0d60), 0x000000000000000000000000000000000b815b8ada52d66d2ccf4b422198f9d0) // fixed_comms[18].x_hi
            mstore(add(payload, 0x0d80), 0xa046c355749850bccac619c1ce08ee21bed484868c02e346e178d86dcea82175) // fixed_comms[18].x_lo
            mstore(add(payload, 0x0da0), 0x0000000000000000000000000000000017fb75a38a57789ed1f22a9f722a773e) // fixed_comms[18].y_hi
            mstore(add(payload, 0x0dc0), 0x3955ce856daece40b0c652ad999ae2a9c1a27f2470bed718a8c9eb33ea4604a2) // fixed_comms[18].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0de0), 0x0000000000000000000000000000000007ed5eda5cc05a4a50e37097c480b6a5) // permutation_comms[0].x_hi
            mstore(add(payload, 0x0e00), 0x663affb55f17d7fec4962148154952b6fcb4afb1665abea88558b77dc2e470de) // permutation_comms[0].x_lo
            mstore(add(payload, 0x0e20), 0x0000000000000000000000000000000013f747c2867fd0452a7b8dfdd339ac23) // permutation_comms[0].y_hi
            mstore(add(payload, 0x0e40), 0x80405dc6fb8cd7f28762110d05dc07cb791e217e49445b99fee34488fa4dd1ee) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0e60), 0x000000000000000000000000000000000a8de322b16845c91b49453b34a08d04) // permutation_comms[1].x_hi
            mstore(add(payload, 0x0e80), 0x6878162ef78525362622b61764f8eb3d7b33af9d3392d18e22ad94fc65f1b238) // permutation_comms[1].x_lo
            mstore(add(payload, 0x0ea0), 0x0000000000000000000000000000000006aeaa7abd5156a1af4c8bed74b6980a) // permutation_comms[1].y_hi
            mstore(add(payload, 0x0ec0), 0x467a83c881033a34e086305ad83d60846fbb4d31e2189b18a59814ea29bfb8bc) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0ee0), 0x0000000000000000000000000000000002752003c3de15199a5520aff16e55a3) // permutation_comms[2].x_hi
            mstore(add(payload, 0x0f00), 0x8e2bb46b0987555b34a1c84e6ffcb9cf5b4fcaa569fd931705192120f29d4e7d) // permutation_comms[2].x_lo
            mstore(add(payload, 0x0f20), 0x0000000000000000000000000000000017f858c355607269a3eefaea04643f94) // permutation_comms[2].y_hi
            mstore(add(payload, 0x0f40), 0x810ec8949cf23d4a577db6f04ad35bdc392cc9416cc84aee7135ec2fb28f4ac5) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0f60), 0x0000000000000000000000000000000009e7f937236c0bff5dafd0048182575d) // permutation_comms[3].x_hi
            mstore(add(payload, 0x0f80), 0xa58f2960fc0fe4eab31c479a585fa6532af0a55e184fd90b6f979ab0a259b914) // permutation_comms[3].x_lo
            mstore(add(payload, 0x0fa0), 0x000000000000000000000000000000000809f390ff0546c1b94382d4f3394d62) // permutation_comms[3].y_hi
            mstore(add(payload, 0x0fc0), 0xbb780142611df388bc7d1c87fae3dedf7d4ec3b96abab48cfecb5733a5e3a4d5) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0fe0), 0x00000000000000000000000000000000065e5923ba1ef242236ed7e532b354d4) // permutation_comms[4].x_hi
            mstore(add(payload, 0x1000), 0x8bbf4f8e3b42ecdd778445b2cc752cbbe748efff79cc5c83b60b3e031a3c5c7a) // permutation_comms[4].x_lo
            mstore(add(payload, 0x1020), 0x000000000000000000000000000000001727d1002e895ce35daa28e3c605398f) // permutation_comms[4].y_hi
            mstore(add(payload, 0x1040), 0xfa34719a0b035fe37ecee326c6310d9195dbb8ed541f46c06678be6bd4eeabe8) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1060), 0x000000000000000000000000000000000b673594fcc9175d927bba933a4be97e) // permutation_comms[5].x_hi
            mstore(add(payload, 0x1080), 0x57480086d056307cae22fc6e98b5f5e5df8aa6caf7a99251e4b6ef879e200c63) // permutation_comms[5].x_lo
            mstore(add(payload, 0x10a0), 0x00000000000000000000000000000000188ef7308f4561b9e8b2f50c7d664a96) // permutation_comms[5].y_hi
            mstore(add(payload, 0x10c0), 0x33f1f9de0503b8d193eba356185573de8abcca159768147b0feb3bbaa40c5e1b) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x10e0), 0x0000000000000000000000000000000019508b48fdb2975eb118421b6a190674) // permutation_comms[6].x_hi
            mstore(add(payload, 0x1100), 0x6abfee37a2564e1467c236d58174d40a090900bdcb6103b0d9709c55193eaf76) // permutation_comms[6].x_lo
            mstore(add(payload, 0x1120), 0x0000000000000000000000000000000003e7d72102d8042da5445b802352e37d) // permutation_comms[6].y_hi
            mstore(add(payload, 0x1140), 0x6f49027a39ba2a781eed399a95b4987c9dd7703e79bafe4de4ff43325b771139) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1160), 0x000000000000000000000000000000001983cb9722d7ec0aff9293143c04ce2e) // permutation_comms[7].x_hi
            mstore(add(payload, 0x1180), 0xd7d405d3ed231b0e95780fcdb0fe1b4fbca6d19c25ed1b32ff24f84d89c3f036) // permutation_comms[7].x_lo
            mstore(add(payload, 0x11a0), 0x00000000000000000000000000000000086c98ee46a4345a7e742b0ca06d7641) // permutation_comms[7].y_hi
            mstore(add(payload, 0x11c0), 0x02d44e62b61bf8a84d95c0049ef449492f0fd0463583d68eb5236069eb3e3fd7) // permutation_comms[7].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x11e1)
        }
    }
}