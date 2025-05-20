#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub(crate) const sigmaTable: [u32; 160] =
    [0u32, 1u32, 2u32, 3u32, 4u32, 5u32, 6u32, 7u32, 8u32, 9u32, 10u32, 11u32, 12u32, 13u32, 14u32,
        15u32, 14u32, 10u32, 4u32, 8u32, 9u32, 15u32, 13u32, 6u32, 1u32, 12u32, 0u32, 2u32, 11u32,
        7u32, 5u32, 3u32, 11u32, 8u32, 12u32, 0u32, 5u32, 2u32, 15u32, 13u32, 10u32, 14u32, 3u32,
        6u32, 7u32, 1u32, 9u32, 4u32, 7u32, 9u32, 3u32, 1u32, 13u32, 12u32, 11u32, 14u32, 2u32, 6u32,
        5u32, 10u32, 4u32, 0u32, 15u32, 8u32, 9u32, 0u32, 5u32, 7u32, 2u32, 4u32, 10u32, 15u32,
        14u32, 1u32, 11u32, 12u32, 6u32, 8u32, 3u32, 13u32, 2u32, 12u32, 6u32, 10u32, 0u32, 11u32,
        8u32, 3u32, 4u32, 13u32, 7u32, 5u32, 15u32, 14u32, 1u32, 9u32, 12u32, 5u32, 1u32, 15u32,
        14u32, 13u32, 4u32, 10u32, 0u32, 7u32, 6u32, 3u32, 9u32, 2u32, 8u32, 11u32, 13u32, 11u32,
        7u32, 14u32, 12u32, 1u32, 3u32, 9u32, 5u32, 0u32, 15u32, 4u32, 8u32, 6u32, 2u32, 10u32, 6u32,
        15u32, 14u32, 9u32, 11u32, 3u32, 0u32, 8u32, 12u32, 2u32, 13u32, 7u32, 1u32, 4u32, 10u32,
        5u32, 10u32, 2u32, 8u32, 4u32, 7u32, 6u32, 1u32, 5u32, 15u32, 11u32, 9u32, 14u32, 3u32,
        12u32, 13u32, 0u32];

pub(crate) const ivTable_S: [u32; 8] =
    [0x6A09E667u32, 0xBB67AE85u32, 0x3C6EF372u32, 0xA54FF53Au32, 0x510E527Fu32, 0x9B05688Cu32,
        0x1F83D9ABu32, 0x5BE0CD19u32];

pub(crate) const ivTable_B: [u64; 8] =
    [0x6A09E667F3BCC908u64, 0xBB67AE8584CAA73Bu64, 0x3C6EF372FE94F82Bu64, 0xA54FF53A5F1D36F1u64,
        0x510E527FADE682D1u64, 0x9B05688C2B3E6C1Fu64, 0x1F83D9ABFB41BD6Bu64, 0x5BE0CD19137E2179u64];
