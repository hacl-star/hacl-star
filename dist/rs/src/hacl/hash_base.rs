#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn word_len(a: crate::hacl::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::MD5 => 4u32,
        crate::hacl::streaming_types::hash_alg::SHA1 => 4u32,
        crate::hacl::streaming_types::hash_alg::SHA2_224 => 4u32,
        crate::hacl::streaming_types::hash_alg::SHA2_256 => 4u32,
        crate::hacl::streaming_types::hash_alg::SHA2_384 => 8u32,
        crate::hacl::streaming_types::hash_alg::SHA2_512 => 8u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub fn block_len(a: crate::hacl::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::MD5 => 64u32,
        crate::hacl::streaming_types::hash_alg::SHA1 => 64u32,
        crate::hacl::streaming_types::hash_alg::SHA2_224 => 64u32,
        crate::hacl::streaming_types::hash_alg::SHA2_256 => 64u32,
        crate::hacl::streaming_types::hash_alg::SHA2_384 => 128u32,
        crate::hacl::streaming_types::hash_alg::SHA2_512 => 128u32,
        crate::hacl::streaming_types::hash_alg::SHA3_224 => 144u32,
        crate::hacl::streaming_types::hash_alg::SHA3_256 => 136u32,
        crate::hacl::streaming_types::hash_alg::SHA3_384 => 104u32,
        crate::hacl::streaming_types::hash_alg::SHA3_512 => 72u32,
        crate::hacl::streaming_types::hash_alg::Shake128 => 168u32,
        crate::hacl::streaming_types::hash_alg::Shake256 => 136u32,
        crate::hacl::streaming_types::hash_alg::Blake2S => 64u32,
        crate::hacl::streaming_types::hash_alg::Blake2B => 128u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub fn hash_word_len(a: crate::hacl::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::MD5 => 4u32,
        crate::hacl::streaming_types::hash_alg::SHA1 => 5u32,
        crate::hacl::streaming_types::hash_alg::SHA2_224 => 7u32,
        crate::hacl::streaming_types::hash_alg::SHA2_256 => 8u32,
        crate::hacl::streaming_types::hash_alg::SHA2_384 => 6u32,
        crate::hacl::streaming_types::hash_alg::SHA2_512 => 8u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub fn hash_len(a: crate::hacl::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::MD5 => 16u32,
        crate::hacl::streaming_types::hash_alg::SHA1 => 20u32,
        crate::hacl::streaming_types::hash_alg::SHA2_224 => 28u32,
        crate::hacl::streaming_types::hash_alg::SHA2_256 => 32u32,
        crate::hacl::streaming_types::hash_alg::SHA2_384 => 48u32,
        crate::hacl::streaming_types::hash_alg::SHA2_512 => 64u32,
        crate::hacl::streaming_types::hash_alg::Blake2S => 32u32,
        crate::hacl::streaming_types::hash_alg::Blake2B => 64u32,
        crate::hacl::streaming_types::hash_alg::SHA3_224 => 28u32,
        crate::hacl::streaming_types::hash_alg::SHA3_256 => 32u32,
        crate::hacl::streaming_types::hash_alg::SHA3_384 => 48u32,
        crate::hacl::streaming_types::hash_alg::SHA3_512 => 64u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub type hash_t <'a> = &'a mut [u8];
