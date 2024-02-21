#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub type supported_alg = crate::hacl::streaming_types::hash_alg;

pub const reseed_interval: u32 = 1024u32;

pub const max_output_length: u32 = 65536u32;

pub const max_length: u32 = 65536u32;

pub const max_personalization_string_length: u32 = 65536u32;

pub const max_additional_input_length: u32 = 65536u32;

pub fn min_length(a: crate::hacl::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::SHA1 => 16u32,
        crate::hacl::streaming_types::hash_alg::SHA2_256 => 32u32,
        crate::hacl::streaming_types::hash_alg::SHA2_384 => 32u32,
        crate::hacl::streaming_types::hash_alg::SHA2_512 => 32u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[derive(PartialEq, Clone, Copy)]
enum state_s_tags
{
    SHA1_s,
    SHA2_256_s,
    SHA2_384_s,
    SHA2_512_s
}
