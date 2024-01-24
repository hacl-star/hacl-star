#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub const reseed_interval: u32 = 1024u32;

pub const max_output_length: u32 = 65536u32;

pub const max_length: u32 = 65536u32;

pub const max_personalization_string_length: u32 = 65536u32;

pub const max_additional_input_length: u32 = 65536u32;

enum state_s_tags
{
    SHA1_s,
    SHA2_256_s,
    SHA2_384_s,
    SHA2_512_s
}

pub fn create(a: crate::hacl::streaming_types::hash_alg) -> &mut [state_s] { create_in(a) }
