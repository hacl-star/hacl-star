#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub const reseed_interval: u32 = 1024u32;

pub const max_output_length: u32 = 65536u32;

pub const max_length: u32 = 65536u32;

pub const max_personalization_string_length: u32 = 65536u32;

pub const max_additional_input_length: u32 = 65536u32;

pub struct state { pub k: Box<[u8]>, pub v: Box<[u8]>, pub reseed_counter: Box<[u32]> }

pub fn uu___is_State(a: crate::hacl::streaming_types::hash_alg, projectee: state) -> bool
{
    crate::lowstar::ignore::ignore::<crate::hacl::streaming_types::hash_alg>(a);
    crate::lowstar::ignore::ignore::<state>(projectee);
    true
}
