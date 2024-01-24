#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub enum hash_alg
{
    SHA2_224,
    SHA2_256,
    SHA2_384,
    SHA2_512,
    SHA1,
    MD5,
    Blake2S,
    Blake2B,
    SHA3_256,
    SHA3_224,
    SHA3_384,
    SHA3_512,
    Shake128,
    Shake256
}

pub enum error_code
{
    Success,
    InvalidAlgorithm,
    InvalidLength,
    MaximumLengthExceeded
}

pub struct state_32 <'a>
{ pub block_state: &'a mut [u32], pub buf: &'a mut [u8], pub total_len: u64 }

pub struct state_64 <'a>
{ pub block_state: &'a mut [u64], pub buf: &'a mut [u8], pub total_len: u64 }
