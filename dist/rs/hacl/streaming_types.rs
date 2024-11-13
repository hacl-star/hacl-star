#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[derive(PartialEq, Clone, Copy)]
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

#[derive(PartialEq, Clone, Copy)]
pub enum error_code
{
    Success,
    InvalidAlgorithm,
    InvalidLength,
    MaximumLengthExceeded
}

#[derive(PartialEq, Clone)]
pub struct state_32
{ pub block_state: Box<[u32]>, pub buf: Box<[u8]>, pub total_len: u64 }

#[derive(PartialEq, Clone)]
pub struct state_64
{ pub block_state: Box<[u64]>, pub buf: Box<[u8]>, pub total_len: u64 }
