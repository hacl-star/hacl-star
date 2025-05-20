#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[derive(PartialEq)]
pub struct context_s <'a>
{
    pub ctx_key: &'a mut [u8],
    pub ctx_nonce: &'a mut [u8],
    pub ctx_seq: &'a mut [u64],
    pub ctx_exporter: &'a mut [u8]
}
