#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub struct context_s
{
    pub ctx_key: &mut [u8],
    pub ctx_nonce: &mut [u8],
    pub ctx_seq: &mut [u64],
    pub ctx_exporter: &mut [u8]
}
