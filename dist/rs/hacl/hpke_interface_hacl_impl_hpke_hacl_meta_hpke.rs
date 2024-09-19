#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub struct context_s <'a>
{
    pub ctx_key: &'a [u8],
    pub ctx_nonce: &'a [u8],
    pub ctx_seq: &'a mut [u64],
    pub ctx_exporter: &'a [u8]
}