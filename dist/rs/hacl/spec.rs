#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[derive(PartialEq, Clone, Copy)]
pub enum ffdhe_alg
{
    FFDHE2048,
    FFDHE3072,
    FFDHE4096,
    FFDHE6144,
    FFDHE8192
}

#[derive(PartialEq, Clone, Copy)]
pub(crate) enum frodo_gen_a
{
    SHAKE128,
    AES128
}
