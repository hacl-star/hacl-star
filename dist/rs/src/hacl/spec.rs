#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

pub enum ffdhe_alg
{
    FFDHE2048,
    FFDHE3072,
    FFDHE4096,
    FFDHE6144,
    FFDHE8192
}

pub enum r#impl
{
    Hacl_CHACHA20,
    Vale_AES128,
    Vale_AES256
}

pub enum alg
{
    AES128_GCM,
    AES256_GCM,
    CHACHA20_POLY1305,
    AES128_CCM,
    AES256_CCM,
    AES128_CCM8,
    AES256_CCM8
}

pub enum frodo_gen_a
{
    SHAKE128,
    AES128
}
