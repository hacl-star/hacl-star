#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn chacha20(
    len: u32,
    dst: &mut [u8],
    src: &mut [u8],
    key: &mut [u8],
    iv: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    crate::hacl::chacha20::chacha20_init(&mut ctx, key, iv, ctr);
    crate::hacl::chacha20::chacha20_update(&mut ctx, len, dst, src)
}
