#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn double_round_32(st: &mut [u32]) -> ()
{
    st[0usize] = (st[0usize]).wrapping_add(st[4usize]);
    let std: u32 = st[12usize] ^ st[0usize];
    st[12usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
    st[8usize] = (st[8usize]).wrapping_add(st[12usize]);
    let std0: u32 = st[4usize] ^ st[8usize];
    st[4usize] = std0.wrapping_shl(12u32) | std0.wrapping_shr(20u32);
    st[0usize] = (st[0usize]).wrapping_add(st[4usize]);
    let std1: u32 = st[12usize] ^ st[0usize];
    st[12usize] = std1.wrapping_shl(8u32) | std1.wrapping_shr(24u32);
    st[8usize] = (st[8usize]).wrapping_add(st[12usize]);
    let std2: u32 = st[4usize] ^ st[8usize];
    st[4usize] = std2.wrapping_shl(7u32) | std2.wrapping_shr(25u32);
    st[1usize] = (st[1usize]).wrapping_add(st[5usize]);
    let std3: u32 = st[13usize] ^ st[1usize];
    st[13usize] = std3.wrapping_shl(16u32) | std3.wrapping_shr(16u32);
    st[9usize] = (st[9usize]).wrapping_add(st[13usize]);
    let std4: u32 = st[5usize] ^ st[9usize];
    st[5usize] = std4.wrapping_shl(12u32) | std4.wrapping_shr(20u32);
    st[1usize] = (st[1usize]).wrapping_add(st[5usize]);
    let std5: u32 = st[13usize] ^ st[1usize];
    st[13usize] = std5.wrapping_shl(8u32) | std5.wrapping_shr(24u32);
    st[9usize] = (st[9usize]).wrapping_add(st[13usize]);
    let std6: u32 = st[5usize] ^ st[9usize];
    st[5usize] = std6.wrapping_shl(7u32) | std6.wrapping_shr(25u32);
    st[2usize] = (st[2usize]).wrapping_add(st[6usize]);
    let std7: u32 = st[14usize] ^ st[2usize];
    st[14usize] = std7.wrapping_shl(16u32) | std7.wrapping_shr(16u32);
    st[10usize] = (st[10usize]).wrapping_add(st[14usize]);
    let std8: u32 = st[6usize] ^ st[10usize];
    st[6usize] = std8.wrapping_shl(12u32) | std8.wrapping_shr(20u32);
    st[2usize] = (st[2usize]).wrapping_add(st[6usize]);
    let std9: u32 = st[14usize] ^ st[2usize];
    st[14usize] = std9.wrapping_shl(8u32) | std9.wrapping_shr(24u32);
    st[10usize] = (st[10usize]).wrapping_add(st[14usize]);
    let std10: u32 = st[6usize] ^ st[10usize];
    st[6usize] = std10.wrapping_shl(7u32) | std10.wrapping_shr(25u32);
    st[3usize] = (st[3usize]).wrapping_add(st[7usize]);
    let std11: u32 = st[15usize] ^ st[3usize];
    st[15usize] = std11.wrapping_shl(16u32) | std11.wrapping_shr(16u32);
    st[11usize] = (st[11usize]).wrapping_add(st[15usize]);
    let std12: u32 = st[7usize] ^ st[11usize];
    st[7usize] = std12.wrapping_shl(12u32) | std12.wrapping_shr(20u32);
    st[3usize] = (st[3usize]).wrapping_add(st[7usize]);
    let std13: u32 = st[15usize] ^ st[3usize];
    st[15usize] = std13.wrapping_shl(8u32) | std13.wrapping_shr(24u32);
    st[11usize] = (st[11usize]).wrapping_add(st[15usize]);
    let std14: u32 = st[7usize] ^ st[11usize];
    st[7usize] = std14.wrapping_shl(7u32) | std14.wrapping_shr(25u32);
    st[0usize] = (st[0usize]).wrapping_add(st[5usize]);
    let std15: u32 = st[15usize] ^ st[0usize];
    st[15usize] = std15.wrapping_shl(16u32) | std15.wrapping_shr(16u32);
    st[10usize] = (st[10usize]).wrapping_add(st[15usize]);
    let std16: u32 = st[5usize] ^ st[10usize];
    st[5usize] = std16.wrapping_shl(12u32) | std16.wrapping_shr(20u32);
    st[0usize] = (st[0usize]).wrapping_add(st[5usize]);
    let std17: u32 = st[15usize] ^ st[0usize];
    st[15usize] = std17.wrapping_shl(8u32) | std17.wrapping_shr(24u32);
    st[10usize] = (st[10usize]).wrapping_add(st[15usize]);
    let std18: u32 = st[5usize] ^ st[10usize];
    st[5usize] = std18.wrapping_shl(7u32) | std18.wrapping_shr(25u32);
    st[1usize] = (st[1usize]).wrapping_add(st[6usize]);
    let std19: u32 = st[12usize] ^ st[1usize];
    st[12usize] = std19.wrapping_shl(16u32) | std19.wrapping_shr(16u32);
    st[11usize] = (st[11usize]).wrapping_add(st[12usize]);
    let std20: u32 = st[6usize] ^ st[11usize];
    st[6usize] = std20.wrapping_shl(12u32) | std20.wrapping_shr(20u32);
    st[1usize] = (st[1usize]).wrapping_add(st[6usize]);
    let std21: u32 = st[12usize] ^ st[1usize];
    st[12usize] = std21.wrapping_shl(8u32) | std21.wrapping_shr(24u32);
    st[11usize] = (st[11usize]).wrapping_add(st[12usize]);
    let std22: u32 = st[6usize] ^ st[11usize];
    st[6usize] = std22.wrapping_shl(7u32) | std22.wrapping_shr(25u32);
    st[2usize] = (st[2usize]).wrapping_add(st[7usize]);
    let std23: u32 = st[13usize] ^ st[2usize];
    st[13usize] = std23.wrapping_shl(16u32) | std23.wrapping_shr(16u32);
    st[8usize] = (st[8usize]).wrapping_add(st[13usize]);
    let std24: u32 = st[7usize] ^ st[8usize];
    st[7usize] = std24.wrapping_shl(12u32) | std24.wrapping_shr(20u32);
    st[2usize] = (st[2usize]).wrapping_add(st[7usize]);
    let std25: u32 = st[13usize] ^ st[2usize];
    st[13usize] = std25.wrapping_shl(8u32) | std25.wrapping_shr(24u32);
    st[8usize] = (st[8usize]).wrapping_add(st[13usize]);
    let std26: u32 = st[7usize] ^ st[8usize];
    st[7usize] = std26.wrapping_shl(7u32) | std26.wrapping_shr(25u32);
    st[3usize] = (st[3usize]).wrapping_add(st[4usize]);
    let std27: u32 = st[14usize] ^ st[3usize];
    st[14usize] = std27.wrapping_shl(16u32) | std27.wrapping_shr(16u32);
    st[9usize] = (st[9usize]).wrapping_add(st[14usize]);
    let std28: u32 = st[4usize] ^ st[9usize];
    st[4usize] = std28.wrapping_shl(12u32) | std28.wrapping_shr(20u32);
    st[3usize] = (st[3usize]).wrapping_add(st[4usize]);
    let std29: u32 = st[14usize] ^ st[3usize];
    st[14usize] = std29.wrapping_shl(8u32) | std29.wrapping_shr(24u32);
    st[9usize] = (st[9usize]).wrapping_add(st[14usize]);
    let std30: u32 = st[4usize] ^ st[9usize];
    st[4usize] = std30.wrapping_shl(7u32) | std30.wrapping_shr(25u32)
}

#[inline] fn chacha20_core_32(k: &mut [u32], ctx: &mut [u32], ctr: u32) -> ()
{
    (k[0usize..16usize]).copy_from_slice(&ctx[0usize..16usize]);
    let ctr_u32: u32 = 1u32.wrapping_mul(ctr);
    let cv: u32 = ctr_u32;
    k[12usize] = (k[12usize]).wrapping_add(cv);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    double_round_32(k);
    for i in 0u32..16u32
    {
        let x: u32 = (k[i as usize]).wrapping_add(ctx[i as usize]);
        let os: (&mut [u32], &mut [u32]) = k.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    k[12usize] = (k[12usize]).wrapping_add(cv)
}

#[inline] fn chacha20_init_32(ctx: &mut [u32], k: &mut [u8], n: &mut [u8], ctr: u32) -> ()
{
    let mut ctx1: [u32; 16] = [0u32; 16usize];
    for i in 0u32..4u32
    {
        let x: u32 = (&crate::hacl::chacha20::chacha20_constants)[i as usize];
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[0usize..])[0usize..];
        os[i as usize] = x
    };
    let uu____0: (&mut [u32], &mut [u32]) = (&mut ctx1).split_at_mut(4usize);
    for i in 0u32..8u32
    {
        let bj: (&mut [u8], &mut [u8]) = k.split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        let os: (&mut [u32], &mut [u32]) = uu____0.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    (&mut ctx1)[12usize] = ctr;
    let uu____1: (&mut [u32], &mut [u32]) = (&mut ctx1).split_at_mut(13usize);
    for i in 0u32..3u32
    {
        let bj: (&mut [u8], &mut [u8]) = n.split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        let os: (&mut [u32], &mut [u32]) = uu____1.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    for i in 0u32..16u32
    {
        let x: u32 = (&mut ctx1)[i as usize];
        let os: (&mut [u32], &mut [u32]) = ctx.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let ctr1: u32 = 0u32;
    let c12: u32 = ctx[12usize];
    ctx[12usize] = c12.wrapping_add(ctr1)
}

pub fn chacha20_encrypt_32(
    len: u32,
    out: &mut [u8],
    text: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    chacha20_init_32(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(64u32);
    let nb: u32 = len.wrapping_div(64u32);
    let rem1: u32 = len.wrapping_rem(64u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(64u32) as usize);
        let uu____1: (&mut [u8], &mut [u8]) = text.split_at_mut(i.wrapping_mul(64u32) as usize);
        let mut k: [u32; 16] = [0u32; 16usize];
        chacha20_core_32(&mut k, &mut ctx, i);
        for i0 in 0u32..16u32
        {
            let u: u32 =
                crate::lowstar::endianness::load32_le(
                    &mut uu____1.1[i0.wrapping_mul(4u32) as usize..]
                );
            let x: u32 = u;
            let y: u32 = x ^ (&mut k)[i0 as usize];
            crate::lowstar::endianness::store32_le(
                &mut uu____0.1[i0.wrapping_mul(4u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(64u32) as usize);
        let mut plain: [u8; 64] = [0u8; 64usize];
        ((&mut plain)[0usize..rem as usize]).copy_from_slice(
            &(&mut text[nb.wrapping_mul(64u32) as usize..])[0usize..rem as usize]
        );
        let mut k: [u32; 16] = [0u32; 16usize];
        chacha20_core_32(&mut k, &mut ctx, nb);
        for i in 0u32..16u32
        {
            let u: u32 =
                crate::lowstar::endianness::load32_le(
                    &mut (&mut plain)[i.wrapping_mul(4u32) as usize..]
                );
            let x: u32 = u;
            let y: u32 = x ^ (&mut k)[i as usize];
            crate::lowstar::endianness::store32_le(
                &mut (&mut plain)[i.wrapping_mul(4u32) as usize..],
                y
            )
        };
        (uu____2.1[0usize..rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0usize..])[0usize..rem as usize]
        )
    }
}

pub fn chacha20_decrypt_32(
    len: u32,
    out: &mut [u8],
    cipher: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [u32; 16] = [0u32; 16usize];
    chacha20_init_32(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(64u32);
    let nb: u32 = len.wrapping_div(64u32);
    let rem1: u32 = len.wrapping_rem(64u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(64u32) as usize);
        let uu____1: (&mut [u8], &mut [u8]) = cipher.split_at_mut(i.wrapping_mul(64u32) as usize);
        let mut k: [u32; 16] = [0u32; 16usize];
        chacha20_core_32(&mut k, &mut ctx, i);
        for i0 in 0u32..16u32
        {
            let u: u32 =
                crate::lowstar::endianness::load32_le(
                    &mut uu____1.1[i0.wrapping_mul(4u32) as usize..]
                );
            let x: u32 = u;
            let y: u32 = x ^ (&mut k)[i0 as usize];
            crate::lowstar::endianness::store32_le(
                &mut uu____0.1[i0.wrapping_mul(4u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(64u32) as usize);
        let mut plain: [u8; 64] = [0u8; 64usize];
        ((&mut plain)[0usize..rem as usize]).copy_from_slice(
            &(&mut cipher[nb.wrapping_mul(64u32) as usize..])[0usize..rem as usize]
        );
        let mut k: [u32; 16] = [0u32; 16usize];
        chacha20_core_32(&mut k, &mut ctx, nb);
        for i in 0u32..16u32
        {
            let u: u32 =
                crate::lowstar::endianness::load32_le(
                    &mut (&mut plain)[i.wrapping_mul(4u32) as usize..]
                );
            let x: u32 = u;
            let y: u32 = x ^ (&mut k)[i as usize];
            crate::lowstar::endianness::store32_le(
                &mut (&mut plain)[i.wrapping_mul(4u32) as usize..],
                y
            )
        };
        (uu____2.1[0usize..rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0usize..])[0usize..rem as usize]
        )
    }
}
