#[inline] fn double_round_128(st: &mut [crate::lib::intvector_intrinsics::vec128]) -> ()
{
    st[0usize] = crate::lib::intvector_intrinsics::vec128_add32(st[0usize], st[4usize]);
    let std: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[12usize], st[0usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std, 16u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec128_add32(st[8usize], st[12usize]);
    let std0: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[4usize], st[8usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std0, 12u32);
    st[0usize] = crate::lib::intvector_intrinsics::vec128_add32(st[0usize], st[4usize]);
    let std1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[12usize], st[0usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std1, 8u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec128_add32(st[8usize], st[12usize]);
    let std2: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[4usize], st[8usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std2, 7u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec128_add32(st[1usize], st[5usize]);
    let std3: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[13usize], st[1usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std3, 16u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec128_add32(st[9usize], st[13usize]);
    let std4: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[5usize], st[9usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std4, 12u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec128_add32(st[1usize], st[5usize]);
    let std5: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[13usize], st[1usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std5, 8u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec128_add32(st[9usize], st[13usize]);
    let std6: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[5usize], st[9usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std6, 7u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec128_add32(st[2usize], st[6usize]);
    let std7: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[14usize], st[2usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std7, 16u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec128_add32(st[10usize], st[14usize]);
    let std8: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[6usize], st[10usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std8, 12u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec128_add32(st[2usize], st[6usize]);
    let std9: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[14usize], st[2usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std9, 8u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec128_add32(st[10usize], st[14usize]);
    let std10: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[6usize], st[10usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std10, 7u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec128_add32(st[3usize], st[7usize]);
    let std11: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[15usize], st[3usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std11, 16u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec128_add32(st[11usize], st[15usize]);
    let std12: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[7usize], st[11usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std12, 12u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec128_add32(st[3usize], st[7usize]);
    let std13: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[15usize], st[3usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std13, 8u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec128_add32(st[11usize], st[15usize]);
    let std14: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[7usize], st[11usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std14, 7u32);
    st[0usize] = crate::lib::intvector_intrinsics::vec128_add32(st[0usize], st[5usize]);
    let std15: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[15usize], st[0usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std15, 16u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec128_add32(st[10usize], st[15usize]);
    let std16: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[5usize], st[10usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std16, 12u32);
    st[0usize] = crate::lib::intvector_intrinsics::vec128_add32(st[0usize], st[5usize]);
    let std17: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[15usize], st[0usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std17, 8u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec128_add32(st[10usize], st[15usize]);
    let std18: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[5usize], st[10usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std18, 7u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec128_add32(st[1usize], st[6usize]);
    let std19: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[12usize], st[1usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std19, 16u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec128_add32(st[11usize], st[12usize]);
    let std20: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[6usize], st[11usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std20, 12u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec128_add32(st[1usize], st[6usize]);
    let std21: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[12usize], st[1usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std21, 8u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec128_add32(st[11usize], st[12usize]);
    let std22: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[6usize], st[11usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std22, 7u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec128_add32(st[2usize], st[7usize]);
    let std23: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[13usize], st[2usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std23, 16u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec128_add32(st[8usize], st[13usize]);
    let std24: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[7usize], st[8usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std24, 12u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec128_add32(st[2usize], st[7usize]);
    let std25: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[13usize], st[2usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std25, 8u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec128_add32(st[8usize], st[13usize]);
    let std26: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[7usize], st[8usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std26, 7u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec128_add32(st[3usize], st[4usize]);
    let std27: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[14usize], st[3usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std27, 16u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec128_add32(st[9usize], st[14usize]);
    let std28: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[4usize], st[9usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std28, 12u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec128_add32(st[3usize], st[4usize]);
    let std29: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[14usize], st[3usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std29, 8u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec128_add32(st[9usize], st[14usize]);
    let std30: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_xor(st[4usize], st[9usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec128_rotate_left32(std30, 7u32)
}

#[inline] fn chacha20_core_128(
    k: &mut [crate::lib::intvector_intrinsics::vec128],
    ctx: &mut [crate::lib::intvector_intrinsics::vec128],
    ctr: u32
) ->
    ()
{
    (k[0usize..0usize + 16usize]).copy_from_slice(&ctx[0usize..0usize + 16usize]);
    let ctr_u32: u32 = 4u32.wrapping_mul(ctr);
    let cv: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load32(ctr_u32);
    k[12usize] = crate::lib::intvector_intrinsics::vec128_add32(k[12usize], cv);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    double_round_128(k);
    for i in 0u32..16u32
    {
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            k.split_at_mut(0usize);
        let x: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_add32(os.1[i as usize], ctx[i as usize]);
        os.1[i as usize] = x
    };
    k[12usize] = crate::lib::intvector_intrinsics::vec128_add32(k[12usize], cv)
}

#[inline] fn chacha20_init_128(
    ctx: &mut [crate::lib::intvector_intrinsics::vec128],
    k: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx1: [u32; 16] = [0u32; 16usize];
    for i in 0u32..4u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[0usize..])[0usize..];
        let x: u32 = (&crate::hacl::chacha20::chacha20_constants)[i as usize];
        os[i as usize] = x
    };
    for i in 0u32..8u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[4usize..])[0usize..];
        let bj: (&mut [u8], &mut [u8]) = k.split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    };
    (&mut ctx1)[12usize] = ctr;
    for i in 0u32..3u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[13usize..])[0usize..];
        let bj: (&mut [u8], &mut [u8]) = n.split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    };
    for i in 0u32..16u32
    {
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            ctx.split_at_mut(0usize);
        let x: u32 = (&mut ctx1)[i as usize];
        let x0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_load32(x);
        os.1[i as usize] = x0
    };
    let ctr1: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_load32s(0u32, 1u32, 2u32, 3u32);
    let c12: crate::lib::intvector_intrinsics::vec128 = ctx[12usize];
    ctx[12usize] = crate::lib::intvector_intrinsics::vec128_add32(c12, ctr1)
}

pub fn chacha20_encrypt_128(
    len: u32,
    out: &mut [u8],
    text: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [crate::lib::intvector_intrinsics::vec128; 16] =
        [crate::lib::intvector_intrinsics::vec128_zero; 16usize];
    chacha20_init_128(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(256u32);
    let nb: u32 = len.wrapping_div(256u32);
    let rem1: u32 = len.wrapping_rem(256u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(256u32) as usize);
        let uu____1: (&mut [u8], &mut [u8]) = text.split_at_mut(i.wrapping_mul(256u32) as usize);
        let mut k: [crate::lib::intvector_intrinsics::vec128; 16] =
            [crate::lib::intvector_intrinsics::vec128_zero; 16usize];
        chacha20_core_128(&mut k, &mut ctx, i);
        let st0: crate::lib::intvector_intrinsics::vec128 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec128 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec128 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec128 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec128 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec128 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec128 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec128 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec128 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec128 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec128 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec128 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec128 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec128 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec128 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec128 = (&mut k)[15usize];
        let v0_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_, v2_);
        let v1__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_, v2_);
        let v2__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_, v3_);
        let v3__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_, v3_);
        let v0__0: crate::lib::intvector_intrinsics::vec128 = v0__;
        let v2__0: crate::lib::intvector_intrinsics::vec128 = v2__;
        let v1__0: crate::lib::intvector_intrinsics::vec128 = v1__;
        let v3__0: crate::lib::intvector_intrinsics::vec128 = v3__;
        let v0: crate::lib::intvector_intrinsics::vec128 = v0__0;
        let v1: crate::lib::intvector_intrinsics::vec128 = v1__0;
        let v2: crate::lib::intvector_intrinsics::vec128 = v2__0;
        let v3: crate::lib::intvector_intrinsics::vec128 = v3__0;
        let v0_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_0, v2_0);
        let v1__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_0, v2_0);
        let v2__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_0, v3_0);
        let v3__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_0, v3_0);
        let v0__2: crate::lib::intvector_intrinsics::vec128 = v0__1;
        let v2__2: crate::lib::intvector_intrinsics::vec128 = v2__1;
        let v1__2: crate::lib::intvector_intrinsics::vec128 = v1__1;
        let v3__2: crate::lib::intvector_intrinsics::vec128 = v3__1;
        let v4: crate::lib::intvector_intrinsics::vec128 = v0__2;
        let v5: crate::lib::intvector_intrinsics::vec128 = v1__2;
        let v6: crate::lib::intvector_intrinsics::vec128 = v2__2;
        let v7: crate::lib::intvector_intrinsics::vec128 = v3__2;
        let v0_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_1, v2_1);
        let v1__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_1, v2_1);
        let v2__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_1, v3_1);
        let v3__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_1, v3_1);
        let v0__4: crate::lib::intvector_intrinsics::vec128 = v0__3;
        let v2__4: crate::lib::intvector_intrinsics::vec128 = v2__3;
        let v1__4: crate::lib::intvector_intrinsics::vec128 = v1__3;
        let v3__4: crate::lib::intvector_intrinsics::vec128 = v3__3;
        let v8: crate::lib::intvector_intrinsics::vec128 = v0__4;
        let v9: crate::lib::intvector_intrinsics::vec128 = v1__4;
        let v10: crate::lib::intvector_intrinsics::vec128 = v2__4;
        let v11: crate::lib::intvector_intrinsics::vec128 = v3__4;
        let v0_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_2, v2_2);
        let v1__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_2, v2_2);
        let v2__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_2, v3_2);
        let v3__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_2, v3_2);
        let v0__6: crate::lib::intvector_intrinsics::vec128 = v0__5;
        let v2__6: crate::lib::intvector_intrinsics::vec128 = v2__5;
        let v1__6: crate::lib::intvector_intrinsics::vec128 = v1__5;
        let v3__6: crate::lib::intvector_intrinsics::vec128 = v3__5;
        let v12: crate::lib::intvector_intrinsics::vec128 = v0__6;
        let v13: crate::lib::intvector_intrinsics::vec128 = v1__6;
        let v14: crate::lib::intvector_intrinsics::vec128 = v2__6;
        let v15: crate::lib::intvector_intrinsics::vec128 = v3__6;
        (&mut k)[0usize] = v0;
        (&mut k)[1usize] = v4;
        (&mut k)[2usize] = v8;
        (&mut k)[3usize] = v12;
        (&mut k)[4usize] = v1;
        (&mut k)[5usize] = v5;
        (&mut k)[6usize] = v9;
        (&mut k)[7usize] = v13;
        (&mut k)[8usize] = v2;
        (&mut k)[9usize] = v6;
        (&mut k)[10usize] = v10;
        (&mut k)[11usize] = v14;
        (&mut k)[12usize] = v3;
        (&mut k)[13usize] = v7;
        (&mut k)[14usize] = v11;
        (&mut k)[15usize] = v15;
        for i0 in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load32_le(
                    &mut uu____1.1[i0.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_xor(x, (&mut k)[i0 as usize]);
            crate::lib::intvector_intrinsics::vec128_store32_le(
                &mut uu____0.1[i0.wrapping_mul(16u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(256u32) as usize);
        let mut plain: [u8; 256] = [0u8; 256usize];
        ((&mut plain)[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut text[nb.wrapping_mul(256u32) as usize..])[0usize..0usize + rem as usize]
        );
        let mut k: [crate::lib::intvector_intrinsics::vec128; 16] =
            [crate::lib::intvector_intrinsics::vec128_zero; 16usize];
        chacha20_core_128(&mut k, &mut ctx, nb);
        let st0: crate::lib::intvector_intrinsics::vec128 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec128 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec128 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec128 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec128 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec128 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec128 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec128 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec128 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec128 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec128 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec128 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec128 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec128 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec128 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec128 = (&mut k)[15usize];
        let v0_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_, v2_);
        let v1__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_, v2_);
        let v2__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_, v3_);
        let v3__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_, v3_);
        let v0__0: crate::lib::intvector_intrinsics::vec128 = v0__;
        let v2__0: crate::lib::intvector_intrinsics::vec128 = v2__;
        let v1__0: crate::lib::intvector_intrinsics::vec128 = v1__;
        let v3__0: crate::lib::intvector_intrinsics::vec128 = v3__;
        let v0: crate::lib::intvector_intrinsics::vec128 = v0__0;
        let v1: crate::lib::intvector_intrinsics::vec128 = v1__0;
        let v2: crate::lib::intvector_intrinsics::vec128 = v2__0;
        let v3: crate::lib::intvector_intrinsics::vec128 = v3__0;
        let v0_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_0, v2_0);
        let v1__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_0, v2_0);
        let v2__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_0, v3_0);
        let v3__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_0, v3_0);
        let v0__2: crate::lib::intvector_intrinsics::vec128 = v0__1;
        let v2__2: crate::lib::intvector_intrinsics::vec128 = v2__1;
        let v1__2: crate::lib::intvector_intrinsics::vec128 = v1__1;
        let v3__2: crate::lib::intvector_intrinsics::vec128 = v3__1;
        let v4: crate::lib::intvector_intrinsics::vec128 = v0__2;
        let v5: crate::lib::intvector_intrinsics::vec128 = v1__2;
        let v6: crate::lib::intvector_intrinsics::vec128 = v2__2;
        let v7: crate::lib::intvector_intrinsics::vec128 = v3__2;
        let v0_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_1, v2_1);
        let v1__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_1, v2_1);
        let v2__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_1, v3_1);
        let v3__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_1, v3_1);
        let v0__4: crate::lib::intvector_intrinsics::vec128 = v0__3;
        let v2__4: crate::lib::intvector_intrinsics::vec128 = v2__3;
        let v1__4: crate::lib::intvector_intrinsics::vec128 = v1__3;
        let v3__4: crate::lib::intvector_intrinsics::vec128 = v3__3;
        let v8: crate::lib::intvector_intrinsics::vec128 = v0__4;
        let v9: crate::lib::intvector_intrinsics::vec128 = v1__4;
        let v10: crate::lib::intvector_intrinsics::vec128 = v2__4;
        let v11: crate::lib::intvector_intrinsics::vec128 = v3__4;
        let v0_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_2, v2_2);
        let v1__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_2, v2_2);
        let v2__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_2, v3_2);
        let v3__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_2, v3_2);
        let v0__6: crate::lib::intvector_intrinsics::vec128 = v0__5;
        let v2__6: crate::lib::intvector_intrinsics::vec128 = v2__5;
        let v1__6: crate::lib::intvector_intrinsics::vec128 = v1__5;
        let v3__6: crate::lib::intvector_intrinsics::vec128 = v3__5;
        let v12: crate::lib::intvector_intrinsics::vec128 = v0__6;
        let v13: crate::lib::intvector_intrinsics::vec128 = v1__6;
        let v14: crate::lib::intvector_intrinsics::vec128 = v2__6;
        let v15: crate::lib::intvector_intrinsics::vec128 = v3__6;
        (&mut k)[0usize] = v0;
        (&mut k)[1usize] = v4;
        (&mut k)[2usize] = v8;
        (&mut k)[3usize] = v12;
        (&mut k)[4usize] = v1;
        (&mut k)[5usize] = v5;
        (&mut k)[6usize] = v9;
        (&mut k)[7usize] = v13;
        (&mut k)[8usize] = v2;
        (&mut k)[9usize] = v6;
        (&mut k)[10usize] = v10;
        (&mut k)[11usize] = v14;
        (&mut k)[12usize] = v3;
        (&mut k)[13usize] = v7;
        (&mut k)[14usize] = v11;
        (&mut k)[15usize] = v15;
        for i in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load32_le(
                    &mut (&mut plain)[i.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_xor(x, (&mut k)[i as usize]);
            crate::lib::intvector_intrinsics::vec128_store32_le(
                &mut (&mut plain)[i.wrapping_mul(16u32) as usize..],
                y
            )
        };
        (uu____2.1[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0usize..])[0usize..0usize + rem as usize]
        )
    }
}

pub fn chacha20_decrypt_128(
    len: u32,
    out: &mut [u8],
    cipher: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [crate::lib::intvector_intrinsics::vec128; 16] =
        [crate::lib::intvector_intrinsics::vec128_zero; 16usize];
    chacha20_init_128(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(256u32);
    let nb: u32 = len.wrapping_div(256u32);
    let rem1: u32 = len.wrapping_rem(256u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(256u32) as usize);
        let uu____1: (&mut [u8], &mut [u8]) = cipher.split_at_mut(i.wrapping_mul(256u32) as usize);
        let mut k: [crate::lib::intvector_intrinsics::vec128; 16] =
            [crate::lib::intvector_intrinsics::vec128_zero; 16usize];
        chacha20_core_128(&mut k, &mut ctx, i);
        let st0: crate::lib::intvector_intrinsics::vec128 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec128 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec128 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec128 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec128 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec128 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec128 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec128 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec128 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec128 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec128 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec128 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec128 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec128 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec128 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec128 = (&mut k)[15usize];
        let v0_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_, v2_);
        let v1__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_, v2_);
        let v2__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_, v3_);
        let v3__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_, v3_);
        let v0__0: crate::lib::intvector_intrinsics::vec128 = v0__;
        let v2__0: crate::lib::intvector_intrinsics::vec128 = v2__;
        let v1__0: crate::lib::intvector_intrinsics::vec128 = v1__;
        let v3__0: crate::lib::intvector_intrinsics::vec128 = v3__;
        let v0: crate::lib::intvector_intrinsics::vec128 = v0__0;
        let v1: crate::lib::intvector_intrinsics::vec128 = v1__0;
        let v2: crate::lib::intvector_intrinsics::vec128 = v2__0;
        let v3: crate::lib::intvector_intrinsics::vec128 = v3__0;
        let v0_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_0, v2_0);
        let v1__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_0, v2_0);
        let v2__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_0, v3_0);
        let v3__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_0, v3_0);
        let v0__2: crate::lib::intvector_intrinsics::vec128 = v0__1;
        let v2__2: crate::lib::intvector_intrinsics::vec128 = v2__1;
        let v1__2: crate::lib::intvector_intrinsics::vec128 = v1__1;
        let v3__2: crate::lib::intvector_intrinsics::vec128 = v3__1;
        let v4: crate::lib::intvector_intrinsics::vec128 = v0__2;
        let v5: crate::lib::intvector_intrinsics::vec128 = v1__2;
        let v6: crate::lib::intvector_intrinsics::vec128 = v2__2;
        let v7: crate::lib::intvector_intrinsics::vec128 = v3__2;
        let v0_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_1, v2_1);
        let v1__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_1, v2_1);
        let v2__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_1, v3_1);
        let v3__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_1, v3_1);
        let v0__4: crate::lib::intvector_intrinsics::vec128 = v0__3;
        let v2__4: crate::lib::intvector_intrinsics::vec128 = v2__3;
        let v1__4: crate::lib::intvector_intrinsics::vec128 = v1__3;
        let v3__4: crate::lib::intvector_intrinsics::vec128 = v3__3;
        let v8: crate::lib::intvector_intrinsics::vec128 = v0__4;
        let v9: crate::lib::intvector_intrinsics::vec128 = v1__4;
        let v10: crate::lib::intvector_intrinsics::vec128 = v2__4;
        let v11: crate::lib::intvector_intrinsics::vec128 = v3__4;
        let v0_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_2, v2_2);
        let v1__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_2, v2_2);
        let v2__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_2, v3_2);
        let v3__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_2, v3_2);
        let v0__6: crate::lib::intvector_intrinsics::vec128 = v0__5;
        let v2__6: crate::lib::intvector_intrinsics::vec128 = v2__5;
        let v1__6: crate::lib::intvector_intrinsics::vec128 = v1__5;
        let v3__6: crate::lib::intvector_intrinsics::vec128 = v3__5;
        let v12: crate::lib::intvector_intrinsics::vec128 = v0__6;
        let v13: crate::lib::intvector_intrinsics::vec128 = v1__6;
        let v14: crate::lib::intvector_intrinsics::vec128 = v2__6;
        let v15: crate::lib::intvector_intrinsics::vec128 = v3__6;
        (&mut k)[0usize] = v0;
        (&mut k)[1usize] = v4;
        (&mut k)[2usize] = v8;
        (&mut k)[3usize] = v12;
        (&mut k)[4usize] = v1;
        (&mut k)[5usize] = v5;
        (&mut k)[6usize] = v9;
        (&mut k)[7usize] = v13;
        (&mut k)[8usize] = v2;
        (&mut k)[9usize] = v6;
        (&mut k)[10usize] = v10;
        (&mut k)[11usize] = v14;
        (&mut k)[12usize] = v3;
        (&mut k)[13usize] = v7;
        (&mut k)[14usize] = v11;
        (&mut k)[15usize] = v15;
        for i0 in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load32_le(
                    &mut uu____1.1[i0.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_xor(x, (&mut k)[i0 as usize]);
            crate::lib::intvector_intrinsics::vec128_store32_le(
                &mut uu____0.1[i0.wrapping_mul(16u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(256u32) as usize);
        let mut plain: [u8; 256] = [0u8; 256usize];
        ((&mut plain)[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut cipher[nb.wrapping_mul(256u32) as usize..])[0usize..0usize + rem as usize]
        );
        let mut k: [crate::lib::intvector_intrinsics::vec128; 16] =
            [crate::lib::intvector_intrinsics::vec128_zero; 16usize];
        chacha20_core_128(&mut k, &mut ctx, nb);
        let st0: crate::lib::intvector_intrinsics::vec128 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec128 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec128 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec128 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec128 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec128 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec128 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec128 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec128 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec128 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec128 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec128 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec128 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec128 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec128 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec128 = (&mut k)[15usize];
        let v0_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3_: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_, v2_);
        let v1__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_, v2_);
        let v2__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_, v3_);
        let v3__: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_, v3_);
        let v0__0: crate::lib::intvector_intrinsics::vec128 = v0__;
        let v2__0: crate::lib::intvector_intrinsics::vec128 = v2__;
        let v1__0: crate::lib::intvector_intrinsics::vec128 = v1__;
        let v3__0: crate::lib::intvector_intrinsics::vec128 = v3__;
        let v0: crate::lib::intvector_intrinsics::vec128 = v0__0;
        let v1: crate::lib::intvector_intrinsics::vec128 = v1__0;
        let v2: crate::lib::intvector_intrinsics::vec128 = v2__0;
        let v3: crate::lib::intvector_intrinsics::vec128 = v3__0;
        let v0_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3_0: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_0, v2_0);
        let v1__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_0, v2_0);
        let v2__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_0, v3_0);
        let v3__1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_0, v3_0);
        let v0__2: crate::lib::intvector_intrinsics::vec128 = v0__1;
        let v2__2: crate::lib::intvector_intrinsics::vec128 = v2__1;
        let v1__2: crate::lib::intvector_intrinsics::vec128 = v1__1;
        let v3__2: crate::lib::intvector_intrinsics::vec128 = v3__1;
        let v4: crate::lib::intvector_intrinsics::vec128 = v0__2;
        let v5: crate::lib::intvector_intrinsics::vec128 = v1__2;
        let v6: crate::lib::intvector_intrinsics::vec128 = v2__2;
        let v7: crate::lib::intvector_intrinsics::vec128 = v3__2;
        let v0_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3_1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_1, v2_1);
        let v1__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_1, v2_1);
        let v2__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_1, v3_1);
        let v3__3: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_1, v3_1);
        let v0__4: crate::lib::intvector_intrinsics::vec128 = v0__3;
        let v2__4: crate::lib::intvector_intrinsics::vec128 = v2__3;
        let v1__4: crate::lib::intvector_intrinsics::vec128 = v1__3;
        let v3__4: crate::lib::intvector_intrinsics::vec128 = v3__3;
        let v8: crate::lib::intvector_intrinsics::vec128 = v0__4;
        let v9: crate::lib::intvector_intrinsics::vec128 = v1__4;
        let v10: crate::lib::intvector_intrinsics::vec128 = v2__4;
        let v11: crate::lib::intvector_intrinsics::vec128 = v3__4;
        let v0_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3_2: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v0_2, v2_2);
        let v1__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v0_2, v2_2);
        let v2__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_low64(v1_2, v3_2);
        let v3__5: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_interleave_high64(v1_2, v3_2);
        let v0__6: crate::lib::intvector_intrinsics::vec128 = v0__5;
        let v2__6: crate::lib::intvector_intrinsics::vec128 = v2__5;
        let v1__6: crate::lib::intvector_intrinsics::vec128 = v1__5;
        let v3__6: crate::lib::intvector_intrinsics::vec128 = v3__5;
        let v12: crate::lib::intvector_intrinsics::vec128 = v0__6;
        let v13: crate::lib::intvector_intrinsics::vec128 = v1__6;
        let v14: crate::lib::intvector_intrinsics::vec128 = v2__6;
        let v15: crate::lib::intvector_intrinsics::vec128 = v3__6;
        (&mut k)[0usize] = v0;
        (&mut k)[1usize] = v4;
        (&mut k)[2usize] = v8;
        (&mut k)[3usize] = v12;
        (&mut k)[4usize] = v1;
        (&mut k)[5usize] = v5;
        (&mut k)[6usize] = v9;
        (&mut k)[7usize] = v13;
        (&mut k)[8usize] = v2;
        (&mut k)[9usize] = v6;
        (&mut k)[10usize] = v10;
        (&mut k)[11usize] = v14;
        (&mut k)[12usize] = v3;
        (&mut k)[13usize] = v7;
        (&mut k)[14usize] = v11;
        (&mut k)[15usize] = v15;
        for i in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_load32_le(
                    &mut (&mut plain)[i.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec128 =
                crate::lib::intvector_intrinsics::vec128_xor(x, (&mut k)[i as usize]);
            crate::lib::intvector_intrinsics::vec128_store32_le(
                &mut (&mut plain)[i.wrapping_mul(16u32) as usize..],
                y
            )
        };
        (uu____2.1[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0usize..])[0usize..0usize + rem as usize]
        )
    }
}
