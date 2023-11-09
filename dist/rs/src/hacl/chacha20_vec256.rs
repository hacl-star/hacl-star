fn double_round_256(st: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
{
    st[0usize] = crate::lib::intvector_intrinsics::vec256_add32(st[0usize], st[4usize]);
    let std: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[12usize], st[0usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std, 16u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec256_add32(st[8usize], st[12usize]);
    let std0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[4usize], st[8usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std0, 12u32);
    st[0usize] = crate::lib::intvector_intrinsics::vec256_add32(st[0usize], st[4usize]);
    let std1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[12usize], st[0usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std1, 8u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec256_add32(st[8usize], st[12usize]);
    let std2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[4usize], st[8usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std2, 7u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec256_add32(st[1usize], st[5usize]);
    let std3: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[13usize], st[1usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std3, 16u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec256_add32(st[9usize], st[13usize]);
    let std4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[5usize], st[9usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std4, 12u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec256_add32(st[1usize], st[5usize]);
    let std5: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[13usize], st[1usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std5, 8u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec256_add32(st[9usize], st[13usize]);
    let std6: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[5usize], st[9usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std6, 7u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec256_add32(st[2usize], st[6usize]);
    let std7: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[14usize], st[2usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std7, 16u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec256_add32(st[10usize], st[14usize]);
    let std8: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[6usize], st[10usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std8, 12u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec256_add32(st[2usize], st[6usize]);
    let std9: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[14usize], st[2usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std9, 8u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec256_add32(st[10usize], st[14usize]);
    let std10: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[6usize], st[10usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std10, 7u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec256_add32(st[3usize], st[7usize]);
    let std11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[15usize], st[3usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std11, 16u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec256_add32(st[11usize], st[15usize]);
    let std12: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[7usize], st[11usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std12, 12u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec256_add32(st[3usize], st[7usize]);
    let std13: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[15usize], st[3usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std13, 8u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec256_add32(st[11usize], st[15usize]);
    let std14: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[7usize], st[11usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std14, 7u32);
    st[0usize] = crate::lib::intvector_intrinsics::vec256_add32(st[0usize], st[5usize]);
    let std15: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[15usize], st[0usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std15, 16u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec256_add32(st[10usize], st[15usize]);
    let std16: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[5usize], st[10usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std16, 12u32);
    st[0usize] = crate::lib::intvector_intrinsics::vec256_add32(st[0usize], st[5usize]);
    let std17: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[15usize], st[0usize]);
    st[15usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std17, 8u32);
    st[10usize] = crate::lib::intvector_intrinsics::vec256_add32(st[10usize], st[15usize]);
    let std18: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[5usize], st[10usize]);
    st[5usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std18, 7u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec256_add32(st[1usize], st[6usize]);
    let std19: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[12usize], st[1usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std19, 16u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec256_add32(st[11usize], st[12usize]);
    let std20: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[6usize], st[11usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std20, 12u32);
    st[1usize] = crate::lib::intvector_intrinsics::vec256_add32(st[1usize], st[6usize]);
    let std21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[12usize], st[1usize]);
    st[12usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std21, 8u32);
    st[11usize] = crate::lib::intvector_intrinsics::vec256_add32(st[11usize], st[12usize]);
    let std22: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[6usize], st[11usize]);
    st[6usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std22, 7u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec256_add32(st[2usize], st[7usize]);
    let std23: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[13usize], st[2usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std23, 16u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec256_add32(st[8usize], st[13usize]);
    let std24: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[7usize], st[8usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std24, 12u32);
    st[2usize] = crate::lib::intvector_intrinsics::vec256_add32(st[2usize], st[7usize]);
    let std25: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[13usize], st[2usize]);
    st[13usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std25, 8u32);
    st[8usize] = crate::lib::intvector_intrinsics::vec256_add32(st[8usize], st[13usize]);
    let std26: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[7usize], st[8usize]);
    st[7usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std26, 7u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec256_add32(st[3usize], st[4usize]);
    let std27: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[14usize], st[3usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std27, 16u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec256_add32(st[9usize], st[14usize]);
    let std28: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[4usize], st[9usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std28, 12u32);
    st[3usize] = crate::lib::intvector_intrinsics::vec256_add32(st[3usize], st[4usize]);
    let std29: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[14usize], st[3usize]);
    st[14usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std29, 8u32);
    st[9usize] = crate::lib::intvector_intrinsics::vec256_add32(st[9usize], st[14usize]);
    let std30: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_xor(st[4usize], st[9usize]);
    st[4usize] = crate::lib::intvector_intrinsics::vec256_rotate_left32(std30, 7u32)
}

fn chacha20_core_256(
    k: &mut [crate::lib::intvector_intrinsics::vec256],
    ctx: &mut [crate::lib::intvector_intrinsics::vec256],
    ctr: u32
) ->
    ()
{
    (k[0usize..0usize + 16usize]).copy_from_slice(&ctx[0usize..0usize + 16usize]);
    let ctr_u32: u32 = 8u32.wrapping_mul(ctr);
    let cv: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load32(ctr_u32);
    k[12usize] = crate::lib::intvector_intrinsics::vec256_add32(k[12usize], cv);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    double_round_256(k);
    for i in 0u32..16u32
    {
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            k.split_at_mut(0usize);
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add32(os.1[i as usize], ctx[i as usize]);
        os.1[i as usize] = x
    };
    k[12usize] = crate::lib::intvector_intrinsics::vec256_add32(k[12usize], cv)
}

fn chacha20_init_256(
    ctx: &mut [crate::lib::intvector_intrinsics::vec256],
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
        let bj: (&mut [u8], &mut [u8]) =
            k.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    };
    (&mut ctx1)[12usize] = ctr;
    for i in 0u32..3u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[13usize..])[0usize..];
        let bj: (&mut [u8], &mut [u8]) =
            n.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    };
    for i in 0u32..16u32
    {
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            ctx.split_at_mut(0usize);
        let x: u32 = (&mut ctx1)[i as usize];
        let x0: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load32(x);
        os.1[i as usize] = x0
    };
    let ctr1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_load32s(
            0u32,
            1u32,
            2u32,
            3u32,
            4u32,
            5u32,
            6u32,
            7u32
        );
    let c12: crate::lib::intvector_intrinsics::vec256 = ctx[12usize];
    ctx[12usize] = crate::lib::intvector_intrinsics::vec256_add32(c12, ctr1)
}

pub fn chacha20_encrypt_256(
    len: u32,
    out: &mut [u8],
    text: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [crate::lib::intvector_intrinsics::vec256; 16] =
        [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
    chacha20_init_256(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(512u32);
    let nb: u32 = len.wrapping_div(512u32);
    let rem1: u32 = len.wrapping_rem(512u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) =
            out.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
        let uu____1: (&mut [u8], &mut [u8]) =
            text.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
        let mut k: [crate::lib::intvector_intrinsics::vec256; 16] =
            [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
        chacha20_core_256(&mut k, &mut ctx, i);
        let st0: crate::lib::intvector_intrinsics::vec256 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec256 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec256 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec256 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec256 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec256 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec256 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec256 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec256 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec256 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec256 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec256 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec256 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec256 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec256 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec256 = (&mut k)[15usize];
        let v0: crate::lib::intvector_intrinsics::vec256 = st0;
        let v1: crate::lib::intvector_intrinsics::vec256 = st1;
        let v2: crate::lib::intvector_intrinsics::vec256 = st2;
        let v3: crate::lib::intvector_intrinsics::vec256 = st3;
        let v4: crate::lib::intvector_intrinsics::vec256 = st4;
        let v5: crate::lib::intvector_intrinsics::vec256 = st5;
        let v6: crate::lib::intvector_intrinsics::vec256 = st6;
        let v7: crate::lib::intvector_intrinsics::vec256 = st7;
        let v0_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
        let v1_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
        let v2_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
        let v3_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
        let v4_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
        let v5_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
        let v6_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
        let v7_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
        let v0_0: crate::lib::intvector_intrinsics::vec256 = v0_;
        let v1_0: crate::lib::intvector_intrinsics::vec256 = v1_;
        let v2_0: crate::lib::intvector_intrinsics::vec256 = v2_;
        let v3_0: crate::lib::intvector_intrinsics::vec256 = v3_;
        let v4_0: crate::lib::intvector_intrinsics::vec256 = v4_;
        let v5_0: crate::lib::intvector_intrinsics::vec256 = v5_;
        let v6_0: crate::lib::intvector_intrinsics::vec256 = v6_;
        let v7_0: crate::lib::intvector_intrinsics::vec256 = v7_;
        let v0_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_0, v2_0);
        let v2_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_0, v2_0);
        let v1_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_0, v3_0);
        let v3_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_0, v3_0);
        let v4_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_0, v6_0);
        let v6_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_0, v6_0);
        let v5_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_0, v7_0);
        let v7_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_0, v7_0);
        let v0_10: crate::lib::intvector_intrinsics::vec256 = v0_1;
        let v1_10: crate::lib::intvector_intrinsics::vec256 = v1_1;
        let v2_10: crate::lib::intvector_intrinsics::vec256 = v2_1;
        let v3_10: crate::lib::intvector_intrinsics::vec256 = v3_1;
        let v4_10: crate::lib::intvector_intrinsics::vec256 = v4_1;
        let v5_10: crate::lib::intvector_intrinsics::vec256 = v5_1;
        let v6_10: crate::lib::intvector_intrinsics::vec256 = v6_1;
        let v7_10: crate::lib::intvector_intrinsics::vec256 = v7_1;
        let v0_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_10, v4_10);
        let v4_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_10, v4_10);
        let v1_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_10, v5_10);
        let v5_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_10, v5_10);
        let v2_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_10, v6_10);
        let v6_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_10, v6_10);
        let v3_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_10, v7_10);
        let v7_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_10, v7_10);
        let v0_20: crate::lib::intvector_intrinsics::vec256 = v0_2;
        let v1_20: crate::lib::intvector_intrinsics::vec256 = v1_2;
        let v2_20: crate::lib::intvector_intrinsics::vec256 = v2_2;
        let v3_20: crate::lib::intvector_intrinsics::vec256 = v3_2;
        let v4_20: crate::lib::intvector_intrinsics::vec256 = v4_2;
        let v5_20: crate::lib::intvector_intrinsics::vec256 = v5_2;
        let v6_20: crate::lib::intvector_intrinsics::vec256 = v6_2;
        let v7_20: crate::lib::intvector_intrinsics::vec256 = v7_2;
        let v0_3: crate::lib::intvector_intrinsics::vec256 = v0_20;
        let v1_3: crate::lib::intvector_intrinsics::vec256 = v1_20;
        let v2_3: crate::lib::intvector_intrinsics::vec256 = v2_20;
        let v3_3: crate::lib::intvector_intrinsics::vec256 = v3_20;
        let v4_3: crate::lib::intvector_intrinsics::vec256 = v4_20;
        let v5_3: crate::lib::intvector_intrinsics::vec256 = v5_20;
        let v6_3: crate::lib::intvector_intrinsics::vec256 = v6_20;
        let v7_3: crate::lib::intvector_intrinsics::vec256 = v7_20;
        let v00: crate::lib::intvector_intrinsics::vec256 = v0_3;
        let v10: crate::lib::intvector_intrinsics::vec256 = v2_3;
        let v20: crate::lib::intvector_intrinsics::vec256 = v1_3;
        let v30: crate::lib::intvector_intrinsics::vec256 = v3_3;
        let v40: crate::lib::intvector_intrinsics::vec256 = v4_3;
        let v50: crate::lib::intvector_intrinsics::vec256 = v6_3;
        let v60: crate::lib::intvector_intrinsics::vec256 = v5_3;
        let v70: crate::lib::intvector_intrinsics::vec256 = v7_3;
        let v01: crate::lib::intvector_intrinsics::vec256 = st8;
        let v11: crate::lib::intvector_intrinsics::vec256 = st9;
        let v21: crate::lib::intvector_intrinsics::vec256 = st10;
        let v31: crate::lib::intvector_intrinsics::vec256 = st11;
        let v41: crate::lib::intvector_intrinsics::vec256 = st12;
        let v51: crate::lib::intvector_intrinsics::vec256 = st13;
        let v61: crate::lib::intvector_intrinsics::vec256 = st14;
        let v71: crate::lib::intvector_intrinsics::vec256 = st15;
        let v0_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v01, v11);
        let v1_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v01, v11);
        let v2_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v21, v31);
        let v3_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v21, v31);
        let v4_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v41, v51);
        let v5_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v41, v51);
        let v6_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v61, v71);
        let v7_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v61, v71);
        let v0_5: crate::lib::intvector_intrinsics::vec256 = v0_4;
        let v1_5: crate::lib::intvector_intrinsics::vec256 = v1_4;
        let v2_5: crate::lib::intvector_intrinsics::vec256 = v2_4;
        let v3_5: crate::lib::intvector_intrinsics::vec256 = v3_4;
        let v4_5: crate::lib::intvector_intrinsics::vec256 = v4_4;
        let v5_5: crate::lib::intvector_intrinsics::vec256 = v5_4;
        let v6_5: crate::lib::intvector_intrinsics::vec256 = v6_4;
        let v7_5: crate::lib::intvector_intrinsics::vec256 = v7_4;
        let v0_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_5, v2_5);
        let v2_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_5, v2_5);
        let v1_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_5, v3_5);
        let v3_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_5, v3_5);
        let v4_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_5, v6_5);
        let v6_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_5, v6_5);
        let v5_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_5, v7_5);
        let v7_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_5, v7_5);
        let v0_12: crate::lib::intvector_intrinsics::vec256 = v0_11;
        let v1_12: crate::lib::intvector_intrinsics::vec256 = v1_11;
        let v2_12: crate::lib::intvector_intrinsics::vec256 = v2_11;
        let v3_12: crate::lib::intvector_intrinsics::vec256 = v3_11;
        let v4_12: crate::lib::intvector_intrinsics::vec256 = v4_11;
        let v5_12: crate::lib::intvector_intrinsics::vec256 = v5_11;
        let v6_12: crate::lib::intvector_intrinsics::vec256 = v6_11;
        let v7_12: crate::lib::intvector_intrinsics::vec256 = v7_11;
        let v0_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_12, v4_12);
        let v4_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_12, v4_12);
        let v1_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_12, v5_12);
        let v5_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_12, v5_12);
        let v2_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_12, v6_12);
        let v6_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_12, v6_12);
        let v3_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_12, v7_12);
        let v7_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_12, v7_12);
        let v0_22: crate::lib::intvector_intrinsics::vec256 = v0_21;
        let v1_22: crate::lib::intvector_intrinsics::vec256 = v1_21;
        let v2_22: crate::lib::intvector_intrinsics::vec256 = v2_21;
        let v3_22: crate::lib::intvector_intrinsics::vec256 = v3_21;
        let v4_22: crate::lib::intvector_intrinsics::vec256 = v4_21;
        let v5_22: crate::lib::intvector_intrinsics::vec256 = v5_21;
        let v6_22: crate::lib::intvector_intrinsics::vec256 = v6_21;
        let v7_22: crate::lib::intvector_intrinsics::vec256 = v7_21;
        let v0_6: crate::lib::intvector_intrinsics::vec256 = v0_22;
        let v1_6: crate::lib::intvector_intrinsics::vec256 = v1_22;
        let v2_6: crate::lib::intvector_intrinsics::vec256 = v2_22;
        let v3_6: crate::lib::intvector_intrinsics::vec256 = v3_22;
        let v4_6: crate::lib::intvector_intrinsics::vec256 = v4_22;
        let v5_6: crate::lib::intvector_intrinsics::vec256 = v5_22;
        let v6_6: crate::lib::intvector_intrinsics::vec256 = v6_22;
        let v7_6: crate::lib::intvector_intrinsics::vec256 = v7_22;
        let v8: crate::lib::intvector_intrinsics::vec256 = v0_6;
        let v9: crate::lib::intvector_intrinsics::vec256 = v2_6;
        let v100: crate::lib::intvector_intrinsics::vec256 = v1_6;
        let v110: crate::lib::intvector_intrinsics::vec256 = v3_6;
        let v12: crate::lib::intvector_intrinsics::vec256 = v4_6;
        let v13: crate::lib::intvector_intrinsics::vec256 = v6_6;
        let v14: crate::lib::intvector_intrinsics::vec256 = v5_6;
        let v15: crate::lib::intvector_intrinsics::vec256 = v7_6;
        (&mut k)[0usize] = v00;
        (&mut k)[1usize] = v8;
        (&mut k)[2usize] = v10;
        (&mut k)[3usize] = v9;
        (&mut k)[4usize] = v20;
        (&mut k)[5usize] = v100;
        (&mut k)[6usize] = v30;
        (&mut k)[7usize] = v110;
        (&mut k)[8usize] = v40;
        (&mut k)[9usize] = v12;
        (&mut k)[10usize] = v50;
        (&mut k)[11usize] = v13;
        (&mut k)[12usize] = v60;
        (&mut k)[13usize] = v14;
        (&mut k)[14usize] = v70;
        (&mut k)[15usize] = v15;
        for i0 in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load32_le(
                    &mut uu____1.1[i0.wrapping_mul(32u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_xor(x, (&mut k)[i0 as usize]);
            crate::lib::intvector_intrinsics::vec256_store32_le(
                &mut uu____0.1[i0.wrapping_mul(32u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) =
            out.split_at_mut((nb.wrapping_mul(512u32) as usize).wrapping_add(0usize));
        let mut plain: [u8; 512] = [0u8; 512usize];
        ((&mut plain)[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut text[nb.wrapping_mul(512u32) as usize..])[0usize..0usize + rem as usize]
        );
        let mut k: [crate::lib::intvector_intrinsics::vec256; 16] =
            [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
        chacha20_core_256(&mut k, &mut ctx, nb);
        let st0: crate::lib::intvector_intrinsics::vec256 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec256 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec256 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec256 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec256 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec256 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec256 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec256 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec256 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec256 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec256 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec256 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec256 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec256 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec256 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec256 = (&mut k)[15usize];
        let v0: crate::lib::intvector_intrinsics::vec256 = st0;
        let v1: crate::lib::intvector_intrinsics::vec256 = st1;
        let v2: crate::lib::intvector_intrinsics::vec256 = st2;
        let v3: crate::lib::intvector_intrinsics::vec256 = st3;
        let v4: crate::lib::intvector_intrinsics::vec256 = st4;
        let v5: crate::lib::intvector_intrinsics::vec256 = st5;
        let v6: crate::lib::intvector_intrinsics::vec256 = st6;
        let v7: crate::lib::intvector_intrinsics::vec256 = st7;
        let v0_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
        let v1_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
        let v2_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
        let v3_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
        let v4_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
        let v5_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
        let v6_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
        let v7_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
        let v0_0: crate::lib::intvector_intrinsics::vec256 = v0_;
        let v1_0: crate::lib::intvector_intrinsics::vec256 = v1_;
        let v2_0: crate::lib::intvector_intrinsics::vec256 = v2_;
        let v3_0: crate::lib::intvector_intrinsics::vec256 = v3_;
        let v4_0: crate::lib::intvector_intrinsics::vec256 = v4_;
        let v5_0: crate::lib::intvector_intrinsics::vec256 = v5_;
        let v6_0: crate::lib::intvector_intrinsics::vec256 = v6_;
        let v7_0: crate::lib::intvector_intrinsics::vec256 = v7_;
        let v0_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_0, v2_0);
        let v2_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_0, v2_0);
        let v1_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_0, v3_0);
        let v3_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_0, v3_0);
        let v4_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_0, v6_0);
        let v6_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_0, v6_0);
        let v5_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_0, v7_0);
        let v7_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_0, v7_0);
        let v0_10: crate::lib::intvector_intrinsics::vec256 = v0_1;
        let v1_10: crate::lib::intvector_intrinsics::vec256 = v1_1;
        let v2_10: crate::lib::intvector_intrinsics::vec256 = v2_1;
        let v3_10: crate::lib::intvector_intrinsics::vec256 = v3_1;
        let v4_10: crate::lib::intvector_intrinsics::vec256 = v4_1;
        let v5_10: crate::lib::intvector_intrinsics::vec256 = v5_1;
        let v6_10: crate::lib::intvector_intrinsics::vec256 = v6_1;
        let v7_10: crate::lib::intvector_intrinsics::vec256 = v7_1;
        let v0_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_10, v4_10);
        let v4_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_10, v4_10);
        let v1_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_10, v5_10);
        let v5_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_10, v5_10);
        let v2_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_10, v6_10);
        let v6_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_10, v6_10);
        let v3_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_10, v7_10);
        let v7_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_10, v7_10);
        let v0_20: crate::lib::intvector_intrinsics::vec256 = v0_2;
        let v1_20: crate::lib::intvector_intrinsics::vec256 = v1_2;
        let v2_20: crate::lib::intvector_intrinsics::vec256 = v2_2;
        let v3_20: crate::lib::intvector_intrinsics::vec256 = v3_2;
        let v4_20: crate::lib::intvector_intrinsics::vec256 = v4_2;
        let v5_20: crate::lib::intvector_intrinsics::vec256 = v5_2;
        let v6_20: crate::lib::intvector_intrinsics::vec256 = v6_2;
        let v7_20: crate::lib::intvector_intrinsics::vec256 = v7_2;
        let v0_3: crate::lib::intvector_intrinsics::vec256 = v0_20;
        let v1_3: crate::lib::intvector_intrinsics::vec256 = v1_20;
        let v2_3: crate::lib::intvector_intrinsics::vec256 = v2_20;
        let v3_3: crate::lib::intvector_intrinsics::vec256 = v3_20;
        let v4_3: crate::lib::intvector_intrinsics::vec256 = v4_20;
        let v5_3: crate::lib::intvector_intrinsics::vec256 = v5_20;
        let v6_3: crate::lib::intvector_intrinsics::vec256 = v6_20;
        let v7_3: crate::lib::intvector_intrinsics::vec256 = v7_20;
        let v00: crate::lib::intvector_intrinsics::vec256 = v0_3;
        let v10: crate::lib::intvector_intrinsics::vec256 = v2_3;
        let v20: crate::lib::intvector_intrinsics::vec256 = v1_3;
        let v30: crate::lib::intvector_intrinsics::vec256 = v3_3;
        let v40: crate::lib::intvector_intrinsics::vec256 = v4_3;
        let v50: crate::lib::intvector_intrinsics::vec256 = v6_3;
        let v60: crate::lib::intvector_intrinsics::vec256 = v5_3;
        let v70: crate::lib::intvector_intrinsics::vec256 = v7_3;
        let v01: crate::lib::intvector_intrinsics::vec256 = st8;
        let v11: crate::lib::intvector_intrinsics::vec256 = st9;
        let v21: crate::lib::intvector_intrinsics::vec256 = st10;
        let v31: crate::lib::intvector_intrinsics::vec256 = st11;
        let v41: crate::lib::intvector_intrinsics::vec256 = st12;
        let v51: crate::lib::intvector_intrinsics::vec256 = st13;
        let v61: crate::lib::intvector_intrinsics::vec256 = st14;
        let v71: crate::lib::intvector_intrinsics::vec256 = st15;
        let v0_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v01, v11);
        let v1_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v01, v11);
        let v2_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v21, v31);
        let v3_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v21, v31);
        let v4_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v41, v51);
        let v5_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v41, v51);
        let v6_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v61, v71);
        let v7_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v61, v71);
        let v0_5: crate::lib::intvector_intrinsics::vec256 = v0_4;
        let v1_5: crate::lib::intvector_intrinsics::vec256 = v1_4;
        let v2_5: crate::lib::intvector_intrinsics::vec256 = v2_4;
        let v3_5: crate::lib::intvector_intrinsics::vec256 = v3_4;
        let v4_5: crate::lib::intvector_intrinsics::vec256 = v4_4;
        let v5_5: crate::lib::intvector_intrinsics::vec256 = v5_4;
        let v6_5: crate::lib::intvector_intrinsics::vec256 = v6_4;
        let v7_5: crate::lib::intvector_intrinsics::vec256 = v7_4;
        let v0_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_5, v2_5);
        let v2_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_5, v2_5);
        let v1_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_5, v3_5);
        let v3_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_5, v3_5);
        let v4_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_5, v6_5);
        let v6_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_5, v6_5);
        let v5_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_5, v7_5);
        let v7_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_5, v7_5);
        let v0_12: crate::lib::intvector_intrinsics::vec256 = v0_11;
        let v1_12: crate::lib::intvector_intrinsics::vec256 = v1_11;
        let v2_12: crate::lib::intvector_intrinsics::vec256 = v2_11;
        let v3_12: crate::lib::intvector_intrinsics::vec256 = v3_11;
        let v4_12: crate::lib::intvector_intrinsics::vec256 = v4_11;
        let v5_12: crate::lib::intvector_intrinsics::vec256 = v5_11;
        let v6_12: crate::lib::intvector_intrinsics::vec256 = v6_11;
        let v7_12: crate::lib::intvector_intrinsics::vec256 = v7_11;
        let v0_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_12, v4_12);
        let v4_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_12, v4_12);
        let v1_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_12, v5_12);
        let v5_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_12, v5_12);
        let v2_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_12, v6_12);
        let v6_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_12, v6_12);
        let v3_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_12, v7_12);
        let v7_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_12, v7_12);
        let v0_22: crate::lib::intvector_intrinsics::vec256 = v0_21;
        let v1_22: crate::lib::intvector_intrinsics::vec256 = v1_21;
        let v2_22: crate::lib::intvector_intrinsics::vec256 = v2_21;
        let v3_22: crate::lib::intvector_intrinsics::vec256 = v3_21;
        let v4_22: crate::lib::intvector_intrinsics::vec256 = v4_21;
        let v5_22: crate::lib::intvector_intrinsics::vec256 = v5_21;
        let v6_22: crate::lib::intvector_intrinsics::vec256 = v6_21;
        let v7_22: crate::lib::intvector_intrinsics::vec256 = v7_21;
        let v0_6: crate::lib::intvector_intrinsics::vec256 = v0_22;
        let v1_6: crate::lib::intvector_intrinsics::vec256 = v1_22;
        let v2_6: crate::lib::intvector_intrinsics::vec256 = v2_22;
        let v3_6: crate::lib::intvector_intrinsics::vec256 = v3_22;
        let v4_6: crate::lib::intvector_intrinsics::vec256 = v4_22;
        let v5_6: crate::lib::intvector_intrinsics::vec256 = v5_22;
        let v6_6: crate::lib::intvector_intrinsics::vec256 = v6_22;
        let v7_6: crate::lib::intvector_intrinsics::vec256 = v7_22;
        let v8: crate::lib::intvector_intrinsics::vec256 = v0_6;
        let v9: crate::lib::intvector_intrinsics::vec256 = v2_6;
        let v100: crate::lib::intvector_intrinsics::vec256 = v1_6;
        let v110: crate::lib::intvector_intrinsics::vec256 = v3_6;
        let v12: crate::lib::intvector_intrinsics::vec256 = v4_6;
        let v13: crate::lib::intvector_intrinsics::vec256 = v6_6;
        let v14: crate::lib::intvector_intrinsics::vec256 = v5_6;
        let v15: crate::lib::intvector_intrinsics::vec256 = v7_6;
        (&mut k)[0usize] = v00;
        (&mut k)[1usize] = v8;
        (&mut k)[2usize] = v10;
        (&mut k)[3usize] = v9;
        (&mut k)[4usize] = v20;
        (&mut k)[5usize] = v100;
        (&mut k)[6usize] = v30;
        (&mut k)[7usize] = v110;
        (&mut k)[8usize] = v40;
        (&mut k)[9usize] = v12;
        (&mut k)[10usize] = v50;
        (&mut k)[11usize] = v13;
        (&mut k)[12usize] = v60;
        (&mut k)[13usize] = v14;
        (&mut k)[14usize] = v70;
        (&mut k)[15usize] = v15;
        for i in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load32_le(
                    &mut (&mut plain)[i.wrapping_mul(32u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_xor(x, (&mut k)[i as usize]);
            crate::lib::intvector_intrinsics::vec256_store32_le(
                &mut (&mut plain)[i.wrapping_mul(32u32) as usize..],
                y
            )
        };
        (uu____2.1[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0usize..])[0usize..0usize + rem as usize]
        )
    }
}

pub fn chacha20_decrypt_256(
    len: u32,
    out: &mut [u8],
    cipher: &mut [u8],
    key: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx: [crate::lib::intvector_intrinsics::vec256; 16] =
        [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
    chacha20_init_256(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(512u32);
    let nb: u32 = len.wrapping_div(512u32);
    let rem1: u32 = len.wrapping_rem(512u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) =
            out.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
        let uu____1: (&mut [u8], &mut [u8]) =
            cipher.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
        let mut k: [crate::lib::intvector_intrinsics::vec256; 16] =
            [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
        chacha20_core_256(&mut k, &mut ctx, i);
        let st0: crate::lib::intvector_intrinsics::vec256 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec256 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec256 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec256 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec256 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec256 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec256 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec256 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec256 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec256 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec256 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec256 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec256 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec256 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec256 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec256 = (&mut k)[15usize];
        let v0: crate::lib::intvector_intrinsics::vec256 = st0;
        let v1: crate::lib::intvector_intrinsics::vec256 = st1;
        let v2: crate::lib::intvector_intrinsics::vec256 = st2;
        let v3: crate::lib::intvector_intrinsics::vec256 = st3;
        let v4: crate::lib::intvector_intrinsics::vec256 = st4;
        let v5: crate::lib::intvector_intrinsics::vec256 = st5;
        let v6: crate::lib::intvector_intrinsics::vec256 = st6;
        let v7: crate::lib::intvector_intrinsics::vec256 = st7;
        let v0_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
        let v1_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
        let v2_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
        let v3_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
        let v4_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
        let v5_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
        let v6_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
        let v7_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
        let v0_0: crate::lib::intvector_intrinsics::vec256 = v0_;
        let v1_0: crate::lib::intvector_intrinsics::vec256 = v1_;
        let v2_0: crate::lib::intvector_intrinsics::vec256 = v2_;
        let v3_0: crate::lib::intvector_intrinsics::vec256 = v3_;
        let v4_0: crate::lib::intvector_intrinsics::vec256 = v4_;
        let v5_0: crate::lib::intvector_intrinsics::vec256 = v5_;
        let v6_0: crate::lib::intvector_intrinsics::vec256 = v6_;
        let v7_0: crate::lib::intvector_intrinsics::vec256 = v7_;
        let v0_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_0, v2_0);
        let v2_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_0, v2_0);
        let v1_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_0, v3_0);
        let v3_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_0, v3_0);
        let v4_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_0, v6_0);
        let v6_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_0, v6_0);
        let v5_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_0, v7_0);
        let v7_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_0, v7_0);
        let v0_10: crate::lib::intvector_intrinsics::vec256 = v0_1;
        let v1_10: crate::lib::intvector_intrinsics::vec256 = v1_1;
        let v2_10: crate::lib::intvector_intrinsics::vec256 = v2_1;
        let v3_10: crate::lib::intvector_intrinsics::vec256 = v3_1;
        let v4_10: crate::lib::intvector_intrinsics::vec256 = v4_1;
        let v5_10: crate::lib::intvector_intrinsics::vec256 = v5_1;
        let v6_10: crate::lib::intvector_intrinsics::vec256 = v6_1;
        let v7_10: crate::lib::intvector_intrinsics::vec256 = v7_1;
        let v0_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_10, v4_10);
        let v4_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_10, v4_10);
        let v1_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_10, v5_10);
        let v5_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_10, v5_10);
        let v2_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_10, v6_10);
        let v6_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_10, v6_10);
        let v3_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_10, v7_10);
        let v7_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_10, v7_10);
        let v0_20: crate::lib::intvector_intrinsics::vec256 = v0_2;
        let v1_20: crate::lib::intvector_intrinsics::vec256 = v1_2;
        let v2_20: crate::lib::intvector_intrinsics::vec256 = v2_2;
        let v3_20: crate::lib::intvector_intrinsics::vec256 = v3_2;
        let v4_20: crate::lib::intvector_intrinsics::vec256 = v4_2;
        let v5_20: crate::lib::intvector_intrinsics::vec256 = v5_2;
        let v6_20: crate::lib::intvector_intrinsics::vec256 = v6_2;
        let v7_20: crate::lib::intvector_intrinsics::vec256 = v7_2;
        let v0_3: crate::lib::intvector_intrinsics::vec256 = v0_20;
        let v1_3: crate::lib::intvector_intrinsics::vec256 = v1_20;
        let v2_3: crate::lib::intvector_intrinsics::vec256 = v2_20;
        let v3_3: crate::lib::intvector_intrinsics::vec256 = v3_20;
        let v4_3: crate::lib::intvector_intrinsics::vec256 = v4_20;
        let v5_3: crate::lib::intvector_intrinsics::vec256 = v5_20;
        let v6_3: crate::lib::intvector_intrinsics::vec256 = v6_20;
        let v7_3: crate::lib::intvector_intrinsics::vec256 = v7_20;
        let v00: crate::lib::intvector_intrinsics::vec256 = v0_3;
        let v10: crate::lib::intvector_intrinsics::vec256 = v2_3;
        let v20: crate::lib::intvector_intrinsics::vec256 = v1_3;
        let v30: crate::lib::intvector_intrinsics::vec256 = v3_3;
        let v40: crate::lib::intvector_intrinsics::vec256 = v4_3;
        let v50: crate::lib::intvector_intrinsics::vec256 = v6_3;
        let v60: crate::lib::intvector_intrinsics::vec256 = v5_3;
        let v70: crate::lib::intvector_intrinsics::vec256 = v7_3;
        let v01: crate::lib::intvector_intrinsics::vec256 = st8;
        let v11: crate::lib::intvector_intrinsics::vec256 = st9;
        let v21: crate::lib::intvector_intrinsics::vec256 = st10;
        let v31: crate::lib::intvector_intrinsics::vec256 = st11;
        let v41: crate::lib::intvector_intrinsics::vec256 = st12;
        let v51: crate::lib::intvector_intrinsics::vec256 = st13;
        let v61: crate::lib::intvector_intrinsics::vec256 = st14;
        let v71: crate::lib::intvector_intrinsics::vec256 = st15;
        let v0_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v01, v11);
        let v1_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v01, v11);
        let v2_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v21, v31);
        let v3_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v21, v31);
        let v4_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v41, v51);
        let v5_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v41, v51);
        let v6_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v61, v71);
        let v7_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v61, v71);
        let v0_5: crate::lib::intvector_intrinsics::vec256 = v0_4;
        let v1_5: crate::lib::intvector_intrinsics::vec256 = v1_4;
        let v2_5: crate::lib::intvector_intrinsics::vec256 = v2_4;
        let v3_5: crate::lib::intvector_intrinsics::vec256 = v3_4;
        let v4_5: crate::lib::intvector_intrinsics::vec256 = v4_4;
        let v5_5: crate::lib::intvector_intrinsics::vec256 = v5_4;
        let v6_5: crate::lib::intvector_intrinsics::vec256 = v6_4;
        let v7_5: crate::lib::intvector_intrinsics::vec256 = v7_4;
        let v0_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_5, v2_5);
        let v2_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_5, v2_5);
        let v1_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_5, v3_5);
        let v3_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_5, v3_5);
        let v4_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_5, v6_5);
        let v6_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_5, v6_5);
        let v5_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_5, v7_5);
        let v7_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_5, v7_5);
        let v0_12: crate::lib::intvector_intrinsics::vec256 = v0_11;
        let v1_12: crate::lib::intvector_intrinsics::vec256 = v1_11;
        let v2_12: crate::lib::intvector_intrinsics::vec256 = v2_11;
        let v3_12: crate::lib::intvector_intrinsics::vec256 = v3_11;
        let v4_12: crate::lib::intvector_intrinsics::vec256 = v4_11;
        let v5_12: crate::lib::intvector_intrinsics::vec256 = v5_11;
        let v6_12: crate::lib::intvector_intrinsics::vec256 = v6_11;
        let v7_12: crate::lib::intvector_intrinsics::vec256 = v7_11;
        let v0_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_12, v4_12);
        let v4_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_12, v4_12);
        let v1_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_12, v5_12);
        let v5_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_12, v5_12);
        let v2_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_12, v6_12);
        let v6_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_12, v6_12);
        let v3_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_12, v7_12);
        let v7_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_12, v7_12);
        let v0_22: crate::lib::intvector_intrinsics::vec256 = v0_21;
        let v1_22: crate::lib::intvector_intrinsics::vec256 = v1_21;
        let v2_22: crate::lib::intvector_intrinsics::vec256 = v2_21;
        let v3_22: crate::lib::intvector_intrinsics::vec256 = v3_21;
        let v4_22: crate::lib::intvector_intrinsics::vec256 = v4_21;
        let v5_22: crate::lib::intvector_intrinsics::vec256 = v5_21;
        let v6_22: crate::lib::intvector_intrinsics::vec256 = v6_21;
        let v7_22: crate::lib::intvector_intrinsics::vec256 = v7_21;
        let v0_6: crate::lib::intvector_intrinsics::vec256 = v0_22;
        let v1_6: crate::lib::intvector_intrinsics::vec256 = v1_22;
        let v2_6: crate::lib::intvector_intrinsics::vec256 = v2_22;
        let v3_6: crate::lib::intvector_intrinsics::vec256 = v3_22;
        let v4_6: crate::lib::intvector_intrinsics::vec256 = v4_22;
        let v5_6: crate::lib::intvector_intrinsics::vec256 = v5_22;
        let v6_6: crate::lib::intvector_intrinsics::vec256 = v6_22;
        let v7_6: crate::lib::intvector_intrinsics::vec256 = v7_22;
        let v8: crate::lib::intvector_intrinsics::vec256 = v0_6;
        let v9: crate::lib::intvector_intrinsics::vec256 = v2_6;
        let v100: crate::lib::intvector_intrinsics::vec256 = v1_6;
        let v110: crate::lib::intvector_intrinsics::vec256 = v3_6;
        let v12: crate::lib::intvector_intrinsics::vec256 = v4_6;
        let v13: crate::lib::intvector_intrinsics::vec256 = v6_6;
        let v14: crate::lib::intvector_intrinsics::vec256 = v5_6;
        let v15: crate::lib::intvector_intrinsics::vec256 = v7_6;
        (&mut k)[0usize] = v00;
        (&mut k)[1usize] = v8;
        (&mut k)[2usize] = v10;
        (&mut k)[3usize] = v9;
        (&mut k)[4usize] = v20;
        (&mut k)[5usize] = v100;
        (&mut k)[6usize] = v30;
        (&mut k)[7usize] = v110;
        (&mut k)[8usize] = v40;
        (&mut k)[9usize] = v12;
        (&mut k)[10usize] = v50;
        (&mut k)[11usize] = v13;
        (&mut k)[12usize] = v60;
        (&mut k)[13usize] = v14;
        (&mut k)[14usize] = v70;
        (&mut k)[15usize] = v15;
        for i0 in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load32_le(
                    &mut uu____1.1[i0.wrapping_mul(32u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_xor(x, (&mut k)[i0 as usize]);
            crate::lib::intvector_intrinsics::vec256_store32_le(
                &mut uu____0.1[i0.wrapping_mul(32u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) =
            out.split_at_mut((nb.wrapping_mul(512u32) as usize).wrapping_add(0usize));
        let mut plain: [u8; 512] = [0u8; 512usize];
        ((&mut plain)[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut cipher[nb.wrapping_mul(512u32) as usize..])[0usize..0usize + rem as usize]
        );
        let mut k: [crate::lib::intvector_intrinsics::vec256; 16] =
            [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
        chacha20_core_256(&mut k, &mut ctx, nb);
        let st0: crate::lib::intvector_intrinsics::vec256 = (&mut k)[0usize];
        let st1: crate::lib::intvector_intrinsics::vec256 = (&mut k)[1usize];
        let st2: crate::lib::intvector_intrinsics::vec256 = (&mut k)[2usize];
        let st3: crate::lib::intvector_intrinsics::vec256 = (&mut k)[3usize];
        let st4: crate::lib::intvector_intrinsics::vec256 = (&mut k)[4usize];
        let st5: crate::lib::intvector_intrinsics::vec256 = (&mut k)[5usize];
        let st6: crate::lib::intvector_intrinsics::vec256 = (&mut k)[6usize];
        let st7: crate::lib::intvector_intrinsics::vec256 = (&mut k)[7usize];
        let st8: crate::lib::intvector_intrinsics::vec256 = (&mut k)[8usize];
        let st9: crate::lib::intvector_intrinsics::vec256 = (&mut k)[9usize];
        let st10: crate::lib::intvector_intrinsics::vec256 = (&mut k)[10usize];
        let st11: crate::lib::intvector_intrinsics::vec256 = (&mut k)[11usize];
        let st12: crate::lib::intvector_intrinsics::vec256 = (&mut k)[12usize];
        let st13: crate::lib::intvector_intrinsics::vec256 = (&mut k)[13usize];
        let st14: crate::lib::intvector_intrinsics::vec256 = (&mut k)[14usize];
        let st15: crate::lib::intvector_intrinsics::vec256 = (&mut k)[15usize];
        let v0: crate::lib::intvector_intrinsics::vec256 = st0;
        let v1: crate::lib::intvector_intrinsics::vec256 = st1;
        let v2: crate::lib::intvector_intrinsics::vec256 = st2;
        let v3: crate::lib::intvector_intrinsics::vec256 = st3;
        let v4: crate::lib::intvector_intrinsics::vec256 = st4;
        let v5: crate::lib::intvector_intrinsics::vec256 = st5;
        let v6: crate::lib::intvector_intrinsics::vec256 = st6;
        let v7: crate::lib::intvector_intrinsics::vec256 = st7;
        let v0_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
        let v1_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
        let v2_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
        let v3_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
        let v4_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
        let v5_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
        let v6_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
        let v7_: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
        let v0_0: crate::lib::intvector_intrinsics::vec256 = v0_;
        let v1_0: crate::lib::intvector_intrinsics::vec256 = v1_;
        let v2_0: crate::lib::intvector_intrinsics::vec256 = v2_;
        let v3_0: crate::lib::intvector_intrinsics::vec256 = v3_;
        let v4_0: crate::lib::intvector_intrinsics::vec256 = v4_;
        let v5_0: crate::lib::intvector_intrinsics::vec256 = v5_;
        let v6_0: crate::lib::intvector_intrinsics::vec256 = v6_;
        let v7_0: crate::lib::intvector_intrinsics::vec256 = v7_;
        let v0_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_0, v2_0);
        let v2_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_0, v2_0);
        let v1_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_0, v3_0);
        let v3_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_0, v3_0);
        let v4_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_0, v6_0);
        let v6_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_0, v6_0);
        let v5_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_0, v7_0);
        let v7_1: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_0, v7_0);
        let v0_10: crate::lib::intvector_intrinsics::vec256 = v0_1;
        let v1_10: crate::lib::intvector_intrinsics::vec256 = v1_1;
        let v2_10: crate::lib::intvector_intrinsics::vec256 = v2_1;
        let v3_10: crate::lib::intvector_intrinsics::vec256 = v3_1;
        let v4_10: crate::lib::intvector_intrinsics::vec256 = v4_1;
        let v5_10: crate::lib::intvector_intrinsics::vec256 = v5_1;
        let v6_10: crate::lib::intvector_intrinsics::vec256 = v6_1;
        let v7_10: crate::lib::intvector_intrinsics::vec256 = v7_1;
        let v0_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_10, v4_10);
        let v4_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_10, v4_10);
        let v1_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_10, v5_10);
        let v5_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_10, v5_10);
        let v2_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_10, v6_10);
        let v6_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_10, v6_10);
        let v3_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_10, v7_10);
        let v7_2: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_10, v7_10);
        let v0_20: crate::lib::intvector_intrinsics::vec256 = v0_2;
        let v1_20: crate::lib::intvector_intrinsics::vec256 = v1_2;
        let v2_20: crate::lib::intvector_intrinsics::vec256 = v2_2;
        let v3_20: crate::lib::intvector_intrinsics::vec256 = v3_2;
        let v4_20: crate::lib::intvector_intrinsics::vec256 = v4_2;
        let v5_20: crate::lib::intvector_intrinsics::vec256 = v5_2;
        let v6_20: crate::lib::intvector_intrinsics::vec256 = v6_2;
        let v7_20: crate::lib::intvector_intrinsics::vec256 = v7_2;
        let v0_3: crate::lib::intvector_intrinsics::vec256 = v0_20;
        let v1_3: crate::lib::intvector_intrinsics::vec256 = v1_20;
        let v2_3: crate::lib::intvector_intrinsics::vec256 = v2_20;
        let v3_3: crate::lib::intvector_intrinsics::vec256 = v3_20;
        let v4_3: crate::lib::intvector_intrinsics::vec256 = v4_20;
        let v5_3: crate::lib::intvector_intrinsics::vec256 = v5_20;
        let v6_3: crate::lib::intvector_intrinsics::vec256 = v6_20;
        let v7_3: crate::lib::intvector_intrinsics::vec256 = v7_20;
        let v00: crate::lib::intvector_intrinsics::vec256 = v0_3;
        let v10: crate::lib::intvector_intrinsics::vec256 = v2_3;
        let v20: crate::lib::intvector_intrinsics::vec256 = v1_3;
        let v30: crate::lib::intvector_intrinsics::vec256 = v3_3;
        let v40: crate::lib::intvector_intrinsics::vec256 = v4_3;
        let v50: crate::lib::intvector_intrinsics::vec256 = v6_3;
        let v60: crate::lib::intvector_intrinsics::vec256 = v5_3;
        let v70: crate::lib::intvector_intrinsics::vec256 = v7_3;
        let v01: crate::lib::intvector_intrinsics::vec256 = st8;
        let v11: crate::lib::intvector_intrinsics::vec256 = st9;
        let v21: crate::lib::intvector_intrinsics::vec256 = st10;
        let v31: crate::lib::intvector_intrinsics::vec256 = st11;
        let v41: crate::lib::intvector_intrinsics::vec256 = st12;
        let v51: crate::lib::intvector_intrinsics::vec256 = st13;
        let v61: crate::lib::intvector_intrinsics::vec256 = st14;
        let v71: crate::lib::intvector_intrinsics::vec256 = st15;
        let v0_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v01, v11);
        let v1_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v01, v11);
        let v2_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v21, v31);
        let v3_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v21, v31);
        let v4_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v41, v51);
        let v5_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v41, v51);
        let v6_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low32(v61, v71);
        let v7_4: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high32(v61, v71);
        let v0_5: crate::lib::intvector_intrinsics::vec256 = v0_4;
        let v1_5: crate::lib::intvector_intrinsics::vec256 = v1_4;
        let v2_5: crate::lib::intvector_intrinsics::vec256 = v2_4;
        let v3_5: crate::lib::intvector_intrinsics::vec256 = v3_4;
        let v4_5: crate::lib::intvector_intrinsics::vec256 = v4_4;
        let v5_5: crate::lib::intvector_intrinsics::vec256 = v5_4;
        let v6_5: crate::lib::intvector_intrinsics::vec256 = v6_4;
        let v7_5: crate::lib::intvector_intrinsics::vec256 = v7_4;
        let v0_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v0_5, v2_5);
        let v2_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v0_5, v2_5);
        let v1_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v1_5, v3_5);
        let v3_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v1_5, v3_5);
        let v4_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v4_5, v6_5);
        let v6_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v4_5, v6_5);
        let v5_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low64(v5_5, v7_5);
        let v7_11: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high64(v5_5, v7_5);
        let v0_12: crate::lib::intvector_intrinsics::vec256 = v0_11;
        let v1_12: crate::lib::intvector_intrinsics::vec256 = v1_11;
        let v2_12: crate::lib::intvector_intrinsics::vec256 = v2_11;
        let v3_12: crate::lib::intvector_intrinsics::vec256 = v3_11;
        let v4_12: crate::lib::intvector_intrinsics::vec256 = v4_11;
        let v5_12: crate::lib::intvector_intrinsics::vec256 = v5_11;
        let v6_12: crate::lib::intvector_intrinsics::vec256 = v6_11;
        let v7_12: crate::lib::intvector_intrinsics::vec256 = v7_11;
        let v0_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v0_12, v4_12);
        let v4_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v0_12, v4_12);
        let v1_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v1_12, v5_12);
        let v5_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v1_12, v5_12);
        let v2_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v2_12, v6_12);
        let v6_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v2_12, v6_12);
        let v3_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_low128(v3_12, v7_12);
        let v7_21: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_interleave_high128(v3_12, v7_12);
        let v0_22: crate::lib::intvector_intrinsics::vec256 = v0_21;
        let v1_22: crate::lib::intvector_intrinsics::vec256 = v1_21;
        let v2_22: crate::lib::intvector_intrinsics::vec256 = v2_21;
        let v3_22: crate::lib::intvector_intrinsics::vec256 = v3_21;
        let v4_22: crate::lib::intvector_intrinsics::vec256 = v4_21;
        let v5_22: crate::lib::intvector_intrinsics::vec256 = v5_21;
        let v6_22: crate::lib::intvector_intrinsics::vec256 = v6_21;
        let v7_22: crate::lib::intvector_intrinsics::vec256 = v7_21;
        let v0_6: crate::lib::intvector_intrinsics::vec256 = v0_22;
        let v1_6: crate::lib::intvector_intrinsics::vec256 = v1_22;
        let v2_6: crate::lib::intvector_intrinsics::vec256 = v2_22;
        let v3_6: crate::lib::intvector_intrinsics::vec256 = v3_22;
        let v4_6: crate::lib::intvector_intrinsics::vec256 = v4_22;
        let v5_6: crate::lib::intvector_intrinsics::vec256 = v5_22;
        let v6_6: crate::lib::intvector_intrinsics::vec256 = v6_22;
        let v7_6: crate::lib::intvector_intrinsics::vec256 = v7_22;
        let v8: crate::lib::intvector_intrinsics::vec256 = v0_6;
        let v9: crate::lib::intvector_intrinsics::vec256 = v2_6;
        let v100: crate::lib::intvector_intrinsics::vec256 = v1_6;
        let v110: crate::lib::intvector_intrinsics::vec256 = v3_6;
        let v12: crate::lib::intvector_intrinsics::vec256 = v4_6;
        let v13: crate::lib::intvector_intrinsics::vec256 = v6_6;
        let v14: crate::lib::intvector_intrinsics::vec256 = v5_6;
        let v15: crate::lib::intvector_intrinsics::vec256 = v7_6;
        (&mut k)[0usize] = v00;
        (&mut k)[1usize] = v8;
        (&mut k)[2usize] = v10;
        (&mut k)[3usize] = v9;
        (&mut k)[4usize] = v20;
        (&mut k)[5usize] = v100;
        (&mut k)[6usize] = v30;
        (&mut k)[7usize] = v110;
        (&mut k)[8usize] = v40;
        (&mut k)[9usize] = v12;
        (&mut k)[10usize] = v50;
        (&mut k)[11usize] = v13;
        (&mut k)[12usize] = v60;
        (&mut k)[13usize] = v14;
        (&mut k)[14usize] = v70;
        (&mut k)[15usize] = v15;
        for i in 0u32..16u32
        {
            let x: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load32_le(
                    &mut (&mut plain)[i.wrapping_mul(32u32) as usize..]
                );
            let y: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_xor(x, (&mut k)[i as usize]);
            crate::lib::intvector_intrinsics::vec256_store32_le(
                &mut (&mut plain)[i.wrapping_mul(32u32) as usize..],
                y
            )
        };
        (uu____2.1[0usize..0usize + rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0usize..])[0usize..0usize + rem as usize]
        )
    }
}
