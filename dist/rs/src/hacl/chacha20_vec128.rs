fn double_round_128(st: &mut [crate::lib::intvector::intrinsics::vec128]) -> ()
{
    st[0u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[0u32 as usize], st[4u32 as usize]);
    let std: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[12u32 as usize], st[0u32 as usize]);
    st[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std, 16u32);
    st[8u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[8u32 as usize], st[12u32 as usize]);
    let std0: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[4u32 as usize], st[8u32 as usize]);
    st[4u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std0, 12u32);
    st[0u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[0u32 as usize], st[4u32 as usize]);
    let std1: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[12u32 as usize], st[0u32 as usize]);
    st[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std1, 8u32);
    st[8u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[8u32 as usize], st[12u32 as usize]);
    let std2: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[4u32 as usize], st[8u32 as usize]);
    st[4u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std2, 7u32);
    st[1u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[1u32 as usize], st[5u32 as usize]);
    let std3: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[13u32 as usize], st[1u32 as usize]);
    st[13u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std3, 16u32);
    st[9u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[9u32 as usize], st[13u32 as usize]);
    let std4: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[5u32 as usize], st[9u32 as usize]);
    st[5u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std4, 12u32);
    st[1u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[1u32 as usize], st[5u32 as usize]);
    let std5: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[13u32 as usize], st[1u32 as usize]);
    st[13u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std5, 8u32);
    st[9u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[9u32 as usize], st[13u32 as usize]);
    let std6: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[5u32 as usize], st[9u32 as usize]);
    st[5u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std6, 7u32);
    st[2u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[2u32 as usize], st[6u32 as usize]);
    let std7: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[14u32 as usize], st[2u32 as usize]);
    st[14u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std7, 16u32);
    st[10u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[10u32 as usize], st[14u32 as usize]);
    let std8: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[6u32 as usize], st[10u32 as usize]);
    st[6u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std8, 12u32);
    st[2u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[2u32 as usize], st[6u32 as usize]);
    let std9: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[14u32 as usize], st[2u32 as usize]);
    st[14u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std9, 8u32);
    st[10u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[10u32 as usize], st[14u32 as usize]);
    let std10: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[6u32 as usize], st[10u32 as usize]);
    st[6u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std10, 7u32);
    st[3u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[3u32 as usize], st[7u32 as usize]);
    let std11: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[15u32 as usize], st[3u32 as usize]);
    st[15u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std11, 16u32);
    st[11u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[11u32 as usize], st[15u32 as usize]);
    let std12: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[7u32 as usize], st[11u32 as usize]);
    st[7u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std12, 12u32);
    st[3u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[3u32 as usize], st[7u32 as usize]);
    let std13: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[15u32 as usize], st[3u32 as usize]);
    st[15u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std13, 8u32);
    st[11u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[11u32 as usize], st[15u32 as usize]);
    let std14: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[7u32 as usize], st[11u32 as usize]);
    st[7u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std14, 7u32);
    st[0u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[0u32 as usize], st[5u32 as usize]);
    let std15: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[15u32 as usize], st[0u32 as usize]);
    st[15u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std15, 16u32);
    st[10u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[10u32 as usize], st[15u32 as usize]);
    let std16: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[5u32 as usize], st[10u32 as usize]);
    st[5u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std16, 12u32);
    st[0u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[0u32 as usize], st[5u32 as usize]);
    let std17: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[15u32 as usize], st[0u32 as usize]);
    st[15u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std17, 8u32);
    st[10u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[10u32 as usize], st[15u32 as usize]);
    let std18: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[5u32 as usize], st[10u32 as usize]);
    st[5u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std18, 7u32);
    st[1u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[1u32 as usize], st[6u32 as usize]);
    let std19: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[12u32 as usize], st[1u32 as usize]);
    st[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std19, 16u32);
    st[11u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[11u32 as usize], st[12u32 as usize]);
    let std20: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[6u32 as usize], st[11u32 as usize]);
    st[6u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std20, 12u32);
    st[1u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[1u32 as usize], st[6u32 as usize]);
    let std21: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[12u32 as usize], st[1u32 as usize]);
    st[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std21, 8u32);
    st[11u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[11u32 as usize], st[12u32 as usize]);
    let std22: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[6u32 as usize], st[11u32 as usize]);
    st[6u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std22, 7u32);
    st[2u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[2u32 as usize], st[7u32 as usize]);
    let std23: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[13u32 as usize], st[2u32 as usize]);
    st[13u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std23, 16u32);
    st[8u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[8u32 as usize], st[13u32 as usize]);
    let std24: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[7u32 as usize], st[8u32 as usize]);
    st[7u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std24, 12u32);
    st[2u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[2u32 as usize], st[7u32 as usize]);
    let std25: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[13u32 as usize], st[2u32 as usize]);
    st[13u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std25, 8u32);
    st[8u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[8u32 as usize], st[13u32 as usize]);
    let std26: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[7u32 as usize], st[8u32 as usize]);
    st[7u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std26, 7u32);
    st[3u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[3u32 as usize], st[4u32 as usize]);
    let std27: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[14u32 as usize], st[3u32 as usize]);
    st[14u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std27, 16u32);
    st[9u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[9u32 as usize], st[14u32 as usize]);
    let std28: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[4u32 as usize], st[9u32 as usize]);
    st[4u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std28, 12u32);
    st[3u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[3u32 as usize], st[4u32 as usize]);
    let std29: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[14u32 as usize], st[3u32 as usize]);
    st[14u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std29, 8u32);
    st[9u32 as usize] =
        crate::lib::intvector::intrinsics::vec128_add32(st[9u32 as usize], st[14u32 as usize]);
    let std30: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_xor(st[4u32 as usize], st[9u32 as usize]);
    st[4u32 as usize] = crate::lib::intvector::intrinsics::vec128_rotate_left32(std30, 7u32)
}

fn chacha20_core_128(
    k: &mut [crate::lib::intvector::intrinsics::vec128],
    ctx: &mut [crate::lib::intvector::intrinsics::vec128],
    ctr: u32
) ->
    ()
{
    (k[0u32 as usize..0u32 as usize + 16u32 as usize]).copy_from_slice(
        &ctx[0u32 as usize..0u32 as usize + 16u32 as usize]
    );
    let ctr_u32: u32 = 4u32.wrapping_mul(ctr);
    let cv: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_load32(ctr_u32);
    k[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_add32(k[12u32 as usize], cv);
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
        (&mut [crate::lib::intvector::intrinsics::vec128],
        &mut [crate::lib::intvector::intrinsics::vec128])
        =
            k.split_at_mut(0usize);
        let x: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_add32(os.1[i as usize], ctx[i as usize]);
        os.1[i as usize] = x
    };
    k[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_add32(k[12u32 as usize], cv)
}

fn chacha20_init_128(
    ctx: &mut [crate::lib::intvector::intrinsics::vec128],
    k: &mut [u8],
    n: &mut [u8],
    ctr: u32
) ->
    ()
{
    let mut ctx1: [u32; 16] = [0u32; 16u32 as usize];
    for i in 0u32..4u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[0u32 as usize..])[0u32 as usize..];
        let x: u32 = (&crate::hacl::chacha20::chacha20_constants)[i as usize];
        os[i as usize] = x
    };
    for i in 0u32..8u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[4u32 as usize..])[0u32 as usize..];
        let bj: (&mut [u8], &mut [u8]) =
            k.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os[i as usize] = x
    };
    (&mut ctx1)[12u32 as usize] = ctr;
    for i in 0u32..3u32
    {
        let os: &mut [u32] = &mut (&mut (&mut ctx1)[13u32 as usize..])[0u32 as usize..];
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
        (&mut [crate::lib::intvector::intrinsics::vec128],
        &mut [crate::lib::intvector::intrinsics::vec128])
        =
            ctx.split_at_mut(0usize);
        let x: u32 = (&mut ctx1)[i as usize];
        let x0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_load32(x);
        os.1[i as usize] = x0
    };
    let ctr1: crate::lib::intvector::intrinsics::vec128 =
        crate::lib::intvector::intrinsics::vec128_load32s(0u32, 1u32, 2u32, 3u32);
    let c12: crate::lib::intvector::intrinsics::vec128 = ctx[12u32 as usize];
    ctx[12u32 as usize] = crate::lib::intvector::intrinsics::vec128_add32(c12, ctr1)
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
    let mut ctx: [crate::lib::intvector::intrinsics::vec128; 16] =
        [crate::lib::intvector::intrinsics::vec128_zero; 16u32 as usize];
    chacha20_init_128(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(256u32);
    let nb: u32 = len.wrapping_div(256u32);
    let rem1: u32 = len.wrapping_rem(256u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) =
            out.split_at_mut((i.wrapping_mul(256u32) as usize).wrapping_add(0usize));
        let uu____1: (&mut [u8], &mut [u8]) =
            text.split_at_mut((i.wrapping_mul(256u32) as usize).wrapping_add(0usize));
        let mut k: [crate::lib::intvector::intrinsics::vec128; 16] =
            [crate::lib::intvector::intrinsics::vec128_zero; 16u32 as usize];
        chacha20_core_128(&mut k, &mut ctx, i);
        let st0: crate::lib::intvector::intrinsics::vec128 = (&mut k)[0u32 as usize];
        let st1: crate::lib::intvector::intrinsics::vec128 = (&mut k)[1u32 as usize];
        let st2: crate::lib::intvector::intrinsics::vec128 = (&mut k)[2u32 as usize];
        let st3: crate::lib::intvector::intrinsics::vec128 = (&mut k)[3u32 as usize];
        let st4: crate::lib::intvector::intrinsics::vec128 = (&mut k)[4u32 as usize];
        let st5: crate::lib::intvector::intrinsics::vec128 = (&mut k)[5u32 as usize];
        let st6: crate::lib::intvector::intrinsics::vec128 = (&mut k)[6u32 as usize];
        let st7: crate::lib::intvector::intrinsics::vec128 = (&mut k)[7u32 as usize];
        let st8: crate::lib::intvector::intrinsics::vec128 = (&mut k)[8u32 as usize];
        let st9: crate::lib::intvector::intrinsics::vec128 = (&mut k)[9u32 as usize];
        let st10: crate::lib::intvector::intrinsics::vec128 = (&mut k)[10u32 as usize];
        let st11: crate::lib::intvector::intrinsics::vec128 = (&mut k)[11u32 as usize];
        let st12: crate::lib::intvector::intrinsics::vec128 = (&mut k)[12u32 as usize];
        let st13: crate::lib::intvector::intrinsics::vec128 = (&mut k)[13u32 as usize];
        let st14: crate::lib::intvector::intrinsics::vec128 = (&mut k)[14u32 as usize];
        let st15: crate::lib::intvector::intrinsics::vec128 = (&mut k)[15u32 as usize];
        let v0': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st0, st1);
        let v1': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st0, st1);
        let v2': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st2, st3);
        let v3': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st2, st3);
        let v0'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0', v2');
        let v1'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0', v2');
        let v2'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1', v3');
        let v3'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1', v3');
        let v0''0: crate::lib::intvector::intrinsics::vec128 = v0'';
        let v2''0: crate::lib::intvector::intrinsics::vec128 = v2'';
        let v1''0: crate::lib::intvector::intrinsics::vec128 = v1'';
        let v3''0: crate::lib::intvector::intrinsics::vec128 = v3'';
        let v0: crate::lib::intvector::intrinsics::vec128 = v0''0;
        let v1: crate::lib::intvector::intrinsics::vec128 = v1''0;
        let v2: crate::lib::intvector::intrinsics::vec128 = v2''0;
        let v3: crate::lib::intvector::intrinsics::vec128 = v3''0;
        let v0'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st4, st5);
        let v1'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st4, st5);
        let v2'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st6, st7);
        let v3'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st6, st7);
        let v0''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'0, v2'0);
        let v1''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'0, v2'0);
        let v2''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'0, v3'0);
        let v3''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'0, v3'0);
        let v0''2: crate::lib::intvector::intrinsics::vec128 = v0''1;
        let v2''2: crate::lib::intvector::intrinsics::vec128 = v2''1;
        let v1''2: crate::lib::intvector::intrinsics::vec128 = v1''1;
        let v3''2: crate::lib::intvector::intrinsics::vec128 = v3''1;
        let v4: crate::lib::intvector::intrinsics::vec128 = v0''2;
        let v5: crate::lib::intvector::intrinsics::vec128 = v1''2;
        let v6: crate::lib::intvector::intrinsics::vec128 = v2''2;
        let v7: crate::lib::intvector::intrinsics::vec128 = v3''2;
        let v0'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st8, st9);
        let v1'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st8, st9);
        let v2'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st10, st11);
        let v3'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st10, st11);
        let v0''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'1, v2'1);
        let v1''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'1, v2'1);
        let v2''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'1, v3'1);
        let v3''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'1, v3'1);
        let v0''4: crate::lib::intvector::intrinsics::vec128 = v0''3;
        let v2''4: crate::lib::intvector::intrinsics::vec128 = v2''3;
        let v1''4: crate::lib::intvector::intrinsics::vec128 = v1''3;
        let v3''4: crate::lib::intvector::intrinsics::vec128 = v3''3;
        let v8: crate::lib::intvector::intrinsics::vec128 = v0''4;
        let v9: crate::lib::intvector::intrinsics::vec128 = v1''4;
        let v10: crate::lib::intvector::intrinsics::vec128 = v2''4;
        let v11: crate::lib::intvector::intrinsics::vec128 = v3''4;
        let v0'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st12, st13);
        let v1'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st12, st13);
        let v2'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st14, st15);
        let v3'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st14, st15);
        let v0''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'2, v2'2);
        let v1''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'2, v2'2);
        let v2''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'2, v3'2);
        let v3''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'2, v3'2);
        let v0''6: crate::lib::intvector::intrinsics::vec128 = v0''5;
        let v2''6: crate::lib::intvector::intrinsics::vec128 = v2''5;
        let v1''6: crate::lib::intvector::intrinsics::vec128 = v1''5;
        let v3''6: crate::lib::intvector::intrinsics::vec128 = v3''5;
        let v12: crate::lib::intvector::intrinsics::vec128 = v0''6;
        let v13: crate::lib::intvector::intrinsics::vec128 = v1''6;
        let v14: crate::lib::intvector::intrinsics::vec128 = v2''6;
        let v15: crate::lib::intvector::intrinsics::vec128 = v3''6;
        (&mut k)[0u32 as usize] = v0;
        (&mut k)[1u32 as usize] = v4;
        (&mut k)[2u32 as usize] = v8;
        (&mut k)[3u32 as usize] = v12;
        (&mut k)[4u32 as usize] = v1;
        (&mut k)[5u32 as usize] = v5;
        (&mut k)[6u32 as usize] = v9;
        (&mut k)[7u32 as usize] = v13;
        (&mut k)[8u32 as usize] = v2;
        (&mut k)[9u32 as usize] = v6;
        (&mut k)[10u32 as usize] = v10;
        (&mut k)[11u32 as usize] = v14;
        (&mut k)[12u32 as usize] = v3;
        (&mut k)[13u32 as usize] = v7;
        (&mut k)[14u32 as usize] = v11;
        (&mut k)[15u32 as usize] = v15;
        for i0 in 0u32..16u32
        {
            let x: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_load32_le(
                    &mut uu____1.1[i0.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_xor(x, (&mut k)[i0 as usize]);
            crate::lib::intvector::intrinsics::vec128_store32_le(
                &mut uu____0.1[i0.wrapping_mul(16u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) =
            out.split_at_mut((nb.wrapping_mul(256u32) as usize).wrapping_add(0usize));
        let mut plain: [u8; 256] = [0u8; 256u32 as usize];
        ((&mut plain)[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
            &(&mut text[nb.wrapping_mul(256u32) as usize..])[0u32 as usize..0u32 as usize
            +
            rem as usize]
        );
        let mut k: [crate::lib::intvector::intrinsics::vec128; 16] =
            [crate::lib::intvector::intrinsics::vec128_zero; 16u32 as usize];
        chacha20_core_128(&mut k, &mut ctx, nb);
        let st0: crate::lib::intvector::intrinsics::vec128 = (&mut k)[0u32 as usize];
        let st1: crate::lib::intvector::intrinsics::vec128 = (&mut k)[1u32 as usize];
        let st2: crate::lib::intvector::intrinsics::vec128 = (&mut k)[2u32 as usize];
        let st3: crate::lib::intvector::intrinsics::vec128 = (&mut k)[3u32 as usize];
        let st4: crate::lib::intvector::intrinsics::vec128 = (&mut k)[4u32 as usize];
        let st5: crate::lib::intvector::intrinsics::vec128 = (&mut k)[5u32 as usize];
        let st6: crate::lib::intvector::intrinsics::vec128 = (&mut k)[6u32 as usize];
        let st7: crate::lib::intvector::intrinsics::vec128 = (&mut k)[7u32 as usize];
        let st8: crate::lib::intvector::intrinsics::vec128 = (&mut k)[8u32 as usize];
        let st9: crate::lib::intvector::intrinsics::vec128 = (&mut k)[9u32 as usize];
        let st10: crate::lib::intvector::intrinsics::vec128 = (&mut k)[10u32 as usize];
        let st11: crate::lib::intvector::intrinsics::vec128 = (&mut k)[11u32 as usize];
        let st12: crate::lib::intvector::intrinsics::vec128 = (&mut k)[12u32 as usize];
        let st13: crate::lib::intvector::intrinsics::vec128 = (&mut k)[13u32 as usize];
        let st14: crate::lib::intvector::intrinsics::vec128 = (&mut k)[14u32 as usize];
        let st15: crate::lib::intvector::intrinsics::vec128 = (&mut k)[15u32 as usize];
        let v0': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st0, st1);
        let v1': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st0, st1);
        let v2': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st2, st3);
        let v3': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st2, st3);
        let v0'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0', v2');
        let v1'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0', v2');
        let v2'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1', v3');
        let v3'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1', v3');
        let v0''0: crate::lib::intvector::intrinsics::vec128 = v0'';
        let v2''0: crate::lib::intvector::intrinsics::vec128 = v2'';
        let v1''0: crate::lib::intvector::intrinsics::vec128 = v1'';
        let v3''0: crate::lib::intvector::intrinsics::vec128 = v3'';
        let v0: crate::lib::intvector::intrinsics::vec128 = v0''0;
        let v1: crate::lib::intvector::intrinsics::vec128 = v1''0;
        let v2: crate::lib::intvector::intrinsics::vec128 = v2''0;
        let v3: crate::lib::intvector::intrinsics::vec128 = v3''0;
        let v0'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st4, st5);
        let v1'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st4, st5);
        let v2'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st6, st7);
        let v3'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st6, st7);
        let v0''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'0, v2'0);
        let v1''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'0, v2'0);
        let v2''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'0, v3'0);
        let v3''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'0, v3'0);
        let v0''2: crate::lib::intvector::intrinsics::vec128 = v0''1;
        let v2''2: crate::lib::intvector::intrinsics::vec128 = v2''1;
        let v1''2: crate::lib::intvector::intrinsics::vec128 = v1''1;
        let v3''2: crate::lib::intvector::intrinsics::vec128 = v3''1;
        let v4: crate::lib::intvector::intrinsics::vec128 = v0''2;
        let v5: crate::lib::intvector::intrinsics::vec128 = v1''2;
        let v6: crate::lib::intvector::intrinsics::vec128 = v2''2;
        let v7: crate::lib::intvector::intrinsics::vec128 = v3''2;
        let v0'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st8, st9);
        let v1'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st8, st9);
        let v2'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st10, st11);
        let v3'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st10, st11);
        let v0''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'1, v2'1);
        let v1''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'1, v2'1);
        let v2''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'1, v3'1);
        let v3''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'1, v3'1);
        let v0''4: crate::lib::intvector::intrinsics::vec128 = v0''3;
        let v2''4: crate::lib::intvector::intrinsics::vec128 = v2''3;
        let v1''4: crate::lib::intvector::intrinsics::vec128 = v1''3;
        let v3''4: crate::lib::intvector::intrinsics::vec128 = v3''3;
        let v8: crate::lib::intvector::intrinsics::vec128 = v0''4;
        let v9: crate::lib::intvector::intrinsics::vec128 = v1''4;
        let v10: crate::lib::intvector::intrinsics::vec128 = v2''4;
        let v11: crate::lib::intvector::intrinsics::vec128 = v3''4;
        let v0'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st12, st13);
        let v1'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st12, st13);
        let v2'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st14, st15);
        let v3'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st14, st15);
        let v0''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'2, v2'2);
        let v1''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'2, v2'2);
        let v2''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'2, v3'2);
        let v3''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'2, v3'2);
        let v0''6: crate::lib::intvector::intrinsics::vec128 = v0''5;
        let v2''6: crate::lib::intvector::intrinsics::vec128 = v2''5;
        let v1''6: crate::lib::intvector::intrinsics::vec128 = v1''5;
        let v3''6: crate::lib::intvector::intrinsics::vec128 = v3''5;
        let v12: crate::lib::intvector::intrinsics::vec128 = v0''6;
        let v13: crate::lib::intvector::intrinsics::vec128 = v1''6;
        let v14: crate::lib::intvector::intrinsics::vec128 = v2''6;
        let v15: crate::lib::intvector::intrinsics::vec128 = v3''6;
        (&mut k)[0u32 as usize] = v0;
        (&mut k)[1u32 as usize] = v4;
        (&mut k)[2u32 as usize] = v8;
        (&mut k)[3u32 as usize] = v12;
        (&mut k)[4u32 as usize] = v1;
        (&mut k)[5u32 as usize] = v5;
        (&mut k)[6u32 as usize] = v9;
        (&mut k)[7u32 as usize] = v13;
        (&mut k)[8u32 as usize] = v2;
        (&mut k)[9u32 as usize] = v6;
        (&mut k)[10u32 as usize] = v10;
        (&mut k)[11u32 as usize] = v14;
        (&mut k)[12u32 as usize] = v3;
        (&mut k)[13u32 as usize] = v7;
        (&mut k)[14u32 as usize] = v11;
        (&mut k)[15u32 as usize] = v15;
        for i in 0u32..16u32
        {
            let x: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_load32_le(
                    &mut (&mut plain)[i.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_xor(x, (&mut k)[i as usize]);
            crate::lib::intvector::intrinsics::vec128_store32_le(
                &mut (&mut plain)[i.wrapping_mul(16u32) as usize..],
                y
            )
        };
        (uu____2.1[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + rem as usize]
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
    let mut ctx: [crate::lib::intvector::intrinsics::vec128; 16] =
        [crate::lib::intvector::intrinsics::vec128_zero; 16u32 as usize];
    chacha20_init_128(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(256u32);
    let nb: u32 = len.wrapping_div(256u32);
    let rem1: u32 = len.wrapping_rem(256u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) =
            out.split_at_mut((i.wrapping_mul(256u32) as usize).wrapping_add(0usize));
        let uu____1: (&mut [u8], &mut [u8]) =
            cipher.split_at_mut((i.wrapping_mul(256u32) as usize).wrapping_add(0usize));
        let mut k: [crate::lib::intvector::intrinsics::vec128; 16] =
            [crate::lib::intvector::intrinsics::vec128_zero; 16u32 as usize];
        chacha20_core_128(&mut k, &mut ctx, i);
        let st0: crate::lib::intvector::intrinsics::vec128 = (&mut k)[0u32 as usize];
        let st1: crate::lib::intvector::intrinsics::vec128 = (&mut k)[1u32 as usize];
        let st2: crate::lib::intvector::intrinsics::vec128 = (&mut k)[2u32 as usize];
        let st3: crate::lib::intvector::intrinsics::vec128 = (&mut k)[3u32 as usize];
        let st4: crate::lib::intvector::intrinsics::vec128 = (&mut k)[4u32 as usize];
        let st5: crate::lib::intvector::intrinsics::vec128 = (&mut k)[5u32 as usize];
        let st6: crate::lib::intvector::intrinsics::vec128 = (&mut k)[6u32 as usize];
        let st7: crate::lib::intvector::intrinsics::vec128 = (&mut k)[7u32 as usize];
        let st8: crate::lib::intvector::intrinsics::vec128 = (&mut k)[8u32 as usize];
        let st9: crate::lib::intvector::intrinsics::vec128 = (&mut k)[9u32 as usize];
        let st10: crate::lib::intvector::intrinsics::vec128 = (&mut k)[10u32 as usize];
        let st11: crate::lib::intvector::intrinsics::vec128 = (&mut k)[11u32 as usize];
        let st12: crate::lib::intvector::intrinsics::vec128 = (&mut k)[12u32 as usize];
        let st13: crate::lib::intvector::intrinsics::vec128 = (&mut k)[13u32 as usize];
        let st14: crate::lib::intvector::intrinsics::vec128 = (&mut k)[14u32 as usize];
        let st15: crate::lib::intvector::intrinsics::vec128 = (&mut k)[15u32 as usize];
        let v0': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st0, st1);
        let v1': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st0, st1);
        let v2': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st2, st3);
        let v3': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st2, st3);
        let v0'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0', v2');
        let v1'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0', v2');
        let v2'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1', v3');
        let v3'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1', v3');
        let v0''0: crate::lib::intvector::intrinsics::vec128 = v0'';
        let v2''0: crate::lib::intvector::intrinsics::vec128 = v2'';
        let v1''0: crate::lib::intvector::intrinsics::vec128 = v1'';
        let v3''0: crate::lib::intvector::intrinsics::vec128 = v3'';
        let v0: crate::lib::intvector::intrinsics::vec128 = v0''0;
        let v1: crate::lib::intvector::intrinsics::vec128 = v1''0;
        let v2: crate::lib::intvector::intrinsics::vec128 = v2''0;
        let v3: crate::lib::intvector::intrinsics::vec128 = v3''0;
        let v0'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st4, st5);
        let v1'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st4, st5);
        let v2'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st6, st7);
        let v3'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st6, st7);
        let v0''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'0, v2'0);
        let v1''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'0, v2'0);
        let v2''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'0, v3'0);
        let v3''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'0, v3'0);
        let v0''2: crate::lib::intvector::intrinsics::vec128 = v0''1;
        let v2''2: crate::lib::intvector::intrinsics::vec128 = v2''1;
        let v1''2: crate::lib::intvector::intrinsics::vec128 = v1''1;
        let v3''2: crate::lib::intvector::intrinsics::vec128 = v3''1;
        let v4: crate::lib::intvector::intrinsics::vec128 = v0''2;
        let v5: crate::lib::intvector::intrinsics::vec128 = v1''2;
        let v6: crate::lib::intvector::intrinsics::vec128 = v2''2;
        let v7: crate::lib::intvector::intrinsics::vec128 = v3''2;
        let v0'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st8, st9);
        let v1'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st8, st9);
        let v2'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st10, st11);
        let v3'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st10, st11);
        let v0''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'1, v2'1);
        let v1''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'1, v2'1);
        let v2''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'1, v3'1);
        let v3''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'1, v3'1);
        let v0''4: crate::lib::intvector::intrinsics::vec128 = v0''3;
        let v2''4: crate::lib::intvector::intrinsics::vec128 = v2''3;
        let v1''4: crate::lib::intvector::intrinsics::vec128 = v1''3;
        let v3''4: crate::lib::intvector::intrinsics::vec128 = v3''3;
        let v8: crate::lib::intvector::intrinsics::vec128 = v0''4;
        let v9: crate::lib::intvector::intrinsics::vec128 = v1''4;
        let v10: crate::lib::intvector::intrinsics::vec128 = v2''4;
        let v11: crate::lib::intvector::intrinsics::vec128 = v3''4;
        let v0'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st12, st13);
        let v1'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st12, st13);
        let v2'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st14, st15);
        let v3'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st14, st15);
        let v0''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'2, v2'2);
        let v1''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'2, v2'2);
        let v2''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'2, v3'2);
        let v3''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'2, v3'2);
        let v0''6: crate::lib::intvector::intrinsics::vec128 = v0''5;
        let v2''6: crate::lib::intvector::intrinsics::vec128 = v2''5;
        let v1''6: crate::lib::intvector::intrinsics::vec128 = v1''5;
        let v3''6: crate::lib::intvector::intrinsics::vec128 = v3''5;
        let v12: crate::lib::intvector::intrinsics::vec128 = v0''6;
        let v13: crate::lib::intvector::intrinsics::vec128 = v1''6;
        let v14: crate::lib::intvector::intrinsics::vec128 = v2''6;
        let v15: crate::lib::intvector::intrinsics::vec128 = v3''6;
        (&mut k)[0u32 as usize] = v0;
        (&mut k)[1u32 as usize] = v4;
        (&mut k)[2u32 as usize] = v8;
        (&mut k)[3u32 as usize] = v12;
        (&mut k)[4u32 as usize] = v1;
        (&mut k)[5u32 as usize] = v5;
        (&mut k)[6u32 as usize] = v9;
        (&mut k)[7u32 as usize] = v13;
        (&mut k)[8u32 as usize] = v2;
        (&mut k)[9u32 as usize] = v6;
        (&mut k)[10u32 as usize] = v10;
        (&mut k)[11u32 as usize] = v14;
        (&mut k)[12u32 as usize] = v3;
        (&mut k)[13u32 as usize] = v7;
        (&mut k)[14u32 as usize] = v11;
        (&mut k)[15u32 as usize] = v15;
        for i0 in 0u32..16u32
        {
            let x: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_load32_le(
                    &mut uu____1.1[i0.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_xor(x, (&mut k)[i0 as usize]);
            crate::lib::intvector::intrinsics::vec128_store32_le(
                &mut uu____0.1[i0.wrapping_mul(16u32) as usize..],
                y
            )
        }
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) =
            out.split_at_mut((nb.wrapping_mul(256u32) as usize).wrapping_add(0usize));
        let mut plain: [u8; 256] = [0u8; 256u32 as usize];
        ((&mut plain)[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
            &(&mut cipher[nb.wrapping_mul(256u32) as usize..])[0u32 as usize..0u32 as usize
            +
            rem as usize]
        );
        let mut k: [crate::lib::intvector::intrinsics::vec128; 16] =
            [crate::lib::intvector::intrinsics::vec128_zero; 16u32 as usize];
        chacha20_core_128(&mut k, &mut ctx, nb);
        let st0: crate::lib::intvector::intrinsics::vec128 = (&mut k)[0u32 as usize];
        let st1: crate::lib::intvector::intrinsics::vec128 = (&mut k)[1u32 as usize];
        let st2: crate::lib::intvector::intrinsics::vec128 = (&mut k)[2u32 as usize];
        let st3: crate::lib::intvector::intrinsics::vec128 = (&mut k)[3u32 as usize];
        let st4: crate::lib::intvector::intrinsics::vec128 = (&mut k)[4u32 as usize];
        let st5: crate::lib::intvector::intrinsics::vec128 = (&mut k)[5u32 as usize];
        let st6: crate::lib::intvector::intrinsics::vec128 = (&mut k)[6u32 as usize];
        let st7: crate::lib::intvector::intrinsics::vec128 = (&mut k)[7u32 as usize];
        let st8: crate::lib::intvector::intrinsics::vec128 = (&mut k)[8u32 as usize];
        let st9: crate::lib::intvector::intrinsics::vec128 = (&mut k)[9u32 as usize];
        let st10: crate::lib::intvector::intrinsics::vec128 = (&mut k)[10u32 as usize];
        let st11: crate::lib::intvector::intrinsics::vec128 = (&mut k)[11u32 as usize];
        let st12: crate::lib::intvector::intrinsics::vec128 = (&mut k)[12u32 as usize];
        let st13: crate::lib::intvector::intrinsics::vec128 = (&mut k)[13u32 as usize];
        let st14: crate::lib::intvector::intrinsics::vec128 = (&mut k)[14u32 as usize];
        let st15: crate::lib::intvector::intrinsics::vec128 = (&mut k)[15u32 as usize];
        let v0': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st0, st1);
        let v1': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st0, st1);
        let v2': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st2, st3);
        let v3': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st2, st3);
        let v0'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0', v2');
        let v1'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0', v2');
        let v2'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1', v3');
        let v3'': crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1', v3');
        let v0''0: crate::lib::intvector::intrinsics::vec128 = v0'';
        let v2''0: crate::lib::intvector::intrinsics::vec128 = v2'';
        let v1''0: crate::lib::intvector::intrinsics::vec128 = v1'';
        let v3''0: crate::lib::intvector::intrinsics::vec128 = v3'';
        let v0: crate::lib::intvector::intrinsics::vec128 = v0''0;
        let v1: crate::lib::intvector::intrinsics::vec128 = v1''0;
        let v2: crate::lib::intvector::intrinsics::vec128 = v2''0;
        let v3: crate::lib::intvector::intrinsics::vec128 = v3''0;
        let v0'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st4, st5);
        let v1'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st4, st5);
        let v2'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st6, st7);
        let v3'0: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st6, st7);
        let v0''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'0, v2'0);
        let v1''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'0, v2'0);
        let v2''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'0, v3'0);
        let v3''1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'0, v3'0);
        let v0''2: crate::lib::intvector::intrinsics::vec128 = v0''1;
        let v2''2: crate::lib::intvector::intrinsics::vec128 = v2''1;
        let v1''2: crate::lib::intvector::intrinsics::vec128 = v1''1;
        let v3''2: crate::lib::intvector::intrinsics::vec128 = v3''1;
        let v4: crate::lib::intvector::intrinsics::vec128 = v0''2;
        let v5: crate::lib::intvector::intrinsics::vec128 = v1''2;
        let v6: crate::lib::intvector::intrinsics::vec128 = v2''2;
        let v7: crate::lib::intvector::intrinsics::vec128 = v3''2;
        let v0'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st8, st9);
        let v1'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st8, st9);
        let v2'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st10, st11);
        let v3'1: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st10, st11);
        let v0''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'1, v2'1);
        let v1''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'1, v2'1);
        let v2''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'1, v3'1);
        let v3''3: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'1, v3'1);
        let v0''4: crate::lib::intvector::intrinsics::vec128 = v0''3;
        let v2''4: crate::lib::intvector::intrinsics::vec128 = v2''3;
        let v1''4: crate::lib::intvector::intrinsics::vec128 = v1''3;
        let v3''4: crate::lib::intvector::intrinsics::vec128 = v3''3;
        let v8: crate::lib::intvector::intrinsics::vec128 = v0''4;
        let v9: crate::lib::intvector::intrinsics::vec128 = v1''4;
        let v10: crate::lib::intvector::intrinsics::vec128 = v2''4;
        let v11: crate::lib::intvector::intrinsics::vec128 = v3''4;
        let v0'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st12, st13);
        let v1'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st12, st13);
        let v2'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low32(st14, st15);
        let v3'2: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high32(st14, st15);
        let v0''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v0'2, v2'2);
        let v1''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v0'2, v2'2);
        let v2''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_low64(v1'2, v3'2);
        let v3''5: crate::lib::intvector::intrinsics::vec128 =
            crate::lib::intvector::intrinsics::vec128_interleave_high64(v1'2, v3'2);
        let v0''6: crate::lib::intvector::intrinsics::vec128 = v0''5;
        let v2''6: crate::lib::intvector::intrinsics::vec128 = v2''5;
        let v1''6: crate::lib::intvector::intrinsics::vec128 = v1''5;
        let v3''6: crate::lib::intvector::intrinsics::vec128 = v3''5;
        let v12: crate::lib::intvector::intrinsics::vec128 = v0''6;
        let v13: crate::lib::intvector::intrinsics::vec128 = v1''6;
        let v14: crate::lib::intvector::intrinsics::vec128 = v2''6;
        let v15: crate::lib::intvector::intrinsics::vec128 = v3''6;
        (&mut k)[0u32 as usize] = v0;
        (&mut k)[1u32 as usize] = v4;
        (&mut k)[2u32 as usize] = v8;
        (&mut k)[3u32 as usize] = v12;
        (&mut k)[4u32 as usize] = v1;
        (&mut k)[5u32 as usize] = v5;
        (&mut k)[6u32 as usize] = v9;
        (&mut k)[7u32 as usize] = v13;
        (&mut k)[8u32 as usize] = v2;
        (&mut k)[9u32 as usize] = v6;
        (&mut k)[10u32 as usize] = v10;
        (&mut k)[11u32 as usize] = v14;
        (&mut k)[12u32 as usize] = v3;
        (&mut k)[13u32 as usize] = v7;
        (&mut k)[14u32 as usize] = v11;
        (&mut k)[15u32 as usize] = v15;
        for i in 0u32..16u32
        {
            let x: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_load32_le(
                    &mut (&mut plain)[i.wrapping_mul(16u32) as usize..]
                );
            let y: crate::lib::intvector::intrinsics::vec128 =
                crate::lib::intvector::intrinsics::vec128_xor(x, (&mut k)[i as usize]);
            crate::lib::intvector::intrinsics::vec128_store32_le(
                &mut (&mut plain)[i.wrapping_mul(16u32) as usize..],
                y
            )
        };
        (uu____2.1[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
            &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + rem as usize]
        )
    }
}