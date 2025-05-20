#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn double_round_128(st: &mut [lib::intvector_intrinsics::vec128])
{
    st[0usize] = lib::intvector_intrinsics::vec128_add32(st[0usize], st[4usize]);
    let std: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[12usize], st[0usize]);
    st[12usize] = lib::intvector_intrinsics::vec128_rotate_left32(std, 16u32);
    st[8usize] = lib::intvector_intrinsics::vec128_add32(st[8usize], st[12usize]);
    let std0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[4usize], st[8usize]);
    st[4usize] = lib::intvector_intrinsics::vec128_rotate_left32(std0, 12u32);
    st[0usize] = lib::intvector_intrinsics::vec128_add32(st[0usize], st[4usize]);
    let std1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[12usize], st[0usize]);
    st[12usize] = lib::intvector_intrinsics::vec128_rotate_left32(std1, 8u32);
    st[8usize] = lib::intvector_intrinsics::vec128_add32(st[8usize], st[12usize]);
    let std2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[4usize], st[8usize]);
    st[4usize] = lib::intvector_intrinsics::vec128_rotate_left32(std2, 7u32);
    st[1usize] = lib::intvector_intrinsics::vec128_add32(st[1usize], st[5usize]);
    let std3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[13usize], st[1usize]);
    st[13usize] = lib::intvector_intrinsics::vec128_rotate_left32(std3, 16u32);
    st[9usize] = lib::intvector_intrinsics::vec128_add32(st[9usize], st[13usize]);
    let std4: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[5usize], st[9usize]);
    st[5usize] = lib::intvector_intrinsics::vec128_rotate_left32(std4, 12u32);
    st[1usize] = lib::intvector_intrinsics::vec128_add32(st[1usize], st[5usize]);
    let std5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[13usize], st[1usize]);
    st[13usize] = lib::intvector_intrinsics::vec128_rotate_left32(std5, 8u32);
    st[9usize] = lib::intvector_intrinsics::vec128_add32(st[9usize], st[13usize]);
    let std6: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[5usize], st[9usize]);
    st[5usize] = lib::intvector_intrinsics::vec128_rotate_left32(std6, 7u32);
    st[2usize] = lib::intvector_intrinsics::vec128_add32(st[2usize], st[6usize]);
    let std7: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[14usize], st[2usize]);
    st[14usize] = lib::intvector_intrinsics::vec128_rotate_left32(std7, 16u32);
    st[10usize] = lib::intvector_intrinsics::vec128_add32(st[10usize], st[14usize]);
    let std8: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[6usize], st[10usize]);
    st[6usize] = lib::intvector_intrinsics::vec128_rotate_left32(std8, 12u32);
    st[2usize] = lib::intvector_intrinsics::vec128_add32(st[2usize], st[6usize]);
    let std9: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[14usize], st[2usize]);
    st[14usize] = lib::intvector_intrinsics::vec128_rotate_left32(std9, 8u32);
    st[10usize] = lib::intvector_intrinsics::vec128_add32(st[10usize], st[14usize]);
    let std10: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[6usize], st[10usize]);
    st[6usize] = lib::intvector_intrinsics::vec128_rotate_left32(std10, 7u32);
    st[3usize] = lib::intvector_intrinsics::vec128_add32(st[3usize], st[7usize]);
    let std11: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[15usize], st[3usize]);
    st[15usize] = lib::intvector_intrinsics::vec128_rotate_left32(std11, 16u32);
    st[11usize] = lib::intvector_intrinsics::vec128_add32(st[11usize], st[15usize]);
    let std12: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[7usize], st[11usize]);
    st[7usize] = lib::intvector_intrinsics::vec128_rotate_left32(std12, 12u32);
    st[3usize] = lib::intvector_intrinsics::vec128_add32(st[3usize], st[7usize]);
    let std13: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[15usize], st[3usize]);
    st[15usize] = lib::intvector_intrinsics::vec128_rotate_left32(std13, 8u32);
    st[11usize] = lib::intvector_intrinsics::vec128_add32(st[11usize], st[15usize]);
    let std14: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[7usize], st[11usize]);
    st[7usize] = lib::intvector_intrinsics::vec128_rotate_left32(std14, 7u32);
    st[0usize] = lib::intvector_intrinsics::vec128_add32(st[0usize], st[5usize]);
    let std15: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[15usize], st[0usize]);
    st[15usize] = lib::intvector_intrinsics::vec128_rotate_left32(std15, 16u32);
    st[10usize] = lib::intvector_intrinsics::vec128_add32(st[10usize], st[15usize]);
    let std16: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[5usize], st[10usize]);
    st[5usize] = lib::intvector_intrinsics::vec128_rotate_left32(std16, 12u32);
    st[0usize] = lib::intvector_intrinsics::vec128_add32(st[0usize], st[5usize]);
    let std17: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[15usize], st[0usize]);
    st[15usize] = lib::intvector_intrinsics::vec128_rotate_left32(std17, 8u32);
    st[10usize] = lib::intvector_intrinsics::vec128_add32(st[10usize], st[15usize]);
    let std18: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[5usize], st[10usize]);
    st[5usize] = lib::intvector_intrinsics::vec128_rotate_left32(std18, 7u32);
    st[1usize] = lib::intvector_intrinsics::vec128_add32(st[1usize], st[6usize]);
    let std19: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[12usize], st[1usize]);
    st[12usize] = lib::intvector_intrinsics::vec128_rotate_left32(std19, 16u32);
    st[11usize] = lib::intvector_intrinsics::vec128_add32(st[11usize], st[12usize]);
    let std20: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[6usize], st[11usize]);
    st[6usize] = lib::intvector_intrinsics::vec128_rotate_left32(std20, 12u32);
    st[1usize] = lib::intvector_intrinsics::vec128_add32(st[1usize], st[6usize]);
    let std21: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[12usize], st[1usize]);
    st[12usize] = lib::intvector_intrinsics::vec128_rotate_left32(std21, 8u32);
    st[11usize] = lib::intvector_intrinsics::vec128_add32(st[11usize], st[12usize]);
    let std22: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[6usize], st[11usize]);
    st[6usize] = lib::intvector_intrinsics::vec128_rotate_left32(std22, 7u32);
    st[2usize] = lib::intvector_intrinsics::vec128_add32(st[2usize], st[7usize]);
    let std23: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[13usize], st[2usize]);
    st[13usize] = lib::intvector_intrinsics::vec128_rotate_left32(std23, 16u32);
    st[8usize] = lib::intvector_intrinsics::vec128_add32(st[8usize], st[13usize]);
    let std24: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[7usize], st[8usize]);
    st[7usize] = lib::intvector_intrinsics::vec128_rotate_left32(std24, 12u32);
    st[2usize] = lib::intvector_intrinsics::vec128_add32(st[2usize], st[7usize]);
    let std25: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[13usize], st[2usize]);
    st[13usize] = lib::intvector_intrinsics::vec128_rotate_left32(std25, 8u32);
    st[8usize] = lib::intvector_intrinsics::vec128_add32(st[8usize], st[13usize]);
    let std26: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[7usize], st[8usize]);
    st[7usize] = lib::intvector_intrinsics::vec128_rotate_left32(std26, 7u32);
    st[3usize] = lib::intvector_intrinsics::vec128_add32(st[3usize], st[4usize]);
    let std27: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[14usize], st[3usize]);
    st[14usize] = lib::intvector_intrinsics::vec128_rotate_left32(std27, 16u32);
    st[9usize] = lib::intvector_intrinsics::vec128_add32(st[9usize], st[14usize]);
    let std28: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[4usize], st[9usize]);
    st[4usize] = lib::intvector_intrinsics::vec128_rotate_left32(std28, 12u32);
    st[3usize] = lib::intvector_intrinsics::vec128_add32(st[3usize], st[4usize]);
    let std29: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[14usize], st[3usize]);
    st[14usize] = lib::intvector_intrinsics::vec128_rotate_left32(std29, 8u32);
    st[9usize] = lib::intvector_intrinsics::vec128_add32(st[9usize], st[14usize]);
    let std30: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_xor(st[4usize], st[9usize]);
    st[4usize] = lib::intvector_intrinsics::vec128_rotate_left32(std30, 7u32)
}

#[inline] fn chacha20_core_128(
    k: &mut [lib::intvector_intrinsics::vec128],
    ctx: &[lib::intvector_intrinsics::vec128],
    ctr: u32
)
{
    (k[0usize..16usize]).copy_from_slice(&ctx[0usize..16usize]);
    let ctr_u32: u32 = 4u32.wrapping_mul(ctr);
    let cv: lib::intvector_intrinsics::vec128 = lib::intvector_intrinsics::vec128_load32(ctr_u32);
    k[12usize] = lib::intvector_intrinsics::vec128_add32(k[12usize], cv);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    crate::chacha20_vec128::double_round_128(k);
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            let x: lib::intvector_intrinsics::vec128 =
                lib::intvector_intrinsics::vec128_add32(k[i as usize], ctx[i as usize]);
            let
            os: (&mut [lib::intvector_intrinsics::vec128], &mut [lib::intvector_intrinsics::vec128])
            =
                k.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    k[12usize] = lib::intvector_intrinsics::vec128_add32(k[12usize], cv)
}

#[inline] fn chacha20_init_128(
    ctx: &mut [lib::intvector_intrinsics::vec128],
    k: &[u8],
    n: &[u8],
    ctr: u32
)
{
    let mut ctx1: [u32; 16] = [0u32; 16usize];
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = (&crate::chacha20::chacha20_constants)[i as usize];
            let os: &mut [u32] = &mut (&mut (&mut ctx1)[0usize..])[0usize..];
            os[i as usize] = x
        }
    );
    let uu____0: (&mut [u32], &mut [u32]) = ctx1.split_at_mut(4usize);
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = k.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    (&mut ctx1)[12usize] = ctr;
    let uu____1: (&mut [u32], &mut [u32]) = ctx1.split_at_mut(13usize);
    krml::unroll_for!(
        3,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = n.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = (uu____1.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = (&ctx1)[i as usize];
            let x0: lib::intvector_intrinsics::vec128 = lib::intvector_intrinsics::vec128_load32(x);
            let
            os: (&mut [lib::intvector_intrinsics::vec128], &mut [lib::intvector_intrinsics::vec128])
            =
                ctx.split_at_mut(0usize);
            os.1[i as usize] = x0
        }
    );
    let ctr1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_load32s(0u32, 1u32, 2u32, 3u32);
    let c12: lib::intvector_intrinsics::vec128 = ctx[12usize];
    ctx[12usize] = lib::intvector_intrinsics::vec128_add32(c12, ctr1)
}

pub fn chacha20_encrypt_128(
    len: u32,
    out: &mut [u8],
    text: &[u8],
    key: &[u8],
    n: &[u8],
    ctr: u32
)
{
    let mut ctx: [lib::intvector_intrinsics::vec128; 16] =
        [lib::intvector_intrinsics::vec128_zero; 16usize];
    crate::chacha20_vec128::chacha20_init_128(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(256u32);
    let nb: u32 = len.wrapping_div(256u32);
    let rem1: u32 = len.wrapping_rem(256u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(256u32) as usize);
        let uu____1: (&[u8], &[u8]) = text.split_at(i.wrapping_mul(256u32) as usize);
        let mut k: [lib::intvector_intrinsics::vec128; 16] =
            [lib::intvector_intrinsics::vec128_zero; 16usize];
        crate::chacha20_vec128::chacha20_core_128(&mut k, &ctx, i);
        let st0: lib::intvector_intrinsics::vec128 = (&k)[0usize];
        let st1: lib::intvector_intrinsics::vec128 = (&k)[1usize];
        let st2: lib::intvector_intrinsics::vec128 = (&k)[2usize];
        let st3: lib::intvector_intrinsics::vec128 = (&k)[3usize];
        let st4: lib::intvector_intrinsics::vec128 = (&k)[4usize];
        let st5: lib::intvector_intrinsics::vec128 = (&k)[5usize];
        let st6: lib::intvector_intrinsics::vec128 = (&k)[6usize];
        let st7: lib::intvector_intrinsics::vec128 = (&k)[7usize];
        let st8: lib::intvector_intrinsics::vec128 = (&k)[8usize];
        let st9: lib::intvector_intrinsics::vec128 = (&k)[9usize];
        let st10: lib::intvector_intrinsics::vec128 = (&k)[10usize];
        let st11: lib::intvector_intrinsics::vec128 = (&k)[11usize];
        let st12: lib::intvector_intrinsics::vec128 = (&k)[12usize];
        let st13: lib::intvector_intrinsics::vec128 = (&k)[13usize];
        let st14: lib::intvector_intrinsics::vec128 = (&k)[14usize];
        let st15: lib::intvector_intrinsics::vec128 = (&k)[15usize];
        let v0·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
        let v1··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
        let v2··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
        let v3··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
        let v0··0: lib::intvector_intrinsics::vec128 = v0··;
        let v2··0: lib::intvector_intrinsics::vec128 = v2··;
        let v1··0: lib::intvector_intrinsics::vec128 = v1··;
        let v3··0: lib::intvector_intrinsics::vec128 = v3··;
        let v0: lib::intvector_intrinsics::vec128 = v0··0;
        let v1: lib::intvector_intrinsics::vec128 = v1··0;
        let v2: lib::intvector_intrinsics::vec128 = v2··0;
        let v3: lib::intvector_intrinsics::vec128 = v3··0;
        let v0·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
        let v1··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
        let v2··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
        let v3··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
        let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
        let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
        let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
        let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
        let v4: lib::intvector_intrinsics::vec128 = v0··2;
        let v5: lib::intvector_intrinsics::vec128 = v1··2;
        let v6: lib::intvector_intrinsics::vec128 = v2··2;
        let v7: lib::intvector_intrinsics::vec128 = v3··2;
        let v0·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·1, v2·1);
        let v1··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·1, v2·1);
        let v2··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·1, v3·1);
        let v3··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·1, v3·1);
        let v0··4: lib::intvector_intrinsics::vec128 = v0··3;
        let v2··4: lib::intvector_intrinsics::vec128 = v2··3;
        let v1··4: lib::intvector_intrinsics::vec128 = v1··3;
        let v3··4: lib::intvector_intrinsics::vec128 = v3··3;
        let v8: lib::intvector_intrinsics::vec128 = v0··4;
        let v9: lib::intvector_intrinsics::vec128 = v1··4;
        let v10: lib::intvector_intrinsics::vec128 = v2··4;
        let v11: lib::intvector_intrinsics::vec128 = v3··4;
        let v0·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·2, v2·2);
        let v1··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·2, v2·2);
        let v2··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·2, v3·2);
        let v3··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·2, v3·2);
        let v0··6: lib::intvector_intrinsics::vec128 = v0··5;
        let v2··6: lib::intvector_intrinsics::vec128 = v2··5;
        let v1··6: lib::intvector_intrinsics::vec128 = v1··5;
        let v3··6: lib::intvector_intrinsics::vec128 = v3··5;
        let v12: lib::intvector_intrinsics::vec128 = v0··6;
        let v13: lib::intvector_intrinsics::vec128 = v1··6;
        let v14: lib::intvector_intrinsics::vec128 = v2··6;
        let v15: lib::intvector_intrinsics::vec128 = v3··6;
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
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            {
                let x: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_load32_le(
                        &uu____1.1[i0.wrapping_mul(16u32) as usize..]
                    );
                let y: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_xor(x, (&k)[i0 as usize]);
                lib::intvector_intrinsics::vec128_store32_le(
                    &mut uu____0.1[i0.wrapping_mul(16u32) as usize..],
                    y
                )
            }
        )
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(256u32) as usize);
        let mut plain: [u8; 256] = [0u8; 256usize];
        ((&mut plain)[0usize..rem as usize]).copy_from_slice(
            &(&text[nb.wrapping_mul(256u32) as usize..])[0usize..rem as usize]
        );
        let mut k: [lib::intvector_intrinsics::vec128; 16] =
            [lib::intvector_intrinsics::vec128_zero; 16usize];
        crate::chacha20_vec128::chacha20_core_128(&mut k, &ctx, nb);
        let st0: lib::intvector_intrinsics::vec128 = (&k)[0usize];
        let st1: lib::intvector_intrinsics::vec128 = (&k)[1usize];
        let st2: lib::intvector_intrinsics::vec128 = (&k)[2usize];
        let st3: lib::intvector_intrinsics::vec128 = (&k)[3usize];
        let st4: lib::intvector_intrinsics::vec128 = (&k)[4usize];
        let st5: lib::intvector_intrinsics::vec128 = (&k)[5usize];
        let st6: lib::intvector_intrinsics::vec128 = (&k)[6usize];
        let st7: lib::intvector_intrinsics::vec128 = (&k)[7usize];
        let st8: lib::intvector_intrinsics::vec128 = (&k)[8usize];
        let st9: lib::intvector_intrinsics::vec128 = (&k)[9usize];
        let st10: lib::intvector_intrinsics::vec128 = (&k)[10usize];
        let st11: lib::intvector_intrinsics::vec128 = (&k)[11usize];
        let st12: lib::intvector_intrinsics::vec128 = (&k)[12usize];
        let st13: lib::intvector_intrinsics::vec128 = (&k)[13usize];
        let st14: lib::intvector_intrinsics::vec128 = (&k)[14usize];
        let st15: lib::intvector_intrinsics::vec128 = (&k)[15usize];
        let v0·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
        let v1··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
        let v2··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
        let v3··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
        let v0··0: lib::intvector_intrinsics::vec128 = v0··;
        let v2··0: lib::intvector_intrinsics::vec128 = v2··;
        let v1··0: lib::intvector_intrinsics::vec128 = v1··;
        let v3··0: lib::intvector_intrinsics::vec128 = v3··;
        let v0: lib::intvector_intrinsics::vec128 = v0··0;
        let v1: lib::intvector_intrinsics::vec128 = v1··0;
        let v2: lib::intvector_intrinsics::vec128 = v2··0;
        let v3: lib::intvector_intrinsics::vec128 = v3··0;
        let v0·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
        let v1··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
        let v2··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
        let v3··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
        let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
        let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
        let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
        let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
        let v4: lib::intvector_intrinsics::vec128 = v0··2;
        let v5: lib::intvector_intrinsics::vec128 = v1··2;
        let v6: lib::intvector_intrinsics::vec128 = v2··2;
        let v7: lib::intvector_intrinsics::vec128 = v3··2;
        let v0·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·1, v2·1);
        let v1··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·1, v2·1);
        let v2··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·1, v3·1);
        let v3··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·1, v3·1);
        let v0··4: lib::intvector_intrinsics::vec128 = v0··3;
        let v2··4: lib::intvector_intrinsics::vec128 = v2··3;
        let v1··4: lib::intvector_intrinsics::vec128 = v1··3;
        let v3··4: lib::intvector_intrinsics::vec128 = v3··3;
        let v8: lib::intvector_intrinsics::vec128 = v0··4;
        let v9: lib::intvector_intrinsics::vec128 = v1··4;
        let v10: lib::intvector_intrinsics::vec128 = v2··4;
        let v11: lib::intvector_intrinsics::vec128 = v3··4;
        let v0·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·2, v2·2);
        let v1··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·2, v2·2);
        let v2··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·2, v3·2);
        let v3··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·2, v3·2);
        let v0··6: lib::intvector_intrinsics::vec128 = v0··5;
        let v2··6: lib::intvector_intrinsics::vec128 = v2··5;
        let v1··6: lib::intvector_intrinsics::vec128 = v1··5;
        let v3··6: lib::intvector_intrinsics::vec128 = v3··5;
        let v12: lib::intvector_intrinsics::vec128 = v0··6;
        let v13: lib::intvector_intrinsics::vec128 = v1··6;
        let v14: lib::intvector_intrinsics::vec128 = v2··6;
        let v15: lib::intvector_intrinsics::vec128 = v3··6;
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
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            {
                let x: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_load32_le(
                        &(&plain)[i.wrapping_mul(16u32) as usize..]
                    );
                let y: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_xor(x, (&k)[i as usize]);
                lib::intvector_intrinsics::vec128_store32_le(
                    &mut (&mut plain)[i.wrapping_mul(16u32) as usize..],
                    y
                )
            }
        );
        (uu____2.1[0usize..rem as usize]).copy_from_slice(
            &(&(&plain)[0usize..])[0usize..rem as usize]
        )
    }
}

pub fn chacha20_decrypt_128(
    len: u32,
    out: &mut [u8],
    cipher: &[u8],
    key: &[u8],
    n: &[u8],
    ctr: u32
)
{
    let mut ctx: [lib::intvector_intrinsics::vec128; 16] =
        [lib::intvector_intrinsics::vec128_zero; 16usize];
    crate::chacha20_vec128::chacha20_init_128(&mut ctx, key, n, ctr);
    let rem: u32 = len.wrapping_rem(256u32);
    let nb: u32 = len.wrapping_div(256u32);
    let rem1: u32 = len.wrapping_rem(256u32);
    for i in 0u32..nb
    {
        let uu____0: (&mut [u8], &mut [u8]) = out.split_at_mut(i.wrapping_mul(256u32) as usize);
        let uu____1: (&[u8], &[u8]) = cipher.split_at(i.wrapping_mul(256u32) as usize);
        let mut k: [lib::intvector_intrinsics::vec128; 16] =
            [lib::intvector_intrinsics::vec128_zero; 16usize];
        crate::chacha20_vec128::chacha20_core_128(&mut k, &ctx, i);
        let st0: lib::intvector_intrinsics::vec128 = (&k)[0usize];
        let st1: lib::intvector_intrinsics::vec128 = (&k)[1usize];
        let st2: lib::intvector_intrinsics::vec128 = (&k)[2usize];
        let st3: lib::intvector_intrinsics::vec128 = (&k)[3usize];
        let st4: lib::intvector_intrinsics::vec128 = (&k)[4usize];
        let st5: lib::intvector_intrinsics::vec128 = (&k)[5usize];
        let st6: lib::intvector_intrinsics::vec128 = (&k)[6usize];
        let st7: lib::intvector_intrinsics::vec128 = (&k)[7usize];
        let st8: lib::intvector_intrinsics::vec128 = (&k)[8usize];
        let st9: lib::intvector_intrinsics::vec128 = (&k)[9usize];
        let st10: lib::intvector_intrinsics::vec128 = (&k)[10usize];
        let st11: lib::intvector_intrinsics::vec128 = (&k)[11usize];
        let st12: lib::intvector_intrinsics::vec128 = (&k)[12usize];
        let st13: lib::intvector_intrinsics::vec128 = (&k)[13usize];
        let st14: lib::intvector_intrinsics::vec128 = (&k)[14usize];
        let st15: lib::intvector_intrinsics::vec128 = (&k)[15usize];
        let v0·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
        let v1··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
        let v2··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
        let v3··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
        let v0··0: lib::intvector_intrinsics::vec128 = v0··;
        let v2··0: lib::intvector_intrinsics::vec128 = v2··;
        let v1··0: lib::intvector_intrinsics::vec128 = v1··;
        let v3··0: lib::intvector_intrinsics::vec128 = v3··;
        let v0: lib::intvector_intrinsics::vec128 = v0··0;
        let v1: lib::intvector_intrinsics::vec128 = v1··0;
        let v2: lib::intvector_intrinsics::vec128 = v2··0;
        let v3: lib::intvector_intrinsics::vec128 = v3··0;
        let v0·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
        let v1··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
        let v2··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
        let v3··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
        let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
        let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
        let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
        let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
        let v4: lib::intvector_intrinsics::vec128 = v0··2;
        let v5: lib::intvector_intrinsics::vec128 = v1··2;
        let v6: lib::intvector_intrinsics::vec128 = v2··2;
        let v7: lib::intvector_intrinsics::vec128 = v3··2;
        let v0·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·1, v2·1);
        let v1··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·1, v2·1);
        let v2··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·1, v3·1);
        let v3··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·1, v3·1);
        let v0··4: lib::intvector_intrinsics::vec128 = v0··3;
        let v2··4: lib::intvector_intrinsics::vec128 = v2··3;
        let v1··4: lib::intvector_intrinsics::vec128 = v1··3;
        let v3··4: lib::intvector_intrinsics::vec128 = v3··3;
        let v8: lib::intvector_intrinsics::vec128 = v0··4;
        let v9: lib::intvector_intrinsics::vec128 = v1··4;
        let v10: lib::intvector_intrinsics::vec128 = v2··4;
        let v11: lib::intvector_intrinsics::vec128 = v3··4;
        let v0·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·2, v2·2);
        let v1··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·2, v2·2);
        let v2··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·2, v3·2);
        let v3··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·2, v3·2);
        let v0··6: lib::intvector_intrinsics::vec128 = v0··5;
        let v2··6: lib::intvector_intrinsics::vec128 = v2··5;
        let v1··6: lib::intvector_intrinsics::vec128 = v1··5;
        let v3··6: lib::intvector_intrinsics::vec128 = v3··5;
        let v12: lib::intvector_intrinsics::vec128 = v0··6;
        let v13: lib::intvector_intrinsics::vec128 = v1··6;
        let v14: lib::intvector_intrinsics::vec128 = v2··6;
        let v15: lib::intvector_intrinsics::vec128 = v3··6;
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
        krml::unroll_for!(
            16,
            "i0",
            0u32,
            1u32,
            {
                let x: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_load32_le(
                        &uu____1.1[i0.wrapping_mul(16u32) as usize..]
                    );
                let y: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_xor(x, (&k)[i0 as usize]);
                lib::intvector_intrinsics::vec128_store32_le(
                    &mut uu____0.1[i0.wrapping_mul(16u32) as usize..],
                    y
                )
            }
        )
    };
    if rem1 > 0u32
    {
        let uu____2: (&mut [u8], &mut [u8]) = out.split_at_mut(nb.wrapping_mul(256u32) as usize);
        let mut plain: [u8; 256] = [0u8; 256usize];
        ((&mut plain)[0usize..rem as usize]).copy_from_slice(
            &(&cipher[nb.wrapping_mul(256u32) as usize..])[0usize..rem as usize]
        );
        let mut k: [lib::intvector_intrinsics::vec128; 16] =
            [lib::intvector_intrinsics::vec128_zero; 16usize];
        crate::chacha20_vec128::chacha20_core_128(&mut k, &ctx, nb);
        let st0: lib::intvector_intrinsics::vec128 = (&k)[0usize];
        let st1: lib::intvector_intrinsics::vec128 = (&k)[1usize];
        let st2: lib::intvector_intrinsics::vec128 = (&k)[2usize];
        let st3: lib::intvector_intrinsics::vec128 = (&k)[3usize];
        let st4: lib::intvector_intrinsics::vec128 = (&k)[4usize];
        let st5: lib::intvector_intrinsics::vec128 = (&k)[5usize];
        let st6: lib::intvector_intrinsics::vec128 = (&k)[6usize];
        let st7: lib::intvector_intrinsics::vec128 = (&k)[7usize];
        let st8: lib::intvector_intrinsics::vec128 = (&k)[8usize];
        let st9: lib::intvector_intrinsics::vec128 = (&k)[9usize];
        let st10: lib::intvector_intrinsics::vec128 = (&k)[10usize];
        let st11: lib::intvector_intrinsics::vec128 = (&k)[11usize];
        let st12: lib::intvector_intrinsics::vec128 = (&k)[12usize];
        let st13: lib::intvector_intrinsics::vec128 = (&k)[13usize];
        let st14: lib::intvector_intrinsics::vec128 = (&k)[14usize];
        let st15: lib::intvector_intrinsics::vec128 = (&k)[15usize];
        let v0·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st0, st1);
        let v1·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st0, st1);
        let v2·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st2, st3);
        let v3·: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st2, st3);
        let v0··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
        let v1··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
        let v2··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
        let v3··: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
        let v0··0: lib::intvector_intrinsics::vec128 = v0··;
        let v2··0: lib::intvector_intrinsics::vec128 = v2··;
        let v1··0: lib::intvector_intrinsics::vec128 = v1··;
        let v3··0: lib::intvector_intrinsics::vec128 = v3··;
        let v0: lib::intvector_intrinsics::vec128 = v0··0;
        let v1: lib::intvector_intrinsics::vec128 = v1··0;
        let v2: lib::intvector_intrinsics::vec128 = v2··0;
        let v3: lib::intvector_intrinsics::vec128 = v3··0;
        let v0·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st4, st5);
        let v1·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st4, st5);
        let v2·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st6, st7);
        let v3·0: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st6, st7);
        let v0··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
        let v1··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
        let v2··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
        let v3··1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
        let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
        let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
        let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
        let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
        let v4: lib::intvector_intrinsics::vec128 = v0··2;
        let v5: lib::intvector_intrinsics::vec128 = v1··2;
        let v6: lib::intvector_intrinsics::vec128 = v2··2;
        let v7: lib::intvector_intrinsics::vec128 = v3··2;
        let v0·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st8, st9);
        let v1·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st8, st9);
        let v2·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st10, st11);
        let v3·1: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st10, st11);
        let v0··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·1, v2·1);
        let v1··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·1, v2·1);
        let v2··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·1, v3·1);
        let v3··3: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·1, v3·1);
        let v0··4: lib::intvector_intrinsics::vec128 = v0··3;
        let v2··4: lib::intvector_intrinsics::vec128 = v2··3;
        let v1··4: lib::intvector_intrinsics::vec128 = v1··3;
        let v3··4: lib::intvector_intrinsics::vec128 = v3··3;
        let v8: lib::intvector_intrinsics::vec128 = v0··4;
        let v9: lib::intvector_intrinsics::vec128 = v1··4;
        let v10: lib::intvector_intrinsics::vec128 = v2··4;
        let v11: lib::intvector_intrinsics::vec128 = v3··4;
        let v0·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st12, st13);
        let v1·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st12, st13);
        let v2·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low32(st14, st15);
        let v3·2: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high32(st14, st15);
        let v0··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v0·2, v2·2);
        let v1··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v0·2, v2·2);
        let v2··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_low64(v1·2, v3·2);
        let v3··5: lib::intvector_intrinsics::vec128 =
            lib::intvector_intrinsics::vec128_interleave_high64(v1·2, v3·2);
        let v0··6: lib::intvector_intrinsics::vec128 = v0··5;
        let v2··6: lib::intvector_intrinsics::vec128 = v2··5;
        let v1··6: lib::intvector_intrinsics::vec128 = v1··5;
        let v3··6: lib::intvector_intrinsics::vec128 = v3··5;
        let v12: lib::intvector_intrinsics::vec128 = v0··6;
        let v13: lib::intvector_intrinsics::vec128 = v1··6;
        let v14: lib::intvector_intrinsics::vec128 = v2··6;
        let v15: lib::intvector_intrinsics::vec128 = v3··6;
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
        krml::unroll_for!(
            16,
            "i",
            0u32,
            1u32,
            {
                let x: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_load32_le(
                        &(&plain)[i.wrapping_mul(16u32) as usize..]
                    );
                let y: lib::intvector_intrinsics::vec128 =
                    lib::intvector_intrinsics::vec128_xor(x, (&k)[i as usize]);
                lib::intvector_intrinsics::vec128_store32_le(
                    &mut (&mut plain)[i.wrapping_mul(16u32) as usize..],
                    y
                )
            }
        );
        (uu____2.1[0usize..rem as usize]).copy_from_slice(
            &(&(&plain)[0usize..])[0usize..rem as usize]
        )
    }
}
