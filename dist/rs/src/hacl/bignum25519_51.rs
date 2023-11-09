pub fn fadd(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
{
    let f10: u64 = f1[0usize];
    let f20: u64 = f2[0usize];
    let f11: u64 = f1[1usize];
    let f21: u64 = f2[1usize];
    let f12: u64 = f1[2usize];
    let f22: u64 = f2[2usize];
    let f13: u64 = f1[3usize];
    let f23: u64 = f2[3usize];
    let f14: u64 = f1[4usize];
    let f24: u64 = f2[4usize];
    out[0usize] = f10.wrapping_add(f20);
    out[1usize] = f11.wrapping_add(f21);
    out[2usize] = f12.wrapping_add(f22);
    out[3usize] = f13.wrapping_add(f23);
    out[4usize] = f14.wrapping_add(f24)
}

pub fn fsub(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
{
    let f10: u64 = f1[0usize];
    let f20: u64 = f2[0usize];
    let f11: u64 = f1[1usize];
    let f21: u64 = f2[1usize];
    let f12: u64 = f1[2usize];
    let f22: u64 = f2[2usize];
    let f13: u64 = f1[3usize];
    let f23: u64 = f2[3usize];
    let f14: u64 = f1[4usize];
    let f24: u64 = f2[4usize];
    out[0usize] = f10.wrapping_add(0x3fffffffffff68u64).wrapping_sub(f20);
    out[1usize] = f11.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f21);
    out[2usize] = f12.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f22);
    out[3usize] = f13.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f23);
    out[4usize] = f14.wrapping_add(0x3ffffffffffff8u64).wrapping_sub(f24)
}

pub fn fmul1(out: &mut [u64], f1: &mut [u64], f2: u64) -> ()
{
    let f10: u64 = f1[0usize];
    let f11: u64 = f1[1usize];
    let f12: u64 = f1[2usize];
    let f13: u64 = f1[3usize];
    let f14: u64 = f1[4usize];
    let tmp_w0: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f2, f10);
    let tmp_w1: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f2, f11);
    let tmp_w2: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f2, f12);
    let tmp_w3: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f2, f13);
    let tmp_w4: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f2, f14);
    let l': crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w0, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp0: u64 = crate::fstar::uint128::uint128_to_uint64(l') & 0x7ffffffffffffu64;
    let c0: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l', 51u32));
    let l'0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w1, crate::fstar::uint128::uint64_to_uint128(c0));
    let tmp1: u64 = crate::fstar::uint128::uint128_to_uint64(l'0) & 0x7ffffffffffffu64;
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l'0, 51u32));
    let l'1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w2, crate::fstar::uint128::uint64_to_uint128(c1));
    let tmp2: u64 = crate::fstar::uint128::uint128_to_uint64(l'1) & 0x7ffffffffffffu64;
    let c2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l'1, 51u32));
    let l'2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w3, crate::fstar::uint128::uint64_to_uint128(c2));
    let tmp3: u64 = crate::fstar::uint128::uint128_to_uint64(l'2) & 0x7ffffffffffffu64;
    let c3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l'2, 51u32));
    let l'3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w4, crate::fstar::uint128::uint64_to_uint128(c3));
    let tmp4: u64 = crate::fstar::uint128::uint128_to_uint64(l'3) & 0x7ffffffffffffu64;
    let c4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l'3, 51u32));
    let l'4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0': u64 = l'4 & 0x7ffffffffffffu64;
    let c5: u64 = l'4.wrapping_shr(51u32);
    let o0: u64 = tmp0';
    let o1: u64 = tmp1.wrapping_add(c5);
    let o2: u64 = tmp2;
    let o3: u64 = tmp3;
    let o4: u64 = tmp4;
    out[0usize] = o0;
    out[1usize] = o1;
    out[2usize] = o2;
    out[3usize] = o3;
    out[4usize] = o4
}

pub fn store_felem(u64s: &mut [u64], f: &mut [u64]) -> ()
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let l': u64 = f0.wrapping_add(0u64);
    let tmp0: u64 = l' & 0x7ffffffffffffu64;
    let c0: u64 = l'.wrapping_shr(51u32);
    let l'0: u64 = f1.wrapping_add(c0);
    let tmp1: u64 = l'0 & 0x7ffffffffffffu64;
    let c1: u64 = l'0.wrapping_shr(51u32);
    let l'1: u64 = f2.wrapping_add(c1);
    let tmp2: u64 = l'1 & 0x7ffffffffffffu64;
    let c2: u64 = l'1.wrapping_shr(51u32);
    let l'2: u64 = f3.wrapping_add(c2);
    let tmp3: u64 = l'2 & 0x7ffffffffffffu64;
    let c3: u64 = l'2.wrapping_shr(51u32);
    let l'3: u64 = f4.wrapping_add(c3);
    let tmp4: u64 = l'3 & 0x7ffffffffffffu64;
    let c4: u64 = l'3.wrapping_shr(51u32);
    let l'4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0': u64 = l'4 & 0x7ffffffffffffu64;
    let c5: u64 = l'4.wrapping_shr(51u32);
    let f01: u64 = tmp0';
    let f11: u64 = tmp1.wrapping_add(c5);
    let f21: u64 = tmp2;
    let f31: u64 = tmp3;
    let f41: u64 = tmp4;
    let m0: u64 = crate::fstar::uint64::gte_mask(f01, 0x7ffffffffffedu64);
    let m1: u64 = crate::fstar::uint64::eq_mask(f11, 0x7ffffffffffffu64);
    let m2: u64 = crate::fstar::uint64::eq_mask(f21, 0x7ffffffffffffu64);
    let m3: u64 = crate::fstar::uint64::eq_mask(f31, 0x7ffffffffffffu64);
    let m4: u64 = crate::fstar::uint64::eq_mask(f41, 0x7ffffffffffffu64);
    let mask: u64 = m0 & m1 & m2 & m3 & m4;
    let f0': u64 = f01.wrapping_sub(mask & 0x7ffffffffffedu64);
    let f1': u64 = f11.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f2': u64 = f21.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f3': u64 = f31.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f4': u64 = f41.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f02: u64 = f0';
    let f12: u64 = f1';
    let f22: u64 = f2';
    let f32: u64 = f3';
    let f42: u64 = f4';
    let o0: u64 = f02 | f12.wrapping_shl(51u32);
    let o1: u64 = f12.wrapping_shr(13u32) | f22.wrapping_shl(38u32);
    let o2: u64 = f22.wrapping_shr(26u32) | f32.wrapping_shl(25u32);
    let o3: u64 = f32.wrapping_shr(39u32) | f42.wrapping_shl(12u32);
    let o00: u64 = o0;
    let o10: u64 = o1;
    let o20: u64 = o2;
    let o30: u64 = o3;
    u64s[0usize] = o00;
    u64s[1usize] = o10;
    u64s[2usize] = o20;
    u64s[3usize] = o30
}

pub fn cswap2(bit: u64, p1: &mut [u64], p2: &mut [u64]) -> ()
{
    let mask: u64 = 0u64.wrapping_sub(bit);
    for i in 0u32..10u32
    {
        let dummy: u64 = mask & (p1[i as usize] ^ p2[i as usize]);
        p1[i as usize] = p1[i as usize] ^ dummy;
        p2[i as usize] = p2[i as usize] ^ dummy
    }
}