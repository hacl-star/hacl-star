#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] pub fn fadd(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
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

#[inline] pub fn fsub(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
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

#[inline] pub fn fmul(
    out: &mut [u64],
    f1: &mut [u64],
    f2: &mut [u64],
    uu___: &mut [crate::fstar::uint128::uint128]
) ->
    ()
{
    crate::lowstar::ignore::ignore::<&mut [crate::fstar::uint128::uint128]>(uu___);
    let f10: u64 = f1[0usize];
    let f11: u64 = f1[1usize];
    let f12: u64 = f1[2usize];
    let f13: u64 = f1[3usize];
    let f14: u64 = f1[4usize];
    let f20: u64 = f2[0usize];
    let f21: u64 = f2[1usize];
    let f22: u64 = f2[2usize];
    let f23: u64 = f2[3usize];
    let f24: u64 = f2[4usize];
    let tmp1: u64 = f21.wrapping_mul(19u64);
    let tmp2: u64 = f22.wrapping_mul(19u64);
    let tmp3: u64 = f23.wrapping_mul(19u64);
    let tmp4: u64 = f24.wrapping_mul(19u64);
    let o0: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f20);
    let o1: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f21);
    let o2: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f22);
    let o3: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f23);
    let o4: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f24);
    let o01: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o0, crate::fstar::uint128::mul_wide(f11, tmp4));
    let o11: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o1, crate::fstar::uint128::mul_wide(f11, f20));
    let o21: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o2, crate::fstar::uint128::mul_wide(f11, f21));
    let o31: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o3, crate::fstar::uint128::mul_wide(f11, f22));
    let o41: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o4, crate::fstar::uint128::mul_wide(f11, f23));
    let o02: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o01, crate::fstar::uint128::mul_wide(f12, tmp3));
    let o12: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o11, crate::fstar::uint128::mul_wide(f12, tmp4));
    let o22: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o21, crate::fstar::uint128::mul_wide(f12, f20));
    let o32: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o31, crate::fstar::uint128::mul_wide(f12, f21));
    let o42: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o41, crate::fstar::uint128::mul_wide(f12, f22));
    let o03: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o02, crate::fstar::uint128::mul_wide(f13, tmp2));
    let o13: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o12, crate::fstar::uint128::mul_wide(f13, tmp3));
    let o23: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o22, crate::fstar::uint128::mul_wide(f13, tmp4));
    let o33: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o32, crate::fstar::uint128::mul_wide(f13, f20));
    let o43: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o42, crate::fstar::uint128::mul_wide(f13, f21));
    let o04: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o03, crate::fstar::uint128::mul_wide(f14, tmp1));
    let o14: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o13, crate::fstar::uint128::mul_wide(f14, tmp2));
    let o24: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o23, crate::fstar::uint128::mul_wide(f14, tmp3));
    let o34: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o33, crate::fstar::uint128::mul_wide(f14, tmp4));
    let o44: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o43, crate::fstar::uint128::mul_wide(f14, f20));
    let tmp_w0: crate::fstar::uint128::uint128 = o04;
    let tmp_w1: crate::fstar::uint128::uint128 = o14;
    let tmp_w2: crate::fstar::uint128::uint128 = o24;
    let tmp_w3: crate::fstar::uint128::uint128 = o34;
    let tmp_w4: crate::fstar::uint128::uint128 = o44;
    let l·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w0, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp01: u64 = crate::fstar::uint128::uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·, 51u32));
    let l·0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w1, crate::fstar::uint128::uint64_to_uint128(c0));
    let tmp11: u64 = crate::fstar::uint128::uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·0, 51u32));
    let l·1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w2, crate::fstar::uint128::uint64_to_uint128(c1));
    let tmp21: u64 = crate::fstar::uint128::uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·1, 51u32));
    let l·2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w3, crate::fstar::uint128::uint64_to_uint128(c2));
    let tmp31: u64 = crate::fstar::uint128::uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·2, 51u32));
    let l·3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w4, crate::fstar::uint128::uint64_to_uint128(c3));
    let tmp41: u64 = crate::fstar::uint128::uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·3, 51u32));
    let l·4: u64 = tmp01.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let o00: u64 = tmp0·;
    let o10: u64 = tmp11.wrapping_add(c5);
    let o20: u64 = tmp21;
    let o30: u64 = tmp31;
    let o40: u64 = tmp41;
    out[0usize] = o00;
    out[1usize] = o10;
    out[2usize] = o20;
    out[3usize] = o30;
    out[4usize] = o40
}

#[inline] pub fn fmul2(
    out: &mut [u64],
    f1: &mut [u64],
    f2: &mut [u64],
    uu___: &mut [crate::fstar::uint128::uint128]
) ->
    ()
{
    crate::lowstar::ignore::ignore::<&mut [crate::fstar::uint128::uint128]>(uu___);
    let f10: u64 = f1[0usize];
    let f11: u64 = f1[1usize];
    let f12: u64 = f1[2usize];
    let f13: u64 = f1[3usize];
    let f14: u64 = f1[4usize];
    let f20: u64 = f2[0usize];
    let f21: u64 = f2[1usize];
    let f22: u64 = f2[2usize];
    let f23: u64 = f2[3usize];
    let f24: u64 = f2[4usize];
    let f30: u64 = f1[5usize];
    let f31: u64 = f1[6usize];
    let f32: u64 = f1[7usize];
    let f33: u64 = f1[8usize];
    let f34: u64 = f1[9usize];
    let f40: u64 = f2[5usize];
    let f41: u64 = f2[6usize];
    let f42: u64 = f2[7usize];
    let f43: u64 = f2[8usize];
    let f44: u64 = f2[9usize];
    let tmp11: u64 = f21.wrapping_mul(19u64);
    let tmp12: u64 = f22.wrapping_mul(19u64);
    let tmp13: u64 = f23.wrapping_mul(19u64);
    let tmp14: u64 = f24.wrapping_mul(19u64);
    let tmp21: u64 = f41.wrapping_mul(19u64);
    let tmp22: u64 = f42.wrapping_mul(19u64);
    let tmp23: u64 = f43.wrapping_mul(19u64);
    let tmp24: u64 = f44.wrapping_mul(19u64);
    let o0: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f20);
    let o1: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f21);
    let o2: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f22);
    let o3: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f23);
    let o4: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f10, f24);
    let o01: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o0, crate::fstar::uint128::mul_wide(f11, tmp14));
    let o11: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o1, crate::fstar::uint128::mul_wide(f11, f20));
    let o21: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o2, crate::fstar::uint128::mul_wide(f11, f21));
    let o31: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o3, crate::fstar::uint128::mul_wide(f11, f22));
    let o41: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o4, crate::fstar::uint128::mul_wide(f11, f23));
    let o02: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o01, crate::fstar::uint128::mul_wide(f12, tmp13));
    let o12: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o11, crate::fstar::uint128::mul_wide(f12, tmp14));
    let o22: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o21, crate::fstar::uint128::mul_wide(f12, f20));
    let o32: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o31, crate::fstar::uint128::mul_wide(f12, f21));
    let o42: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o41, crate::fstar::uint128::mul_wide(f12, f22));
    let o03: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o02, crate::fstar::uint128::mul_wide(f13, tmp12));
    let o13: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o12, crate::fstar::uint128::mul_wide(f13, tmp13));
    let o23: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o22, crate::fstar::uint128::mul_wide(f13, tmp14));
    let o33: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o32, crate::fstar::uint128::mul_wide(f13, f20));
    let o43: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o42, crate::fstar::uint128::mul_wide(f13, f21));
    let o04: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o03, crate::fstar::uint128::mul_wide(f14, tmp11));
    let o14: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o13, crate::fstar::uint128::mul_wide(f14, tmp12));
    let o24: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o23, crate::fstar::uint128::mul_wide(f14, tmp13));
    let o34: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o33, crate::fstar::uint128::mul_wide(f14, tmp14));
    let o44: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o43, crate::fstar::uint128::mul_wide(f14, f20));
    let tmp_w10: crate::fstar::uint128::uint128 = o04;
    let tmp_w11: crate::fstar::uint128::uint128 = o14;
    let tmp_w12: crate::fstar::uint128::uint128 = o24;
    let tmp_w13: crate::fstar::uint128::uint128 = o34;
    let tmp_w14: crate::fstar::uint128::uint128 = o44;
    let o00: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f30, f40);
    let o10: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f30, f41);
    let o20: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f30, f42);
    let o30: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f30, f43);
    let o40: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(f30, f44);
    let o010: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o00, crate::fstar::uint128::mul_wide(f31, tmp24));
    let o110: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o10, crate::fstar::uint128::mul_wide(f31, f40));
    let o210: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o20, crate::fstar::uint128::mul_wide(f31, f41));
    let o310: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o30, crate::fstar::uint128::mul_wide(f31, f42));
    let o410: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o40, crate::fstar::uint128::mul_wide(f31, f43));
    let o020: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o010, crate::fstar::uint128::mul_wide(f32, tmp23));
    let o120: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o110, crate::fstar::uint128::mul_wide(f32, tmp24));
    let o220: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o210, crate::fstar::uint128::mul_wide(f32, f40));
    let o320: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o310, crate::fstar::uint128::mul_wide(f32, f41));
    let o420: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o410, crate::fstar::uint128::mul_wide(f32, f42));
    let o030: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o020, crate::fstar::uint128::mul_wide(f33, tmp22));
    let o130: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o120, crate::fstar::uint128::mul_wide(f33, tmp23));
    let o230: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o220, crate::fstar::uint128::mul_wide(f33, tmp24));
    let o330: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o320, crate::fstar::uint128::mul_wide(f33, f40));
    let o430: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o420, crate::fstar::uint128::mul_wide(f33, f41));
    let o040: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o030, crate::fstar::uint128::mul_wide(f34, tmp21));
    let o140: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o130, crate::fstar::uint128::mul_wide(f34, tmp22));
    let o240: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o230, crate::fstar::uint128::mul_wide(f34, tmp23));
    let o340: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o330, crate::fstar::uint128::mul_wide(f34, tmp24));
    let o440: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o430, crate::fstar::uint128::mul_wide(f34, f40));
    let tmp_w20: crate::fstar::uint128::uint128 = o040;
    let tmp_w21: crate::fstar::uint128::uint128 = o140;
    let tmp_w22: crate::fstar::uint128::uint128 = o240;
    let tmp_w23: crate::fstar::uint128::uint128 = o340;
    let tmp_w24: crate::fstar::uint128::uint128 = o440;
    let l·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w10, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp0: u64 = crate::fstar::uint128::uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·, 51u32));
    let l·0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w11, crate::fstar::uint128::uint64_to_uint128(c0));
    let tmp1: u64 = crate::fstar::uint128::uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·0, 51u32));
    let l·1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w12, crate::fstar::uint128::uint64_to_uint128(c1));
    let tmp2: u64 = crate::fstar::uint128::uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·1, 51u32));
    let l·2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w13, crate::fstar::uint128::uint64_to_uint128(c2));
    let tmp3: u64 = crate::fstar::uint128::uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·2, 51u32));
    let l·3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w14, crate::fstar::uint128::uint64_to_uint128(c3));
    let tmp4: u64 = crate::fstar::uint128::uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·3, 51u32));
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let o100: u64 = tmp0·;
    let o111: u64 = tmp1.wrapping_add(c5);
    let o121: u64 = tmp2;
    let o131: u64 = tmp3;
    let o141: u64 = tmp4;
    let l·5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w20, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp00: u64 = crate::fstar::uint128::uint128_to_uint64(l·5) & 0x7ffffffffffffu64;
    let c00: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·5, 51u32));
    let l·6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w21, crate::fstar::uint128::uint64_to_uint128(c00));
    let tmp10: u64 = crate::fstar::uint128::uint128_to_uint64(l·6) & 0x7ffffffffffffu64;
    let c10: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·6, 51u32));
    let l·7: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w22, crate::fstar::uint128::uint64_to_uint128(c10));
    let tmp20: u64 = crate::fstar::uint128::uint128_to_uint64(l·7) & 0x7ffffffffffffu64;
    let c20: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·7, 51u32));
    let l·8: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w23, crate::fstar::uint128::uint64_to_uint128(c20));
    let tmp30: u64 = crate::fstar::uint128::uint128_to_uint64(l·8) & 0x7ffffffffffffu64;
    let c30: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·8, 51u32));
    let l·9: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w24, crate::fstar::uint128::uint64_to_uint128(c30));
    let tmp40: u64 = crate::fstar::uint128::uint128_to_uint64(l·9) & 0x7ffffffffffffu64;
    let c40: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·9, 51u32));
    let l·10: u64 = tmp00.wrapping_add(c40.wrapping_mul(19u64));
    let tmp0·0: u64 = l·10 & 0x7ffffffffffffu64;
    let c50: u64 = l·10.wrapping_shr(51u32);
    let o200: u64 = tmp0·0;
    let o211: u64 = tmp10.wrapping_add(c50);
    let o221: u64 = tmp20;
    let o231: u64 = tmp30;
    let o241: u64 = tmp40;
    let o101: u64 = o100;
    let o112: u64 = o111;
    let o122: u64 = o121;
    let o132: u64 = o131;
    let o142: u64 = o141;
    let o201: u64 = o200;
    let o212: u64 = o211;
    let o222: u64 = o221;
    let o232: u64 = o231;
    let o242: u64 = o241;
    out[0usize] = o101;
    out[1usize] = o112;
    out[2usize] = o122;
    out[3usize] = o132;
    out[4usize] = o142;
    out[5usize] = o201;
    out[6usize] = o212;
    out[7usize] = o222;
    out[8usize] = o232;
    out[9usize] = o242
}

#[inline] pub fn fmul1(out: &mut [u64], f1: &mut [u64], f2: u64) -> ()
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
    let l·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w0, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp0: u64 = crate::fstar::uint128::uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·, 51u32));
    let l·0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w1, crate::fstar::uint128::uint64_to_uint128(c0));
    let tmp1: u64 = crate::fstar::uint128::uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·0, 51u32));
    let l·1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w2, crate::fstar::uint128::uint64_to_uint128(c1));
    let tmp2: u64 = crate::fstar::uint128::uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·1, 51u32));
    let l·2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w3, crate::fstar::uint128::uint64_to_uint128(c2));
    let tmp3: u64 = crate::fstar::uint128::uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·2, 51u32));
    let l·3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(tmp_w4, crate::fstar::uint128::uint64_to_uint128(c3));
    let tmp4: u64 = crate::fstar::uint128::uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·3, 51u32));
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let o0: u64 = tmp0·;
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

#[inline] pub fn fsqr(
    out: &mut [u64],
    f: &mut [u64],
    uu___: &mut [crate::fstar::uint128::uint128]
) ->
    ()
{
    crate::lowstar::ignore::ignore::<&mut [crate::fstar::uint128::uint128]>(uu___);
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let d0: u64 = 2u64.wrapping_mul(f0);
    let d1: u64 = 2u64.wrapping_mul(f1);
    let d2: u64 = 38u64.wrapping_mul(f2);
    let d3: u64 = 19u64.wrapping_mul(f3);
    let d419: u64 = 19u64.wrapping_mul(f4);
    let d4: u64 = 2u64.wrapping_mul(d419);
    let s0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(f0, f0),
                crate::fstar::uint128::mul_wide(d4, f1)
            ),
            crate::fstar::uint128::mul_wide(d2, f3)
        );
    let s1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f1),
                crate::fstar::uint128::mul_wide(d4, f2)
            ),
            crate::fstar::uint128::mul_wide(d3, f3)
        );
    let s2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f2),
                crate::fstar::uint128::mul_wide(f1, f1)
            ),
            crate::fstar::uint128::mul_wide(d4, f3)
        );
    let s3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f3),
                crate::fstar::uint128::mul_wide(d1, f2)
            ),
            crate::fstar::uint128::mul_wide(f4, d419)
        );
    let s4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f4),
                crate::fstar::uint128::mul_wide(d1, f3)
            ),
            crate::fstar::uint128::mul_wide(f2, f2)
        );
    let o0: crate::fstar::uint128::uint128 = s0;
    let o1: crate::fstar::uint128::uint128 = s1;
    let o2: crate::fstar::uint128::uint128 = s2;
    let o3: crate::fstar::uint128::uint128 = s3;
    let o4: crate::fstar::uint128::uint128 = s4;
    let l·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o0, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp0: u64 = crate::fstar::uint128::uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·, 51u32));
    let l·0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o1, crate::fstar::uint128::uint64_to_uint128(c0));
    let tmp1: u64 = crate::fstar::uint128::uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·0, 51u32));
    let l·1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o2, crate::fstar::uint128::uint64_to_uint128(c1));
    let tmp2: u64 = crate::fstar::uint128::uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·1, 51u32));
    let l·2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o3, crate::fstar::uint128::uint64_to_uint128(c2));
    let tmp3: u64 = crate::fstar::uint128::uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·2, 51u32));
    let l·3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o4, crate::fstar::uint128::uint64_to_uint128(c3));
    let tmp4: u64 = crate::fstar::uint128::uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·3, 51u32));
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let o00: u64 = tmp0·;
    let o10: u64 = tmp1.wrapping_add(c5);
    let o20: u64 = tmp2;
    let o30: u64 = tmp3;
    let o40: u64 = tmp4;
    out[0usize] = o00;
    out[1usize] = o10;
    out[2usize] = o20;
    out[3usize] = o30;
    out[4usize] = o40
}

#[inline] pub fn fsqr2(
    out: &mut [u64],
    f: &mut [u64],
    uu___: &mut [crate::fstar::uint128::uint128]
) ->
    ()
{
    crate::lowstar::ignore::ignore::<&mut [crate::fstar::uint128::uint128]>(uu___);
    let f10: u64 = f[0usize];
    let f11: u64 = f[1usize];
    let f12: u64 = f[2usize];
    let f13: u64 = f[3usize];
    let f14: u64 = f[4usize];
    let f20: u64 = f[5usize];
    let f21: u64 = f[6usize];
    let f22: u64 = f[7usize];
    let f23: u64 = f[8usize];
    let f24: u64 = f[9usize];
    let d0: u64 = 2u64.wrapping_mul(f10);
    let d1: u64 = 2u64.wrapping_mul(f11);
    let d2: u64 = 38u64.wrapping_mul(f12);
    let d3: u64 = 19u64.wrapping_mul(f13);
    let d419: u64 = 19u64.wrapping_mul(f14);
    let d4: u64 = 2u64.wrapping_mul(d419);
    let s0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(f10, f10),
                crate::fstar::uint128::mul_wide(d4, f11)
            ),
            crate::fstar::uint128::mul_wide(d2, f13)
        );
    let s1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f11),
                crate::fstar::uint128::mul_wide(d4, f12)
            ),
            crate::fstar::uint128::mul_wide(d3, f13)
        );
    let s2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f12),
                crate::fstar::uint128::mul_wide(f11, f11)
            ),
            crate::fstar::uint128::mul_wide(d4, f13)
        );
    let s3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f13),
                crate::fstar::uint128::mul_wide(d1, f12)
            ),
            crate::fstar::uint128::mul_wide(f14, d419)
        );
    let s4: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d0, f14),
                crate::fstar::uint128::mul_wide(d1, f13)
            ),
            crate::fstar::uint128::mul_wide(f12, f12)
        );
    let o10: crate::fstar::uint128::uint128 = s0;
    let o11: crate::fstar::uint128::uint128 = s1;
    let o12: crate::fstar::uint128::uint128 = s2;
    let o13: crate::fstar::uint128::uint128 = s3;
    let o14: crate::fstar::uint128::uint128 = s4;
    let d00: u64 = 2u64.wrapping_mul(f20);
    let d10: u64 = 2u64.wrapping_mul(f21);
    let d20: u64 = 38u64.wrapping_mul(f22);
    let d30: u64 = 19u64.wrapping_mul(f23);
    let d4190: u64 = 19u64.wrapping_mul(f24);
    let d40: u64 = 2u64.wrapping_mul(d4190);
    let s00: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(f20, f20),
                crate::fstar::uint128::mul_wide(d40, f21)
            ),
            crate::fstar::uint128::mul_wide(d20, f23)
        );
    let s10: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d00, f21),
                crate::fstar::uint128::mul_wide(d40, f22)
            ),
            crate::fstar::uint128::mul_wide(d30, f23)
        );
    let s20: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d00, f22),
                crate::fstar::uint128::mul_wide(f21, f21)
            ),
            crate::fstar::uint128::mul_wide(d40, f23)
        );
    let s30: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d00, f23),
                crate::fstar::uint128::mul_wide(d10, f22)
            ),
            crate::fstar::uint128::mul_wide(f24, d4190)
        );
    let s40: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::mul_wide(d00, f24),
                crate::fstar::uint128::mul_wide(d10, f23)
            ),
            crate::fstar::uint128::mul_wide(f22, f22)
        );
    let o20: crate::fstar::uint128::uint128 = s00;
    let o21: crate::fstar::uint128::uint128 = s10;
    let o22: crate::fstar::uint128::uint128 = s20;
    let o23: crate::fstar::uint128::uint128 = s30;
    let o24: crate::fstar::uint128::uint128 = s40;
    let l·: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o10, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp0: u64 = crate::fstar::uint128::uint128_to_uint64(l·) & 0x7ffffffffffffu64;
    let c0: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·, 51u32));
    let l·0: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o11, crate::fstar::uint128::uint64_to_uint128(c0));
    let tmp1: u64 = crate::fstar::uint128::uint128_to_uint64(l·0) & 0x7ffffffffffffu64;
    let c1: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·0, 51u32));
    let l·1: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o12, crate::fstar::uint128::uint64_to_uint128(c1));
    let tmp2: u64 = crate::fstar::uint128::uint128_to_uint64(l·1) & 0x7ffffffffffffu64;
    let c2: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·1, 51u32));
    let l·2: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o13, crate::fstar::uint128::uint64_to_uint128(c2));
    let tmp3: u64 = crate::fstar::uint128::uint128_to_uint64(l·2) & 0x7ffffffffffffu64;
    let c3: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·2, 51u32));
    let l·3: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o14, crate::fstar::uint128::uint64_to_uint128(c3));
    let tmp4: u64 = crate::fstar::uint128::uint128_to_uint64(l·3) & 0x7ffffffffffffu64;
    let c4: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·3, 51u32));
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let o101: u64 = tmp0·;
    let o111: u64 = tmp1.wrapping_add(c5);
    let o121: u64 = tmp2;
    let o131: u64 = tmp3;
    let o141: u64 = tmp4;
    let l·5: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o20, crate::fstar::uint128::uint64_to_uint128(0u64));
    let tmp00: u64 = crate::fstar::uint128::uint128_to_uint64(l·5) & 0x7ffffffffffffu64;
    let c00: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·5, 51u32));
    let l·6: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o21, crate::fstar::uint128::uint64_to_uint128(c00));
    let tmp10: u64 = crate::fstar::uint128::uint128_to_uint64(l·6) & 0x7ffffffffffffu64;
    let c10: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·6, 51u32));
    let l·7: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o22, crate::fstar::uint128::uint64_to_uint128(c10));
    let tmp20: u64 = crate::fstar::uint128::uint128_to_uint64(l·7) & 0x7ffffffffffffu64;
    let c20: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·7, 51u32));
    let l·8: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o23, crate::fstar::uint128::uint64_to_uint128(c20));
    let tmp30: u64 = crate::fstar::uint128::uint128_to_uint64(l·8) & 0x7ffffffffffffu64;
    let c30: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·8, 51u32));
    let l·9: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add(o24, crate::fstar::uint128::uint64_to_uint128(c30));
    let tmp40: u64 = crate::fstar::uint128::uint128_to_uint64(l·9) & 0x7ffffffffffffu64;
    let c40: u64 =
        crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::shift_right(l·9, 51u32));
    let l·10: u64 = tmp00.wrapping_add(c40.wrapping_mul(19u64));
    let tmp0·0: u64 = l·10 & 0x7ffffffffffffu64;
    let c50: u64 = l·10.wrapping_shr(51u32);
    let o201: u64 = tmp0·0;
    let o211: u64 = tmp10.wrapping_add(c50);
    let o221: u64 = tmp20;
    let o231: u64 = tmp30;
    let o241: u64 = tmp40;
    let o100: u64 = o101;
    let o110: u64 = o111;
    let o120: u64 = o121;
    let o130: u64 = o131;
    let o140: u64 = o141;
    let o200: u64 = o201;
    let o210: u64 = o211;
    let o220: u64 = o221;
    let o230: u64 = o231;
    let o240: u64 = o241;
    out[0usize] = o100;
    out[1usize] = o110;
    out[2usize] = o120;
    out[3usize] = o130;
    out[4usize] = o140;
    out[5usize] = o200;
    out[6usize] = o210;
    out[7usize] = o220;
    out[8usize] = o230;
    out[9usize] = o240
}

pub fn store_felem(u64s: &mut [u64], f: &mut [u64]) -> ()
{
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f3: u64 = f[3usize];
    let f4: u64 = f[4usize];
    let l·: u64 = f0.wrapping_add(0u64);
    let tmp0: u64 = l· & 0x7ffffffffffffu64;
    let c0: u64 = l·.wrapping_shr(51u32);
    let l·0: u64 = f1.wrapping_add(c0);
    let tmp1: u64 = l·0 & 0x7ffffffffffffu64;
    let c1: u64 = l·0.wrapping_shr(51u32);
    let l·1: u64 = f2.wrapping_add(c1);
    let tmp2: u64 = l·1 & 0x7ffffffffffffu64;
    let c2: u64 = l·1.wrapping_shr(51u32);
    let l·2: u64 = f3.wrapping_add(c2);
    let tmp3: u64 = l·2 & 0x7ffffffffffffu64;
    let c3: u64 = l·2.wrapping_shr(51u32);
    let l·3: u64 = f4.wrapping_add(c3);
    let tmp4: u64 = l·3 & 0x7ffffffffffffu64;
    let c4: u64 = l·3.wrapping_shr(51u32);
    let l·4: u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
    let tmp0·: u64 = l·4 & 0x7ffffffffffffu64;
    let c5: u64 = l·4.wrapping_shr(51u32);
    let f01: u64 = tmp0·;
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
    let f0·: u64 = f01.wrapping_sub(mask & 0x7ffffffffffedu64);
    let f1·: u64 = f11.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f2·: u64 = f21.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f3·: u64 = f31.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f4·: u64 = f41.wrapping_sub(mask & 0x7ffffffffffffu64);
    let f02: u64 = f0·;
    let f12: u64 = f1·;
    let f22: u64 = f2·;
    let f32: u64 = f3·;
    let f42: u64 = f4·;
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

#[inline] pub fn cswap2(bit: u64, p1: &mut [u64], p2: &mut [u64]) -> ()
{
    let mask: u64 = 0u64.wrapping_sub(bit);
    for i in 0u32..10u32
    {
        let dummy: u64 = mask & (p1[i as usize] ^ p2[i as usize]);
        p1[i as usize] = p1[i as usize] ^ dummy;
        p2[i as usize] = p2[i as usize] ^ dummy
    }
}
