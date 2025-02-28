#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]
extern "C" {
    fn memcpy(
        _: *mut libc::c_void,
        _: *const libc::c_void,
        _: libc::c_ulong,
    ) -> *mut libc::c_void;
}
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type FStar_UInt128_uint128 = u128;
pub type uint128_t = FStar_UInt128_uint128;
#[inline]
unsafe extern "C" fn load64(mut b: *mut uint8_t) -> uint64_t {
    let mut x: uint64_t = 0;
    memcpy(
        &mut x as *mut uint64_t as *mut libc::c_void,
        b as *const libc::c_void,
        8 as libc::c_int as libc::c_ulong,
    );
    return x;
}
#[inline]
unsafe extern "C" fn store64(mut b: *mut uint8_t, mut i: uint64_t) {
    memcpy(
        b as *mut libc::c_void,
        &mut i as *mut uint64_t as *const libc::c_void,
        8 as libc::c_int as libc::c_ulong,
    );
}
#[inline]
unsafe extern "C" fn FStar_UInt128_add(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_add(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_shift_right(
    mut x: uint128_t,
    mut y: uint32_t,
) -> FStar_UInt128_uint128 {
    return x >> y;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_uint64_to_uint128(
    mut x: uint64_t,
) -> FStar_UInt128_uint128 {
    return x as uint128_t;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_uint128_to_uint64(mut x: uint128_t) -> uint64_t {
    return x as uint64_t;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_mul_wide(
    mut x: uint64_t,
    mut y: uint64_t,
) -> FStar_UInt128_uint128 {
    return x as uint128_t * y as uint128_t;
}
#[inline(never)]
unsafe extern "C" fn FStar_UInt64_eq_mask(mut a: uint64_t, mut b: uint64_t) -> uint64_t {
    let mut x: uint64_t = a ^ b;
    let mut minus_x: uint64_t = (!x).wrapping_add(1 as libc::c_ulonglong);
    let mut x_or_minus_x: uint64_t = x | minus_x;
    let mut xnx: uint64_t = x_or_minus_x >> 63 as libc::c_uint;
    return xnx.wrapping_sub(1 as libc::c_ulonglong);
}
#[inline(never)]
unsafe extern "C" fn FStar_UInt64_gte_mask(
    mut a: uint64_t,
    mut b: uint64_t,
) -> uint64_t {
    let mut x: uint64_t = a;
    let mut y: uint64_t = b;
    let mut x_xor_y: uint64_t = x ^ y;
    let mut x_sub_y: uint64_t = x.wrapping_sub(y);
    let mut x_sub_y_xor_y: uint64_t = x_sub_y ^ y;
    let mut q: uint64_t = x_xor_y | x_sub_y_xor_y;
    let mut x_xor_q: uint64_t = x ^ q;
    let mut x_xor_q_: uint64_t = x_xor_q >> 63 as libc::c_uint;
    return x_xor_q_.wrapping_sub(1 as libc::c_ulonglong);
}
#[inline(never)]
unsafe extern "C" fn FStar_UInt8_eq_mask(mut a: uint8_t, mut b: uint8_t) -> uint8_t {
    let mut x: uint8_t = (a as uint32_t ^ b as uint32_t) as uint8_t;
    let mut minus_x: uint8_t = (!(x as libc::c_int) as uint32_t)
        .wrapping_add(1 as libc::c_uint) as uint8_t;
    let mut x_or_minus_x: uint8_t = (x as uint32_t | minus_x as uint32_t) as uint8_t;
    let mut xnx: uint8_t = (x_or_minus_x as uint32_t >> 7 as libc::c_uint) as uint8_t;
    return (xnx as uint32_t).wrapping_sub(1 as libc::c_uint) as uint8_t;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fadd(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) {
    let mut f10: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut f20: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut f11: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut f21: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut f12: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut f22: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut f13: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut f23: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut f14: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut f24: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    *out.offset(0 as libc::c_uint as isize) = f10.wrapping_add(f20);
    *out.offset(1 as libc::c_uint as isize) = f11.wrapping_add(f21);
    *out.offset(2 as libc::c_uint as isize) = f12.wrapping_add(f22);
    *out.offset(3 as libc::c_uint as isize) = f13.wrapping_add(f23);
    *out.offset(4 as libc::c_uint as isize) = f14.wrapping_add(f24);
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fsub(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
) {
    let mut f10: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut f20: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut f11: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut f21: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut f12: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut f22: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut f13: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut f23: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut f14: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut f24: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    *out
        .offset(
            0 as libc::c_uint as isize,
        ) = f10.wrapping_add(0x3fffffffffff68 as libc::c_ulonglong).wrapping_sub(f20);
    *out
        .offset(
            1 as libc::c_uint as isize,
        ) = f11.wrapping_add(0x3ffffffffffff8 as libc::c_ulonglong).wrapping_sub(f21);
    *out
        .offset(
            2 as libc::c_uint as isize,
        ) = f12.wrapping_add(0x3ffffffffffff8 as libc::c_ulonglong).wrapping_sub(f22);
    *out
        .offset(
            3 as libc::c_uint as isize,
        ) = f13.wrapping_add(0x3ffffffffffff8 as libc::c_ulonglong).wrapping_sub(f23);
    *out
        .offset(
            4 as libc::c_uint as isize,
        ) = f14.wrapping_add(0x3ffffffffffff8 as libc::c_ulonglong).wrapping_sub(f24);
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fmul(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
    mut uu___: *mut FStar_UInt128_uint128,
) {
    let mut f10: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut f11: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut f12: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut f13: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut f14: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut f20: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut f21: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut f22: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut f23: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut f24: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    let mut tmp1: uint64_t = f21.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp2: uint64_t = f22.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp3: uint64_t = f23.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp4: uint64_t = f24.wrapping_mul(19 as libc::c_ulonglong);
    let mut o00: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f20);
    let mut o10: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f21);
    let mut o20: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f22);
    let mut o30: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f23);
    let mut o40: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f24);
    let mut o01: FStar_UInt128_uint128 = FStar_UInt128_add(
        o00,
        FStar_UInt128_mul_wide(f11, tmp4),
    );
    let mut o11: FStar_UInt128_uint128 = FStar_UInt128_add(
        o10,
        FStar_UInt128_mul_wide(f11, f20),
    );
    let mut o21: FStar_UInt128_uint128 = FStar_UInt128_add(
        o20,
        FStar_UInt128_mul_wide(f11, f21),
    );
    let mut o31: FStar_UInt128_uint128 = FStar_UInt128_add(
        o30,
        FStar_UInt128_mul_wide(f11, f22),
    );
    let mut o41: FStar_UInt128_uint128 = FStar_UInt128_add(
        o40,
        FStar_UInt128_mul_wide(f11, f23),
    );
    let mut o02: FStar_UInt128_uint128 = FStar_UInt128_add(
        o01,
        FStar_UInt128_mul_wide(f12, tmp3),
    );
    let mut o12: FStar_UInt128_uint128 = FStar_UInt128_add(
        o11,
        FStar_UInt128_mul_wide(f12, tmp4),
    );
    let mut o22: FStar_UInt128_uint128 = FStar_UInt128_add(
        o21,
        FStar_UInt128_mul_wide(f12, f20),
    );
    let mut o32: FStar_UInt128_uint128 = FStar_UInt128_add(
        o31,
        FStar_UInt128_mul_wide(f12, f21),
    );
    let mut o42: FStar_UInt128_uint128 = FStar_UInt128_add(
        o41,
        FStar_UInt128_mul_wide(f12, f22),
    );
    let mut o03: FStar_UInt128_uint128 = FStar_UInt128_add(
        o02,
        FStar_UInt128_mul_wide(f13, tmp2),
    );
    let mut o13: FStar_UInt128_uint128 = FStar_UInt128_add(
        o12,
        FStar_UInt128_mul_wide(f13, tmp3),
    );
    let mut o23: FStar_UInt128_uint128 = FStar_UInt128_add(
        o22,
        FStar_UInt128_mul_wide(f13, tmp4),
    );
    let mut o33: FStar_UInt128_uint128 = FStar_UInt128_add(
        o32,
        FStar_UInt128_mul_wide(f13, f20),
    );
    let mut o43: FStar_UInt128_uint128 = FStar_UInt128_add(
        o42,
        FStar_UInt128_mul_wide(f13, f21),
    );
    let mut o04: FStar_UInt128_uint128 = FStar_UInt128_add(
        o03,
        FStar_UInt128_mul_wide(f14, tmp1),
    );
    let mut o14: FStar_UInt128_uint128 = FStar_UInt128_add(
        o13,
        FStar_UInt128_mul_wide(f14, tmp2),
    );
    let mut o24: FStar_UInt128_uint128 = FStar_UInt128_add(
        o23,
        FStar_UInt128_mul_wide(f14, tmp3),
    );
    let mut o34: FStar_UInt128_uint128 = FStar_UInt128_add(
        o33,
        FStar_UInt128_mul_wide(f14, tmp4),
    );
    let mut o44: FStar_UInt128_uint128 = FStar_UInt128_add(
        o43,
        FStar_UInt128_mul_wide(f14, f20),
    );
    let mut tmp_w0: FStar_UInt128_uint128 = o04;
    let mut tmp_w1: FStar_UInt128_uint128 = o14;
    let mut tmp_w2: FStar_UInt128_uint128 = o24;
    let mut tmp_w3: FStar_UInt128_uint128 = o34;
    let mut tmp_w4: FStar_UInt128_uint128 = o44;
    let mut l_: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w0,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp01: uint64_t = FStar_UInt128_uint128_to_uint64(l_)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_, 51 as libc::c_uint),
    );
    let mut l_0: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w1,
        FStar_UInt128_uint64_to_uint128(c0),
    );
    let mut tmp11: uint64_t = FStar_UInt128_uint128_to_uint64(l_0)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_0, 51 as libc::c_uint),
    );
    let mut l_1: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w2,
        FStar_UInt128_uint64_to_uint128(c1),
    );
    let mut tmp21: uint64_t = FStar_UInt128_uint128_to_uint64(l_1)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_1, 51 as libc::c_uint),
    );
    let mut l_2: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w3,
        FStar_UInt128_uint64_to_uint128(c2),
    );
    let mut tmp31: uint64_t = FStar_UInt128_uint128_to_uint64(l_2)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c3: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_2, 51 as libc::c_uint),
    );
    let mut l_3: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w4,
        FStar_UInt128_uint64_to_uint128(c3),
    );
    let mut tmp41: uint64_t = FStar_UInt128_uint128_to_uint64(l_3)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c4: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_3, 51 as libc::c_uint),
    );
    let mut l_4: uint64_t = tmp01.wrapping_add(c4.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_: uint64_t = l_4 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c5: uint64_t = l_4 >> 51 as libc::c_uint;
    let mut o0: uint64_t = tmp0_;
    let mut o1: uint64_t = tmp11.wrapping_add(c5);
    let mut o2: uint64_t = tmp21;
    let mut o3: uint64_t = tmp31;
    let mut o4: uint64_t = tmp41;
    *out.offset(0 as libc::c_uint as isize) = o0;
    *out.offset(1 as libc::c_uint as isize) = o1;
    *out.offset(2 as libc::c_uint as isize) = o2;
    *out.offset(3 as libc::c_uint as isize) = o3;
    *out.offset(4 as libc::c_uint as isize) = o4;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fmul2(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: *mut uint64_t,
    mut uu___: *mut FStar_UInt128_uint128,
) {
    let mut f10: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut f11: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut f12: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut f13: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut f14: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut f20: uint64_t = *f2.offset(0 as libc::c_uint as isize);
    let mut f21: uint64_t = *f2.offset(1 as libc::c_uint as isize);
    let mut f22: uint64_t = *f2.offset(2 as libc::c_uint as isize);
    let mut f23: uint64_t = *f2.offset(3 as libc::c_uint as isize);
    let mut f24: uint64_t = *f2.offset(4 as libc::c_uint as isize);
    let mut f30: uint64_t = *f1.offset(5 as libc::c_uint as isize);
    let mut f31: uint64_t = *f1.offset(6 as libc::c_uint as isize);
    let mut f32: uint64_t = *f1.offset(7 as libc::c_uint as isize);
    let mut f33: uint64_t = *f1.offset(8 as libc::c_uint as isize);
    let mut f34: uint64_t = *f1.offset(9 as libc::c_uint as isize);
    let mut f40: uint64_t = *f2.offset(5 as libc::c_uint as isize);
    let mut f41: uint64_t = *f2.offset(6 as libc::c_uint as isize);
    let mut f42: uint64_t = *f2.offset(7 as libc::c_uint as isize);
    let mut f43: uint64_t = *f2.offset(8 as libc::c_uint as isize);
    let mut f44: uint64_t = *f2.offset(9 as libc::c_uint as isize);
    let mut tmp11: uint64_t = f21.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp12: uint64_t = f22.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp13: uint64_t = f23.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp14: uint64_t = f24.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp21: uint64_t = f41.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp22: uint64_t = f42.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp23: uint64_t = f43.wrapping_mul(19 as libc::c_ulonglong);
    let mut tmp24: uint64_t = f44.wrapping_mul(19 as libc::c_ulonglong);
    let mut o00: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f20);
    let mut o15: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f21);
    let mut o25: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f22);
    let mut o30: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f23);
    let mut o40: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f10, f24);
    let mut o010: FStar_UInt128_uint128 = FStar_UInt128_add(
        o00,
        FStar_UInt128_mul_wide(f11, tmp14),
    );
    let mut o110: FStar_UInt128_uint128 = FStar_UInt128_add(
        o15,
        FStar_UInt128_mul_wide(f11, f20),
    );
    let mut o210: FStar_UInt128_uint128 = FStar_UInt128_add(
        o25,
        FStar_UInt128_mul_wide(f11, f21),
    );
    let mut o310: FStar_UInt128_uint128 = FStar_UInt128_add(
        o30,
        FStar_UInt128_mul_wide(f11, f22),
    );
    let mut o410: FStar_UInt128_uint128 = FStar_UInt128_add(
        o40,
        FStar_UInt128_mul_wide(f11, f23),
    );
    let mut o020: FStar_UInt128_uint128 = FStar_UInt128_add(
        o010,
        FStar_UInt128_mul_wide(f12, tmp13),
    );
    let mut o120: FStar_UInt128_uint128 = FStar_UInt128_add(
        o110,
        FStar_UInt128_mul_wide(f12, tmp14),
    );
    let mut o220: FStar_UInt128_uint128 = FStar_UInt128_add(
        o210,
        FStar_UInt128_mul_wide(f12, f20),
    );
    let mut o320: FStar_UInt128_uint128 = FStar_UInt128_add(
        o310,
        FStar_UInt128_mul_wide(f12, f21),
    );
    let mut o420: FStar_UInt128_uint128 = FStar_UInt128_add(
        o410,
        FStar_UInt128_mul_wide(f12, f22),
    );
    let mut o030: FStar_UInt128_uint128 = FStar_UInt128_add(
        o020,
        FStar_UInt128_mul_wide(f13, tmp12),
    );
    let mut o130: FStar_UInt128_uint128 = FStar_UInt128_add(
        o120,
        FStar_UInt128_mul_wide(f13, tmp13),
    );
    let mut o230: FStar_UInt128_uint128 = FStar_UInt128_add(
        o220,
        FStar_UInt128_mul_wide(f13, tmp14),
    );
    let mut o330: FStar_UInt128_uint128 = FStar_UInt128_add(
        o320,
        FStar_UInt128_mul_wide(f13, f20),
    );
    let mut o430: FStar_UInt128_uint128 = FStar_UInt128_add(
        o420,
        FStar_UInt128_mul_wide(f13, f21),
    );
    let mut o040: FStar_UInt128_uint128 = FStar_UInt128_add(
        o030,
        FStar_UInt128_mul_wide(f14, tmp11),
    );
    let mut o140: FStar_UInt128_uint128 = FStar_UInt128_add(
        o130,
        FStar_UInt128_mul_wide(f14, tmp12),
    );
    let mut o240: FStar_UInt128_uint128 = FStar_UInt128_add(
        o230,
        FStar_UInt128_mul_wide(f14, tmp13),
    );
    let mut o340: FStar_UInt128_uint128 = FStar_UInt128_add(
        o330,
        FStar_UInt128_mul_wide(f14, tmp14),
    );
    let mut o440: FStar_UInt128_uint128 = FStar_UInt128_add(
        o430,
        FStar_UInt128_mul_wide(f14, f20),
    );
    let mut tmp_w10: FStar_UInt128_uint128 = o040;
    let mut tmp_w11: FStar_UInt128_uint128 = o140;
    let mut tmp_w12: FStar_UInt128_uint128 = o240;
    let mut tmp_w13: FStar_UInt128_uint128 = o340;
    let mut tmp_w14: FStar_UInt128_uint128 = o440;
    let mut o0: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f30, f40);
    let mut o1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f30, f41);
    let mut o2: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f30, f42);
    let mut o3: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f30, f43);
    let mut o4: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f30, f44);
    let mut o01: FStar_UInt128_uint128 = FStar_UInt128_add(
        o0,
        FStar_UInt128_mul_wide(f31, tmp24),
    );
    let mut o111: FStar_UInt128_uint128 = FStar_UInt128_add(
        o1,
        FStar_UInt128_mul_wide(f31, f40),
    );
    let mut o211: FStar_UInt128_uint128 = FStar_UInt128_add(
        o2,
        FStar_UInt128_mul_wide(f31, f41),
    );
    let mut o31: FStar_UInt128_uint128 = FStar_UInt128_add(
        o3,
        FStar_UInt128_mul_wide(f31, f42),
    );
    let mut o41: FStar_UInt128_uint128 = FStar_UInt128_add(
        o4,
        FStar_UInt128_mul_wide(f31, f43),
    );
    let mut o02: FStar_UInt128_uint128 = FStar_UInt128_add(
        o01,
        FStar_UInt128_mul_wide(f32, tmp23),
    );
    let mut o121: FStar_UInt128_uint128 = FStar_UInt128_add(
        o111,
        FStar_UInt128_mul_wide(f32, tmp24),
    );
    let mut o221: FStar_UInt128_uint128 = FStar_UInt128_add(
        o211,
        FStar_UInt128_mul_wide(f32, f40),
    );
    let mut o32: FStar_UInt128_uint128 = FStar_UInt128_add(
        o31,
        FStar_UInt128_mul_wide(f32, f41),
    );
    let mut o42: FStar_UInt128_uint128 = FStar_UInt128_add(
        o41,
        FStar_UInt128_mul_wide(f32, f42),
    );
    let mut o03: FStar_UInt128_uint128 = FStar_UInt128_add(
        o02,
        FStar_UInt128_mul_wide(f33, tmp22),
    );
    let mut o131: FStar_UInt128_uint128 = FStar_UInt128_add(
        o121,
        FStar_UInt128_mul_wide(f33, tmp23),
    );
    let mut o231: FStar_UInt128_uint128 = FStar_UInt128_add(
        o221,
        FStar_UInt128_mul_wide(f33, tmp24),
    );
    let mut o33: FStar_UInt128_uint128 = FStar_UInt128_add(
        o32,
        FStar_UInt128_mul_wide(f33, f40),
    );
    let mut o43: FStar_UInt128_uint128 = FStar_UInt128_add(
        o42,
        FStar_UInt128_mul_wide(f33, f41),
    );
    let mut o04: FStar_UInt128_uint128 = FStar_UInt128_add(
        o03,
        FStar_UInt128_mul_wide(f34, tmp21),
    );
    let mut o141: FStar_UInt128_uint128 = FStar_UInt128_add(
        o131,
        FStar_UInt128_mul_wide(f34, tmp22),
    );
    let mut o241: FStar_UInt128_uint128 = FStar_UInt128_add(
        o231,
        FStar_UInt128_mul_wide(f34, tmp23),
    );
    let mut o34: FStar_UInt128_uint128 = FStar_UInt128_add(
        o33,
        FStar_UInt128_mul_wide(f34, tmp24),
    );
    let mut o44: FStar_UInt128_uint128 = FStar_UInt128_add(
        o43,
        FStar_UInt128_mul_wide(f34, f40),
    );
    let mut tmp_w20: FStar_UInt128_uint128 = o04;
    let mut tmp_w21: FStar_UInt128_uint128 = o141;
    let mut tmp_w22: FStar_UInt128_uint128 = o241;
    let mut tmp_w23: FStar_UInt128_uint128 = o34;
    let mut tmp_w24: FStar_UInt128_uint128 = o44;
    let mut l_: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w10,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp00: uint64_t = FStar_UInt128_uint128_to_uint64(l_)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c00: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_, 51 as libc::c_uint),
    );
    let mut l_0: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w11,
        FStar_UInt128_uint64_to_uint128(c00),
    );
    let mut tmp10: uint64_t = FStar_UInt128_uint128_to_uint64(l_0)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c10: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_0, 51 as libc::c_uint),
    );
    let mut l_1: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w12,
        FStar_UInt128_uint64_to_uint128(c10),
    );
    let mut tmp20: uint64_t = FStar_UInt128_uint128_to_uint64(l_1)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c20: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_1, 51 as libc::c_uint),
    );
    let mut l_2: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w13,
        FStar_UInt128_uint64_to_uint128(c20),
    );
    let mut tmp30: uint64_t = FStar_UInt128_uint128_to_uint64(l_2)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c30: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_2, 51 as libc::c_uint),
    );
    let mut l_3: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w14,
        FStar_UInt128_uint64_to_uint128(c30),
    );
    let mut tmp40: uint64_t = FStar_UInt128_uint128_to_uint64(l_3)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c40: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_3, 51 as libc::c_uint),
    );
    let mut l_4: uint64_t = tmp00
        .wrapping_add(c40.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_: uint64_t = l_4 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c50: uint64_t = l_4 >> 51 as libc::c_uint;
    let mut o100: uint64_t = tmp0_;
    let mut o112: uint64_t = tmp10.wrapping_add(c50);
    let mut o122: uint64_t = tmp20;
    let mut o132: uint64_t = tmp30;
    let mut o142: uint64_t = tmp40;
    let mut l_5: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w20,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp0: uint64_t = FStar_UInt128_uint128_to_uint64(l_5)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_5, 51 as libc::c_uint),
    );
    let mut l_6: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w21,
        FStar_UInt128_uint64_to_uint128(c0),
    );
    let mut tmp1: uint64_t = FStar_UInt128_uint128_to_uint64(l_6)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_6, 51 as libc::c_uint),
    );
    let mut l_7: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w22,
        FStar_UInt128_uint64_to_uint128(c1),
    );
    let mut tmp2: uint64_t = FStar_UInt128_uint128_to_uint64(l_7)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_7, 51 as libc::c_uint),
    );
    let mut l_8: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w23,
        FStar_UInt128_uint64_to_uint128(c2),
    );
    let mut tmp3: uint64_t = FStar_UInt128_uint128_to_uint64(l_8)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c3: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_8, 51 as libc::c_uint),
    );
    let mut l_9: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w24,
        FStar_UInt128_uint64_to_uint128(c3),
    );
    let mut tmp4: uint64_t = FStar_UInt128_uint128_to_uint64(l_9)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c4: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_9, 51 as libc::c_uint),
    );
    let mut l_10: uint64_t = tmp0.wrapping_add(c4.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_0: uint64_t = l_10 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c5: uint64_t = l_10 >> 51 as libc::c_uint;
    let mut o200: uint64_t = tmp0_0;
    let mut o212: uint64_t = tmp1.wrapping_add(c5);
    let mut o222: uint64_t = tmp2;
    let mut o232: uint64_t = tmp3;
    let mut o242: uint64_t = tmp4;
    let mut o10: uint64_t = o100;
    let mut o11: uint64_t = o112;
    let mut o12: uint64_t = o122;
    let mut o13: uint64_t = o132;
    let mut o14: uint64_t = o142;
    let mut o20: uint64_t = o200;
    let mut o21: uint64_t = o212;
    let mut o22: uint64_t = o222;
    let mut o23: uint64_t = o232;
    let mut o24: uint64_t = o242;
    *out.offset(0 as libc::c_uint as isize) = o10;
    *out.offset(1 as libc::c_uint as isize) = o11;
    *out.offset(2 as libc::c_uint as isize) = o12;
    *out.offset(3 as libc::c_uint as isize) = o13;
    *out.offset(4 as libc::c_uint as isize) = o14;
    *out.offset(5 as libc::c_uint as isize) = o20;
    *out.offset(6 as libc::c_uint as isize) = o21;
    *out.offset(7 as libc::c_uint as isize) = o22;
    *out.offset(8 as libc::c_uint as isize) = o23;
    *out.offset(9 as libc::c_uint as isize) = o24;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fmul1(
    mut out: *mut uint64_t,
    mut f1: *mut uint64_t,
    mut f2: uint64_t,
) {
    let mut f10: uint64_t = *f1.offset(0 as libc::c_uint as isize);
    let mut f11: uint64_t = *f1.offset(1 as libc::c_uint as isize);
    let mut f12: uint64_t = *f1.offset(2 as libc::c_uint as isize);
    let mut f13: uint64_t = *f1.offset(3 as libc::c_uint as isize);
    let mut f14: uint64_t = *f1.offset(4 as libc::c_uint as isize);
    let mut tmp_w0: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f2, f10);
    let mut tmp_w1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f2, f11);
    let mut tmp_w2: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f2, f12);
    let mut tmp_w3: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f2, f13);
    let mut tmp_w4: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(f2, f14);
    let mut l_: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w0,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp0: uint64_t = FStar_UInt128_uint128_to_uint64(l_)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_, 51 as libc::c_uint),
    );
    let mut l_0: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w1,
        FStar_UInt128_uint64_to_uint128(c0),
    );
    let mut tmp1: uint64_t = FStar_UInt128_uint128_to_uint64(l_0)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_0, 51 as libc::c_uint),
    );
    let mut l_1: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w2,
        FStar_UInt128_uint64_to_uint128(c1),
    );
    let mut tmp2: uint64_t = FStar_UInt128_uint128_to_uint64(l_1)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_1, 51 as libc::c_uint),
    );
    let mut l_2: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w3,
        FStar_UInt128_uint64_to_uint128(c2),
    );
    let mut tmp3: uint64_t = FStar_UInt128_uint128_to_uint64(l_2)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c3: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_2, 51 as libc::c_uint),
    );
    let mut l_3: FStar_UInt128_uint128 = FStar_UInt128_add(
        tmp_w4,
        FStar_UInt128_uint64_to_uint128(c3),
    );
    let mut tmp4: uint64_t = FStar_UInt128_uint128_to_uint64(l_3)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c4: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_3, 51 as libc::c_uint),
    );
    let mut l_4: uint64_t = tmp0.wrapping_add(c4.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_: uint64_t = l_4 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c5: uint64_t = l_4 >> 51 as libc::c_uint;
    let mut o0: uint64_t = tmp0_;
    let mut o1: uint64_t = tmp1.wrapping_add(c5);
    let mut o2: uint64_t = tmp2;
    let mut o3: uint64_t = tmp3;
    let mut o4: uint64_t = tmp4;
    *out.offset(0 as libc::c_uint as isize) = o0;
    *out.offset(1 as libc::c_uint as isize) = o1;
    *out.offset(2 as libc::c_uint as isize) = o2;
    *out.offset(3 as libc::c_uint as isize) = o3;
    *out.offset(4 as libc::c_uint as isize) = o4;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fsqr(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
    mut uu___: *mut FStar_UInt128_uint128,
) {
    let mut f0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut d0: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(f0);
    let mut d1: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(f1);
    let mut d2: uint64_t = (38 as libc::c_ulonglong).wrapping_mul(f2);
    let mut d3: uint64_t = (19 as libc::c_ulonglong).wrapping_mul(f3);
    let mut d419: uint64_t = (19 as libc::c_ulonglong).wrapping_mul(f4);
    let mut d4: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(d419);
    let mut s0: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(f0, f0),
            FStar_UInt128_mul_wide(d4, f1),
        ),
        FStar_UInt128_mul_wide(d2, f3),
    );
    let mut s1: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f1),
            FStar_UInt128_mul_wide(d4, f2),
        ),
        FStar_UInt128_mul_wide(d3, f3),
    );
    let mut s2: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f2),
            FStar_UInt128_mul_wide(f1, f1),
        ),
        FStar_UInt128_mul_wide(d4, f3),
    );
    let mut s3: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f3),
            FStar_UInt128_mul_wide(d1, f2),
        ),
        FStar_UInt128_mul_wide(f4, d419),
    );
    let mut s4: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f4),
            FStar_UInt128_mul_wide(d1, f3),
        ),
        FStar_UInt128_mul_wide(f2, f2),
    );
    let mut o00: FStar_UInt128_uint128 = s0;
    let mut o10: FStar_UInt128_uint128 = s1;
    let mut o20: FStar_UInt128_uint128 = s2;
    let mut o30: FStar_UInt128_uint128 = s3;
    let mut o40: FStar_UInt128_uint128 = s4;
    let mut l_: FStar_UInt128_uint128 = FStar_UInt128_add(
        o00,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp0: uint64_t = FStar_UInt128_uint128_to_uint64(l_)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_, 51 as libc::c_uint),
    );
    let mut l_0: FStar_UInt128_uint128 = FStar_UInt128_add(
        o10,
        FStar_UInt128_uint64_to_uint128(c0),
    );
    let mut tmp1: uint64_t = FStar_UInt128_uint128_to_uint64(l_0)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_0, 51 as libc::c_uint),
    );
    let mut l_1: FStar_UInt128_uint128 = FStar_UInt128_add(
        o20,
        FStar_UInt128_uint64_to_uint128(c1),
    );
    let mut tmp2: uint64_t = FStar_UInt128_uint128_to_uint64(l_1)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_1, 51 as libc::c_uint),
    );
    let mut l_2: FStar_UInt128_uint128 = FStar_UInt128_add(
        o30,
        FStar_UInt128_uint64_to_uint128(c2),
    );
    let mut tmp3: uint64_t = FStar_UInt128_uint128_to_uint64(l_2)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c3: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_2, 51 as libc::c_uint),
    );
    let mut l_3: FStar_UInt128_uint128 = FStar_UInt128_add(
        o40,
        FStar_UInt128_uint64_to_uint128(c3),
    );
    let mut tmp4: uint64_t = FStar_UInt128_uint128_to_uint64(l_3)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c4: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_3, 51 as libc::c_uint),
    );
    let mut l_4: uint64_t = tmp0.wrapping_add(c4.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_: uint64_t = l_4 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c5: uint64_t = l_4 >> 51 as libc::c_uint;
    let mut o0: uint64_t = tmp0_;
    let mut o1: uint64_t = tmp1.wrapping_add(c5);
    let mut o2: uint64_t = tmp2;
    let mut o3: uint64_t = tmp3;
    let mut o4: uint64_t = tmp4;
    *out.offset(0 as libc::c_uint as isize) = o0;
    *out.offset(1 as libc::c_uint as isize) = o1;
    *out.offset(2 as libc::c_uint as isize) = o2;
    *out.offset(3 as libc::c_uint as isize) = o3;
    *out.offset(4 as libc::c_uint as isize) = o4;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_fsqr2(
    mut out: *mut uint64_t,
    mut f: *mut uint64_t,
    mut uu___: *mut FStar_UInt128_uint128,
) {
    let mut f10: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f11: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f12: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f13: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f14: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut f20: uint64_t = *f.offset(5 as libc::c_uint as isize);
    let mut f21: uint64_t = *f.offset(6 as libc::c_uint as isize);
    let mut f22: uint64_t = *f.offset(7 as libc::c_uint as isize);
    let mut f23: uint64_t = *f.offset(8 as libc::c_uint as isize);
    let mut f24: uint64_t = *f.offset(9 as libc::c_uint as isize);
    let mut d00: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(f10);
    let mut d10: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(f11);
    let mut d20: uint64_t = (38 as libc::c_ulonglong).wrapping_mul(f12);
    let mut d30: uint64_t = (19 as libc::c_ulonglong).wrapping_mul(f13);
    let mut d4190: uint64_t = (19 as libc::c_ulonglong).wrapping_mul(f14);
    let mut d40: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(d4190);
    let mut s00: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(f10, f10),
            FStar_UInt128_mul_wide(d40, f11),
        ),
        FStar_UInt128_mul_wide(d20, f13),
    );
    let mut s10: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d00, f11),
            FStar_UInt128_mul_wide(d40, f12),
        ),
        FStar_UInt128_mul_wide(d30, f13),
    );
    let mut s20: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d00, f12),
            FStar_UInt128_mul_wide(f11, f11),
        ),
        FStar_UInt128_mul_wide(d40, f13),
    );
    let mut s30: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d00, f13),
            FStar_UInt128_mul_wide(d10, f12),
        ),
        FStar_UInt128_mul_wide(f14, d4190),
    );
    let mut s40: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d00, f14),
            FStar_UInt128_mul_wide(d10, f13),
        ),
        FStar_UInt128_mul_wide(f12, f12),
    );
    let mut o100: FStar_UInt128_uint128 = s00;
    let mut o110: FStar_UInt128_uint128 = s10;
    let mut o120: FStar_UInt128_uint128 = s20;
    let mut o130: FStar_UInt128_uint128 = s30;
    let mut o140: FStar_UInt128_uint128 = s40;
    let mut d0: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(f20);
    let mut d1: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(f21);
    let mut d2: uint64_t = (38 as libc::c_ulonglong).wrapping_mul(f22);
    let mut d3: uint64_t = (19 as libc::c_ulonglong).wrapping_mul(f23);
    let mut d419: uint64_t = (19 as libc::c_ulonglong).wrapping_mul(f24);
    let mut d4: uint64_t = (2 as libc::c_ulonglong).wrapping_mul(d419);
    let mut s0: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(f20, f20),
            FStar_UInt128_mul_wide(d4, f21),
        ),
        FStar_UInt128_mul_wide(d2, f23),
    );
    let mut s1: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f21),
            FStar_UInt128_mul_wide(d4, f22),
        ),
        FStar_UInt128_mul_wide(d3, f23),
    );
    let mut s2: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f22),
            FStar_UInt128_mul_wide(f21, f21),
        ),
        FStar_UInt128_mul_wide(d4, f23),
    );
    let mut s3: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f23),
            FStar_UInt128_mul_wide(d1, f22),
        ),
        FStar_UInt128_mul_wide(f24, d419),
    );
    let mut s4: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(d0, f24),
            FStar_UInt128_mul_wide(d1, f23),
        ),
        FStar_UInt128_mul_wide(f22, f22),
    );
    let mut o200: FStar_UInt128_uint128 = s0;
    let mut o210: FStar_UInt128_uint128 = s1;
    let mut o220: FStar_UInt128_uint128 = s2;
    let mut o230: FStar_UInt128_uint128 = s3;
    let mut o240: FStar_UInt128_uint128 = s4;
    let mut l_: FStar_UInt128_uint128 = FStar_UInt128_add(
        o100,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp00: uint64_t = FStar_UInt128_uint128_to_uint64(l_)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c00: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_, 51 as libc::c_uint),
    );
    let mut l_0: FStar_UInt128_uint128 = FStar_UInt128_add(
        o110,
        FStar_UInt128_uint64_to_uint128(c00),
    );
    let mut tmp10: uint64_t = FStar_UInt128_uint128_to_uint64(l_0)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c10: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_0, 51 as libc::c_uint),
    );
    let mut l_1: FStar_UInt128_uint128 = FStar_UInt128_add(
        o120,
        FStar_UInt128_uint64_to_uint128(c10),
    );
    let mut tmp20: uint64_t = FStar_UInt128_uint128_to_uint64(l_1)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c20: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_1, 51 as libc::c_uint),
    );
    let mut l_2: FStar_UInt128_uint128 = FStar_UInt128_add(
        o130,
        FStar_UInt128_uint64_to_uint128(c20),
    );
    let mut tmp30: uint64_t = FStar_UInt128_uint128_to_uint64(l_2)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c30: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_2, 51 as libc::c_uint),
    );
    let mut l_3: FStar_UInt128_uint128 = FStar_UInt128_add(
        o140,
        FStar_UInt128_uint64_to_uint128(c30),
    );
    let mut tmp40: uint64_t = FStar_UInt128_uint128_to_uint64(l_3)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c40: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_3, 51 as libc::c_uint),
    );
    let mut l_4: uint64_t = tmp00
        .wrapping_add(c40.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_: uint64_t = l_4 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c50: uint64_t = l_4 >> 51 as libc::c_uint;
    let mut o101: uint64_t = tmp0_;
    let mut o111: uint64_t = tmp10.wrapping_add(c50);
    let mut o121: uint64_t = tmp20;
    let mut o131: uint64_t = tmp30;
    let mut o141: uint64_t = tmp40;
    let mut l_5: FStar_UInt128_uint128 = FStar_UInt128_add(
        o200,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
    );
    let mut tmp0: uint64_t = FStar_UInt128_uint128_to_uint64(l_5)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_5, 51 as libc::c_uint),
    );
    let mut l_6: FStar_UInt128_uint128 = FStar_UInt128_add(
        o210,
        FStar_UInt128_uint64_to_uint128(c0),
    );
    let mut tmp1: uint64_t = FStar_UInt128_uint128_to_uint64(l_6)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_6, 51 as libc::c_uint),
    );
    let mut l_7: FStar_UInt128_uint128 = FStar_UInt128_add(
        o220,
        FStar_UInt128_uint64_to_uint128(c1),
    );
    let mut tmp2: uint64_t = FStar_UInt128_uint128_to_uint64(l_7)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_7, 51 as libc::c_uint),
    );
    let mut l_8: FStar_UInt128_uint128 = FStar_UInt128_add(
        o230,
        FStar_UInt128_uint64_to_uint128(c2),
    );
    let mut tmp3: uint64_t = FStar_UInt128_uint128_to_uint64(l_8)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c3: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_8, 51 as libc::c_uint),
    );
    let mut l_9: FStar_UInt128_uint128 = FStar_UInt128_add(
        o240,
        FStar_UInt128_uint64_to_uint128(c3),
    );
    let mut tmp4: uint64_t = FStar_UInt128_uint128_to_uint64(l_9)
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c4: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(l_9, 51 as libc::c_uint),
    );
    let mut l_10: uint64_t = tmp0.wrapping_add(c4.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_0: uint64_t = l_10 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c5: uint64_t = l_10 >> 51 as libc::c_uint;
    let mut o201: uint64_t = tmp0_0;
    let mut o211: uint64_t = tmp1.wrapping_add(c5);
    let mut o221: uint64_t = tmp2;
    let mut o231: uint64_t = tmp3;
    let mut o241: uint64_t = tmp4;
    let mut o10: uint64_t = o101;
    let mut o11: uint64_t = o111;
    let mut o12: uint64_t = o121;
    let mut o13: uint64_t = o131;
    let mut o14: uint64_t = o141;
    let mut o20: uint64_t = o201;
    let mut o21: uint64_t = o211;
    let mut o22: uint64_t = o221;
    let mut o23: uint64_t = o231;
    let mut o24: uint64_t = o241;
    *out.offset(0 as libc::c_uint as isize) = o10;
    *out.offset(1 as libc::c_uint as isize) = o11;
    *out.offset(2 as libc::c_uint as isize) = o12;
    *out.offset(3 as libc::c_uint as isize) = o13;
    *out.offset(4 as libc::c_uint as isize) = o14;
    *out.offset(5 as libc::c_uint as isize) = o20;
    *out.offset(6 as libc::c_uint as isize) = o21;
    *out.offset(7 as libc::c_uint as isize) = o22;
    *out.offset(8 as libc::c_uint as isize) = o23;
    *out.offset(9 as libc::c_uint as isize) = o24;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_store_felem(
    mut u64s: *mut uint64_t,
    mut f: *mut uint64_t,
) {
    let mut f0: uint64_t = *f.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *f.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *f.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *f.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *f.offset(4 as libc::c_uint as isize);
    let mut l_: uint64_t = f0.wrapping_add(0 as libc::c_ulonglong);
    let mut tmp0: uint64_t = l_ & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c0: uint64_t = l_ >> 51 as libc::c_uint;
    let mut l_0: uint64_t = f1.wrapping_add(c0);
    let mut tmp1: uint64_t = l_0 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c1: uint64_t = l_0 >> 51 as libc::c_uint;
    let mut l_1: uint64_t = f2.wrapping_add(c1);
    let mut tmp2: uint64_t = l_1 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c2: uint64_t = l_1 >> 51 as libc::c_uint;
    let mut l_2: uint64_t = f3.wrapping_add(c2);
    let mut tmp3: uint64_t = l_2 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c3: uint64_t = l_2 >> 51 as libc::c_uint;
    let mut l_3: uint64_t = f4.wrapping_add(c3);
    let mut tmp4: uint64_t = l_3 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c4: uint64_t = l_3 >> 51 as libc::c_uint;
    let mut l_4: uint64_t = tmp0.wrapping_add(c4.wrapping_mul(19 as libc::c_ulonglong));
    let mut tmp0_: uint64_t = l_4 & 0x7ffffffffffff as libc::c_ulonglong;
    let mut c5: uint64_t = l_4 >> 51 as libc::c_uint;
    let mut f01: uint64_t = tmp0_;
    let mut f11: uint64_t = tmp1.wrapping_add(c5);
    let mut f21: uint64_t = tmp2;
    let mut f31: uint64_t = tmp3;
    let mut f41: uint64_t = tmp4;
    let mut m0: uint64_t = FStar_UInt64_gte_mask(
        f01,
        0x7ffffffffffed as libc::c_ulonglong,
    );
    let mut m1: uint64_t = FStar_UInt64_eq_mask(
        f11,
        0x7ffffffffffff as libc::c_ulonglong,
    );
    let mut m2: uint64_t = FStar_UInt64_eq_mask(
        f21,
        0x7ffffffffffff as libc::c_ulonglong,
    );
    let mut m3: uint64_t = FStar_UInt64_eq_mask(
        f31,
        0x7ffffffffffff as libc::c_ulonglong,
    );
    let mut m4: uint64_t = FStar_UInt64_eq_mask(
        f41,
        0x7ffffffffffff as libc::c_ulonglong,
    );
    let mut mask: uint64_t = m0 & m1 & m2 & m3 & m4;
    let mut f0_: uint64_t = f01
        .wrapping_sub(mask & 0x7ffffffffffed as libc::c_ulonglong);
    let mut f1_: uint64_t = f11
        .wrapping_sub(mask & 0x7ffffffffffff as libc::c_ulonglong);
    let mut f2_: uint64_t = f21
        .wrapping_sub(mask & 0x7ffffffffffff as libc::c_ulonglong);
    let mut f3_: uint64_t = f31
        .wrapping_sub(mask & 0x7ffffffffffff as libc::c_ulonglong);
    let mut f4_: uint64_t = f41
        .wrapping_sub(mask & 0x7ffffffffffff as libc::c_ulonglong);
    let mut f02: uint64_t = f0_;
    let mut f12: uint64_t = f1_;
    let mut f22: uint64_t = f2_;
    let mut f32: uint64_t = f3_;
    let mut f42: uint64_t = f4_;
    let mut o00: uint64_t = f02 | f12 << 51 as libc::c_uint;
    let mut o10: uint64_t = f12 >> 13 as libc::c_uint | f22 << 38 as libc::c_uint;
    let mut o20: uint64_t = f22 >> 26 as libc::c_uint | f32 << 25 as libc::c_uint;
    let mut o30: uint64_t = f32 >> 39 as libc::c_uint | f42 << 12 as libc::c_uint;
    let mut o0: uint64_t = o00;
    let mut o1: uint64_t = o10;
    let mut o2: uint64_t = o20;
    let mut o3: uint64_t = o30;
    *u64s.offset(0 as libc::c_uint as isize) = o0;
    *u64s.offset(1 as libc::c_uint as isize) = o1;
    *u64s.offset(2 as libc::c_uint as isize) = o2;
    *u64s.offset(3 as libc::c_uint as isize) = o3;
}
#[inline]
unsafe extern "C" fn Hacl_Impl_Curve25519_Field51_cswap2(
    mut bit: uint64_t,
    mut p1: *mut uint64_t,
    mut p2: *mut uint64_t,
) {
    let mut mask: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bit);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut dummy: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_0: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_0;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_1: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_1;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_2: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_2;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_3: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_3;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_4: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_4;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_5: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_5;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_6: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_6;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_7: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_7;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_7;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut dummy_8: uint64_t = mask & (*p1.offset(i as isize) ^ *p2.offset(i as isize));
    *p1.offset(i as isize) = *p1.offset(i as isize) ^ dummy_8;
    *p2.offset(i as isize) = *p2.offset(i as isize) ^ dummy_8;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
static mut g25519: [uint8_t; 32] = [
    9 as libc::c_uint as uint8_t,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
];
unsafe extern "C" fn point_add_and_double(
    mut q: *mut uint64_t,
    mut p01_tmp1: *mut uint64_t,
    mut tmp2: *mut FStar_UInt128_uint128,
) {
    let mut nq: *mut uint64_t = p01_tmp1;
    let mut nq_p1: *mut uint64_t = p01_tmp1.offset(10 as libc::c_uint as isize);
    let mut tmp1: *mut uint64_t = p01_tmp1.offset(20 as libc::c_uint as isize);
    let mut x1: *mut uint64_t = q;
    let mut x2: *mut uint64_t = nq;
    let mut z2: *mut uint64_t = nq.offset(5 as libc::c_uint as isize);
    let mut dc: *mut uint64_t = tmp1.offset(10 as libc::c_uint as isize);
    let mut ab: *mut uint64_t = tmp1;
    let mut a: *mut uint64_t = ab;
    let mut b: *mut uint64_t = ab.offset(5 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
    Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
    let mut ab1: *mut uint64_t = tmp1;
    let mut x3: *mut uint64_t = nq_p1;
    let mut z31: *mut uint64_t = nq_p1.offset(5 as libc::c_uint as isize);
    let mut d0: *mut uint64_t = dc;
    let mut c0: *mut uint64_t = dc.offset(5 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fadd(c0, x3, z31);
    Hacl_Impl_Curve25519_Field51_fsub(d0, x3, z31);
    let mut f1_copy0: [uint64_t; 10] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        dc as *const libc::c_void,
        (10 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul2(dc, f1_copy0.as_mut_ptr(), ab1, tmp2);
    let mut d1: *mut uint64_t = dc;
    let mut c1: *mut uint64_t = dc.offset(5 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fadd(x3, d1, c1);
    Hacl_Impl_Curve25519_Field51_fsub(z31, d1, c1);
    let mut ab2: *mut uint64_t = tmp1;
    let mut dc1: *mut uint64_t = tmp1.offset(10 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fsqr2(dc1, ab2, tmp2);
    let mut f1_copy1: [uint64_t; 10] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        f1_copy1.as_mut_ptr() as *mut libc::c_void,
        nq_p1 as *const libc::c_void,
        (10 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fsqr2(nq_p1, f1_copy1.as_mut_ptr(), tmp2);
    let mut a1: *mut uint64_t = ab2;
    let mut b1: *mut uint64_t = ab2.offset(5 as libc::c_uint as isize);
    let mut d: *mut uint64_t = dc1;
    let mut c: *mut uint64_t = dc1.offset(5 as libc::c_uint as isize);
    *a1.offset(0 as libc::c_uint as isize) = *c.offset(0 as libc::c_uint as isize);
    *a1.offset(1 as libc::c_uint as isize) = *c.offset(1 as libc::c_uint as isize);
    *a1.offset(2 as libc::c_uint as isize) = *c.offset(2 as libc::c_uint as isize);
    *a1.offset(3 as libc::c_uint as isize) = *c.offset(3 as libc::c_uint as isize);
    *a1.offset(4 as libc::c_uint as isize) = *c.offset(4 as libc::c_uint as isize);
    let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        c as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fsub(c, d, f2_copy.as_mut_ptr());
    Hacl_Impl_Curve25519_Field51_fmul1(b1, c, 121665 as libc::c_ulonglong);
    let mut f1_copy2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy2.as_mut_ptr() as *mut libc::c_void,
        b1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fadd(b1, f1_copy2.as_mut_ptr(), d);
    let mut ab3: *mut uint64_t = tmp1;
    let mut dc2: *mut uint64_t = tmp1.offset(10 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fmul2(nq, dc2, ab3, tmp2);
    let mut z310: *mut uint64_t = nq_p1.offset(5 as libc::c_uint as isize);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        z310 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(z310, f1_copy.as_mut_ptr(), x1, tmp2);
}
unsafe extern "C" fn point_double(
    mut nq: *mut uint64_t,
    mut tmp1: *mut uint64_t,
    mut tmp2: *mut FStar_UInt128_uint128,
) {
    let mut x2: *mut uint64_t = nq;
    let mut z2: *mut uint64_t = nq.offset(5 as libc::c_uint as isize);
    let mut ab: *mut uint64_t = tmp1;
    let mut dc: *mut uint64_t = tmp1.offset(10 as libc::c_uint as isize);
    let mut a: *mut uint64_t = ab;
    let mut b: *mut uint64_t = ab.offset(5 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fadd(a, x2, z2);
    Hacl_Impl_Curve25519_Field51_fsub(b, x2, z2);
    Hacl_Impl_Curve25519_Field51_fsqr2(dc, ab, tmp2);
    let mut d: *mut uint64_t = dc;
    let mut c: *mut uint64_t = dc.offset(5 as libc::c_uint as isize);
    let mut a1: *mut uint64_t = ab;
    let mut b1: *mut uint64_t = ab.offset(5 as libc::c_uint as isize);
    *a1.offset(0 as libc::c_uint as isize) = *c.offset(0 as libc::c_uint as isize);
    *a1.offset(1 as libc::c_uint as isize) = *c.offset(1 as libc::c_uint as isize);
    *a1.offset(2 as libc::c_uint as isize) = *c.offset(2 as libc::c_uint as isize);
    *a1.offset(3 as libc::c_uint as isize) = *c.offset(3 as libc::c_uint as isize);
    *a1.offset(4 as libc::c_uint as isize) = *c.offset(4 as libc::c_uint as isize);
    let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        c as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fsub(c, d, f2_copy.as_mut_ptr());
    Hacl_Impl_Curve25519_Field51_fmul1(b1, c, 121665 as libc::c_ulonglong);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        b1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fadd(b1, f1_copy.as_mut_ptr(), d);
    let mut ab1: *mut uint64_t = tmp1;
    let mut dc1: *mut uint64_t = tmp1.offset(10 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fmul2(nq, dc1, ab1, tmp2);
}
unsafe extern "C" fn montgomery_ladder(
    mut out: *mut uint64_t,
    mut key: *mut uint8_t,
    mut init: *mut uint64_t,
) {
    let mut tmp2: [FStar_UInt128_uint128; 10] = [0; 10];
    let mut _i: uint32_t = 0 as libc::c_uint;
    while _i < 10 as libc::c_uint {
        tmp2[_i as usize] = FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong);
        _i = _i.wrapping_add(1);
        _i;
    }
    let mut p01_tmp1_swap: [uint64_t; 41] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut p01: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
    let mut p03: *mut uint64_t = p01;
    let mut p11: *mut uint64_t = p01.offset(10 as libc::c_uint as isize);
    memcpy(
        p11 as *mut libc::c_void,
        init as *const libc::c_void,
        (10 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut x0: *mut uint64_t = p03;
    let mut z0: *mut uint64_t = p03.offset(5 as libc::c_uint as isize);
    *x0.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    *x0.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *x0.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *x0.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *x0.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z0.offset(0 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z0.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z0.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z0.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z0.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    let mut swap: *mut uint64_t = p01_tmp1_swap
        .as_mut_ptr()
        .offset(40 as libc::c_uint as isize);
    let mut p01_tmp1: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
    let mut nq0: *mut uint64_t = p01_tmp1;
    let mut nq_p1: *mut uint64_t = p01_tmp1.offset(10 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_cswap2(1 as libc::c_ulonglong, nq0, nq_p1);
    let mut p01_tmp11: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
    point_add_and_double(init, p01_tmp11, tmp2.as_mut_ptr());
    *swap.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 251 as libc::c_uint {
        let mut p01_tmp12: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
        let mut swap1: *mut uint64_t = p01_tmp1_swap
            .as_mut_ptr()
            .offset(40 as libc::c_uint as isize);
        let mut nq1: *mut uint64_t = p01_tmp12;
        let mut nq_p11: *mut uint64_t = p01_tmp12.offset(10 as libc::c_uint as isize);
        let mut bit: uint64_t = (*key
            .offset(
                (253 as libc::c_uint).wrapping_sub(i).wrapping_div(8 as libc::c_uint)
                    as isize,
            ) as uint32_t
            >> (253 as libc::c_uint).wrapping_sub(i).wrapping_rem(8 as libc::c_uint)
            & 1 as libc::c_uint) as uint64_t;
        let mut sw: uint64_t = *swap1.offset(0 as libc::c_uint as isize) ^ bit;
        Hacl_Impl_Curve25519_Field51_cswap2(sw, nq1, nq_p11);
        point_add_and_double(init, p01_tmp12, tmp2.as_mut_ptr());
        *swap1.offset(0 as libc::c_uint as isize) = bit;
        i = i.wrapping_add(1);
        i;
    }
    let mut sw_0: uint64_t = *swap.offset(0 as libc::c_uint as isize);
    let mut p01_tmp12_0: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
    let mut nq1_0: *mut uint64_t = p01_tmp12_0;
    let mut nq_p11_0: *mut uint64_t = p01_tmp12_0.offset(10 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_cswap2(sw_0, nq1_0, nq_p11_0);
    let mut p01_tmp10: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
    let mut nq: *mut uint64_t = p01_tmp10;
    let mut tmp1: *mut uint64_t = p01_tmp10.offset(20 as libc::c_uint as isize);
    point_double(nq, tmp1, tmp2.as_mut_ptr());
    point_double(nq, tmp1, tmp2.as_mut_ptr());
    point_double(nq, tmp1, tmp2.as_mut_ptr());
    let mut p010: *mut uint64_t = p01_tmp1_swap.as_mut_ptr();
    memcpy(
        out as *mut libc::c_void,
        p010 as *const libc::c_void,
        (10 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Curve25519_51_fsquare_times(
    mut o: *mut uint64_t,
    mut inp: *mut uint64_t,
    mut tmp: *mut FStar_UInt128_uint128,
    mut n: uint32_t,
) {
    Hacl_Impl_Curve25519_Field51_fsqr(o, inp, tmp);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < n.wrapping_sub(1 as libc::c_uint) {
        let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        memcpy(
            f1_copy.as_mut_ptr() as *mut libc::c_void,
            o as *const libc::c_void,
            (5 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Impl_Curve25519_Field51_fsqr(o, f1_copy.as_mut_ptr(), tmp);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Curve25519_51_finv(
    mut o: *mut uint64_t,
    mut i: *mut uint64_t,
    mut tmp: *mut FStar_UInt128_uint128,
) {
    let mut t1: [uint64_t; 20] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut a1: *mut uint64_t = t1.as_mut_ptr();
    let mut b1: *mut uint64_t = t1.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut t010: *mut uint64_t = t1.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut tmp10: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(a1, i, tmp10, 1 as libc::c_uint);
    Hacl_Curve25519_51_fsquare_times(t010, a1, tmp10, 2 as libc::c_uint);
    Hacl_Impl_Curve25519_Field51_fmul(b1, t010, i, tmp);
    let mut f2_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy.as_mut_ptr() as *mut libc::c_void,
        a1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(a1, b1, f2_copy.as_mut_ptr(), tmp);
    let mut tmp11: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(t010, a1, tmp11, 1 as libc::c_uint);
    let mut f2_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy0.as_mut_ptr() as *mut libc::c_void,
        b1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(b1, t010, f2_copy0.as_mut_ptr(), tmp);
    let mut tmp12: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(t010, b1, tmp12, 5 as libc::c_uint);
    let mut f2_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy1.as_mut_ptr() as *mut libc::c_void,
        b1 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(b1, t010, f2_copy1.as_mut_ptr(), tmp);
    let mut b10: *mut uint64_t = t1.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut c10: *mut uint64_t = t1.as_mut_ptr().offset(10 as libc::c_uint as isize);
    let mut t011: *mut uint64_t = t1.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut tmp13: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(t011, b10, tmp13, 10 as libc::c_uint);
    Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b10, tmp);
    let mut tmp110: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(t011, c10, tmp110, 20 as libc::c_uint);
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        t011 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(t011, f1_copy.as_mut_ptr(), c10, tmp);
    let mut tmp120: *mut FStar_UInt128_uint128 = tmp;
    let mut i_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        i_copy0.as_mut_ptr() as *mut libc::c_void,
        t011 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Curve25519_51_fsquare_times(
        t011,
        i_copy0.as_mut_ptr(),
        tmp120,
        10 as libc::c_uint,
    );
    let mut f2_copy2: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f2_copy2.as_mut_ptr() as *mut libc::c_void,
        b10 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(b10, t011, f2_copy2.as_mut_ptr(), tmp);
    let mut tmp130: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(t011, b10, tmp130, 50 as libc::c_uint);
    Hacl_Impl_Curve25519_Field51_fmul(c10, t011, b10, tmp);
    let mut b11: *mut uint64_t = t1.as_mut_ptr().offset(5 as libc::c_uint as isize);
    let mut c1: *mut uint64_t = t1.as_mut_ptr().offset(10 as libc::c_uint as isize);
    let mut t01: *mut uint64_t = t1.as_mut_ptr().offset(15 as libc::c_uint as isize);
    let mut tmp1: *mut FStar_UInt128_uint128 = tmp;
    Hacl_Curve25519_51_fsquare_times(t01, c1, tmp1, 100 as libc::c_uint);
    let mut f1_copy0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy0.as_mut_ptr() as *mut libc::c_void,
        t01 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(t01, f1_copy0.as_mut_ptr(), c1, tmp);
    let mut tmp111: *mut FStar_UInt128_uint128 = tmp;
    let mut i_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        i_copy1.as_mut_ptr() as *mut libc::c_void,
        t01 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Curve25519_51_fsquare_times(
        t01,
        i_copy1.as_mut_ptr(),
        tmp111,
        50 as libc::c_uint,
    );
    let mut f1_copy1: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy1.as_mut_ptr() as *mut libc::c_void,
        t01 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(t01, f1_copy1.as_mut_ptr(), b11, tmp);
    let mut tmp121: *mut FStar_UInt128_uint128 = tmp;
    let mut i_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        i_copy.as_mut_ptr() as *mut libc::c_void,
        t01 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Curve25519_51_fsquare_times(
        t01,
        i_copy.as_mut_ptr(),
        tmp121,
        5 as libc::c_uint,
    );
    let mut a: *mut uint64_t = t1.as_mut_ptr();
    let mut t0: *mut uint64_t = t1.as_mut_ptr().offset(15 as libc::c_uint as isize);
    Hacl_Impl_Curve25519_Field51_fmul(o, t0, a, tmp);
}
unsafe extern "C" fn encode_point(mut o: *mut uint8_t, mut i: *mut uint64_t) {
    let mut x: *mut uint64_t = i;
    let mut z: *mut uint64_t = i.offset(5 as libc::c_uint as isize);
    let mut tmp: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    let mut u64s: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut tmp_w: [FStar_UInt128_uint128; 10] = [0; 10];
    let mut _i: uint32_t = 0 as libc::c_uint;
    while _i < 10 as libc::c_uint {
        tmp_w[_i as usize] = FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong);
        _i = _i.wrapping_add(1);
        _i;
    }
    Hacl_Curve25519_51_finv(tmp.as_mut_ptr(), z, tmp_w.as_mut_ptr());
    let mut f1_copy: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
    memcpy(
        f1_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Impl_Curve25519_Field51_fmul(
        tmp.as_mut_ptr(),
        f1_copy.as_mut_ptr(),
        x,
        tmp_w.as_mut_ptr(),
    );
    Hacl_Impl_Curve25519_Field51_store_felem(u64s.as_mut_ptr(), tmp.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    store64(o.offset(i0.wrapping_mul(8 as libc::c_uint) as isize), u64s[i0 as usize]);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(o.offset(i0.wrapping_mul(8 as libc::c_uint) as isize), u64s[i0 as usize]);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(o.offset(i0.wrapping_mul(8 as libc::c_uint) as isize), u64s[i0 as usize]);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(o.offset(i0.wrapping_mul(8 as libc::c_uint) as isize), u64s[i0 as usize]);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Curve25519_51_scalarmult(
    mut out: *mut uint8_t,
    mut priv_0: *mut uint8_t,
    mut pub_0: *mut uint8_t,
) {
    let mut init: [uint64_t; 10] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut init_copy: [uint64_t; 10] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = pub_0.offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u: uint64_t = load64(bj);
    let mut r: uint64_t = u;
    let mut x: uint64_t = r;
    let mut os: *mut uint64_t = tmp.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = pub_0
        .offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u_0: uint64_t = load64(bj_0);
    let mut r_0: uint64_t = u_0;
    let mut x_0: uint64_t = r_0;
    let mut os_0: *mut uint64_t = tmp.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = pub_0
        .offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u_1: uint64_t = load64(bj_1);
    let mut r_1: uint64_t = u_1;
    let mut x_1: uint64_t = r_1;
    let mut os_1: *mut uint64_t = tmp.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = pub_0
        .offset(i.wrapping_mul(8 as libc::c_uint) as isize);
    let mut u_2: uint64_t = load64(bj_2);
    let mut r_2: uint64_t = u_2;
    let mut x_2: uint64_t = r_2;
    let mut os_2: *mut uint64_t = tmp.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut tmp3: uint64_t = tmp[3 as libc::c_uint as usize];
    tmp[3 as libc::c_uint as usize] = tmp3 & 0x7fffffffffffffff as libc::c_ulonglong;
    let mut x_3: *mut uint64_t = init.as_mut_ptr();
    let mut z: *mut uint64_t = init.as_mut_ptr().offset(5 as libc::c_uint as isize);
    *z.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    *z.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *z.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    let mut f0l: uint64_t = tmp[0 as libc::c_uint as usize]
        & 0x7ffffffffffff as libc::c_ulonglong;
    let mut f0h: uint64_t = tmp[0 as libc::c_uint as usize] >> 51 as libc::c_uint;
    let mut f1l: uint64_t = (tmp[1 as libc::c_uint as usize]
        & 0x3fffffffff as libc::c_ulonglong) << 13 as libc::c_uint;
    let mut f1h: uint64_t = tmp[1 as libc::c_uint as usize] >> 38 as libc::c_uint;
    let mut f2l: uint64_t = (tmp[2 as libc::c_uint as usize]
        & 0x1ffffff as libc::c_ulonglong) << 26 as libc::c_uint;
    let mut f2h: uint64_t = tmp[2 as libc::c_uint as usize] >> 25 as libc::c_uint;
    let mut f3l: uint64_t = (tmp[3 as libc::c_uint as usize]
        & 0xfff as libc::c_ulonglong) << 39 as libc::c_uint;
    let mut f3h: uint64_t = tmp[3 as libc::c_uint as usize] >> 12 as libc::c_uint;
    *x_3.offset(0 as libc::c_uint as isize) = f0l;
    *x_3.offset(1 as libc::c_uint as isize) = f0h | f1l;
    *x_3.offset(2 as libc::c_uint as isize) = f1h | f2l;
    *x_3.offset(3 as libc::c_uint as isize) = f2h | f3l;
    *x_3.offset(4 as libc::c_uint as isize) = f3h;
    memcpy(
        init_copy.as_mut_ptr() as *mut libc::c_void,
        init.as_mut_ptr() as *const libc::c_void,
        (10 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    montgomery_ladder(init.as_mut_ptr(), priv_0, init_copy.as_mut_ptr());
    encode_point(out, init.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Curve25519_51_secret_to_public(
    mut pub_0: *mut uint8_t,
    mut priv_0: *mut uint8_t,
) {
    let mut basepoint: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 32 as libc::c_uint {
        let mut x: uint8_t = g25519[i as usize];
        let mut os: *mut uint8_t = basepoint.as_mut_ptr();
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    Hacl_Curve25519_51_scalarmult(pub_0, priv_0, basepoint.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Curve25519_51_ecdh(
    mut out: *mut uint8_t,
    mut priv_0: *mut uint8_t,
    mut pub_0: *mut uint8_t,
) -> bool {
    let mut zeros: [uint8_t; 32] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    Hacl_Curve25519_51_scalarmult(out, priv_0, pub_0);
    let mut res: uint8_t = 255 as libc::c_uint as uint8_t;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 32 as libc::c_uint {
        let mut uu____0: uint8_t = FStar_UInt8_eq_mask(
            *out.offset(i as isize),
            zeros[i as usize],
        );
        res = (uu____0 as uint32_t & res as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut z: uint8_t = res;
    let mut r: bool = z as libc::c_uint == 255 as libc::c_uint;
    return !r;
}
