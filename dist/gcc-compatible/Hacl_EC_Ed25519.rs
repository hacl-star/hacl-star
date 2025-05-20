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
    fn Hacl_Bignum25519_reduce_513(a: *mut uint64_t);
    fn Hacl_Bignum25519_inverse(out: *mut uint64_t, a: *mut uint64_t);
    fn Hacl_Bignum25519_load_51(output: *mut uint64_t, input: *mut uint8_t);
    fn Hacl_Bignum25519_store_51(output: *mut uint8_t, input: *mut uint64_t);
    fn Hacl_Impl_Ed25519_PointDouble_point_double(out: *mut uint64_t, p: *mut uint64_t);
    fn Hacl_Impl_Ed25519_PointAdd_point_add(
        out: *mut uint64_t,
        p: *mut uint64_t,
        q: *mut uint64_t,
    );
    fn Hacl_Impl_Ed25519_PointConstants_make_point_inf(b: *mut uint64_t);
    fn Hacl_Impl_Ed25519_PointDecompress_point_decompress(
        out: *mut uint64_t,
        s: *mut uint8_t,
    ) -> bool;
    fn Hacl_Impl_Ed25519_PointCompress_point_compress(z: *mut uint8_t, p: *mut uint64_t);
    fn Hacl_Impl_Ed25519_PointEqual_point_equal(
        p: *mut uint64_t,
        q: *mut uint64_t,
    ) -> bool;
    fn Hacl_Impl_Ed25519_PointNegate_point_negate(p: *mut uint64_t, out: *mut uint64_t);
    fn Hacl_Impl_Ed25519_Ladder_point_mul(
        out: *mut uint64_t,
        scalar: *mut uint8_t,
        q: *mut uint64_t,
    );
}
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type FStar_UInt128_uint128 = u128;
pub type uint128_t = FStar_UInt128_uint128;
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
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_mk_felem_zero(mut b: *mut uint64_t) {
    *b.offset(0 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_mk_felem_one(mut b: *mut uint64_t) {
    *b.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    *b.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *b.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_add(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Impl_Curve25519_Field51_fadd(out, a, b);
    Hacl_Bignum25519_reduce_513(out);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_sub(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Impl_Curve25519_Field51_fsub(out, a, b);
    Hacl_Bignum25519_reduce_513(out);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_mul(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    let mut tmp: [FStar_UInt128_uint128; 10] = [0; 10];
    let mut _i: uint32_t = 0 as libc::c_uint;
    while _i < 10 as libc::c_uint {
        tmp[_i as usize] = FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong);
        _i = _i.wrapping_add(1);
        _i;
    }
    Hacl_Impl_Curve25519_Field51_fmul(out, a, b, tmp.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_sqr(
    mut a: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    let mut tmp: [FStar_UInt128_uint128; 5] = [0; 5];
    let mut _i: uint32_t = 0 as libc::c_uint;
    while _i < 5 as libc::c_uint {
        tmp[_i as usize] = FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong);
        _i = _i.wrapping_add(1);
        _i;
    }
    Hacl_Impl_Curve25519_Field51_fsqr(out, a, tmp.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_inv(
    mut a: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Bignum25519_inverse(out, a);
    Hacl_Bignum25519_reduce_513(out);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_load(
    mut b: *mut uint8_t,
    mut out: *mut uint64_t,
) {
    Hacl_Bignum25519_load_51(out, b);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_felem_store(
    mut a: *mut uint64_t,
    mut out: *mut uint8_t,
) {
    Hacl_Bignum25519_store_51(out, a);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_mk_point_at_inf(mut p: *mut uint64_t) {
    Hacl_Impl_Ed25519_PointConstants_make_point_inf(p);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_mk_base_point(mut p: *mut uint64_t) {
    let mut gx: *mut uint64_t = p;
    let mut gy: *mut uint64_t = p.offset(5 as libc::c_uint as isize);
    let mut gz: *mut uint64_t = p.offset(10 as libc::c_uint as isize);
    let mut gt: *mut uint64_t = p.offset(15 as libc::c_uint as isize);
    *gx.offset(0 as libc::c_uint as isize) = 0x62d608f25d51a as libc::c_ulonglong;
    *gx.offset(1 as libc::c_uint as isize) = 0x412a4b4f6592a as libc::c_ulonglong;
    *gx.offset(2 as libc::c_uint as isize) = 0x75b7171a4b31d as libc::c_ulonglong;
    *gx.offset(3 as libc::c_uint as isize) = 0x1ff60527118fe as libc::c_ulonglong;
    *gx.offset(4 as libc::c_uint as isize) = 0x216936d3cd6e5 as libc::c_ulonglong;
    *gy.offset(0 as libc::c_uint as isize) = 0x6666666666658 as libc::c_ulonglong;
    *gy.offset(1 as libc::c_uint as isize) = 0x4cccccccccccc as libc::c_ulonglong;
    *gy.offset(2 as libc::c_uint as isize) = 0x1999999999999 as libc::c_ulonglong;
    *gy.offset(3 as libc::c_uint as isize) = 0x3333333333333 as libc::c_ulonglong;
    *gy.offset(4 as libc::c_uint as isize) = 0x6666666666666 as libc::c_ulonglong;
    *gz.offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    *gz.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *gz.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *gz.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *gz.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *gt.offset(0 as libc::c_uint as isize) = 0x68ab3a5b7dda3 as libc::c_ulonglong;
    *gt.offset(1 as libc::c_uint as isize) = 0xeea2a5eadbb as libc::c_ulonglong;
    *gt.offset(2 as libc::c_uint as isize) = 0x2af8df483c27e as libc::c_ulonglong;
    *gt.offset(3 as libc::c_uint as isize) = 0x332b375274732 as libc::c_ulonglong;
    *gt.offset(4 as libc::c_uint as isize) = 0x67875f0fd78b7 as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_negate(
    mut p: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Impl_Ed25519_PointNegate_point_negate(p, out);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_add(
    mut p: *mut uint64_t,
    mut q: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Impl_Ed25519_PointAdd_point_add(out, p, q);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_double(
    mut p: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Impl_Ed25519_PointDouble_point_double(out, p);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_mul(
    mut scalar: *mut uint8_t,
    mut p: *mut uint64_t,
    mut out: *mut uint64_t,
) {
    Hacl_Impl_Ed25519_Ladder_point_mul(out, scalar, p);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_eq(
    mut p: *mut uint64_t,
    mut q: *mut uint64_t,
) -> bool {
    return Hacl_Impl_Ed25519_PointEqual_point_equal(p, q);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_compress(
    mut p: *mut uint64_t,
    mut out: *mut uint8_t,
) {
    Hacl_Impl_Ed25519_PointCompress_point_compress(out, p);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_EC_Ed25519_point_decompress(
    mut s: *mut uint8_t,
    mut out: *mut uint64_t,
) -> bool {
    return Hacl_Impl_Ed25519_PointDecompress_point_decompress(out, s);
}
