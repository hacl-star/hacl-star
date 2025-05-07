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
    fn memset(
        _: *mut libc::c_void,
        _: libc::c_int,
        _: libc::c_ulong,
    ) -> *mut libc::c_void;
    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
}
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
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
unsafe extern "C" fn FStar_UInt128_add_mod(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_add(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_sub_mod(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_sub(y);
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
unsafe extern "C" fn FStar_UInt32_eq_mask(mut a: uint32_t, mut b: uint32_t) -> uint32_t {
    let mut x: uint32_t = a ^ b;
    let mut minus_x: uint32_t = (!x).wrapping_add(1 as libc::c_uint);
    let mut x_or_minus_x: uint32_t = x | minus_x;
    let mut xnx: uint32_t = x_or_minus_x >> 31 as libc::c_uint;
    return xnx.wrapping_sub(1 as libc::c_uint);
}
#[inline(never)]
unsafe extern "C" fn FStar_UInt32_gte_mask(
    mut a: uint32_t,
    mut b: uint32_t,
) -> uint32_t {
    let mut x: uint32_t = a;
    let mut y: uint32_t = b;
    let mut x_xor_y: uint32_t = x ^ y;
    let mut x_sub_y: uint32_t = x.wrapping_sub(y);
    let mut x_sub_y_xor_y: uint32_t = x_sub_y ^ y;
    let mut q: uint32_t = x_xor_y | x_sub_y_xor_y;
    let mut x_xor_q: uint32_t = x ^ q;
    let mut x_xor_q_: uint32_t = x_xor_q >> 31 as libc::c_uint;
    return x_xor_q_.wrapping_sub(1 as libc::c_uint);
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_add_carry_u32(
    mut cin: uint32_t,
    mut x: uint32_t,
    mut y: uint32_t,
    mut r: *mut uint32_t,
) -> uint32_t {
    let mut res: uint64_t = (x as uint64_t)
        .wrapping_add(cin as uint64_t)
        .wrapping_add(y as uint64_t);
    let mut c: uint32_t = (res >> 32 as libc::c_uint) as uint32_t;
    *r.offset(0 as libc::c_uint as isize) = res as uint32_t;
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_sub_borrow_u32(
    mut cin: uint32_t,
    mut x: uint32_t,
    mut y: uint32_t,
    mut r: *mut uint32_t,
) -> uint32_t {
    let mut res: uint64_t = (x as uint64_t)
        .wrapping_sub(y as uint64_t)
        .wrapping_sub(cin as uint64_t);
    let mut c: uint32_t = (res >> 32 as libc::c_uint) as uint32_t & 1 as libc::c_uint;
    *r.offset(0 as libc::c_uint as isize) = res as uint32_t;
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_128_add_carry_u64(
    mut cin: uint64_t,
    mut x: uint64_t,
    mut y: uint64_t,
    mut r: *mut uint64_t,
) -> uint64_t {
    let mut res: FStar_UInt128_uint128 = FStar_UInt128_add_mod(
        FStar_UInt128_add_mod(
            FStar_UInt128_uint64_to_uint128(x),
            FStar_UInt128_uint64_to_uint128(cin),
        ),
        FStar_UInt128_uint64_to_uint128(y),
    );
    let mut c: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res, 64 as libc::c_uint),
    );
    *r.offset(0 as libc::c_uint as isize) = FStar_UInt128_uint128_to_uint64(res);
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
    mut cin: uint64_t,
    mut x: uint64_t,
    mut y: uint64_t,
    mut r: *mut uint64_t,
) -> uint64_t {
    let mut res: FStar_UInt128_uint128 = FStar_UInt128_sub_mod(
        FStar_UInt128_sub_mod(
            FStar_UInt128_uint64_to_uint128(x),
            FStar_UInt128_uint64_to_uint128(y),
        ),
        FStar_UInt128_uint64_to_uint128(cin),
    );
    let mut c: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res, 64 as libc::c_uint),
    ) & 1 as libc::c_ulonglong;
    *r.offset(0 as libc::c_uint as isize) = FStar_UInt128_uint128_to_uint64(res);
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Base_mul_wide_add2_u32(
    mut a: uint32_t,
    mut b: uint32_t,
    mut c_in: uint32_t,
    mut out: *mut uint32_t,
) -> uint32_t {
    let mut out0: uint32_t = *out.offset(0 as libc::c_uint as isize);
    let mut res: uint64_t = (a as uint64_t * b as uint64_t)
        .wrapping_add(c_in as uint64_t)
        .wrapping_add(out0 as uint64_t);
    *out.offset(0 as libc::c_uint as isize) = res as uint32_t;
    return (res >> 32 as libc::c_uint) as uint32_t;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Base_mul_wide_add2_u64(
    mut a: uint64_t,
    mut b: uint64_t,
    mut c_in: uint64_t,
    mut out: *mut uint64_t,
) -> uint64_t {
    let mut out0: uint64_t = *out.offset(0 as libc::c_uint as isize);
    let mut res: FStar_UInt128_uint128 = FStar_UInt128_add(
        FStar_UInt128_add(
            FStar_UInt128_mul_wide(a, b),
            FStar_UInt128_uint64_to_uint128(c_in),
        ),
        FStar_UInt128_uint64_to_uint128(out0),
    );
    *out.offset(0 as libc::c_uint as isize) = FStar_UInt128_uint128_to_uint64(res);
    return FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res, 64 as libc::c_uint),
    );
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_bits_u32(
    mut len: uint32_t,
    mut b: *mut uint32_t,
    mut i: uint32_t,
    mut l: uint32_t,
) -> uint32_t {
    let mut i1: uint32_t = i.wrapping_div(32 as libc::c_uint);
    let mut j: uint32_t = i.wrapping_rem(32 as libc::c_uint);
    let mut p1: uint32_t = *b.offset(i1 as isize) >> j;
    let mut ite: uint32_t = 0;
    if i1.wrapping_add(1 as libc::c_uint) < len && (0 as libc::c_uint) < j {
        ite = p1
            | *b.offset(i1.wrapping_add(1 as libc::c_uint) as isize)
                << (32 as libc::c_uint).wrapping_sub(j);
    } else {
        ite = p1;
    }
    return ite & ((1 as libc::c_uint) << l).wrapping_sub(1 as libc::c_uint);
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_bits_u64(
    mut len: uint32_t,
    mut b: *mut uint64_t,
    mut i: uint32_t,
    mut l: uint32_t,
) -> uint64_t {
    let mut i1: uint32_t = i.wrapping_div(64 as libc::c_uint);
    let mut j: uint32_t = i.wrapping_rem(64 as libc::c_uint);
    let mut p1: uint64_t = *b.offset(i1 as isize) >> j;
    let mut ite: uint64_t = 0;
    if i1.wrapping_add(1 as libc::c_uint) < len && (0 as libc::c_uint) < j {
        ite = p1
            | *b.offset(i1.wrapping_add(1 as libc::c_uint) as isize)
                << (64 as libc::c_uint).wrapping_sub(j);
    } else {
        ite = p1;
    }
    return ite & ((1 as libc::c_ulonglong) << l).wrapping_sub(1 as libc::c_ulonglong);
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Addition_bn_sub_eq_len_u32(
    mut aLen: uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) -> uint32_t {
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < aLen.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
        let mut t10: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
        let mut t11: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
        let mut t12: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = aLen
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < aLen {
        let mut t1_0: uint32_t = *a.offset(i_0 as isize);
        let mut t2_0: uint32_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint32_t = res.offset(i_0 as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Addition_bn_sub_eq_len_u64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < aLen.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint64_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1, t20, res_i0);
        let mut t10: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t10, t21, res_i1);
        let mut t11: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t11, t22, res_i2);
        let mut t12: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = aLen
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < aLen {
        let mut t1_0: uint64_t = *a.offset(i_0 as isize);
        let mut t2_0: uint64_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res.offset(i_0 as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Addition_bn_add_eq_len_u32(
    mut aLen: uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) -> uint32_t {
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < aLen.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
        let mut t10: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
        let mut t11: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
        let mut t12: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = aLen
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < aLen {
        let mut t1_0: uint32_t = *a.offset(i_0 as isize);
        let mut t2_0: uint32_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint32_t = res.offset(i_0 as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Addition_bn_add_eq_len_u64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < aLen.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint64_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1, t20, res_i0);
        let mut t10: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10, t21, res_i1);
        let mut t11: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11, t22, res_i2);
        let mut t12: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = aLen
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < aLen {
        let mut t1_0: uint64_t = *a.offset(i_0 as isize);
        let mut t2_0: uint64_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res.offset(i_0 as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Multiplication_bn_mul_u32(
    mut aLen: uint32_t,
    mut a: *mut uint32_t,
    mut bLen: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(bLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < bLen {
        let mut bj: uint32_t = *b.offset(i0 as isize);
        let mut res_j: *mut uint32_t = res.offset(i0 as isize);
        let mut c: uint32_t = 0 as libc::c_uint;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < aLen.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint32_t = *a
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
            let mut a_i0: uint32_t = *a
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
            let mut a_i1: uint32_t = *a
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
            let mut a_i2: uint32_t = *a
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = aLen
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < aLen {
            let mut a_i_0: uint32_t = *a.offset(i_0 as isize);
            let mut res_i_0: *mut uint32_t = res_j.offset(i_0 as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, bj, c, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint32_t = c;
        *res.offset(aLen.wrapping_add(i0) as isize) = r;
        i0 = i0.wrapping_add(1);
        i0;
    }
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Multiplication_bn_mul_u64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut bLen: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(bLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < bLen {
        let mut bj: uint64_t = *b.offset(i0 as isize);
        let mut res_j: *mut uint64_t = res.offset(i0 as isize);
        let mut c: uint64_t = 0 as libc::c_ulonglong;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < aLen.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint64_t = *a
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
            let mut a_i0: uint64_t = *a
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
            let mut a_i1: uint64_t = *a
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
            let mut a_i2: uint64_t = *a
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = aLen
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < aLen {
            let mut a_i_0: uint64_t = *a.offset(i_0 as isize);
            let mut res_i_0: *mut uint64_t = res_j.offset(i_0 as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, bj, c, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint64_t = c;
        *res.offset(aLen.wrapping_add(i0) as isize) = r;
        i0 = i0.wrapping_add(1);
        i0;
    }
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Multiplication_bn_sqr_u32(
    mut aLen: uint32_t,
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < aLen {
        let mut a_j: uint32_t = *a.offset(i0 as isize);
        let mut ab: *mut uint32_t = a;
        let mut res_j: *mut uint32_t = res.offset(i0 as isize);
        let mut c: uint32_t = 0 as libc::c_uint;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < i0.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint32_t = *ab
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, a_j, c, res_i0);
            let mut a_i0: uint32_t = *ab
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, a_j, c, res_i1);
            let mut a_i1: uint32_t = *ab
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, a_j, c, res_i2);
            let mut a_i2: uint32_t = *ab
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, a_j, c, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = i0
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < i0 {
            let mut a_i_0: uint32_t = *ab.offset(i_0 as isize);
            let mut res_i_0: *mut uint32_t = res_j.offset(i_0 as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, a_j, c, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint32_t = c;
        *res.offset(i0.wrapping_add(i0) as isize) = r;
        i0 = i0.wrapping_add(1);
        i0;
    }
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            403 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = aLen.wrapping_add(aLen) as usize;
    let mut a_copy0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            406 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = aLen.wrapping_add(aLen) as usize;
    let mut b_copy0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut r_0: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(
        aLen.wrapping_add(aLen),
        a_copy0.as_mut_ptr(),
        b_copy0.as_mut_ptr(),
        res,
    );
    let mut c0: uint32_t = r_0;
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            414 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = aLen.wrapping_add(aLen) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < aLen {
        let mut res1: uint64_t = *a.offset(i_1 as isize) as uint64_t
            * *a.offset(i_1 as isize) as uint64_t;
        let mut hi: uint32_t = (res1 >> 32 as libc::c_uint) as uint32_t;
        let mut lo: uint32_t = res1 as uint32_t;
        *tmp.as_mut_ptr().offset((2 as libc::c_uint).wrapping_mul(i_1) as isize) = lo;
        *tmp
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            ) = hi;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            425 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_2 = aLen.wrapping_add(aLen) as usize;
    let mut a_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_2);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            428 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_3 = aLen.wrapping_add(aLen) as usize;
    let mut b_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_3);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut r0: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(
        aLen.wrapping_add(aLen),
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        res,
    );
    let mut c1: uint32_t = r0;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Multiplication_bn_sqr_u64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < aLen {
        let mut a_j: uint64_t = *a.offset(i0 as isize);
        let mut ab: *mut uint64_t = a;
        let mut res_j: *mut uint64_t = res.offset(i0 as isize);
        let mut c: uint64_t = 0 as libc::c_ulonglong;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < i0.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint64_t = *ab
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, a_j, c, res_i0);
            let mut a_i0: uint64_t = *ab
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, a_j, c, res_i1);
            let mut a_i1: uint64_t = *ab
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, a_j, c, res_i2);
            let mut a_i2: uint64_t = *ab
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint64_t = res_j
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, a_j, c, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = i0
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < i0 {
            let mut a_i_0: uint64_t = *ab.offset(i_0 as isize);
            let mut res_i_0: *mut uint64_t = res_j.offset(i_0 as isize);
            c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, a_j, c, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint64_t = c;
        *res.offset(i0.wrapping_add(i0) as isize) = r;
        i0 = i0.wrapping_add(1);
        i0;
    }
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            472 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = aLen.wrapping_add(aLen) as usize;
    let mut a_copy0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            475 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = aLen.wrapping_add(aLen) as usize;
    let mut b_copy0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r_0: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        aLen.wrapping_add(aLen),
        a_copy0.as_mut_ptr(),
        b_copy0.as_mut_ptr(),
        res,
    );
    let mut c0: uint64_t = r_0;
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            483 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = aLen.wrapping_add(aLen) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < aLen {
        let mut res1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
            *a.offset(i_1 as isize),
            *a.offset(i_1 as isize),
        );
        let mut hi: uint64_t = FStar_UInt128_uint128_to_uint64(
            FStar_UInt128_shift_right(res1, 64 as libc::c_uint),
        );
        let mut lo: uint64_t = FStar_UInt128_uint128_to_uint64(res1);
        *tmp.as_mut_ptr().offset((2 as libc::c_uint).wrapping_mul(i_1) as isize) = lo;
        *tmp
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            ) = hi;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            494 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_2 = aLen.wrapping_add(aLen) as usize;
    let mut a_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_2);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if aLen.wrapping_add(aLen) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            497 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_3 = aLen.wrapping_add(aLen) as usize;
    let mut b_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_3);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (aLen.wrapping_add(aLen) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r0: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        aLen.wrapping_add(aLen),
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        res,
    );
    let mut c1: uint64_t = r0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
    mut aLen: uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut tmp: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if aLen < 32 as libc::c_uint
        || aLen.wrapping_rem(2 as libc::c_uint) == 1 as libc::c_uint
    {
        Hacl_Bignum_Multiplication_bn_mul_u32(aLen, a, aLen, b, res);
        return;
    }
    let mut len2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut a0: *mut uint32_t = a;
    let mut a1: *mut uint32_t = a.offset(len2 as isize);
    let mut b0: *mut uint32_t = b;
    let mut b1: *mut uint32_t = b.offset(len2 as isize);
    let mut t0: *mut uint32_t = tmp;
    let mut t1: *mut uint32_t = tmp.offset(len2 as isize);
    let mut tmp_: *mut uint32_t = tmp.offset(aLen as isize);
    let mut c0: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
    let mut c10: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len2 {
        let mut x: uint32_t = (0 as libc::c_uint).wrapping_sub(c0)
            & *t0.offset(i as isize)
            | !(0 as libc::c_uint).wrapping_sub(c0) & *tmp_.offset(i as isize);
        let mut os: *mut uint32_t = t0;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    let mut c00: uint32_t = c0;
    let mut c010: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b0, b1, tmp_);
    let mut c1: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, b1, b0, t1);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < len2 {
        let mut x_0: uint32_t = (0 as libc::c_uint).wrapping_sub(c010)
            & *t1.offset(i_0 as isize)
            | !(0 as libc::c_uint).wrapping_sub(c010) & *tmp_.offset(i_0 as isize);
        let mut os_0: *mut uint32_t = t1;
        *os_0.offset(i_0 as isize) = x_0;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c11: uint32_t = c010;
    let mut t23: *mut uint32_t = tmp.offset(aLen as isize);
    let mut tmp1: *mut uint32_t = tmp.offset(aLen as isize).offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, t0, t1, tmp1, t23);
    let mut r01: *mut uint32_t = res;
    let mut r23: *mut uint32_t = res.offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, a0, b0, tmp1, r01);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(len2, a1, b1, tmp1, r23);
    let mut r011: *mut uint32_t = res;
    let mut r231: *mut uint32_t = res.offset(aLen as isize);
    let mut t01: *mut uint32_t = tmp;
    let mut t231: *mut uint32_t = tmp.offset(aLen as isize);
    let mut t45: *mut uint32_t = tmp
        .offset((2 as libc::c_uint).wrapping_mul(aLen) as isize);
    let mut t67: *mut uint32_t = tmp
        .offset((3 as libc::c_uint).wrapping_mul(aLen) as isize);
    let mut c2: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
    let mut c_sign: uint32_t = c00 ^ c11;
    let mut c3: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t67);
    let mut c31: uint32_t = c2.wrapping_sub(c3);
    let mut c4: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, t01, t231, t45);
    let mut c41: uint32_t = c2.wrapping_add(c4);
    let mut mask: uint32_t = (0 as libc::c_uint).wrapping_sub(c_sign);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < aLen {
        let mut x_1: uint32_t = mask & *t45.offset(i_1 as isize)
            | !mask & *t67.offset(i_1 as isize);
        let mut os_1: *mut uint32_t = t45;
        *os_1.offset(i_1 as isize) = x_1;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut c5: uint32_t = mask & c41 | !mask & c31;
    let mut aLen2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut r0: *mut uint32_t = res.offset(aLen2 as isize);
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            105 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = aLen as usize;
    let mut a_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            108 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = aLen as usize;
    let mut b_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        r0 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        t45 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut r10: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(
        aLen,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        r0,
    );
    let mut r11: uint32_t = r10;
    let mut c6: uint32_t = r11;
    let mut c60: uint32_t = c6;
    let mut c7: uint32_t = c5.wrapping_add(c60);
    let mut r: *mut uint32_t = res.offset(aLen as isize).offset(aLen2 as isize);
    let mut c01: uint32_t = Hacl_IntTypes_Intrinsics_add_carry_u32(
        0 as libc::c_uint,
        *r.offset(0 as libc::c_uint as isize),
        c7,
        r,
    );
    let mut r1: uint32_t = 0;
    if (1 as libc::c_uint)
        < aLen.wrapping_add(aLen).wrapping_sub(aLen.wrapping_add(aLen2))
    {
        let mut res1: *mut uint32_t = r.offset(1 as libc::c_uint as isize);
        let mut c: uint32_t = c01;
        let mut i_2: uint32_t = 0 as libc::c_uint;
        while i_2
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(4 as libc::c_uint)
        {
            let mut t11: uint32_t = *res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
            let mut res_i0: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t11,
                0 as libc::c_uint,
                res_i0,
            );
            let mut t110: uint32_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t110,
                0 as libc::c_uint,
                res_i1,
            );
            let mut t111: uint32_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t111,
                0 as libc::c_uint,
                res_i2,
            );
            let mut t112: uint32_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t112,
                0 as libc::c_uint,
                res_i,
            );
            i_2 = i_2.wrapping_add(1);
            i_2;
        }
        let mut i_3: uint32_t = aLen
            .wrapping_add(aLen)
            .wrapping_sub(aLen.wrapping_add(aLen2))
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_3
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
        {
            let mut t11_0: uint32_t = *res1.offset(i_3 as isize);
            let mut res_i_0: *mut uint32_t = res1.offset(i_3 as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t11_0,
                0 as libc::c_uint,
                res_i_0,
            );
            i_3 = i_3.wrapping_add(1);
            i_3;
        }
        let mut c110: uint32_t = c;
        r1 = c110;
    } else {
        r1 = c01;
    }
    let mut c8: uint32_t = r1;
    let mut c_0: uint32_t = c8;
    let mut c9: uint32_t = c_0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut tmp: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if aLen < 32 as libc::c_uint
        || aLen.wrapping_rem(2 as libc::c_uint) == 1 as libc::c_uint
    {
        Hacl_Bignum_Multiplication_bn_mul_u64(aLen, a, aLen, b, res);
        return;
    }
    let mut len2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut a0: *mut uint64_t = a;
    let mut a1: *mut uint64_t = a.offset(len2 as isize);
    let mut b0: *mut uint64_t = b;
    let mut b1: *mut uint64_t = b.offset(len2 as isize);
    let mut t0: *mut uint64_t = tmp;
    let mut t1: *mut uint64_t = tmp.offset(len2 as isize);
    let mut tmp_: *mut uint64_t = tmp.offset(aLen as isize);
    let mut c0: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
    let mut c10: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len2 {
        let mut x: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c0)
            & *t0.offset(i as isize)
            | !(0 as libc::c_ulonglong).wrapping_sub(c0) & *tmp_.offset(i as isize);
        let mut os: *mut uint64_t = t0;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    let mut c00: uint64_t = c0;
    let mut c010: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b0, b1, tmp_);
    let mut c1: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, b1, b0, t1);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < len2 {
        let mut x_0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c010)
            & *t1.offset(i_0 as isize)
            | !(0 as libc::c_ulonglong).wrapping_sub(c010) & *tmp_.offset(i_0 as isize);
        let mut os_0: *mut uint64_t = t1;
        *os_0.offset(i_0 as isize) = x_0;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c11: uint64_t = c010;
    let mut t23: *mut uint64_t = tmp.offset(aLen as isize);
    let mut tmp1: *mut uint64_t = tmp.offset(aLen as isize).offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, t0, t1, tmp1, t23);
    let mut r01: *mut uint64_t = res;
    let mut r23: *mut uint64_t = res.offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a0, b0, tmp1, r01);
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(len2, a1, b1, tmp1, r23);
    let mut r011: *mut uint64_t = res;
    let mut r231: *mut uint64_t = res.offset(aLen as isize);
    let mut t01: *mut uint64_t = tmp;
    let mut t231: *mut uint64_t = tmp.offset(aLen as isize);
    let mut t45: *mut uint64_t = tmp
        .offset((2 as libc::c_uint).wrapping_mul(aLen) as isize);
    let mut t67: *mut uint64_t = tmp
        .offset((3 as libc::c_uint).wrapping_mul(aLen) as isize);
    let mut c2: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
    let mut c_sign: uint64_t = c00 ^ c11;
    let mut c3: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t67);
    let mut c31: uint64_t = c2.wrapping_sub(c3);
    let mut c4: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, t01, t231, t45);
    let mut c41: uint64_t = c2.wrapping_add(c4);
    let mut mask: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c_sign);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < aLen {
        let mut x_1: uint64_t = mask & *t45.offset(i_1 as isize)
            | !mask & *t67.offset(i_1 as isize);
        let mut os_1: *mut uint64_t = t45;
        *os_1.offset(i_1 as isize) = x_1;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut c5: uint64_t = mask & c41 | !mask & c31;
    let mut aLen2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut r0: *mut uint64_t = res.offset(aLen2 as isize);
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            239 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = aLen as usize;
    let mut a_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            242 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = aLen as usize;
    let mut b_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        r0 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        t45 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r10: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        aLen,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        r0,
    );
    let mut r11: uint64_t = r10;
    let mut c6: uint64_t = r11;
    let mut c60: uint64_t = c6;
    let mut c7: uint64_t = c5.wrapping_add(c60);
    let mut r: *mut uint64_t = res.offset(aLen as isize).offset(aLen2 as isize);
    let mut c01: uint64_t = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
        0 as libc::c_ulonglong,
        *r.offset(0 as libc::c_uint as isize),
        c7,
        r,
    );
    let mut r1: uint64_t = 0;
    if (1 as libc::c_uint)
        < aLen.wrapping_add(aLen).wrapping_sub(aLen.wrapping_add(aLen2))
    {
        let mut res1: *mut uint64_t = r.offset(1 as libc::c_uint as isize);
        let mut c: uint64_t = c01;
        let mut i_2: uint32_t = 0 as libc::c_uint;
        while i_2
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(4 as libc::c_uint)
        {
            let mut t11: uint64_t = *res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
            let mut res_i0: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t11,
                0 as libc::c_ulonglong,
                res_i0,
            );
            let mut t110: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t110,
                0 as libc::c_ulonglong,
                res_i1,
            );
            let mut t111: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t111,
                0 as libc::c_ulonglong,
                res_i2,
            );
            let mut t112: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t112,
                0 as libc::c_ulonglong,
                res_i,
            );
            i_2 = i_2.wrapping_add(1);
            i_2;
        }
        let mut i_3: uint32_t = aLen
            .wrapping_add(aLen)
            .wrapping_sub(aLen.wrapping_add(aLen2))
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_3
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
        {
            let mut t11_0: uint64_t = *res1.offset(i_3 as isize);
            let mut res_i_0: *mut uint64_t = res1.offset(i_3 as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t11_0,
                0 as libc::c_ulonglong,
                res_i_0,
            );
            i_3 = i_3.wrapping_add(1);
            i_3;
        }
        let mut c110: uint64_t = c;
        r1 = c110;
    } else {
        r1 = c01;
    }
    let mut c8: uint64_t = r1;
    let mut c_0: uint64_t = c8;
    let mut c9: uint64_t = c_0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(
    mut aLen: uint32_t,
    mut a: *mut uint32_t,
    mut tmp: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if aLen < 32 as libc::c_uint
        || aLen.wrapping_rem(2 as libc::c_uint) == 1 as libc::c_uint
    {
        Hacl_Bignum_Multiplication_bn_sqr_u32(aLen, a, res);
        return;
    }
    let mut len2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut a0: *mut uint32_t = a;
    let mut a1: *mut uint32_t = a.offset(len2 as isize);
    let mut t0: *mut uint32_t = tmp;
    let mut tmp_: *mut uint32_t = tmp.offset(aLen as isize);
    let mut c0: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a0, a1, tmp_);
    let mut c1: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(len2, a1, a0, t0);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len2 {
        let mut x: uint32_t = (0 as libc::c_uint).wrapping_sub(c0)
            & *t0.offset(i as isize)
            | !(0 as libc::c_uint).wrapping_sub(c0) & *tmp_.offset(i as isize);
        let mut os: *mut uint32_t = t0;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    let mut c00: uint32_t = c0;
    let mut t23: *mut uint32_t = tmp.offset(aLen as isize);
    let mut tmp1: *mut uint32_t = tmp.offset(aLen as isize).offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, t0, tmp1, t23);
    let mut r01: *mut uint32_t = res;
    let mut r23: *mut uint32_t = res.offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, a0, tmp1, r01);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(len2, a1, tmp1, r23);
    let mut r011: *mut uint32_t = res;
    let mut r231: *mut uint32_t = res.offset(aLen as isize);
    let mut t01: *mut uint32_t = tmp;
    let mut t231: *mut uint32_t = tmp.offset(aLen as isize);
    let mut t45: *mut uint32_t = tmp
        .offset((2 as libc::c_uint).wrapping_mul(aLen) as isize);
    let mut c2: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(aLen, r011, r231, t01);
    let mut c3: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(aLen, t01, t231, t45);
    let mut c5: uint32_t = c2.wrapping_sub(c3);
    let mut aLen2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut r0: *mut uint32_t = res.offset(aLen2 as isize);
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            348 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = aLen as usize;
    let mut a_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            351 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = aLen as usize;
    let mut b_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        r0 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        t45 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut r10: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(
        aLen,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        r0,
    );
    let mut r11: uint32_t = r10;
    let mut c4: uint32_t = r11;
    let mut c6: uint32_t = c4;
    let mut c7: uint32_t = c5.wrapping_add(c6);
    let mut r: *mut uint32_t = res.offset(aLen as isize).offset(aLen2 as isize);
    let mut c01: uint32_t = Hacl_IntTypes_Intrinsics_add_carry_u32(
        0 as libc::c_uint,
        *r.offset(0 as libc::c_uint as isize),
        c7,
        r,
    );
    let mut r1: uint32_t = 0;
    if (1 as libc::c_uint)
        < aLen.wrapping_add(aLen).wrapping_sub(aLen.wrapping_add(aLen2))
    {
        let mut res1: *mut uint32_t = r.offset(1 as libc::c_uint as isize);
        let mut c: uint32_t = c01;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(4 as libc::c_uint)
        {
            let mut t1: uint32_t = *res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
            let mut res_i0: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1, 0 as libc::c_uint, res_i0);
            let mut t10: uint32_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t10,
                0 as libc::c_uint,
                res_i1,
            );
            let mut t11: uint32_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t11,
                0 as libc::c_uint,
                res_i2,
            );
            let mut t12: uint32_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12, 0 as libc::c_uint, res_i);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut i_1: uint32_t = aLen
            .wrapping_add(aLen)
            .wrapping_sub(aLen.wrapping_add(aLen2))
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_1
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
        {
            let mut t1_0: uint32_t = *res1.offset(i_1 as isize);
            let mut res_i_0: *mut uint32_t = res1.offset(i_1 as isize);
            c = Hacl_IntTypes_Intrinsics_add_carry_u32(
                c,
                t1_0,
                0 as libc::c_uint,
                res_i_0,
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut c10: uint32_t = c;
        r1 = c10;
    } else {
        r1 = c01;
    }
    let mut c8: uint32_t = r1;
    let mut c_0: uint32_t = c8;
    let mut c9: uint32_t = c_0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
    mut aLen: uint32_t,
    mut a: *mut uint64_t,
    mut tmp: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if aLen < 32 as libc::c_uint
        || aLen.wrapping_rem(2 as libc::c_uint) == 1 as libc::c_uint
    {
        Hacl_Bignum_Multiplication_bn_sqr_u64(aLen, a, res);
        return;
    }
    let mut len2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut a0: *mut uint64_t = a;
    let mut a1: *mut uint64_t = a.offset(len2 as isize);
    let mut t0: *mut uint64_t = tmp;
    let mut tmp_: *mut uint64_t = tmp.offset(aLen as isize);
    let mut c0: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a0, a1, tmp_);
    let mut c1: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(len2, a1, a0, t0);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len2 {
        let mut x: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c0)
            & *t0.offset(i as isize)
            | !(0 as libc::c_ulonglong).wrapping_sub(c0) & *tmp_.offset(i as isize);
        let mut os: *mut uint64_t = t0;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    let mut c00: uint64_t = c0;
    let mut t23: *mut uint64_t = tmp.offset(aLen as isize);
    let mut tmp1: *mut uint64_t = tmp.offset(aLen as isize).offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, t0, tmp1, t23);
    let mut r01: *mut uint64_t = res;
    let mut r23: *mut uint64_t = res.offset(aLen as isize);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a0, tmp1, r01);
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(len2, a1, tmp1, r23);
    let mut r011: *mut uint64_t = res;
    let mut r231: *mut uint64_t = res.offset(aLen as isize);
    let mut t01: *mut uint64_t = tmp;
    let mut t231: *mut uint64_t = tmp.offset(aLen as isize);
    let mut t45: *mut uint64_t = tmp
        .offset((2 as libc::c_uint).wrapping_mul(aLen) as isize);
    let mut c2: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(aLen, r011, r231, t01);
    let mut c3: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(aLen, t01, t231, t45);
    let mut c5: uint64_t = c2.wrapping_sub(c3);
    let mut aLen2: uint32_t = aLen.wrapping_div(2 as libc::c_uint);
    let mut r0: *mut uint64_t = res.offset(aLen2 as isize);
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            457 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = aLen as usize;
    let mut a_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if aLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            460 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = aLen as usize;
    let mut b_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        r0 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        t45 as *const libc::c_void,
        (aLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r10: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        aLen,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        r0,
    );
    let mut r11: uint64_t = r10;
    let mut c4: uint64_t = r11;
    let mut c6: uint64_t = c4;
    let mut c7: uint64_t = c5.wrapping_add(c6);
    let mut r: *mut uint64_t = res.offset(aLen as isize).offset(aLen2 as isize);
    let mut c01: uint64_t = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
        0 as libc::c_ulonglong,
        *r.offset(0 as libc::c_uint as isize),
        c7,
        r,
    );
    let mut r1: uint64_t = 0;
    if (1 as libc::c_uint)
        < aLen.wrapping_add(aLen).wrapping_sub(aLen.wrapping_add(aLen2))
    {
        let mut res1: *mut uint64_t = r.offset(1 as libc::c_uint as isize);
        let mut c: uint64_t = c01;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(4 as libc::c_uint)
        {
            let mut t1: uint64_t = *res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
            let mut res_i0: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t1,
                0 as libc::c_ulonglong,
                res_i0,
            );
            let mut t10: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t10,
                0 as libc::c_ulonglong,
                res_i1,
            );
            let mut t11: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t11,
                0 as libc::c_ulonglong,
                res_i2,
            );
            let mut t12: uint64_t = *res1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint64_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t12,
                0 as libc::c_ulonglong,
                res_i,
            );
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut i_1: uint32_t = aLen
            .wrapping_add(aLen)
            .wrapping_sub(aLen.wrapping_add(aLen2))
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_1
            < aLen
                .wrapping_add(aLen)
                .wrapping_sub(aLen.wrapping_add(aLen2))
                .wrapping_sub(1 as libc::c_uint)
        {
            let mut t1_0: uint64_t = *res1.offset(i_1 as isize);
            let mut res_i_0: *mut uint64_t = res1.offset(i_1 as isize);
            c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(
                c,
                t1_0,
                0 as libc::c_ulonglong,
                res_i_0,
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut c10: uint64_t = c;
        r1 = c10;
    } else {
        r1 = c01;
    }
    let mut c8: uint64_t = r1;
    let mut c_0: uint64_t = c8;
    let mut c9: uint64_t = c_0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_bn_add_mod_n_u32(
    mut len1: uint32_t,
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
        let mut t10: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
        let mut t11: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
        let mut t12: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < len1 {
        let mut t1_0: uint32_t = *a.offset(i_0 as isize);
        let mut t2_0: uint32_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint32_t = res.offset(i_0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c00: uint32_t = c0;
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            554 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len1 as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1_1: uint32_t = *res
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut t20_0: uint32_t = *n
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_1, t20_0, res_i0_0);
        let mut t10_0: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21_0: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10_0, t21_0, res_i1_0);
        let mut t11_0: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22_0: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11_0, t22_0, res_i2_0);
        let mut t12_0: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2_1: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12_0, t2_1, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len1 {
        let mut t1_2: uint32_t = *res.offset(i_2 as isize);
        let mut t2_2: uint32_t = *n.offset(i_2 as isize);
        let mut res_i_2: *mut uint32_t = tmp.as_mut_ptr().offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_2, t2_2, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut c1: uint32_t = c;
    let mut c2: uint32_t = c00.wrapping_sub(c1);
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < len1 {
        let mut x: uint32_t = c2 & *res.offset(i_3 as isize)
            | !c2 & *tmp.as_mut_ptr().offset(i_3 as isize);
        let mut os: *mut uint32_t = res;
        *os.offset(i_3 as isize) = x;
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_bn_add_mod_n_u64(
    mut len1: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint64_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t1, t20, res_i0);
        let mut t10: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t10, t21, res_i1);
        let mut t11: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t11, t22, res_i2);
        let mut t12: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < len1 {
        let mut t1_0: uint64_t = *a.offset(i_0 as isize);
        let mut t2_0: uint64_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res.offset(i_0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c00: uint64_t = c0;
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            631 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len1 as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1_1: uint64_t = *res
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut t20_0: uint64_t = *n
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1_1, t20_0, res_i0_0);
        let mut t10_0: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21_0: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t10_0, t21_0, res_i1_0);
        let mut t11_0: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22_0: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t11_0, t22_0, res_i2_0);
        let mut t12_0: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2_1: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t12_0, t2_1, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len1 {
        let mut t1_2: uint64_t = *res.offset(i_2 as isize);
        let mut t2_2: uint64_t = *n.offset(i_2 as isize);
        let mut res_i_2: *mut uint64_t = tmp.as_mut_ptr().offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1_2, t2_2, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = c00.wrapping_sub(c1);
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < len1 {
        let mut x: uint64_t = c2 & *res.offset(i_3 as isize)
            | !c2 & *tmp.as_mut_ptr().offset(i_3 as isize);
        let mut os: *mut uint64_t = res;
        *os.offset(i_3 as isize) = x;
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_bn_sub_mod_n_u32(
    mut len1: uint32_t,
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
        let mut t10: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
        let mut t11: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
        let mut t12: uint32_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint32_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint32_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < len1 {
        let mut t1_0: uint32_t = *a.offset(i_0 as isize);
        let mut t2_0: uint32_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint32_t = res.offset(i_0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c00: uint32_t = c0;
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            708 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len1 as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1_1: uint32_t = *res
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut t20_0: uint32_t = *n
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1_1, t20_0, res_i0_0);
        let mut t10_0: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21_0: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t10_0, t21_0, res_i1_0);
        let mut t11_0: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22_0: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t11_0, t22_0, res_i2_0);
        let mut t12_0: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2_1: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12_0, t2_1, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len1 {
        let mut t1_2: uint32_t = *res.offset(i_2 as isize);
        let mut t2_2: uint32_t = *n.offset(i_2 as isize);
        let mut res_i_2: *mut uint32_t = tmp.as_mut_ptr().offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1_2, t2_2, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut c1: uint32_t = c;
    let mut c2: uint32_t = (0 as libc::c_uint).wrapping_sub(c00);
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < len1 {
        let mut x: uint32_t = c2 & *tmp.as_mut_ptr().offset(i_3 as isize)
            | !c2 & *res.offset(i_3 as isize);
        let mut os: *mut uint32_t = res;
        *os.offset(i_3 as isize) = x;
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_bn_sub_mod_n_u64(
    mut len1: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut t20: uint64_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        let mut res_i0: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t1, t20, res_i0);
        let mut t10: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(1 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t10, t21, res_i1);
        let mut t11: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(2 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t11, t22, res_i2);
        let mut t12: uint64_t = *a
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *b
            .offset(
                (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i: *mut uint64_t = res
            .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
            .offset(3 as libc::c_uint as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t12, t2, res_i);
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_0 < len1 {
        let mut t1_0: uint64_t = *a.offset(i_0 as isize);
        let mut t2_0: uint64_t = *b.offset(i_0 as isize);
        let mut res_i_0: *mut uint64_t = res.offset(i_0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t1_0, t2_0, res_i_0);
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut c00: uint64_t = c0;
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            786 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len1 as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len1.wrapping_div(4 as libc::c_uint) {
        let mut t1_1: uint64_t = *res
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut t20_0: uint64_t = *n
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1_1, t20_0, res_i0_0);
        let mut t10_0: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21_0: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10_0, t21_0, res_i1_0);
        let mut t11_0: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22_0: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11_0, t22_0, res_i2_0);
        let mut t12_0: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2_1: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12_0, t2_1, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len1
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len1 {
        let mut t1_2: uint64_t = *res.offset(i_2 as isize);
        let mut t2_2: uint64_t = *n.offset(i_2 as isize);
        let mut res_i_2: *mut uint64_t = tmp.as_mut_ptr().offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1_2, t2_2, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c00);
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < len1 {
        let mut x: uint64_t = c2 & *tmp.as_mut_ptr().offset(i_3 as isize)
            | !c2 & *res.offset(i_3 as isize);
        let mut os: *mut uint64_t = res;
        *os.offset(i_3 as isize) = x;
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_ModInvLimb_mod_inv_uint32(
    mut n0: uint32_t,
) -> uint32_t {
    let mut alpha: uint32_t = 2147483648 as libc::c_uint;
    let mut beta: uint32_t = n0;
    let mut ub: uint32_t = 0 as libc::c_uint;
    let mut vb: uint32_t = 0 as libc::c_uint;
    ub = 1 as libc::c_uint;
    vb = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 32 as libc::c_uint {
        let mut us: uint32_t = ub;
        let mut vs: uint32_t = vb;
        let mut u_is_odd: uint32_t = (0 as libc::c_uint)
            .wrapping_sub(us & 1 as libc::c_uint);
        let mut beta_if_u_is_odd: uint32_t = beta & u_is_odd;
        ub = ((us ^ beta_if_u_is_odd) >> 1 as libc::c_uint)
            .wrapping_add(us & beta_if_u_is_odd);
        let mut alpha_if_u_is_odd: uint32_t = alpha & u_is_odd;
        vb = (vs >> 1 as libc::c_uint).wrapping_add(alpha_if_u_is_odd);
        i = i.wrapping_add(1);
        i;
    }
    return vb;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_ModInvLimb_mod_inv_uint64(
    mut n0: uint64_t,
) -> uint64_t {
    let mut alpha: uint64_t = 9223372036854775808 as libc::c_ulonglong;
    let mut beta: uint64_t = n0;
    let mut ub: uint64_t = 0 as libc::c_ulonglong;
    let mut vb: uint64_t = 0 as libc::c_ulonglong;
    ub = 1 as libc::c_ulonglong;
    vb = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 64 as libc::c_uint {
        let mut us: uint64_t = ub;
        let mut vs: uint64_t = vb;
        let mut u_is_odd: uint64_t = (0 as libc::c_ulonglong)
            .wrapping_sub(us & 1 as libc::c_ulonglong);
        let mut beta_if_u_is_odd: uint64_t = beta & u_is_odd;
        ub = ((us ^ beta_if_u_is_odd) >> 1 as libc::c_uint)
            .wrapping_add(us & beta_if_u_is_odd);
        let mut alpha_if_u_is_odd: uint64_t = alpha & u_is_odd;
        vb = (vs >> 1 as libc::c_uint).wrapping_add(alpha_if_u_is_odd);
        i = i.wrapping_add(1);
        i;
    }
    return vb;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_check_modulus_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
) -> uint32_t {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            871 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut one: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    *one.as_mut_ptr().offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    let mut bit0: uint32_t = *n.offset(0 as libc::c_uint as isize) & 1 as libc::c_uint;
    let mut m0: uint32_t = (0 as libc::c_uint).wrapping_sub(bit0);
    let mut acc: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut beq: uint32_t = FStar_UInt32_eq_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        let mut blt: uint32_t = !FStar_UInt32_gte_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        acc = beq & acc | !beq & blt;
        i = i.wrapping_add(1);
        i;
    }
    let mut m1: uint32_t = acc;
    return m0 & m1;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(
    mut len: uint32_t,
    mut nBits: uint32_t,
    mut n: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = nBits.wrapping_div(32 as libc::c_uint);
    let mut j: uint32_t = nBits.wrapping_rem(32 as libc::c_uint);
    *res.offset(i as isize) = *res.offset(i as isize) | (1 as libc::c_uint) << j;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (64 as libc::c_uint).wrapping_mul(len).wrapping_sub(nBits) {
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                903 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = len as usize;
        let mut a_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
        memset(
            a_copy.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                906 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len as usize;
        let mut b_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            a_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        Hacl_Bignum_bn_add_mod_n_u32(
            len,
            n,
            a_copy.as_mut_ptr(),
            b_copy.as_mut_ptr(),
            res,
        );
        i0 = i0.wrapping_add(1);
        i0;
    }
}
unsafe extern "C" fn bn_mont_reduction_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv: uint32_t,
    mut c: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < len {
        let mut qj: uint32_t = nInv * *c.offset(i0 as isize);
        let mut res_j0: *mut uint32_t = c.offset(i0 as isize);
        let mut c1: uint32_t = 0 as libc::c_uint;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < len.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint32_t = *n
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
            let mut a_i0: uint32_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
            let mut a_i1: uint32_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
            let mut a_i2: uint32_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = len
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < len {
            let mut a_i_0: uint32_t = *n.offset(i_0 as isize);
            let mut res_i_0: *mut uint32_t = res_j0.offset(i_0 as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, qj, c1, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint32_t = c1;
        let mut c10: uint32_t = r;
        let mut res_j: uint32_t = *c.offset(len.wrapping_add(i0) as isize);
        let mut resb: *mut uint32_t = c.offset(len as isize).offset(i0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
        i0 = i0.wrapping_add(1);
        i0;
    }
    memcpy(
        res as *mut libc::c_void,
        c.offset(len as isize) as *const libc::c_void,
        (len.wrapping_add(len).wrapping_sub(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c00: uint32_t = c0;
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            953 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c1_0: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint32_t = *res
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut t20: uint32_t = *n
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_0, t1, t20, res_i0_0);
        let mut t10: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_0, t10, t21, res_i1_0);
        let mut t11: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_0, t11, t22, res_i2_0);
        let mut t12: uint32_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint32_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint32_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_0, t12, t2, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len {
        let mut t1_0: uint32_t = *res.offset(i_2 as isize);
        let mut t2_0: uint32_t = *n.offset(i_2 as isize);
        let mut res_i_2: *mut uint32_t = tmp.as_mut_ptr().offset(i_2 as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_0, t1_0, t2_0, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut c10_0: uint32_t = c1_0;
    let mut c2: uint32_t = c00.wrapping_sub(c10_0);
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < len {
        let mut x: uint32_t = c2 & *res.offset(i_3 as isize)
            | !c2 & *tmp.as_mut_ptr().offset(i_3 as isize);
        let mut os: *mut uint32_t = res;
        *os.offset(i_3 as isize) = x;
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_to_mont_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut aM: *mut uint32_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1003 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1006 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
        len,
        a,
        r2,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    bn_mont_reduction_u32(len, n, nInv, c.as_mut_ptr(), aM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_from_mont_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut a: *mut uint32_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1022 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        tmp.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    bn_mont_reduction_u32(len, n, nInv_u64, tmp.as_mut_ptr(), a);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_mont_mul_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut bM: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1039 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1042 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
        len,
        aM,
        bM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    bn_mont_reduction_u32(len, n, nInv_u64, c.as_mut_ptr(), resM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1058 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1061 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(
        len,
        aM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    bn_mont_reduction_u32(len, n, nInv_u64, c.as_mut_ptr(), resM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_check_modulus_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
) -> uint64_t {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1070 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut one: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    *one.as_mut_ptr().offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    let mut bit0: uint64_t = *n.offset(0 as libc::c_uint as isize)
        & 1 as libc::c_ulonglong;
    let mut m0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bit0);
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut beq: uint64_t = FStar_UInt64_eq_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        let mut blt: uint64_t = !FStar_UInt64_gte_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        acc = beq & acc | !beq & blt;
        i = i.wrapping_add(1);
        i;
    }
    let mut m1: uint64_t = acc;
    return m0 & m1;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
    mut len: uint32_t,
    mut nBits: uint32_t,
    mut n: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = nBits.wrapping_div(64 as libc::c_uint);
    let mut j: uint32_t = nBits.wrapping_rem(64 as libc::c_uint);
    *res.offset(i as isize) = *res.offset(i as isize) | (1 as libc::c_ulonglong) << j;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (128 as libc::c_uint).wrapping_mul(len).wrapping_sub(nBits) {
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1102 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = len as usize;
        let mut a_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
        memset(
            a_copy.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1105 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len as usize;
        let mut b_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            a_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Bignum_bn_add_mod_n_u64(
            len,
            n,
            a_copy.as_mut_ptr(),
            b_copy.as_mut_ptr(),
            res,
        );
        i0 = i0.wrapping_add(1);
        i0;
    }
}
unsafe extern "C" fn bn_mont_reduction_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv: uint64_t,
    mut c: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < len {
        let mut qj: uint64_t = nInv * *c.offset(i0 as isize);
        let mut res_j0: *mut uint64_t = c.offset(i0 as isize);
        let mut c1: uint64_t = 0 as libc::c_ulonglong;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < len.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint64_t = *n
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
            let mut a_i0: uint64_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
            let mut a_i1: uint64_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
            let mut a_i2: uint64_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = len
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < len {
            let mut a_i_0: uint64_t = *n.offset(i_0 as isize);
            let mut res_i_0: *mut uint64_t = res_j0.offset(i_0 as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, qj, c1, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint64_t = c1;
        let mut c10: uint64_t = r;
        let mut res_j: uint64_t = *c.offset(len.wrapping_add(i0) as isize);
        let mut resb: *mut uint64_t = c.offset(len as isize).offset(i0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10, res_j, resb);
        i0 = i0.wrapping_add(1);
        i0;
    }
    memcpy(
        res as *mut libc::c_void,
        c.offset(len as isize) as *const libc::c_void,
        (len.wrapping_add(len).wrapping_sub(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c00: uint64_t = c0;
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1152 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c1_0: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len.wrapping_div(4 as libc::c_uint) {
        let mut t1: uint64_t = *res
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut t20: uint64_t = *n
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_0, t1, t20, res_i0_0);
        let mut t10: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut t21: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_0, t10, t21, res_i1_0);
        let mut t11: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut t22: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_0, t11, t22, res_i2_0);
        let mut t12: uint64_t = *res
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut t2: uint64_t = *n
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint64_t = tmp
            .as_mut_ptr()
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_0, t12, t2, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = len
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < len {
        let mut t1_0: uint64_t = *res.offset(i_2 as isize);
        let mut t2_0: uint64_t = *n.offset(i_2 as isize);
        let mut res_i_2: *mut uint64_t = tmp.as_mut_ptr().offset(i_2 as isize);
        c1_0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_0, t1_0, t2_0, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut c10_0: uint64_t = c1_0;
    let mut c2: uint64_t = c00.wrapping_sub(c10_0);
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < len {
        let mut x: uint64_t = c2 & *res.offset(i_3 as isize)
            | !c2 & *tmp.as_mut_ptr().offset(i_3 as isize);
        let mut os: *mut uint64_t = res;
        *os.offset(i_3 as isize) = x;
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_to_mont_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut aM: *mut uint64_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1202 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1205 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
        len,
        a,
        r2,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    bn_mont_reduction_u64(len, n, nInv, c.as_mut_ptr(), aM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_from_mont_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut a: *mut uint64_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1221 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        tmp.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    bn_mont_reduction_u64(len, n, nInv_u64, tmp.as_mut_ptr(), a);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_mont_mul_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut bM: *mut uint64_t,
    mut resM: *mut uint64_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1238 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1241 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
        len,
        aM,
        bM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    bn_mont_reduction_u64(len, n, nInv_u64, c.as_mut_ptr(), resM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Montgomery_bn_mont_sqr_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut resM: *mut uint64_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1257 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1260 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
        len,
        aM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    bn_mont_reduction_u64(len, n, nInv_u64, c.as_mut_ptr(), resM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv: uint32_t,
    mut c: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < len {
        let mut qj: uint32_t = nInv * *c.offset(i0 as isize);
        let mut res_j0: *mut uint32_t = c.offset(i0 as isize);
        let mut c1: uint32_t = 0 as libc::c_uint;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < len.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint32_t = *n
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
            let mut a_i0: uint32_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
            let mut a_i1: uint32_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
            let mut a_i2: uint32_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = len
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < len {
            let mut a_i_0: uint32_t = *n.offset(i_0 as isize);
            let mut res_i_0: *mut uint32_t = res_j0.offset(i_0 as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, qj, c1, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint32_t = c1;
        let mut c10: uint32_t = r;
        let mut res_j: uint32_t = *c.offset(len.wrapping_add(i0) as isize);
        let mut resb: *mut uint32_t = c.offset(len as isize).offset(i0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
        i0 = i0.wrapping_add(1);
        i0;
    }
    memcpy(
        res as *mut libc::c_void,
        c.offset(len as isize) as *const libc::c_void,
        (len.wrapping_add(len).wrapping_sub(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c00: uint32_t = c0;
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1311 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c1_0: uint32_t = Hacl_Bignum_Addition_bn_sub_eq_len_u32(
        len,
        res,
        n,
        tmp.as_mut_ptr(),
    );
    let mut m: uint32_t = (0 as libc::c_uint).wrapping_sub(c00);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len {
        let mut x: uint32_t = m & *tmp.as_mut_ptr().offset(i_1 as isize)
            | !m & *res.offset(i_1 as isize);
        let mut os: *mut uint32_t = res;
        *os.offset(i_1 as isize) = x;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
}
unsafe extern "C" fn bn_almost_mont_mul_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut bM: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1335 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1338 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
        len,
        aM,
        bM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(
        len,
        n,
        nInv_u64,
        c.as_mut_ptr(),
        resM,
    );
}
unsafe extern "C" fn bn_almost_mont_sqr_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1354 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1357 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(
        len,
        aM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u32(
        len,
        n,
        nInv_u64,
        c.as_mut_ptr(),
        resM,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv: uint64_t,
    mut c: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < len {
        let mut qj: uint64_t = nInv * *c.offset(i0 as isize);
        let mut res_j0: *mut uint64_t = c.offset(i0 as isize);
        let mut c1: uint64_t = 0 as libc::c_ulonglong;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < len.wrapping_div(4 as libc::c_uint) {
            let mut a_i: uint64_t = *n
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
            let mut a_i0: uint64_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
            let mut a_i1: uint64_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
            let mut a_i2: uint64_t = *n
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint64_t = res_j0
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = len
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < len {
            let mut a_i_0: uint64_t = *n.offset(i_0 as isize);
            let mut res_i_0: *mut uint64_t = res_j0.offset(i_0 as isize);
            c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, qj, c1, res_i_0);
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut r: uint64_t = c1;
        let mut c10: uint64_t = r;
        let mut res_j: uint64_t = *c.offset(len.wrapping_add(i0) as isize);
        let mut resb: *mut uint64_t = c.offset(len as isize).offset(i0 as isize);
        c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10, res_j, resb);
        i0 = i0.wrapping_add(1);
        i0;
    }
    memcpy(
        res as *mut libc::c_void,
        c.offset(len as isize) as *const libc::c_void,
        (len.wrapping_add(len).wrapping_sub(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c00: uint64_t = c0;
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1408 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c1_0: uint64_t = Hacl_Bignum_Addition_bn_sub_eq_len_u64(
        len,
        res,
        n,
        tmp.as_mut_ptr(),
    );
    let mut m: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c00);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len {
        let mut x: uint64_t = m & *tmp.as_mut_ptr().offset(i_1 as isize)
            | !m & *res.offset(i_1 as isize);
        let mut os: *mut uint64_t = res;
        *os.offset(i_1 as isize) = x;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
}
unsafe extern "C" fn bn_almost_mont_mul_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut bM: *mut uint64_t,
    mut resM: *mut uint64_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1432 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1435 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
        len,
        aM,
        bM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(
        len,
        n,
        nInv_u64,
        c.as_mut_ptr(),
        resM,
    );
}
unsafe extern "C" fn bn_almost_mont_sqr_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut resM: *mut uint64_t,
) {
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1451 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(len) as usize;
    let mut c: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        c.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (4 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1454 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = (4 as libc::c_uint).wrapping_mul(len) as usize;
    let mut tmp: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((4 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
        len,
        aM,
        tmp.as_mut_ptr(),
        c.as_mut_ptr(),
    );
    Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64(
        len,
        n,
        nInv_u64,
        c.as_mut_ptr(),
        resM,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
) -> uint32_t {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1470 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut one: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    *one.as_mut_ptr().offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    let mut bit0: uint32_t = *n.offset(0 as libc::c_uint as isize) & 1 as libc::c_uint;
    let mut m0: uint32_t = (0 as libc::c_uint).wrapping_sub(bit0);
    let mut acc0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut beq: uint32_t = FStar_UInt32_eq_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        let mut blt: uint32_t = !FStar_UInt32_gte_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        acc0 = beq & acc0 | !beq & blt;
        i = i.wrapping_add(1);
        i;
    }
    let mut m10: uint32_t = acc0;
    let mut m00: uint32_t = m0 & m10;
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(32 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    let mut m1: uint32_t = 0;
    if bBits < (32 as libc::c_uint).wrapping_mul(bLen) {
        if bLen as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1498 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = bLen as usize;
        let mut b2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            b2.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (bLen as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i0: uint32_t = bBits.wrapping_div(32 as libc::c_uint);
        let mut j: uint32_t = bBits.wrapping_rem(32 as libc::c_uint);
        *b2
            .as_mut_ptr()
            .offset(
                i0 as isize,
            ) = *b2.as_mut_ptr().offset(i0 as isize) | (1 as libc::c_uint) << j;
        let mut acc: uint32_t = 0 as libc::c_uint;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0 < bLen {
            let mut beq_0: uint32_t = FStar_UInt32_eq_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            let mut blt_0: uint32_t = !FStar_UInt32_gte_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            acc = beq_0 & acc | !beq_0 & blt_0;
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut res: uint32_t = acc;
        m1 = res;
    } else {
        m1 = 0xffffffff as libc::c_uint;
    }
    let mut acc_0: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len {
        let mut beq_1: uint32_t = FStar_UInt32_eq_mask(
            *a.offset(i_1 as isize),
            *n.offset(i_1 as isize),
        );
        let mut blt_1: uint32_t = !FStar_UInt32_gte_mask(
            *a.offset(i_1 as isize),
            *n.offset(i_1 as isize),
        );
        acc_0 = beq_1 & acc_0 | !beq_1 & blt_1;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut m2: uint32_t = acc_0;
    let mut m: uint32_t = m1 & m2;
    return m00 & m;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut mu: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if bBits < 200 as libc::c_uint {
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1544 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = len as usize;
        let mut aM: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
        memset(
            aM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM.as_mut_ptr());
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1548 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len as usize;
        let mut resM: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            resM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if len.wrapping_add(len) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1551 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len.wrapping_add(len) as usize;
        let mut ctx: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            ctx.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len.wrapping_add(len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n0: *mut uint32_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint32_t = ctx.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(
            len,
            ctx_n0,
            mu,
            ctx_r2,
            resM.as_mut_ptr(),
        );
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < bBits {
            let mut i1: uint32_t = i.wrapping_div(32 as libc::c_uint);
            let mut j: uint32_t = i.wrapping_rem(32 as libc::c_uint);
            let mut tmp: uint32_t = *b.offset(i1 as isize);
            let mut bit: uint32_t = tmp >> j & 1 as libc::c_uint;
            if !(bit == 0 as libc::c_uint) {
                if len as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(
                            ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
                        )
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                        1568 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = len as usize;
                let mut aM_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    aM_copy.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (len as libc::c_ulong)
                        .wrapping_mul(
                            ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
                        ),
                );
                memcpy(
                    aM_copy.as_mut_ptr() as *mut libc::c_void,
                    resM.as_mut_ptr() as *const libc::c_void,
                    (len as libc::c_ulong)
                        .wrapping_mul(
                            ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
                        ),
                );
                let mut ctx_n: *mut uint32_t = ctx.as_mut_ptr();
                bn_almost_mont_mul_u32(
                    len,
                    ctx_n,
                    mu,
                    aM_copy.as_mut_ptr(),
                    aM.as_mut_ptr(),
                    resM.as_mut_ptr(),
                );
            }
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                    1576 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_3 = len as usize;
            let mut aM_copy_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_3);
            memset(
                aM_copy_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            memcpy(
                aM_copy_0.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n_0: *mut uint32_t = ctx.as_mut_ptr();
            bn_almost_mont_sqr_u32(
                len,
                ctx_n_0,
                mu,
                aM_copy_0.as_mut_ptr(),
                aM.as_mut_ptr(),
            );
            i = i.wrapping_add(1);
            i;
        }
        Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM.as_mut_ptr(), res);
        return;
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1587 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_4 = len as usize;
    let mut aM_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_4);
    memset(
        aM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM_0.as_mut_ptr());
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1591 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = len as usize;
    let mut resM_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        resM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(32 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1603 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_6 = len.wrapping_add(len) as usize;
    let mut ctx_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_6);
    memset(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (16 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1608 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_7 = (16 as libc::c_uint).wrapping_mul(len) as usize;
    let mut table: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_7);
    memset(
        table.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((16 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1611 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_8 = len as usize;
    let mut tmp_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_8);
    memset(
        tmp_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t0: *mut uint32_t = table.as_mut_ptr();
    let mut t1: *mut uint32_t = table.as_mut_ptr().offset(len as isize);
    let mut ctx_n0_0: *mut uint32_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint32_t = ctx_0.as_mut_ptr().offset(len as isize);
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_9 = len as usize;
    let mut aM_copy0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_9);
    memset(
        aM_copy0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(len, ctx_n1, mu, aM_copy0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_10 = len as usize;
    let mut aM_copy_1: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_10);
    memset(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_1,
        mu,
        aM_copy_1.as_mut_ptr(),
        t2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_11 = len as usize;
    let mut aM_copy0_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_11);
    memset(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_0,
        mu,
        aM_copy0_0.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_12 = len as usize;
    let mut aM_copy_2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_12);
    memset(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_2,
        mu,
        aM_copy_2.as_mut_ptr(),
        t2_0,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_13 = len as usize;
    let mut aM_copy0_1: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_13);
    memset(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_1,
        mu,
        aM_copy0_1.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_14 = len as usize;
    let mut aM_copy_3: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_14);
    memset(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_3,
        mu,
        aM_copy_3.as_mut_ptr(),
        t2_1,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_15 = len as usize;
    let mut aM_copy0_2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_15);
    memset(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_2,
        mu,
        aM_copy0_2.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_16 = len as usize;
    let mut aM_copy_4: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_16);
    memset(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_4,
        mu,
        aM_copy_4.as_mut_ptr(),
        t2_2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_17 = len as usize;
    let mut aM_copy0_3: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_17);
    memset(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_3,
        mu,
        aM_copy0_3.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_18 = len as usize;
    let mut aM_copy_5: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_18);
    memset(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_5,
        mu,
        aM_copy_5.as_mut_ptr(),
        t2_3,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_19 = len as usize;
    let mut aM_copy0_4: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_19);
    memset(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_4,
        mu,
        aM_copy0_4.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_20 = len as usize;
    let mut aM_copy_6: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_20);
    memset(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_6,
        mu,
        aM_copy_6.as_mut_ptr(),
        t2_4,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1627 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_21 = len as usize;
    let mut aM_copy0_5: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_21);
    memset(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_5,
        mu,
        aM_copy0_5.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1636 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_22 = len as usize;
    let mut aM_copy_7: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_22);
    memset(
        aM_copy_7.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_7.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_7: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_7,
        mu,
        aM_copy_7.as_mut_ptr(),
        t2_5,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if bBits.wrapping_rem(4 as libc::c_uint) != 0 as libc::c_uint {
        let mut i_1: uint32_t = bBits
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        let mut bits_c: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
            bLen,
            b,
            i_1,
            4 as libc::c_uint,
        );
        let mut bits_l32: uint32_t = bits_c;
        let mut a_bits_l: *const uint32_t = table
            .as_mut_ptr()
            .offset((bits_l32 * len) as isize);
        memcpy(
            resM_0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l as *mut uint32_t as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
    } else {
        let mut ctx_n_8: *mut uint32_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint32_t = ctx_0.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(
            len,
            ctx_n_8,
            mu,
            ctx_r2_0,
            resM_0.as_mut_ptr(),
        );
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1659 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_23 = len as usize;
    let mut tmp0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_23);
    memset(
        tmp0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i_2: uint32_t = 0 as libc::c_uint;
    while i_2 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i0: uint32_t = 0 as libc::c_uint;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1668 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_24 = len as usize;
        let mut aM_copy_8: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_24);
        memset(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_9,
            mu,
            aM_copy_8.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1668 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_25 = len as usize;
        let mut aM_copy_9: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_25);
        memset(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_10,
            mu,
            aM_copy_9.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1668 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_26 = len as usize;
        let mut aM_copy_10: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_26);
        memset(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_11,
            mu,
            aM_copy_10.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1668 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_27 = len as usize;
        let mut aM_copy_11: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_27);
        memset(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_12,
            mu,
            aM_copy_11.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = bBits
            .wrapping_sub(bBits.wrapping_rem(4 as libc::c_uint))
            .wrapping_sub((4 as libc::c_uint).wrapping_mul(i_2))
            .wrapping_sub(4 as libc::c_uint);
        let mut bits_l: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
            bLen,
            b,
            k,
            4 as libc::c_uint,
        );
        let mut bits_l32_0: uint32_t = bits_l;
        let mut a_bits_l_0: *const uint32_t = table
            .as_mut_ptr()
            .offset((bits_l32_0 * len) as isize);
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l_0 as *mut uint32_t as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1681 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_28 = len as usize;
        let mut aM_copy_12: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_28);
        memset(
            aM_copy_12.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_12.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_13: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_mul_u32(
            len,
            ctx_n_13,
            mu,
            aM_copy_12.as_mut_ptr(),
            tmp0.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM_0.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(
    mut len: uint32_t,
    mut n: *mut uint32_t,
    mut mu: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if bBits < 200 as libc::c_uint {
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1706 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = len as usize;
        let mut aM: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
        memset(
            aM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM.as_mut_ptr());
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1710 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len as usize;
        let mut resM: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            resM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if len.wrapping_add(len) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1713 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len.wrapping_add(len) as usize;
        let mut ctx: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            ctx.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len.wrapping_add(len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut sw: uint32_t = 0 as libc::c_uint;
        let mut ctx_n0: *mut uint32_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint32_t = ctx.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(
            len,
            ctx_n0,
            mu,
            ctx_r2,
            resM.as_mut_ptr(),
        );
        let mut i0: uint32_t = 0 as libc::c_uint;
        while i0 < bBits {
            let mut i1: uint32_t = bBits
                .wrapping_sub(i0)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(32 as libc::c_uint);
            let mut j: uint32_t = bBits
                .wrapping_sub(i0)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_rem(32 as libc::c_uint);
            let mut tmp: uint32_t = *b.offset(i1 as isize);
            let mut bit: uint32_t = tmp >> j & 1 as libc::c_uint;
            let mut sw1: uint32_t = bit ^ sw;
            let mut i: uint32_t = 0 as libc::c_uint;
            while i < len {
                let mut dummy: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                    & (*resM.as_mut_ptr().offset(i as isize)
                        ^ *aM.as_mut_ptr().offset(i as isize));
                *resM
                    .as_mut_ptr()
                    .offset(i as isize) = *resM.as_mut_ptr().offset(i as isize) ^ dummy;
                *aM
                    .as_mut_ptr()
                    .offset(i as isize) = *aM.as_mut_ptr().offset(i as isize) ^ dummy;
                i = i.wrapping_add(1);
                i;
            }
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                    1736 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_2 = len as usize;
            let mut aM_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_2);
            memset(
                aM_copy.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            memcpy(
                aM_copy.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n1: *mut uint32_t = ctx.as_mut_ptr();
            bn_almost_mont_mul_u32(
                len,
                ctx_n1,
                mu,
                aM_copy.as_mut_ptr(),
                resM.as_mut_ptr(),
                aM.as_mut_ptr(),
            );
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                    1743 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_3 = len as usize;
            let mut aM_copy0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_3);
            memset(
                aM_copy0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            memcpy(
                aM_copy0.as_mut_ptr() as *mut libc::c_void,
                resM.as_mut_ptr() as *const libc::c_void,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n: *mut uint32_t = ctx.as_mut_ptr();
            bn_almost_mont_sqr_u32(
                len,
                ctx_n,
                mu,
                aM_copy0.as_mut_ptr(),
                resM.as_mut_ptr(),
            );
            sw = bit;
            i0 = i0.wrapping_add(1);
            i0;
        }
        let mut sw0: uint32_t = sw;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0 < len {
            let mut dummy_0: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
                & (*resM.as_mut_ptr().offset(i_0 as isize)
                    ^ *aM.as_mut_ptr().offset(i_0 as isize));
            *resM
                .as_mut_ptr()
                .offset(
                    i_0 as isize,
                ) = *resM.as_mut_ptr().offset(i_0 as isize) ^ dummy_0;
            *aM
                .as_mut_ptr()
                .offset(i_0 as isize) = *aM.as_mut_ptr().offset(i_0 as isize) ^ dummy_0;
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM.as_mut_ptr(), res);
        return;
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1762 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_4 = len as usize;
    let mut aM_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_4);
    memset(
        aM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_to_mont_u32(len, n, mu, r2, a, aM_0.as_mut_ptr());
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1766 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = len as usize;
    let mut resM_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        resM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(32 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1778 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_6 = len.wrapping_add(len) as usize;
    let mut ctx_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_6);
    memset(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if (16 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1783 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_7 = (16 as libc::c_uint).wrapping_mul(len) as usize;
    let mut table: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_7);
    memset(
        table.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((16 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1786 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_8 = len as usize;
    let mut tmp_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_8);
    memset(
        tmp_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t0: *mut uint32_t = table.as_mut_ptr();
    let mut t1: *mut uint32_t = table.as_mut_ptr().offset(len as isize);
    let mut ctx_n0_0: *mut uint32_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint32_t = ctx_0.as_mut_ptr().offset(len as isize);
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_9 = len as usize;
    let mut aM_copy0_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_9);
    memset(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_0,
        mu,
        aM_copy0_0.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_10 = len as usize;
    let mut aM_copy_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_10);
    memset(
        aM_copy_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_0.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_0: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_0,
        mu,
        aM_copy_0.as_mut_ptr(),
        t2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_11 = len as usize;
    let mut aM_copy0_1: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_11);
    memset(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_1,
        mu,
        aM_copy0_1.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_12 = len as usize;
    let mut aM_copy_1: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_12);
    memset(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_1,
        mu,
        aM_copy_1.as_mut_ptr(),
        t2_0,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_13 = len as usize;
    let mut aM_copy0_2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_13);
    memset(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_2,
        mu,
        aM_copy0_2.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_14 = len as usize;
    let mut aM_copy_2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_14);
    memset(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_2,
        mu,
        aM_copy_2.as_mut_ptr(),
        t2_1,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_15 = len as usize;
    let mut aM_copy0_3: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_15);
    memset(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_3,
        mu,
        aM_copy0_3.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_16 = len as usize;
    let mut aM_copy_3: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_16);
    memset(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_3,
        mu,
        aM_copy_3.as_mut_ptr(),
        t2_2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_17 = len as usize;
    let mut aM_copy0_4: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_17);
    memset(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_4,
        mu,
        aM_copy0_4.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_18 = len as usize;
    let mut aM_copy_4: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_18);
    memset(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_4,
        mu,
        aM_copy_4.as_mut_ptr(),
        t2_3,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_19 = len as usize;
    let mut aM_copy0_5: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_19);
    memset(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_5,
        mu,
        aM_copy0_5.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_20 = len as usize;
    let mut aM_copy_5: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_20);
    memset(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_5,
        mu,
        aM_copy_5.as_mut_ptr(),
        t2_4,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1802 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_21 = len as usize;
    let mut aM_copy0_6: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_21);
    memset(
        aM_copy0_6.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_6.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_6: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u32(
        len,
        ctx_n1_6,
        mu,
        aM_copy0_6.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1811 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_22 = len as usize;
    let mut aM_copy_6: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_22);
    memset(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint32_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u32(
        len,
        ctx_n_6,
        mu,
        aM_copy_6.as_mut_ptr(),
        t2_5,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if bBits.wrapping_rem(4 as libc::c_uint) != 0 as libc::c_uint {
        let mut i0_0: uint32_t = bBits
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        let mut bits_c: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
            bLen,
            b,
            i0_0,
            4 as libc::c_uint,
        );
        memcpy(
            resM_0.as_mut_ptr() as *mut libc::c_void,
            table.as_mut_ptr().offset((0 as libc::c_uint).wrapping_mul(len) as isize)
                as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i1_0: uint32_t = 0 as libc::c_uint;
        let mut c: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_2: uint32_t = 0 as libc::c_uint;
        while i_2 < len {
            let mut x: uint32_t = c & *res_j.offset(i_2 as isize)
                | !c & *resM_0.as_mut_ptr().offset(i_2 as isize);
            let mut os: *mut uint32_t = resM_0.as_mut_ptr();
            *os.offset(i_2 as isize) = x;
            i_2 = i_2.wrapping_add(1);
            i_2;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_0: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_0: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_3: uint32_t = 0 as libc::c_uint;
        while i_3 < len {
            let mut x_0: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
                | !c_0 & *resM_0.as_mut_ptr().offset(i_3 as isize);
            let mut os_0: *mut uint32_t = resM_0.as_mut_ptr();
            *os_0.offset(i_3 as isize) = x_0;
            i_3 = i_3.wrapping_add(1);
            i_3;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_1: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_1: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_4: uint32_t = 0 as libc::c_uint;
        while i_4 < len {
            let mut x_1: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
                | !c_1 & *resM_0.as_mut_ptr().offset(i_4 as isize);
            let mut os_1: *mut uint32_t = resM_0.as_mut_ptr();
            *os_1.offset(i_4 as isize) = x_1;
            i_4 = i_4.wrapping_add(1);
            i_4;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_2: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_2: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_5: uint32_t = 0 as libc::c_uint;
        while i_5 < len {
            let mut x_2: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
                | !c_2 & *resM_0.as_mut_ptr().offset(i_5 as isize);
            let mut os_2: *mut uint32_t = resM_0.as_mut_ptr();
            *os_2.offset(i_5 as isize) = x_2;
            i_5 = i_5.wrapping_add(1);
            i_5;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_3: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_3: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_6: uint32_t = 0 as libc::c_uint;
        while i_6 < len {
            let mut x_3: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
                | !c_3 & *resM_0.as_mut_ptr().offset(i_6 as isize);
            let mut os_3: *mut uint32_t = resM_0.as_mut_ptr();
            *os_3.offset(i_6 as isize) = x_3;
            i_6 = i_6.wrapping_add(1);
            i_6;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_4: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_4: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_7: uint32_t = 0 as libc::c_uint;
        while i_7 < len {
            let mut x_4: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
                | !c_4 & *resM_0.as_mut_ptr().offset(i_7 as isize);
            let mut os_4: *mut uint32_t = resM_0.as_mut_ptr();
            *os_4.offset(i_7 as isize) = x_4;
            i_7 = i_7.wrapping_add(1);
            i_7;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_5: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_5: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_8: uint32_t = 0 as libc::c_uint;
        while i_8 < len {
            let mut x_5: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
                | !c_5 & *resM_0.as_mut_ptr().offset(i_8 as isize);
            let mut os_5: *mut uint32_t = resM_0.as_mut_ptr();
            *os_5.offset(i_8 as isize) = x_5;
            i_8 = i_8.wrapping_add(1);
            i_8;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_6: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_6: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_9: uint32_t = 0 as libc::c_uint;
        while i_9 < len {
            let mut x_6: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
                | !c_6 & *resM_0.as_mut_ptr().offset(i_9 as isize);
            let mut os_6: *mut uint32_t = resM_0.as_mut_ptr();
            *os_6.offset(i_9 as isize) = x_6;
            i_9 = i_9.wrapping_add(1);
            i_9;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_7: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_7: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_10: uint32_t = 0 as libc::c_uint;
        while i_10 < len {
            let mut x_7: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
                | !c_7 & *resM_0.as_mut_ptr().offset(i_10 as isize);
            let mut os_7: *mut uint32_t = resM_0.as_mut_ptr();
            *os_7.offset(i_10 as isize) = x_7;
            i_10 = i_10.wrapping_add(1);
            i_10;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_8: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_8: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_11: uint32_t = 0 as libc::c_uint;
        while i_11 < len {
            let mut x_8: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
                | !c_8 & *resM_0.as_mut_ptr().offset(i_11 as isize);
            let mut os_8: *mut uint32_t = resM_0.as_mut_ptr();
            *os_8.offset(i_11 as isize) = x_8;
            i_11 = i_11.wrapping_add(1);
            i_11;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_9: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_9: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_12: uint32_t = 0 as libc::c_uint;
        while i_12 < len {
            let mut x_9: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
                | !c_9 & *resM_0.as_mut_ptr().offset(i_12 as isize);
            let mut os_9: *mut uint32_t = resM_0.as_mut_ptr();
            *os_9.offset(i_12 as isize) = x_9;
            i_12 = i_12.wrapping_add(1);
            i_12;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_10: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_10: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_13: uint32_t = 0 as libc::c_uint;
        while i_13 < len {
            let mut x_10: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
                | !c_10 & *resM_0.as_mut_ptr().offset(i_13 as isize);
            let mut os_10: *mut uint32_t = resM_0.as_mut_ptr();
            *os_10.offset(i_13 as isize) = x_10;
            i_13 = i_13.wrapping_add(1);
            i_13;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_11: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_11: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_14: uint32_t = 0 as libc::c_uint;
        while i_14 < len {
            let mut x_11: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
                | !c_11 & *resM_0.as_mut_ptr().offset(i_14 as isize);
            let mut os_11: *mut uint32_t = resM_0.as_mut_ptr();
            *os_11.offset(i_14 as isize) = x_11;
            i_14 = i_14.wrapping_add(1);
            i_14;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_12: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_12: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_15: uint32_t = 0 as libc::c_uint;
        while i_15 < len {
            let mut x_12: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
                | !c_12 & *resM_0.as_mut_ptr().offset(i_15 as isize);
            let mut os_12: *mut uint32_t = resM_0.as_mut_ptr();
            *os_12.offset(i_15 as isize) = x_12;
            i_15 = i_15.wrapping_add(1);
            i_15;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_13: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_13: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_16: uint32_t = 0 as libc::c_uint;
        while i_16 < len {
            let mut x_13: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
                | !c_13 & *resM_0.as_mut_ptr().offset(i_16 as isize);
            let mut os_13: *mut uint32_t = resM_0.as_mut_ptr();
            *os_13.offset(i_16 as isize) = x_13;
            i_16 = i_16.wrapping_add(1);
            i_16;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    } else {
        let mut ctx_n_7: *mut uint32_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint32_t = ctx_0.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(
            len,
            ctx_n_7,
            mu,
            ctx_r2_0,
            resM_0.as_mut_ptr(),
        );
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1844 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_23 = len as usize;
    let mut tmp0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_23);
    memset(
        tmp0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i0_1: uint32_t = 0 as libc::c_uint;
    while i0_1 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i_17: uint32_t = 0 as libc::c_uint;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1853 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_24 = len as usize;
        let mut aM_copy_7: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_24);
        memset(
            aM_copy_7.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_7.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_8: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_8,
            mu,
            aM_copy_7.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1853 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_25 = len as usize;
        let mut aM_copy_8: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_25);
        memset(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_9,
            mu,
            aM_copy_8.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1853 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_26 = len as usize;
        let mut aM_copy_9: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_26);
        memset(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_10,
            mu,
            aM_copy_9.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1853 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_27 = len as usize;
        let mut aM_copy_10: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_27);
        memset(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u32(
            len,
            ctx_n_11,
            mu,
            aM_copy_10.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = bBits
            .wrapping_sub(bBits.wrapping_rem(4 as libc::c_uint))
            .wrapping_sub((4 as libc::c_uint).wrapping_mul(i0_1))
            .wrapping_sub(4 as libc::c_uint);
        let mut bits_l: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
            bLen,
            b,
            k,
            4 as libc::c_uint,
        );
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            table.as_mut_ptr().offset((0 as libc::c_uint).wrapping_mul(len) as isize)
                as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i1_1: uint32_t = 0 as libc::c_uint;
        let mut c_14: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_14: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_18: uint32_t = 0 as libc::c_uint;
        while i_18 < len {
            let mut x_14: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
                | !c_14 & *tmp0.as_mut_ptr().offset(i_18 as isize);
            let mut os_14: *mut uint32_t = tmp0.as_mut_ptr();
            *os_14.offset(i_18 as isize) = x_14;
            i_18 = i_18.wrapping_add(1);
            i_18;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_15: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_15: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_19: uint32_t = 0 as libc::c_uint;
        while i_19 < len {
            let mut x_15: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
                | !c_15 & *tmp0.as_mut_ptr().offset(i_19 as isize);
            let mut os_15: *mut uint32_t = tmp0.as_mut_ptr();
            *os_15.offset(i_19 as isize) = x_15;
            i_19 = i_19.wrapping_add(1);
            i_19;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_16: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_16: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_20: uint32_t = 0 as libc::c_uint;
        while i_20 < len {
            let mut x_16: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
                | !c_16 & *tmp0.as_mut_ptr().offset(i_20 as isize);
            let mut os_16: *mut uint32_t = tmp0.as_mut_ptr();
            *os_16.offset(i_20 as isize) = x_16;
            i_20 = i_20.wrapping_add(1);
            i_20;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_17: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_17: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_21: uint32_t = 0 as libc::c_uint;
        while i_21 < len {
            let mut x_17: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
                | !c_17 & *tmp0.as_mut_ptr().offset(i_21 as isize);
            let mut os_17: *mut uint32_t = tmp0.as_mut_ptr();
            *os_17.offset(i_21 as isize) = x_17;
            i_21 = i_21.wrapping_add(1);
            i_21;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_18: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_18: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_22: uint32_t = 0 as libc::c_uint;
        while i_22 < len {
            let mut x_18: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
                | !c_18 & *tmp0.as_mut_ptr().offset(i_22 as isize);
            let mut os_18: *mut uint32_t = tmp0.as_mut_ptr();
            *os_18.offset(i_22 as isize) = x_18;
            i_22 = i_22.wrapping_add(1);
            i_22;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_19: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_19: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_23: uint32_t = 0 as libc::c_uint;
        while i_23 < len {
            let mut x_19: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
                | !c_19 & *tmp0.as_mut_ptr().offset(i_23 as isize);
            let mut os_19: *mut uint32_t = tmp0.as_mut_ptr();
            *os_19.offset(i_23 as isize) = x_19;
            i_23 = i_23.wrapping_add(1);
            i_23;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_20: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_20: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_24: uint32_t = 0 as libc::c_uint;
        while i_24 < len {
            let mut x_20: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
                | !c_20 & *tmp0.as_mut_ptr().offset(i_24 as isize);
            let mut os_20: *mut uint32_t = tmp0.as_mut_ptr();
            *os_20.offset(i_24 as isize) = x_20;
            i_24 = i_24.wrapping_add(1);
            i_24;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_21: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_21: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_25: uint32_t = 0 as libc::c_uint;
        while i_25 < len {
            let mut x_21: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
                | !c_21 & *tmp0.as_mut_ptr().offset(i_25 as isize);
            let mut os_21: *mut uint32_t = tmp0.as_mut_ptr();
            *os_21.offset(i_25 as isize) = x_21;
            i_25 = i_25.wrapping_add(1);
            i_25;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_22: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_22: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_26: uint32_t = 0 as libc::c_uint;
        while i_26 < len {
            let mut x_22: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
                | !c_22 & *tmp0.as_mut_ptr().offset(i_26 as isize);
            let mut os_22: *mut uint32_t = tmp0.as_mut_ptr();
            *os_22.offset(i_26 as isize) = x_22;
            i_26 = i_26.wrapping_add(1);
            i_26;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_23: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_23: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_27: uint32_t = 0 as libc::c_uint;
        while i_27 < len {
            let mut x_23: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
                | !c_23 & *tmp0.as_mut_ptr().offset(i_27 as isize);
            let mut os_23: *mut uint32_t = tmp0.as_mut_ptr();
            *os_23.offset(i_27 as isize) = x_23;
            i_27 = i_27.wrapping_add(1);
            i_27;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_24: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_24: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_28: uint32_t = 0 as libc::c_uint;
        while i_28 < len {
            let mut x_24: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
                | !c_24 & *tmp0.as_mut_ptr().offset(i_28 as isize);
            let mut os_24: *mut uint32_t = tmp0.as_mut_ptr();
            *os_24.offset(i_28 as isize) = x_24;
            i_28 = i_28.wrapping_add(1);
            i_28;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_25: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_25: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_29: uint32_t = 0 as libc::c_uint;
        while i_29 < len {
            let mut x_25: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
                | !c_25 & *tmp0.as_mut_ptr().offset(i_29 as isize);
            let mut os_25: *mut uint32_t = tmp0.as_mut_ptr();
            *os_25.offset(i_29 as isize) = x_25;
            i_29 = i_29.wrapping_add(1);
            i_29;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_26: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_26: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_30: uint32_t = 0 as libc::c_uint;
        while i_30 < len {
            let mut x_26: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
                | !c_26 & *tmp0.as_mut_ptr().offset(i_30 as isize);
            let mut os_26: *mut uint32_t = tmp0.as_mut_ptr();
            *os_26.offset(i_30 as isize) = x_26;
            i_30 = i_30.wrapping_add(1);
            i_30;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_27: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_27: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_31: uint32_t = 0 as libc::c_uint;
        while i_31 < len {
            let mut x_27: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
                | !c_27 & *tmp0.as_mut_ptr().offset(i_31 as isize);
            let mut os_27: *mut uint32_t = tmp0.as_mut_ptr();
            *os_27.offset(i_31 as isize) = x_27;
            i_31 = i_31.wrapping_add(1);
            i_31;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_28: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_28: *const uint32_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_32: uint32_t = 0 as libc::c_uint;
        while i_32 < len {
            let mut x_28: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
                | !c_28 & *tmp0.as_mut_ptr().offset(i_32 as isize);
            let mut os_28: *mut uint32_t = tmp0.as_mut_ptr();
            *os_28.offset(i_32 as isize) = x_28;
            i_32 = i_32.wrapping_add(1);
            i_32;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1876 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_28 = len as usize;
        let mut aM_copy_11: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_28);
        memset(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint32_t = ctx_0.as_mut_ptr();
        bn_almost_mont_mul_u32(
            len,
            ctx_n_12,
            mu,
            aM_copy_11.as_mut_ptr(),
            tmp0.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0_1 = i0_1.wrapping_add(1);
        i0_1;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len, n, mu, resM_0.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32(
    mut len: uint32_t,
    mut nBits: uint32_t,
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1898 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut r2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        r2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2.as_mut_ptr());
    let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
        *n.offset(0 as libc::c_uint as isize),
    );
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(
        len,
        n,
        mu,
        r2.as_mut_ptr(),
        a,
        bBits,
        b,
        res,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32(
    mut len: uint32_t,
    mut nBits: uint32_t,
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1917 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut r2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        r2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r2.as_mut_ptr());
    let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
        *n.offset(0 as libc::c_uint as isize),
    );
    Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(
        len,
        n,
        mu,
        r2.as_mut_ptr(),
        a,
        bBits,
        b,
        res,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
) -> uint64_t {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            1934 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut one: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    *one.as_mut_ptr().offset(0 as libc::c_uint as isize) = 1 as libc::c_ulonglong;
    let mut bit0: uint64_t = *n.offset(0 as libc::c_uint as isize)
        & 1 as libc::c_ulonglong;
    let mut m0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bit0);
    let mut acc0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut beq: uint64_t = FStar_UInt64_eq_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        let mut blt: uint64_t = !FStar_UInt64_gte_mask(
            *one.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        acc0 = beq & acc0 | !beq & blt;
        i = i.wrapping_add(1);
        i;
    }
    let mut m10: uint64_t = acc0;
    let mut m00: uint64_t = m0 & m10;
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    let mut m1: uint64_t = 0;
    if bBits < (64 as libc::c_uint).wrapping_mul(bLen) {
        if bLen as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                1962 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = bLen as usize;
        let mut b2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            b2.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (bLen as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i0: uint32_t = bBits.wrapping_div(64 as libc::c_uint);
        let mut j: uint32_t = bBits.wrapping_rem(64 as libc::c_uint);
        *b2
            .as_mut_ptr()
            .offset(
                i0 as isize,
            ) = *b2.as_mut_ptr().offset(i0 as isize) | (1 as libc::c_ulonglong) << j;
        let mut acc: uint64_t = 0 as libc::c_ulonglong;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0 < bLen {
            let mut beq_0: uint64_t = FStar_UInt64_eq_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            let mut blt_0: uint64_t = !FStar_UInt64_gte_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            acc = beq_0 & acc | !beq_0 & blt_0;
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut res: uint64_t = acc;
        m1 = res;
    } else {
        m1 = 0xffffffffffffffff as libc::c_ulonglong;
    }
    let mut acc_0: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < len {
        let mut beq_1: uint64_t = FStar_UInt64_eq_mask(
            *a.offset(i_1 as isize),
            *n.offset(i_1 as isize),
        );
        let mut blt_1: uint64_t = !FStar_UInt64_gte_mask(
            *a.offset(i_1 as isize),
            *n.offset(i_1 as isize),
        );
        acc_0 = beq_1 & acc_0 | !beq_1 & blt_1;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut m2: uint64_t = acc_0;
    let mut m: uint64_t = m1 & m2;
    return m00 & m;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut mu: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if bBits < 200 as libc::c_uint {
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2008 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = len as usize;
        let mut aM: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
        memset(
            aM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM.as_mut_ptr());
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2012 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len as usize;
        let mut resM: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            resM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        if len.wrapping_add(len) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2015 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len.wrapping_add(len) as usize;
        let mut ctx: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            ctx.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len.wrapping_add(len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n0: *mut uint64_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint64_t = ctx.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u64(
            len,
            ctx_n0,
            mu,
            ctx_r2,
            resM.as_mut_ptr(),
        );
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < bBits {
            let mut i1: uint32_t = i.wrapping_div(64 as libc::c_uint);
            let mut j: uint32_t = i.wrapping_rem(64 as libc::c_uint);
            let mut tmp: uint64_t = *b.offset(i1 as isize);
            let mut bit: uint64_t = tmp >> j & 1 as libc::c_ulonglong;
            if !(bit == 0 as libc::c_ulonglong) {
                if len as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(
                            ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
                        )
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                        2032 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = len as usize;
                let mut aM_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    aM_copy.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (len as libc::c_ulong)
                        .wrapping_mul(
                            ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
                        ),
                );
                memcpy(
                    aM_copy.as_mut_ptr() as *mut libc::c_void,
                    resM.as_mut_ptr() as *const libc::c_void,
                    (len as libc::c_ulong)
                        .wrapping_mul(
                            ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
                        ),
                );
                let mut ctx_n: *mut uint64_t = ctx.as_mut_ptr();
                bn_almost_mont_mul_u64(
                    len,
                    ctx_n,
                    mu,
                    aM_copy.as_mut_ptr(),
                    aM.as_mut_ptr(),
                    resM.as_mut_ptr(),
                );
            }
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                    2040 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_3 = len as usize;
            let mut aM_copy_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_3);
            memset(
                aM_copy_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            memcpy(
                aM_copy_0.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut ctx_n_0: *mut uint64_t = ctx.as_mut_ptr();
            bn_almost_mont_sqr_u64(
                len,
                ctx_n_0,
                mu,
                aM_copy_0.as_mut_ptr(),
                aM.as_mut_ptr(),
            );
            i = i.wrapping_add(1);
            i;
        }
        Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM.as_mut_ptr(), res);
        return;
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2051 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_4 = len as usize;
    let mut aM_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_4);
    memset(
        aM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM_0.as_mut_ptr());
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2055 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = len as usize;
    let mut resM_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        resM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2067 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_6 = len.wrapping_add(len) as usize;
    let mut ctx_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_6);
    memset(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (16 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2072 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_7 = (16 as libc::c_uint).wrapping_mul(len) as usize;
    let mut table: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_7);
    memset(
        table.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((16 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2075 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_8 = len as usize;
    let mut tmp_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_8);
    memset(
        tmp_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t0: *mut uint64_t = table.as_mut_ptr();
    let mut t1: *mut uint64_t = table.as_mut_ptr().offset(len as isize);
    let mut ctx_n0_0: *mut uint64_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint64_t = ctx_0.as_mut_ptr().offset(len as isize);
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_9 = len as usize;
    let mut aM_copy0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_9);
    memset(
        aM_copy0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(len, ctx_n1, mu, aM_copy0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_10 = len as usize;
    let mut aM_copy_1: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_10);
    memset(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_1,
        mu,
        aM_copy_1.as_mut_ptr(),
        t2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_11 = len as usize;
    let mut aM_copy0_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_11);
    memset(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_0,
        mu,
        aM_copy0_0.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_12 = len as usize;
    let mut aM_copy_2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_12);
    memset(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_2,
        mu,
        aM_copy_2.as_mut_ptr(),
        t2_0,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_13 = len as usize;
    let mut aM_copy0_1: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_13);
    memset(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_1,
        mu,
        aM_copy0_1.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_14 = len as usize;
    let mut aM_copy_3: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_14);
    memset(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_3,
        mu,
        aM_copy_3.as_mut_ptr(),
        t2_1,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_15 = len as usize;
    let mut aM_copy0_2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_15);
    memset(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_2,
        mu,
        aM_copy0_2.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_16 = len as usize;
    let mut aM_copy_4: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_16);
    memset(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_4,
        mu,
        aM_copy_4.as_mut_ptr(),
        t2_2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_17 = len as usize;
    let mut aM_copy0_3: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_17);
    memset(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_3,
        mu,
        aM_copy0_3.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_18 = len as usize;
    let mut aM_copy_5: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_18);
    memset(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_5,
        mu,
        aM_copy_5.as_mut_ptr(),
        t2_3,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_19 = len as usize;
    let mut aM_copy0_4: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_19);
    memset(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_4,
        mu,
        aM_copy0_4.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_20 = len as usize;
    let mut aM_copy_6: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_20);
    memset(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_6,
        mu,
        aM_copy_6.as_mut_ptr(),
        t2_4,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2091 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_21 = len as usize;
    let mut aM_copy0_5: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_21);
    memset(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_5,
        mu,
        aM_copy0_5.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2100 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_22 = len as usize;
    let mut aM_copy_7: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_22);
    memset(
        aM_copy_7.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_7.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_7: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_7,
        mu,
        aM_copy_7.as_mut_ptr(),
        t2_5,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if bBits.wrapping_rem(4 as libc::c_uint) != 0 as libc::c_uint {
        let mut i_1: uint32_t = bBits
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        let mut bits_c: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            bLen,
            b,
            i_1,
            4 as libc::c_uint,
        );
        let mut bits_l32: uint32_t = bits_c as uint32_t;
        let mut a_bits_l: *const uint64_t = table
            .as_mut_ptr()
            .offset((bits_l32 * len) as isize);
        memcpy(
            resM_0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l as *mut uint64_t as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
    } else {
        let mut ctx_n_8: *mut uint64_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint64_t = ctx_0.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u64(
            len,
            ctx_n_8,
            mu,
            ctx_r2_0,
            resM_0.as_mut_ptr(),
        );
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2123 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_23 = len as usize;
    let mut tmp0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_23);
    memset(
        tmp0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_2: uint32_t = 0 as libc::c_uint;
    while i_2 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i0: uint32_t = 0 as libc::c_uint;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2132 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_24 = len as usize;
        let mut aM_copy_8: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_24);
        memset(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_9,
            mu,
            aM_copy_8.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2132 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_25 = len as usize;
        let mut aM_copy_9: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_25);
        memset(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_10,
            mu,
            aM_copy_9.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2132 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_26 = len as usize;
        let mut aM_copy_10: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_26);
        memset(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_11,
            mu,
            aM_copy_10.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2132 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_27 = len as usize;
        let mut aM_copy_11: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_27);
        memset(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_12,
            mu,
            aM_copy_11.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = bBits
            .wrapping_sub(bBits.wrapping_rem(4 as libc::c_uint))
            .wrapping_sub((4 as libc::c_uint).wrapping_mul(i_2))
            .wrapping_sub(4 as libc::c_uint);
        let mut bits_l: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            bLen,
            b,
            k,
            4 as libc::c_uint,
        );
        let mut bits_l32_0: uint32_t = bits_l as uint32_t;
        let mut a_bits_l_0: *const uint64_t = table
            .as_mut_ptr()
            .offset((bits_l32_0 * len) as isize);
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l_0 as *mut uint64_t as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2145 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_28 = len as usize;
        let mut aM_copy_12: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_28);
        memset(
            aM_copy_12.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_12.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_13: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_mul_u64(
            len,
            ctx_n_13,
            mu,
            aM_copy_12.as_mut_ptr(),
            tmp0.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM_0.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
    mut len: uint32_t,
    mut n: *mut uint64_t,
    mut mu: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if bBits < 200 as libc::c_uint {
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2170 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = len as usize;
        let mut aM: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
        memset(
            aM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM.as_mut_ptr());
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2174 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len as usize;
        let mut resM: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            resM.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        if len.wrapping_add(len) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2177 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len.wrapping_add(len) as usize;
        let mut ctx: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            ctx.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len.wrapping_add(len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut sw: uint64_t = 0 as libc::c_ulonglong;
        let mut ctx_n0: *mut uint64_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint64_t = ctx.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u64(
            len,
            ctx_n0,
            mu,
            ctx_r2,
            resM.as_mut_ptr(),
        );
        let mut i0: uint32_t = 0 as libc::c_uint;
        while i0 < bBits {
            let mut i1: uint32_t = bBits
                .wrapping_sub(i0)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint);
            let mut j: uint32_t = bBits
                .wrapping_sub(i0)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_rem(64 as libc::c_uint);
            let mut tmp: uint64_t = *b.offset(i1 as isize);
            let mut bit: uint64_t = tmp >> j & 1 as libc::c_ulonglong;
            let mut sw1: uint64_t = bit ^ sw;
            let mut i: uint32_t = 0 as libc::c_uint;
            while i < len {
                let mut dummy: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw1)
                    & (*resM.as_mut_ptr().offset(i as isize)
                        ^ *aM.as_mut_ptr().offset(i as isize));
                *resM
                    .as_mut_ptr()
                    .offset(i as isize) = *resM.as_mut_ptr().offset(i as isize) ^ dummy;
                *aM
                    .as_mut_ptr()
                    .offset(i as isize) = *aM.as_mut_ptr().offset(i as isize) ^ dummy;
                i = i.wrapping_add(1);
                i;
            }
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                    2200 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_2 = len as usize;
            let mut aM_copy: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_2);
            memset(
                aM_copy.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            memcpy(
                aM_copy.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut ctx_n1: *mut uint64_t = ctx.as_mut_ptr();
            bn_almost_mont_mul_u64(
                len,
                ctx_n1,
                mu,
                aM_copy.as_mut_ptr(),
                resM.as_mut_ptr(),
                aM.as_mut_ptr(),
            );
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                    2207 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_3 = len as usize;
            let mut aM_copy0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_3);
            memset(
                aM_copy0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            memcpy(
                aM_copy0.as_mut_ptr() as *mut libc::c_void,
                resM.as_mut_ptr() as *const libc::c_void,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut ctx_n: *mut uint64_t = ctx.as_mut_ptr();
            bn_almost_mont_sqr_u64(
                len,
                ctx_n,
                mu,
                aM_copy0.as_mut_ptr(),
                resM.as_mut_ptr(),
            );
            sw = bit;
            i0 = i0.wrapping_add(1);
            i0;
        }
        let mut sw0: uint64_t = sw;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0 < len {
            let mut dummy_0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw0)
                & (*resM.as_mut_ptr().offset(i_0 as isize)
                    ^ *aM.as_mut_ptr().offset(i_0 as isize));
            *resM
                .as_mut_ptr()
                .offset(
                    i_0 as isize,
                ) = *resM.as_mut_ptr().offset(i_0 as isize) ^ dummy_0;
            *aM
                .as_mut_ptr()
                .offset(i_0 as isize) = *aM.as_mut_ptr().offset(i_0 as isize) ^ dummy_0;
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM.as_mut_ptr(), res);
        return;
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2226 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_4 = len as usize;
    let mut aM_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_4);
    memset(
        aM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_to_mont_u64(len, n, mu, r2, a, aM_0.as_mut_ptr());
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2230 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = len as usize;
    let mut resM_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        resM_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    if len.wrapping_add(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2242 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_6 = len.wrapping_add(len) as usize;
    let mut ctx_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_6);
    memset(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(len as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if (16 as libc::c_uint).wrapping_mul(len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2247 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_7 = (16 as libc::c_uint).wrapping_mul(len) as usize;
    let mut table: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_7);
    memset(
        table.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((16 as libc::c_uint).wrapping_mul(len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2250 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_8 = len as usize;
    let mut tmp_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_8);
    memset(
        tmp_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t0: *mut uint64_t = table.as_mut_ptr();
    let mut t1: *mut uint64_t = table.as_mut_ptr().offset(len as isize);
    let mut ctx_n0_0: *mut uint64_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint64_t = ctx_0.as_mut_ptr().offset(len as isize);
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_9 = len as usize;
    let mut aM_copy0_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_9);
    memset(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_0,
        mu,
        aM_copy0_0.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_10 = len as usize;
    let mut aM_copy_0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_10);
    memset(
        aM_copy_0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_0.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_0: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_0,
        mu,
        aM_copy_0.as_mut_ptr(),
        t2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_11 = len as usize;
    let mut aM_copy0_1: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_11);
    memset(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_1,
        mu,
        aM_copy0_1.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_12 = len as usize;
    let mut aM_copy_1: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_12);
    memset(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_1,
        mu,
        aM_copy_1.as_mut_ptr(),
        t2_0,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_13 = len as usize;
    let mut aM_copy0_2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_13);
    memset(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_2,
        mu,
        aM_copy0_2.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_14 = len as usize;
    let mut aM_copy_2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_14);
    memset(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_2,
        mu,
        aM_copy_2.as_mut_ptr(),
        t2_1,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_15 = len as usize;
    let mut aM_copy0_3: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_15);
    memset(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_3,
        mu,
        aM_copy0_3.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_16 = len as usize;
    let mut aM_copy_3: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_16);
    memset(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_3,
        mu,
        aM_copy_3.as_mut_ptr(),
        t2_2,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_17 = len as usize;
    let mut aM_copy0_4: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_17);
    memset(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_4,
        mu,
        aM_copy0_4.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_18 = len as usize;
    let mut aM_copy_4: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_18);
    memset(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_4,
        mu,
        aM_copy_4.as_mut_ptr(),
        t2_3,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_19 = len as usize;
    let mut aM_copy0_5: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_19);
    memset(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_5,
        mu,
        aM_copy0_5.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_20 = len as usize;
    let mut aM_copy_5: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_20);
    memset(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_5,
        mu,
        aM_copy_5.as_mut_ptr(),
        t2_4,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2266 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_21 = len as usize;
    let mut aM_copy0_6: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_21);
    memset(
        aM_copy0_6.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy0_6.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_6: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_sqr_u64(
        len,
        ctx_n1_6,
        mu,
        aM_copy0_6.as_mut_ptr(),
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(len) as isize,
        );
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2275 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_22 = len as usize;
    let mut aM_copy_6: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_22);
    memset(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint64_t = ctx_0.as_mut_ptr();
    bn_almost_mont_mul_u64(
        len,
        ctx_n_6,
        mu,
        aM_copy_6.as_mut_ptr(),
        t2_5,
        tmp_0.as_mut_ptr(),
    );
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(len) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if bBits.wrapping_rem(4 as libc::c_uint) != 0 as libc::c_uint {
        let mut i0_0: uint32_t = bBits
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        let mut bits_c: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            bLen,
            b,
            i0_0,
            4 as libc::c_uint,
        );
        memcpy(
            resM_0.as_mut_ptr() as *mut libc::c_void,
            table.as_mut_ptr().offset((0 as libc::c_uint).wrapping_mul(len) as isize)
                as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i1_0: uint32_t = 0 as libc::c_uint;
        let mut c: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_2: uint32_t = 0 as libc::c_uint;
        while i_2 < len {
            let mut x: uint64_t = c & *res_j.offset(i_2 as isize)
                | !c & *resM_0.as_mut_ptr().offset(i_2 as isize);
            let mut os: *mut uint64_t = resM_0.as_mut_ptr();
            *os.offset(i_2 as isize) = x;
            i_2 = i_2.wrapping_add(1);
            i_2;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_0: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_0: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_3: uint32_t = 0 as libc::c_uint;
        while i_3 < len {
            let mut x_0: uint64_t = c_0 & *res_j_0.offset(i_3 as isize)
                | !c_0 & *resM_0.as_mut_ptr().offset(i_3 as isize);
            let mut os_0: *mut uint64_t = resM_0.as_mut_ptr();
            *os_0.offset(i_3 as isize) = x_0;
            i_3 = i_3.wrapping_add(1);
            i_3;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_1: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_1: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_4: uint32_t = 0 as libc::c_uint;
        while i_4 < len {
            let mut x_1: uint64_t = c_1 & *res_j_1.offset(i_4 as isize)
                | !c_1 & *resM_0.as_mut_ptr().offset(i_4 as isize);
            let mut os_1: *mut uint64_t = resM_0.as_mut_ptr();
            *os_1.offset(i_4 as isize) = x_1;
            i_4 = i_4.wrapping_add(1);
            i_4;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_2: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_2: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_5: uint32_t = 0 as libc::c_uint;
        while i_5 < len {
            let mut x_2: uint64_t = c_2 & *res_j_2.offset(i_5 as isize)
                | !c_2 & *resM_0.as_mut_ptr().offset(i_5 as isize);
            let mut os_2: *mut uint64_t = resM_0.as_mut_ptr();
            *os_2.offset(i_5 as isize) = x_2;
            i_5 = i_5.wrapping_add(1);
            i_5;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_3: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_3: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_6: uint32_t = 0 as libc::c_uint;
        while i_6 < len {
            let mut x_3: uint64_t = c_3 & *res_j_3.offset(i_6 as isize)
                | !c_3 & *resM_0.as_mut_ptr().offset(i_6 as isize);
            let mut os_3: *mut uint64_t = resM_0.as_mut_ptr();
            *os_3.offset(i_6 as isize) = x_3;
            i_6 = i_6.wrapping_add(1);
            i_6;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_4: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_4: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_7: uint32_t = 0 as libc::c_uint;
        while i_7 < len {
            let mut x_4: uint64_t = c_4 & *res_j_4.offset(i_7 as isize)
                | !c_4 & *resM_0.as_mut_ptr().offset(i_7 as isize);
            let mut os_4: *mut uint64_t = resM_0.as_mut_ptr();
            *os_4.offset(i_7 as isize) = x_4;
            i_7 = i_7.wrapping_add(1);
            i_7;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_5: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_5: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_8: uint32_t = 0 as libc::c_uint;
        while i_8 < len {
            let mut x_5: uint64_t = c_5 & *res_j_5.offset(i_8 as isize)
                | !c_5 & *resM_0.as_mut_ptr().offset(i_8 as isize);
            let mut os_5: *mut uint64_t = resM_0.as_mut_ptr();
            *os_5.offset(i_8 as isize) = x_5;
            i_8 = i_8.wrapping_add(1);
            i_8;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_6: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_6: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_9: uint32_t = 0 as libc::c_uint;
        while i_9 < len {
            let mut x_6: uint64_t = c_6 & *res_j_6.offset(i_9 as isize)
                | !c_6 & *resM_0.as_mut_ptr().offset(i_9 as isize);
            let mut os_6: *mut uint64_t = resM_0.as_mut_ptr();
            *os_6.offset(i_9 as isize) = x_6;
            i_9 = i_9.wrapping_add(1);
            i_9;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_7: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_7: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_10: uint32_t = 0 as libc::c_uint;
        while i_10 < len {
            let mut x_7: uint64_t = c_7 & *res_j_7.offset(i_10 as isize)
                | !c_7 & *resM_0.as_mut_ptr().offset(i_10 as isize);
            let mut os_7: *mut uint64_t = resM_0.as_mut_ptr();
            *os_7.offset(i_10 as isize) = x_7;
            i_10 = i_10.wrapping_add(1);
            i_10;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_8: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_8: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_11: uint32_t = 0 as libc::c_uint;
        while i_11 < len {
            let mut x_8: uint64_t = c_8 & *res_j_8.offset(i_11 as isize)
                | !c_8 & *resM_0.as_mut_ptr().offset(i_11 as isize);
            let mut os_8: *mut uint64_t = resM_0.as_mut_ptr();
            *os_8.offset(i_11 as isize) = x_8;
            i_11 = i_11.wrapping_add(1);
            i_11;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_9: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_9: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_12: uint32_t = 0 as libc::c_uint;
        while i_12 < len {
            let mut x_9: uint64_t = c_9 & *res_j_9.offset(i_12 as isize)
                | !c_9 & *resM_0.as_mut_ptr().offset(i_12 as isize);
            let mut os_9: *mut uint64_t = resM_0.as_mut_ptr();
            *os_9.offset(i_12 as isize) = x_9;
            i_12 = i_12.wrapping_add(1);
            i_12;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_10: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_10: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_13: uint32_t = 0 as libc::c_uint;
        while i_13 < len {
            let mut x_10: uint64_t = c_10 & *res_j_10.offset(i_13 as isize)
                | !c_10 & *resM_0.as_mut_ptr().offset(i_13 as isize);
            let mut os_10: *mut uint64_t = resM_0.as_mut_ptr();
            *os_10.offset(i_13 as isize) = x_10;
            i_13 = i_13.wrapping_add(1);
            i_13;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_11: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_11: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_14: uint32_t = 0 as libc::c_uint;
        while i_14 < len {
            let mut x_11: uint64_t = c_11 & *res_j_11.offset(i_14 as isize)
                | !c_11 & *resM_0.as_mut_ptr().offset(i_14 as isize);
            let mut os_11: *mut uint64_t = resM_0.as_mut_ptr();
            *os_11.offset(i_14 as isize) = x_11;
            i_14 = i_14.wrapping_add(1);
            i_14;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_12: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_12: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_15: uint32_t = 0 as libc::c_uint;
        while i_15 < len {
            let mut x_12: uint64_t = c_12 & *res_j_12.offset(i_15 as isize)
                | !c_12 & *resM_0.as_mut_ptr().offset(i_15 as isize);
            let mut os_12: *mut uint64_t = resM_0.as_mut_ptr();
            *os_12.offset(i_15 as isize) = x_12;
            i_15 = i_15.wrapping_add(1);
            i_15;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_13: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_13: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_16: uint32_t = 0 as libc::c_uint;
        while i_16 < len {
            let mut x_13: uint64_t = c_13 & *res_j_13.offset(i_16 as isize)
                | !c_13 & *resM_0.as_mut_ptr().offset(i_16 as isize);
            let mut os_13: *mut uint64_t = resM_0.as_mut_ptr();
            *os_13.offset(i_16 as isize) = x_13;
            i_16 = i_16.wrapping_add(1);
            i_16;
        }
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    } else {
        let mut ctx_n_7: *mut uint64_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint64_t = ctx_0.as_mut_ptr().offset(len as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u64(
            len,
            ctx_n_7,
            mu,
            ctx_r2_0,
            resM_0.as_mut_ptr(),
        );
    }
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2308 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_23 = len as usize;
    let mut tmp0: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_23);
    memset(
        tmp0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0_1: uint32_t = 0 as libc::c_uint;
    while i0_1 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i_17: uint32_t = 0 as libc::c_uint;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2317 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_24 = len as usize;
        let mut aM_copy_7: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_24);
        memset(
            aM_copy_7.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_7.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_8: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_8,
            mu,
            aM_copy_7.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2317 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_25 = len as usize;
        let mut aM_copy_8: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_25);
        memset(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_9,
            mu,
            aM_copy_8.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2317 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_26 = len as usize;
        let mut aM_copy_9: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_26);
        memset(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_10,
            mu,
            aM_copy_9.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2317 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_27 = len as usize;
        let mut aM_copy_10: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_27);
        memset(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_sqr_u64(
            len,
            ctx_n_11,
            mu,
            aM_copy_10.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut k: uint32_t = bBits
            .wrapping_sub(bBits.wrapping_rem(4 as libc::c_uint))
            .wrapping_sub((4 as libc::c_uint).wrapping_mul(i0_1))
            .wrapping_sub(4 as libc::c_uint);
        let mut bits_l: uint64_t = Hacl_Bignum_Lib_bn_get_bits_u64(
            bLen,
            b,
            k,
            4 as libc::c_uint,
        );
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            table.as_mut_ptr().offset((0 as libc::c_uint).wrapping_mul(len) as isize)
                as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i1_1: uint32_t = 0 as libc::c_uint;
        let mut c_14: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_14: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_18: uint32_t = 0 as libc::c_uint;
        while i_18 < len {
            let mut x_14: uint64_t = c_14 & *res_j_14.offset(i_18 as isize)
                | !c_14 & *tmp0.as_mut_ptr().offset(i_18 as isize);
            let mut os_14: *mut uint64_t = tmp0.as_mut_ptr();
            *os_14.offset(i_18 as isize) = x_14;
            i_18 = i_18.wrapping_add(1);
            i_18;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_15: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_15: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_19: uint32_t = 0 as libc::c_uint;
        while i_19 < len {
            let mut x_15: uint64_t = c_15 & *res_j_15.offset(i_19 as isize)
                | !c_15 & *tmp0.as_mut_ptr().offset(i_19 as isize);
            let mut os_15: *mut uint64_t = tmp0.as_mut_ptr();
            *os_15.offset(i_19 as isize) = x_15;
            i_19 = i_19.wrapping_add(1);
            i_19;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_16: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_16: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_20: uint32_t = 0 as libc::c_uint;
        while i_20 < len {
            let mut x_16: uint64_t = c_16 & *res_j_16.offset(i_20 as isize)
                | !c_16 & *tmp0.as_mut_ptr().offset(i_20 as isize);
            let mut os_16: *mut uint64_t = tmp0.as_mut_ptr();
            *os_16.offset(i_20 as isize) = x_16;
            i_20 = i_20.wrapping_add(1);
            i_20;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_17: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_17: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_21: uint32_t = 0 as libc::c_uint;
        while i_21 < len {
            let mut x_17: uint64_t = c_17 & *res_j_17.offset(i_21 as isize)
                | !c_17 & *tmp0.as_mut_ptr().offset(i_21 as isize);
            let mut os_17: *mut uint64_t = tmp0.as_mut_ptr();
            *os_17.offset(i_21 as isize) = x_17;
            i_21 = i_21.wrapping_add(1);
            i_21;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_18: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_18: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_22: uint32_t = 0 as libc::c_uint;
        while i_22 < len {
            let mut x_18: uint64_t = c_18 & *res_j_18.offset(i_22 as isize)
                | !c_18 & *tmp0.as_mut_ptr().offset(i_22 as isize);
            let mut os_18: *mut uint64_t = tmp0.as_mut_ptr();
            *os_18.offset(i_22 as isize) = x_18;
            i_22 = i_22.wrapping_add(1);
            i_22;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_19: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_19: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_23: uint32_t = 0 as libc::c_uint;
        while i_23 < len {
            let mut x_19: uint64_t = c_19 & *res_j_19.offset(i_23 as isize)
                | !c_19 & *tmp0.as_mut_ptr().offset(i_23 as isize);
            let mut os_19: *mut uint64_t = tmp0.as_mut_ptr();
            *os_19.offset(i_23 as isize) = x_19;
            i_23 = i_23.wrapping_add(1);
            i_23;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_20: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_20: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_24: uint32_t = 0 as libc::c_uint;
        while i_24 < len {
            let mut x_20: uint64_t = c_20 & *res_j_20.offset(i_24 as isize)
                | !c_20 & *tmp0.as_mut_ptr().offset(i_24 as isize);
            let mut os_20: *mut uint64_t = tmp0.as_mut_ptr();
            *os_20.offset(i_24 as isize) = x_20;
            i_24 = i_24.wrapping_add(1);
            i_24;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_21: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_21: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_25: uint32_t = 0 as libc::c_uint;
        while i_25 < len {
            let mut x_21: uint64_t = c_21 & *res_j_21.offset(i_25 as isize)
                | !c_21 & *tmp0.as_mut_ptr().offset(i_25 as isize);
            let mut os_21: *mut uint64_t = tmp0.as_mut_ptr();
            *os_21.offset(i_25 as isize) = x_21;
            i_25 = i_25.wrapping_add(1);
            i_25;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_22: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_22: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_26: uint32_t = 0 as libc::c_uint;
        while i_26 < len {
            let mut x_22: uint64_t = c_22 & *res_j_22.offset(i_26 as isize)
                | !c_22 & *tmp0.as_mut_ptr().offset(i_26 as isize);
            let mut os_22: *mut uint64_t = tmp0.as_mut_ptr();
            *os_22.offset(i_26 as isize) = x_22;
            i_26 = i_26.wrapping_add(1);
            i_26;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_23: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_23: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_27: uint32_t = 0 as libc::c_uint;
        while i_27 < len {
            let mut x_23: uint64_t = c_23 & *res_j_23.offset(i_27 as isize)
                | !c_23 & *tmp0.as_mut_ptr().offset(i_27 as isize);
            let mut os_23: *mut uint64_t = tmp0.as_mut_ptr();
            *os_23.offset(i_27 as isize) = x_23;
            i_27 = i_27.wrapping_add(1);
            i_27;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_24: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_24: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_28: uint32_t = 0 as libc::c_uint;
        while i_28 < len {
            let mut x_24: uint64_t = c_24 & *res_j_24.offset(i_28 as isize)
                | !c_24 & *tmp0.as_mut_ptr().offset(i_28 as isize);
            let mut os_24: *mut uint64_t = tmp0.as_mut_ptr();
            *os_24.offset(i_28 as isize) = x_24;
            i_28 = i_28.wrapping_add(1);
            i_28;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_25: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_25: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_29: uint32_t = 0 as libc::c_uint;
        while i_29 < len {
            let mut x_25: uint64_t = c_25 & *res_j_25.offset(i_29 as isize)
                | !c_25 & *tmp0.as_mut_ptr().offset(i_29 as isize);
            let mut os_25: *mut uint64_t = tmp0.as_mut_ptr();
            *os_25.offset(i_29 as isize) = x_25;
            i_29 = i_29.wrapping_add(1);
            i_29;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_26: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_26: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_30: uint32_t = 0 as libc::c_uint;
        while i_30 < len {
            let mut x_26: uint64_t = c_26 & *res_j_26.offset(i_30 as isize)
                | !c_26 & *tmp0.as_mut_ptr().offset(i_30 as isize);
            let mut os_26: *mut uint64_t = tmp0.as_mut_ptr();
            *os_26.offset(i_30 as isize) = x_26;
            i_30 = i_30.wrapping_add(1);
            i_30;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_27: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_27: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_31: uint32_t = 0 as libc::c_uint;
        while i_31 < len {
            let mut x_27: uint64_t = c_27 & *res_j_27.offset(i_31 as isize)
                | !c_27 & *tmp0.as_mut_ptr().offset(i_31 as isize);
            let mut os_27: *mut uint64_t = tmp0.as_mut_ptr();
            *os_27.offset(i_31 as isize) = x_27;
            i_31 = i_31.wrapping_add(1);
            i_31;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_28: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_28: *const uint64_t = table
            .as_mut_ptr()
            .offset(i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len) as isize);
        let mut i_32: uint32_t = 0 as libc::c_uint;
        while i_32 < len {
            let mut x_28: uint64_t = c_28 & *res_j_28.offset(i_32 as isize)
                | !c_28 & *tmp0.as_mut_ptr().offset(i_32 as isize);
            let mut os_28: *mut uint64_t = tmp0.as_mut_ptr();
            *os_28.offset(i_32 as isize) = x_28;
            i_32 = i_32.wrapping_add(1);
            i_32;
        }
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
                2340 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_28 = len as usize;
        let mut aM_copy_11: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_28);
        memset(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint64_t = ctx_0.as_mut_ptr();
        bn_almost_mont_mul_u64(
            len,
            ctx_n_12,
            mu,
            aM_copy_11.as_mut_ptr(),
            tmp0.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0_1 = i0_1.wrapping_add(1);
        i0_1;
    }
    Hacl_Bignum_Montgomery_bn_from_mont_u64(len, n, mu, resM_0.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64(
    mut len: uint32_t,
    mut nBits: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2362 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut r2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        r2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2.as_mut_ptr());
    let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
        *n.offset(0 as libc::c_uint as isize),
    );
    Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
        len,
        n,
        mu,
        r2.as_mut_ptr(),
        a,
        bBits,
        b,
        res,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64(
    mut len: uint32_t,
    mut nBits: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum.c\0" as *const u8 as *const libc::c_char,
            2381 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len as usize;
    let mut r2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        r2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(len, nBits, n, r2.as_mut_ptr());
    let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
        *n.offset(0 as libc::c_uint as isize),
    );
    Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
        len,
        n,
        mu,
        r2.as_mut_ptr(),
        a,
        bBits,
        b,
        res,
    );
}
