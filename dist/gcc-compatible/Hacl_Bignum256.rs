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
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
    fn Hacl_Bignum_ModInvLimb_mod_inv_uint64(n0: uint64_t) -> uint64_t;
}
pub type __uint64_t = libc::c_ulonglong;
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type FStar_UInt128_uint128 = u128;
pub type uint128_t = FStar_UInt128_uint128;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_s {
    pub len: uint32_t,
    pub n: *mut uint64_t,
    pub mu: uint64_t,
    pub r2: *mut uint64_t,
}
pub type Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 = Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_s;
#[inline]
unsafe extern "C" fn _OSSwapInt64(mut _data: __uint64_t) -> __uint64_t {
    return _data.swap_bytes();
}
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
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_top_index_u64(
    mut len: uint32_t,
    mut b: *mut uint64_t,
) -> uint64_t {
    let mut priv_0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut mask: uint64_t = FStar_UInt64_eq_mask(
            *b.offset(i as isize),
            0 as libc::c_ulonglong,
        );
        priv_0 = mask & priv_0 | !mask & i as uint64_t;
        i = i.wrapping_add(1);
        i;
    }
    return priv_0;
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
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_add(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12, t2, res_i);
    return c;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_sub(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> uint64_t {
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t12, t2, res_i);
    return c;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_add_mod(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, t12, t2, res_i);
    let mut c00: uint64_t = c0;
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1_0: uint64_t = *res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20_0: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c, t12_0, t2_0, res_i_0);
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = c00.wrapping_sub(c1);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os: *mut uint64_t = res;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_sub_mod(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *b
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t1, t20, res_i0);
    let mut t10: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t10, t21, res_i1);
    let mut t11: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t11, t22, res_i2);
    let mut t12: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *b
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c0, t12, t2, res_i);
    let mut c00: uint64_t = c0;
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut t1_0: uint64_t = *res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20_0: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c, t12_0, t2_0, res_i_0);
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c00);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os: *mut uint64_t = res;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = c2 & tmp[i as usize] | !c2 & *res.offset(i as isize);
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mul(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut bj: uint64_t = *b.offset(i0 as isize);
    let mut res_j: *mut uint64_t = res.offset(i0 as isize);
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, bj, c, res_i0);
    let mut a_i0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, bj, c, res_i1);
    let mut a_i1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, bj, c, res_i2);
    let mut a_i2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, bj, c, res_i);
    let mut r: uint64_t = c;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: uint64_t = *b.offset(i0 as isize);
    let mut res_j_0: *mut uint64_t = res.offset(i0 as isize);
    let mut c_0: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_0: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, bj_0, c_0, res_i0_0);
    let mut a_i0_0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, bj_0, c_0, res_i1_0);
    let mut a_i1_0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, bj_0, c_0, res_i2_0);
    let mut a_i2_0: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, bj_0, c_0, res_i_0);
    let mut r_0: uint64_t = c_0;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: uint64_t = *b.offset(i0 as isize);
    let mut res_j_1: *mut uint64_t = res.offset(i0 as isize);
    let mut c_1: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_1: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, bj_1, c_1, res_i0_1);
    let mut a_i0_1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_1, bj_1, c_1, res_i1_1);
    let mut a_i1_1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_1, bj_1, c_1, res_i2_1);
    let mut a_i2_1: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_1: *mut uint64_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_1, bj_1, c_1, res_i_1);
    let mut r_1: uint64_t = c_1;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r_1;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: uint64_t = *b.offset(i0 as isize);
    let mut res_j_2: *mut uint64_t = res.offset(i0 as isize);
    let mut c_2: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_2: uint64_t = *a
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, bj_2, c_2, res_i0_2);
    let mut a_i0_2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_2, bj_2, c_2, res_i1_2);
    let mut a_i1_2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_2, bj_2, c_2, res_i2_2);
    let mut a_i2_2: uint64_t = *a
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_2: *mut uint64_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_2, bj_2, c_2, res_i_2);
    let mut r_2: uint64_t = c_2;
    *res.offset((4 as libc::c_uint).wrapping_add(i0) as isize) = r_2;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_sqr(
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut a_j: uint64_t = *a.offset(i0 as isize);
    let mut ab: *mut uint64_t = a;
    let mut res_j: *mut uint64_t = res.offset(i0 as isize);
    let mut c: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i: uint64_t = *ab.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
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
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_0: uint64_t = *a.offset(i0 as isize);
    let mut ab_0: *mut uint64_t = a;
    let mut res_j_0: *mut uint64_t = res.offset(i0 as isize);
    let mut c_0: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_1: uint64_t = *ab_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, a_j_0, c_0, res_i0_0);
        let mut a_i0_0: uint64_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, a_j_0, c_0, res_i1_0);
        let mut a_i1_0: uint64_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, a_j_0, c_0, res_i2_0);
        let mut a_i2_0: uint64_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint64_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, a_j_0, c_0, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < i0 {
        let mut a_i_2: uint64_t = *ab_0.offset(i_2 as isize);
        let mut res_i_2: *mut uint64_t = res_j_0.offset(i_2 as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, a_j_0, c_0, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut r_0: uint64_t = c_0;
    *res.offset(i0.wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_1: uint64_t = *a.offset(i0 as isize);
    let mut ab_1: *mut uint64_t = a;
    let mut res_j_1: *mut uint64_t = res.offset(i0 as isize);
    let mut c_1: uint64_t = 0 as libc::c_ulonglong;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_3: uint64_t = *ab_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
        let mut res_i0_1: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_3, a_j_1, c_1, res_i0_1);
        let mut a_i0_1: uint64_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_1: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(1 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_1, a_j_1, c_1, res_i1_1);
        let mut a_i1_1: uint64_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_1: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(2 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_1, a_j_1, c_1, res_i2_1);
        let mut a_i2_1: uint64_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_3: *mut uint64_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(3 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_1, a_j_1, c_1, res_i_3);
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
    let mut i_4: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_4 < i0 {
        let mut a_i_4: uint64_t = *ab_1.offset(i_4 as isize);
        let mut res_i_4: *mut uint64_t = res_j_1.offset(i_4 as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_4, a_j_1, c_1, res_i_4);
        i_4 = i_4.wrapping_add(1);
        i_4;
    }
    let mut r_1: uint64_t = c_1;
    *res.offset(i0.wrapping_add(i0) as isize) = r_1;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_2: uint64_t = *a.offset(i0 as isize);
    let mut ab_2: *mut uint64_t = a;
    let mut res_j_2: *mut uint64_t = res.offset(i0 as isize);
    let mut c_2: uint64_t = 0 as libc::c_ulonglong;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    while i_5 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_5: uint64_t = *ab_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
        let mut res_i0_2: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_5, a_j_2, c_2, res_i0_2);
        let mut a_i0_2: uint64_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_2: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(1 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_2, a_j_2, c_2, res_i1_2);
        let mut a_i1_2: uint64_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_2: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(2 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_2, a_j_2, c_2, res_i2_2);
        let mut a_i2_2: uint64_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_5: *mut uint64_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(3 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_2, a_j_2, c_2, res_i_5);
        i_5 = i_5.wrapping_add(1);
        i_5;
    }
    let mut i_6: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_6 < i0 {
        let mut a_i_6: uint64_t = *ab_2.offset(i_6 as isize);
        let mut res_i_6: *mut uint64_t = res_j_2.offset(i_6 as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_6, a_j_2, c_2, res_i_6);
        i_6 = i_6.wrapping_add(1);
        i_6;
    }
    let mut r_2: uint64_t = c_2;
    *res.offset(i0.wrapping_add(i0) as isize) = r_2;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_copy0: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut b_copy0: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r_3: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        8 as libc::c_uint,
        a_copy0.as_mut_ptr(),
        b_copy0.as_mut_ptr(),
        res,
    );
    let mut c0: uint64_t = r_3;
    let mut tmp: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut res1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1, 64 as libc::c_uint),
    );
    let mut lo: uint64_t = FStar_UInt128_uint128_to_uint64(res1);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut res1_0: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi_0: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1_0, 64 as libc::c_uint),
    );
    let mut lo_0: uint64_t = FStar_UInt128_uint128_to_uint64(res1_0);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo_0;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi_0;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut res1_1: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi_1: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1_1, 64 as libc::c_uint),
    );
    let mut lo_1: uint64_t = FStar_UInt128_uint128_to_uint64(res1_1);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo_1;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi_1;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut res1_2: FStar_UInt128_uint128 = FStar_UInt128_mul_wide(
        *a.offset(i_7 as isize),
        *a.offset(i_7 as isize),
    );
    let mut hi_2: uint64_t = FStar_UInt128_uint128_to_uint64(
        FStar_UInt128_shift_right(res1_2, 64 as libc::c_uint),
    );
    let mut lo_2: uint64_t = FStar_UInt128_uint128_to_uint64(res1_2);
    tmp[(2 as libc::c_uint).wrapping_mul(i_7) as usize] = lo_2;
    tmp[(2 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
        as usize] = hi_2;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_copy: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    let mut b_copy: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut r0: uint64_t = Hacl_Bignum_Addition_bn_add_eq_len_u64(
        8 as libc::c_uint,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        res,
    );
    let mut c1: uint64_t = r0;
}
#[inline]
unsafe extern "C" fn precompr2(
    mut nBits: uint32_t,
    mut n: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = nBits.wrapping_div(64 as libc::c_uint);
    let mut j: uint32_t = nBits.wrapping_rem(64 as libc::c_uint);
    *res.offset(i as isize) = *res.offset(i as isize) | (1 as libc::c_ulonglong) << j;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (512 as libc::c_uint).wrapping_sub(nBits) {
        let mut a_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        let mut b_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            a_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Bignum256_add_mod(n, a_copy.as_mut_ptr(), b_copy.as_mut_ptr(), res);
        i0 = i0.wrapping_add(1);
        i0;
    }
}
#[inline]
unsafe extern "C" fn reduction(
    mut n: *mut uint64_t,
    mut nInv: uint64_t,
    mut c: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut qj: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0: *mut uint64_t = c.offset(i0 as isize);
    let mut c1: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
    let mut a_i0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
    let mut a_i1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
    let mut a_i2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    let mut r: uint64_t = c1;
    let mut c10: uint64_t = r;
    let mut res_j: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10, res_j, resb);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_0: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_0: *mut uint64_t = c.offset(i0 as isize);
    let mut c1_0: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_0: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, qj_0, c1_0, res_i0_0);
    let mut a_i0_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, qj_0, c1_0, res_i1_0);
    let mut a_i1_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, qj_0, c1_0, res_i2_0);
    let mut a_i2_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, qj_0, c1_0, res_i_0);
    let mut r_0: uint64_t = c1_0;
    let mut c10_0: uint64_t = r_0;
    let mut res_j_0: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_0: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10_0, res_j_0, resb_0);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_1: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_1: *mut uint64_t = c.offset(i0 as isize);
    let mut c1_1: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_1: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, qj_1, c1_1, res_i0_1);
    let mut a_i0_1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_1, qj_1, c1_1, res_i1_1);
    let mut a_i1_1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_1, qj_1, c1_1, res_i2_1);
    let mut a_i2_1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_1, qj_1, c1_1, res_i_1);
    let mut r_1: uint64_t = c1_1;
    let mut c10_1: uint64_t = r_1;
    let mut res_j_1: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_1: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10_1, res_j_1, resb_1);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_2: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_2: *mut uint64_t = c.offset(i0 as isize);
    let mut c1_2: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_2: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, qj_2, c1_2, res_i0_2);
    let mut a_i0_2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_2, qj_2, c1_2, res_i1_2);
    let mut a_i1_2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_2, qj_2, c1_2, res_i2_2);
    let mut a_i2_2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_2, qj_2, c1_2, res_i_2);
    let mut r_2: uint64_t = c1_2;
    let mut c10_2: uint64_t = r_2;
    let mut res_j_2: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_2: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10_2, res_j_2, resb_2);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        res as *mut libc::c_void,
        c.offset(4 as libc::c_uint as isize) as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c00: uint64_t = c0;
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c1_3: uint64_t = 0 as libc::c_ulonglong;
    let mut t1: uint64_t = *res
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut t20: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_3: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_3 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_3, t1, t20, res_i0_3);
    let mut t10: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_3: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_3 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_3, t10, t21, res_i1_3);
    let mut t11: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_3: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_3 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_3, t11, t22, res_i2_3);
    let mut t12: uint64_t = *res
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_3: *mut uint64_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_3 = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(c1_3, t12, t2, res_i_3);
    let mut c10_3: uint64_t = c1_3;
    let mut c2: uint64_t = c00.wrapping_sub(c10_3);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os: *mut uint64_t = res;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = c2 & *res.offset(i as isize) | !c2 & tmp[i as usize];
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn to(
    mut n: *mut uint64_t,
    mut nInv: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut aM: *mut uint64_t,
) {
    let mut c: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Bignum256_mul(a, r2, c.as_mut_ptr());
    reduction(n, nInv, c.as_mut_ptr(), aM);
}
#[inline]
unsafe extern "C" fn from(
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut a: *mut uint64_t,
) {
    let mut tmp: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        tmp.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    reduction(n, nInv_u64, tmp.as_mut_ptr(), a);
}
#[inline]
unsafe extern "C" fn areduction(
    mut n: *mut uint64_t,
    mut nInv: uint64_t,
    mut c: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut c0: uint64_t = 0 as libc::c_ulonglong;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut qj: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0: *mut uint64_t = c.offset(i0 as isize);
    let mut c1: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i, qj, c1, res_i0);
    let mut a_i0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0, qj, c1, res_i1);
    let mut a_i1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1, qj, c1, res_i2);
    let mut a_i2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint64_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2, qj, c1, res_i);
    let mut r: uint64_t = c1;
    let mut c10: uint64_t = r;
    let mut res_j: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10, res_j, resb);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_0: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_0: *mut uint64_t = c.offset(i0 as isize);
    let mut c1_0: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_0: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_0, qj_0, c1_0, res_i0_0);
    let mut a_i0_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_0, qj_0, c1_0, res_i1_0);
    let mut a_i1_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_0, qj_0, c1_0, res_i2_0);
    let mut a_i2_0: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint64_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_0, qj_0, c1_0, res_i_0);
    let mut r_0: uint64_t = c1_0;
    let mut c10_0: uint64_t = r_0;
    let mut res_j_0: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_0: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10_0, res_j_0, resb_0);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_1: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_1: *mut uint64_t = c.offset(i0 as isize);
    let mut c1_1: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_1: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_1, qj_1, c1_1, res_i0_1);
    let mut a_i0_1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_1, qj_1, c1_1, res_i1_1);
    let mut a_i1_1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_1, qj_1, c1_1, res_i2_1);
    let mut a_i2_1: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_1: *mut uint64_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_1, qj_1, c1_1, res_i_1);
    let mut r_1: uint64_t = c1_1;
    let mut c10_1: uint64_t = r_1;
    let mut res_j_1: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_1: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10_1, res_j_1, resb_1);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_2: uint64_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_2: *mut uint64_t = c.offset(i0 as isize);
    let mut c1_2: uint64_t = 0 as libc::c_ulonglong;
    let mut a_i_2: uint64_t = *n
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i_2, qj_2, c1_2, res_i0_2);
    let mut a_i0_2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i0_2, qj_2, c1_2, res_i1_2);
    let mut a_i1_2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i1_2, qj_2, c1_2, res_i2_2);
    let mut a_i2_2: uint64_t = *n
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_2: *mut uint64_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u64(a_i2_2, qj_2, c1_2, res_i_2);
    let mut r_2: uint64_t = c1_2;
    let mut c10_2: uint64_t = r_2;
    let mut res_j_2: uint64_t = *c.offset((4 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_2: *mut uint64_t = c
        .offset(4 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_128_add_carry_u64(c0, c10_2, res_j_2, resb_2);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        res as *mut libc::c_void,
        c.offset(4 as libc::c_uint as isize) as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut c00: uint64_t = c0;
    let mut tmp: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c1_3: uint64_t = Hacl_Bignum256_sub(res, n, tmp.as_mut_ptr());
    let mut m: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(c00);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = m & tmp[i as usize] | !m & *res.offset(i as isize);
    let mut os: *mut uint64_t = res;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = m & tmp[i as usize] | !m & *res.offset(i as isize);
    let mut os_0: *mut uint64_t = res;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = m & tmp[i as usize] | !m & *res.offset(i as isize);
    let mut os_1: *mut uint64_t = res;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = m & tmp[i as usize] | !m & *res.offset(i as isize);
    let mut os_2: *mut uint64_t = res;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn amont_mul(
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut bM: *mut uint64_t,
    mut resM: *mut uint64_t,
) {
    let mut c: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Bignum256_mul(aM, bM, c.as_mut_ptr());
    areduction(n, nInv_u64, c.as_mut_ptr(), resM);
}
#[inline]
unsafe extern "C" fn amont_sqr(
    mut n: *mut uint64_t,
    mut nInv_u64: uint64_t,
    mut aM: *mut uint64_t,
    mut resM: *mut uint64_t,
) {
    let mut c: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Bignum256_sqr(aM, c.as_mut_ptr());
    areduction(n, nInv_u64, c.as_mut_ptr(), resM);
}
#[inline]
unsafe extern "C" fn bn_slow_precomp(
    mut n: *mut uint64_t,
    mut mu: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut a_mod: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut a1: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        a1.as_mut_ptr() as *mut libc::c_void,
        a as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    areduction(n, mu, a1.as_mut_ptr(), a_mod.as_mut_ptr());
    to(n, mu, r2, a_mod.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) -> bool {
    let mut one: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    one[0 as libc::c_uint as usize] = 1 as libc::c_ulonglong;
    let mut bit0: uint64_t = *n.offset(0 as libc::c_uint as isize)
        & 1 as libc::c_ulonglong;
    let mut m0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bit0);
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint64_t = FStar_UInt64_eq_mask(one[i as usize], *n.offset(i as isize));
    let mut blt: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq & acc | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_0: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_0 & acc | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_1: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_1 & acc | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_2: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_2 & acc | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m1: uint64_t = acc;
    let mut is_valid_m: uint64_t = m0 & m1;
    let mut nBits: uint32_t = (64 as libc::c_uint)
        .wrapping_mul(
            Hacl_Bignum_Lib_bn_get_top_index_u64(4 as libc::c_uint, n) as uint32_t,
        );
    if is_valid_m == 0xffffffffffffffff as libc::c_ulonglong {
        let mut r2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        precompr2(nBits, n, r2.as_mut_ptr());
        let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
            *n.offset(0 as libc::c_uint as isize),
        );
        bn_slow_precomp(n, mu, r2.as_mut_ptr(), a, res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffffffffffff as libc::c_ulonglong;
}
unsafe extern "C" fn exp_check(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
) -> uint64_t {
    let mut one: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    one[0 as libc::c_uint as usize] = 1 as libc::c_ulonglong;
    let mut bit0: uint64_t = *n.offset(0 as libc::c_uint as isize)
        & 1 as libc::c_ulonglong;
    let mut m0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bit0);
    let mut acc0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint64_t = FStar_UInt64_eq_mask(one[i as usize], *n.offset(i as isize));
    let mut blt: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq & acc0 | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_0: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_0 & acc0 | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_1: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_1 & acc0 | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_2: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_2 & acc0 | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
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
                b"Hacl_Bignum256.c\0" as *const u8 as *const libc::c_char,
                576 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = bLen as usize;
        let mut b2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
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
            let mut beq_3: uint64_t = FStar_UInt64_eq_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            let mut blt_3: uint64_t = !FStar_UInt64_gte_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            acc = beq_3 & acc | !beq_3 & blt_3;
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
    let mut beq_4: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_4: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_4 & acc_0 | !beq_4 & blt_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_5: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_5: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_5 & acc_0 | !beq_5 & blt_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_6: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_6: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_6 & acc_0 | !beq_6 & blt_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_7: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_7: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_7 & acc_0 | !beq_7 & blt_7;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m2: uint64_t = acc_0;
    let mut m: uint64_t = m1 & m2;
    return m00 & m;
}
#[inline]
unsafe extern "C" fn exp_vartime_precomp(
    mut n: *mut uint64_t,
    mut mu: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if bBits < 200 as libc::c_uint {
        let mut aM: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        to(n, mu, r2, a, aM.as_mut_ptr());
        let mut resM: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        let mut ctx: [uint64_t; 8] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(4 as libc::c_uint as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n0: *mut uint64_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint64_t = ctx
            .as_mut_ptr()
            .offset(4 as libc::c_uint as isize);
        from(ctx_n0, mu, ctx_r2, resM.as_mut_ptr());
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < bBits {
            let mut i1: uint32_t = i.wrapping_div(64 as libc::c_uint);
            let mut j: uint32_t = i.wrapping_rem(64 as libc::c_uint);
            let mut tmp: uint64_t = *b.offset(i1 as isize);
            let mut bit: uint64_t = tmp >> j & 1 as libc::c_ulonglong;
            if !(bit == 0 as libc::c_ulonglong) {
                let mut aM_copy: [uint64_t; 4] = [
                    0 as libc::c_uint as uint64_t,
                    0,
                    0,
                    0,
                ];
                memcpy(
                    aM_copy.as_mut_ptr() as *mut libc::c_void,
                    resM.as_mut_ptr() as *const libc::c_void,
                    (4 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(
                            ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
                        ),
                );
                let mut ctx_n: *mut uint64_t = ctx.as_mut_ptr();
                amont_mul(
                    ctx_n,
                    mu,
                    aM_copy.as_mut_ptr(),
                    aM.as_mut_ptr(),
                    resM.as_mut_ptr(),
                );
            }
            let mut aM_copy_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
            memcpy(
                aM_copy_0.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (4 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut ctx_n_0: *mut uint64_t = ctx.as_mut_ptr();
            amont_sqr(ctx_n_0, mu, aM_copy_0.as_mut_ptr(), aM.as_mut_ptr());
            i = i.wrapping_add(1);
            i;
        }
        from(n, mu, resM.as_mut_ptr(), res);
        return;
    }
    let mut aM_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    to(n, mu, r2, a, aM_0.as_mut_ptr());
    let mut resM_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    let mut ctx_0: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(4 as libc::c_uint as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut table: [uint64_t; 64] = [
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
    let mut tmp_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut t0: *mut uint64_t = table.as_mut_ptr();
    let mut t1: *mut uint64_t = table.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut ctx_n0_0: *mut uint64_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint64_t = ctx_0
        .as_mut_ptr()
        .offset(4 as libc::c_uint as isize);
    from(ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1, mu, aM_copy0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_1: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_1, mu, aM_copy_1.as_mut_ptr(), t2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_0, mu, aM_copy0_0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_2, mu, aM_copy_2.as_mut_ptr(), t2_0, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_1: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_1, mu, aM_copy0_1.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_3: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_3, mu, aM_copy_3.as_mut_ptr(), t2_1, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_2, mu, aM_copy0_2.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_4: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_4, mu, aM_copy_4.as_mut_ptr(), t2_2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_3: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_3, mu, aM_copy0_3.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_5: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_5, mu, aM_copy_5.as_mut_ptr(), t2_3, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_4: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_4, mu, aM_copy0_4.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_6: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_6, mu, aM_copy_6.as_mut_ptr(), t2_4, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_5: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_5, mu, aM_copy0_5.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_7: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_7.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_7: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_7, mu, aM_copy_7.as_mut_ptr(), t2_5, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
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
            .offset(bits_l32.wrapping_mul(4 as libc::c_uint) as isize);
        memcpy(
            resM_0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l as *mut uint64_t as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
    } else {
        let mut ctx_n_8: *mut uint64_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint64_t = ctx_0
            .as_mut_ptr()
            .offset(4 as libc::c_uint as isize);
        from(ctx_n_8, mu, ctx_r2_0, resM_0.as_mut_ptr());
    }
    let mut tmp0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut i_2: uint32_t = 0 as libc::c_uint;
    while i_2 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i0: uint32_t = 0 as libc::c_uint;
        let mut aM_copy_8: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_9, mu, aM_copy_8.as_mut_ptr(), resM_0.as_mut_ptr());
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_9: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_10, mu, aM_copy_9.as_mut_ptr(), resM_0.as_mut_ptr());
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_10: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_11, mu, aM_copy_10.as_mut_ptr(), resM_0.as_mut_ptr());
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_11: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_12, mu, aM_copy_11.as_mut_ptr(), resM_0.as_mut_ptr());
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
            .offset(bits_l32_0.wrapping_mul(4 as libc::c_uint) as isize);
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l_0 as *mut uint64_t as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut aM_copy_12: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_12.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_13: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_mul(
            ctx_n_13,
            mu,
            aM_copy_12.as_mut_ptr(),
            tmp0.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    from(n, mu, resM_0.as_mut_ptr(), res);
}
#[inline]
unsafe extern "C" fn exp_consttime_precomp(
    mut n: *mut uint64_t,
    mut mu: uint64_t,
    mut r2: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    if bBits < 200 as libc::c_uint {
        let mut aM: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        to(n, mu, r2, a, aM.as_mut_ptr());
        let mut resM: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        let mut ctx: [uint64_t; 8] = [
            0 as libc::c_uint as uint64_t,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ];
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(4 as libc::c_uint as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut sw: uint64_t = 0 as libc::c_ulonglong;
        let mut ctx_n0: *mut uint64_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint64_t = ctx
            .as_mut_ptr()
            .offset(4 as libc::c_uint as isize);
        from(ctx_n0, mu, ctx_r2, resM.as_mut_ptr());
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
            let mut dummy: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy;
            aM[i as usize] = aM[i as usize] ^ dummy;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_0;
            aM[i as usize] = aM[i as usize] ^ dummy_0;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_1: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_1;
            aM[i as usize] = aM[i as usize] ^ dummy_1;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_2: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_2;
            aM[i as usize] = aM[i as usize] ^ dummy_2;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut aM_copy: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
            memcpy(
                aM_copy.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (4 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut ctx_n1: *mut uint64_t = ctx.as_mut_ptr();
            amont_mul(
                ctx_n1,
                mu,
                aM_copy.as_mut_ptr(),
                resM.as_mut_ptr(),
                aM.as_mut_ptr(),
            );
            let mut aM_copy0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
            memcpy(
                aM_copy0.as_mut_ptr() as *mut libc::c_void,
                resM.as_mut_ptr() as *const libc::c_void,
                (4 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut ctx_n: *mut uint64_t = ctx.as_mut_ptr();
            amont_sqr(ctx_n, mu, aM_copy0.as_mut_ptr(), resM.as_mut_ptr());
            sw = bit;
            i0 = i0.wrapping_add(1);
            i0;
        }
        let mut sw0: uint64_t = sw;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        let mut dummy_3: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_3;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_3;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_4: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_4;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_4;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_5: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_5;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_5;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_6: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_6;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_6;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        from(n, mu, resM.as_mut_ptr(), res);
        return;
    }
    let mut aM_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    to(n, mu, r2, a, aM_0.as_mut_ptr());
    let mut resM_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    let mut ctx_0: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(4 as libc::c_uint as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut table: [uint64_t; 64] = [
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
    let mut tmp_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut t0: *mut uint64_t = table.as_mut_ptr();
    let mut t1: *mut uint64_t = table.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut ctx_n0_0: *mut uint64_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint64_t = ctx_0
        .as_mut_ptr()
        .offset(4 as libc::c_uint as isize);
    from(ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_0, mu, aM_copy0_0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_0.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_0: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_0, mu, aM_copy_0.as_mut_ptr(), t2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_1: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_1, mu, aM_copy0_1.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_1: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_1, mu, aM_copy_1.as_mut_ptr(), t2_0, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_2, mu, aM_copy0_2.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_2, mu, aM_copy_2.as_mut_ptr(), t2_1, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_3: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_3, mu, aM_copy0_3.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_3: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_3, mu, aM_copy_3.as_mut_ptr(), t2_2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_4: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_4, mu, aM_copy0_4.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_4: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_4, mu, aM_copy_4.as_mut_ptr(), t2_3, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_5: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_5, mu, aM_copy0_5.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_5: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_5, mu, aM_copy_5.as_mut_ptr(), t2_4, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy0_6: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy0_6.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n1_6: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_6, mu, aM_copy0_6.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint64_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint) as isize,
        );
    let mut aM_copy_6: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint64_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_6, mu, aM_copy_6.as_mut_ptr(), t2_5, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(4 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
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
            table.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i1_0: uint32_t = 0 as libc::c_uint;
        let mut c: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut x: uint64_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os: *mut uint64_t = resM_0.as_mut_ptr();
        *os.offset(i_2 as isize) = x;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_0: uint64_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_0: *mut uint64_t = resM_0.as_mut_ptr();
        *os_0.offset(i_2 as isize) = x_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_1: uint64_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_1: *mut uint64_t = resM_0.as_mut_ptr();
        *os_1.offset(i_2 as isize) = x_1;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_2: uint64_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_2: *mut uint64_t = resM_0.as_mut_ptr();
        *os_2.offset(i_2 as isize) = x_2;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_0: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_0: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_3: uint32_t = 0 as libc::c_uint;
        let mut x_3: uint64_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_3: *mut uint64_t = resM_0.as_mut_ptr();
        *os_3.offset(i_3 as isize) = x_3;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_4: uint64_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_4: *mut uint64_t = resM_0.as_mut_ptr();
        *os_4.offset(i_3 as isize) = x_4;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_5: uint64_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_5: *mut uint64_t = resM_0.as_mut_ptr();
        *os_5.offset(i_3 as isize) = x_5;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_6: uint64_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_6: *mut uint64_t = resM_0.as_mut_ptr();
        *os_6.offset(i_3 as isize) = x_6;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_1: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_1: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut x_7: uint64_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_7: *mut uint64_t = resM_0.as_mut_ptr();
        *os_7.offset(i_4 as isize) = x_7;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_8: uint64_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_8: *mut uint64_t = resM_0.as_mut_ptr();
        *os_8.offset(i_4 as isize) = x_8;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_9: uint64_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_9: *mut uint64_t = resM_0.as_mut_ptr();
        *os_9.offset(i_4 as isize) = x_9;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_10: uint64_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_10: *mut uint64_t = resM_0.as_mut_ptr();
        *os_10.offset(i_4 as isize) = x_10;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_2: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_2: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_5: uint32_t = 0 as libc::c_uint;
        let mut x_11: uint64_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_11: *mut uint64_t = resM_0.as_mut_ptr();
        *os_11.offset(i_5 as isize) = x_11;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_12: uint64_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_12: *mut uint64_t = resM_0.as_mut_ptr();
        *os_12.offset(i_5 as isize) = x_12;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_13: uint64_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_13: *mut uint64_t = resM_0.as_mut_ptr();
        *os_13.offset(i_5 as isize) = x_13;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_14: uint64_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_14: *mut uint64_t = resM_0.as_mut_ptr();
        *os_14.offset(i_5 as isize) = x_14;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_3: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_3: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_6: uint32_t = 0 as libc::c_uint;
        let mut x_15: uint64_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_15: *mut uint64_t = resM_0.as_mut_ptr();
        *os_15.offset(i_6 as isize) = x_15;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_16: uint64_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_16: *mut uint64_t = resM_0.as_mut_ptr();
        *os_16.offset(i_6 as isize) = x_16;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_17: uint64_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_17: *mut uint64_t = resM_0.as_mut_ptr();
        *os_17.offset(i_6 as isize) = x_17;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_18: uint64_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_18: *mut uint64_t = resM_0.as_mut_ptr();
        *os_18.offset(i_6 as isize) = x_18;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_4: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_4: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_7: uint32_t = 0 as libc::c_uint;
        let mut x_19: uint64_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_19: *mut uint64_t = resM_0.as_mut_ptr();
        *os_19.offset(i_7 as isize) = x_19;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_20: uint64_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_20: *mut uint64_t = resM_0.as_mut_ptr();
        *os_20.offset(i_7 as isize) = x_20;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_21: uint64_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_21: *mut uint64_t = resM_0.as_mut_ptr();
        *os_21.offset(i_7 as isize) = x_21;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_22: uint64_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_22: *mut uint64_t = resM_0.as_mut_ptr();
        *os_22.offset(i_7 as isize) = x_22;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_5: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_5: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_8: uint32_t = 0 as libc::c_uint;
        let mut x_23: uint64_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_23: *mut uint64_t = resM_0.as_mut_ptr();
        *os_23.offset(i_8 as isize) = x_23;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_24: uint64_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_24: *mut uint64_t = resM_0.as_mut_ptr();
        *os_24.offset(i_8 as isize) = x_24;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_25: uint64_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_25: *mut uint64_t = resM_0.as_mut_ptr();
        *os_25.offset(i_8 as isize) = x_25;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_26: uint64_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_26: *mut uint64_t = resM_0.as_mut_ptr();
        *os_26.offset(i_8 as isize) = x_26;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_6: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_6: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_9: uint32_t = 0 as libc::c_uint;
        let mut x_27: uint64_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_27: *mut uint64_t = resM_0.as_mut_ptr();
        *os_27.offset(i_9 as isize) = x_27;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_28: uint64_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_28: *mut uint64_t = resM_0.as_mut_ptr();
        *os_28.offset(i_9 as isize) = x_28;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_29: uint64_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_29: *mut uint64_t = resM_0.as_mut_ptr();
        *os_29.offset(i_9 as isize) = x_29;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_30: uint64_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_30: *mut uint64_t = resM_0.as_mut_ptr();
        *os_30.offset(i_9 as isize) = x_30;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_7: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_7: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_10: uint32_t = 0 as libc::c_uint;
        let mut x_31: uint64_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_31: *mut uint64_t = resM_0.as_mut_ptr();
        *os_31.offset(i_10 as isize) = x_31;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_32: uint64_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_32: *mut uint64_t = resM_0.as_mut_ptr();
        *os_32.offset(i_10 as isize) = x_32;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_33: uint64_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_33: *mut uint64_t = resM_0.as_mut_ptr();
        *os_33.offset(i_10 as isize) = x_33;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_34: uint64_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_34: *mut uint64_t = resM_0.as_mut_ptr();
        *os_34.offset(i_10 as isize) = x_34;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_8: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_8: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_11: uint32_t = 0 as libc::c_uint;
        let mut x_35: uint64_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_35: *mut uint64_t = resM_0.as_mut_ptr();
        *os_35.offset(i_11 as isize) = x_35;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_36: uint64_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_36: *mut uint64_t = resM_0.as_mut_ptr();
        *os_36.offset(i_11 as isize) = x_36;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_37: uint64_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_37: *mut uint64_t = resM_0.as_mut_ptr();
        *os_37.offset(i_11 as isize) = x_37;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_38: uint64_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_38: *mut uint64_t = resM_0.as_mut_ptr();
        *os_38.offset(i_11 as isize) = x_38;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_9: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_9: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_12: uint32_t = 0 as libc::c_uint;
        let mut x_39: uint64_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_39: *mut uint64_t = resM_0.as_mut_ptr();
        *os_39.offset(i_12 as isize) = x_39;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_40: uint64_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_40: *mut uint64_t = resM_0.as_mut_ptr();
        *os_40.offset(i_12 as isize) = x_40;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_41: uint64_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_41: *mut uint64_t = resM_0.as_mut_ptr();
        *os_41.offset(i_12 as isize) = x_41;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_42: uint64_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_42: *mut uint64_t = resM_0.as_mut_ptr();
        *os_42.offset(i_12 as isize) = x_42;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_10: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_10: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_13: uint32_t = 0 as libc::c_uint;
        let mut x_43: uint64_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_43: *mut uint64_t = resM_0.as_mut_ptr();
        *os_43.offset(i_13 as isize) = x_43;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_44: uint64_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_44: *mut uint64_t = resM_0.as_mut_ptr();
        *os_44.offset(i_13 as isize) = x_44;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_45: uint64_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_45: *mut uint64_t = resM_0.as_mut_ptr();
        *os_45.offset(i_13 as isize) = x_45;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_46: uint64_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_46: *mut uint64_t = resM_0.as_mut_ptr();
        *os_46.offset(i_13 as isize) = x_46;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_11: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_11: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_14: uint32_t = 0 as libc::c_uint;
        let mut x_47: uint64_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_47: *mut uint64_t = resM_0.as_mut_ptr();
        *os_47.offset(i_14 as isize) = x_47;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_48: uint64_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_48: *mut uint64_t = resM_0.as_mut_ptr();
        *os_48.offset(i_14 as isize) = x_48;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_49: uint64_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_49: *mut uint64_t = resM_0.as_mut_ptr();
        *os_49.offset(i_14 as isize) = x_49;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_50: uint64_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_50: *mut uint64_t = resM_0.as_mut_ptr();
        *os_50.offset(i_14 as isize) = x_50;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_12: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_12: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_15: uint32_t = 0 as libc::c_uint;
        let mut x_51: uint64_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_51: *mut uint64_t = resM_0.as_mut_ptr();
        *os_51.offset(i_15 as isize) = x_51;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_52: uint64_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_52: *mut uint64_t = resM_0.as_mut_ptr();
        *os_52.offset(i_15 as isize) = x_52;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_53: uint64_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_53: *mut uint64_t = resM_0.as_mut_ptr();
        *os_53.offset(i_15 as isize) = x_53;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_54: uint64_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_54: *mut uint64_t = resM_0.as_mut_ptr();
        *os_54.offset(i_15 as isize) = x_54;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_13: uint64_t = FStar_UInt64_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_13: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_16: uint32_t = 0 as libc::c_uint;
        let mut x_55: uint64_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_55: *mut uint64_t = resM_0.as_mut_ptr();
        *os_55.offset(i_16 as isize) = x_55;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_56: uint64_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_56: *mut uint64_t = resM_0.as_mut_ptr();
        *os_56.offset(i_16 as isize) = x_56;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_57: uint64_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_57: *mut uint64_t = resM_0.as_mut_ptr();
        *os_57.offset(i_16 as isize) = x_57;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_58: uint64_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_58: *mut uint64_t = resM_0.as_mut_ptr();
        *os_58.offset(i_16 as isize) = x_58;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    } else {
        let mut ctx_n_7: *mut uint64_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint64_t = ctx_0
            .as_mut_ptr()
            .offset(4 as libc::c_uint as isize);
        from(ctx_n_7, mu, ctx_r2_0, resM_0.as_mut_ptr());
    }
    let mut tmp0: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut i0_1: uint32_t = 0 as libc::c_uint;
    while i0_1 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i_17: uint32_t = 0 as libc::c_uint;
        let mut aM_copy_7: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_7.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_8: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_8, mu, aM_copy_7.as_mut_ptr(), resM_0.as_mut_ptr());
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_8: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_9, mu, aM_copy_8.as_mut_ptr(), resM_0.as_mut_ptr());
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_9: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_10, mu, aM_copy_9.as_mut_ptr(), resM_0.as_mut_ptr());
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_10: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_11, mu, aM_copy_10.as_mut_ptr(), resM_0.as_mut_ptr());
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
            table.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i1_1: uint32_t = 0 as libc::c_uint;
        let mut c_14: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_14: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_18: uint32_t = 0 as libc::c_uint;
        let mut x_59: uint64_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_59: *mut uint64_t = tmp0.as_mut_ptr();
        *os_59.offset(i_18 as isize) = x_59;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_60: uint64_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_60: *mut uint64_t = tmp0.as_mut_ptr();
        *os_60.offset(i_18 as isize) = x_60;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_61: uint64_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_61: *mut uint64_t = tmp0.as_mut_ptr();
        *os_61.offset(i_18 as isize) = x_61;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_62: uint64_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_62: *mut uint64_t = tmp0.as_mut_ptr();
        *os_62.offset(i_18 as isize) = x_62;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_15: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_15: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_19: uint32_t = 0 as libc::c_uint;
        let mut x_63: uint64_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_63: *mut uint64_t = tmp0.as_mut_ptr();
        *os_63.offset(i_19 as isize) = x_63;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_64: uint64_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_64: *mut uint64_t = tmp0.as_mut_ptr();
        *os_64.offset(i_19 as isize) = x_64;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_65: uint64_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_65: *mut uint64_t = tmp0.as_mut_ptr();
        *os_65.offset(i_19 as isize) = x_65;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_66: uint64_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_66: *mut uint64_t = tmp0.as_mut_ptr();
        *os_66.offset(i_19 as isize) = x_66;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_16: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_16: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_20: uint32_t = 0 as libc::c_uint;
        let mut x_67: uint64_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_67: *mut uint64_t = tmp0.as_mut_ptr();
        *os_67.offset(i_20 as isize) = x_67;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_68: uint64_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_68: *mut uint64_t = tmp0.as_mut_ptr();
        *os_68.offset(i_20 as isize) = x_68;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_69: uint64_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_69: *mut uint64_t = tmp0.as_mut_ptr();
        *os_69.offset(i_20 as isize) = x_69;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_70: uint64_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_70: *mut uint64_t = tmp0.as_mut_ptr();
        *os_70.offset(i_20 as isize) = x_70;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_17: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_17: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_21: uint32_t = 0 as libc::c_uint;
        let mut x_71: uint64_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_71: *mut uint64_t = tmp0.as_mut_ptr();
        *os_71.offset(i_21 as isize) = x_71;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_72: uint64_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_72: *mut uint64_t = tmp0.as_mut_ptr();
        *os_72.offset(i_21 as isize) = x_72;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_73: uint64_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_73: *mut uint64_t = tmp0.as_mut_ptr();
        *os_73.offset(i_21 as isize) = x_73;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_74: uint64_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_74: *mut uint64_t = tmp0.as_mut_ptr();
        *os_74.offset(i_21 as isize) = x_74;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_18: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_18: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_22: uint32_t = 0 as libc::c_uint;
        let mut x_75: uint64_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_75: *mut uint64_t = tmp0.as_mut_ptr();
        *os_75.offset(i_22 as isize) = x_75;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_76: uint64_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_76: *mut uint64_t = tmp0.as_mut_ptr();
        *os_76.offset(i_22 as isize) = x_76;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_77: uint64_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_77: *mut uint64_t = tmp0.as_mut_ptr();
        *os_77.offset(i_22 as isize) = x_77;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_78: uint64_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_78: *mut uint64_t = tmp0.as_mut_ptr();
        *os_78.offset(i_22 as isize) = x_78;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_19: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_19: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_23: uint32_t = 0 as libc::c_uint;
        let mut x_79: uint64_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_79: *mut uint64_t = tmp0.as_mut_ptr();
        *os_79.offset(i_23 as isize) = x_79;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_80: uint64_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_80: *mut uint64_t = tmp0.as_mut_ptr();
        *os_80.offset(i_23 as isize) = x_80;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_81: uint64_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_81: *mut uint64_t = tmp0.as_mut_ptr();
        *os_81.offset(i_23 as isize) = x_81;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_82: uint64_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_82: *mut uint64_t = tmp0.as_mut_ptr();
        *os_82.offset(i_23 as isize) = x_82;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_20: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_20: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_24: uint32_t = 0 as libc::c_uint;
        let mut x_83: uint64_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_83: *mut uint64_t = tmp0.as_mut_ptr();
        *os_83.offset(i_24 as isize) = x_83;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_84: uint64_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_84: *mut uint64_t = tmp0.as_mut_ptr();
        *os_84.offset(i_24 as isize) = x_84;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_85: uint64_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_85: *mut uint64_t = tmp0.as_mut_ptr();
        *os_85.offset(i_24 as isize) = x_85;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_86: uint64_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_86: *mut uint64_t = tmp0.as_mut_ptr();
        *os_86.offset(i_24 as isize) = x_86;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_21: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_21: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_25: uint32_t = 0 as libc::c_uint;
        let mut x_87: uint64_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_87: *mut uint64_t = tmp0.as_mut_ptr();
        *os_87.offset(i_25 as isize) = x_87;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_88: uint64_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_88: *mut uint64_t = tmp0.as_mut_ptr();
        *os_88.offset(i_25 as isize) = x_88;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_89: uint64_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_89: *mut uint64_t = tmp0.as_mut_ptr();
        *os_89.offset(i_25 as isize) = x_89;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_90: uint64_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_90: *mut uint64_t = tmp0.as_mut_ptr();
        *os_90.offset(i_25 as isize) = x_90;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_22: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_22: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_26: uint32_t = 0 as libc::c_uint;
        let mut x_91: uint64_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_91: *mut uint64_t = tmp0.as_mut_ptr();
        *os_91.offset(i_26 as isize) = x_91;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_92: uint64_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_92: *mut uint64_t = tmp0.as_mut_ptr();
        *os_92.offset(i_26 as isize) = x_92;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_93: uint64_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_93: *mut uint64_t = tmp0.as_mut_ptr();
        *os_93.offset(i_26 as isize) = x_93;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_94: uint64_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_94: *mut uint64_t = tmp0.as_mut_ptr();
        *os_94.offset(i_26 as isize) = x_94;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_23: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_23: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_27: uint32_t = 0 as libc::c_uint;
        let mut x_95: uint64_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_95: *mut uint64_t = tmp0.as_mut_ptr();
        *os_95.offset(i_27 as isize) = x_95;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_96: uint64_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_96: *mut uint64_t = tmp0.as_mut_ptr();
        *os_96.offset(i_27 as isize) = x_96;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_97: uint64_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_97: *mut uint64_t = tmp0.as_mut_ptr();
        *os_97.offset(i_27 as isize) = x_97;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_98: uint64_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_98: *mut uint64_t = tmp0.as_mut_ptr();
        *os_98.offset(i_27 as isize) = x_98;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_24: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_24: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_28: uint32_t = 0 as libc::c_uint;
        let mut x_99: uint64_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_99: *mut uint64_t = tmp0.as_mut_ptr();
        *os_99.offset(i_28 as isize) = x_99;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_100: uint64_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_100: *mut uint64_t = tmp0.as_mut_ptr();
        *os_100.offset(i_28 as isize) = x_100;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_101: uint64_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_101: *mut uint64_t = tmp0.as_mut_ptr();
        *os_101.offset(i_28 as isize) = x_101;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_102: uint64_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_102: *mut uint64_t = tmp0.as_mut_ptr();
        *os_102.offset(i_28 as isize) = x_102;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_25: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_25: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_29: uint32_t = 0 as libc::c_uint;
        let mut x_103: uint64_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_103: *mut uint64_t = tmp0.as_mut_ptr();
        *os_103.offset(i_29 as isize) = x_103;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_104: uint64_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_104: *mut uint64_t = tmp0.as_mut_ptr();
        *os_104.offset(i_29 as isize) = x_104;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_105: uint64_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_105: *mut uint64_t = tmp0.as_mut_ptr();
        *os_105.offset(i_29 as isize) = x_105;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_106: uint64_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_106: *mut uint64_t = tmp0.as_mut_ptr();
        *os_106.offset(i_29 as isize) = x_106;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_26: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_26: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_30: uint32_t = 0 as libc::c_uint;
        let mut x_107: uint64_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_107: *mut uint64_t = tmp0.as_mut_ptr();
        *os_107.offset(i_30 as isize) = x_107;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_108: uint64_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_108: *mut uint64_t = tmp0.as_mut_ptr();
        *os_108.offset(i_30 as isize) = x_108;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_109: uint64_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_109: *mut uint64_t = tmp0.as_mut_ptr();
        *os_109.offset(i_30 as isize) = x_109;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_110: uint64_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_110: *mut uint64_t = tmp0.as_mut_ptr();
        *os_110.offset(i_30 as isize) = x_110;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_27: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_27: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_31: uint32_t = 0 as libc::c_uint;
        let mut x_111: uint64_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_111: *mut uint64_t = tmp0.as_mut_ptr();
        *os_111.offset(i_31 as isize) = x_111;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_112: uint64_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_112: *mut uint64_t = tmp0.as_mut_ptr();
        *os_112.offset(i_31 as isize) = x_112;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_113: uint64_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_113: *mut uint64_t = tmp0.as_mut_ptr();
        *os_113.offset(i_31 as isize) = x_113;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_114: uint64_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_114: *mut uint64_t = tmp0.as_mut_ptr();
        *os_114.offset(i_31 as isize) = x_114;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_28: uint64_t = FStar_UInt64_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint) as uint64_t,
        );
        let mut res_j_28: *const uint64_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(4 as libc::c_uint)
                    as isize,
            );
        let mut i_32: uint32_t = 0 as libc::c_uint;
        let mut x_115: uint64_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_115: *mut uint64_t = tmp0.as_mut_ptr();
        *os_115.offset(i_32 as isize) = x_115;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_116: uint64_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_116: *mut uint64_t = tmp0.as_mut_ptr();
        *os_116.offset(i_32 as isize) = x_116;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_117: uint64_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_117: *mut uint64_t = tmp0.as_mut_ptr();
        *os_117.offset(i_32 as isize) = x_117;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_118: uint64_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_118: *mut uint64_t = tmp0.as_mut_ptr();
        *os_118.offset(i_32 as isize) = x_118;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_11: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint64_t = ctx_0.as_mut_ptr();
        amont_mul(
            ctx_n_12,
            mu,
            aM_copy_11.as_mut_ptr(),
            tmp0.as_mut_ptr(),
            resM_0.as_mut_ptr(),
        );
        i0_1 = i0_1.wrapping_add(1);
        i0_1;
    }
    from(n, mu, resM_0.as_mut_ptr(), res);
}
#[inline]
unsafe extern "C" fn exp_vartime(
    mut nBits: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut r2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    precompr2(nBits, n, r2.as_mut_ptr());
    let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
        *n.offset(0 as libc::c_uint as isize),
    );
    exp_vartime_precomp(n, mu, r2.as_mut_ptr(), a, bBits, b, res);
}
#[inline]
unsafe extern "C" fn exp_consttime(
    mut nBits: uint32_t,
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut r2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    precompr2(nBits, n, r2.as_mut_ptr());
    let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
        *n.offset(0 as libc::c_uint as isize),
    );
    exp_consttime_precomp(n, mu, r2.as_mut_ptr(), a, bBits, b, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_exp_vartime(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> bool {
    let mut is_valid_m: uint64_t = exp_check(n, a, bBits, b);
    let mut nBits: uint32_t = (64 as libc::c_uint)
        .wrapping_mul(
            Hacl_Bignum_Lib_bn_get_top_index_u64(4 as libc::c_uint, n) as uint32_t,
        );
    if is_valid_m == 0xffffffffffffffff as libc::c_ulonglong {
        exp_vartime(nBits, n, a, bBits, b, res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffffffffffff as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_exp_consttime(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) -> bool {
    let mut is_valid_m: uint64_t = exp_check(n, a, bBits, b);
    let mut nBits: uint32_t = (64 as libc::c_uint)
        .wrapping_mul(
            Hacl_Bignum_Lib_bn_get_top_index_u64(4 as libc::c_uint, n) as uint32_t,
        );
    if is_valid_m == 0xffffffffffffffff as libc::c_ulonglong {
        exp_consttime(nBits, n, a, bBits, b, res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffffffffffff as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_inv_prime_vartime(
    mut n: *mut uint64_t,
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) -> bool {
    let mut one: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    one[0 as libc::c_uint as usize] = 1 as libc::c_ulonglong;
    let mut bit0: uint64_t = *n.offset(0 as libc::c_uint as isize)
        & 1 as libc::c_ulonglong;
    let mut m0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bit0);
    let mut acc0: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint64_t = FStar_UInt64_eq_mask(one[i as usize], *n.offset(i as isize));
    let mut blt: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq & acc0 | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_0: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_0 & acc0 | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_1: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_1 & acc0 | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint64_t = FStar_UInt64_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_2: uint64_t = !FStar_UInt64_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_2 & acc0 | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m1: uint64_t = acc0;
    let mut m00: uint64_t = m0 & m1;
    let mut bn_zero: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut mask: uint64_t = 0xffffffffffffffff as libc::c_ulonglong;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_0 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_1 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_2 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut mask1: uint64_t = mask;
    let mut res10: uint64_t = mask1;
    let mut m10: uint64_t = res10;
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut beq_3: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_3: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_3 & acc | !beq_3 & blt_3;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_4: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_4: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_4 & acc | !beq_4 & blt_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_5: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_5: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_5 & acc | !beq_5 & blt_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_6: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_6: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_6 & acc | !beq_6 & blt_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m2: uint64_t = acc;
    let mut is_valid_m: uint64_t = m00 & !m10 & m2;
    let mut nBits: uint32_t = (64 as libc::c_uint)
        .wrapping_mul(
            Hacl_Bignum_Lib_bn_get_top_index_u64(4 as libc::c_uint, n) as uint32_t,
        );
    if is_valid_m == 0xffffffffffffffff as libc::c_ulonglong {
        let mut n2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
        let mut c0: uint64_t = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
            0 as libc::c_ulonglong,
            *n.offset(0 as libc::c_uint as isize),
            2 as libc::c_ulonglong,
            n2.as_mut_ptr(),
        );
        let mut a1: *mut uint64_t = n.offset(1 as libc::c_uint as isize);
        let mut res1: *mut uint64_t = n2.as_mut_ptr().offset(1 as libc::c_uint as isize);
        let mut c: uint64_t = c0;
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut t1: uint64_t = *a1.offset(i_2 as isize);
        let mut res_i: *mut uint64_t = res1.offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
            c,
            t1,
            0 as libc::c_ulonglong,
            res_i,
        );
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t1_0: uint64_t = *a1.offset(i_2 as isize);
        let mut res_i_0: *mut uint64_t = res1.offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
            c,
            t1_0,
            0 as libc::c_ulonglong,
            res_i_0,
        );
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t1_1: uint64_t = *a1.offset(i_2 as isize);
        let mut res_i_1: *mut uint64_t = res1.offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
            c,
            t1_1,
            0 as libc::c_ulonglong,
            res_i_1,
        );
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c1: uint64_t = c;
        let mut c2: uint64_t = c1;
        exp_vartime(nBits, n, a, 256 as libc::c_uint, n2.as_mut_ptr(), res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (4 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffffffffffff as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mont_ctx_init(
    mut n: *mut uint64_t,
) -> *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 {
    let mut r2: *mut uint64_t = calloc(
        4 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    let mut n1: *mut uint64_t = calloc(
        4 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    let mut r21: *mut uint64_t = r2;
    let mut n11: *mut uint64_t = n1;
    memcpy(
        n11 as *mut libc::c_void,
        n as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut nBits: uint32_t = (64 as libc::c_uint)
        .wrapping_mul(
            Hacl_Bignum_Lib_bn_get_top_index_u64(4 as libc::c_uint, n) as uint32_t,
        );
    precompr2(nBits, n, r21);
    let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
        *n.offset(0 as libc::c_uint as isize),
    );
    let mut res: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 = {
        let mut init = Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_s {
            len: 4 as libc::c_uint,
            n: n11,
            mu: mu,
            r2: r21,
        };
        init
    };
    let mut buf: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 = malloc(
        ::core::mem::size_of::<Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64>()
            as libc::c_ulong,
    ) as *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64;
    *buf.offset(0 as libc::c_uint as isize) = res;
    return buf;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mont_ctx_free(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64,
) {
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 = *k;
    let mut n: *mut uint64_t = uu____0.n;
    let mut r2: *mut uint64_t = uu____0.r2;
    free(n as *mut libc::c_void);
    free(r2 as *mut libc::c_void);
    free(k as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64,
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut n: *mut uint64_t = (*k).n;
    let mut mu: uint64_t = (*k).mu;
    let mut r2: *mut uint64_t = (*k).r2;
    bn_slow_precomp(n, mu, r2, a, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_exp_vartime_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut n: *mut uint64_t = (*k).n;
    let mut mu: uint64_t = (*k).mu;
    let mut r2: *mut uint64_t = (*k).r2;
    exp_vartime_precomp(n, mu, r2, a, bBits, b, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_exp_consttime_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64,
    mut a: *mut uint64_t,
    mut bBits: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut n: *mut uint64_t = (*k).n;
    let mut mu: uint64_t = (*k).mu;
    let mut r2: *mut uint64_t = (*k).r2;
    exp_consttime_precomp(n, mu, r2, a, bBits, b, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_mod_inv_prime_vartime_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64,
    mut a: *mut uint64_t,
    mut res: *mut uint64_t,
) {
    let mut n: *mut uint64_t = (*k).n;
    let mut mu: uint64_t = (*k).mu;
    let mut r2: *mut uint64_t = (*k).r2;
    let mut n2: [uint64_t; 4] = [0 as libc::c_uint as uint64_t, 0, 0, 0];
    let mut c0: uint64_t = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
        0 as libc::c_ulonglong,
        *n.offset(0 as libc::c_uint as isize),
        2 as libc::c_ulonglong,
        n2.as_mut_ptr(),
    );
    let mut a1: *mut uint64_t = n.offset(1 as libc::c_uint as isize);
    let mut res1: *mut uint64_t = n2.as_mut_ptr().offset(1 as libc::c_uint as isize);
    let mut c: uint64_t = c0;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t1: uint64_t = *a1.offset(i as isize);
    let mut res_i: *mut uint64_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
        c,
        t1,
        0 as libc::c_ulonglong,
        res_i,
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint64_t = *a1.offset(i as isize);
    let mut res_i_0: *mut uint64_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
        c,
        t1_0,
        0 as libc::c_ulonglong,
        res_i_0,
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_1: uint64_t = *a1.offset(i as isize);
    let mut res_i_1: *mut uint64_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_128_sub_borrow_u64(
        c,
        t1_1,
        0 as libc::c_ulonglong,
        res_i_1,
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c1: uint64_t = c;
    let mut c2: uint64_t = c1;
    exp_vartime_precomp(n, mu, r2, a, 256 as libc::c_uint, n2.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_new_bn_from_bytes_be(
    mut len: uint32_t,
    mut b: *mut uint8_t,
) -> *mut uint64_t {
    if len == 0 as libc::c_uint
        || !(len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) <= 536870911 as libc::c_uint)
    {
        return 0 as *mut uint64_t;
    }
    if len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256.c\0" as *const u8 as *const libc::c_char,
            1309 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut res: *mut uint64_t = calloc(
        len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    if res.is_null() {
        return res;
    }
    let mut res1: *mut uint64_t = res;
    let mut res2: *mut uint64_t = res1;
    let mut bnLen: uint32_t = len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut tmpLen: uint32_t = (8 as libc::c_uint).wrapping_mul(bnLen);
    if tmpLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256.c\0" as *const u8 as *const libc::c_char,
            1319 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = tmpLen as usize;
    let mut tmp: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (tmpLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        tmp.as_mut_ptr().offset(tmpLen as isize).offset(-(len as isize))
            as *mut libc::c_void,
        b as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < bnLen {
        let mut u: uint64_t = if 0 != 0 {
            (load64(
                tmp
                    .as_mut_ptr()
                    .offset(
                        bnLen
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(8 as libc::c_uint) as isize,
                    ),
            ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                load64(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(8 as libc::c_uint) as isize,
                        ),
                ),
            )
        };
        let mut x: uint64_t = u;
        let mut os: *mut uint64_t = res2;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    return res2;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_new_bn_from_bytes_le(
    mut len: uint32_t,
    mut b: *mut uint8_t,
) -> *mut uint64_t {
    if len == 0 as libc::c_uint
        || !(len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) <= 536870911 as libc::c_uint)
    {
        return 0 as *mut uint64_t;
    }
    if len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256.c\0" as *const u8 as *const libc::c_char,
            1350 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut res: *mut uint64_t = calloc(
        len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    if res.is_null() {
        return res;
    }
    let mut res1: *mut uint64_t = res;
    let mut res2: *mut uint64_t = res1;
    let mut bnLen: uint32_t = len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut tmpLen: uint32_t = (8 as libc::c_uint).wrapping_mul(bnLen);
    if tmpLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256.c\0" as *const u8 as *const libc::c_char,
            1360 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = tmpLen as usize;
    let mut tmp: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        tmp.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (tmpLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        tmp.as_mut_ptr() as *mut libc::c_void,
        b as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i
        < len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint)
    {
        let mut bj: *mut uint8_t = tmp
            .as_mut_ptr()
            .offset(i.wrapping_mul(8 as libc::c_uint) as isize);
        let mut u: uint64_t = load64(bj);
        let mut r1: uint64_t = u;
        let mut x: uint64_t = r1;
        let mut os: *mut uint64_t = res2;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    return res2;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_bn_to_bytes_be(
    mut b: *mut uint64_t,
    mut res: *mut uint8_t,
) {
    let mut tmp: [uint8_t; 32] = [
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
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (4 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (*b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(
                *b
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_bn_to_bytes_le(
    mut b: *mut uint64_t,
    mut res: *mut uint8_t,
) {
    let mut tmp: [uint8_t; 32] = [
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
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        res.offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_lt_mask(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
) -> uint64_t {
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq & acc | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_0: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_0 & acc | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_1: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_1 & acc | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_2: uint64_t = !FStar_UInt64_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_2 & acc | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    return acc;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_eq_mask(
    mut a: *mut uint64_t,
    mut b: *mut uint64_t,
) -> uint64_t {
    let mut mask: uint64_t = 0xffffffffffffffff as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_0 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_1 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint64_t = FStar_UInt64_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_2 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut mask1: uint64_t = mask;
    return mask1;
}
