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
    fn Hacl_Bignum_ModInvLimb_mod_inv_uint32(n0: uint32_t) -> uint32_t;
}
pub type __uint32_t = libc::c_uint;
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s {
    pub len: uint32_t,
    pub n: *mut uint32_t,
    pub mu: uint32_t,
    pub r2: *mut uint32_t,
}
pub type Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s;
#[inline]
unsafe extern "C" fn _OSSwapInt32(mut _data: __uint32_t) -> __uint32_t {
    _data = _data.swap_bytes();
    return _data;
}
#[inline]
unsafe extern "C" fn load32(mut b: *mut uint8_t) -> uint32_t {
    let mut x: uint32_t = 0;
    memcpy(
        &mut x as *mut uint32_t as *mut libc::c_void,
        b as *const libc::c_void,
        4 as libc::c_int as libc::c_ulong,
    );
    return x;
}
#[inline]
unsafe extern "C" fn store32(mut b: *mut uint8_t, mut i: uint32_t) {
    memcpy(
        b as *mut libc::c_void,
        &mut i as *mut uint32_t as *const libc::c_void,
        4 as libc::c_int as libc::c_ulong,
    );
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
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_top_index_u32(
    mut len: uint32_t,
    mut b: *mut uint32_t,
) -> uint32_t {
    let mut priv_0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut mask: uint32_t = FStar_UInt32_eq_mask(
            *b.offset(i as isize),
            0 as libc::c_uint,
        );
        priv_0 = mask & priv_0 | !mask & i;
        i = i.wrapping_add(1);
        i;
    }
    return priv_0;
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
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_add(
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) -> uint32_t {
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1, t20, res_i0);
    let mut t10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t10, t21, res_i1);
    let mut t11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t11, t22, res_i2);
    let mut t12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12, t2, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20_0: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12_0, t2_0, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    return c;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_sub(
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) -> uint32_t {
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1, t20, res_i0);
    let mut t10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10, t21, res_i1);
    let mut t11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11, t22, res_i2);
    let mut t12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12, t2, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20_0: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12_0, t2_0, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    return c;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_add_mod(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t1, t20, res_i0);
    let mut t10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t10, t21, res_i1);
    let mut t11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t11, t22, res_i2);
    let mut t12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t12, t2, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20_0: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, t12_0, t2_0, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c00: uint32_t = c0;
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut t1_1: uint32_t = *res.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut t20_1: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_1, t20_1, res_i0_1);
    let mut t10_1: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut t21_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10_1, t21_1, res_i1_1);
    let mut t11_1: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut t22_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11_1, t22_1, res_i2_1);
    let mut t12_1: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut t2_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12_1, t2_1, res_i_1);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_2: uint32_t = *res.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut t20_2: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_2, t20_2, res_i0_2);
    let mut t10_2: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut t21_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10_2, t21_2, res_i1_2);
    let mut t11_2: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut t22_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11_2, t22_2, res_i2_2);
    let mut t12_2: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut t2_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12_2, t2_2, res_i_2);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c1: uint32_t = c;
    let mut c2: uint32_t = c00.wrapping_sub(c1);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os: *mut uint32_t = res;
    *os.offset(i_1 as isize) = x;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_0: *mut uint32_t = res;
    *os_0.offset(i_1 as isize) = x_0;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_1: *mut uint32_t = res;
    *os_1.offset(i_1 as isize) = x_1;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_2: *mut uint32_t = res;
    *os_2.offset(i_1 as isize) = x_2;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_3: *mut uint32_t = res;
    *os_3.offset(i_1 as isize) = x_3;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_4: *mut uint32_t = res;
    *os_4.offset(i_1 as isize) = x_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_5: *mut uint32_t = res;
    *os_5.offset(i_1 as isize) = x_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = c2 & *res.offset(i_1 as isize) | !c2 & tmp[i_1 as usize];
    let mut os_6: *mut uint32_t = res;
    *os_6.offset(i_1 as isize) = x_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_sub_mod(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut t1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t1, t20, res_i0);
    let mut t10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t10, t21, res_i1);
    let mut t11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t11, t22, res_i2);
    let mut t12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t12, t2, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut t20_0: uint32_t = *b.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t1_0, t20_0, res_i0_0);
    let mut t10_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut t21_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t10_0, t21_0, res_i1_0);
    let mut t11_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut t22_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t11_0, t22_0, res_i2_0);
    let mut t12_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut t2_0: uint32_t = *b
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c0 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c0, t12_0, t2_0, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c00: uint32_t = c0;
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut t1_1: uint32_t = *res.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut t20_1: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1_1, t20_1, res_i0_1);
    let mut t10_1: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut t21_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t10_1, t21_1, res_i1_1);
    let mut t11_1: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut t22_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t11_1, t22_1, res_i2_1);
    let mut t12_1: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut t2_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_1: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12_1, t2_1, res_i_1);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_2: uint32_t = *res.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut t20_2: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t1_2, t20_2, res_i0_2);
    let mut t10_2: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut t21_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t10_2, t21_2, res_i1_2);
    let mut t11_2: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut t22_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t11_2, t22_2, res_i2_2);
    let mut t12_2: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut t2_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_2: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_add_carry_u32(c, t12_2, t2_2, res_i_2);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c1: uint32_t = c;
    let mut c2: uint32_t = (0 as libc::c_uint).wrapping_sub(c00);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os: *mut uint32_t = res;
    *os.offset(i_1 as isize) = x;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_0: *mut uint32_t = res;
    *os_0.offset(i_1 as isize) = x_0;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_1: *mut uint32_t = res;
    *os_1.offset(i_1 as isize) = x_1;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_2: *mut uint32_t = res;
    *os_2.offset(i_1 as isize) = x_2;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_3: *mut uint32_t = res;
    *os_3.offset(i_1 as isize) = x_3;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_4: *mut uint32_t = res;
    *os_4.offset(i_1 as isize) = x_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_5: *mut uint32_t = res;
    *os_5.offset(i_1 as isize) = x_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = c2 & tmp[i_1 as usize] | !c2 & *res.offset(i_1 as isize);
    let mut os_6: *mut uint32_t = res;
    *os_6.offset(i_1 as isize) = x_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mul(
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut bj: uint32_t = *b.offset(i0 as isize);
    let mut res_j: *mut uint32_t = res.offset(i0 as isize);
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut a_i: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, bj, c, res_i0);
    let mut a_i0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, bj, c, res_i1);
    let mut a_i1: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, bj, c, res_i2);
    let mut a_i2: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, bj, c, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_0: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, bj, c, res_i0_0);
    let mut a_i0_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_0, bj, c, res_i1_0);
    let mut a_i1_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_0, bj, c, res_i2_0);
    let mut a_i2_0: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res_j
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_0, bj, c, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r: uint32_t = c;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: uint32_t = *b.offset(i0 as isize);
    let mut res_j_0: *mut uint32_t = res.offset(i0 as isize);
    let mut c_0: uint32_t = 0 as libc::c_uint;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut a_i_1: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_1: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_1, bj_0, c_0, res_i0_1);
    let mut a_i0_1: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_1: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_1, bj_0, c_0, res_i1_1);
    let mut a_i1_1: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_1: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_1, bj_0, c_0, res_i2_1);
    let mut a_i2_1: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_1: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_1, bj_0, c_0, res_i_1);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_2: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_2: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_2, bj_0, c_0, res_i0_2);
    let mut a_i0_2: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_2: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_2, bj_0, c_0, res_i1_2);
    let mut a_i1_2: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_2: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_2, bj_0, c_0, res_i2_2);
    let mut a_i2_2: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_2: *mut uint32_t = res_j_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_2, bj_0, c_0, res_i_2);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_0: uint32_t = c_0;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: uint32_t = *b.offset(i0 as isize);
    let mut res_j_1: *mut uint32_t = res.offset(i0 as isize);
    let mut c_1: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut a_i_3: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    let mut res_i0_3: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_3, bj_1, c_1, res_i0_3);
    let mut a_i0_3: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_3: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(1 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_3, bj_1, c_1, res_i1_3);
    let mut a_i1_3: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_3: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(2 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_3, bj_1, c_1, res_i2_3);
    let mut a_i2_3: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_3: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(3 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_3, bj_1, c_1, res_i_3);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_4: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    let mut res_i0_4: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_4, bj_1, c_1, res_i0_4);
    let mut a_i0_4: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_4: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(1 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_4, bj_1, c_1, res_i1_4);
    let mut a_i1_4: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_4: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(2 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_4, bj_1, c_1, res_i2_4);
    let mut a_i2_4: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_4: *mut uint32_t = res_j_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(3 as libc::c_uint as isize);
    c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_4, bj_1, c_1, res_i_4);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_1: uint32_t = c_1;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_1;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: uint32_t = *b.offset(i0 as isize);
    let mut res_j_2: *mut uint32_t = res.offset(i0 as isize);
    let mut c_2: uint32_t = 0 as libc::c_uint;
    let mut i_2: uint32_t = 0 as libc::c_uint;
    let mut a_i_5: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    let mut res_i0_5: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_5, bj_2, c_2, res_i0_5);
    let mut a_i0_5: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_5: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(1 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_5, bj_2, c_2, res_i1_5);
    let mut a_i1_5: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_5: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(2 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_5, bj_2, c_2, res_i2_5);
    let mut a_i2_5: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_5: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(3 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_5, bj_2, c_2, res_i_5);
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_6: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    let mut res_i0_6: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_6, bj_2, c_2, res_i0_6);
    let mut a_i0_6: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_6: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(1 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_6, bj_2, c_2, res_i1_6);
    let mut a_i1_6: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_6: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(2 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_6, bj_2, c_2, res_i2_6);
    let mut a_i2_6: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_6: *mut uint32_t = res_j_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(3 as libc::c_uint as isize);
    c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_6, bj_2, c_2, res_i_6);
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_2: uint32_t = c_2;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_2;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: uint32_t = *b.offset(i0 as isize);
    let mut res_j_3: *mut uint32_t = res.offset(i0 as isize);
    let mut c_3: uint32_t = 0 as libc::c_uint;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    let mut a_i_7: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    let mut res_i0_7: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_7, bj_3, c_3, res_i0_7);
    let mut a_i0_7: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_7: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(1 as libc::c_uint as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_7, bj_3, c_3, res_i1_7);
    let mut a_i1_7: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_7: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(2 as libc::c_uint as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_7, bj_3, c_3, res_i2_7);
    let mut a_i2_7: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_7: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(3 as libc::c_uint as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_7, bj_3, c_3, res_i_7);
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_8: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    let mut res_i0_8: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_8, bj_3, c_3, res_i0_8);
    let mut a_i0_8: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_8: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(1 as libc::c_uint as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_8, bj_3, c_3, res_i1_8);
    let mut a_i1_8: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_8: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(2 as libc::c_uint as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_8, bj_3, c_3, res_i2_8);
    let mut a_i2_8: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_8: *mut uint32_t = res_j_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(3 as libc::c_uint as isize);
    c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_8, bj_3, c_3, res_i_8);
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_3: uint32_t = c_3;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_3;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: uint32_t = *b.offset(i0 as isize);
    let mut res_j_4: *mut uint32_t = res.offset(i0 as isize);
    let mut c_4: uint32_t = 0 as libc::c_uint;
    let mut i_4: uint32_t = 0 as libc::c_uint;
    let mut a_i_9: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    let mut res_i0_9: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_9, bj_4, c_4, res_i0_9);
    let mut a_i0_9: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_9: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(1 as libc::c_uint as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_9, bj_4, c_4, res_i1_9);
    let mut a_i1_9: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_9: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(2 as libc::c_uint as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_9, bj_4, c_4, res_i2_9);
    let mut a_i2_9: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_9: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(3 as libc::c_uint as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_9, bj_4, c_4, res_i_9);
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_10: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    let mut res_i0_10: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_10, bj_4, c_4, res_i0_10);
    let mut a_i0_10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_10: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(1 as libc::c_uint as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_10, bj_4, c_4, res_i1_10);
    let mut a_i1_10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_10: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(2 as libc::c_uint as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_10, bj_4, c_4, res_i2_10);
    let mut a_i2_10: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_10: *mut uint32_t = res_j_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(3 as libc::c_uint as isize);
    c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_10, bj_4, c_4, res_i_10);
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_4: uint32_t = c_4;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_4;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: uint32_t = *b.offset(i0 as isize);
    let mut res_j_5: *mut uint32_t = res.offset(i0 as isize);
    let mut c_5: uint32_t = 0 as libc::c_uint;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    let mut a_i_11: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    let mut res_i0_11: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_11, bj_5, c_5, res_i0_11);
    let mut a_i0_11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_11: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(1 as libc::c_uint as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_11, bj_5, c_5, res_i1_11);
    let mut a_i1_11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_11: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(2 as libc::c_uint as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_11, bj_5, c_5, res_i2_11);
    let mut a_i2_11: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_11: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(3 as libc::c_uint as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_11, bj_5, c_5, res_i_11);
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_12: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    let mut res_i0_12: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_12, bj_5, c_5, res_i0_12);
    let mut a_i0_12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_12: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(1 as libc::c_uint as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_12, bj_5, c_5, res_i1_12);
    let mut a_i1_12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_12: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(2 as libc::c_uint as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_12, bj_5, c_5, res_i2_12);
    let mut a_i2_12: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_12: *mut uint32_t = res_j_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(3 as libc::c_uint as isize);
    c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_12, bj_5, c_5, res_i_12);
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_5: uint32_t = c_5;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_5;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: uint32_t = *b.offset(i0 as isize);
    let mut res_j_6: *mut uint32_t = res.offset(i0 as isize);
    let mut c_6: uint32_t = 0 as libc::c_uint;
    let mut i_6: uint32_t = 0 as libc::c_uint;
    let mut a_i_13: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    let mut res_i0_13: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_13, bj_6, c_6, res_i0_13);
    let mut a_i0_13: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_13: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(1 as libc::c_uint as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_13, bj_6, c_6, res_i1_13);
    let mut a_i1_13: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_13: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(2 as libc::c_uint as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_13, bj_6, c_6, res_i2_13);
    let mut a_i2_13: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_13: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(3 as libc::c_uint as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_13, bj_6, c_6, res_i_13);
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_14: uint32_t = *a.offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    let mut res_i0_14: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_14, bj_6, c_6, res_i0_14);
    let mut a_i0_14: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_14: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(1 as libc::c_uint as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_14, bj_6, c_6, res_i1_14);
    let mut a_i1_14: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_14: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(2 as libc::c_uint as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_14, bj_6, c_6, res_i2_14);
    let mut a_i2_14: uint32_t = *a
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_14: *mut uint32_t = res_j_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(3 as libc::c_uint as isize);
    c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_14, bj_6, c_6, res_i_14);
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_6: uint32_t = c_6;
    *res.offset((8 as libc::c_uint).wrapping_add(i0) as isize) = r_6;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_sqr(
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut a_j: uint32_t = *a.offset(i0 as isize);
    let mut ab: *mut uint32_t = a;
    let mut res_j: *mut uint32_t = res.offset(i0 as isize);
    let mut c: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i: uint32_t = *ab.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
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
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_0: uint32_t = *a.offset(i0 as isize);
    let mut ab_0: *mut uint32_t = a;
    let mut res_j_0: *mut uint32_t = res.offset(i0 as isize);
    let mut c_0: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_1: uint32_t = *ab_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        let mut res_i0_0: *mut uint32_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_1, a_j_0, c_0, res_i0_0);
        let mut a_i0_0: uint32_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_0: *mut uint32_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(1 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_0, a_j_0, c_0, res_i1_0);
        let mut a_i1_0: uint32_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_0: *mut uint32_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(2 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_0, a_j_0, c_0, res_i2_0);
        let mut a_i2_0: uint32_t = *ab_0
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_1: *mut uint32_t = res_j_0
            .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
            .offset(3 as libc::c_uint as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_0, a_j_0, c_0, res_i_1);
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut i_2: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_2 < i0 {
        let mut a_i_2: uint32_t = *ab_0.offset(i_2 as isize);
        let mut res_i_2: *mut uint32_t = res_j_0.offset(i_2 as isize);
        c_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_2, a_j_0, c_0, res_i_2);
        i_2 = i_2.wrapping_add(1);
        i_2;
    }
    let mut r_0: uint32_t = c_0;
    *res.offset(i0.wrapping_add(i0) as isize) = r_0;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_1: uint32_t = *a.offset(i0 as isize);
    let mut ab_1: *mut uint32_t = a;
    let mut res_j_1: *mut uint32_t = res.offset(i0 as isize);
    let mut c_1: uint32_t = 0 as libc::c_uint;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    while i_3 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_3: uint32_t = *ab_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
        let mut res_i0_1: *mut uint32_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_3, a_j_1, c_1, res_i0_1);
        let mut a_i0_1: uint32_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_1: *mut uint32_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(1 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_1, a_j_1, c_1, res_i1_1);
        let mut a_i1_1: uint32_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_1: *mut uint32_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(2 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_1, a_j_1, c_1, res_i2_1);
        let mut a_i2_1: uint32_t = *ab_1
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_3: *mut uint32_t = res_j_1
            .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
            .offset(3 as libc::c_uint as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_1, a_j_1, c_1, res_i_3);
        i_3 = i_3.wrapping_add(1);
        i_3;
    }
    let mut i_4: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_4 < i0 {
        let mut a_i_4: uint32_t = *ab_1.offset(i_4 as isize);
        let mut res_i_4: *mut uint32_t = res_j_1.offset(i_4 as isize);
        c_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_4, a_j_1, c_1, res_i_4);
        i_4 = i_4.wrapping_add(1);
        i_4;
    }
    let mut r_1: uint32_t = c_1;
    *res.offset(i0.wrapping_add(i0) as isize) = r_1;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_2: uint32_t = *a.offset(i0 as isize);
    let mut ab_2: *mut uint32_t = a;
    let mut res_j_2: *mut uint32_t = res.offset(i0 as isize);
    let mut c_2: uint32_t = 0 as libc::c_uint;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    while i_5 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_5: uint32_t = *ab_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
        let mut res_i0_2: *mut uint32_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_5, a_j_2, c_2, res_i0_2);
        let mut a_i0_2: uint32_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_2: *mut uint32_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(1 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_2, a_j_2, c_2, res_i1_2);
        let mut a_i1_2: uint32_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_2: *mut uint32_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(2 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_2, a_j_2, c_2, res_i2_2);
        let mut a_i2_2: uint32_t = *ab_2
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_5: *mut uint32_t = res_j_2
            .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
            .offset(3 as libc::c_uint as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_2, a_j_2, c_2, res_i_5);
        i_5 = i_5.wrapping_add(1);
        i_5;
    }
    let mut i_6: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_6 < i0 {
        let mut a_i_6: uint32_t = *ab_2.offset(i_6 as isize);
        let mut res_i_6: *mut uint32_t = res_j_2.offset(i_6 as isize);
        c_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_6, a_j_2, c_2, res_i_6);
        i_6 = i_6.wrapping_add(1);
        i_6;
    }
    let mut r_2: uint32_t = c_2;
    *res.offset(i0.wrapping_add(i0) as isize) = r_2;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_3: uint32_t = *a.offset(i0 as isize);
    let mut ab_3: *mut uint32_t = a;
    let mut res_j_3: *mut uint32_t = res.offset(i0 as isize);
    let mut c_3: uint32_t = 0 as libc::c_uint;
    let mut i_7: uint32_t = 0 as libc::c_uint;
    while i_7 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_7: uint32_t = *ab_3
            .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
        let mut res_i0_3: *mut uint32_t = res_j_3
            .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
        c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_7, a_j_3, c_3, res_i0_3);
        let mut a_i0_3: uint32_t = *ab_3
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_3: *mut uint32_t = res_j_3
            .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
            .offset(1 as libc::c_uint as isize);
        c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_3, a_j_3, c_3, res_i1_3);
        let mut a_i1_3: uint32_t = *ab_3
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_3: *mut uint32_t = res_j_3
            .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
            .offset(2 as libc::c_uint as isize);
        c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_3, a_j_3, c_3, res_i2_3);
        let mut a_i2_3: uint32_t = *ab_3
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_7: *mut uint32_t = res_j_3
            .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
            .offset(3 as libc::c_uint as isize);
        c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_3, a_j_3, c_3, res_i_7);
        i_7 = i_7.wrapping_add(1);
        i_7;
    }
    let mut i_8: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_8 < i0 {
        let mut a_i_8: uint32_t = *ab_3.offset(i_8 as isize);
        let mut res_i_8: *mut uint32_t = res_j_3.offset(i_8 as isize);
        c_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_8, a_j_3, c_3, res_i_8);
        i_8 = i_8.wrapping_add(1);
        i_8;
    }
    let mut r_3: uint32_t = c_3;
    *res.offset(i0.wrapping_add(i0) as isize) = r_3;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_4: uint32_t = *a.offset(i0 as isize);
    let mut ab_4: *mut uint32_t = a;
    let mut res_j_4: *mut uint32_t = res.offset(i0 as isize);
    let mut c_4: uint32_t = 0 as libc::c_uint;
    let mut i_9: uint32_t = 0 as libc::c_uint;
    while i_9 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_9: uint32_t = *ab_4
            .offset((4 as libc::c_uint).wrapping_mul(i_9) as isize);
        let mut res_i0_4: *mut uint32_t = res_j_4
            .offset((4 as libc::c_uint).wrapping_mul(i_9) as isize);
        c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_9, a_j_4, c_4, res_i0_4);
        let mut a_i0_4: uint32_t = *ab_4
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_9).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_4: *mut uint32_t = res_j_4
            .offset((4 as libc::c_uint).wrapping_mul(i_9) as isize)
            .offset(1 as libc::c_uint as isize);
        c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_4, a_j_4, c_4, res_i1_4);
        let mut a_i1_4: uint32_t = *ab_4
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_9).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_4: *mut uint32_t = res_j_4
            .offset((4 as libc::c_uint).wrapping_mul(i_9) as isize)
            .offset(2 as libc::c_uint as isize);
        c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_4, a_j_4, c_4, res_i2_4);
        let mut a_i2_4: uint32_t = *ab_4
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_9).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_9: *mut uint32_t = res_j_4
            .offset((4 as libc::c_uint).wrapping_mul(i_9) as isize)
            .offset(3 as libc::c_uint as isize);
        c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_4, a_j_4, c_4, res_i_9);
        i_9 = i_9.wrapping_add(1);
        i_9;
    }
    let mut i_10: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_10 < i0 {
        let mut a_i_10: uint32_t = *ab_4.offset(i_10 as isize);
        let mut res_i_10: *mut uint32_t = res_j_4.offset(i_10 as isize);
        c_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_10, a_j_4, c_4, res_i_10);
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    let mut r_4: uint32_t = c_4;
    *res.offset(i0.wrapping_add(i0) as isize) = r_4;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_5: uint32_t = *a.offset(i0 as isize);
    let mut ab_5: *mut uint32_t = a;
    let mut res_j_5: *mut uint32_t = res.offset(i0 as isize);
    let mut c_5: uint32_t = 0 as libc::c_uint;
    let mut i_11: uint32_t = 0 as libc::c_uint;
    while i_11 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_11: uint32_t = *ab_5
            .offset((4 as libc::c_uint).wrapping_mul(i_11) as isize);
        let mut res_i0_5: *mut uint32_t = res_j_5
            .offset((4 as libc::c_uint).wrapping_mul(i_11) as isize);
        c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_11, a_j_5, c_5, res_i0_5);
        let mut a_i0_5: uint32_t = *ab_5
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_11).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_5: *mut uint32_t = res_j_5
            .offset((4 as libc::c_uint).wrapping_mul(i_11) as isize)
            .offset(1 as libc::c_uint as isize);
        c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_5, a_j_5, c_5, res_i1_5);
        let mut a_i1_5: uint32_t = *ab_5
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_11).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_5: *mut uint32_t = res_j_5
            .offset((4 as libc::c_uint).wrapping_mul(i_11) as isize)
            .offset(2 as libc::c_uint as isize);
        c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_5, a_j_5, c_5, res_i2_5);
        let mut a_i2_5: uint32_t = *ab_5
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_11).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_11: *mut uint32_t = res_j_5
            .offset((4 as libc::c_uint).wrapping_mul(i_11) as isize)
            .offset(3 as libc::c_uint as isize);
        c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_5, a_j_5, c_5, res_i_11);
        i_11 = i_11.wrapping_add(1);
        i_11;
    }
    let mut i_12: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_12 < i0 {
        let mut a_i_12: uint32_t = *ab_5.offset(i_12 as isize);
        let mut res_i_12: *mut uint32_t = res_j_5.offset(i_12 as isize);
        c_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_12, a_j_5, c_5, res_i_12);
        i_12 = i_12.wrapping_add(1);
        i_12;
    }
    let mut r_5: uint32_t = c_5;
    *res.offset(i0.wrapping_add(i0) as isize) = r_5;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_j_6: uint32_t = *a.offset(i0 as isize);
    let mut ab_6: *mut uint32_t = a;
    let mut res_j_6: *mut uint32_t = res.offset(i0 as isize);
    let mut c_6: uint32_t = 0 as libc::c_uint;
    let mut i_13: uint32_t = 0 as libc::c_uint;
    while i_13 < i0.wrapping_div(4 as libc::c_uint) {
        let mut a_i_13: uint32_t = *ab_6
            .offset((4 as libc::c_uint).wrapping_mul(i_13) as isize);
        let mut res_i0_6: *mut uint32_t = res_j_6
            .offset((4 as libc::c_uint).wrapping_mul(i_13) as isize);
        c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_13, a_j_6, c_6, res_i0_6);
        let mut a_i0_6: uint32_t = *ab_6
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_13).wrapping_add(1 as libc::c_uint)
                    as isize,
            );
        let mut res_i1_6: *mut uint32_t = res_j_6
            .offset((4 as libc::c_uint).wrapping_mul(i_13) as isize)
            .offset(1 as libc::c_uint as isize);
        c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_6, a_j_6, c_6, res_i1_6);
        let mut a_i1_6: uint32_t = *ab_6
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_13).wrapping_add(2 as libc::c_uint)
                    as isize,
            );
        let mut res_i2_6: *mut uint32_t = res_j_6
            .offset((4 as libc::c_uint).wrapping_mul(i_13) as isize)
            .offset(2 as libc::c_uint as isize);
        c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_6, a_j_6, c_6, res_i2_6);
        let mut a_i2_6: uint32_t = *ab_6
            .offset(
                (4 as libc::c_uint).wrapping_mul(i_13).wrapping_add(3 as libc::c_uint)
                    as isize,
            );
        let mut res_i_13: *mut uint32_t = res_j_6
            .offset((4 as libc::c_uint).wrapping_mul(i_13) as isize)
            .offset(3 as libc::c_uint as isize);
        c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_6, a_j_6, c_6, res_i_13);
        i_13 = i_13.wrapping_add(1);
        i_13;
    }
    let mut i_14: uint32_t = i0
        .wrapping_div(4 as libc::c_uint)
        .wrapping_mul(4 as libc::c_uint);
    while i_14 < i0 {
        let mut a_i_14: uint32_t = *ab_6.offset(i_14 as isize);
        let mut res_i_14: *mut uint32_t = res_j_6.offset(i_14 as isize);
        c_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_14, a_j_6, c_6, res_i_14);
        i_14 = i_14.wrapping_add(1);
        i_14;
    }
    let mut r_6: uint32_t = c_6;
    *res.offset(i0.wrapping_add(i0) as isize) = r_6;
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_copy0: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b_copy0: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
        a_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy0.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut r_7: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(
        16 as libc::c_uint,
        a_copy0.as_mut_ptr(),
        b_copy0.as_mut_ptr(),
        res,
    );
    let mut c0: uint32_t = r_7;
    let mut tmp: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut i_15: uint32_t = 0 as libc::c_uint;
    let mut res1: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi: uint32_t = (res1 >> 32 as libc::c_uint) as uint32_t;
    let mut lo: uint32_t = res1 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_0: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_0: uint32_t = (res1_0 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_0: uint32_t = res1_0 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_0;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_0;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_1: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_1: uint32_t = (res1_1 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_1: uint32_t = res1_1 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_1;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_1;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_2: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_2: uint32_t = (res1_2 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_2: uint32_t = res1_2 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_2;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_2;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_3: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_3: uint32_t = (res1_3 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_3: uint32_t = res1_3 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_3;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_3;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_4: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_4: uint32_t = (res1_4 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_4: uint32_t = res1_4 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_4;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_4;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_5: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_5: uint32_t = (res1_5 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_5: uint32_t = res1_5 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_5;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_5;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut res1_6: uint64_t = *a.offset(i_15 as isize) as uint64_t
        * *a.offset(i_15 as isize) as uint64_t;
    let mut hi_6: uint32_t = (res1_6 >> 32 as libc::c_uint) as uint32_t;
    let mut lo_6: uint32_t = res1_6 as uint32_t;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15) as usize] = lo_6;
    tmp[(2 as libc::c_uint).wrapping_mul(i_15).wrapping_add(1 as libc::c_uint)
        as usize] = hi_6;
    i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
        as uint32_t;
    let mut a_copy: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b_copy: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
        a_copy.as_mut_ptr() as *mut libc::c_void,
        res as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        tmp.as_mut_ptr() as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut r0: uint32_t = Hacl_Bignum_Addition_bn_add_eq_len_u32(
        16 as libc::c_uint,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        res,
    );
    let mut c1: uint32_t = r0;
}
#[inline]
unsafe extern "C" fn precompr2(
    mut nBits: uint32_t,
    mut n: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    memset(
        res as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = nBits.wrapping_div(32 as libc::c_uint);
    let mut j: uint32_t = nBits.wrapping_rem(32 as libc::c_uint);
    *res.offset(i as isize) = *res.offset(i as isize) | (1 as libc::c_uint) << j;
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (512 as libc::c_uint).wrapping_sub(nBits) {
        let mut a_copy: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        let mut b_copy: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            a_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            b_copy.as_mut_ptr() as *mut libc::c_void,
            res as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        Hacl_Bignum256_32_add_mod(n, a_copy.as_mut_ptr(), b_copy.as_mut_ptr(), res);
        i0 = i0.wrapping_add(1);
        i0;
    }
}
#[inline]
unsafe extern "C" fn reduction(
    mut n: *mut uint32_t,
    mut nInv: uint32_t,
    mut c: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut qj: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0: *mut uint32_t = c.offset(i0 as isize);
    let mut c1: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut a_i: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
    let mut a_i0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
    let mut a_i1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
    let mut a_i2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_0: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, qj, c1, res_i0_0);
    let mut a_i0_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_0, qj, c1, res_i1_0);
    let mut a_i1_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_0, qj, c1, res_i2_0);
    let mut a_i2_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_0, qj, c1, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r: uint32_t = c1;
    let mut c10: uint32_t = r;
    let mut res_j: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_0: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_0: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_0: uint32_t = 0 as libc::c_uint;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut a_i_1: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_1, qj_0, c1_0, res_i0_1);
    let mut a_i0_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_1, qj_0, c1_0, res_i1_1);
    let mut a_i1_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_1, qj_0, c1_0, res_i2_1);
    let mut a_i2_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_1, qj_0, c1_0, res_i_1);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_2: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_2, qj_0, c1_0, res_i0_2);
    let mut a_i0_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_2, qj_0, c1_0, res_i1_2);
    let mut a_i1_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_2, qj_0, c1_0, res_i2_2);
    let mut a_i2_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_2, qj_0, c1_0, res_i_2);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_0: uint32_t = c1_0;
    let mut c10_0: uint32_t = r_0;
    let mut res_j_0: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_0: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_0, res_j_0, resb_0);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_1: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_1: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_1: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut a_i_3: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    let mut res_i0_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_3, qj_1, c1_1, res_i0_3);
    let mut a_i0_3: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_3, qj_1, c1_1, res_i1_3);
    let mut a_i1_3: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_3, qj_1, c1_1, res_i2_3);
    let mut a_i2_3: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_3, qj_1, c1_1, res_i_3);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_4: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    let mut res_i0_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_4, qj_1, c1_1, res_i0_4);
    let mut a_i0_4: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_4, qj_1, c1_1, res_i1_4);
    let mut a_i1_4: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_4, qj_1, c1_1, res_i2_4);
    let mut a_i2_4: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_4, qj_1, c1_1, res_i_4);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_1: uint32_t = c1_1;
    let mut c10_1: uint32_t = r_1;
    let mut res_j_1: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_1: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_1, res_j_1, resb_1);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_2: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_2: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_2: uint32_t = 0 as libc::c_uint;
    let mut i_2: uint32_t = 0 as libc::c_uint;
    let mut a_i_5: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    let mut res_i0_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_5, qj_2, c1_2, res_i0_5);
    let mut a_i0_5: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_5, qj_2, c1_2, res_i1_5);
    let mut a_i1_5: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_5, qj_2, c1_2, res_i2_5);
    let mut a_i2_5: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_5, qj_2, c1_2, res_i_5);
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_6: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    let mut res_i0_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_6, qj_2, c1_2, res_i0_6);
    let mut a_i0_6: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_6, qj_2, c1_2, res_i1_6);
    let mut a_i1_6: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_6, qj_2, c1_2, res_i2_6);
    let mut a_i2_6: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_6, qj_2, c1_2, res_i_6);
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_2: uint32_t = c1_2;
    let mut c10_2: uint32_t = r_2;
    let mut res_j_2: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_2: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_2, res_j_2, resb_2);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_3: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_3: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_3: uint32_t = 0 as libc::c_uint;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    let mut a_i_7: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    let mut res_i0_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_7, qj_3, c1_3, res_i0_7);
    let mut a_i0_7: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_7, qj_3, c1_3, res_i1_7);
    let mut a_i1_7: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_7, qj_3, c1_3, res_i2_7);
    let mut a_i2_7: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_7, qj_3, c1_3, res_i_7);
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_8: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    let mut res_i0_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_8, qj_3, c1_3, res_i0_8);
    let mut a_i0_8: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_8, qj_3, c1_3, res_i1_8);
    let mut a_i1_8: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_8, qj_3, c1_3, res_i2_8);
    let mut a_i2_8: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_8, qj_3, c1_3, res_i_8);
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_3: uint32_t = c1_3;
    let mut c10_3: uint32_t = r_3;
    let mut res_j_3: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_3: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_3, res_j_3, resb_3);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_4: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_4: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_4: uint32_t = 0 as libc::c_uint;
    let mut i_4: uint32_t = 0 as libc::c_uint;
    let mut a_i_9: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    let mut res_i0_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_9, qj_4, c1_4, res_i0_9);
    let mut a_i0_9: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_9, qj_4, c1_4, res_i1_9);
    let mut a_i1_9: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_9, qj_4, c1_4, res_i2_9);
    let mut a_i2_9: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_9, qj_4, c1_4, res_i_9);
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_10: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    let mut res_i0_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_10, qj_4, c1_4, res_i0_10);
    let mut a_i0_10: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_10, qj_4, c1_4, res_i1_10);
    let mut a_i1_10: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_10, qj_4, c1_4, res_i2_10);
    let mut a_i2_10: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_10, qj_4, c1_4, res_i_10);
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_4: uint32_t = c1_4;
    let mut c10_4: uint32_t = r_4;
    let mut res_j_4: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_4: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_4, res_j_4, resb_4);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_5: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_5: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_5: uint32_t = 0 as libc::c_uint;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    let mut a_i_11: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    let mut res_i0_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_11, qj_5, c1_5, res_i0_11);
    let mut a_i0_11: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_11, qj_5, c1_5, res_i1_11);
    let mut a_i1_11: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_11, qj_5, c1_5, res_i2_11);
    let mut a_i2_11: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_11, qj_5, c1_5, res_i_11);
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_12: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    let mut res_i0_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_12, qj_5, c1_5, res_i0_12);
    let mut a_i0_12: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_12, qj_5, c1_5, res_i1_12);
    let mut a_i1_12: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_12, qj_5, c1_5, res_i2_12);
    let mut a_i2_12: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_12, qj_5, c1_5, res_i_12);
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_5: uint32_t = c1_5;
    let mut c10_5: uint32_t = r_5;
    let mut res_j_5: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_5: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_5, res_j_5, resb_5);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_6: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_6: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_6: uint32_t = 0 as libc::c_uint;
    let mut i_6: uint32_t = 0 as libc::c_uint;
    let mut a_i_13: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    let mut res_i0_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_13, qj_6, c1_6, res_i0_13);
    let mut a_i0_13: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_13, qj_6, c1_6, res_i1_13);
    let mut a_i1_13: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_13, qj_6, c1_6, res_i2_13);
    let mut a_i2_13: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_13, qj_6, c1_6, res_i_13);
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_14: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    let mut res_i0_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_14, qj_6, c1_6, res_i0_14);
    let mut a_i0_14: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_14, qj_6, c1_6, res_i1_14);
    let mut a_i1_14: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_14, qj_6, c1_6, res_i2_14);
    let mut a_i2_14: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_14, qj_6, c1_6, res_i_14);
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_6: uint32_t = c1_6;
    let mut c10_6: uint32_t = r_6;
    let mut res_j_6: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_6: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_6, res_j_6, resb_6);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        res as *mut libc::c_void,
        c.offset(8 as libc::c_uint as isize) as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c00: uint32_t = c0;
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut c1_7: uint32_t = 0 as libc::c_uint;
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut t1: uint32_t = *res.offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
    let mut t20: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
    let mut res_i0_15: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t1, t20, res_i0_15);
    let mut t10: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut t21: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_15: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t10, t21, res_i1_15);
    let mut t11: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut t22: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_15: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t11, t22, res_i2_15);
    let mut t12: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut t2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_15: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t12, t2, res_i_15);
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_0: uint32_t = *res.offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
    let mut t20_0: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
    let mut res_i0_16: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t1_0, t20_0, res_i0_16);
    let mut t10_0: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut t21_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_16: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t10_0, t21_0, res_i1_16);
    let mut t11_0: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut t22_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_16: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t11_0, t22_0, res_i2_16);
    let mut t12_0: uint32_t = *res
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut t2_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_7).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_16: *mut uint32_t = tmp
        .as_mut_ptr()
        .offset((4 as libc::c_uint).wrapping_mul(i_7) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_7 = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c1_7, t12_0, t2_0, res_i_16);
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c10_7: uint32_t = c1_7;
    let mut c2: uint32_t = c00.wrapping_sub(c10_7);
    let mut i_8: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os: *mut uint32_t = res;
    *os.offset(i_8 as isize) = x;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_0: *mut uint32_t = res;
    *os_0.offset(i_8 as isize) = x_0;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_1: *mut uint32_t = res;
    *os_1.offset(i_8 as isize) = x_1;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_2: *mut uint32_t = res;
    *os_2.offset(i_8 as isize) = x_2;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_3: *mut uint32_t = res;
    *os_3.offset(i_8 as isize) = x_3;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_4: *mut uint32_t = res;
    *os_4.offset(i_8 as isize) = x_4;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_5: *mut uint32_t = res;
    *os_5.offset(i_8 as isize) = x_5;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = c2 & *res.offset(i_8 as isize) | !c2 & tmp[i_8 as usize];
    let mut os_6: *mut uint32_t = res;
    *os_6.offset(i_8 as isize) = x_6;
    i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn to(
    mut n: *mut uint32_t,
    mut nInv: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut aM: *mut uint32_t,
) {
    let mut c: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
    Hacl_Bignum256_32_mul(a, r2, c.as_mut_ptr());
    reduction(n, nInv, c.as_mut_ptr(), aM);
}
#[inline]
unsafe extern "C" fn from(
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut a: *mut uint32_t,
) {
    let mut tmp: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
        tmp.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    reduction(n, nInv_u64, tmp.as_mut_ptr(), a);
}
#[inline]
unsafe extern "C" fn areduction(
    mut n: *mut uint32_t,
    mut nInv: uint32_t,
    mut c: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut c0: uint32_t = 0 as libc::c_uint;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut qj: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0: *mut uint32_t = c.offset(i0 as isize);
    let mut c1: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut a_i: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i, qj, c1, res_i0);
    let mut a_i0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0, qj, c1, res_i1);
    let mut a_i1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1, qj, c1, res_i2);
    let mut a_i2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2, qj, c1, res_i);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_0: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    let mut res_i0_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_0, qj, c1, res_i0_0);
    let mut a_i0_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(1 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_0, qj, c1, res_i1_0);
    let mut a_i1_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(2 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_0, qj, c1, res_i2_0);
    let mut a_i2_0: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i_0: *mut uint32_t = res_j0
        .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
        .offset(3 as libc::c_uint as isize);
    c1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_0, qj, c1, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r: uint32_t = c1;
    let mut c10: uint32_t = r;
    let mut res_j: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10, res_j, resb);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_0: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_0: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_0: uint32_t = 0 as libc::c_uint;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut a_i_1: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_1, qj_0, c1_0, res_i0_1);
    let mut a_i0_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_1, qj_0, c1_0, res_i1_1);
    let mut a_i1_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_1, qj_0, c1_0, res_i2_1);
    let mut a_i2_1: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_1: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_1, qj_0, c1_0, res_i_1);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_2: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    let mut res_i0_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_2, qj_0, c1_0, res_i0_2);
    let mut a_i0_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_2, qj_0, c1_0, res_i1_2);
    let mut a_i1_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_2, qj_0, c1_0, res_i2_2);
    let mut a_i2_2: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_0).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_2: *mut uint32_t = res_j0_0
        .offset((4 as libc::c_uint).wrapping_mul(i_0) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_0 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_2, qj_0, c1_0, res_i_2);
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_0: uint32_t = c1_0;
    let mut c10_0: uint32_t = r_0;
    let mut res_j_0: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_0: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_0, res_j_0, resb_0);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_1: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_1: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_1: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut a_i_3: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    let mut res_i0_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_3, qj_1, c1_1, res_i0_3);
    let mut a_i0_3: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_3, qj_1, c1_1, res_i1_3);
    let mut a_i1_3: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_3, qj_1, c1_1, res_i2_3);
    let mut a_i2_3: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_3: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_3, qj_1, c1_1, res_i_3);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_4: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    let mut res_i0_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_4, qj_1, c1_1, res_i0_4);
    let mut a_i0_4: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_4, qj_1, c1_1, res_i1_4);
    let mut a_i1_4: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_4, qj_1, c1_1, res_i2_4);
    let mut a_i2_4: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_1).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_4: *mut uint32_t = res_j0_1
        .offset((4 as libc::c_uint).wrapping_mul(i_1) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_1 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_4, qj_1, c1_1, res_i_4);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_1: uint32_t = c1_1;
    let mut c10_1: uint32_t = r_1;
    let mut res_j_1: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_1: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_1, res_j_1, resb_1);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_2: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_2: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_2: uint32_t = 0 as libc::c_uint;
    let mut i_2: uint32_t = 0 as libc::c_uint;
    let mut a_i_5: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    let mut res_i0_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_5, qj_2, c1_2, res_i0_5);
    let mut a_i0_5: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_5, qj_2, c1_2, res_i1_5);
    let mut a_i1_5: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_5, qj_2, c1_2, res_i2_5);
    let mut a_i2_5: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_5: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_5, qj_2, c1_2, res_i_5);
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_6: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    let mut res_i0_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_6, qj_2, c1_2, res_i0_6);
    let mut a_i0_6: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_6, qj_2, c1_2, res_i1_6);
    let mut a_i1_6: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_6, qj_2, c1_2, res_i2_6);
    let mut a_i2_6: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_2).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_6: *mut uint32_t = res_j0_2
        .offset((4 as libc::c_uint).wrapping_mul(i_2) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_2 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_6, qj_2, c1_2, res_i_6);
    i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_2: uint32_t = c1_2;
    let mut c10_2: uint32_t = r_2;
    let mut res_j_2: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_2: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_2, res_j_2, resb_2);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_3: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_3: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_3: uint32_t = 0 as libc::c_uint;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    let mut a_i_7: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    let mut res_i0_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_7, qj_3, c1_3, res_i0_7);
    let mut a_i0_7: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_7, qj_3, c1_3, res_i1_7);
    let mut a_i1_7: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_7, qj_3, c1_3, res_i2_7);
    let mut a_i2_7: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_7: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_7, qj_3, c1_3, res_i_7);
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_8: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    let mut res_i0_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_8, qj_3, c1_3, res_i0_8);
    let mut a_i0_8: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_8, qj_3, c1_3, res_i1_8);
    let mut a_i1_8: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_8, qj_3, c1_3, res_i2_8);
    let mut a_i2_8: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_3).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_8: *mut uint32_t = res_j0_3
        .offset((4 as libc::c_uint).wrapping_mul(i_3) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_3 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_8, qj_3, c1_3, res_i_8);
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_3: uint32_t = c1_3;
    let mut c10_3: uint32_t = r_3;
    let mut res_j_3: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_3: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_3, res_j_3, resb_3);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_4: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_4: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_4: uint32_t = 0 as libc::c_uint;
    let mut i_4: uint32_t = 0 as libc::c_uint;
    let mut a_i_9: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    let mut res_i0_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_9, qj_4, c1_4, res_i0_9);
    let mut a_i0_9: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_9, qj_4, c1_4, res_i1_9);
    let mut a_i1_9: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_9, qj_4, c1_4, res_i2_9);
    let mut a_i2_9: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_9: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_9, qj_4, c1_4, res_i_9);
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_10: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    let mut res_i0_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_10, qj_4, c1_4, res_i0_10);
    let mut a_i0_10: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_10, qj_4, c1_4, res_i1_10);
    let mut a_i1_10: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_10, qj_4, c1_4, res_i2_10);
    let mut a_i2_10: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_4).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_10: *mut uint32_t = res_j0_4
        .offset((4 as libc::c_uint).wrapping_mul(i_4) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_4 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_10, qj_4, c1_4, res_i_10);
    i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_4: uint32_t = c1_4;
    let mut c10_4: uint32_t = r_4;
    let mut res_j_4: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_4: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_4, res_j_4, resb_4);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_5: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_5: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_5: uint32_t = 0 as libc::c_uint;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    let mut a_i_11: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    let mut res_i0_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_11, qj_5, c1_5, res_i0_11);
    let mut a_i0_11: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_11, qj_5, c1_5, res_i1_11);
    let mut a_i1_11: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_11, qj_5, c1_5, res_i2_11);
    let mut a_i2_11: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_11: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_11, qj_5, c1_5, res_i_11);
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_12: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    let mut res_i0_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_12, qj_5, c1_5, res_i0_12);
    let mut a_i0_12: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_12, qj_5, c1_5, res_i1_12);
    let mut a_i1_12: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_12, qj_5, c1_5, res_i2_12);
    let mut a_i2_12: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_5).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_12: *mut uint32_t = res_j0_5
        .offset((4 as libc::c_uint).wrapping_mul(i_5) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_5 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_12, qj_5, c1_5, res_i_12);
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_5: uint32_t = c1_5;
    let mut c10_5: uint32_t = r_5;
    let mut res_j_5: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_5: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_5, res_j_5, resb_5);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut qj_6: uint32_t = nInv * *c.offset(i0 as isize);
    let mut res_j0_6: *mut uint32_t = c.offset(i0 as isize);
    let mut c1_6: uint32_t = 0 as libc::c_uint;
    let mut i_6: uint32_t = 0 as libc::c_uint;
    let mut a_i_13: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    let mut res_i0_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_13, qj_6, c1_6, res_i0_13);
    let mut a_i0_13: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_13, qj_6, c1_6, res_i1_13);
    let mut a_i1_13: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_13, qj_6, c1_6, res_i2_13);
    let mut a_i2_13: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_13: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_13, qj_6, c1_6, res_i_13);
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut a_i_14: uint32_t = *n.offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    let mut res_i0_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i_14, qj_6, c1_6, res_i0_14);
    let mut a_i0_14: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(1 as libc::c_uint)
                as isize,
        );
    let mut res_i1_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(1 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i0_14, qj_6, c1_6, res_i1_14);
    let mut a_i1_14: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(2 as libc::c_uint)
                as isize,
        );
    let mut res_i2_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(2 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i1_14, qj_6, c1_6, res_i2_14);
    let mut a_i2_14: uint32_t = *n
        .offset(
            (4 as libc::c_uint).wrapping_mul(i_6).wrapping_add(3 as libc::c_uint)
                as isize,
        );
    let mut res_i_14: *mut uint32_t = res_j0_6
        .offset((4 as libc::c_uint).wrapping_mul(i_6) as isize)
        .offset(3 as libc::c_uint as isize);
    c1_6 = Hacl_Bignum_Base_mul_wide_add2_u32(a_i2_14, qj_6, c1_6, res_i_14);
    i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut r_6: uint32_t = c1_6;
    let mut c10_6: uint32_t = r_6;
    let mut res_j_6: uint32_t = *c.offset((8 as libc::c_uint).wrapping_add(i0) as isize);
    let mut resb_6: *mut uint32_t = c
        .offset(8 as libc::c_uint as isize)
        .offset(i0 as isize);
    c0 = Hacl_IntTypes_Intrinsics_add_carry_u32(c0, c10_6, res_j_6, resb_6);
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        res as *mut libc::c_void,
        c.offset(8 as libc::c_uint as isize) as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c00: uint32_t = c0;
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut c1_7: uint32_t = Hacl_Bignum256_32_sub(res, n, tmp.as_mut_ptr());
    let mut m: uint32_t = (0 as libc::c_uint).wrapping_sub(c00);
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os: *mut uint32_t = res;
    *os.offset(i_7 as isize) = x;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_0: *mut uint32_t = res;
    *os_0.offset(i_7 as isize) = x_0;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_1: *mut uint32_t = res;
    *os_1.offset(i_7 as isize) = x_1;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_2: *mut uint32_t = res;
    *os_2.offset(i_7 as isize) = x_2;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_3: *mut uint32_t = res;
    *os_3.offset(i_7 as isize) = x_3;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_4: *mut uint32_t = res;
    *os_4.offset(i_7 as isize) = x_4;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_5: *mut uint32_t = res;
    *os_5.offset(i_7 as isize) = x_5;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = m & tmp[i_7 as usize] | !m & *res.offset(i_7 as isize);
    let mut os_6: *mut uint32_t = res;
    *os_6.offset(i_7 as isize) = x_6;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn amont_mul(
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut bM: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    let mut c: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
    Hacl_Bignum256_32_mul(aM, bM, c.as_mut_ptr());
    areduction(n, nInv_u64, c.as_mut_ptr(), resM);
}
#[inline]
unsafe extern "C" fn amont_sqr(
    mut n: *mut uint32_t,
    mut nInv_u64: uint32_t,
    mut aM: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    let mut c: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
    Hacl_Bignum256_32_sqr(aM, c.as_mut_ptr());
    areduction(n, nInv_u64, c.as_mut_ptr(), resM);
}
#[inline]
unsafe extern "C" fn bn_slow_precomp(
    mut n: *mut uint32_t,
    mut mu: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut a_mod: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut a1: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
        a1.as_mut_ptr() as *mut libc::c_void,
        a as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    areduction(n, mu, a1.as_mut_ptr(), a_mod.as_mut_ptr());
    to(n, mu, r2, a_mod.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) -> bool {
    let mut one: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    one[0 as libc::c_uint as usize] = 1 as libc::c_uint;
    let mut bit0: uint32_t = *n.offset(0 as libc::c_uint as isize) & 1 as libc::c_uint;
    let mut m0: uint32_t = (0 as libc::c_uint).wrapping_sub(bit0);
    let mut acc: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint32_t = FStar_UInt32_eq_mask(one[i as usize], *n.offset(i as isize));
    let mut blt: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq & acc | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_0: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_0 & acc | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_1: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_1 & acc | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_2: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_2 & acc | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_3: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_3: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_3 & acc | !beq_3 & blt_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_4: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_4: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_4 & acc | !beq_4 & blt_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_5: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_5: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_5 & acc | !beq_5 & blt_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_6: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_6: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc = beq_6 & acc | !beq_6 & blt_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m1: uint32_t = acc;
    let mut is_valid_m: uint32_t = m0 & m1;
    let mut nBits: uint32_t = (32 as libc::c_uint)
        .wrapping_mul(Hacl_Bignum_Lib_bn_get_top_index_u32(8 as libc::c_uint, n));
    if is_valid_m == 0xffffffff as libc::c_uint {
        let mut r2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        precompr2(nBits, n, r2.as_mut_ptr());
        let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
            *n.offset(0 as libc::c_uint as isize),
        );
        bn_slow_precomp(n, mu, r2.as_mut_ptr(), a, res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffff as libc::c_uint;
}
unsafe extern "C" fn exp_check(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
) -> uint32_t {
    let mut one: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    one[0 as libc::c_uint as usize] = 1 as libc::c_uint;
    let mut bit0: uint32_t = *n.offset(0 as libc::c_uint as isize) & 1 as libc::c_uint;
    let mut m0: uint32_t = (0 as libc::c_uint).wrapping_sub(bit0);
    let mut acc0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint32_t = FStar_UInt32_eq_mask(one[i as usize], *n.offset(i as isize));
    let mut blt: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq & acc0 | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_0: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_0 & acc0 | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_1: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_1 & acc0 | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_2: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_2 & acc0 | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_3: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_3: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_3 & acc0 | !beq_3 & blt_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_4: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_4: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_4 & acc0 | !beq_4 & blt_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_5: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_5: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_5 & acc0 | !beq_5 & blt_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_6: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_6: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_6 & acc0 | !beq_6 & blt_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
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
                b"Hacl_Bignum256_32.c\0" as *const u8 as *const libc::c_char,
                596 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = bLen as usize;
        let mut b2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
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
            let mut beq_7: uint32_t = FStar_UInt32_eq_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            let mut blt_7: uint32_t = !FStar_UInt32_gte_mask(
                *b.offset(i_0 as isize),
                *b2.as_mut_ptr().offset(i_0 as isize),
            );
            acc = beq_7 & acc | !beq_7 & blt_7;
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
    let mut beq_8: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_8: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_8 & acc_0 | !beq_8 & blt_8;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_9: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_9: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_9 & acc_0 | !beq_9 & blt_9;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_10: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_10: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_10 & acc_0 | !beq_10 & blt_10;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_11: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_11: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_11 & acc_0 | !beq_11 & blt_11;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_12: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_12: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_12 & acc_0 | !beq_12 & blt_12;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_13: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_13: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_13 & acc_0 | !beq_13 & blt_13;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_14: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_14: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_14 & acc_0 | !beq_14 & blt_14;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_15: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_15: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc_0 = beq_15 & acc_0 | !beq_15 & blt_15;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m2: uint32_t = acc_0;
    let mut m: uint32_t = m1 & m2;
    return m00 & m;
}
#[inline]
unsafe extern "C" fn exp_vartime_precomp(
    mut n: *mut uint32_t,
    mut mu: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if bBits < 200 as libc::c_uint {
        let mut aM: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        to(n, mu, r2, a, aM.as_mut_ptr());
        let mut resM: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        let mut ctx: [uint32_t; 16] = [
            0 as libc::c_uint,
            0,
            0,
            0,
            0,
            0,
            0,
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
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(8 as libc::c_uint as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n0: *mut uint32_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint32_t = ctx
            .as_mut_ptr()
            .offset(8 as libc::c_uint as isize);
        from(ctx_n0, mu, ctx_r2, resM.as_mut_ptr());
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < bBits {
            let mut i1: uint32_t = i.wrapping_div(32 as libc::c_uint);
            let mut j: uint32_t = i.wrapping_rem(32 as libc::c_uint);
            let mut tmp: uint32_t = *b.offset(i1 as isize);
            let mut bit: uint32_t = tmp >> j & 1 as libc::c_uint;
            if !(bit == 0 as libc::c_uint) {
                let mut aM_copy: [uint32_t; 8] = [
                    0 as libc::c_uint,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                ];
                memcpy(
                    aM_copy.as_mut_ptr() as *mut libc::c_void,
                    resM.as_mut_ptr() as *const libc::c_void,
                    (8 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(
                            ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
                        ),
                );
                let mut ctx_n: *mut uint32_t = ctx.as_mut_ptr();
                amont_mul(
                    ctx_n,
                    mu,
                    aM_copy.as_mut_ptr(),
                    aM.as_mut_ptr(),
                    resM.as_mut_ptr(),
                );
            }
            let mut aM_copy_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
            memcpy(
                aM_copy_0.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (8 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n_0: *mut uint32_t = ctx.as_mut_ptr();
            amont_sqr(ctx_n_0, mu, aM_copy_0.as_mut_ptr(), aM.as_mut_ptr());
            i = i.wrapping_add(1);
            i;
        }
        from(n, mu, resM.as_mut_ptr(), res);
        return;
    }
    let mut aM_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    to(n, mu, r2, a, aM_0.as_mut_ptr());
    let mut resM_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(32 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    let mut ctx_0: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(8 as libc::c_uint as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut table: [uint32_t; 128] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut tmp_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut t0: *mut uint32_t = table.as_mut_ptr();
    let mut t1: *mut uint32_t = table.as_mut_ptr().offset(8 as libc::c_uint as isize);
    let mut ctx_n0_0: *mut uint32_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint32_t = ctx_0
        .as_mut_ptr()
        .offset(8 as libc::c_uint as isize);
    from(ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1, mu, aM_copy0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_1: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_1, mu, aM_copy_1.as_mut_ptr(), t2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_0, mu, aM_copy0_0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_2, mu, aM_copy_2.as_mut_ptr(), t2_0, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_1: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_1, mu, aM_copy0_1.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_3: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_3, mu, aM_copy_3.as_mut_ptr(), t2_1, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_2, mu, aM_copy0_2.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_4: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_4, mu, aM_copy_4.as_mut_ptr(), t2_2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_3: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_3, mu, aM_copy0_3.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_5: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_5, mu, aM_copy_5.as_mut_ptr(), t2_3, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_4: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_4, mu, aM_copy0_4.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_6: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_6, mu, aM_copy_6.as_mut_ptr(), t2_4, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_5: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_5, mu, aM_copy0_5.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_0)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_7: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_7.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_7: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_7, mu, aM_copy_7.as_mut_ptr(), t2_5, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
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
            .offset(bits_l32.wrapping_mul(8 as libc::c_uint) as isize);
        memcpy(
            resM_0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l as *mut uint32_t as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
    } else {
        let mut ctx_n_8: *mut uint32_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint32_t = ctx_0
            .as_mut_ptr()
            .offset(8 as libc::c_uint as isize);
        from(ctx_n_8, mu, ctx_r2_0, resM_0.as_mut_ptr());
    }
    let mut tmp0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut i_2: uint32_t = 0 as libc::c_uint;
    while i_2 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i0: uint32_t = 0 as libc::c_uint;
        let mut aM_copy_8: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_9, mu, aM_copy_8.as_mut_ptr(), resM_0.as_mut_ptr());
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_9: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_10, mu, aM_copy_9.as_mut_ptr(), resM_0.as_mut_ptr());
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_10: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_11, mu, aM_copy_10.as_mut_ptr(), resM_0.as_mut_ptr());
        i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_11: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_12, mu, aM_copy_11.as_mut_ptr(), resM_0.as_mut_ptr());
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
            .offset(bits_l32_0.wrapping_mul(8 as libc::c_uint) as isize);
        memcpy(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            a_bits_l_0 as *mut uint32_t as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut aM_copy_12: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_12.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_13: *mut uint32_t = ctx_0.as_mut_ptr();
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
    mut n: *mut uint32_t,
    mut mu: uint32_t,
    mut r2: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    if bBits < 200 as libc::c_uint {
        let mut aM: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        to(n, mu, r2, a, aM.as_mut_ptr());
        let mut resM: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        let mut ctx: [uint32_t; 16] = [
            0 as libc::c_uint,
            0,
            0,
            0,
            0,
            0,
            0,
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
            ctx.as_mut_ptr() as *mut libc::c_void,
            n as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(8 as libc::c_uint as isize) as *mut libc::c_void,
            r2 as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut sw: uint32_t = 0 as libc::c_uint;
        let mut ctx_n0: *mut uint32_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint32_t = ctx
            .as_mut_ptr()
            .offset(8 as libc::c_uint as isize);
        from(ctx_n0, mu, ctx_r2, resM.as_mut_ptr());
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
            let mut dummy: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy;
            aM[i as usize] = aM[i as usize] ^ dummy;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_0: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_0;
            aM[i as usize] = aM[i as usize] ^ dummy_0;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_1: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_1;
            aM[i as usize] = aM[i as usize] ^ dummy_1;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_2: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_2;
            aM[i as usize] = aM[i as usize] ^ dummy_2;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_3: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_3;
            aM[i as usize] = aM[i as usize] ^ dummy_3;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_4: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_4;
            aM[i as usize] = aM[i as usize] ^ dummy_4;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_5: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_5;
            aM[i as usize] = aM[i as usize] ^ dummy_5;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut dummy_6: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                & (resM[i as usize] ^ aM[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy_6;
            aM[i as usize] = aM[i as usize] ^ dummy_6;
            i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut aM_copy: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
            memcpy(
                aM_copy.as_mut_ptr() as *mut libc::c_void,
                aM.as_mut_ptr() as *const libc::c_void,
                (8 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n1: *mut uint32_t = ctx.as_mut_ptr();
            amont_mul(
                ctx_n1,
                mu,
                aM_copy.as_mut_ptr(),
                resM.as_mut_ptr(),
                aM.as_mut_ptr(),
            );
            let mut aM_copy0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
            memcpy(
                aM_copy0.as_mut_ptr() as *mut libc::c_void,
                resM.as_mut_ptr() as *const libc::c_void,
                (8 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n: *mut uint32_t = ctx.as_mut_ptr();
            amont_sqr(ctx_n, mu, aM_copy0.as_mut_ptr(), resM.as_mut_ptr());
            sw = bit;
            i0 = i0.wrapping_add(1);
            i0;
        }
        let mut sw0: uint32_t = sw;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        let mut dummy_7: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_7;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_7;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_8: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_8;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_8;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_9: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_9;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_9;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_10: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_10;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_10;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_11: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_11;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_11;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_12: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_12;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_12;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_13: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_13;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_13;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut dummy_14: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
            & (resM[i_0 as usize] ^ aM[i_0 as usize]);
        resM[i_0 as usize] = resM[i_0 as usize] ^ dummy_14;
        aM[i_0 as usize] = aM[i_0 as usize] ^ dummy_14;
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        from(n, mu, resM.as_mut_ptr(), res);
        return;
    }
    let mut aM_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    to(n, mu, r2, a, aM_0.as_mut_ptr());
    let mut resM_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut bLen: uint32_t = 0;
    if bBits == 0 as libc::c_uint {
        bLen = 1 as libc::c_uint;
    } else {
        bLen = bBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(32 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
    }
    let mut ctx_0: [uint32_t; 16] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
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
        ctx_0.as_mut_ptr() as *mut libc::c_void,
        n as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        ctx_0.as_mut_ptr().offset(8 as libc::c_uint as isize) as *mut libc::c_void,
        r2 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut table: [uint32_t; 128] = [
        0 as libc::c_uint,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut tmp_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut t0: *mut uint32_t = table.as_mut_ptr();
    let mut t1: *mut uint32_t = table.as_mut_ptr().offset(8 as libc::c_uint as isize);
    let mut ctx_n0_0: *mut uint32_t = ctx_0.as_mut_ptr();
    let mut ctx_r20: *mut uint32_t = ctx_0
        .as_mut_ptr()
        .offset(8 as libc::c_uint as isize);
    from(ctx_n0_0, mu, ctx_r20, t0);
    memcpy(
        t1 as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut t11: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_0.as_mut_ptr() as *mut libc::c_void,
        t11 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_0: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_0, mu, aM_copy0_0.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_0.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_0: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_0, mu, aM_copy_0.as_mut_ptr(), t2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_1: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_1.as_mut_ptr() as *mut libc::c_void,
        t11_0 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_1: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_1, mu, aM_copy0_1.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_0: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_1: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_1.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_1: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_1, mu, aM_copy_1.as_mut_ptr(), t2_0, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_2.as_mut_ptr() as *mut libc::c_void,
        t11_1 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_2: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_2, mu, aM_copy0_2.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_1: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_2.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_2: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_2, mu, aM_copy_2.as_mut_ptr(), t2_1, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_3: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_3.as_mut_ptr() as *mut libc::c_void,
        t11_2 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_3: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_3, mu, aM_copy0_3.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_2: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_3: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_3.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_3: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_3, mu, aM_copy_3.as_mut_ptr(), t2_2, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_4: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_4.as_mut_ptr() as *mut libc::c_void,
        t11_3 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_4: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_4, mu, aM_copy0_4.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_3: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_4: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_4.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_4: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_4, mu, aM_copy_4.as_mut_ptr(), t2_3, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_5: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_5.as_mut_ptr() as *mut libc::c_void,
        t11_4 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_5: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_5, mu, aM_copy0_5.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_4: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_5: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_5.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_5: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_5, mu, aM_copy_5.as_mut_ptr(), t2_4, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t11_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy0_6: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy0_6.as_mut_ptr() as *mut libc::c_void,
        t11_5 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n1_6: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_sqr(ctx_n1_6, mu, aM_copy0_6.as_mut_ptr(), tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut t2_5: *mut uint32_t = table
        .as_mut_ptr()
        .offset(
            (2 as libc::c_uint)
                .wrapping_mul(i_1)
                .wrapping_add(2 as libc::c_uint)
                .wrapping_mul(8 as libc::c_uint) as isize,
        );
    let mut aM_copy_6: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        aM_copy_6.as_mut_ptr() as *mut libc::c_void,
        aM_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctx_n_6: *mut uint32_t = ctx_0.as_mut_ptr();
    amont_mul(ctx_n_6, mu, aM_copy_6.as_mut_ptr(), t2_5, tmp_0.as_mut_ptr());
    memcpy(
        table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(3 as libc::c_uint)
                    .wrapping_mul(8 as libc::c_uint) as isize,
            ) as *mut libc::c_void,
        tmp_0.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
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
            table.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i1_0: uint32_t = 0 as libc::c_uint;
        let mut c: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut x: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os: *mut uint32_t = resM_0.as_mut_ptr();
        *os.offset(i_2 as isize) = x;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_0: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_0: *mut uint32_t = resM_0.as_mut_ptr();
        *os_0.offset(i_2 as isize) = x_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_1: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_1: *mut uint32_t = resM_0.as_mut_ptr();
        *os_1.offset(i_2 as isize) = x_1;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_2: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_2: *mut uint32_t = resM_0.as_mut_ptr();
        *os_2.offset(i_2 as isize) = x_2;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_3: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_3: *mut uint32_t = resM_0.as_mut_ptr();
        *os_3.offset(i_2 as isize) = x_3;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_4: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_4: *mut uint32_t = resM_0.as_mut_ptr();
        *os_4.offset(i_2 as isize) = x_4;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_5: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_5: *mut uint32_t = resM_0.as_mut_ptr();
        *os_5.offset(i_2 as isize) = x_5;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_6: uint32_t = c & *res_j.offset(i_2 as isize)
            | !c & resM_0[i_2 as usize];
        let mut os_6: *mut uint32_t = resM_0.as_mut_ptr();
        *os_6.offset(i_2 as isize) = x_6;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_0: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_0: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_3: uint32_t = 0 as libc::c_uint;
        let mut x_7: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_7: *mut uint32_t = resM_0.as_mut_ptr();
        *os_7.offset(i_3 as isize) = x_7;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_8: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_8: *mut uint32_t = resM_0.as_mut_ptr();
        *os_8.offset(i_3 as isize) = x_8;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_9: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_9: *mut uint32_t = resM_0.as_mut_ptr();
        *os_9.offset(i_3 as isize) = x_9;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_10: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_10: *mut uint32_t = resM_0.as_mut_ptr();
        *os_10.offset(i_3 as isize) = x_10;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_11: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_11: *mut uint32_t = resM_0.as_mut_ptr();
        *os_11.offset(i_3 as isize) = x_11;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_12: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_12: *mut uint32_t = resM_0.as_mut_ptr();
        *os_12.offset(i_3 as isize) = x_12;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_13: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_13: *mut uint32_t = resM_0.as_mut_ptr();
        *os_13.offset(i_3 as isize) = x_13;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_14: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
            | !c_0 & resM_0[i_3 as usize];
        let mut os_14: *mut uint32_t = resM_0.as_mut_ptr();
        *os_14.offset(i_3 as isize) = x_14;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_1: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_1: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut x_15: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_15: *mut uint32_t = resM_0.as_mut_ptr();
        *os_15.offset(i_4 as isize) = x_15;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_16: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_16: *mut uint32_t = resM_0.as_mut_ptr();
        *os_16.offset(i_4 as isize) = x_16;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_17: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_17: *mut uint32_t = resM_0.as_mut_ptr();
        *os_17.offset(i_4 as isize) = x_17;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_18: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_18: *mut uint32_t = resM_0.as_mut_ptr();
        *os_18.offset(i_4 as isize) = x_18;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_19: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_19: *mut uint32_t = resM_0.as_mut_ptr();
        *os_19.offset(i_4 as isize) = x_19;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_20: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_20: *mut uint32_t = resM_0.as_mut_ptr();
        *os_20.offset(i_4 as isize) = x_20;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_21: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_21: *mut uint32_t = resM_0.as_mut_ptr();
        *os_21.offset(i_4 as isize) = x_21;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_22: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
            | !c_1 & resM_0[i_4 as usize];
        let mut os_22: *mut uint32_t = resM_0.as_mut_ptr();
        *os_22.offset(i_4 as isize) = x_22;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_2: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_2: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_5: uint32_t = 0 as libc::c_uint;
        let mut x_23: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_23: *mut uint32_t = resM_0.as_mut_ptr();
        *os_23.offset(i_5 as isize) = x_23;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_24: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_24: *mut uint32_t = resM_0.as_mut_ptr();
        *os_24.offset(i_5 as isize) = x_24;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_25: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_25: *mut uint32_t = resM_0.as_mut_ptr();
        *os_25.offset(i_5 as isize) = x_25;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_26: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_26: *mut uint32_t = resM_0.as_mut_ptr();
        *os_26.offset(i_5 as isize) = x_26;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_27: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_27: *mut uint32_t = resM_0.as_mut_ptr();
        *os_27.offset(i_5 as isize) = x_27;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_28: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_28: *mut uint32_t = resM_0.as_mut_ptr();
        *os_28.offset(i_5 as isize) = x_28;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_29: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_29: *mut uint32_t = resM_0.as_mut_ptr();
        *os_29.offset(i_5 as isize) = x_29;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_30: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
            | !c_2 & resM_0[i_5 as usize];
        let mut os_30: *mut uint32_t = resM_0.as_mut_ptr();
        *os_30.offset(i_5 as isize) = x_30;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_3: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_3: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_6: uint32_t = 0 as libc::c_uint;
        let mut x_31: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_31: *mut uint32_t = resM_0.as_mut_ptr();
        *os_31.offset(i_6 as isize) = x_31;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_32: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_32: *mut uint32_t = resM_0.as_mut_ptr();
        *os_32.offset(i_6 as isize) = x_32;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_33: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_33: *mut uint32_t = resM_0.as_mut_ptr();
        *os_33.offset(i_6 as isize) = x_33;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_34: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_34: *mut uint32_t = resM_0.as_mut_ptr();
        *os_34.offset(i_6 as isize) = x_34;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_35: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_35: *mut uint32_t = resM_0.as_mut_ptr();
        *os_35.offset(i_6 as isize) = x_35;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_36: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_36: *mut uint32_t = resM_0.as_mut_ptr();
        *os_36.offset(i_6 as isize) = x_36;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_37: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_37: *mut uint32_t = resM_0.as_mut_ptr();
        *os_37.offset(i_6 as isize) = x_37;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_38: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
            | !c_3 & resM_0[i_6 as usize];
        let mut os_38: *mut uint32_t = resM_0.as_mut_ptr();
        *os_38.offset(i_6 as isize) = x_38;
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_4: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_4: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_7: uint32_t = 0 as libc::c_uint;
        let mut x_39: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_39: *mut uint32_t = resM_0.as_mut_ptr();
        *os_39.offset(i_7 as isize) = x_39;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_40: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_40: *mut uint32_t = resM_0.as_mut_ptr();
        *os_40.offset(i_7 as isize) = x_40;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_41: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_41: *mut uint32_t = resM_0.as_mut_ptr();
        *os_41.offset(i_7 as isize) = x_41;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_42: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_42: *mut uint32_t = resM_0.as_mut_ptr();
        *os_42.offset(i_7 as isize) = x_42;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_43: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_43: *mut uint32_t = resM_0.as_mut_ptr();
        *os_43.offset(i_7 as isize) = x_43;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_44: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_44: *mut uint32_t = resM_0.as_mut_ptr();
        *os_44.offset(i_7 as isize) = x_44;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_45: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_45: *mut uint32_t = resM_0.as_mut_ptr();
        *os_45.offset(i_7 as isize) = x_45;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_46: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
            | !c_4 & resM_0[i_7 as usize];
        let mut os_46: *mut uint32_t = resM_0.as_mut_ptr();
        *os_46.offset(i_7 as isize) = x_46;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_5: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_5: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_8: uint32_t = 0 as libc::c_uint;
        let mut x_47: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_47: *mut uint32_t = resM_0.as_mut_ptr();
        *os_47.offset(i_8 as isize) = x_47;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_48: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_48: *mut uint32_t = resM_0.as_mut_ptr();
        *os_48.offset(i_8 as isize) = x_48;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_49: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_49: *mut uint32_t = resM_0.as_mut_ptr();
        *os_49.offset(i_8 as isize) = x_49;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_50: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_50: *mut uint32_t = resM_0.as_mut_ptr();
        *os_50.offset(i_8 as isize) = x_50;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_51: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_51: *mut uint32_t = resM_0.as_mut_ptr();
        *os_51.offset(i_8 as isize) = x_51;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_52: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_52: *mut uint32_t = resM_0.as_mut_ptr();
        *os_52.offset(i_8 as isize) = x_52;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_53: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_53: *mut uint32_t = resM_0.as_mut_ptr();
        *os_53.offset(i_8 as isize) = x_53;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_54: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
            | !c_5 & resM_0[i_8 as usize];
        let mut os_54: *mut uint32_t = resM_0.as_mut_ptr();
        *os_54.offset(i_8 as isize) = x_54;
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_6: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_6: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_9: uint32_t = 0 as libc::c_uint;
        let mut x_55: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_55: *mut uint32_t = resM_0.as_mut_ptr();
        *os_55.offset(i_9 as isize) = x_55;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_56: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_56: *mut uint32_t = resM_0.as_mut_ptr();
        *os_56.offset(i_9 as isize) = x_56;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_57: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_57: *mut uint32_t = resM_0.as_mut_ptr();
        *os_57.offset(i_9 as isize) = x_57;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_58: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_58: *mut uint32_t = resM_0.as_mut_ptr();
        *os_58.offset(i_9 as isize) = x_58;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_59: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_59: *mut uint32_t = resM_0.as_mut_ptr();
        *os_59.offset(i_9 as isize) = x_59;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_60: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_60: *mut uint32_t = resM_0.as_mut_ptr();
        *os_60.offset(i_9 as isize) = x_60;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_61: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_61: *mut uint32_t = resM_0.as_mut_ptr();
        *os_61.offset(i_9 as isize) = x_61;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_62: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
            | !c_6 & resM_0[i_9 as usize];
        let mut os_62: *mut uint32_t = resM_0.as_mut_ptr();
        *os_62.offset(i_9 as isize) = x_62;
        i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_7: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_7: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_10: uint32_t = 0 as libc::c_uint;
        let mut x_63: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_63: *mut uint32_t = resM_0.as_mut_ptr();
        *os_63.offset(i_10 as isize) = x_63;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_64: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_64: *mut uint32_t = resM_0.as_mut_ptr();
        *os_64.offset(i_10 as isize) = x_64;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_65: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_65: *mut uint32_t = resM_0.as_mut_ptr();
        *os_65.offset(i_10 as isize) = x_65;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_66: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_66: *mut uint32_t = resM_0.as_mut_ptr();
        *os_66.offset(i_10 as isize) = x_66;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_67: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_67: *mut uint32_t = resM_0.as_mut_ptr();
        *os_67.offset(i_10 as isize) = x_67;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_68: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_68: *mut uint32_t = resM_0.as_mut_ptr();
        *os_68.offset(i_10 as isize) = x_68;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_69: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_69: *mut uint32_t = resM_0.as_mut_ptr();
        *os_69.offset(i_10 as isize) = x_69;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_70: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
            | !c_7 & resM_0[i_10 as usize];
        let mut os_70: *mut uint32_t = resM_0.as_mut_ptr();
        *os_70.offset(i_10 as isize) = x_70;
        i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_8: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_8: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_11: uint32_t = 0 as libc::c_uint;
        let mut x_71: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_71: *mut uint32_t = resM_0.as_mut_ptr();
        *os_71.offset(i_11 as isize) = x_71;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_72: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_72: *mut uint32_t = resM_0.as_mut_ptr();
        *os_72.offset(i_11 as isize) = x_72;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_73: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_73: *mut uint32_t = resM_0.as_mut_ptr();
        *os_73.offset(i_11 as isize) = x_73;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_74: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_74: *mut uint32_t = resM_0.as_mut_ptr();
        *os_74.offset(i_11 as isize) = x_74;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_75: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_75: *mut uint32_t = resM_0.as_mut_ptr();
        *os_75.offset(i_11 as isize) = x_75;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_76: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_76: *mut uint32_t = resM_0.as_mut_ptr();
        *os_76.offset(i_11 as isize) = x_76;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_77: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_77: *mut uint32_t = resM_0.as_mut_ptr();
        *os_77.offset(i_11 as isize) = x_77;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_78: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
            | !c_8 & resM_0[i_11 as usize];
        let mut os_78: *mut uint32_t = resM_0.as_mut_ptr();
        *os_78.offset(i_11 as isize) = x_78;
        i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_9: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_9: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_12: uint32_t = 0 as libc::c_uint;
        let mut x_79: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_79: *mut uint32_t = resM_0.as_mut_ptr();
        *os_79.offset(i_12 as isize) = x_79;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_80: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_80: *mut uint32_t = resM_0.as_mut_ptr();
        *os_80.offset(i_12 as isize) = x_80;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_81: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_81: *mut uint32_t = resM_0.as_mut_ptr();
        *os_81.offset(i_12 as isize) = x_81;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_82: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_82: *mut uint32_t = resM_0.as_mut_ptr();
        *os_82.offset(i_12 as isize) = x_82;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_83: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_83: *mut uint32_t = resM_0.as_mut_ptr();
        *os_83.offset(i_12 as isize) = x_83;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_84: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_84: *mut uint32_t = resM_0.as_mut_ptr();
        *os_84.offset(i_12 as isize) = x_84;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_85: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_85: *mut uint32_t = resM_0.as_mut_ptr();
        *os_85.offset(i_12 as isize) = x_85;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_86: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
            | !c_9 & resM_0[i_12 as usize];
        let mut os_86: *mut uint32_t = resM_0.as_mut_ptr();
        *os_86.offset(i_12 as isize) = x_86;
        i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_10: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_10: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_13: uint32_t = 0 as libc::c_uint;
        let mut x_87: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_87: *mut uint32_t = resM_0.as_mut_ptr();
        *os_87.offset(i_13 as isize) = x_87;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_88: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_88: *mut uint32_t = resM_0.as_mut_ptr();
        *os_88.offset(i_13 as isize) = x_88;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_89: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_89: *mut uint32_t = resM_0.as_mut_ptr();
        *os_89.offset(i_13 as isize) = x_89;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_90: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_90: *mut uint32_t = resM_0.as_mut_ptr();
        *os_90.offset(i_13 as isize) = x_90;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_91: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_91: *mut uint32_t = resM_0.as_mut_ptr();
        *os_91.offset(i_13 as isize) = x_91;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_92: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_92: *mut uint32_t = resM_0.as_mut_ptr();
        *os_92.offset(i_13 as isize) = x_92;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_93: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_93: *mut uint32_t = resM_0.as_mut_ptr();
        *os_93.offset(i_13 as isize) = x_93;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_94: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
            | !c_10 & resM_0[i_13 as usize];
        let mut os_94: *mut uint32_t = resM_0.as_mut_ptr();
        *os_94.offset(i_13 as isize) = x_94;
        i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_11: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_11: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_14: uint32_t = 0 as libc::c_uint;
        let mut x_95: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_95: *mut uint32_t = resM_0.as_mut_ptr();
        *os_95.offset(i_14 as isize) = x_95;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_96: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_96: *mut uint32_t = resM_0.as_mut_ptr();
        *os_96.offset(i_14 as isize) = x_96;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_97: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_97: *mut uint32_t = resM_0.as_mut_ptr();
        *os_97.offset(i_14 as isize) = x_97;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_98: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_98: *mut uint32_t = resM_0.as_mut_ptr();
        *os_98.offset(i_14 as isize) = x_98;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_99: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_99: *mut uint32_t = resM_0.as_mut_ptr();
        *os_99.offset(i_14 as isize) = x_99;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_100: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_100: *mut uint32_t = resM_0.as_mut_ptr();
        *os_100.offset(i_14 as isize) = x_100;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_101: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_101: *mut uint32_t = resM_0.as_mut_ptr();
        *os_101.offset(i_14 as isize) = x_101;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_102: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
            | !c_11 & resM_0[i_14 as usize];
        let mut os_102: *mut uint32_t = resM_0.as_mut_ptr();
        *os_102.offset(i_14 as isize) = x_102;
        i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_12: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_12: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_15: uint32_t = 0 as libc::c_uint;
        let mut x_103: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_103: *mut uint32_t = resM_0.as_mut_ptr();
        *os_103.offset(i_15 as isize) = x_103;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_104: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_104: *mut uint32_t = resM_0.as_mut_ptr();
        *os_104.offset(i_15 as isize) = x_104;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_105: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_105: *mut uint32_t = resM_0.as_mut_ptr();
        *os_105.offset(i_15 as isize) = x_105;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_106: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_106: *mut uint32_t = resM_0.as_mut_ptr();
        *os_106.offset(i_15 as isize) = x_106;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_107: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_107: *mut uint32_t = resM_0.as_mut_ptr();
        *os_107.offset(i_15 as isize) = x_107;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_108: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_108: *mut uint32_t = resM_0.as_mut_ptr();
        *os_108.offset(i_15 as isize) = x_108;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_109: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_109: *mut uint32_t = resM_0.as_mut_ptr();
        *os_109.offset(i_15 as isize) = x_109;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_110: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
            | !c_12 & resM_0[i_15 as usize];
        let mut os_110: *mut uint32_t = resM_0.as_mut_ptr();
        *os_110.offset(i_15 as isize) = x_110;
        i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_13: uint32_t = FStar_UInt32_eq_mask(
            bits_c,
            i1_0.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_13: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_16: uint32_t = 0 as libc::c_uint;
        let mut x_111: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_111: *mut uint32_t = resM_0.as_mut_ptr();
        *os_111.offset(i_16 as isize) = x_111;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_112: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_112: *mut uint32_t = resM_0.as_mut_ptr();
        *os_112.offset(i_16 as isize) = x_112;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_113: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_113: *mut uint32_t = resM_0.as_mut_ptr();
        *os_113.offset(i_16 as isize) = x_113;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_114: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_114: *mut uint32_t = resM_0.as_mut_ptr();
        *os_114.offset(i_16 as isize) = x_114;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_115: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_115: *mut uint32_t = resM_0.as_mut_ptr();
        *os_115.offset(i_16 as isize) = x_115;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_116: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_116: *mut uint32_t = resM_0.as_mut_ptr();
        *os_116.offset(i_16 as isize) = x_116;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_117: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_117: *mut uint32_t = resM_0.as_mut_ptr();
        *os_117.offset(i_16 as isize) = x_117;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_118: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
            | !c_13 & resM_0[i_16 as usize];
        let mut os_118: *mut uint32_t = resM_0.as_mut_ptr();
        *os_118.offset(i_16 as isize) = x_118;
        i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    } else {
        let mut ctx_n_7: *mut uint32_t = ctx_0.as_mut_ptr();
        let mut ctx_r2_0: *mut uint32_t = ctx_0
            .as_mut_ptr()
            .offset(8 as libc::c_uint as isize);
        from(ctx_n_7, mu, ctx_r2_0, resM_0.as_mut_ptr());
    }
    let mut tmp0: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut i0_1: uint32_t = 0 as libc::c_uint;
    while i0_1 < bBits.wrapping_div(4 as libc::c_uint) {
        let mut i_17: uint32_t = 0 as libc::c_uint;
        let mut aM_copy_7: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_7.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_8: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_8, mu, aM_copy_7.as_mut_ptr(), resM_0.as_mut_ptr());
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_8: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_8.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_9: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_9, mu, aM_copy_8.as_mut_ptr(), resM_0.as_mut_ptr());
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_9: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_9.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_10: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_10, mu, aM_copy_9.as_mut_ptr(), resM_0.as_mut_ptr());
        i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_10: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_10.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_11: *mut uint32_t = ctx_0.as_mut_ptr();
        amont_sqr(ctx_n_11, mu, aM_copy_10.as_mut_ptr(), resM_0.as_mut_ptr());
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
            table.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i1_1: uint32_t = 0 as libc::c_uint;
        let mut c_14: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_14: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_18: uint32_t = 0 as libc::c_uint;
        let mut x_119: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_119: *mut uint32_t = tmp0.as_mut_ptr();
        *os_119.offset(i_18 as isize) = x_119;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_120: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_120: *mut uint32_t = tmp0.as_mut_ptr();
        *os_120.offset(i_18 as isize) = x_120;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_121: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_121: *mut uint32_t = tmp0.as_mut_ptr();
        *os_121.offset(i_18 as isize) = x_121;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_122: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_122: *mut uint32_t = tmp0.as_mut_ptr();
        *os_122.offset(i_18 as isize) = x_122;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_123: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_123: *mut uint32_t = tmp0.as_mut_ptr();
        *os_123.offset(i_18 as isize) = x_123;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_124: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_124: *mut uint32_t = tmp0.as_mut_ptr();
        *os_124.offset(i_18 as isize) = x_124;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_125: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_125: *mut uint32_t = tmp0.as_mut_ptr();
        *os_125.offset(i_18 as isize) = x_125;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_126: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
            | !c_14 & tmp0[i_18 as usize];
        let mut os_126: *mut uint32_t = tmp0.as_mut_ptr();
        *os_126.offset(i_18 as isize) = x_126;
        i_18 = (i_18 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_15: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_15: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_19: uint32_t = 0 as libc::c_uint;
        let mut x_127: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_127: *mut uint32_t = tmp0.as_mut_ptr();
        *os_127.offset(i_19 as isize) = x_127;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_128: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_128: *mut uint32_t = tmp0.as_mut_ptr();
        *os_128.offset(i_19 as isize) = x_128;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_129: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_129: *mut uint32_t = tmp0.as_mut_ptr();
        *os_129.offset(i_19 as isize) = x_129;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_130: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_130: *mut uint32_t = tmp0.as_mut_ptr();
        *os_130.offset(i_19 as isize) = x_130;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_131: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_131: *mut uint32_t = tmp0.as_mut_ptr();
        *os_131.offset(i_19 as isize) = x_131;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_132: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_132: *mut uint32_t = tmp0.as_mut_ptr();
        *os_132.offset(i_19 as isize) = x_132;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_133: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_133: *mut uint32_t = tmp0.as_mut_ptr();
        *os_133.offset(i_19 as isize) = x_133;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_134: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
            | !c_15 & tmp0[i_19 as usize];
        let mut os_134: *mut uint32_t = tmp0.as_mut_ptr();
        *os_134.offset(i_19 as isize) = x_134;
        i_19 = (i_19 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_16: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_16: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_20: uint32_t = 0 as libc::c_uint;
        let mut x_135: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_135: *mut uint32_t = tmp0.as_mut_ptr();
        *os_135.offset(i_20 as isize) = x_135;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_136: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_136: *mut uint32_t = tmp0.as_mut_ptr();
        *os_136.offset(i_20 as isize) = x_136;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_137: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_137: *mut uint32_t = tmp0.as_mut_ptr();
        *os_137.offset(i_20 as isize) = x_137;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_138: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_138: *mut uint32_t = tmp0.as_mut_ptr();
        *os_138.offset(i_20 as isize) = x_138;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_139: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_139: *mut uint32_t = tmp0.as_mut_ptr();
        *os_139.offset(i_20 as isize) = x_139;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_140: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_140: *mut uint32_t = tmp0.as_mut_ptr();
        *os_140.offset(i_20 as isize) = x_140;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_141: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_141: *mut uint32_t = tmp0.as_mut_ptr();
        *os_141.offset(i_20 as isize) = x_141;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_142: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
            | !c_16 & tmp0[i_20 as usize];
        let mut os_142: *mut uint32_t = tmp0.as_mut_ptr();
        *os_142.offset(i_20 as isize) = x_142;
        i_20 = (i_20 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_17: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_17: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_21: uint32_t = 0 as libc::c_uint;
        let mut x_143: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_143: *mut uint32_t = tmp0.as_mut_ptr();
        *os_143.offset(i_21 as isize) = x_143;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_144: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_144: *mut uint32_t = tmp0.as_mut_ptr();
        *os_144.offset(i_21 as isize) = x_144;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_145: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_145: *mut uint32_t = tmp0.as_mut_ptr();
        *os_145.offset(i_21 as isize) = x_145;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_146: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_146: *mut uint32_t = tmp0.as_mut_ptr();
        *os_146.offset(i_21 as isize) = x_146;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_147: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_147: *mut uint32_t = tmp0.as_mut_ptr();
        *os_147.offset(i_21 as isize) = x_147;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_148: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_148: *mut uint32_t = tmp0.as_mut_ptr();
        *os_148.offset(i_21 as isize) = x_148;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_149: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_149: *mut uint32_t = tmp0.as_mut_ptr();
        *os_149.offset(i_21 as isize) = x_149;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_150: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
            | !c_17 & tmp0[i_21 as usize];
        let mut os_150: *mut uint32_t = tmp0.as_mut_ptr();
        *os_150.offset(i_21 as isize) = x_150;
        i_21 = (i_21 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_18: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_18: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_22: uint32_t = 0 as libc::c_uint;
        let mut x_151: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_151: *mut uint32_t = tmp0.as_mut_ptr();
        *os_151.offset(i_22 as isize) = x_151;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_152: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_152: *mut uint32_t = tmp0.as_mut_ptr();
        *os_152.offset(i_22 as isize) = x_152;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_153: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_153: *mut uint32_t = tmp0.as_mut_ptr();
        *os_153.offset(i_22 as isize) = x_153;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_154: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_154: *mut uint32_t = tmp0.as_mut_ptr();
        *os_154.offset(i_22 as isize) = x_154;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_155: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_155: *mut uint32_t = tmp0.as_mut_ptr();
        *os_155.offset(i_22 as isize) = x_155;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_156: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_156: *mut uint32_t = tmp0.as_mut_ptr();
        *os_156.offset(i_22 as isize) = x_156;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_157: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_157: *mut uint32_t = tmp0.as_mut_ptr();
        *os_157.offset(i_22 as isize) = x_157;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_158: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
            | !c_18 & tmp0[i_22 as usize];
        let mut os_158: *mut uint32_t = tmp0.as_mut_ptr();
        *os_158.offset(i_22 as isize) = x_158;
        i_22 = (i_22 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_19: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_19: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_23: uint32_t = 0 as libc::c_uint;
        let mut x_159: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_159: *mut uint32_t = tmp0.as_mut_ptr();
        *os_159.offset(i_23 as isize) = x_159;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_160: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_160: *mut uint32_t = tmp0.as_mut_ptr();
        *os_160.offset(i_23 as isize) = x_160;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_161: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_161: *mut uint32_t = tmp0.as_mut_ptr();
        *os_161.offset(i_23 as isize) = x_161;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_162: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_162: *mut uint32_t = tmp0.as_mut_ptr();
        *os_162.offset(i_23 as isize) = x_162;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_163: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_163: *mut uint32_t = tmp0.as_mut_ptr();
        *os_163.offset(i_23 as isize) = x_163;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_164: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_164: *mut uint32_t = tmp0.as_mut_ptr();
        *os_164.offset(i_23 as isize) = x_164;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_165: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_165: *mut uint32_t = tmp0.as_mut_ptr();
        *os_165.offset(i_23 as isize) = x_165;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_166: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
            | !c_19 & tmp0[i_23 as usize];
        let mut os_166: *mut uint32_t = tmp0.as_mut_ptr();
        *os_166.offset(i_23 as isize) = x_166;
        i_23 = (i_23 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_20: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_20: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_24: uint32_t = 0 as libc::c_uint;
        let mut x_167: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_167: *mut uint32_t = tmp0.as_mut_ptr();
        *os_167.offset(i_24 as isize) = x_167;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_168: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_168: *mut uint32_t = tmp0.as_mut_ptr();
        *os_168.offset(i_24 as isize) = x_168;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_169: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_169: *mut uint32_t = tmp0.as_mut_ptr();
        *os_169.offset(i_24 as isize) = x_169;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_170: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_170: *mut uint32_t = tmp0.as_mut_ptr();
        *os_170.offset(i_24 as isize) = x_170;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_171: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_171: *mut uint32_t = tmp0.as_mut_ptr();
        *os_171.offset(i_24 as isize) = x_171;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_172: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_172: *mut uint32_t = tmp0.as_mut_ptr();
        *os_172.offset(i_24 as isize) = x_172;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_173: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_173: *mut uint32_t = tmp0.as_mut_ptr();
        *os_173.offset(i_24 as isize) = x_173;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_174: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
            | !c_20 & tmp0[i_24 as usize];
        let mut os_174: *mut uint32_t = tmp0.as_mut_ptr();
        *os_174.offset(i_24 as isize) = x_174;
        i_24 = (i_24 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_21: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_21: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_25: uint32_t = 0 as libc::c_uint;
        let mut x_175: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_175: *mut uint32_t = tmp0.as_mut_ptr();
        *os_175.offset(i_25 as isize) = x_175;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_176: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_176: *mut uint32_t = tmp0.as_mut_ptr();
        *os_176.offset(i_25 as isize) = x_176;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_177: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_177: *mut uint32_t = tmp0.as_mut_ptr();
        *os_177.offset(i_25 as isize) = x_177;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_178: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_178: *mut uint32_t = tmp0.as_mut_ptr();
        *os_178.offset(i_25 as isize) = x_178;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_179: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_179: *mut uint32_t = tmp0.as_mut_ptr();
        *os_179.offset(i_25 as isize) = x_179;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_180: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_180: *mut uint32_t = tmp0.as_mut_ptr();
        *os_180.offset(i_25 as isize) = x_180;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_181: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_181: *mut uint32_t = tmp0.as_mut_ptr();
        *os_181.offset(i_25 as isize) = x_181;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_182: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
            | !c_21 & tmp0[i_25 as usize];
        let mut os_182: *mut uint32_t = tmp0.as_mut_ptr();
        *os_182.offset(i_25 as isize) = x_182;
        i_25 = (i_25 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_22: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_22: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_26: uint32_t = 0 as libc::c_uint;
        let mut x_183: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_183: *mut uint32_t = tmp0.as_mut_ptr();
        *os_183.offset(i_26 as isize) = x_183;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_184: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_184: *mut uint32_t = tmp0.as_mut_ptr();
        *os_184.offset(i_26 as isize) = x_184;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_185: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_185: *mut uint32_t = tmp0.as_mut_ptr();
        *os_185.offset(i_26 as isize) = x_185;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_186: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_186: *mut uint32_t = tmp0.as_mut_ptr();
        *os_186.offset(i_26 as isize) = x_186;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_187: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_187: *mut uint32_t = tmp0.as_mut_ptr();
        *os_187.offset(i_26 as isize) = x_187;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_188: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_188: *mut uint32_t = tmp0.as_mut_ptr();
        *os_188.offset(i_26 as isize) = x_188;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_189: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_189: *mut uint32_t = tmp0.as_mut_ptr();
        *os_189.offset(i_26 as isize) = x_189;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_190: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
            | !c_22 & tmp0[i_26 as usize];
        let mut os_190: *mut uint32_t = tmp0.as_mut_ptr();
        *os_190.offset(i_26 as isize) = x_190;
        i_26 = (i_26 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_23: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_23: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_27: uint32_t = 0 as libc::c_uint;
        let mut x_191: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_191: *mut uint32_t = tmp0.as_mut_ptr();
        *os_191.offset(i_27 as isize) = x_191;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_192: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_192: *mut uint32_t = tmp0.as_mut_ptr();
        *os_192.offset(i_27 as isize) = x_192;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_193: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_193: *mut uint32_t = tmp0.as_mut_ptr();
        *os_193.offset(i_27 as isize) = x_193;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_194: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_194: *mut uint32_t = tmp0.as_mut_ptr();
        *os_194.offset(i_27 as isize) = x_194;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_195: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_195: *mut uint32_t = tmp0.as_mut_ptr();
        *os_195.offset(i_27 as isize) = x_195;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_196: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_196: *mut uint32_t = tmp0.as_mut_ptr();
        *os_196.offset(i_27 as isize) = x_196;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_197: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_197: *mut uint32_t = tmp0.as_mut_ptr();
        *os_197.offset(i_27 as isize) = x_197;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_198: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
            | !c_23 & tmp0[i_27 as usize];
        let mut os_198: *mut uint32_t = tmp0.as_mut_ptr();
        *os_198.offset(i_27 as isize) = x_198;
        i_27 = (i_27 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_24: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_24: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_28: uint32_t = 0 as libc::c_uint;
        let mut x_199: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_199: *mut uint32_t = tmp0.as_mut_ptr();
        *os_199.offset(i_28 as isize) = x_199;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_200: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_200: *mut uint32_t = tmp0.as_mut_ptr();
        *os_200.offset(i_28 as isize) = x_200;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_201: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_201: *mut uint32_t = tmp0.as_mut_ptr();
        *os_201.offset(i_28 as isize) = x_201;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_202: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_202: *mut uint32_t = tmp0.as_mut_ptr();
        *os_202.offset(i_28 as isize) = x_202;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_203: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_203: *mut uint32_t = tmp0.as_mut_ptr();
        *os_203.offset(i_28 as isize) = x_203;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_204: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_204: *mut uint32_t = tmp0.as_mut_ptr();
        *os_204.offset(i_28 as isize) = x_204;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_205: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_205: *mut uint32_t = tmp0.as_mut_ptr();
        *os_205.offset(i_28 as isize) = x_205;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_206: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
            | !c_24 & tmp0[i_28 as usize];
        let mut os_206: *mut uint32_t = tmp0.as_mut_ptr();
        *os_206.offset(i_28 as isize) = x_206;
        i_28 = (i_28 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_25: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_25: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_29: uint32_t = 0 as libc::c_uint;
        let mut x_207: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_207: *mut uint32_t = tmp0.as_mut_ptr();
        *os_207.offset(i_29 as isize) = x_207;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_208: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_208: *mut uint32_t = tmp0.as_mut_ptr();
        *os_208.offset(i_29 as isize) = x_208;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_209: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_209: *mut uint32_t = tmp0.as_mut_ptr();
        *os_209.offset(i_29 as isize) = x_209;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_210: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_210: *mut uint32_t = tmp0.as_mut_ptr();
        *os_210.offset(i_29 as isize) = x_210;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_211: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_211: *mut uint32_t = tmp0.as_mut_ptr();
        *os_211.offset(i_29 as isize) = x_211;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_212: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_212: *mut uint32_t = tmp0.as_mut_ptr();
        *os_212.offset(i_29 as isize) = x_212;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_213: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_213: *mut uint32_t = tmp0.as_mut_ptr();
        *os_213.offset(i_29 as isize) = x_213;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_214: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
            | !c_25 & tmp0[i_29 as usize];
        let mut os_214: *mut uint32_t = tmp0.as_mut_ptr();
        *os_214.offset(i_29 as isize) = x_214;
        i_29 = (i_29 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_26: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_26: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_30: uint32_t = 0 as libc::c_uint;
        let mut x_215: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_215: *mut uint32_t = tmp0.as_mut_ptr();
        *os_215.offset(i_30 as isize) = x_215;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_216: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_216: *mut uint32_t = tmp0.as_mut_ptr();
        *os_216.offset(i_30 as isize) = x_216;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_217: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_217: *mut uint32_t = tmp0.as_mut_ptr();
        *os_217.offset(i_30 as isize) = x_217;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_218: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_218: *mut uint32_t = tmp0.as_mut_ptr();
        *os_218.offset(i_30 as isize) = x_218;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_219: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_219: *mut uint32_t = tmp0.as_mut_ptr();
        *os_219.offset(i_30 as isize) = x_219;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_220: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_220: *mut uint32_t = tmp0.as_mut_ptr();
        *os_220.offset(i_30 as isize) = x_220;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_221: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_221: *mut uint32_t = tmp0.as_mut_ptr();
        *os_221.offset(i_30 as isize) = x_221;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_222: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
            | !c_26 & tmp0[i_30 as usize];
        let mut os_222: *mut uint32_t = tmp0.as_mut_ptr();
        *os_222.offset(i_30 as isize) = x_222;
        i_30 = (i_30 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_27: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_27: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_31: uint32_t = 0 as libc::c_uint;
        let mut x_223: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_223: *mut uint32_t = tmp0.as_mut_ptr();
        *os_223.offset(i_31 as isize) = x_223;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_224: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_224: *mut uint32_t = tmp0.as_mut_ptr();
        *os_224.offset(i_31 as isize) = x_224;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_225: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_225: *mut uint32_t = tmp0.as_mut_ptr();
        *os_225.offset(i_31 as isize) = x_225;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_226: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_226: *mut uint32_t = tmp0.as_mut_ptr();
        *os_226.offset(i_31 as isize) = x_226;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_227: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_227: *mut uint32_t = tmp0.as_mut_ptr();
        *os_227.offset(i_31 as isize) = x_227;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_228: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_228: *mut uint32_t = tmp0.as_mut_ptr();
        *os_228.offset(i_31 as isize) = x_228;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_229: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_229: *mut uint32_t = tmp0.as_mut_ptr();
        *os_229.offset(i_31 as isize) = x_229;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_230: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
            | !c_27 & tmp0[i_31 as usize];
        let mut os_230: *mut uint32_t = tmp0.as_mut_ptr();
        *os_230.offset(i_31 as isize) = x_230;
        i_31 = (i_31 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c_28: uint32_t = FStar_UInt32_eq_mask(
            bits_l,
            i1_1.wrapping_add(1 as libc::c_uint),
        );
        let mut res_j_28: *const uint32_t = table
            .as_mut_ptr()
            .offset(
                i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(8 as libc::c_uint)
                    as isize,
            );
        let mut i_32: uint32_t = 0 as libc::c_uint;
        let mut x_231: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_231: *mut uint32_t = tmp0.as_mut_ptr();
        *os_231.offset(i_32 as isize) = x_231;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_232: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_232: *mut uint32_t = tmp0.as_mut_ptr();
        *os_232.offset(i_32 as isize) = x_232;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_233: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_233: *mut uint32_t = tmp0.as_mut_ptr();
        *os_233.offset(i_32 as isize) = x_233;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_234: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_234: *mut uint32_t = tmp0.as_mut_ptr();
        *os_234.offset(i_32 as isize) = x_234;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_235: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_235: *mut uint32_t = tmp0.as_mut_ptr();
        *os_235.offset(i_32 as isize) = x_235;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_236: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_236: *mut uint32_t = tmp0.as_mut_ptr();
        *os_236.offset(i_32 as isize) = x_236;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_237: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_237: *mut uint32_t = tmp0.as_mut_ptr();
        *os_237.offset(i_32 as isize) = x_237;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_238: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
            | !c_28 & tmp0[i_32 as usize];
        let mut os_238: *mut uint32_t = tmp0.as_mut_ptr();
        *os_238.offset(i_32 as isize) = x_238;
        i_32 = (i_32 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut aM_copy_11: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        memcpy(
            aM_copy_11.as_mut_ptr() as *mut libc::c_void,
            resM_0.as_mut_ptr() as *const libc::c_void,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n_12: *mut uint32_t = ctx_0.as_mut_ptr();
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
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut r2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    precompr2(nBits, n, r2.as_mut_ptr());
    let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
        *n.offset(0 as libc::c_uint as isize),
    );
    exp_vartime_precomp(n, mu, r2.as_mut_ptr(), a, bBits, b, res);
}
#[inline]
unsafe extern "C" fn exp_consttime(
    mut nBits: uint32_t,
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut r2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    precompr2(nBits, n, r2.as_mut_ptr());
    let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
        *n.offset(0 as libc::c_uint as isize),
    );
    exp_consttime_precomp(n, mu, r2.as_mut_ptr(), a, bBits, b, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_exp_vartime(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) -> bool {
    let mut is_valid_m: uint32_t = exp_check(n, a, bBits, b);
    let mut nBits: uint32_t = (32 as libc::c_uint)
        .wrapping_mul(Hacl_Bignum_Lib_bn_get_top_index_u32(8 as libc::c_uint, n));
    if is_valid_m == 0xffffffff as libc::c_uint {
        exp_vartime(nBits, n, a, bBits, b, res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffff as libc::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_exp_consttime(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) -> bool {
    let mut is_valid_m: uint32_t = exp_check(n, a, bBits, b);
    let mut nBits: uint32_t = (32 as libc::c_uint)
        .wrapping_mul(Hacl_Bignum_Lib_bn_get_top_index_u32(8 as libc::c_uint, n));
    if is_valid_m == 0xffffffff as libc::c_uint {
        exp_consttime(nBits, n, a, bBits, b, res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffff as libc::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_inv_prime_vartime(
    mut n: *mut uint32_t,
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) -> bool {
    let mut one: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memset(
        one.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    one[0 as libc::c_uint as usize] = 1 as libc::c_uint;
    let mut bit0: uint32_t = *n.offset(0 as libc::c_uint as isize) & 1 as libc::c_uint;
    let mut m0: uint32_t = (0 as libc::c_uint).wrapping_sub(bit0);
    let mut acc0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint32_t = FStar_UInt32_eq_mask(one[i as usize], *n.offset(i as isize));
    let mut blt: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq & acc0 | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_0: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_0 & acc0 | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_1: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_1 & acc0 | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_2: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_2 & acc0 | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_3: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_3: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_3 & acc0 | !beq_3 & blt_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_4: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_4: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_4 & acc0 | !beq_4 & blt_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_5: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_5: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_5 & acc0 | !beq_5 & blt_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_6: uint32_t = FStar_UInt32_eq_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    let mut blt_6: uint32_t = !FStar_UInt32_gte_mask(
        one[i as usize],
        *n.offset(i as isize),
    );
    acc0 = beq_6 & acc0 | !beq_6 & blt_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m1: uint32_t = acc0;
    let mut m00: uint32_t = m0 & m1;
    let mut bn_zero: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut mask: uint32_t = 0xffffffff as libc::c_uint;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_0 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_1 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_2 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_3: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_3 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_4: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_4 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_5: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_5 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_6: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_0 as isize),
        bn_zero[i_0 as usize],
    );
    mask = uu____0_6 & mask;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut mask1: uint32_t = mask;
    let mut res10: uint32_t = mask1;
    let mut m10: uint32_t = res10;
    let mut acc: uint32_t = 0 as libc::c_uint;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut beq_7: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_7: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_7 & acc | !beq_7 & blt_7;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_8: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_8: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_8 & acc | !beq_8 & blt_8;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_9: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_9: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_9 & acc | !beq_9 & blt_9;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_10: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_10: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_10 & acc | !beq_10 & blt_10;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_11: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_11: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_11 & acc | !beq_11 & blt_11;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_12: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_12: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_12 & acc | !beq_12 & blt_12;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_13: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_13: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_13 & acc | !beq_13 & blt_13;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_14: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    let mut blt_14: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i_1 as isize),
        *n.offset(i_1 as isize),
    );
    acc = beq_14 & acc | !beq_14 & blt_14;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut m2: uint32_t = acc;
    let mut is_valid_m: uint32_t = m00 & !m10 & m2;
    let mut nBits: uint32_t = (32 as libc::c_uint)
        .wrapping_mul(Hacl_Bignum_Lib_bn_get_top_index_u32(8 as libc::c_uint, n));
    if is_valid_m == 0xffffffff as libc::c_uint {
        let mut n2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
        let mut c0: uint32_t = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
            0 as libc::c_uint,
            *n.offset(0 as libc::c_uint as isize),
            2 as libc::c_uint,
            n2.as_mut_ptr(),
        );
        let mut a1: *mut uint32_t = n.offset(1 as libc::c_uint as isize);
        let mut res1: *mut uint32_t = n2.as_mut_ptr().offset(1 as libc::c_uint as isize);
        let mut c: uint32_t = c0;
        let mut t1: uint32_t = *a1
            .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
        let mut res_i0: *mut uint32_t = res1
            .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0 as libc::c_uint, res_i0);
        let mut t10: uint32_t = *a1
            .offset(
                (4 as libc::c_uint)
                    .wrapping_mul(0 as libc::c_uint)
                    .wrapping_add(1 as libc::c_uint) as isize,
            );
        let mut res_i1: *mut uint32_t = res1
            .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
            .offset(1 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10, 0 as libc::c_uint, res_i1);
        let mut t11: uint32_t = *a1
            .offset(
                (4 as libc::c_uint)
                    .wrapping_mul(0 as libc::c_uint)
                    .wrapping_add(2 as libc::c_uint) as isize,
            );
        let mut res_i2: *mut uint32_t = res1
            .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
            .offset(2 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11, 0 as libc::c_uint, res_i2);
        let mut t12: uint32_t = *a1
            .offset(
                (4 as libc::c_uint)
                    .wrapping_mul(0 as libc::c_uint)
                    .wrapping_add(3 as libc::c_uint) as isize,
            );
        let mut res_i: *mut uint32_t = res1
            .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
            .offset(3 as libc::c_uint as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12, 0 as libc::c_uint, res_i);
        let mut i_2: uint32_t = 4 as libc::c_uint;
        let mut t1_0: uint32_t = *a1.offset(i_2 as isize);
        let mut res_i_0: *mut uint32_t = res1.offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_0, 0 as libc::c_uint, res_i_0);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t1_1: uint32_t = *a1.offset(i_2 as isize);
        let mut res_i_1: *mut uint32_t = res1.offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_1, 0 as libc::c_uint, res_i_1);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t1_2: uint32_t = *a1.offset(i_2 as isize);
        let mut res_i_2: *mut uint32_t = res1.offset(i_2 as isize);
        c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_2, 0 as libc::c_uint, res_i_2);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c1: uint32_t = c;
        let mut c2: uint32_t = c1;
        exp_vartime(nBits, n, a, 256 as libc::c_uint, n2.as_mut_ptr(), res);
    } else {
        memset(
            res as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (8 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
    }
    return is_valid_m == 0xffffffff as libc::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mont_ctx_init(
    mut n: *mut uint32_t,
) -> *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 {
    let mut r2: *mut uint32_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    let mut n1: *mut uint32_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    let mut r21: *mut uint32_t = r2;
    let mut n11: *mut uint32_t = n1;
    memcpy(
        n11 as *mut libc::c_void,
        n as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut nBits: uint32_t = (32 as libc::c_uint)
        .wrapping_mul(Hacl_Bignum_Lib_bn_get_top_index_u32(8 as libc::c_uint, n));
    precompr2(nBits, n, r21);
    let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
        *n.offset(0 as libc::c_uint as isize),
    );
    let mut res: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = {
        let mut init = Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s {
            len: 8 as libc::c_uint,
            n: n11,
            mu: mu,
            r2: r21,
        };
        init
    };
    let mut buf: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = malloc(
        ::core::mem::size_of::<Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32>()
            as libc::c_ulong,
    ) as *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32;
    *buf.offset(0 as libc::c_uint as isize) = res;
    return buf;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mont_ctx_free(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
) {
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    let mut n: *mut uint32_t = uu____0.n;
    let mut r2: *mut uint32_t = uu____0.r2;
    free(n as *mut libc::c_void);
    free(r2 as *mut libc::c_void);
    free(k as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut n: *mut uint32_t = (*k).n;
    let mut mu: uint32_t = (*k).mu;
    let mut r2: *mut uint32_t = (*k).r2;
    bn_slow_precomp(n, mu, r2, a, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_exp_vartime_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut n: *mut uint32_t = (*k).n;
    let mut mu: uint32_t = (*k).mu;
    let mut r2: *mut uint32_t = (*k).r2;
    exp_vartime_precomp(n, mu, r2, a, bBits, b, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_exp_consttime_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut a: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut n: *mut uint32_t = (*k).n;
    let mut mu: uint32_t = (*k).mu;
    let mut r2: *mut uint32_t = (*k).r2;
    exp_consttime_precomp(n, mu, r2, a, bBits, b, res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_mod_inv_prime_vartime_precomp(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut a: *mut uint32_t,
    mut res: *mut uint32_t,
) {
    let mut n: *mut uint32_t = (*k).n;
    let mut mu: uint32_t = (*k).mu;
    let mut r2: *mut uint32_t = (*k).r2;
    let mut n2: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut c0: uint32_t = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
        0 as libc::c_uint,
        *n.offset(0 as libc::c_uint as isize),
        2 as libc::c_uint,
        n2.as_mut_ptr(),
    );
    let mut a1: *mut uint32_t = n.offset(1 as libc::c_uint as isize);
    let mut res1: *mut uint32_t = n2.as_mut_ptr().offset(1 as libc::c_uint as isize);
    let mut c: uint32_t = c0;
    let mut t1: uint32_t = *a1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    let mut res_i0: *mut uint32_t = res1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1, 0 as libc::c_uint, res_i0);
    let mut t10: uint32_t = *a1
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint) as isize,
        );
    let mut res_i1: *mut uint32_t = res1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(1 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t10, 0 as libc::c_uint, res_i1);
    let mut t11: uint32_t = *a1
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(2 as libc::c_uint) as isize,
        );
    let mut res_i2: *mut uint32_t = res1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(2 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t11, 0 as libc::c_uint, res_i2);
    let mut t12: uint32_t = *a1
        .offset(
            (4 as libc::c_uint)
                .wrapping_mul(0 as libc::c_uint)
                .wrapping_add(3 as libc::c_uint) as isize,
        );
    let mut res_i: *mut uint32_t = res1
        .offset((4 as libc::c_uint).wrapping_mul(0 as libc::c_uint) as isize)
        .offset(3 as libc::c_uint as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t12, 0 as libc::c_uint, res_i);
    let mut i: uint32_t = 4 as libc::c_uint;
    let mut t1_0: uint32_t = *a1.offset(i as isize);
    let mut res_i_0: *mut uint32_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_0, 0 as libc::c_uint, res_i_0);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_1: uint32_t = *a1.offset(i as isize);
    let mut res_i_1: *mut uint32_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_1, 0 as libc::c_uint, res_i_1);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut t1_2: uint32_t = *a1.offset(i as isize);
    let mut res_i_2: *mut uint32_t = res1.offset(i as isize);
    c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(c, t1_2, 0 as libc::c_uint, res_i_2);
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut c1: uint32_t = c;
    let mut c2: uint32_t = c1;
    exp_vartime_precomp(n, mu, r2, a, 256 as libc::c_uint, n2.as_mut_ptr(), res);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_new_bn_from_bytes_be(
    mut len: uint32_t,
    mut b: *mut uint8_t,
) -> *mut uint32_t {
    if len == 0 as libc::c_uint
        || !(len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) <= 1073741823 as libc::c_uint)
    {
        return 0 as *mut uint32_t;
    }
    if len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(4 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256_32.c\0" as *const u8 as *const libc::c_char,
            1357 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut res: *mut uint32_t = calloc(
        len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    if res.is_null() {
        return res;
    }
    let mut res1: *mut uint32_t = res;
    let mut res2: *mut uint32_t = res1;
    let mut bnLen: uint32_t = len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(4 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut tmpLen: uint32_t = (4 as libc::c_uint).wrapping_mul(bnLen);
    if tmpLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256_32.c\0" as *const u8 as *const libc::c_char,
            1367 as libc::c_int,
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
        let mut u: uint32_t = if 0 != 0 {
            (load32(
                tmp
                    .as_mut_ptr()
                    .offset(
                        bnLen
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint)
                            .wrapping_mul(4 as libc::c_uint) as isize,
                    ),
            ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (load32(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(4 as libc::c_uint) as isize,
                        ),
                ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (load32(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(4 as libc::c_uint) as isize,
                        ),
                ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (load32(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(4 as libc::c_uint) as isize,
                        ),
                ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                load32(
                    tmp
                        .as_mut_ptr()
                        .offset(
                            bnLen
                                .wrapping_sub(i)
                                .wrapping_sub(1 as libc::c_uint)
                                .wrapping_mul(4 as libc::c_uint) as isize,
                        ),
                ),
            )
        };
        let mut x: uint32_t = u;
        let mut os: *mut uint32_t = res2;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    return res2;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_new_bn_from_bytes_le(
    mut len: uint32_t,
    mut b: *mut uint8_t,
) -> *mut uint32_t {
    if len == 0 as libc::c_uint
        || !(len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) <= 1073741823 as libc::c_uint)
    {
        return 0 as *mut uint32_t;
    }
    if len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(4 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256_32.c\0" as *const u8 as *const libc::c_char,
            1398 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut res: *mut uint32_t = calloc(
        len
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint) as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    if res.is_null() {
        return res;
    }
    let mut res1: *mut uint32_t = res;
    let mut res2: *mut uint32_t = res1;
    let mut bnLen: uint32_t = len
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(4 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut tmpLen: uint32_t = (4 as libc::c_uint).wrapping_mul(bnLen);
    if tmpLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Bignum256_32.c\0" as *const u8 as *const libc::c_char,
            1408 as libc::c_int,
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
            .wrapping_div(4 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint)
    {
        let mut bj: *mut uint8_t = tmp
            .as_mut_ptr()
            .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u: uint32_t = load32(bj);
        let mut r1: uint32_t = u;
        let mut x: uint32_t = r1;
        let mut os: *mut uint32_t = res2;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    return res2;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_bn_to_bytes_be(
    mut b: *mut uint32_t,
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
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*b
                .offset(
                    (8 as libc::c_uint).wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                        as isize,
                ) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(
                *b
                    .offset(
                        (8 as libc::c_uint)
                            .wrapping_sub(i)
                            .wrapping_sub(1 as libc::c_uint) as isize,
                    ),
            )
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_bn_to_bytes_le(
    mut b: *mut uint32_t,
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
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        res.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *b.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_lt_mask(
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
) -> uint32_t {
    let mut acc: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut beq: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq & acc | !beq & blt;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_0: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_0: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_0 & acc | !beq_0 & blt_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_1: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_1: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_1 & acc | !beq_1 & blt_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_2: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_2: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_2 & acc | !beq_2 & blt_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_3: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_3: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_3 & acc | !beq_3 & blt_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_4: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_4: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_4 & acc | !beq_4 & blt_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_5: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_5: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_5 & acc | !beq_5 & blt_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut beq_6: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    let mut blt_6: uint32_t = !FStar_UInt32_gte_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    acc = beq_6 & acc | !beq_6 & blt_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    return acc;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Bignum256_32_eq_mask(
    mut a: *mut uint32_t,
    mut b: *mut uint32_t,
) -> uint32_t {
    let mut mask: uint32_t = 0xffffffff as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut uu____0: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_0: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_0 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_1: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_1 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_2: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_2 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_3: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_3 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_4: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_4 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_5: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_5 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0_6: uint32_t = FStar_UInt32_eq_mask(
        *a.offset(i as isize),
        *b.offset(i as isize),
    );
    mask = uu____0_6 & mask;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut mask1: uint32_t = mask;
    return mask1;
}
