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
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
}
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type Hacl_Streaming_Types_error_code = uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_MAC_Poly1305_state_t_s {
    pub block_state: *mut uint64_t,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
    pub p_key: *mut uint8_t,
}
pub type Hacl_MAC_Poly1305_state_t = Hacl_MAC_Poly1305_state_t_s;
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
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_poly1305_init(
    mut ctx: *mut uint64_t,
    mut key: *mut uint8_t,
) {
    let mut acc: *mut uint64_t = ctx;
    let mut pre: *mut uint64_t = ctx.offset(5 as libc::c_uint as isize);
    let mut kr: *mut uint8_t = key;
    *acc.offset(0 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *acc.offset(1 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *acc.offset(2 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *acc.offset(3 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    *acc.offset(4 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
    let mut u0: uint64_t = load64(kr);
    let mut lo: uint64_t = u0;
    let mut u: uint64_t = load64(kr.offset(8 as libc::c_uint as isize));
    let mut hi: uint64_t = u;
    let mut mask0: uint64_t = 0xffffffc0fffffff as libc::c_ulonglong;
    let mut mask1: uint64_t = 0xffffffc0ffffffc as libc::c_ulonglong;
    let mut lo1: uint64_t = lo & mask0;
    let mut hi1: uint64_t = hi & mask1;
    let mut r: *mut uint64_t = pre;
    let mut r5: *mut uint64_t = pre.offset(5 as libc::c_uint as isize);
    let mut rn: *mut uint64_t = pre.offset(10 as libc::c_uint as isize);
    let mut rn_5: *mut uint64_t = pre.offset(15 as libc::c_uint as isize);
    let mut r_vec0: uint64_t = lo1;
    let mut r_vec1: uint64_t = hi1;
    let mut f00: uint64_t = r_vec0 & 0x3ffffff as libc::c_ulonglong;
    let mut f10: uint64_t = r_vec0 >> 26 as libc::c_uint
        & 0x3ffffff as libc::c_ulonglong;
    let mut f20: uint64_t = r_vec0 >> 52 as libc::c_uint
        | (r_vec1 & 0x3fff as libc::c_ulonglong) << 12 as libc::c_uint;
    let mut f30: uint64_t = r_vec1 >> 14 as libc::c_uint
        & 0x3ffffff as libc::c_ulonglong;
    let mut f40: uint64_t = r_vec1 >> 40 as libc::c_uint;
    let mut f0: uint64_t = f00;
    let mut f1: uint64_t = f10;
    let mut f2: uint64_t = f20;
    let mut f3: uint64_t = f30;
    let mut f4: uint64_t = f40;
    *r.offset(0 as libc::c_uint as isize) = f0;
    *r.offset(1 as libc::c_uint as isize) = f1;
    *r.offset(2 as libc::c_uint as isize) = f2;
    *r.offset(3 as libc::c_uint as isize) = f3;
    *r.offset(4 as libc::c_uint as isize) = f4;
    let mut f200: uint64_t = *r.offset(0 as libc::c_uint as isize);
    let mut f21: uint64_t = *r.offset(1 as libc::c_uint as isize);
    let mut f22: uint64_t = *r.offset(2 as libc::c_uint as isize);
    let mut f23: uint64_t = *r.offset(3 as libc::c_uint as isize);
    let mut f24: uint64_t = *r.offset(4 as libc::c_uint as isize);
    *r5.offset(0 as libc::c_uint as isize) = f200.wrapping_mul(5 as libc::c_ulonglong);
    *r5.offset(1 as libc::c_uint as isize) = f21.wrapping_mul(5 as libc::c_ulonglong);
    *r5.offset(2 as libc::c_uint as isize) = f22.wrapping_mul(5 as libc::c_ulonglong);
    *r5.offset(3 as libc::c_uint as isize) = f23.wrapping_mul(5 as libc::c_ulonglong);
    *r5.offset(4 as libc::c_uint as isize) = f24.wrapping_mul(5 as libc::c_ulonglong);
    *rn.offset(0 as libc::c_uint as isize) = *r.offset(0 as libc::c_uint as isize);
    *rn.offset(1 as libc::c_uint as isize) = *r.offset(1 as libc::c_uint as isize);
    *rn.offset(2 as libc::c_uint as isize) = *r.offset(2 as libc::c_uint as isize);
    *rn.offset(3 as libc::c_uint as isize) = *r.offset(3 as libc::c_uint as isize);
    *rn.offset(4 as libc::c_uint as isize) = *r.offset(4 as libc::c_uint as isize);
    *rn_5.offset(0 as libc::c_uint as isize) = *r5.offset(0 as libc::c_uint as isize);
    *rn_5.offset(1 as libc::c_uint as isize) = *r5.offset(1 as libc::c_uint as isize);
    *rn_5.offset(2 as libc::c_uint as isize) = *r5.offset(2 as libc::c_uint as isize);
    *rn_5.offset(3 as libc::c_uint as isize) = *r5.offset(3 as libc::c_uint as isize);
    *rn_5.offset(4 as libc::c_uint as isize) = *r5.offset(4 as libc::c_uint as isize);
}
unsafe extern "C" fn poly1305_update(
    mut ctx: *mut uint64_t,
    mut len: uint32_t,
    mut text: *mut uint8_t,
) {
    let mut pre: *mut uint64_t = ctx.offset(5 as libc::c_uint as isize);
    let mut acc: *mut uint64_t = ctx;
    let mut nb: uint32_t = len.wrapping_div(16 as libc::c_uint);
    let mut rem: uint32_t = len.wrapping_rem(16 as libc::c_uint);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < nb {
        let mut block: *mut uint8_t = text
            .offset(i.wrapping_mul(16 as libc::c_uint) as isize);
        let mut e: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        let mut u0: uint64_t = load64(block);
        let mut lo: uint64_t = u0;
        let mut u: uint64_t = load64(block.offset(8 as libc::c_uint as isize));
        let mut hi: uint64_t = u;
        let mut f0: uint64_t = lo;
        let mut f1: uint64_t = hi;
        let mut f010: uint64_t = f0 & 0x3ffffff as libc::c_ulonglong;
        let mut f110: uint64_t = f0 >> 26 as libc::c_uint
            & 0x3ffffff as libc::c_ulonglong;
        let mut f20: uint64_t = f0 >> 52 as libc::c_uint
            | (f1 & 0x3fff as libc::c_ulonglong) << 12 as libc::c_uint;
        let mut f30: uint64_t = f1 >> 14 as libc::c_uint
            & 0x3ffffff as libc::c_ulonglong;
        let mut f40: uint64_t = f1 >> 40 as libc::c_uint;
        let mut f01: uint64_t = f010;
        let mut f111: uint64_t = f110;
        let mut f2: uint64_t = f20;
        let mut f3: uint64_t = f30;
        let mut f41: uint64_t = f40;
        e[0 as libc::c_uint as usize] = f01;
        e[1 as libc::c_uint as usize] = f111;
        e[2 as libc::c_uint as usize] = f2;
        e[3 as libc::c_uint as usize] = f3;
        e[4 as libc::c_uint as usize] = f41;
        let mut b: uint64_t = 0x1000000 as libc::c_ulonglong;
        let mut mask: uint64_t = b;
        let mut f4: uint64_t = e[4 as libc::c_uint as usize];
        e[4 as libc::c_uint as usize] = f4 | mask;
        let mut r: *mut uint64_t = pre;
        let mut r5: *mut uint64_t = pre.offset(5 as libc::c_uint as isize);
        let mut r0: uint64_t = *r.offset(0 as libc::c_uint as isize);
        let mut r1: uint64_t = *r.offset(1 as libc::c_uint as isize);
        let mut r2: uint64_t = *r.offset(2 as libc::c_uint as isize);
        let mut r3: uint64_t = *r.offset(3 as libc::c_uint as isize);
        let mut r4: uint64_t = *r.offset(4 as libc::c_uint as isize);
        let mut r51: uint64_t = *r5.offset(1 as libc::c_uint as isize);
        let mut r52: uint64_t = *r5.offset(2 as libc::c_uint as isize);
        let mut r53: uint64_t = *r5.offset(3 as libc::c_uint as isize);
        let mut r54: uint64_t = *r5.offset(4 as libc::c_uint as isize);
        let mut f10: uint64_t = e[0 as libc::c_uint as usize];
        let mut f11: uint64_t = e[1 as libc::c_uint as usize];
        let mut f12: uint64_t = e[2 as libc::c_uint as usize];
        let mut f13: uint64_t = e[3 as libc::c_uint as usize];
        let mut f14: uint64_t = e[4 as libc::c_uint as usize];
        let mut a0: uint64_t = *acc.offset(0 as libc::c_uint as isize);
        let mut a1: uint64_t = *acc.offset(1 as libc::c_uint as isize);
        let mut a2: uint64_t = *acc.offset(2 as libc::c_uint as isize);
        let mut a3: uint64_t = *acc.offset(3 as libc::c_uint as isize);
        let mut a4: uint64_t = *acc.offset(4 as libc::c_uint as isize);
        let mut a01: uint64_t = a0.wrapping_add(f10);
        let mut a11: uint64_t = a1.wrapping_add(f11);
        let mut a21: uint64_t = a2.wrapping_add(f12);
        let mut a31: uint64_t = a3.wrapping_add(f13);
        let mut a41: uint64_t = a4.wrapping_add(f14);
        let mut a02: uint64_t = r0 * a01;
        let mut a12: uint64_t = r1 * a01;
        let mut a22: uint64_t = r2 * a01;
        let mut a32: uint64_t = r3 * a01;
        let mut a42: uint64_t = r4 * a01;
        let mut a03: uint64_t = a02.wrapping_add(r54 * a11);
        let mut a13: uint64_t = a12.wrapping_add(r0 * a11);
        let mut a23: uint64_t = a22.wrapping_add(r1 * a11);
        let mut a33: uint64_t = a32.wrapping_add(r2 * a11);
        let mut a43: uint64_t = a42.wrapping_add(r3 * a11);
        let mut a04: uint64_t = a03.wrapping_add(r53 * a21);
        let mut a14: uint64_t = a13.wrapping_add(r54 * a21);
        let mut a24: uint64_t = a23.wrapping_add(r0 * a21);
        let mut a34: uint64_t = a33.wrapping_add(r1 * a21);
        let mut a44: uint64_t = a43.wrapping_add(r2 * a21);
        let mut a05: uint64_t = a04.wrapping_add(r52 * a31);
        let mut a15: uint64_t = a14.wrapping_add(r53 * a31);
        let mut a25: uint64_t = a24.wrapping_add(r54 * a31);
        let mut a35: uint64_t = a34.wrapping_add(r0 * a31);
        let mut a45: uint64_t = a44.wrapping_add(r1 * a31);
        let mut a06: uint64_t = a05.wrapping_add(r51 * a41);
        let mut a16: uint64_t = a15.wrapping_add(r52 * a41);
        let mut a26: uint64_t = a25.wrapping_add(r53 * a41);
        let mut a36: uint64_t = a35.wrapping_add(r54 * a41);
        let mut a46: uint64_t = a45.wrapping_add(r0 * a41);
        let mut t0: uint64_t = a06;
        let mut t1: uint64_t = a16;
        let mut t2: uint64_t = a26;
        let mut t3: uint64_t = a36;
        let mut t4: uint64_t = a46;
        let mut mask26: uint64_t = 0x3ffffff as libc::c_ulonglong;
        let mut z0: uint64_t = t0 >> 26 as libc::c_uint;
        let mut z1: uint64_t = t3 >> 26 as libc::c_uint;
        let mut x0: uint64_t = t0 & mask26;
        let mut x3: uint64_t = t3 & mask26;
        let mut x1: uint64_t = t1.wrapping_add(z0);
        let mut x4: uint64_t = t4.wrapping_add(z1);
        let mut z01: uint64_t = x1 >> 26 as libc::c_uint;
        let mut z11: uint64_t = x4 >> 26 as libc::c_uint;
        let mut t: uint64_t = z11 << 2 as libc::c_uint;
        let mut z12: uint64_t = z11.wrapping_add(t);
        let mut x11: uint64_t = x1 & mask26;
        let mut x41: uint64_t = x4 & mask26;
        let mut x2: uint64_t = t2.wrapping_add(z01);
        let mut x01: uint64_t = x0.wrapping_add(z12);
        let mut z02: uint64_t = x2 >> 26 as libc::c_uint;
        let mut z13: uint64_t = x01 >> 26 as libc::c_uint;
        let mut x21: uint64_t = x2 & mask26;
        let mut x02: uint64_t = x01 & mask26;
        let mut x31: uint64_t = x3.wrapping_add(z02);
        let mut x12: uint64_t = x11.wrapping_add(z13);
        let mut z03: uint64_t = x31 >> 26 as libc::c_uint;
        let mut x32: uint64_t = x31 & mask26;
        let mut x42: uint64_t = x41.wrapping_add(z03);
        let mut o0: uint64_t = x02;
        let mut o1: uint64_t = x12;
        let mut o2: uint64_t = x21;
        let mut o3: uint64_t = x32;
        let mut o4: uint64_t = x42;
        *acc.offset(0 as libc::c_uint as isize) = o0;
        *acc.offset(1 as libc::c_uint as isize) = o1;
        *acc.offset(2 as libc::c_uint as isize) = o2;
        *acc.offset(3 as libc::c_uint as isize) = o3;
        *acc.offset(4 as libc::c_uint as isize) = o4;
        i = i.wrapping_add(1);
        i;
    }
    if rem > 0 as libc::c_uint {
        let mut last: *mut uint8_t = text
            .offset(nb.wrapping_mul(16 as libc::c_uint) as isize);
        let mut e_0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        let mut tmp: [uint8_t; 16] = [
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
        ];
        memcpy(
            tmp.as_mut_ptr() as *mut libc::c_void,
            last as *const libc::c_void,
            (rem as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut u0_0: uint64_t = load64(tmp.as_mut_ptr());
        let mut lo_0: uint64_t = u0_0;
        let mut u_0: uint64_t = load64(
            tmp.as_mut_ptr().offset(8 as libc::c_uint as isize),
        );
        let mut hi_0: uint64_t = u_0;
        let mut f0_0: uint64_t = lo_0;
        let mut f1_0: uint64_t = hi_0;
        let mut f010_0: uint64_t = f0_0 & 0x3ffffff as libc::c_ulonglong;
        let mut f110_0: uint64_t = f0_0 >> 26 as libc::c_uint
            & 0x3ffffff as libc::c_ulonglong;
        let mut f20_0: uint64_t = f0_0 >> 52 as libc::c_uint
            | (f1_0 & 0x3fff as libc::c_ulonglong) << 12 as libc::c_uint;
        let mut f30_0: uint64_t = f1_0 >> 14 as libc::c_uint
            & 0x3ffffff as libc::c_ulonglong;
        let mut f40_0: uint64_t = f1_0 >> 40 as libc::c_uint;
        let mut f01_0: uint64_t = f010_0;
        let mut f111_0: uint64_t = f110_0;
        let mut f2_0: uint64_t = f20_0;
        let mut f3_0: uint64_t = f30_0;
        let mut f4_0: uint64_t = f40_0;
        e_0[0 as libc::c_uint as usize] = f01_0;
        e_0[1 as libc::c_uint as usize] = f111_0;
        e_0[2 as libc::c_uint as usize] = f2_0;
        e_0[3 as libc::c_uint as usize] = f3_0;
        e_0[4 as libc::c_uint as usize] = f4_0;
        let mut b_0: uint64_t = (1 as libc::c_ulonglong)
            << rem.wrapping_mul(8 as libc::c_uint).wrapping_rem(26 as libc::c_uint);
        let mut mask_0: uint64_t = b_0;
        let mut fi: uint64_t = e_0[rem
            .wrapping_mul(8 as libc::c_uint)
            .wrapping_div(26 as libc::c_uint) as usize];
        e_0[rem.wrapping_mul(8 as libc::c_uint).wrapping_div(26 as libc::c_uint)
            as usize] = fi | mask_0;
        let mut r_0: *mut uint64_t = pre;
        let mut r5_0: *mut uint64_t = pre.offset(5 as libc::c_uint as isize);
        let mut r0_0: uint64_t = *r_0.offset(0 as libc::c_uint as isize);
        let mut r1_0: uint64_t = *r_0.offset(1 as libc::c_uint as isize);
        let mut r2_0: uint64_t = *r_0.offset(2 as libc::c_uint as isize);
        let mut r3_0: uint64_t = *r_0.offset(3 as libc::c_uint as isize);
        let mut r4_0: uint64_t = *r_0.offset(4 as libc::c_uint as isize);
        let mut r51_0: uint64_t = *r5_0.offset(1 as libc::c_uint as isize);
        let mut r52_0: uint64_t = *r5_0.offset(2 as libc::c_uint as isize);
        let mut r53_0: uint64_t = *r5_0.offset(3 as libc::c_uint as isize);
        let mut r54_0: uint64_t = *r5_0.offset(4 as libc::c_uint as isize);
        let mut f10_0: uint64_t = e_0[0 as libc::c_uint as usize];
        let mut f11_0: uint64_t = e_0[1 as libc::c_uint as usize];
        let mut f12_0: uint64_t = e_0[2 as libc::c_uint as usize];
        let mut f13_0: uint64_t = e_0[3 as libc::c_uint as usize];
        let mut f14_0: uint64_t = e_0[4 as libc::c_uint as usize];
        let mut a0_0: uint64_t = *acc.offset(0 as libc::c_uint as isize);
        let mut a1_0: uint64_t = *acc.offset(1 as libc::c_uint as isize);
        let mut a2_0: uint64_t = *acc.offset(2 as libc::c_uint as isize);
        let mut a3_0: uint64_t = *acc.offset(3 as libc::c_uint as isize);
        let mut a4_0: uint64_t = *acc.offset(4 as libc::c_uint as isize);
        let mut a01_0: uint64_t = a0_0.wrapping_add(f10_0);
        let mut a11_0: uint64_t = a1_0.wrapping_add(f11_0);
        let mut a21_0: uint64_t = a2_0.wrapping_add(f12_0);
        let mut a31_0: uint64_t = a3_0.wrapping_add(f13_0);
        let mut a41_0: uint64_t = a4_0.wrapping_add(f14_0);
        let mut a02_0: uint64_t = r0_0 * a01_0;
        let mut a12_0: uint64_t = r1_0 * a01_0;
        let mut a22_0: uint64_t = r2_0 * a01_0;
        let mut a32_0: uint64_t = r3_0 * a01_0;
        let mut a42_0: uint64_t = r4_0 * a01_0;
        let mut a03_0: uint64_t = a02_0.wrapping_add(r54_0 * a11_0);
        let mut a13_0: uint64_t = a12_0.wrapping_add(r0_0 * a11_0);
        let mut a23_0: uint64_t = a22_0.wrapping_add(r1_0 * a11_0);
        let mut a33_0: uint64_t = a32_0.wrapping_add(r2_0 * a11_0);
        let mut a43_0: uint64_t = a42_0.wrapping_add(r3_0 * a11_0);
        let mut a04_0: uint64_t = a03_0.wrapping_add(r53_0 * a21_0);
        let mut a14_0: uint64_t = a13_0.wrapping_add(r54_0 * a21_0);
        let mut a24_0: uint64_t = a23_0.wrapping_add(r0_0 * a21_0);
        let mut a34_0: uint64_t = a33_0.wrapping_add(r1_0 * a21_0);
        let mut a44_0: uint64_t = a43_0.wrapping_add(r2_0 * a21_0);
        let mut a05_0: uint64_t = a04_0.wrapping_add(r52_0 * a31_0);
        let mut a15_0: uint64_t = a14_0.wrapping_add(r53_0 * a31_0);
        let mut a25_0: uint64_t = a24_0.wrapping_add(r54_0 * a31_0);
        let mut a35_0: uint64_t = a34_0.wrapping_add(r0_0 * a31_0);
        let mut a45_0: uint64_t = a44_0.wrapping_add(r1_0 * a31_0);
        let mut a06_0: uint64_t = a05_0.wrapping_add(r51_0 * a41_0);
        let mut a16_0: uint64_t = a15_0.wrapping_add(r52_0 * a41_0);
        let mut a26_0: uint64_t = a25_0.wrapping_add(r53_0 * a41_0);
        let mut a36_0: uint64_t = a35_0.wrapping_add(r54_0 * a41_0);
        let mut a46_0: uint64_t = a45_0.wrapping_add(r0_0 * a41_0);
        let mut t0_0: uint64_t = a06_0;
        let mut t1_0: uint64_t = a16_0;
        let mut t2_0: uint64_t = a26_0;
        let mut t3_0: uint64_t = a36_0;
        let mut t4_0: uint64_t = a46_0;
        let mut mask26_0: uint64_t = 0x3ffffff as libc::c_ulonglong;
        let mut z0_0: uint64_t = t0_0 >> 26 as libc::c_uint;
        let mut z1_0: uint64_t = t3_0 >> 26 as libc::c_uint;
        let mut x0_0: uint64_t = t0_0 & mask26_0;
        let mut x3_0: uint64_t = t3_0 & mask26_0;
        let mut x1_0: uint64_t = t1_0.wrapping_add(z0_0);
        let mut x4_0: uint64_t = t4_0.wrapping_add(z1_0);
        let mut z01_0: uint64_t = x1_0 >> 26 as libc::c_uint;
        let mut z11_0: uint64_t = x4_0 >> 26 as libc::c_uint;
        let mut t_0: uint64_t = z11_0 << 2 as libc::c_uint;
        let mut z12_0: uint64_t = z11_0.wrapping_add(t_0);
        let mut x11_0: uint64_t = x1_0 & mask26_0;
        let mut x41_0: uint64_t = x4_0 & mask26_0;
        let mut x2_0: uint64_t = t2_0.wrapping_add(z01_0);
        let mut x01_0: uint64_t = x0_0.wrapping_add(z12_0);
        let mut z02_0: uint64_t = x2_0 >> 26 as libc::c_uint;
        let mut z13_0: uint64_t = x01_0 >> 26 as libc::c_uint;
        let mut x21_0: uint64_t = x2_0 & mask26_0;
        let mut x02_0: uint64_t = x01_0 & mask26_0;
        let mut x31_0: uint64_t = x3_0.wrapping_add(z02_0);
        let mut x12_0: uint64_t = x11_0.wrapping_add(z13_0);
        let mut z03_0: uint64_t = x31_0 >> 26 as libc::c_uint;
        let mut x32_0: uint64_t = x31_0 & mask26_0;
        let mut x42_0: uint64_t = x41_0.wrapping_add(z03_0);
        let mut o0_0: uint64_t = x02_0;
        let mut o1_0: uint64_t = x12_0;
        let mut o2_0: uint64_t = x21_0;
        let mut o3_0: uint64_t = x32_0;
        let mut o4_0: uint64_t = x42_0;
        *acc.offset(0 as libc::c_uint as isize) = o0_0;
        *acc.offset(1 as libc::c_uint as isize) = o1_0;
        *acc.offset(2 as libc::c_uint as isize) = o2_0;
        *acc.offset(3 as libc::c_uint as isize) = o3_0;
        *acc.offset(4 as libc::c_uint as isize) = o4_0;
        return;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_poly1305_finish(
    mut tag: *mut uint8_t,
    mut key: *mut uint8_t,
    mut ctx: *mut uint64_t,
) {
    let mut acc: *mut uint64_t = ctx;
    let mut ks: *mut uint8_t = key.offset(16 as libc::c_uint as isize);
    let mut f0: uint64_t = *acc.offset(0 as libc::c_uint as isize);
    let mut f13: uint64_t = *acc.offset(1 as libc::c_uint as isize);
    let mut f23: uint64_t = *acc.offset(2 as libc::c_uint as isize);
    let mut f33: uint64_t = *acc.offset(3 as libc::c_uint as isize);
    let mut f40: uint64_t = *acc.offset(4 as libc::c_uint as isize);
    let mut l0: uint64_t = f0.wrapping_add(0 as libc::c_ulonglong);
    let mut tmp00: uint64_t = l0 & 0x3ffffff as libc::c_ulonglong;
    let mut c00: uint64_t = l0 >> 26 as libc::c_uint;
    let mut l1: uint64_t = f13.wrapping_add(c00);
    let mut tmp10: uint64_t = l1 & 0x3ffffff as libc::c_ulonglong;
    let mut c10: uint64_t = l1 >> 26 as libc::c_uint;
    let mut l2: uint64_t = f23.wrapping_add(c10);
    let mut tmp20: uint64_t = l2 & 0x3ffffff as libc::c_ulonglong;
    let mut c20: uint64_t = l2 >> 26 as libc::c_uint;
    let mut l3: uint64_t = f33.wrapping_add(c20);
    let mut tmp30: uint64_t = l3 & 0x3ffffff as libc::c_ulonglong;
    let mut c30: uint64_t = l3 >> 26 as libc::c_uint;
    let mut l4: uint64_t = f40.wrapping_add(c30);
    let mut tmp40: uint64_t = l4 & 0x3ffffff as libc::c_ulonglong;
    let mut c40: uint64_t = l4 >> 26 as libc::c_uint;
    let mut f010: uint64_t = tmp00
        .wrapping_add(c40.wrapping_mul(5 as libc::c_ulonglong));
    let mut f110: uint64_t = tmp10;
    let mut f210: uint64_t = tmp20;
    let mut f310: uint64_t = tmp30;
    let mut f410: uint64_t = tmp40;
    let mut l: uint64_t = f010.wrapping_add(0 as libc::c_ulonglong);
    let mut tmp0: uint64_t = l & 0x3ffffff as libc::c_ulonglong;
    let mut c0: uint64_t = l >> 26 as libc::c_uint;
    let mut l5: uint64_t = f110.wrapping_add(c0);
    let mut tmp1: uint64_t = l5 & 0x3ffffff as libc::c_ulonglong;
    let mut c1: uint64_t = l5 >> 26 as libc::c_uint;
    let mut l6: uint64_t = f210.wrapping_add(c1);
    let mut tmp2: uint64_t = l6 & 0x3ffffff as libc::c_ulonglong;
    let mut c2: uint64_t = l6 >> 26 as libc::c_uint;
    let mut l7: uint64_t = f310.wrapping_add(c2);
    let mut tmp3: uint64_t = l7 & 0x3ffffff as libc::c_ulonglong;
    let mut c3: uint64_t = l7 >> 26 as libc::c_uint;
    let mut l8: uint64_t = f410.wrapping_add(c3);
    let mut tmp4: uint64_t = l8 & 0x3ffffff as libc::c_ulonglong;
    let mut c4: uint64_t = l8 >> 26 as libc::c_uint;
    let mut f02: uint64_t = tmp0.wrapping_add(c4.wrapping_mul(5 as libc::c_ulonglong));
    let mut f12: uint64_t = tmp1;
    let mut f22: uint64_t = tmp2;
    let mut f32: uint64_t = tmp3;
    let mut f42: uint64_t = tmp4;
    let mut mh: uint64_t = 0x3ffffff as libc::c_ulonglong;
    let mut ml: uint64_t = 0x3fffffb as libc::c_ulonglong;
    let mut mask: uint64_t = FStar_UInt64_eq_mask(f42, mh);
    let mut mask1: uint64_t = mask & FStar_UInt64_eq_mask(f32, mh);
    let mut mask2: uint64_t = mask1 & FStar_UInt64_eq_mask(f22, mh);
    let mut mask3: uint64_t = mask2 & FStar_UInt64_eq_mask(f12, mh);
    let mut mask4: uint64_t = mask3 & !!FStar_UInt64_gte_mask(f02, ml);
    let mut ph: uint64_t = mask4 & mh;
    let mut pl: uint64_t = mask4 & ml;
    let mut o0: uint64_t = f02.wrapping_sub(pl);
    let mut o1: uint64_t = f12.wrapping_sub(ph);
    let mut o2: uint64_t = f22.wrapping_sub(ph);
    let mut o3: uint64_t = f32.wrapping_sub(ph);
    let mut o4: uint64_t = f42.wrapping_sub(ph);
    let mut f011: uint64_t = o0;
    let mut f111: uint64_t = o1;
    let mut f211: uint64_t = o2;
    let mut f311: uint64_t = o3;
    let mut f411: uint64_t = o4;
    *acc.offset(0 as libc::c_uint as isize) = f011;
    *acc.offset(1 as libc::c_uint as isize) = f111;
    *acc.offset(2 as libc::c_uint as isize) = f211;
    *acc.offset(3 as libc::c_uint as isize) = f311;
    *acc.offset(4 as libc::c_uint as isize) = f411;
    let mut f00: uint64_t = *acc.offset(0 as libc::c_uint as isize);
    let mut f1: uint64_t = *acc.offset(1 as libc::c_uint as isize);
    let mut f2: uint64_t = *acc.offset(2 as libc::c_uint as isize);
    let mut f3: uint64_t = *acc.offset(3 as libc::c_uint as isize);
    let mut f4: uint64_t = *acc.offset(4 as libc::c_uint as isize);
    let mut f01: uint64_t = f00;
    let mut f112: uint64_t = f1;
    let mut f212: uint64_t = f2;
    let mut f312: uint64_t = f3;
    let mut f41: uint64_t = f4;
    let mut lo: uint64_t = f01 | f112 << 26 as libc::c_uint | f212 << 52 as libc::c_uint;
    let mut hi: uint64_t = f212 >> 12 as libc::c_uint | f312 << 14 as libc::c_uint
        | f41 << 40 as libc::c_uint;
    let mut f10: uint64_t = lo;
    let mut f11: uint64_t = hi;
    let mut u0: uint64_t = load64(ks);
    let mut lo0: uint64_t = u0;
    let mut u: uint64_t = load64(ks.offset(8 as libc::c_uint as isize));
    let mut hi0: uint64_t = u;
    let mut f20: uint64_t = lo0;
    let mut f21: uint64_t = hi0;
    let mut r0: uint64_t = f10.wrapping_add(f20);
    let mut r1: uint64_t = f11.wrapping_add(f21);
    let mut c: uint64_t = (r0 ^ (r0 ^ f20 | r0.wrapping_sub(f20) ^ f20))
        >> 63 as libc::c_uint;
    let mut r11: uint64_t = r1.wrapping_add(c);
    let mut f30: uint64_t = r0;
    let mut f31: uint64_t = r11;
    store64(tag, f30);
    store64(tag.offset(8 as libc::c_uint as isize), f31);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_malloc(
    mut key: *mut uint8_t,
) -> *mut Hacl_MAC_Poly1305_state_t {
    let mut buf: *mut uint8_t = calloc(
        16 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut r1: *mut uint64_t = calloc(
        25 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    let mut block_state: *mut uint64_t = r1;
    Hacl_MAC_Poly1305_poly1305_init(block_state, key);
    let mut k_: *mut uint8_t = calloc(
        32 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    memcpy(
        k_ as *mut libc::c_void,
        key as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_0: *mut uint8_t = k_;
    let mut s: Hacl_MAC_Poly1305_state_t = {
        let mut init = Hacl_MAC_Poly1305_state_t_s {
            block_state: block_state,
            buf: buf,
            total_len: 0 as libc::c_uint as uint64_t,
            p_key: k_0,
        };
        init
    };
    let mut p: *mut Hacl_MAC_Poly1305_state_t = malloc(
        ::core::mem::size_of::<Hacl_MAC_Poly1305_state_t>() as libc::c_ulong,
    ) as *mut Hacl_MAC_Poly1305_state_t;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_reset(
    mut state: *mut Hacl_MAC_Poly1305_state_t,
    mut key: *mut uint8_t,
) {
    let mut block_state: *mut uint64_t = (*state).block_state;
    let mut k_: *mut uint8_t = (*state).p_key;
    Hacl_MAC_Poly1305_poly1305_init(block_state, key);
    memcpy(
        k_ as *mut libc::c_void,
        key as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_1: *mut uint8_t = k_;
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
    (*state).p_key = k_1;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_update(
    mut state: *mut Hacl_MAC_Poly1305_state_t,
    mut chunk: *mut uint8_t,
    mut chunk_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut block_state: *mut uint64_t = (*state).block_state;
    let mut total_len: uint64_t = (*state).total_len;
    if chunk_len as uint64_t > (0xffffffff as libc::c_ulonglong).wrapping_sub(total_len)
    {
        return 3 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    let mut sz: uint32_t = 0;
    if total_len % 16 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        sz = 16 as libc::c_uint;
    } else {
        sz = (total_len % 16 as libc::c_uint as uint64_t) as uint32_t;
    }
    if chunk_len <= (16 as libc::c_uint).wrapping_sub(sz) {
        let mut buf: *mut uint8_t = (*state).buf;
        let mut total_len1: uint64_t = (*state).total_len;
        let mut k_1: *mut uint8_t = (*state).p_key;
        let mut sz1: uint32_t = 0;
        if total_len1 % 16 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1 > 0 as libc::c_ulonglong
        {
            sz1 = 16 as libc::c_uint;
        } else {
            sz1 = (total_len1 % 16 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut buf2: *mut uint8_t = buf.offset(sz1 as isize);
        memcpy(
            buf2 as *mut libc::c_void,
            chunk as *const libc::c_void,
            (chunk_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut total_len2: uint64_t = total_len1.wrapping_add(chunk_len as uint64_t);
        (*state).total_len = total_len2;
        (*state).p_key = k_1;
    } else if sz == 0 as libc::c_uint {
        let mut buf_0: *mut uint8_t = (*state).buf;
        let mut total_len1_0: uint64_t = (*state).total_len;
        let mut k_1_0: *mut uint8_t = (*state).p_key;
        let mut sz1_0: uint32_t = 0;
        if total_len1_0 % 16 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_0 > 0 as libc::c_ulonglong
        {
            sz1_0 = 16 as libc::c_uint;
        } else {
            sz1_0 = (total_len1_0 % 16 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_0 == 0 as libc::c_uint) {
            poly1305_update(block_state, 16 as libc::c_uint, buf_0);
        }
        let mut ite: uint32_t = 0;
        if chunk_len as uint64_t % 16 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong && chunk_len as uint64_t > 0 as libc::c_ulonglong
        {
            ite = 16 as libc::c_uint;
        } else {
            ite = (chunk_len as uint64_t % 16 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks: uint32_t = chunk_len
            .wrapping_sub(ite)
            .wrapping_div(16 as libc::c_uint);
        let mut data1_len: uint32_t = n_blocks.wrapping_mul(16 as libc::c_uint);
        let mut data2_len: uint32_t = chunk_len.wrapping_sub(data1_len);
        let mut data1: *mut uint8_t = chunk;
        let mut data2: *mut uint8_t = chunk.offset(data1_len as isize);
        poly1305_update(block_state, data1_len, data1);
        let mut dst: *mut uint8_t = buf_0;
        memcpy(
            dst as *mut libc::c_void,
            data2 as *const libc::c_void,
            (data2_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        (*state).total_len = total_len1_0.wrapping_add(chunk_len as uint64_t);
        (*state).p_key = k_1_0;
    } else {
        let mut diff: uint32_t = (16 as libc::c_uint).wrapping_sub(sz);
        let mut chunk1: *mut uint8_t = chunk;
        let mut chunk2: *mut uint8_t = chunk.offset(diff as isize);
        let mut buf_1: *mut uint8_t = (*state).buf;
        let mut total_len10: uint64_t = (*state).total_len;
        let mut k_1_1: *mut uint8_t = (*state).p_key;
        let mut sz10: uint32_t = 0;
        if total_len10 % 16 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len10 > 0 as libc::c_ulonglong
        {
            sz10 = 16 as libc::c_uint;
        } else {
            sz10 = (total_len10 % 16 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut buf2_0: *mut uint8_t = buf_1.offset(sz10 as isize);
        memcpy(
            buf2_0 as *mut libc::c_void,
            chunk1 as *const libc::c_void,
            (diff as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut total_len2_0: uint64_t = total_len10.wrapping_add(diff as uint64_t);
        (*state).total_len = total_len2_0;
        (*state).p_key = k_1_1;
        let mut buf0: *mut uint8_t = (*state).buf;
        let mut total_len1_1: uint64_t = (*state).total_len;
        let mut k_10: *mut uint8_t = (*state).p_key;
        let mut sz1_1: uint32_t = 0;
        if total_len1_1 % 16 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_1 > 0 as libc::c_ulonglong
        {
            sz1_1 = 16 as libc::c_uint;
        } else {
            sz1_1 = (total_len1_1 % 16 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_1 == 0 as libc::c_uint) {
            poly1305_update(block_state, 16 as libc::c_uint, buf0);
        }
        let mut ite_0: uint32_t = 0;
        if chunk_len.wrapping_sub(diff) as uint64_t % 16 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong
            && chunk_len.wrapping_sub(diff) as uint64_t > 0 as libc::c_ulonglong
        {
            ite_0 = 16 as libc::c_uint;
        } else {
            ite_0 = (chunk_len.wrapping_sub(diff) as uint64_t
                % 16 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(ite_0)
            .wrapping_div(16 as libc::c_uint);
        let mut data1_len_0: uint32_t = n_blocks_0.wrapping_mul(16 as libc::c_uint);
        let mut data2_len_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(data1_len_0);
        let mut data1_0: *mut uint8_t = chunk2;
        let mut data2_0: *mut uint8_t = chunk2.offset(data1_len_0 as isize);
        poly1305_update(block_state, data1_len_0, data1_0);
        let mut dst_0: *mut uint8_t = buf0;
        memcpy(
            dst_0 as *mut libc::c_void,
            data2_0 as *const libc::c_void,
            (data2_len_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        (*state)
            .total_len = total_len1_1
            .wrapping_add(chunk_len.wrapping_sub(diff) as uint64_t);
        (*state).p_key = k_10;
    }
    return 0 as libc::c_int as Hacl_Streaming_Types_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_digest(
    mut state: *mut Hacl_MAC_Poly1305_state_t,
    mut output: *mut uint8_t,
) {
    let mut block_state: *mut uint64_t = (*state).block_state;
    let mut buf_: *mut uint8_t = (*state).buf;
    let mut total_len: uint64_t = (*state).total_len;
    let mut k_: *mut uint8_t = (*state).p_key;
    let mut r: uint32_t = 0;
    if total_len % 16 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        r = 16 as libc::c_uint;
    } else {
        r = (total_len % 16 as libc::c_uint as uint64_t) as uint32_t;
    }
    let mut buf_1: *mut uint8_t = buf_;
    let mut r1: [uint64_t; 25] = [
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
    ];
    let mut tmp_block_state: *mut uint64_t = r1.as_mut_ptr();
    memcpy(
        tmp_block_state as *mut libc::c_void,
        block_state as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut buf_multi: *mut uint8_t = buf_1;
    let mut ite: uint32_t = 0;
    if r.wrapping_rem(16 as libc::c_uint) == 0 as libc::c_uint && r > 0 as libc::c_uint {
        ite = 16 as libc::c_uint;
    } else {
        ite = r.wrapping_rem(16 as libc::c_uint);
    }
    let mut buf_last: *mut uint8_t = buf_1.offset(r as isize).offset(-(ite as isize));
    poly1305_update(tmp_block_state, 0 as libc::c_uint, buf_multi);
    poly1305_update(tmp_block_state, r, buf_last);
    let mut tmp: [uint64_t; 25] = [
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
    ];
    memcpy(
        tmp.as_mut_ptr() as *mut libc::c_void,
        tmp_block_state as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    Hacl_MAC_Poly1305_poly1305_finish(output, k_, tmp.as_mut_ptr());
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_free(
    mut state: *mut Hacl_MAC_Poly1305_state_t,
) {
    let mut scrut: Hacl_MAC_Poly1305_state_t = *state;
    let mut k_: *mut uint8_t = scrut.p_key;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: *mut uint64_t = scrut.block_state;
    free(k_ as *mut libc::c_void);
    free(block_state as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_mac(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
    mut key: *mut uint8_t,
) {
    let mut ctx: [uint64_t; 25] = [
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
    ];
    Hacl_MAC_Poly1305_poly1305_init(ctx.as_mut_ptr(), key);
    poly1305_update(ctx.as_mut_ptr(), input_len, input);
    Hacl_MAC_Poly1305_poly1305_finish(output, key, ctx.as_mut_ptr());
}
