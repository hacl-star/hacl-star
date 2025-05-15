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
#[inline]
unsafe extern "C" fn quarter_round(
    mut st: *mut uint32_t,
    mut a: uint32_t,
    mut b: uint32_t,
    mut c: uint32_t,
    mut d: uint32_t,
) {
    let mut sta: uint32_t = *st.offset(b as isize);
    let mut stb0: uint32_t = *st.offset(a as isize);
    let mut std0: uint32_t = *st.offset(d as isize);
    let mut sta1: uint32_t = sta
        ^ (stb0.wrapping_add(std0) << 7 as libc::c_uint
            | stb0.wrapping_add(std0) >> 25 as libc::c_uint);
    *st.offset(b as isize) = sta1;
    let mut sta0: uint32_t = *st.offset(c as isize);
    let mut stb1: uint32_t = *st.offset(b as isize);
    let mut std1: uint32_t = *st.offset(a as isize);
    let mut sta10: uint32_t = sta0
        ^ (stb1.wrapping_add(std1) << 9 as libc::c_uint
            | stb1.wrapping_add(std1) >> 23 as libc::c_uint);
    *st.offset(c as isize) = sta10;
    let mut sta2: uint32_t = *st.offset(d as isize);
    let mut stb2: uint32_t = *st.offset(c as isize);
    let mut std2: uint32_t = *st.offset(b as isize);
    let mut sta11: uint32_t = sta2
        ^ (stb2.wrapping_add(std2) << 13 as libc::c_uint
            | stb2.wrapping_add(std2) >> 19 as libc::c_uint);
    *st.offset(d as isize) = sta11;
    let mut sta3: uint32_t = *st.offset(a as isize);
    let mut stb: uint32_t = *st.offset(d as isize);
    let mut std: uint32_t = *st.offset(c as isize);
    let mut sta12: uint32_t = sta3
        ^ (stb.wrapping_add(std) << 18 as libc::c_uint
            | stb.wrapping_add(std) >> 14 as libc::c_uint);
    *st.offset(a as isize) = sta12;
}
#[inline]
unsafe extern "C" fn double_round(mut st: *mut uint32_t) {
    quarter_round(
        st,
        0 as libc::c_uint,
        4 as libc::c_uint,
        8 as libc::c_uint,
        12 as libc::c_uint,
    );
    quarter_round(
        st,
        5 as libc::c_uint,
        9 as libc::c_uint,
        13 as libc::c_uint,
        1 as libc::c_uint,
    );
    quarter_round(
        st,
        10 as libc::c_uint,
        14 as libc::c_uint,
        2 as libc::c_uint,
        6 as libc::c_uint,
    );
    quarter_round(
        st,
        15 as libc::c_uint,
        3 as libc::c_uint,
        7 as libc::c_uint,
        11 as libc::c_uint,
    );
    quarter_round(
        st,
        0 as libc::c_uint,
        1 as libc::c_uint,
        2 as libc::c_uint,
        3 as libc::c_uint,
    );
    quarter_round(
        st,
        5 as libc::c_uint,
        6 as libc::c_uint,
        7 as libc::c_uint,
        4 as libc::c_uint,
    );
    quarter_round(
        st,
        10 as libc::c_uint,
        11 as libc::c_uint,
        8 as libc::c_uint,
        9 as libc::c_uint,
    );
    quarter_round(
        st,
        15 as libc::c_uint,
        12 as libc::c_uint,
        13 as libc::c_uint,
        14 as libc::c_uint,
    );
}
#[inline]
unsafe extern "C" fn rounds(mut st: *mut uint32_t) {
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
}
#[inline]
unsafe extern "C" fn salsa20_core(
    mut k: *mut uint32_t,
    mut ctx: *mut uint32_t,
    mut ctr: uint32_t,
) {
    memcpy(
        k as *mut libc::c_void,
        ctx as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut ctr_u32: uint32_t = ctr;
    *k
        .offset(
            8 as libc::c_uint as isize,
        ) = (*k.offset(8 as libc::c_uint as isize)).wrapping_add(ctr_u32);
    rounds(k);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = (*k.offset(i as isize)).wrapping_add(*ctx.offset(i as isize));
    let mut os: *mut uint32_t = k;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_0: *mut uint32_t = k;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_1: *mut uint32_t = k;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_2: *mut uint32_t = k;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_3: *mut uint32_t = k;
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_4: *mut uint32_t = k;
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_5: *mut uint32_t = k;
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_6: *mut uint32_t = k;
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_7: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_7: *mut uint32_t = k;
    *os_7.offset(i as isize) = x_7;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_8: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_8: *mut uint32_t = k;
    *os_8.offset(i as isize) = x_8;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_9: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_9: *mut uint32_t = k;
    *os_9.offset(i as isize) = x_9;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_10: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_10: *mut uint32_t = k;
    *os_10.offset(i as isize) = x_10;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_11: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_11: *mut uint32_t = k;
    *os_11.offset(i as isize) = x_11;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_12: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_12: *mut uint32_t = k;
    *os_12.offset(i as isize) = x_12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_13: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_13: *mut uint32_t = k;
    *os_13.offset(i as isize) = x_13;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_14: uint32_t = (*k.offset(i as isize))
        .wrapping_add(*ctx.offset(i as isize));
    let mut os_14: *mut uint32_t = k;
    *os_14.offset(i as isize) = x_14;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *k
        .offset(
            8 as libc::c_uint as isize,
        ) = (*k.offset(8 as libc::c_uint as isize)).wrapping_add(ctr_u32);
}
#[inline]
unsafe extern "C" fn salsa20_key_block0(
    mut out: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
) {
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
    let mut k: [uint32_t; 16] = [
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
    let mut k32: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut n32: [uint32_t; 2] = [0 as libc::c_uint, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = k32.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = k32.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = k32.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = k32.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_3: uint32_t = load32(bj_3);
    let mut r_3: uint32_t = u_3;
    let mut x_3: uint32_t = r_3;
    let mut os_3: *mut uint32_t = k32.as_mut_ptr();
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_4: uint32_t = load32(bj_4);
    let mut r_4: uint32_t = u_4;
    let mut x_4: uint32_t = r_4;
    let mut os_4: *mut uint32_t = k32.as_mut_ptr();
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_5: uint32_t = load32(bj_5);
    let mut r_5: uint32_t = u_5;
    let mut x_5: uint32_t = r_5;
    let mut os_5: *mut uint32_t = k32.as_mut_ptr();
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_6: uint32_t = load32(bj_6);
    let mut r_6: uint32_t = u_6;
    let mut x_6: uint32_t = r_6;
    let mut os_6: *mut uint32_t = k32.as_mut_ptr();
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_7: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_7: uint32_t = load32(bj_7);
    let mut r_7: uint32_t = u_7;
    let mut x_7: uint32_t = r_7;
    let mut os_7: *mut uint32_t = n32.as_mut_ptr();
    *os_7.offset(i_0 as isize) = x_7;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_8: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_8: uint32_t = load32(bj_8);
    let mut r_8: uint32_t = u_8;
    let mut x_8: uint32_t = r_8;
    let mut os_8: *mut uint32_t = n32.as_mut_ptr();
    *os_8.offset(i_0 as isize) = x_8;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    ctx[0 as libc::c_uint as usize] = 0x61707865 as libc::c_uint;
    let mut k0: *mut uint32_t = k32.as_mut_ptr();
    let mut k1: *mut uint32_t = k32.as_mut_ptr().offset(4 as libc::c_uint as isize);
    memcpy(
        ctx.as_mut_ptr().offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        k0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[5 as libc::c_uint as usize] = 0x3320646e as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(6 as libc::c_uint as isize) as *mut libc::c_void,
        n32.as_mut_ptr() as *const libc::c_void,
        (2 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[8 as libc::c_uint as usize] = 0 as libc::c_uint;
    ctx[9 as libc::c_uint as usize] = 0 as libc::c_uint;
    ctx[10 as libc::c_uint as usize] = 0x79622d32 as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(11 as libc::c_uint as isize) as *mut libc::c_void,
        k1 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[15 as libc::c_uint as usize] = 0x6b206574 as libc::c_uint;
    salsa20_core(k.as_mut_ptr(), ctx.as_mut_ptr(), 0 as libc::c_uint);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), k[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn salsa20_encrypt(
    mut len: uint32_t,
    mut out: *mut uint8_t,
    mut text: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
    mut ctr: uint32_t,
) {
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
    let mut k32: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut n32: [uint32_t; 2] = [0 as libc::c_uint, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = k32.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = k32.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = k32.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = k32.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_3: uint32_t = load32(bj_3);
    let mut r_3: uint32_t = u_3;
    let mut x_3: uint32_t = r_3;
    let mut os_3: *mut uint32_t = k32.as_mut_ptr();
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_4: uint32_t = load32(bj_4);
    let mut r_4: uint32_t = u_4;
    let mut x_4: uint32_t = r_4;
    let mut os_4: *mut uint32_t = k32.as_mut_ptr();
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_5: uint32_t = load32(bj_5);
    let mut r_5: uint32_t = u_5;
    let mut x_5: uint32_t = r_5;
    let mut os_5: *mut uint32_t = k32.as_mut_ptr();
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_6: uint32_t = load32(bj_6);
    let mut r_6: uint32_t = u_6;
    let mut x_6: uint32_t = r_6;
    let mut os_6: *mut uint32_t = k32.as_mut_ptr();
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_7: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_7: uint32_t = load32(bj_7);
    let mut r_7: uint32_t = u_7;
    let mut x_7: uint32_t = r_7;
    let mut os_7: *mut uint32_t = n32.as_mut_ptr();
    *os_7.offset(i_0 as isize) = x_7;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_8: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_8: uint32_t = load32(bj_8);
    let mut r_8: uint32_t = u_8;
    let mut x_8: uint32_t = r_8;
    let mut os_8: *mut uint32_t = n32.as_mut_ptr();
    *os_8.offset(i_0 as isize) = x_8;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    ctx[0 as libc::c_uint as usize] = 0x61707865 as libc::c_uint;
    let mut k0: *mut uint32_t = k32.as_mut_ptr();
    let mut k10: *mut uint32_t = k32.as_mut_ptr().offset(4 as libc::c_uint as isize);
    memcpy(
        ctx.as_mut_ptr().offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        k0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[5 as libc::c_uint as usize] = 0x3320646e as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(6 as libc::c_uint as isize) as *mut libc::c_void,
        n32.as_mut_ptr() as *const libc::c_void,
        (2 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[8 as libc::c_uint as usize] = ctr;
    ctx[9 as libc::c_uint as usize] = 0 as libc::c_uint;
    ctx[10 as libc::c_uint as usize] = 0x79622d32 as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(11 as libc::c_uint as isize) as *mut libc::c_void,
        k10 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[15 as libc::c_uint as usize] = 0x6b206574 as libc::c_uint;
    let mut k: [uint32_t; 16] = [
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
    let mut rem: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut nb: uint32_t = len.wrapping_div(64 as libc::c_uint);
    let mut rem1: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < nb {
        let mut uu____0: *mut uint8_t = out
            .offset(i0.wrapping_mul(64 as libc::c_uint) as isize);
        let mut uu____1: *mut uint8_t = text
            .offset(i0.wrapping_mul(64 as libc::c_uint) as isize);
        let mut k1: [uint32_t; 16] = [
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
        salsa20_core(k1.as_mut_ptr(), ctx.as_mut_ptr(), i0);
        let mut bl: [uint32_t; 16] = [
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
        let mut i_1: uint32_t = 0 as libc::c_uint;
        let mut bj_9: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_9: uint32_t = load32(bj_9);
        let mut r_9: uint32_t = u_9;
        let mut x_9: uint32_t = r_9;
        let mut os_9: *mut uint32_t = bl.as_mut_ptr();
        *os_9.offset(i_1 as isize) = x_9;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_10: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_10: uint32_t = load32(bj_10);
        let mut r_10: uint32_t = u_10;
        let mut x_10: uint32_t = r_10;
        let mut os_10: *mut uint32_t = bl.as_mut_ptr();
        *os_10.offset(i_1 as isize) = x_10;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_11: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_11: uint32_t = load32(bj_11);
        let mut r_11: uint32_t = u_11;
        let mut x_11: uint32_t = r_11;
        let mut os_11: *mut uint32_t = bl.as_mut_ptr();
        *os_11.offset(i_1 as isize) = x_11;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_12: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_12: uint32_t = load32(bj_12);
        let mut r_12: uint32_t = u_12;
        let mut x_12: uint32_t = r_12;
        let mut os_12: *mut uint32_t = bl.as_mut_ptr();
        *os_12.offset(i_1 as isize) = x_12;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_13: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_13: uint32_t = load32(bj_13);
        let mut r_13: uint32_t = u_13;
        let mut x_13: uint32_t = r_13;
        let mut os_13: *mut uint32_t = bl.as_mut_ptr();
        *os_13.offset(i_1 as isize) = x_13;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_14: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_14: uint32_t = load32(bj_14);
        let mut r_14: uint32_t = u_14;
        let mut x_14: uint32_t = r_14;
        let mut os_14: *mut uint32_t = bl.as_mut_ptr();
        *os_14.offset(i_1 as isize) = x_14;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_15: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_15: uint32_t = load32(bj_15);
        let mut r_15: uint32_t = u_15;
        let mut x_15: uint32_t = r_15;
        let mut os_15: *mut uint32_t = bl.as_mut_ptr();
        *os_15.offset(i_1 as isize) = x_15;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_16: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_16: uint32_t = load32(bj_16);
        let mut r_16: uint32_t = u_16;
        let mut x_16: uint32_t = r_16;
        let mut os_16: *mut uint32_t = bl.as_mut_ptr();
        *os_16.offset(i_1 as isize) = x_16;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_17: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_17: uint32_t = load32(bj_17);
        let mut r_17: uint32_t = u_17;
        let mut x_17: uint32_t = r_17;
        let mut os_17: *mut uint32_t = bl.as_mut_ptr();
        *os_17.offset(i_1 as isize) = x_17;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_18: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_18: uint32_t = load32(bj_18);
        let mut r_18: uint32_t = u_18;
        let mut x_18: uint32_t = r_18;
        let mut os_18: *mut uint32_t = bl.as_mut_ptr();
        *os_18.offset(i_1 as isize) = x_18;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_19: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_19: uint32_t = load32(bj_19);
        let mut r_19: uint32_t = u_19;
        let mut x_19: uint32_t = r_19;
        let mut os_19: *mut uint32_t = bl.as_mut_ptr();
        *os_19.offset(i_1 as isize) = x_19;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_20: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_20: uint32_t = load32(bj_20);
        let mut r_20: uint32_t = u_20;
        let mut x_20: uint32_t = r_20;
        let mut os_20: *mut uint32_t = bl.as_mut_ptr();
        *os_20.offset(i_1 as isize) = x_20;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_21: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_21: uint32_t = load32(bj_21);
        let mut r_21: uint32_t = u_21;
        let mut x_21: uint32_t = r_21;
        let mut os_21: *mut uint32_t = bl.as_mut_ptr();
        *os_21.offset(i_1 as isize) = x_21;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_22: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_22: uint32_t = load32(bj_22);
        let mut r_22: uint32_t = u_22;
        let mut x_22: uint32_t = r_22;
        let mut os_22: *mut uint32_t = bl.as_mut_ptr();
        *os_22.offset(i_1 as isize) = x_22;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_23: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_23: uint32_t = load32(bj_23);
        let mut r_23: uint32_t = u_23;
        let mut x_23: uint32_t = r_23;
        let mut os_23: *mut uint32_t = bl.as_mut_ptr();
        *os_23.offset(i_1 as isize) = x_23;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_24: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_24: uint32_t = load32(bj_24);
        let mut r_24: uint32_t = u_24;
        let mut x_24: uint32_t = r_24;
        let mut os_24: *mut uint32_t = bl.as_mut_ptr();
        *os_24.offset(i_1 as isize) = x_24;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut x_25: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_25: *mut uint32_t = bl.as_mut_ptr();
        *os_25.offset(i_2 as isize) = x_25;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_26: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_26: *mut uint32_t = bl.as_mut_ptr();
        *os_26.offset(i_2 as isize) = x_26;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_27: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_27: *mut uint32_t = bl.as_mut_ptr();
        *os_27.offset(i_2 as isize) = x_27;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_28: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_28: *mut uint32_t = bl.as_mut_ptr();
        *os_28.offset(i_2 as isize) = x_28;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_29: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_29: *mut uint32_t = bl.as_mut_ptr();
        *os_29.offset(i_2 as isize) = x_29;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_30: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_30: *mut uint32_t = bl.as_mut_ptr();
        *os_30.offset(i_2 as isize) = x_30;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_31: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_31: *mut uint32_t = bl.as_mut_ptr();
        *os_31.offset(i_2 as isize) = x_31;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_32: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_32: *mut uint32_t = bl.as_mut_ptr();
        *os_32.offset(i_2 as isize) = x_32;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_33: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_33: *mut uint32_t = bl.as_mut_ptr();
        *os_33.offset(i_2 as isize) = x_33;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_34: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_34: *mut uint32_t = bl.as_mut_ptr();
        *os_34.offset(i_2 as isize) = x_34;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_35: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_35: *mut uint32_t = bl.as_mut_ptr();
        *os_35.offset(i_2 as isize) = x_35;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_36: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_36: *mut uint32_t = bl.as_mut_ptr();
        *os_36.offset(i_2 as isize) = x_36;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_37: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_37: *mut uint32_t = bl.as_mut_ptr();
        *os_37.offset(i_2 as isize) = x_37;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_38: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_38: *mut uint32_t = bl.as_mut_ptr();
        *os_38.offset(i_2 as isize) = x_38;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_39: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_39: *mut uint32_t = bl.as_mut_ptr();
        *os_39.offset(i_2 as isize) = x_39;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_40: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_40: *mut uint32_t = bl.as_mut_ptr();
        *os_40.offset(i_2 as isize) = x_40;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_3: uint32_t = 0 as libc::c_uint;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i0 = i0.wrapping_add(1);
        i0;
    }
    if rem1 > 0 as libc::c_uint {
        let mut uu____2: *mut uint8_t = out
            .offset(nb.wrapping_mul(64 as libc::c_uint) as isize);
        let mut plain: [uint8_t; 64] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
            plain.as_mut_ptr() as *mut libc::c_void,
            text.offset(nb.wrapping_mul(64 as libc::c_uint) as isize)
                as *const libc::c_void,
            (rem as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k1_0: [uint32_t; 16] = [
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
        salsa20_core(k1_0.as_mut_ptr(), ctx.as_mut_ptr(), nb);
        let mut bl_0: [uint32_t; 16] = [
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
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut bj_25: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_25: uint32_t = load32(bj_25);
        let mut r_25: uint32_t = u_25;
        let mut x_41: uint32_t = r_25;
        let mut os_41: *mut uint32_t = bl_0.as_mut_ptr();
        *os_41.offset(i_4 as isize) = x_41;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_26: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_26: uint32_t = load32(bj_26);
        let mut r_26: uint32_t = u_26;
        let mut x_42: uint32_t = r_26;
        let mut os_42: *mut uint32_t = bl_0.as_mut_ptr();
        *os_42.offset(i_4 as isize) = x_42;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_27: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_27: uint32_t = load32(bj_27);
        let mut r_27: uint32_t = u_27;
        let mut x_43: uint32_t = r_27;
        let mut os_43: *mut uint32_t = bl_0.as_mut_ptr();
        *os_43.offset(i_4 as isize) = x_43;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_28: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_28: uint32_t = load32(bj_28);
        let mut r_28: uint32_t = u_28;
        let mut x_44: uint32_t = r_28;
        let mut os_44: *mut uint32_t = bl_0.as_mut_ptr();
        *os_44.offset(i_4 as isize) = x_44;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_29: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_29: uint32_t = load32(bj_29);
        let mut r_29: uint32_t = u_29;
        let mut x_45: uint32_t = r_29;
        let mut os_45: *mut uint32_t = bl_0.as_mut_ptr();
        *os_45.offset(i_4 as isize) = x_45;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_30: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_30: uint32_t = load32(bj_30);
        let mut r_30: uint32_t = u_30;
        let mut x_46: uint32_t = r_30;
        let mut os_46: *mut uint32_t = bl_0.as_mut_ptr();
        *os_46.offset(i_4 as isize) = x_46;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_31: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_31: uint32_t = load32(bj_31);
        let mut r_31: uint32_t = u_31;
        let mut x_47: uint32_t = r_31;
        let mut os_47: *mut uint32_t = bl_0.as_mut_ptr();
        *os_47.offset(i_4 as isize) = x_47;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_32: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_32: uint32_t = load32(bj_32);
        let mut r_32: uint32_t = u_32;
        let mut x_48: uint32_t = r_32;
        let mut os_48: *mut uint32_t = bl_0.as_mut_ptr();
        *os_48.offset(i_4 as isize) = x_48;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_33: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_33: uint32_t = load32(bj_33);
        let mut r_33: uint32_t = u_33;
        let mut x_49: uint32_t = r_33;
        let mut os_49: *mut uint32_t = bl_0.as_mut_ptr();
        *os_49.offset(i_4 as isize) = x_49;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_34: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_34: uint32_t = load32(bj_34);
        let mut r_34: uint32_t = u_34;
        let mut x_50: uint32_t = r_34;
        let mut os_50: *mut uint32_t = bl_0.as_mut_ptr();
        *os_50.offset(i_4 as isize) = x_50;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_35: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_35: uint32_t = load32(bj_35);
        let mut r_35: uint32_t = u_35;
        let mut x_51: uint32_t = r_35;
        let mut os_51: *mut uint32_t = bl_0.as_mut_ptr();
        *os_51.offset(i_4 as isize) = x_51;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_36: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_36: uint32_t = load32(bj_36);
        let mut r_36: uint32_t = u_36;
        let mut x_52: uint32_t = r_36;
        let mut os_52: *mut uint32_t = bl_0.as_mut_ptr();
        *os_52.offset(i_4 as isize) = x_52;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_37: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_37: uint32_t = load32(bj_37);
        let mut r_37: uint32_t = u_37;
        let mut x_53: uint32_t = r_37;
        let mut os_53: *mut uint32_t = bl_0.as_mut_ptr();
        *os_53.offset(i_4 as isize) = x_53;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_38: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_38: uint32_t = load32(bj_38);
        let mut r_38: uint32_t = u_38;
        let mut x_54: uint32_t = r_38;
        let mut os_54: *mut uint32_t = bl_0.as_mut_ptr();
        *os_54.offset(i_4 as isize) = x_54;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_39: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_39: uint32_t = load32(bj_39);
        let mut r_39: uint32_t = u_39;
        let mut x_55: uint32_t = r_39;
        let mut os_55: *mut uint32_t = bl_0.as_mut_ptr();
        *os_55.offset(i_4 as isize) = x_55;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_40: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_40: uint32_t = load32(bj_40);
        let mut r_40: uint32_t = u_40;
        let mut x_56: uint32_t = r_40;
        let mut os_56: *mut uint32_t = bl_0.as_mut_ptr();
        *os_56.offset(i_4 as isize) = x_56;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_5: uint32_t = 0 as libc::c_uint;
        let mut x_57: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_57: *mut uint32_t = bl_0.as_mut_ptr();
        *os_57.offset(i_5 as isize) = x_57;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_58: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_58: *mut uint32_t = bl_0.as_mut_ptr();
        *os_58.offset(i_5 as isize) = x_58;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_59: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_59: *mut uint32_t = bl_0.as_mut_ptr();
        *os_59.offset(i_5 as isize) = x_59;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_60: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_60: *mut uint32_t = bl_0.as_mut_ptr();
        *os_60.offset(i_5 as isize) = x_60;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_61: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_61: *mut uint32_t = bl_0.as_mut_ptr();
        *os_61.offset(i_5 as isize) = x_61;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_62: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_62: *mut uint32_t = bl_0.as_mut_ptr();
        *os_62.offset(i_5 as isize) = x_62;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_63: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_63: *mut uint32_t = bl_0.as_mut_ptr();
        *os_63.offset(i_5 as isize) = x_63;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_64: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_64: *mut uint32_t = bl_0.as_mut_ptr();
        *os_64.offset(i_5 as isize) = x_64;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_65: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_65: *mut uint32_t = bl_0.as_mut_ptr();
        *os_65.offset(i_5 as isize) = x_65;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_66: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_66: *mut uint32_t = bl_0.as_mut_ptr();
        *os_66.offset(i_5 as isize) = x_66;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_67: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_67: *mut uint32_t = bl_0.as_mut_ptr();
        *os_67.offset(i_5 as isize) = x_67;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_68: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_68: *mut uint32_t = bl_0.as_mut_ptr();
        *os_68.offset(i_5 as isize) = x_68;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_69: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_69: *mut uint32_t = bl_0.as_mut_ptr();
        *os_69.offset(i_5 as isize) = x_69;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_70: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_70: *mut uint32_t = bl_0.as_mut_ptr();
        *os_70.offset(i_5 as isize) = x_70;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_71: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_71: *mut uint32_t = bl_0.as_mut_ptr();
        *os_71.offset(i_5 as isize) = x_71;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_72: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_72: *mut uint32_t = bl_0.as_mut_ptr();
        *os_72.offset(i_5 as isize) = x_72;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_6: uint32_t = 0 as libc::c_uint;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        memcpy(
            uu____2 as *mut libc::c_void,
            plain.as_mut_ptr() as *const libc::c_void,
            (rem as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
}
#[inline]
unsafe extern "C" fn salsa20_decrypt(
    mut len: uint32_t,
    mut out: *mut uint8_t,
    mut cipher: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
    mut ctr: uint32_t,
) {
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
    let mut k32: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut n32: [uint32_t; 2] = [0 as libc::c_uint, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = k32.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = k32.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = k32.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = k32.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_3: uint32_t = load32(bj_3);
    let mut r_3: uint32_t = u_3;
    let mut x_3: uint32_t = r_3;
    let mut os_3: *mut uint32_t = k32.as_mut_ptr();
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_4: uint32_t = load32(bj_4);
    let mut r_4: uint32_t = u_4;
    let mut x_4: uint32_t = r_4;
    let mut os_4: *mut uint32_t = k32.as_mut_ptr();
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_5: uint32_t = load32(bj_5);
    let mut r_5: uint32_t = u_5;
    let mut x_5: uint32_t = r_5;
    let mut os_5: *mut uint32_t = k32.as_mut_ptr();
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_6: uint32_t = load32(bj_6);
    let mut r_6: uint32_t = u_6;
    let mut x_6: uint32_t = r_6;
    let mut os_6: *mut uint32_t = k32.as_mut_ptr();
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_7: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_7: uint32_t = load32(bj_7);
    let mut r_7: uint32_t = u_7;
    let mut x_7: uint32_t = r_7;
    let mut os_7: *mut uint32_t = n32.as_mut_ptr();
    *os_7.offset(i_0 as isize) = x_7;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_8: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_8: uint32_t = load32(bj_8);
    let mut r_8: uint32_t = u_8;
    let mut x_8: uint32_t = r_8;
    let mut os_8: *mut uint32_t = n32.as_mut_ptr();
    *os_8.offset(i_0 as isize) = x_8;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    ctx[0 as libc::c_uint as usize] = 0x61707865 as libc::c_uint;
    let mut k0: *mut uint32_t = k32.as_mut_ptr();
    let mut k10: *mut uint32_t = k32.as_mut_ptr().offset(4 as libc::c_uint as isize);
    memcpy(
        ctx.as_mut_ptr().offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        k0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[5 as libc::c_uint as usize] = 0x3320646e as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(6 as libc::c_uint as isize) as *mut libc::c_void,
        n32.as_mut_ptr() as *const libc::c_void,
        (2 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[8 as libc::c_uint as usize] = ctr;
    ctx[9 as libc::c_uint as usize] = 0 as libc::c_uint;
    ctx[10 as libc::c_uint as usize] = 0x79622d32 as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(11 as libc::c_uint as isize) as *mut libc::c_void,
        k10 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[15 as libc::c_uint as usize] = 0x6b206574 as libc::c_uint;
    let mut k: [uint32_t; 16] = [
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
    let mut rem: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut nb: uint32_t = len.wrapping_div(64 as libc::c_uint);
    let mut rem1: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < nb {
        let mut uu____0: *mut uint8_t = out
            .offset(i0.wrapping_mul(64 as libc::c_uint) as isize);
        let mut uu____1: *mut uint8_t = cipher
            .offset(i0.wrapping_mul(64 as libc::c_uint) as isize);
        let mut k1: [uint32_t; 16] = [
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
        salsa20_core(k1.as_mut_ptr(), ctx.as_mut_ptr(), i0);
        let mut bl: [uint32_t; 16] = [
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
        let mut i_1: uint32_t = 0 as libc::c_uint;
        let mut bj_9: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_9: uint32_t = load32(bj_9);
        let mut r_9: uint32_t = u_9;
        let mut x_9: uint32_t = r_9;
        let mut os_9: *mut uint32_t = bl.as_mut_ptr();
        *os_9.offset(i_1 as isize) = x_9;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_10: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_10: uint32_t = load32(bj_10);
        let mut r_10: uint32_t = u_10;
        let mut x_10: uint32_t = r_10;
        let mut os_10: *mut uint32_t = bl.as_mut_ptr();
        *os_10.offset(i_1 as isize) = x_10;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_11: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_11: uint32_t = load32(bj_11);
        let mut r_11: uint32_t = u_11;
        let mut x_11: uint32_t = r_11;
        let mut os_11: *mut uint32_t = bl.as_mut_ptr();
        *os_11.offset(i_1 as isize) = x_11;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_12: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_12: uint32_t = load32(bj_12);
        let mut r_12: uint32_t = u_12;
        let mut x_12: uint32_t = r_12;
        let mut os_12: *mut uint32_t = bl.as_mut_ptr();
        *os_12.offset(i_1 as isize) = x_12;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_13: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_13: uint32_t = load32(bj_13);
        let mut r_13: uint32_t = u_13;
        let mut x_13: uint32_t = r_13;
        let mut os_13: *mut uint32_t = bl.as_mut_ptr();
        *os_13.offset(i_1 as isize) = x_13;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_14: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_14: uint32_t = load32(bj_14);
        let mut r_14: uint32_t = u_14;
        let mut x_14: uint32_t = r_14;
        let mut os_14: *mut uint32_t = bl.as_mut_ptr();
        *os_14.offset(i_1 as isize) = x_14;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_15: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_15: uint32_t = load32(bj_15);
        let mut r_15: uint32_t = u_15;
        let mut x_15: uint32_t = r_15;
        let mut os_15: *mut uint32_t = bl.as_mut_ptr();
        *os_15.offset(i_1 as isize) = x_15;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_16: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_16: uint32_t = load32(bj_16);
        let mut r_16: uint32_t = u_16;
        let mut x_16: uint32_t = r_16;
        let mut os_16: *mut uint32_t = bl.as_mut_ptr();
        *os_16.offset(i_1 as isize) = x_16;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_17: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_17: uint32_t = load32(bj_17);
        let mut r_17: uint32_t = u_17;
        let mut x_17: uint32_t = r_17;
        let mut os_17: *mut uint32_t = bl.as_mut_ptr();
        *os_17.offset(i_1 as isize) = x_17;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_18: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_18: uint32_t = load32(bj_18);
        let mut r_18: uint32_t = u_18;
        let mut x_18: uint32_t = r_18;
        let mut os_18: *mut uint32_t = bl.as_mut_ptr();
        *os_18.offset(i_1 as isize) = x_18;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_19: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_19: uint32_t = load32(bj_19);
        let mut r_19: uint32_t = u_19;
        let mut x_19: uint32_t = r_19;
        let mut os_19: *mut uint32_t = bl.as_mut_ptr();
        *os_19.offset(i_1 as isize) = x_19;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_20: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_20: uint32_t = load32(bj_20);
        let mut r_20: uint32_t = u_20;
        let mut x_20: uint32_t = r_20;
        let mut os_20: *mut uint32_t = bl.as_mut_ptr();
        *os_20.offset(i_1 as isize) = x_20;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_21: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_21: uint32_t = load32(bj_21);
        let mut r_21: uint32_t = u_21;
        let mut x_21: uint32_t = r_21;
        let mut os_21: *mut uint32_t = bl.as_mut_ptr();
        *os_21.offset(i_1 as isize) = x_21;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_22: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_22: uint32_t = load32(bj_22);
        let mut r_22: uint32_t = u_22;
        let mut x_22: uint32_t = r_22;
        let mut os_22: *mut uint32_t = bl.as_mut_ptr();
        *os_22.offset(i_1 as isize) = x_22;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_23: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_23: uint32_t = load32(bj_23);
        let mut r_23: uint32_t = u_23;
        let mut x_23: uint32_t = r_23;
        let mut os_23: *mut uint32_t = bl.as_mut_ptr();
        *os_23.offset(i_1 as isize) = x_23;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_24: *mut uint8_t = uu____1
            .offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_24: uint32_t = load32(bj_24);
        let mut r_24: uint32_t = u_24;
        let mut x_24: uint32_t = r_24;
        let mut os_24: *mut uint32_t = bl.as_mut_ptr();
        *os_24.offset(i_1 as isize) = x_24;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut x_25: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_25: *mut uint32_t = bl.as_mut_ptr();
        *os_25.offset(i_2 as isize) = x_25;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_26: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_26: *mut uint32_t = bl.as_mut_ptr();
        *os_26.offset(i_2 as isize) = x_26;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_27: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_27: *mut uint32_t = bl.as_mut_ptr();
        *os_27.offset(i_2 as isize) = x_27;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_28: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_28: *mut uint32_t = bl.as_mut_ptr();
        *os_28.offset(i_2 as isize) = x_28;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_29: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_29: *mut uint32_t = bl.as_mut_ptr();
        *os_29.offset(i_2 as isize) = x_29;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_30: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_30: *mut uint32_t = bl.as_mut_ptr();
        *os_30.offset(i_2 as isize) = x_30;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_31: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_31: *mut uint32_t = bl.as_mut_ptr();
        *os_31.offset(i_2 as isize) = x_31;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_32: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_32: *mut uint32_t = bl.as_mut_ptr();
        *os_32.offset(i_2 as isize) = x_32;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_33: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_33: *mut uint32_t = bl.as_mut_ptr();
        *os_33.offset(i_2 as isize) = x_33;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_34: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_34: *mut uint32_t = bl.as_mut_ptr();
        *os_34.offset(i_2 as isize) = x_34;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_35: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_35: *mut uint32_t = bl.as_mut_ptr();
        *os_35.offset(i_2 as isize) = x_35;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_36: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_36: *mut uint32_t = bl.as_mut_ptr();
        *os_36.offset(i_2 as isize) = x_36;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_37: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_37: *mut uint32_t = bl.as_mut_ptr();
        *os_37.offset(i_2 as isize) = x_37;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_38: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_38: *mut uint32_t = bl.as_mut_ptr();
        *os_38.offset(i_2 as isize) = x_38;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_39: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_39: *mut uint32_t = bl.as_mut_ptr();
        *os_39.offset(i_2 as isize) = x_39;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_40: uint32_t = bl[i_2 as usize] ^ k1[i_2 as usize];
        let mut os_40: *mut uint32_t = bl.as_mut_ptr();
        *os_40.offset(i_2 as isize) = x_40;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_3: uint32_t = 0 as libc::c_uint;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            uu____0.offset(i_3.wrapping_mul(4 as libc::c_uint) as isize),
            bl[i_3 as usize],
        );
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i0 = i0.wrapping_add(1);
        i0;
    }
    if rem1 > 0 as libc::c_uint {
        let mut uu____2: *mut uint8_t = out
            .offset(nb.wrapping_mul(64 as libc::c_uint) as isize);
        let mut plain: [uint8_t; 64] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
            plain.as_mut_ptr() as *mut libc::c_void,
            cipher.offset(nb.wrapping_mul(64 as libc::c_uint) as isize)
                as *const libc::c_void,
            (rem as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k1_0: [uint32_t; 16] = [
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
        salsa20_core(k1_0.as_mut_ptr(), ctx.as_mut_ptr(), nb);
        let mut bl_0: [uint32_t; 16] = [
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
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut bj_25: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_25: uint32_t = load32(bj_25);
        let mut r_25: uint32_t = u_25;
        let mut x_41: uint32_t = r_25;
        let mut os_41: *mut uint32_t = bl_0.as_mut_ptr();
        *os_41.offset(i_4 as isize) = x_41;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_26: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_26: uint32_t = load32(bj_26);
        let mut r_26: uint32_t = u_26;
        let mut x_42: uint32_t = r_26;
        let mut os_42: *mut uint32_t = bl_0.as_mut_ptr();
        *os_42.offset(i_4 as isize) = x_42;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_27: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_27: uint32_t = load32(bj_27);
        let mut r_27: uint32_t = u_27;
        let mut x_43: uint32_t = r_27;
        let mut os_43: *mut uint32_t = bl_0.as_mut_ptr();
        *os_43.offset(i_4 as isize) = x_43;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_28: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_28: uint32_t = load32(bj_28);
        let mut r_28: uint32_t = u_28;
        let mut x_44: uint32_t = r_28;
        let mut os_44: *mut uint32_t = bl_0.as_mut_ptr();
        *os_44.offset(i_4 as isize) = x_44;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_29: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_29: uint32_t = load32(bj_29);
        let mut r_29: uint32_t = u_29;
        let mut x_45: uint32_t = r_29;
        let mut os_45: *mut uint32_t = bl_0.as_mut_ptr();
        *os_45.offset(i_4 as isize) = x_45;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_30: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_30: uint32_t = load32(bj_30);
        let mut r_30: uint32_t = u_30;
        let mut x_46: uint32_t = r_30;
        let mut os_46: *mut uint32_t = bl_0.as_mut_ptr();
        *os_46.offset(i_4 as isize) = x_46;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_31: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_31: uint32_t = load32(bj_31);
        let mut r_31: uint32_t = u_31;
        let mut x_47: uint32_t = r_31;
        let mut os_47: *mut uint32_t = bl_0.as_mut_ptr();
        *os_47.offset(i_4 as isize) = x_47;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_32: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_32: uint32_t = load32(bj_32);
        let mut r_32: uint32_t = u_32;
        let mut x_48: uint32_t = r_32;
        let mut os_48: *mut uint32_t = bl_0.as_mut_ptr();
        *os_48.offset(i_4 as isize) = x_48;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_33: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_33: uint32_t = load32(bj_33);
        let mut r_33: uint32_t = u_33;
        let mut x_49: uint32_t = r_33;
        let mut os_49: *mut uint32_t = bl_0.as_mut_ptr();
        *os_49.offset(i_4 as isize) = x_49;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_34: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_34: uint32_t = load32(bj_34);
        let mut r_34: uint32_t = u_34;
        let mut x_50: uint32_t = r_34;
        let mut os_50: *mut uint32_t = bl_0.as_mut_ptr();
        *os_50.offset(i_4 as isize) = x_50;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_35: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_35: uint32_t = load32(bj_35);
        let mut r_35: uint32_t = u_35;
        let mut x_51: uint32_t = r_35;
        let mut os_51: *mut uint32_t = bl_0.as_mut_ptr();
        *os_51.offset(i_4 as isize) = x_51;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_36: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_36: uint32_t = load32(bj_36);
        let mut r_36: uint32_t = u_36;
        let mut x_52: uint32_t = r_36;
        let mut os_52: *mut uint32_t = bl_0.as_mut_ptr();
        *os_52.offset(i_4 as isize) = x_52;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_37: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_37: uint32_t = load32(bj_37);
        let mut r_37: uint32_t = u_37;
        let mut x_53: uint32_t = r_37;
        let mut os_53: *mut uint32_t = bl_0.as_mut_ptr();
        *os_53.offset(i_4 as isize) = x_53;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_38: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_38: uint32_t = load32(bj_38);
        let mut r_38: uint32_t = u_38;
        let mut x_54: uint32_t = r_38;
        let mut os_54: *mut uint32_t = bl_0.as_mut_ptr();
        *os_54.offset(i_4 as isize) = x_54;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_39: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_39: uint32_t = load32(bj_39);
        let mut r_39: uint32_t = u_39;
        let mut x_55: uint32_t = r_39;
        let mut os_55: *mut uint32_t = bl_0.as_mut_ptr();
        *os_55.offset(i_4 as isize) = x_55;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut bj_40: *mut uint8_t = plain
            .as_mut_ptr()
            .offset(i_4.wrapping_mul(4 as libc::c_uint) as isize);
        let mut u_40: uint32_t = load32(bj_40);
        let mut r_40: uint32_t = u_40;
        let mut x_56: uint32_t = r_40;
        let mut os_56: *mut uint32_t = bl_0.as_mut_ptr();
        *os_56.offset(i_4 as isize) = x_56;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_5: uint32_t = 0 as libc::c_uint;
        let mut x_57: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_57: *mut uint32_t = bl_0.as_mut_ptr();
        *os_57.offset(i_5 as isize) = x_57;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_58: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_58: *mut uint32_t = bl_0.as_mut_ptr();
        *os_58.offset(i_5 as isize) = x_58;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_59: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_59: *mut uint32_t = bl_0.as_mut_ptr();
        *os_59.offset(i_5 as isize) = x_59;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_60: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_60: *mut uint32_t = bl_0.as_mut_ptr();
        *os_60.offset(i_5 as isize) = x_60;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_61: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_61: *mut uint32_t = bl_0.as_mut_ptr();
        *os_61.offset(i_5 as isize) = x_61;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_62: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_62: *mut uint32_t = bl_0.as_mut_ptr();
        *os_62.offset(i_5 as isize) = x_62;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_63: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_63: *mut uint32_t = bl_0.as_mut_ptr();
        *os_63.offset(i_5 as isize) = x_63;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_64: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_64: *mut uint32_t = bl_0.as_mut_ptr();
        *os_64.offset(i_5 as isize) = x_64;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_65: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_65: *mut uint32_t = bl_0.as_mut_ptr();
        *os_65.offset(i_5 as isize) = x_65;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_66: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_66: *mut uint32_t = bl_0.as_mut_ptr();
        *os_66.offset(i_5 as isize) = x_66;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_67: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_67: *mut uint32_t = bl_0.as_mut_ptr();
        *os_67.offset(i_5 as isize) = x_67;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_68: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_68: *mut uint32_t = bl_0.as_mut_ptr();
        *os_68.offset(i_5 as isize) = x_68;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_69: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_69: *mut uint32_t = bl_0.as_mut_ptr();
        *os_69.offset(i_5 as isize) = x_69;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_70: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_70: *mut uint32_t = bl_0.as_mut_ptr();
        *os_70.offset(i_5 as isize) = x_70;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_71: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_71: *mut uint32_t = bl_0.as_mut_ptr();
        *os_71.offset(i_5 as isize) = x_71;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x_72: uint32_t = bl_0[i_5 as usize] ^ k1_0[i_5 as usize];
        let mut os_72: *mut uint32_t = bl_0.as_mut_ptr();
        *os_72.offset(i_5 as isize) = x_72;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i_6: uint32_t = 0 as libc::c_uint;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        store32(
            plain.as_mut_ptr().offset(i_6.wrapping_mul(4 as libc::c_uint) as isize),
            bl_0[i_6 as usize],
        );
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        memcpy(
            uu____2 as *mut libc::c_void,
            plain.as_mut_ptr() as *const libc::c_void,
            (rem as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
}
#[inline]
unsafe extern "C" fn hsalsa20(
    mut out: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
) {
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
    let mut k32: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut n32: [uint32_t; 4] = [0 as libc::c_uint, 0, 0, 0];
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = k32.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = k32.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = k32.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = k32.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_3: uint32_t = load32(bj_3);
    let mut r_3: uint32_t = u_3;
    let mut x_3: uint32_t = r_3;
    let mut os_3: *mut uint32_t = k32.as_mut_ptr();
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_4: uint32_t = load32(bj_4);
    let mut r_4: uint32_t = u_4;
    let mut x_4: uint32_t = r_4;
    let mut os_4: *mut uint32_t = k32.as_mut_ptr();
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_5: uint32_t = load32(bj_5);
    let mut r_5: uint32_t = u_5;
    let mut x_5: uint32_t = r_5;
    let mut os_5: *mut uint32_t = k32.as_mut_ptr();
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: *mut uint8_t = key.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_6: uint32_t = load32(bj_6);
    let mut r_6: uint32_t = u_6;
    let mut x_6: uint32_t = r_6;
    let mut os_6: *mut uint32_t = k32.as_mut_ptr();
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_7: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_7: uint32_t = load32(bj_7);
    let mut r_7: uint32_t = u_7;
    let mut x_7: uint32_t = r_7;
    let mut os_7: *mut uint32_t = n32.as_mut_ptr();
    *os_7.offset(i_0 as isize) = x_7;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_8: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_8: uint32_t = load32(bj_8);
    let mut r_8: uint32_t = u_8;
    let mut x_8: uint32_t = r_8;
    let mut os_8: *mut uint32_t = n32.as_mut_ptr();
    *os_8.offset(i_0 as isize) = x_8;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_9: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_9: uint32_t = load32(bj_9);
    let mut r_9: uint32_t = u_9;
    let mut x_9: uint32_t = r_9;
    let mut os_9: *mut uint32_t = n32.as_mut_ptr();
    *os_9.offset(i_0 as isize) = x_9;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_10: *mut uint8_t = n.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_10: uint32_t = load32(bj_10);
    let mut r_10: uint32_t = u_10;
    let mut x_10: uint32_t = r_10;
    let mut os_10: *mut uint32_t = n32.as_mut_ptr();
    *os_10.offset(i_0 as isize) = x_10;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k0: *mut uint32_t = k32.as_mut_ptr();
    let mut k1: *mut uint32_t = k32.as_mut_ptr().offset(4 as libc::c_uint as isize);
    ctx[0 as libc::c_uint as usize] = 0x61707865 as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        k0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[5 as libc::c_uint as usize] = 0x3320646e as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(6 as libc::c_uint as isize) as *mut libc::c_void,
        n32.as_mut_ptr() as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[10 as libc::c_uint as usize] = 0x79622d32 as libc::c_uint;
    memcpy(
        ctx.as_mut_ptr().offset(11 as libc::c_uint as isize) as *mut libc::c_void,
        k1 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    ctx[15 as libc::c_uint as usize] = 0x6b206574 as libc::c_uint;
    rounds(ctx.as_mut_ptr());
    let mut r0: uint32_t = ctx[0 as libc::c_uint as usize];
    let mut r1: uint32_t = ctx[5 as libc::c_uint as usize];
    let mut r2: uint32_t = ctx[10 as libc::c_uint as usize];
    let mut r3: uint32_t = ctx[15 as libc::c_uint as usize];
    let mut r4: uint32_t = ctx[6 as libc::c_uint as usize];
    let mut r5: uint32_t = ctx[7 as libc::c_uint as usize];
    let mut r6: uint32_t = ctx[8 as libc::c_uint as usize];
    let mut r7: uint32_t = ctx[9 as libc::c_uint as usize];
    let mut res: [uint32_t; 8] = [r0, r1, r2, r3, r4, r5, r6, r7];
    let mut i_1: uint32_t = 0 as libc::c_uint;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), res[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Salsa20_salsa20_encrypt(
    mut len: uint32_t,
    mut out: *mut uint8_t,
    mut text: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
    mut ctr: uint32_t,
) {
    salsa20_encrypt(len, out, text, key, n, ctr);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Salsa20_salsa20_decrypt(
    mut len: uint32_t,
    mut out: *mut uint8_t,
    mut cipher: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
    mut ctr: uint32_t,
) {
    salsa20_decrypt(len, out, cipher, key, n, ctr);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Salsa20_salsa20_key_block0(
    mut out: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
) {
    salsa20_key_block0(out, key, n);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Salsa20_hsalsa20(
    mut out: *mut uint8_t,
    mut key: *mut uint8_t,
    mut n: *mut uint8_t,
) {
    hsalsa20(out, key, n);
}
