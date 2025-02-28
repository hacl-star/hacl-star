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
#[no_mangle]
pub static mut Hacl_Impl_Chacha20_Vec_chacha20_constants: [uint32_t; 4] = [
    0x61707865 as libc::c_uint,
    0x3320646e as libc::c_uint,
    0x79622d32 as libc::c_uint,
    0x6b206574 as libc::c_uint,
];
#[inline]
unsafe extern "C" fn quarter_round(
    mut st: *mut uint32_t,
    mut a: uint32_t,
    mut b: uint32_t,
    mut c: uint32_t,
    mut d: uint32_t,
) {
    let mut sta: uint32_t = *st.offset(a as isize);
    let mut stb0: uint32_t = *st.offset(b as isize);
    let mut std0: uint32_t = *st.offset(d as isize);
    let mut sta10: uint32_t = sta.wrapping_add(stb0);
    let mut std10: uint32_t = std0 ^ sta10;
    let mut std2: uint32_t = std10 << 16 as libc::c_uint | std10 >> 16 as libc::c_uint;
    *st.offset(a as isize) = sta10;
    *st.offset(d as isize) = std2;
    let mut sta0: uint32_t = *st.offset(c as isize);
    let mut stb1: uint32_t = *st.offset(d as isize);
    let mut std3: uint32_t = *st.offset(b as isize);
    let mut sta11: uint32_t = sta0.wrapping_add(stb1);
    let mut std11: uint32_t = std3 ^ sta11;
    let mut std20: uint32_t = std11 << 12 as libc::c_uint | std11 >> 20 as libc::c_uint;
    *st.offset(c as isize) = sta11;
    *st.offset(b as isize) = std20;
    let mut sta2: uint32_t = *st.offset(a as isize);
    let mut stb2: uint32_t = *st.offset(b as isize);
    let mut std4: uint32_t = *st.offset(d as isize);
    let mut sta12: uint32_t = sta2.wrapping_add(stb2);
    let mut std12: uint32_t = std4 ^ sta12;
    let mut std21: uint32_t = std12 << 8 as libc::c_uint | std12 >> 24 as libc::c_uint;
    *st.offset(a as isize) = sta12;
    *st.offset(d as isize) = std21;
    let mut sta3: uint32_t = *st.offset(c as isize);
    let mut stb: uint32_t = *st.offset(d as isize);
    let mut std: uint32_t = *st.offset(b as isize);
    let mut sta1: uint32_t = sta3.wrapping_add(stb);
    let mut std1: uint32_t = std ^ sta1;
    let mut std22: uint32_t = std1 << 7 as libc::c_uint | std1 >> 25 as libc::c_uint;
    *st.offset(c as isize) = sta1;
    *st.offset(b as isize) = std22;
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
        1 as libc::c_uint,
        5 as libc::c_uint,
        9 as libc::c_uint,
        13 as libc::c_uint,
    );
    quarter_round(
        st,
        2 as libc::c_uint,
        6 as libc::c_uint,
        10 as libc::c_uint,
        14 as libc::c_uint,
    );
    quarter_round(
        st,
        3 as libc::c_uint,
        7 as libc::c_uint,
        11 as libc::c_uint,
        15 as libc::c_uint,
    );
    quarter_round(
        st,
        0 as libc::c_uint,
        5 as libc::c_uint,
        10 as libc::c_uint,
        15 as libc::c_uint,
    );
    quarter_round(
        st,
        1 as libc::c_uint,
        6 as libc::c_uint,
        11 as libc::c_uint,
        12 as libc::c_uint,
    );
    quarter_round(
        st,
        2 as libc::c_uint,
        7 as libc::c_uint,
        8 as libc::c_uint,
        13 as libc::c_uint,
    );
    quarter_round(
        st,
        3 as libc::c_uint,
        4 as libc::c_uint,
        9 as libc::c_uint,
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
unsafe extern "C" fn chacha20_core(
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
            12 as libc::c_uint as isize,
        ) = (*k.offset(12 as libc::c_uint as isize)).wrapping_add(ctr_u32);
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
            12 as libc::c_uint as isize,
        ) = (*k.offset(12 as libc::c_uint as isize)).wrapping_add(ctr_u32);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_Chacha20_chacha20_init(
    mut ctx: *mut uint32_t,
    mut k: *mut uint8_t,
    mut n: *mut uint8_t,
    mut ctr: uint32_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = Hacl_Impl_Chacha20_Vec_chacha20_constants[i as usize];
    let mut os: *mut uint32_t = ctx;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = Hacl_Impl_Chacha20_Vec_chacha20_constants[i as usize];
    let mut os_0: *mut uint32_t = ctx;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = Hacl_Impl_Chacha20_Vec_chacha20_constants[i as usize];
    let mut os_1: *mut uint32_t = ctx;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = Hacl_Impl_Chacha20_Vec_chacha20_constants[i as usize];
    let mut os_2: *mut uint32_t = ctx;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____0: *mut uint32_t = ctx.offset(4 as libc::c_uint as isize);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x_3: uint32_t = r;
    let mut os_3: *mut uint32_t = uu____0;
    *os_3.offset(i_0 as isize) = x_3;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_4: uint32_t = r_0;
    let mut os_4: *mut uint32_t = uu____0;
    *os_4.offset(i_0 as isize) = x_4;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_5: uint32_t = r_1;
    let mut os_5: *mut uint32_t = uu____0;
    *os_5.offset(i_0 as isize) = x_5;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_6: uint32_t = r_2;
    let mut os_6: *mut uint32_t = uu____0;
    *os_6.offset(i_0 as isize) = x_6;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_3: uint32_t = load32(bj_3);
    let mut r_3: uint32_t = u_3;
    let mut x_7: uint32_t = r_3;
    let mut os_7: *mut uint32_t = uu____0;
    *os_7.offset(i_0 as isize) = x_7;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_4: uint32_t = load32(bj_4);
    let mut r_4: uint32_t = u_4;
    let mut x_8: uint32_t = r_4;
    let mut os_8: *mut uint32_t = uu____0;
    *os_8.offset(i_0 as isize) = x_8;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_5: uint32_t = load32(bj_5);
    let mut r_5: uint32_t = u_5;
    let mut x_9: uint32_t = r_5;
    let mut os_9: *mut uint32_t = uu____0;
    *os_9.offset(i_0 as isize) = x_9;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: *mut uint8_t = k.offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_6: uint32_t = load32(bj_6);
    let mut r_6: uint32_t = u_6;
    let mut x_10: uint32_t = r_6;
    let mut os_10: *mut uint32_t = uu____0;
    *os_10.offset(i_0 as isize) = x_10;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *ctx.offset(12 as libc::c_uint as isize) = ctr;
    let mut uu____1: *mut uint32_t = ctx.offset(13 as libc::c_uint as isize);
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut bj_7: *mut uint8_t = n.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_7: uint32_t = load32(bj_7);
    let mut r_7: uint32_t = u_7;
    let mut x_11: uint32_t = r_7;
    let mut os_11: *mut uint32_t = uu____1;
    *os_11.offset(i_1 as isize) = x_11;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_8: *mut uint8_t = n.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_8: uint32_t = load32(bj_8);
    let mut r_8: uint32_t = u_8;
    let mut x_12: uint32_t = r_8;
    let mut os_12: *mut uint32_t = uu____1;
    *os_12.offset(i_1 as isize) = x_12;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_9: *mut uint8_t = n.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_9: uint32_t = load32(bj_9);
    let mut r_9: uint32_t = u_9;
    let mut x_13: uint32_t = r_9;
    let mut os_13: *mut uint32_t = uu____1;
    *os_13.offset(i_1 as isize) = x_13;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
unsafe extern "C" fn chacha20_encrypt_block(
    mut ctx: *mut uint32_t,
    mut out: *mut uint8_t,
    mut incr: uint32_t,
    mut text: *mut uint8_t,
) {
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
    chacha20_core(k.as_mut_ptr(), ctx, incr);
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
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = bl.as_mut_ptr();
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = bl.as_mut_ptr();
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_1: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = bl.as_mut_ptr();
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = bl.as_mut_ptr();
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_3: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_3: uint32_t = load32(bj_3);
    let mut r_3: uint32_t = u_3;
    let mut x_3: uint32_t = r_3;
    let mut os_3: *mut uint32_t = bl.as_mut_ptr();
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_4: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_4: uint32_t = load32(bj_4);
    let mut r_4: uint32_t = u_4;
    let mut x_4: uint32_t = r_4;
    let mut os_4: *mut uint32_t = bl.as_mut_ptr();
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_5: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_5: uint32_t = load32(bj_5);
    let mut r_5: uint32_t = u_5;
    let mut x_5: uint32_t = r_5;
    let mut os_5: *mut uint32_t = bl.as_mut_ptr();
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_6: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_6: uint32_t = load32(bj_6);
    let mut r_6: uint32_t = u_6;
    let mut x_6: uint32_t = r_6;
    let mut os_6: *mut uint32_t = bl.as_mut_ptr();
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_7: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_7: uint32_t = load32(bj_7);
    let mut r_7: uint32_t = u_7;
    let mut x_7: uint32_t = r_7;
    let mut os_7: *mut uint32_t = bl.as_mut_ptr();
    *os_7.offset(i as isize) = x_7;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_8: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_8: uint32_t = load32(bj_8);
    let mut r_8: uint32_t = u_8;
    let mut x_8: uint32_t = r_8;
    let mut os_8: *mut uint32_t = bl.as_mut_ptr();
    *os_8.offset(i as isize) = x_8;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_9: *mut uint8_t = text.offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_9: uint32_t = load32(bj_9);
    let mut r_9: uint32_t = u_9;
    let mut x_9: uint32_t = r_9;
    let mut os_9: *mut uint32_t = bl.as_mut_ptr();
    *os_9.offset(i as isize) = x_9;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_10: *mut uint8_t = text
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_10: uint32_t = load32(bj_10);
    let mut r_10: uint32_t = u_10;
    let mut x_10: uint32_t = r_10;
    let mut os_10: *mut uint32_t = bl.as_mut_ptr();
    *os_10.offset(i as isize) = x_10;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_11: *mut uint8_t = text
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_11: uint32_t = load32(bj_11);
    let mut r_11: uint32_t = u_11;
    let mut x_11: uint32_t = r_11;
    let mut os_11: *mut uint32_t = bl.as_mut_ptr();
    *os_11.offset(i as isize) = x_11;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_12: *mut uint8_t = text
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_12: uint32_t = load32(bj_12);
    let mut r_12: uint32_t = u_12;
    let mut x_12: uint32_t = r_12;
    let mut os_12: *mut uint32_t = bl.as_mut_ptr();
    *os_12.offset(i as isize) = x_12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_13: *mut uint8_t = text
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_13: uint32_t = load32(bj_13);
    let mut r_13: uint32_t = u_13;
    let mut x_13: uint32_t = r_13;
    let mut os_13: *mut uint32_t = bl.as_mut_ptr();
    *os_13.offset(i as isize) = x_13;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_14: *mut uint8_t = text
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_14: uint32_t = load32(bj_14);
    let mut r_14: uint32_t = u_14;
    let mut x_14: uint32_t = r_14;
    let mut os_14: *mut uint32_t = bl.as_mut_ptr();
    *os_14.offset(i as isize) = x_14;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut x_15: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_15: *mut uint32_t = bl.as_mut_ptr();
    *os_15.offset(i_0 as isize) = x_15;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_16: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_16: *mut uint32_t = bl.as_mut_ptr();
    *os_16.offset(i_0 as isize) = x_16;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_17: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_17: *mut uint32_t = bl.as_mut_ptr();
    *os_17.offset(i_0 as isize) = x_17;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_18: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_18: *mut uint32_t = bl.as_mut_ptr();
    *os_18.offset(i_0 as isize) = x_18;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_19: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_19: *mut uint32_t = bl.as_mut_ptr();
    *os_19.offset(i_0 as isize) = x_19;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_20: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_20: *mut uint32_t = bl.as_mut_ptr();
    *os_20.offset(i_0 as isize) = x_20;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_21: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_21: *mut uint32_t = bl.as_mut_ptr();
    *os_21.offset(i_0 as isize) = x_21;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_22: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_22: *mut uint32_t = bl.as_mut_ptr();
    *os_22.offset(i_0 as isize) = x_22;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_23: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_23: *mut uint32_t = bl.as_mut_ptr();
    *os_23.offset(i_0 as isize) = x_23;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_24: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_24: *mut uint32_t = bl.as_mut_ptr();
    *os_24.offset(i_0 as isize) = x_24;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_25: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_25: *mut uint32_t = bl.as_mut_ptr();
    *os_25.offset(i_0 as isize) = x_25;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_26: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_26: *mut uint32_t = bl.as_mut_ptr();
    *os_26.offset(i_0 as isize) = x_26;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_27: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_27: *mut uint32_t = bl.as_mut_ptr();
    *os_27.offset(i_0 as isize) = x_27;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_28: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_28: *mut uint32_t = bl.as_mut_ptr();
    *os_28.offset(i_0 as isize) = x_28;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_29: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_29: *mut uint32_t = bl.as_mut_ptr();
    *os_29.offset(i_0 as isize) = x_29;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_30: uint32_t = bl[i_0 as usize] ^ k[i_0 as usize];
    let mut os_30: *mut uint32_t = bl.as_mut_ptr();
    *os_30.offset(i_0 as isize) = x_30;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(out.offset(i_1.wrapping_mul(4 as libc::c_uint) as isize), bl[i_1 as usize]);
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn chacha20_encrypt_last(
    mut ctx: *mut uint32_t,
    mut len: uint32_t,
    mut out: *mut uint8_t,
    mut incr: uint32_t,
    mut text: *mut uint8_t,
) {
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
        text as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut plain_copy: [uint8_t; 64] = [
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
        plain_copy.as_mut_ptr() as *mut libc::c_void,
        plain.as_mut_ptr() as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    chacha20_encrypt_block(ctx, plain.as_mut_ptr(), incr, plain_copy.as_mut_ptr());
    memcpy(
        out as *mut libc::c_void,
        plain.as_mut_ptr() as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Impl_Chacha20_chacha20_update(
    mut ctx: *mut uint32_t,
    mut len: uint32_t,
    mut out: *mut uint8_t,
    mut text: *mut uint8_t,
) {
    let mut rem: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut nb: uint32_t = len.wrapping_div(64 as libc::c_uint);
    let mut rem1: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < nb {
        chacha20_encrypt_block(
            ctx,
            out.offset(i.wrapping_mul(64 as libc::c_uint) as isize),
            i,
            text.offset(i.wrapping_mul(64 as libc::c_uint) as isize),
        );
        i = i.wrapping_add(1);
        i;
    }
    if rem1 > 0 as libc::c_uint {
        chacha20_encrypt_last(
            ctx,
            rem,
            out.offset(nb.wrapping_mul(64 as libc::c_uint) as isize),
            nb,
            text.offset(nb.wrapping_mul(64 as libc::c_uint) as isize),
        );
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Chacha20_chacha20_encrypt(
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
    Hacl_Impl_Chacha20_chacha20_init(ctx.as_mut_ptr(), key, n, ctr);
    Hacl_Impl_Chacha20_chacha20_update(ctx.as_mut_ptr(), len, out, text);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Chacha20_chacha20_decrypt(
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
    Hacl_Impl_Chacha20_chacha20_init(ctx.as_mut_ptr(), key, n, ctr);
    Hacl_Impl_Chacha20_chacha20_update(ctx.as_mut_ptr(), len, out, cipher);
}
