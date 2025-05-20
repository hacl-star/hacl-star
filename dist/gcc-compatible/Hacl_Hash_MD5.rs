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
pub struct Hacl_Streaming_MD_state_32_s {
    pub block_state: *mut uint32_t,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
}
pub type Hacl_Streaming_MD_state_32 = Hacl_Streaming_MD_state_32_s;
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
unsafe extern "C" fn store64(mut b: *mut uint8_t, mut i: uint64_t) {
    memcpy(
        b as *mut libc::c_void,
        &mut i as *mut uint64_t as *const libc::c_void,
        8 as libc::c_int as libc::c_ulong,
    );
}
static mut _h0: [uint32_t; 4] = [
    0x67452301 as libc::c_uint,
    0xefcdab89 as libc::c_uint,
    0x98badcfe as libc::c_uint,
    0x10325476 as libc::c_uint,
];
static mut _t: [uint32_t; 64] = [
    0xd76aa478 as libc::c_uint,
    0xe8c7b756 as libc::c_uint,
    0x242070db as libc::c_uint,
    0xc1bdceee as libc::c_uint,
    0xf57c0faf as libc::c_uint,
    0x4787c62a as libc::c_uint,
    0xa8304613 as libc::c_uint,
    0xfd469501 as libc::c_uint,
    0x698098d8 as libc::c_uint,
    0x8b44f7af as libc::c_uint,
    0xffff5bb1 as libc::c_uint,
    0x895cd7be as libc::c_uint,
    0x6b901122 as libc::c_uint,
    0xfd987193 as libc::c_uint,
    0xa679438e as libc::c_uint,
    0x49b40821 as libc::c_uint,
    0xf61e2562 as libc::c_uint,
    0xc040b340 as libc::c_uint,
    0x265e5a51 as libc::c_uint,
    0xe9b6c7aa as libc::c_uint,
    0xd62f105d as libc::c_uint,
    0x2441453 as libc::c_uint,
    0xd8a1e681 as libc::c_uint,
    0xe7d3fbc8 as libc::c_uint,
    0x21e1cde6 as libc::c_uint,
    0xc33707d6 as libc::c_uint,
    0xf4d50d87 as libc::c_uint,
    0x455a14ed as libc::c_uint,
    0xa9e3e905 as libc::c_uint,
    0xfcefa3f8 as libc::c_uint,
    0x676f02d9 as libc::c_uint,
    0x8d2a4c8a as libc::c_uint,
    0xfffa3942 as libc::c_uint,
    0x8771f681 as libc::c_uint,
    0x6d9d6122 as libc::c_uint,
    0xfde5380c as libc::c_uint,
    0xa4beea44 as libc::c_uint,
    0x4bdecfa9 as libc::c_uint,
    0xf6bb4b60 as libc::c_uint,
    0xbebfbc70 as libc::c_uint,
    0x289b7ec6 as libc::c_uint,
    0xeaa127fa as libc::c_uint,
    0xd4ef3085 as libc::c_uint,
    0x4881d05 as libc::c_uint,
    0xd9d4d039 as libc::c_uint,
    0xe6db99e5 as libc::c_uint,
    0x1fa27cf8 as libc::c_uint,
    0xc4ac5665 as libc::c_uint,
    0xf4292244 as libc::c_uint,
    0x432aff97 as libc::c_uint,
    0xab9423a7 as libc::c_uint,
    0xfc93a039 as libc::c_uint,
    0x655b59c3 as libc::c_uint,
    0x8f0ccc92 as libc::c_uint,
    0xffeff47d as libc::c_uint,
    0x85845dd1 as libc::c_uint,
    0x6fa87e4f as libc::c_uint,
    0xfe2ce6e0 as libc::c_uint,
    0xa3014314 as libc::c_uint,
    0x4e0811a1 as libc::c_uint,
    0xf7537e82 as libc::c_uint,
    0xbd3af235 as libc::c_uint,
    0x2ad7d2bb as libc::c_uint,
    0xeb86d391 as libc::c_uint,
];
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_init(mut s: *mut uint32_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
unsafe extern "C" fn update(mut abcd: *mut uint32_t, mut x: *mut uint8_t) {
    let mut aa: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut bb: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut cc: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut dd: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut va: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb0: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc0: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd0: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b0: *mut uint8_t = x;
    let mut u: uint32_t = load32(b0);
    let mut xk: uint32_t = u;
    let mut ti0: uint32_t = _t[0 as libc::c_uint as usize];
    let mut v: uint32_t = vb0
        .wrapping_add(
            va.wrapping_add(vb0 & vc0 | !vb0 & vd0).wrapping_add(xk).wrapping_add(ti0)
                << 7 as libc::c_uint
                | va
                    .wrapping_add(vb0 & vc0 | !vb0 & vd0)
                    .wrapping_add(xk)
                    .wrapping_add(ti0) >> 25 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v;
    let mut va0: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb1: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc1: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd1: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b1: *mut uint8_t = x.offset(4 as libc::c_uint as isize);
    let mut u0: uint32_t = load32(b1);
    let mut xk0: uint32_t = u0;
    let mut ti1: uint32_t = _t[1 as libc::c_uint as usize];
    let mut v0: uint32_t = vb1
        .wrapping_add(
            va0.wrapping_add(vb1 & vc1 | !vb1 & vd1).wrapping_add(xk0).wrapping_add(ti1)
                << 12 as libc::c_uint
                | va0
                    .wrapping_add(vb1 & vc1 | !vb1 & vd1)
                    .wrapping_add(xk0)
                    .wrapping_add(ti1) >> 20 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v0;
    let mut va1: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb2: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc2: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd2: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b2: *mut uint8_t = x.offset(8 as libc::c_uint as isize);
    let mut u1: uint32_t = load32(b2);
    let mut xk1: uint32_t = u1;
    let mut ti2: uint32_t = _t[2 as libc::c_uint as usize];
    let mut v1: uint32_t = vb2
        .wrapping_add(
            va1.wrapping_add(vb2 & vc2 | !vb2 & vd2).wrapping_add(xk1).wrapping_add(ti2)
                << 17 as libc::c_uint
                | va1
                    .wrapping_add(vb2 & vc2 | !vb2 & vd2)
                    .wrapping_add(xk1)
                    .wrapping_add(ti2) >> 15 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v1;
    let mut va2: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb3: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc3: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd3: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b3: *mut uint8_t = x.offset(12 as libc::c_uint as isize);
    let mut u2: uint32_t = load32(b3);
    let mut xk2: uint32_t = u2;
    let mut ti3: uint32_t = _t[3 as libc::c_uint as usize];
    let mut v2: uint32_t = vb3
        .wrapping_add(
            va2.wrapping_add(vb3 & vc3 | !vb3 & vd3).wrapping_add(xk2).wrapping_add(ti3)
                << 22 as libc::c_uint
                | va2
                    .wrapping_add(vb3 & vc3 | !vb3 & vd3)
                    .wrapping_add(xk2)
                    .wrapping_add(ti3) >> 10 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v2;
    let mut va3: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb4: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc4: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd4: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b4: *mut uint8_t = x.offset(16 as libc::c_uint as isize);
    let mut u3: uint32_t = load32(b4);
    let mut xk3: uint32_t = u3;
    let mut ti4: uint32_t = _t[4 as libc::c_uint as usize];
    let mut v3: uint32_t = vb4
        .wrapping_add(
            va3.wrapping_add(vb4 & vc4 | !vb4 & vd4).wrapping_add(xk3).wrapping_add(ti4)
                << 7 as libc::c_uint
                | va3
                    .wrapping_add(vb4 & vc4 | !vb4 & vd4)
                    .wrapping_add(xk3)
                    .wrapping_add(ti4) >> 25 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v3;
    let mut va4: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb5: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc5: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd5: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b5: *mut uint8_t = x.offset(20 as libc::c_uint as isize);
    let mut u4: uint32_t = load32(b5);
    let mut xk4: uint32_t = u4;
    let mut ti5: uint32_t = _t[5 as libc::c_uint as usize];
    let mut v4: uint32_t = vb5
        .wrapping_add(
            va4.wrapping_add(vb5 & vc5 | !vb5 & vd5).wrapping_add(xk4).wrapping_add(ti5)
                << 12 as libc::c_uint
                | va4
                    .wrapping_add(vb5 & vc5 | !vb5 & vd5)
                    .wrapping_add(xk4)
                    .wrapping_add(ti5) >> 20 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v4;
    let mut va5: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb6: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc6: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd6: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b6: *mut uint8_t = x.offset(24 as libc::c_uint as isize);
    let mut u5: uint32_t = load32(b6);
    let mut xk5: uint32_t = u5;
    let mut ti6: uint32_t = _t[6 as libc::c_uint as usize];
    let mut v5: uint32_t = vb6
        .wrapping_add(
            va5.wrapping_add(vb6 & vc6 | !vb6 & vd6).wrapping_add(xk5).wrapping_add(ti6)
                << 17 as libc::c_uint
                | va5
                    .wrapping_add(vb6 & vc6 | !vb6 & vd6)
                    .wrapping_add(xk5)
                    .wrapping_add(ti6) >> 15 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v5;
    let mut va6: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb7: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc7: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd7: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b7: *mut uint8_t = x.offset(28 as libc::c_uint as isize);
    let mut u6: uint32_t = load32(b7);
    let mut xk6: uint32_t = u6;
    let mut ti7: uint32_t = _t[7 as libc::c_uint as usize];
    let mut v6: uint32_t = vb7
        .wrapping_add(
            va6.wrapping_add(vb7 & vc7 | !vb7 & vd7).wrapping_add(xk6).wrapping_add(ti7)
                << 22 as libc::c_uint
                | va6
                    .wrapping_add(vb7 & vc7 | !vb7 & vd7)
                    .wrapping_add(xk6)
                    .wrapping_add(ti7) >> 10 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v6;
    let mut va7: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb8: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc8: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd8: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b8: *mut uint8_t = x.offset(32 as libc::c_uint as isize);
    let mut u7: uint32_t = load32(b8);
    let mut xk7: uint32_t = u7;
    let mut ti8: uint32_t = _t[8 as libc::c_uint as usize];
    let mut v7: uint32_t = vb8
        .wrapping_add(
            va7.wrapping_add(vb8 & vc8 | !vb8 & vd8).wrapping_add(xk7).wrapping_add(ti8)
                << 7 as libc::c_uint
                | va7
                    .wrapping_add(vb8 & vc8 | !vb8 & vd8)
                    .wrapping_add(xk7)
                    .wrapping_add(ti8) >> 25 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v7;
    let mut va8: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb9: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc9: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd9: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b9: *mut uint8_t = x.offset(36 as libc::c_uint as isize);
    let mut u8: uint32_t = load32(b9);
    let mut xk8: uint32_t = u8;
    let mut ti9: uint32_t = _t[9 as libc::c_uint as usize];
    let mut v8: uint32_t = vb9
        .wrapping_add(
            va8.wrapping_add(vb9 & vc9 | !vb9 & vd9).wrapping_add(xk8).wrapping_add(ti9)
                << 12 as libc::c_uint
                | va8
                    .wrapping_add(vb9 & vc9 | !vb9 & vd9)
                    .wrapping_add(xk8)
                    .wrapping_add(ti9) >> 20 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v8;
    let mut va9: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb10: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc10: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd10: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b10: *mut uint8_t = x.offset(40 as libc::c_uint as isize);
    let mut u9: uint32_t = load32(b10);
    let mut xk9: uint32_t = u9;
    let mut ti10: uint32_t = _t[10 as libc::c_uint as usize];
    let mut v9: uint32_t = vb10
        .wrapping_add(
            va9
                .wrapping_add(vb10 & vc10 | !vb10 & vd10)
                .wrapping_add(xk9)
                .wrapping_add(ti10) << 17 as libc::c_uint
                | va9
                    .wrapping_add(vb10 & vc10 | !vb10 & vd10)
                    .wrapping_add(xk9)
                    .wrapping_add(ti10) >> 15 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v9;
    let mut va10: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb11: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc11: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd11: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b11: *mut uint8_t = x.offset(44 as libc::c_uint as isize);
    let mut u10: uint32_t = load32(b11);
    let mut xk10: uint32_t = u10;
    let mut ti11: uint32_t = _t[11 as libc::c_uint as usize];
    let mut v10: uint32_t = vb11
        .wrapping_add(
            va10
                .wrapping_add(vb11 & vc11 | !vb11 & vd11)
                .wrapping_add(xk10)
                .wrapping_add(ti11) << 22 as libc::c_uint
                | va10
                    .wrapping_add(vb11 & vc11 | !vb11 & vd11)
                    .wrapping_add(xk10)
                    .wrapping_add(ti11) >> 10 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v10;
    let mut va11: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb12: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc12: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd12: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b12: *mut uint8_t = x.offset(48 as libc::c_uint as isize);
    let mut u11: uint32_t = load32(b12);
    let mut xk11: uint32_t = u11;
    let mut ti12: uint32_t = _t[12 as libc::c_uint as usize];
    let mut v11: uint32_t = vb12
        .wrapping_add(
            va11
                .wrapping_add(vb12 & vc12 | !vb12 & vd12)
                .wrapping_add(xk11)
                .wrapping_add(ti12) << 7 as libc::c_uint
                | va11
                    .wrapping_add(vb12 & vc12 | !vb12 & vd12)
                    .wrapping_add(xk11)
                    .wrapping_add(ti12) >> 25 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v11;
    let mut va12: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb13: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc13: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd13: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b13: *mut uint8_t = x.offset(52 as libc::c_uint as isize);
    let mut u12: uint32_t = load32(b13);
    let mut xk12: uint32_t = u12;
    let mut ti13: uint32_t = _t[13 as libc::c_uint as usize];
    let mut v12: uint32_t = vb13
        .wrapping_add(
            va12
                .wrapping_add(vb13 & vc13 | !vb13 & vd13)
                .wrapping_add(xk12)
                .wrapping_add(ti13) << 12 as libc::c_uint
                | va12
                    .wrapping_add(vb13 & vc13 | !vb13 & vd13)
                    .wrapping_add(xk12)
                    .wrapping_add(ti13) >> 20 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v12;
    let mut va13: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb14: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc14: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd14: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b14: *mut uint8_t = x.offset(56 as libc::c_uint as isize);
    let mut u13: uint32_t = load32(b14);
    let mut xk13: uint32_t = u13;
    let mut ti14: uint32_t = _t[14 as libc::c_uint as usize];
    let mut v13: uint32_t = vb14
        .wrapping_add(
            va13
                .wrapping_add(vb14 & vc14 | !vb14 & vd14)
                .wrapping_add(xk13)
                .wrapping_add(ti14) << 17 as libc::c_uint
                | va13
                    .wrapping_add(vb14 & vc14 | !vb14 & vd14)
                    .wrapping_add(xk13)
                    .wrapping_add(ti14) >> 15 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v13;
    let mut va14: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb15: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc15: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd15: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b15: *mut uint8_t = x.offset(60 as libc::c_uint as isize);
    let mut u14: uint32_t = load32(b15);
    let mut xk14: uint32_t = u14;
    let mut ti15: uint32_t = _t[15 as libc::c_uint as usize];
    let mut v14: uint32_t = vb15
        .wrapping_add(
            va14
                .wrapping_add(vb15 & vc15 | !vb15 & vd15)
                .wrapping_add(xk14)
                .wrapping_add(ti15) << 22 as libc::c_uint
                | va14
                    .wrapping_add(vb15 & vc15 | !vb15 & vd15)
                    .wrapping_add(xk14)
                    .wrapping_add(ti15) >> 10 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v14;
    let mut va15: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb16: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc16: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd16: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b16: *mut uint8_t = x.offset(4 as libc::c_uint as isize);
    let mut u15: uint32_t = load32(b16);
    let mut xk15: uint32_t = u15;
    let mut ti16: uint32_t = _t[16 as libc::c_uint as usize];
    let mut v15: uint32_t = vb16
        .wrapping_add(
            va15
                .wrapping_add(vb16 & vd16 | vc16 & !vd16)
                .wrapping_add(xk15)
                .wrapping_add(ti16) << 5 as libc::c_uint
                | va15
                    .wrapping_add(vb16 & vd16 | vc16 & !vd16)
                    .wrapping_add(xk15)
                    .wrapping_add(ti16) >> 27 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v15;
    let mut va16: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb17: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc17: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd17: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b17: *mut uint8_t = x.offset(24 as libc::c_uint as isize);
    let mut u16: uint32_t = load32(b17);
    let mut xk16: uint32_t = u16;
    let mut ti17: uint32_t = _t[17 as libc::c_uint as usize];
    let mut v16: uint32_t = vb17
        .wrapping_add(
            va16
                .wrapping_add(vb17 & vd17 | vc17 & !vd17)
                .wrapping_add(xk16)
                .wrapping_add(ti17) << 9 as libc::c_uint
                | va16
                    .wrapping_add(vb17 & vd17 | vc17 & !vd17)
                    .wrapping_add(xk16)
                    .wrapping_add(ti17) >> 23 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v16;
    let mut va17: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb18: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc18: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd18: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b18: *mut uint8_t = x.offset(44 as libc::c_uint as isize);
    let mut u17: uint32_t = load32(b18);
    let mut xk17: uint32_t = u17;
    let mut ti18: uint32_t = _t[18 as libc::c_uint as usize];
    let mut v17: uint32_t = vb18
        .wrapping_add(
            va17
                .wrapping_add(vb18 & vd18 | vc18 & !vd18)
                .wrapping_add(xk17)
                .wrapping_add(ti18) << 14 as libc::c_uint
                | va17
                    .wrapping_add(vb18 & vd18 | vc18 & !vd18)
                    .wrapping_add(xk17)
                    .wrapping_add(ti18) >> 18 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v17;
    let mut va18: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb19: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc19: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd19: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b19: *mut uint8_t = x;
    let mut u18: uint32_t = load32(b19);
    let mut xk18: uint32_t = u18;
    let mut ti19: uint32_t = _t[19 as libc::c_uint as usize];
    let mut v18: uint32_t = vb19
        .wrapping_add(
            va18
                .wrapping_add(vb19 & vd19 | vc19 & !vd19)
                .wrapping_add(xk18)
                .wrapping_add(ti19) << 20 as libc::c_uint
                | va18
                    .wrapping_add(vb19 & vd19 | vc19 & !vd19)
                    .wrapping_add(xk18)
                    .wrapping_add(ti19) >> 12 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v18;
    let mut va19: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb20: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc20: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd20: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b20: *mut uint8_t = x.offset(20 as libc::c_uint as isize);
    let mut u19: uint32_t = load32(b20);
    let mut xk19: uint32_t = u19;
    let mut ti20: uint32_t = _t[20 as libc::c_uint as usize];
    let mut v19: uint32_t = vb20
        .wrapping_add(
            va19
                .wrapping_add(vb20 & vd20 | vc20 & !vd20)
                .wrapping_add(xk19)
                .wrapping_add(ti20) << 5 as libc::c_uint
                | va19
                    .wrapping_add(vb20 & vd20 | vc20 & !vd20)
                    .wrapping_add(xk19)
                    .wrapping_add(ti20) >> 27 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v19;
    let mut va20: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb21: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc21: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd21: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b21: *mut uint8_t = x.offset(40 as libc::c_uint as isize);
    let mut u20: uint32_t = load32(b21);
    let mut xk20: uint32_t = u20;
    let mut ti21: uint32_t = _t[21 as libc::c_uint as usize];
    let mut v20: uint32_t = vb21
        .wrapping_add(
            va20
                .wrapping_add(vb21 & vd21 | vc21 & !vd21)
                .wrapping_add(xk20)
                .wrapping_add(ti21) << 9 as libc::c_uint
                | va20
                    .wrapping_add(vb21 & vd21 | vc21 & !vd21)
                    .wrapping_add(xk20)
                    .wrapping_add(ti21) >> 23 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v20;
    let mut va21: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb22: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc22: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd22: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b22: *mut uint8_t = x.offset(60 as libc::c_uint as isize);
    let mut u21: uint32_t = load32(b22);
    let mut xk21: uint32_t = u21;
    let mut ti22: uint32_t = _t[22 as libc::c_uint as usize];
    let mut v21: uint32_t = vb22
        .wrapping_add(
            va21
                .wrapping_add(vb22 & vd22 | vc22 & !vd22)
                .wrapping_add(xk21)
                .wrapping_add(ti22) << 14 as libc::c_uint
                | va21
                    .wrapping_add(vb22 & vd22 | vc22 & !vd22)
                    .wrapping_add(xk21)
                    .wrapping_add(ti22) >> 18 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v21;
    let mut va22: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb23: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc23: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd23: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b23: *mut uint8_t = x.offset(16 as libc::c_uint as isize);
    let mut u22: uint32_t = load32(b23);
    let mut xk22: uint32_t = u22;
    let mut ti23: uint32_t = _t[23 as libc::c_uint as usize];
    let mut v22: uint32_t = vb23
        .wrapping_add(
            va22
                .wrapping_add(vb23 & vd23 | vc23 & !vd23)
                .wrapping_add(xk22)
                .wrapping_add(ti23) << 20 as libc::c_uint
                | va22
                    .wrapping_add(vb23 & vd23 | vc23 & !vd23)
                    .wrapping_add(xk22)
                    .wrapping_add(ti23) >> 12 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v22;
    let mut va23: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb24: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc24: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd24: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b24: *mut uint8_t = x.offset(36 as libc::c_uint as isize);
    let mut u23: uint32_t = load32(b24);
    let mut xk23: uint32_t = u23;
    let mut ti24: uint32_t = _t[24 as libc::c_uint as usize];
    let mut v23: uint32_t = vb24
        .wrapping_add(
            va23
                .wrapping_add(vb24 & vd24 | vc24 & !vd24)
                .wrapping_add(xk23)
                .wrapping_add(ti24) << 5 as libc::c_uint
                | va23
                    .wrapping_add(vb24 & vd24 | vc24 & !vd24)
                    .wrapping_add(xk23)
                    .wrapping_add(ti24) >> 27 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v23;
    let mut va24: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb25: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc25: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd25: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b25: *mut uint8_t = x.offset(56 as libc::c_uint as isize);
    let mut u24: uint32_t = load32(b25);
    let mut xk24: uint32_t = u24;
    let mut ti25: uint32_t = _t[25 as libc::c_uint as usize];
    let mut v24: uint32_t = vb25
        .wrapping_add(
            va24
                .wrapping_add(vb25 & vd25 | vc25 & !vd25)
                .wrapping_add(xk24)
                .wrapping_add(ti25) << 9 as libc::c_uint
                | va24
                    .wrapping_add(vb25 & vd25 | vc25 & !vd25)
                    .wrapping_add(xk24)
                    .wrapping_add(ti25) >> 23 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v24;
    let mut va25: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb26: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc26: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd26: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b26: *mut uint8_t = x.offset(12 as libc::c_uint as isize);
    let mut u25: uint32_t = load32(b26);
    let mut xk25: uint32_t = u25;
    let mut ti26: uint32_t = _t[26 as libc::c_uint as usize];
    let mut v25: uint32_t = vb26
        .wrapping_add(
            va25
                .wrapping_add(vb26 & vd26 | vc26 & !vd26)
                .wrapping_add(xk25)
                .wrapping_add(ti26) << 14 as libc::c_uint
                | va25
                    .wrapping_add(vb26 & vd26 | vc26 & !vd26)
                    .wrapping_add(xk25)
                    .wrapping_add(ti26) >> 18 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v25;
    let mut va26: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb27: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc27: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd27: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b27: *mut uint8_t = x.offset(32 as libc::c_uint as isize);
    let mut u26: uint32_t = load32(b27);
    let mut xk26: uint32_t = u26;
    let mut ti27: uint32_t = _t[27 as libc::c_uint as usize];
    let mut v26: uint32_t = vb27
        .wrapping_add(
            va26
                .wrapping_add(vb27 & vd27 | vc27 & !vd27)
                .wrapping_add(xk26)
                .wrapping_add(ti27) << 20 as libc::c_uint
                | va26
                    .wrapping_add(vb27 & vd27 | vc27 & !vd27)
                    .wrapping_add(xk26)
                    .wrapping_add(ti27) >> 12 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v26;
    let mut va27: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb28: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc28: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd28: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b28: *mut uint8_t = x.offset(52 as libc::c_uint as isize);
    let mut u27: uint32_t = load32(b28);
    let mut xk27: uint32_t = u27;
    let mut ti28: uint32_t = _t[28 as libc::c_uint as usize];
    let mut v27: uint32_t = vb28
        .wrapping_add(
            va27
                .wrapping_add(vb28 & vd28 | vc28 & !vd28)
                .wrapping_add(xk27)
                .wrapping_add(ti28) << 5 as libc::c_uint
                | va27
                    .wrapping_add(vb28 & vd28 | vc28 & !vd28)
                    .wrapping_add(xk27)
                    .wrapping_add(ti28) >> 27 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v27;
    let mut va28: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb29: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc29: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd29: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b29: *mut uint8_t = x.offset(8 as libc::c_uint as isize);
    let mut u28: uint32_t = load32(b29);
    let mut xk28: uint32_t = u28;
    let mut ti29: uint32_t = _t[29 as libc::c_uint as usize];
    let mut v28: uint32_t = vb29
        .wrapping_add(
            va28
                .wrapping_add(vb29 & vd29 | vc29 & !vd29)
                .wrapping_add(xk28)
                .wrapping_add(ti29) << 9 as libc::c_uint
                | va28
                    .wrapping_add(vb29 & vd29 | vc29 & !vd29)
                    .wrapping_add(xk28)
                    .wrapping_add(ti29) >> 23 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v28;
    let mut va29: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb30: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc30: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd30: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b30: *mut uint8_t = x.offset(28 as libc::c_uint as isize);
    let mut u29: uint32_t = load32(b30);
    let mut xk29: uint32_t = u29;
    let mut ti30: uint32_t = _t[30 as libc::c_uint as usize];
    let mut v29: uint32_t = vb30
        .wrapping_add(
            va29
                .wrapping_add(vb30 & vd30 | vc30 & !vd30)
                .wrapping_add(xk29)
                .wrapping_add(ti30) << 14 as libc::c_uint
                | va29
                    .wrapping_add(vb30 & vd30 | vc30 & !vd30)
                    .wrapping_add(xk29)
                    .wrapping_add(ti30) >> 18 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v29;
    let mut va30: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb31: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc31: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd31: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b31: *mut uint8_t = x.offset(48 as libc::c_uint as isize);
    let mut u30: uint32_t = load32(b31);
    let mut xk30: uint32_t = u30;
    let mut ti31: uint32_t = _t[31 as libc::c_uint as usize];
    let mut v30: uint32_t = vb31
        .wrapping_add(
            va30
                .wrapping_add(vb31 & vd31 | vc31 & !vd31)
                .wrapping_add(xk30)
                .wrapping_add(ti31) << 20 as libc::c_uint
                | va30
                    .wrapping_add(vb31 & vd31 | vc31 & !vd31)
                    .wrapping_add(xk30)
                    .wrapping_add(ti31) >> 12 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v30;
    let mut va31: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb32: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc32: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd32: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b32: *mut uint8_t = x.offset(20 as libc::c_uint as isize);
    let mut u31: uint32_t = load32(b32);
    let mut xk31: uint32_t = u31;
    let mut ti32: uint32_t = _t[32 as libc::c_uint as usize];
    let mut v31: uint32_t = vb32
        .wrapping_add(
            va31.wrapping_add(vb32 ^ (vc32 ^ vd32)).wrapping_add(xk31).wrapping_add(ti32)
                << 4 as libc::c_uint
                | va31
                    .wrapping_add(vb32 ^ (vc32 ^ vd32))
                    .wrapping_add(xk31)
                    .wrapping_add(ti32) >> 28 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v31;
    let mut va32: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb33: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc33: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd33: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b33: *mut uint8_t = x.offset(32 as libc::c_uint as isize);
    let mut u32: uint32_t = load32(b33);
    let mut xk32: uint32_t = u32;
    let mut ti33: uint32_t = _t[33 as libc::c_uint as usize];
    let mut v32: uint32_t = vb33
        .wrapping_add(
            va32.wrapping_add(vb33 ^ (vc33 ^ vd33)).wrapping_add(xk32).wrapping_add(ti33)
                << 11 as libc::c_uint
                | va32
                    .wrapping_add(vb33 ^ (vc33 ^ vd33))
                    .wrapping_add(xk32)
                    .wrapping_add(ti33) >> 21 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v32;
    let mut va33: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb34: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc34: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd34: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b34: *mut uint8_t = x.offset(44 as libc::c_uint as isize);
    let mut u33: uint32_t = load32(b34);
    let mut xk33: uint32_t = u33;
    let mut ti34: uint32_t = _t[34 as libc::c_uint as usize];
    let mut v33: uint32_t = vb34
        .wrapping_add(
            va33.wrapping_add(vb34 ^ (vc34 ^ vd34)).wrapping_add(xk33).wrapping_add(ti34)
                << 16 as libc::c_uint
                | va33
                    .wrapping_add(vb34 ^ (vc34 ^ vd34))
                    .wrapping_add(xk33)
                    .wrapping_add(ti34) >> 16 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v33;
    let mut va34: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb35: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc35: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd35: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b35: *mut uint8_t = x.offset(56 as libc::c_uint as isize);
    let mut u34: uint32_t = load32(b35);
    let mut xk34: uint32_t = u34;
    let mut ti35: uint32_t = _t[35 as libc::c_uint as usize];
    let mut v34: uint32_t = vb35
        .wrapping_add(
            va34.wrapping_add(vb35 ^ (vc35 ^ vd35)).wrapping_add(xk34).wrapping_add(ti35)
                << 23 as libc::c_uint
                | va34
                    .wrapping_add(vb35 ^ (vc35 ^ vd35))
                    .wrapping_add(xk34)
                    .wrapping_add(ti35) >> 9 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v34;
    let mut va35: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb36: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc36: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd36: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b36: *mut uint8_t = x.offset(4 as libc::c_uint as isize);
    let mut u35: uint32_t = load32(b36);
    let mut xk35: uint32_t = u35;
    let mut ti36: uint32_t = _t[36 as libc::c_uint as usize];
    let mut v35: uint32_t = vb36
        .wrapping_add(
            va35.wrapping_add(vb36 ^ (vc36 ^ vd36)).wrapping_add(xk35).wrapping_add(ti36)
                << 4 as libc::c_uint
                | va35
                    .wrapping_add(vb36 ^ (vc36 ^ vd36))
                    .wrapping_add(xk35)
                    .wrapping_add(ti36) >> 28 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v35;
    let mut va36: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb37: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc37: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd37: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b37: *mut uint8_t = x.offset(16 as libc::c_uint as isize);
    let mut u36: uint32_t = load32(b37);
    let mut xk36: uint32_t = u36;
    let mut ti37: uint32_t = _t[37 as libc::c_uint as usize];
    let mut v36: uint32_t = vb37
        .wrapping_add(
            va36.wrapping_add(vb37 ^ (vc37 ^ vd37)).wrapping_add(xk36).wrapping_add(ti37)
                << 11 as libc::c_uint
                | va36
                    .wrapping_add(vb37 ^ (vc37 ^ vd37))
                    .wrapping_add(xk36)
                    .wrapping_add(ti37) >> 21 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v36;
    let mut va37: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb38: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc38: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd38: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b38: *mut uint8_t = x.offset(28 as libc::c_uint as isize);
    let mut u37: uint32_t = load32(b38);
    let mut xk37: uint32_t = u37;
    let mut ti38: uint32_t = _t[38 as libc::c_uint as usize];
    let mut v37: uint32_t = vb38
        .wrapping_add(
            va37.wrapping_add(vb38 ^ (vc38 ^ vd38)).wrapping_add(xk37).wrapping_add(ti38)
                << 16 as libc::c_uint
                | va37
                    .wrapping_add(vb38 ^ (vc38 ^ vd38))
                    .wrapping_add(xk37)
                    .wrapping_add(ti38) >> 16 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v37;
    let mut va38: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb39: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc39: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd39: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b39: *mut uint8_t = x.offset(40 as libc::c_uint as isize);
    let mut u38: uint32_t = load32(b39);
    let mut xk38: uint32_t = u38;
    let mut ti39: uint32_t = _t[39 as libc::c_uint as usize];
    let mut v38: uint32_t = vb39
        .wrapping_add(
            va38.wrapping_add(vb39 ^ (vc39 ^ vd39)).wrapping_add(xk38).wrapping_add(ti39)
                << 23 as libc::c_uint
                | va38
                    .wrapping_add(vb39 ^ (vc39 ^ vd39))
                    .wrapping_add(xk38)
                    .wrapping_add(ti39) >> 9 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v38;
    let mut va39: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb40: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc40: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd40: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b40: *mut uint8_t = x.offset(52 as libc::c_uint as isize);
    let mut u39: uint32_t = load32(b40);
    let mut xk39: uint32_t = u39;
    let mut ti40: uint32_t = _t[40 as libc::c_uint as usize];
    let mut v39: uint32_t = vb40
        .wrapping_add(
            va39.wrapping_add(vb40 ^ (vc40 ^ vd40)).wrapping_add(xk39).wrapping_add(ti40)
                << 4 as libc::c_uint
                | va39
                    .wrapping_add(vb40 ^ (vc40 ^ vd40))
                    .wrapping_add(xk39)
                    .wrapping_add(ti40) >> 28 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v39;
    let mut va40: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb41: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc41: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd41: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b41: *mut uint8_t = x;
    let mut u40: uint32_t = load32(b41);
    let mut xk40: uint32_t = u40;
    let mut ti41: uint32_t = _t[41 as libc::c_uint as usize];
    let mut v40: uint32_t = vb41
        .wrapping_add(
            va40.wrapping_add(vb41 ^ (vc41 ^ vd41)).wrapping_add(xk40).wrapping_add(ti41)
                << 11 as libc::c_uint
                | va40
                    .wrapping_add(vb41 ^ (vc41 ^ vd41))
                    .wrapping_add(xk40)
                    .wrapping_add(ti41) >> 21 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v40;
    let mut va41: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb42: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc42: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd42: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b42: *mut uint8_t = x.offset(12 as libc::c_uint as isize);
    let mut u41: uint32_t = load32(b42);
    let mut xk41: uint32_t = u41;
    let mut ti42: uint32_t = _t[42 as libc::c_uint as usize];
    let mut v41: uint32_t = vb42
        .wrapping_add(
            va41.wrapping_add(vb42 ^ (vc42 ^ vd42)).wrapping_add(xk41).wrapping_add(ti42)
                << 16 as libc::c_uint
                | va41
                    .wrapping_add(vb42 ^ (vc42 ^ vd42))
                    .wrapping_add(xk41)
                    .wrapping_add(ti42) >> 16 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v41;
    let mut va42: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb43: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc43: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd43: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b43: *mut uint8_t = x.offset(24 as libc::c_uint as isize);
    let mut u42: uint32_t = load32(b43);
    let mut xk42: uint32_t = u42;
    let mut ti43: uint32_t = _t[43 as libc::c_uint as usize];
    let mut v42: uint32_t = vb43
        .wrapping_add(
            va42.wrapping_add(vb43 ^ (vc43 ^ vd43)).wrapping_add(xk42).wrapping_add(ti43)
                << 23 as libc::c_uint
                | va42
                    .wrapping_add(vb43 ^ (vc43 ^ vd43))
                    .wrapping_add(xk42)
                    .wrapping_add(ti43) >> 9 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v42;
    let mut va43: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb44: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc44: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd44: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b44: *mut uint8_t = x.offset(36 as libc::c_uint as isize);
    let mut u43: uint32_t = load32(b44);
    let mut xk43: uint32_t = u43;
    let mut ti44: uint32_t = _t[44 as libc::c_uint as usize];
    let mut v43: uint32_t = vb44
        .wrapping_add(
            va43.wrapping_add(vb44 ^ (vc44 ^ vd44)).wrapping_add(xk43).wrapping_add(ti44)
                << 4 as libc::c_uint
                | va43
                    .wrapping_add(vb44 ^ (vc44 ^ vd44))
                    .wrapping_add(xk43)
                    .wrapping_add(ti44) >> 28 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v43;
    let mut va44: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb45: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc45: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd45: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b45: *mut uint8_t = x.offset(48 as libc::c_uint as isize);
    let mut u44: uint32_t = load32(b45);
    let mut xk44: uint32_t = u44;
    let mut ti45: uint32_t = _t[45 as libc::c_uint as usize];
    let mut v44: uint32_t = vb45
        .wrapping_add(
            va44.wrapping_add(vb45 ^ (vc45 ^ vd45)).wrapping_add(xk44).wrapping_add(ti45)
                << 11 as libc::c_uint
                | va44
                    .wrapping_add(vb45 ^ (vc45 ^ vd45))
                    .wrapping_add(xk44)
                    .wrapping_add(ti45) >> 21 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v44;
    let mut va45: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb46: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc46: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd46: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b46: *mut uint8_t = x.offset(60 as libc::c_uint as isize);
    let mut u45: uint32_t = load32(b46);
    let mut xk45: uint32_t = u45;
    let mut ti46: uint32_t = _t[46 as libc::c_uint as usize];
    let mut v45: uint32_t = vb46
        .wrapping_add(
            va45.wrapping_add(vb46 ^ (vc46 ^ vd46)).wrapping_add(xk45).wrapping_add(ti46)
                << 16 as libc::c_uint
                | va45
                    .wrapping_add(vb46 ^ (vc46 ^ vd46))
                    .wrapping_add(xk45)
                    .wrapping_add(ti46) >> 16 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v45;
    let mut va46: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb47: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc47: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd47: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b47: *mut uint8_t = x.offset(8 as libc::c_uint as isize);
    let mut u46: uint32_t = load32(b47);
    let mut xk46: uint32_t = u46;
    let mut ti47: uint32_t = _t[47 as libc::c_uint as usize];
    let mut v46: uint32_t = vb47
        .wrapping_add(
            va46.wrapping_add(vb47 ^ (vc47 ^ vd47)).wrapping_add(xk46).wrapping_add(ti47)
                << 23 as libc::c_uint
                | va46
                    .wrapping_add(vb47 ^ (vc47 ^ vd47))
                    .wrapping_add(xk46)
                    .wrapping_add(ti47) >> 9 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v46;
    let mut va47: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb48: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc48: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd48: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b48: *mut uint8_t = x;
    let mut u47: uint32_t = load32(b48);
    let mut xk47: uint32_t = u47;
    let mut ti48: uint32_t = _t[48 as libc::c_uint as usize];
    let mut v47: uint32_t = vb48
        .wrapping_add(
            va47
                .wrapping_add(vc48 ^ (vb48 | !vd48))
                .wrapping_add(xk47)
                .wrapping_add(ti48) << 6 as libc::c_uint
                | va47
                    .wrapping_add(vc48 ^ (vb48 | !vd48))
                    .wrapping_add(xk47)
                    .wrapping_add(ti48) >> 26 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v47;
    let mut va48: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb49: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc49: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd49: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b49: *mut uint8_t = x.offset(28 as libc::c_uint as isize);
    let mut u48: uint32_t = load32(b49);
    let mut xk48: uint32_t = u48;
    let mut ti49: uint32_t = _t[49 as libc::c_uint as usize];
    let mut v48: uint32_t = vb49
        .wrapping_add(
            va48
                .wrapping_add(vc49 ^ (vb49 | !vd49))
                .wrapping_add(xk48)
                .wrapping_add(ti49) << 10 as libc::c_uint
                | va48
                    .wrapping_add(vc49 ^ (vb49 | !vd49))
                    .wrapping_add(xk48)
                    .wrapping_add(ti49) >> 22 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v48;
    let mut va49: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb50: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc50: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd50: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b50: *mut uint8_t = x.offset(56 as libc::c_uint as isize);
    let mut u49: uint32_t = load32(b50);
    let mut xk49: uint32_t = u49;
    let mut ti50: uint32_t = _t[50 as libc::c_uint as usize];
    let mut v49: uint32_t = vb50
        .wrapping_add(
            va49
                .wrapping_add(vc50 ^ (vb50 | !vd50))
                .wrapping_add(xk49)
                .wrapping_add(ti50) << 15 as libc::c_uint
                | va49
                    .wrapping_add(vc50 ^ (vb50 | !vd50))
                    .wrapping_add(xk49)
                    .wrapping_add(ti50) >> 17 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v49;
    let mut va50: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb51: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc51: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd51: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b51: *mut uint8_t = x.offset(20 as libc::c_uint as isize);
    let mut u50: uint32_t = load32(b51);
    let mut xk50: uint32_t = u50;
    let mut ti51: uint32_t = _t[51 as libc::c_uint as usize];
    let mut v50: uint32_t = vb51
        .wrapping_add(
            va50
                .wrapping_add(vc51 ^ (vb51 | !vd51))
                .wrapping_add(xk50)
                .wrapping_add(ti51) << 21 as libc::c_uint
                | va50
                    .wrapping_add(vc51 ^ (vb51 | !vd51))
                    .wrapping_add(xk50)
                    .wrapping_add(ti51) >> 11 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v50;
    let mut va51: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb52: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc52: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd52: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b52: *mut uint8_t = x.offset(48 as libc::c_uint as isize);
    let mut u51: uint32_t = load32(b52);
    let mut xk51: uint32_t = u51;
    let mut ti52: uint32_t = _t[52 as libc::c_uint as usize];
    let mut v51: uint32_t = vb52
        .wrapping_add(
            va51
                .wrapping_add(vc52 ^ (vb52 | !vd52))
                .wrapping_add(xk51)
                .wrapping_add(ti52) << 6 as libc::c_uint
                | va51
                    .wrapping_add(vc52 ^ (vb52 | !vd52))
                    .wrapping_add(xk51)
                    .wrapping_add(ti52) >> 26 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v51;
    let mut va52: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb53: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc53: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd53: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b53: *mut uint8_t = x.offset(12 as libc::c_uint as isize);
    let mut u52: uint32_t = load32(b53);
    let mut xk52: uint32_t = u52;
    let mut ti53: uint32_t = _t[53 as libc::c_uint as usize];
    let mut v52: uint32_t = vb53
        .wrapping_add(
            va52
                .wrapping_add(vc53 ^ (vb53 | !vd53))
                .wrapping_add(xk52)
                .wrapping_add(ti53) << 10 as libc::c_uint
                | va52
                    .wrapping_add(vc53 ^ (vb53 | !vd53))
                    .wrapping_add(xk52)
                    .wrapping_add(ti53) >> 22 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v52;
    let mut va53: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb54: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc54: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd54: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b54: *mut uint8_t = x.offset(40 as libc::c_uint as isize);
    let mut u53: uint32_t = load32(b54);
    let mut xk53: uint32_t = u53;
    let mut ti54: uint32_t = _t[54 as libc::c_uint as usize];
    let mut v53: uint32_t = vb54
        .wrapping_add(
            va53
                .wrapping_add(vc54 ^ (vb54 | !vd54))
                .wrapping_add(xk53)
                .wrapping_add(ti54) << 15 as libc::c_uint
                | va53
                    .wrapping_add(vc54 ^ (vb54 | !vd54))
                    .wrapping_add(xk53)
                    .wrapping_add(ti54) >> 17 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v53;
    let mut va54: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb55: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc55: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd55: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b55: *mut uint8_t = x.offset(4 as libc::c_uint as isize);
    let mut u54: uint32_t = load32(b55);
    let mut xk54: uint32_t = u54;
    let mut ti55: uint32_t = _t[55 as libc::c_uint as usize];
    let mut v54: uint32_t = vb55
        .wrapping_add(
            va54
                .wrapping_add(vc55 ^ (vb55 | !vd55))
                .wrapping_add(xk54)
                .wrapping_add(ti55) << 21 as libc::c_uint
                | va54
                    .wrapping_add(vc55 ^ (vb55 | !vd55))
                    .wrapping_add(xk54)
                    .wrapping_add(ti55) >> 11 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v54;
    let mut va55: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb56: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc56: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd56: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b56: *mut uint8_t = x.offset(32 as libc::c_uint as isize);
    let mut u55: uint32_t = load32(b56);
    let mut xk55: uint32_t = u55;
    let mut ti56: uint32_t = _t[56 as libc::c_uint as usize];
    let mut v55: uint32_t = vb56
        .wrapping_add(
            va55
                .wrapping_add(vc56 ^ (vb56 | !vd56))
                .wrapping_add(xk55)
                .wrapping_add(ti56) << 6 as libc::c_uint
                | va55
                    .wrapping_add(vc56 ^ (vb56 | !vd56))
                    .wrapping_add(xk55)
                    .wrapping_add(ti56) >> 26 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v55;
    let mut va56: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb57: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc57: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd57: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b57: *mut uint8_t = x.offset(60 as libc::c_uint as isize);
    let mut u56: uint32_t = load32(b57);
    let mut xk56: uint32_t = u56;
    let mut ti57: uint32_t = _t[57 as libc::c_uint as usize];
    let mut v56: uint32_t = vb57
        .wrapping_add(
            va56
                .wrapping_add(vc57 ^ (vb57 | !vd57))
                .wrapping_add(xk56)
                .wrapping_add(ti57) << 10 as libc::c_uint
                | va56
                    .wrapping_add(vc57 ^ (vb57 | !vd57))
                    .wrapping_add(xk56)
                    .wrapping_add(ti57) >> 22 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v56;
    let mut va57: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb58: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc58: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd58: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b58: *mut uint8_t = x.offset(24 as libc::c_uint as isize);
    let mut u57: uint32_t = load32(b58);
    let mut xk57: uint32_t = u57;
    let mut ti58: uint32_t = _t[58 as libc::c_uint as usize];
    let mut v57: uint32_t = vb58
        .wrapping_add(
            va57
                .wrapping_add(vc58 ^ (vb58 | !vd58))
                .wrapping_add(xk57)
                .wrapping_add(ti58) << 15 as libc::c_uint
                | va57
                    .wrapping_add(vc58 ^ (vb58 | !vd58))
                    .wrapping_add(xk57)
                    .wrapping_add(ti58) >> 17 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v57;
    let mut va58: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb59: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc59: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd59: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b59: *mut uint8_t = x.offset(52 as libc::c_uint as isize);
    let mut u58: uint32_t = load32(b59);
    let mut xk58: uint32_t = u58;
    let mut ti59: uint32_t = _t[59 as libc::c_uint as usize];
    let mut v58: uint32_t = vb59
        .wrapping_add(
            va58
                .wrapping_add(vc59 ^ (vb59 | !vd59))
                .wrapping_add(xk58)
                .wrapping_add(ti59) << 21 as libc::c_uint
                | va58
                    .wrapping_add(vc59 ^ (vb59 | !vd59))
                    .wrapping_add(xk58)
                    .wrapping_add(ti59) >> 11 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v58;
    let mut va59: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vb60: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vc60: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vd60: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut b60: *mut uint8_t = x.offset(16 as libc::c_uint as isize);
    let mut u59: uint32_t = load32(b60);
    let mut xk59: uint32_t = u59;
    let mut ti60: uint32_t = _t[60 as libc::c_uint as usize];
    let mut v59: uint32_t = vb60
        .wrapping_add(
            va59
                .wrapping_add(vc60 ^ (vb60 | !vd60))
                .wrapping_add(xk59)
                .wrapping_add(ti60) << 6 as libc::c_uint
                | va59
                    .wrapping_add(vc60 ^ (vb60 | !vd60))
                    .wrapping_add(xk59)
                    .wrapping_add(ti60) >> 26 as libc::c_uint,
        );
    *abcd.offset(0 as libc::c_uint as isize) = v59;
    let mut va60: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vb61: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vc61: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vd61: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut b61: *mut uint8_t = x.offset(44 as libc::c_uint as isize);
    let mut u60: uint32_t = load32(b61);
    let mut xk60: uint32_t = u60;
    let mut ti61: uint32_t = _t[61 as libc::c_uint as usize];
    let mut v60: uint32_t = vb61
        .wrapping_add(
            va60
                .wrapping_add(vc61 ^ (vb61 | !vd61))
                .wrapping_add(xk60)
                .wrapping_add(ti61) << 10 as libc::c_uint
                | va60
                    .wrapping_add(vc61 ^ (vb61 | !vd61))
                    .wrapping_add(xk60)
                    .wrapping_add(ti61) >> 22 as libc::c_uint,
        );
    *abcd.offset(3 as libc::c_uint as isize) = v60;
    let mut va61: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vb62: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vc62: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut vd62: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut b62: *mut uint8_t = x.offset(8 as libc::c_uint as isize);
    let mut u61: uint32_t = load32(b62);
    let mut xk61: uint32_t = u61;
    let mut ti62: uint32_t = _t[62 as libc::c_uint as usize];
    let mut v61: uint32_t = vb62
        .wrapping_add(
            va61
                .wrapping_add(vc62 ^ (vb62 | !vd62))
                .wrapping_add(xk61)
                .wrapping_add(ti62) << 15 as libc::c_uint
                | va61
                    .wrapping_add(vc62 ^ (vb62 | !vd62))
                    .wrapping_add(xk61)
                    .wrapping_add(ti62) >> 17 as libc::c_uint,
        );
    *abcd.offset(2 as libc::c_uint as isize) = v61;
    let mut va62: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut vb: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut vc: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    let mut vd: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b63: *mut uint8_t = x.offset(36 as libc::c_uint as isize);
    let mut u62: uint32_t = load32(b63);
    let mut xk62: uint32_t = u62;
    let mut ti: uint32_t = _t[63 as libc::c_uint as usize];
    let mut v62: uint32_t = vb
        .wrapping_add(
            va62.wrapping_add(vc ^ (vb | !vd)).wrapping_add(xk62).wrapping_add(ti)
                << 21 as libc::c_uint
                | va62.wrapping_add(vc ^ (vb | !vd)).wrapping_add(xk62).wrapping_add(ti)
                    >> 11 as libc::c_uint,
        );
    *abcd.offset(1 as libc::c_uint as isize) = v62;
    let mut a: uint32_t = *abcd.offset(0 as libc::c_uint as isize);
    let mut b: uint32_t = *abcd.offset(1 as libc::c_uint as isize);
    let mut c: uint32_t = *abcd.offset(2 as libc::c_uint as isize);
    let mut d: uint32_t = *abcd.offset(3 as libc::c_uint as isize);
    *abcd.offset(0 as libc::c_uint as isize) = a.wrapping_add(aa);
    *abcd.offset(1 as libc::c_uint as isize) = b.wrapping_add(bb);
    *abcd.offset(2 as libc::c_uint as isize) = c.wrapping_add(cc);
    *abcd.offset(3 as libc::c_uint as isize) = d.wrapping_add(dd);
}
unsafe extern "C" fn pad(mut len: uint64_t, mut dst: *mut uint8_t) {
    let mut dst1: *mut uint8_t = dst;
    *dst1.offset(0 as libc::c_uint as isize) = 0x80 as libc::c_uint as uint8_t;
    let mut dst2: *mut uint8_t = dst.offset(1 as libc::c_uint as isize);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i
        < (128 as libc::c_uint)
            .wrapping_sub(
                (9 as libc::c_uint)
                    .wrapping_add((len % 64 as libc::c_uint as uint64_t) as uint32_t),
            )
            .wrapping_rem(64 as libc::c_uint)
    {
        *dst2.offset(i as isize) = 0 as libc::c_uint as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut dst3: *mut uint8_t = dst
        .offset(1 as libc::c_uint as isize)
        .offset(
            (128 as libc::c_uint)
                .wrapping_sub(
                    (9 as libc::c_uint)
                        .wrapping_add((len % 64 as libc::c_uint as uint64_t) as uint32_t),
                )
                .wrapping_rem(64 as libc::c_uint) as isize,
        );
    store64(dst3, len << 3 as libc::c_uint);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_finish(
    mut s: *mut uint32_t,
    mut dst: *mut uint8_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *s.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *s.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *s.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        *s.offset(i as isize),
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_update_multi(
    mut s: *mut uint32_t,
    mut blocks: *mut uint8_t,
    mut n_blocks: uint32_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < n_blocks {
        let mut sz: uint32_t = 64 as libc::c_uint;
        let mut block: *mut uint8_t = blocks.offset((sz * i) as isize);
        update(s, block);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_update_last(
    mut s: *mut uint32_t,
    mut prev_len: uint64_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut blocks_n: uint32_t = input_len.wrapping_div(64 as libc::c_uint);
    let mut blocks_len: uint32_t = blocks_n.wrapping_mul(64 as libc::c_uint);
    let mut blocks: *mut uint8_t = input;
    let mut rest_len: uint32_t = input_len.wrapping_sub(blocks_len);
    let mut rest: *mut uint8_t = input.offset(blocks_len as isize);
    Hacl_Hash_MD5_update_multi(s, blocks, blocks_n);
    let mut total_input_len: uint64_t = prev_len.wrapping_add(input_len as uint64_t);
    let mut pad_len: uint32_t = (1 as libc::c_uint)
        .wrapping_add(
            (128 as libc::c_uint)
                .wrapping_sub(
                    (9 as libc::c_uint)
                        .wrapping_add(
                            (total_input_len % 64 as libc::c_uint as uint64_t)
                                as uint32_t,
                        ),
                )
                .wrapping_rem(64 as libc::c_uint),
        )
        .wrapping_add(8 as libc::c_uint);
    let mut tmp_len: uint32_t = rest_len.wrapping_add(pad_len);
    let mut tmp_twoblocks: [uint8_t; 128] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut tmp: *mut uint8_t = tmp_twoblocks.as_mut_ptr();
    let mut tmp_rest: *mut uint8_t = tmp;
    let mut tmp_pad: *mut uint8_t = tmp.offset(rest_len as isize);
    memcpy(
        tmp_rest as *mut libc::c_void,
        rest as *const libc::c_void,
        (rest_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    pad(total_input_len, tmp_pad);
    Hacl_Hash_MD5_update_multi(s, tmp, tmp_len.wrapping_div(64 as libc::c_uint));
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_hash_oneshot(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut s: [uint32_t; 4] = [
        0x67452301 as libc::c_uint,
        0xefcdab89 as libc::c_uint,
        0x98badcfe as libc::c_uint,
        0x10325476 as libc::c_uint,
    ];
    let mut blocks_n0: uint32_t = input_len.wrapping_div(64 as libc::c_uint);
    let mut blocks_n1: uint32_t = 0;
    if input_len.wrapping_rem(64 as libc::c_uint) == 0 as libc::c_uint
        && blocks_n0 > 0 as libc::c_uint
    {
        blocks_n1 = blocks_n0.wrapping_sub(1 as libc::c_uint);
    } else {
        blocks_n1 = blocks_n0;
    }
    let mut blocks_len0: uint32_t = blocks_n1.wrapping_mul(64 as libc::c_uint);
    let mut blocks0: *mut uint8_t = input;
    let mut rest_len0: uint32_t = input_len.wrapping_sub(blocks_len0);
    let mut rest0: *mut uint8_t = input.offset(blocks_len0 as isize);
    let mut blocks_n: uint32_t = blocks_n1;
    let mut blocks_len: uint32_t = blocks_len0;
    let mut blocks: *mut uint8_t = blocks0;
    let mut rest_len: uint32_t = rest_len0;
    let mut rest: *mut uint8_t = rest0;
    Hacl_Hash_MD5_update_multi(s.as_mut_ptr(), blocks, blocks_n);
    Hacl_Hash_MD5_update_last(s.as_mut_ptr(), blocks_len as uint64_t, rest, rest_len);
    Hacl_Hash_MD5_finish(s.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_malloc() -> *mut Hacl_Streaming_MD_state_32 {
    let mut buf: *mut uint8_t = calloc(
        64 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut block_state: *mut uint32_t = calloc(
        4 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    Hacl_Hash_MD5_init(block_state);
    let mut s: Hacl_Streaming_MD_state_32 = {
        let mut init = Hacl_Streaming_MD_state_32_s {
            block_state: block_state,
            buf: buf,
            total_len: 0 as libc::c_uint as uint64_t,
        };
        init
    };
    let mut p: *mut Hacl_Streaming_MD_state_32 = malloc(
        ::core::mem::size_of::<Hacl_Streaming_MD_state_32>() as libc::c_ulong,
    ) as *mut Hacl_Streaming_MD_state_32;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_reset(
    mut state: *mut Hacl_Streaming_MD_state_32,
) {
    let mut block_state: *mut uint32_t = (*state).block_state;
    Hacl_Hash_MD5_init(block_state);
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_update(
    mut state: *mut Hacl_Streaming_MD_state_32,
    mut chunk: *mut uint8_t,
    mut chunk_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut block_state: *mut uint32_t = (*state).block_state;
    let mut total_len: uint64_t = (*state).total_len;
    if chunk_len as uint64_t
        > (2305843009213693951 as libc::c_ulonglong).wrapping_sub(total_len)
    {
        return 3 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    let mut sz: uint32_t = 0;
    if total_len % 64 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        sz = 64 as libc::c_uint;
    } else {
        sz = (total_len % 64 as libc::c_uint as uint64_t) as uint32_t;
    }
    if chunk_len <= (64 as libc::c_uint).wrapping_sub(sz) {
        let mut buf: *mut uint8_t = (*state).buf;
        let mut total_len1: uint64_t = (*state).total_len;
        let mut sz1: uint32_t = 0;
        if total_len1 % 64 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1 > 0 as libc::c_ulonglong
        {
            sz1 = 64 as libc::c_uint;
        } else {
            sz1 = (total_len1 % 64 as libc::c_uint as uint64_t) as uint32_t;
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
    } else if sz == 0 as libc::c_uint {
        let mut buf_0: *mut uint8_t = (*state).buf;
        let mut total_len1_0: uint64_t = (*state).total_len;
        let mut sz1_0: uint32_t = 0;
        if total_len1_0 % 64 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_0 > 0 as libc::c_ulonglong
        {
            sz1_0 = 64 as libc::c_uint;
        } else {
            sz1_0 = (total_len1_0 % 64 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_0 == 0 as libc::c_uint) {
            Hacl_Hash_MD5_update_multi(block_state, buf_0, 1 as libc::c_uint);
        }
        let mut ite: uint32_t = 0;
        if chunk_len as uint64_t % 64 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong && chunk_len as uint64_t > 0 as libc::c_ulonglong
        {
            ite = 64 as libc::c_uint;
        } else {
            ite = (chunk_len as uint64_t % 64 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks: uint32_t = chunk_len
            .wrapping_sub(ite)
            .wrapping_div(64 as libc::c_uint);
        let mut data1_len: uint32_t = n_blocks.wrapping_mul(64 as libc::c_uint);
        let mut data2_len: uint32_t = chunk_len.wrapping_sub(data1_len);
        let mut data1: *mut uint8_t = chunk;
        let mut data2: *mut uint8_t = chunk.offset(data1_len as isize);
        Hacl_Hash_MD5_update_multi(
            block_state,
            data1,
            data1_len.wrapping_div(64 as libc::c_uint),
        );
        let mut dst: *mut uint8_t = buf_0;
        memcpy(
            dst as *mut libc::c_void,
            data2 as *const libc::c_void,
            (data2_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        (*state).total_len = total_len1_0.wrapping_add(chunk_len as uint64_t);
    } else {
        let mut diff: uint32_t = (64 as libc::c_uint).wrapping_sub(sz);
        let mut chunk1: *mut uint8_t = chunk;
        let mut chunk2: *mut uint8_t = chunk.offset(diff as isize);
        let mut buf_1: *mut uint8_t = (*state).buf;
        let mut total_len10: uint64_t = (*state).total_len;
        let mut sz10: uint32_t = 0;
        if total_len10 % 64 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len10 > 0 as libc::c_ulonglong
        {
            sz10 = 64 as libc::c_uint;
        } else {
            sz10 = (total_len10 % 64 as libc::c_uint as uint64_t) as uint32_t;
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
        let mut buf0: *mut uint8_t = (*state).buf;
        let mut total_len1_1: uint64_t = (*state).total_len;
        let mut sz1_1: uint32_t = 0;
        if total_len1_1 % 64 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_1 > 0 as libc::c_ulonglong
        {
            sz1_1 = 64 as libc::c_uint;
        } else {
            sz1_1 = (total_len1_1 % 64 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_1 == 0 as libc::c_uint) {
            Hacl_Hash_MD5_update_multi(block_state, buf0, 1 as libc::c_uint);
        }
        let mut ite_0: uint32_t = 0;
        if chunk_len.wrapping_sub(diff) as uint64_t % 64 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong
            && chunk_len.wrapping_sub(diff) as uint64_t > 0 as libc::c_ulonglong
        {
            ite_0 = 64 as libc::c_uint;
        } else {
            ite_0 = (chunk_len.wrapping_sub(diff) as uint64_t
                % 64 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(ite_0)
            .wrapping_div(64 as libc::c_uint);
        let mut data1_len_0: uint32_t = n_blocks_0.wrapping_mul(64 as libc::c_uint);
        let mut data2_len_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(data1_len_0);
        let mut data1_0: *mut uint8_t = chunk2;
        let mut data2_0: *mut uint8_t = chunk2.offset(data1_len_0 as isize);
        Hacl_Hash_MD5_update_multi(
            block_state,
            data1_0,
            data1_len_0.wrapping_div(64 as libc::c_uint),
        );
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
    }
    return 0 as libc::c_int as Hacl_Streaming_Types_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_digest(
    mut state: *mut Hacl_Streaming_MD_state_32,
    mut output: *mut uint8_t,
) {
    let mut block_state: *mut uint32_t = (*state).block_state;
    let mut buf_: *mut uint8_t = (*state).buf;
    let mut total_len: uint64_t = (*state).total_len;
    let mut r: uint32_t = 0;
    if total_len % 64 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        r = 64 as libc::c_uint;
    } else {
        r = (total_len % 64 as libc::c_uint as uint64_t) as uint32_t;
    }
    let mut buf_1: *mut uint8_t = buf_;
    let mut tmp_block_state: [uint32_t; 4] = [0 as libc::c_uint, 0, 0, 0];
    memcpy(
        tmp_block_state.as_mut_ptr() as *mut libc::c_void,
        block_state as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut buf_multi: *mut uint8_t = buf_1;
    let mut ite: uint32_t = 0;
    if r.wrapping_rem(64 as libc::c_uint) == 0 as libc::c_uint && r > 0 as libc::c_uint {
        ite = 64 as libc::c_uint;
    } else {
        ite = r.wrapping_rem(64 as libc::c_uint);
    }
    let mut buf_last: *mut uint8_t = buf_1.offset(r as isize).offset(-(ite as isize));
    Hacl_Hash_MD5_update_multi(
        tmp_block_state.as_mut_ptr(),
        buf_multi,
        0 as libc::c_uint,
    );
    let mut prev_len_last: uint64_t = total_len.wrapping_sub(r as uint64_t);
    Hacl_Hash_MD5_update_last(tmp_block_state.as_mut_ptr(), prev_len_last, buf_last, r);
    Hacl_Hash_MD5_finish(tmp_block_state.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_free(mut state: *mut Hacl_Streaming_MD_state_32) {
    let mut scrut: Hacl_Streaming_MD_state_32 = *state;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: *mut uint32_t = scrut.block_state;
    free(block_state as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_copy(
    mut state: *mut Hacl_Streaming_MD_state_32,
) -> *mut Hacl_Streaming_MD_state_32 {
    let mut block_state0: *mut uint32_t = (*state).block_state;
    let mut buf0: *mut uint8_t = (*state).buf;
    let mut total_len0: uint64_t = (*state).total_len;
    let mut buf: *mut uint8_t = calloc(
        64 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    memcpy(
        buf as *mut libc::c_void,
        buf0 as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut block_state: *mut uint32_t = calloc(
        4 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    memcpy(
        block_state as *mut libc::c_void,
        block_state0 as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut s: Hacl_Streaming_MD_state_32 = {
        let mut init = Hacl_Streaming_MD_state_32_s {
            block_state: block_state,
            buf: buf,
            total_len: total_len0,
        };
        init
    };
    let mut p: *mut Hacl_Streaming_MD_state_32 = malloc(
        ::core::mem::size_of::<Hacl_Streaming_MD_state_32>() as libc::c_ulong,
    ) as *mut Hacl_Streaming_MD_state_32;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_MD5_hash(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    Hacl_Hash_MD5_hash_oneshot(output, input, input_len);
}
