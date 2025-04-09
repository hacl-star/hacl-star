#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]
#![feature(extern_types)]
extern "C" {
    pub type __sFILEX;
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
    static mut __stderrp: *mut FILE;
    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
}
pub type __int64_t = libc::c_longlong;
pub type __darwin_size_t = libc::c_ulong;
pub type __darwin_off_t = __int64_t;
pub type size_t = __darwin_size_t;
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type fpos_t = __darwin_off_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __sbuf {
    pub _base: *mut libc::c_uchar,
    pub _size: libc::c_int,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct __sFILE {
    pub _p: *mut libc::c_uchar,
    pub _r: libc::c_int,
    pub _w: libc::c_int,
    pub _flags: libc::c_short,
    pub _file: libc::c_short,
    pub _bf: __sbuf,
    pub _lbfsize: libc::c_int,
    pub _cookie: *mut libc::c_void,
    pub _close: Option::<unsafe extern "C" fn(*mut libc::c_void) -> libc::c_int>,
    pub _read: Option::<
        unsafe extern "C" fn(
            *mut libc::c_void,
            *mut libc::c_char,
            libc::c_int,
        ) -> libc::c_int,
    >,
    pub _seek: Option::<
        unsafe extern "C" fn(*mut libc::c_void, fpos_t, libc::c_int) -> fpos_t,
    >,
    pub _write: Option::<
        unsafe extern "C" fn(
            *mut libc::c_void,
            *const libc::c_char,
            libc::c_int,
        ) -> libc::c_int,
    >,
    pub _ub: __sbuf,
    pub _extra: *mut __sFILEX,
    pub _ur: libc::c_int,
    pub _ubuf: [libc::c_uchar; 3],
    pub _nbuf: [libc::c_uchar; 1],
    pub _lb: __sbuf,
    pub _blksize: libc::c_int,
    pub _offset: fpos_t,
}
pub type FILE = __sFILE;
pub type Spec_Hash_Definitions_hash_alg = uint8_t;
pub type Hacl_Streaming_Types_error_code = uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_SHA3_hash_buf_s {
    pub fst: Spec_Hash_Definitions_hash_alg,
    pub snd: *mut uint64_t,
}
pub type Hacl_Hash_SHA3_hash_buf = Hacl_Hash_SHA3_hash_buf_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_SHA3_state_t_s {
    pub block_state: Hacl_Hash_SHA3_hash_buf,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
}
pub type Hacl_Hash_SHA3_state_t = Hacl_Hash_SHA3_state_t_s;
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
#[no_mangle]
pub static mut Hacl_Hash_SHA3_keccak_rotc: [uint32_t; 24] = [
    1 as libc::c_uint,
    3 as libc::c_uint,
    6 as libc::c_uint,
    10 as libc::c_uint,
    15 as libc::c_uint,
    21 as libc::c_uint,
    28 as libc::c_uint,
    36 as libc::c_uint,
    45 as libc::c_uint,
    55 as libc::c_uint,
    2 as libc::c_uint,
    14 as libc::c_uint,
    27 as libc::c_uint,
    41 as libc::c_uint,
    56 as libc::c_uint,
    8 as libc::c_uint,
    25 as libc::c_uint,
    43 as libc::c_uint,
    62 as libc::c_uint,
    18 as libc::c_uint,
    39 as libc::c_uint,
    61 as libc::c_uint,
    20 as libc::c_uint,
    44 as libc::c_uint,
];
#[no_mangle]
pub static mut Hacl_Hash_SHA3_keccak_piln: [uint32_t; 24] = [
    10 as libc::c_uint,
    7 as libc::c_uint,
    11 as libc::c_uint,
    17 as libc::c_uint,
    18 as libc::c_uint,
    3 as libc::c_uint,
    5 as libc::c_uint,
    16 as libc::c_uint,
    8 as libc::c_uint,
    21 as libc::c_uint,
    24 as libc::c_uint,
    4 as libc::c_uint,
    15 as libc::c_uint,
    23 as libc::c_uint,
    19 as libc::c_uint,
    13 as libc::c_uint,
    12 as libc::c_uint,
    2 as libc::c_uint,
    20 as libc::c_uint,
    14 as libc::c_uint,
    22 as libc::c_uint,
    9 as libc::c_uint,
    6 as libc::c_uint,
    1 as libc::c_uint,
];
#[no_mangle]
pub static mut Hacl_Hash_SHA3_keccak_rndc: [uint64_t; 24] = [
    0x1 as libc::c_ulonglong,
    0x8082 as libc::c_ulonglong,
    0x800000000000808a as libc::c_ulonglong,
    0x8000000080008000 as libc::c_ulonglong,
    0x808b as libc::c_ulonglong,
    0x80000001 as libc::c_ulonglong,
    0x8000000080008081 as libc::c_ulonglong,
    0x8000000000008009 as libc::c_ulonglong,
    0x8a as libc::c_ulonglong,
    0x88 as libc::c_ulonglong,
    0x80008009 as libc::c_ulonglong,
    0x8000000a as libc::c_ulonglong,
    0x8000808b as libc::c_ulonglong,
    0x800000000000008b as libc::c_ulonglong,
    0x8000000000008089 as libc::c_ulonglong,
    0x8000000000008003 as libc::c_ulonglong,
    0x8000000000008002 as libc::c_ulonglong,
    0x8000000000000080 as libc::c_ulonglong,
    0x800a as libc::c_ulonglong,
    0x800000008000000a as libc::c_ulonglong,
    0x8000000080008081 as libc::c_ulonglong,
    0x8000000000008080 as libc::c_ulonglong,
    0x80000001 as libc::c_ulonglong,
    0x8000000080008008 as libc::c_ulonglong,
];
unsafe extern "C" fn absorb_inner_32(mut b: *mut uint8_t, mut s: *mut uint64_t) {
    let mut ws: [uint64_t; 32] = [
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
    ];
    let mut b1: *mut uint8_t = b;
    let mut u: uint64_t = load64(b1);
    ws[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b1.offset(8 as libc::c_uint as isize));
    ws[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b1.offset(16 as libc::c_uint as isize));
    ws[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b1.offset(24 as libc::c_uint as isize));
    ws[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b1.offset(32 as libc::c_uint as isize));
    ws[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b1.offset(40 as libc::c_uint as isize));
    ws[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b1.offset(48 as libc::c_uint as isize));
    ws[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b1.offset(56 as libc::c_uint as isize));
    ws[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b1.offset(64 as libc::c_uint as isize));
    ws[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b1.offset(72 as libc::c_uint as isize));
    ws[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b1.offset(80 as libc::c_uint as isize));
    ws[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b1.offset(88 as libc::c_uint as isize));
    ws[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b1.offset(96 as libc::c_uint as isize));
    ws[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b1.offset(104 as libc::c_uint as isize));
    ws[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b1.offset(112 as libc::c_uint as isize));
    ws[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b1.offset(120 as libc::c_uint as isize));
    ws[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b1.offset(128 as libc::c_uint as isize));
    ws[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b1.offset(136 as libc::c_uint as isize));
    ws[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b1.offset(144 as libc::c_uint as isize));
    ws[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b1.offset(152 as libc::c_uint as isize));
    ws[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b1.offset(160 as libc::c_uint as isize));
    ws[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b1.offset(168 as libc::c_uint as isize));
    ws[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b1.offset(176 as libc::c_uint as isize));
    ws[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b1.offset(184 as libc::c_uint as isize));
    ws[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b1.offset(192 as libc::c_uint as isize));
    ws[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b1.offset(200 as libc::c_uint as isize));
    ws[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b1.offset(208 as libc::c_uint as isize));
    ws[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b1.offset(216 as libc::c_uint as isize));
    ws[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b1.offset(224 as libc::c_uint as isize));
    ws[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b1.offset(232 as libc::c_uint as isize));
    ws[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b1.offset(240 as libc::c_uint as isize));
    ws[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b1.offset(248 as libc::c_uint as isize));
    ws[31 as libc::c_uint as usize] = u30;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 25 as libc::c_uint {
        *s.offset(i as isize) = *s.offset(i as isize) ^ ws[i as usize];
        i = i.wrapping_add(1);
        i;
    }
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < 24 as libc::c_uint {
        let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        let mut i_0: uint32_t = 0 as libc::c_uint;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i1: uint32_t = 0 as libc::c_uint;
        let mut uu____0: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
        let mut i_1: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_0: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_0: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
        let mut i_2: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_1: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_1: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
        let mut i_3: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_2: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_2: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
        let mut i_4: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_3: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_3: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
        let mut i_5: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x: uint64_t = *s.offset(1 as libc::c_uint as isize);
        let mut current: uint64_t = x;
        let mut i_6: uint32_t = 0 as libc::c_uint;
        while i_6 < 24 as libc::c_uint {
            let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_6 as usize];
            let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_6 as usize];
            let mut temp: uint64_t = *s.offset(_Y as isize);
            let mut uu____1: uint64_t = current;
            *s
                .offset(
                    _Y as isize,
                ) = uu____1 << r | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
            current = temp;
            i_6 = i_6.wrapping_add(1);
            i_6;
        }
        let mut i_7: uint32_t = 0 as libc::c_uint;
        let mut v0: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_0: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_0: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_0: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_0: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_0: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_0;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_0;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_0;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_0;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_0;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_1: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_1: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_1: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_1: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_1: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_1;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_1;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_1;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_1;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_1;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_2: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_2: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_2: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_2: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_2: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_2;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_2;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_2;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_2;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_2;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_3: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_3: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_3: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_3: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_3: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_3;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_3;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_3;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_3;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_3;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i0 as usize];
        *s
            .offset(
                0 as libc::c_uint as isize,
            ) = *s.offset(0 as libc::c_uint as isize) ^ c;
        i0 = i0.wrapping_add(1);
        i0;
    }
}
unsafe extern "C" fn block_len(mut a: Spec_Hash_Definitions_hash_alg) -> uint32_t {
    match a as libc::c_int {
        9 => return 144 as libc::c_uint,
        8 => return 136 as libc::c_uint,
        10 => return 104 as libc::c_uint,
        11 => return 72 as libc::c_uint,
        12 => return 168 as libc::c_uint,
        13 => return 136 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_Hash_SHA3.c\0" as *const u8 as *const libc::c_char,
                203 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
unsafe extern "C" fn hash_len(mut a: Spec_Hash_Definitions_hash_alg) -> uint32_t {
    match a as libc::c_int {
        9 => return 28 as libc::c_uint,
        8 => return 32 as libc::c_uint,
        10 => return 48 as libc::c_uint,
        11 => return 64 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_Hash_SHA3.c\0" as *const u8 as *const libc::c_char,
                231 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_update_multi_sha3(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut s: *mut uint64_t,
    mut blocks: *mut uint8_t,
    mut n_blocks: uint32_t,
) {
    let mut l: uint32_t = block_len(a) * n_blocks;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < l / block_len(a) {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = blocks;
        let mut bl0: *mut uint8_t = b_;
        let mut uu____0: *mut uint8_t = b0.offset((i * block_len(a)) as isize);
        memcpy(
            bl0 as *mut libc::c_void,
            uu____0 as *const libc::c_void,
            (block_len(a) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut unused: uint32_t = block_len(a);
        absorb_inner_32(b_, s);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_update_last_sha3(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut s: *mut uint64_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut suffix: uint8_t = 0;
    if a as libc::c_int == 12 as libc::c_int || a as libc::c_int == 13 as libc::c_int {
        suffix = 0x1f as libc::c_uint as uint8_t;
    } else {
        suffix = 0x6 as libc::c_uint as uint8_t;
    }
    let mut len: uint32_t = block_len(a);
    if input_len == len {
        let mut b1: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b1.as_mut_ptr();
        let mut b00: *mut uint8_t = input;
        let mut bl00: *mut uint8_t = b_;
        memcpy(
            bl00 as *mut libc::c_void,
            b00.offset((0 as libc::c_uint).wrapping_mul(len) as isize)
                as *const libc::c_void,
            (len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        absorb_inner_32(b_, s);
        let mut b2: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_0: *mut uint8_t = b2.as_mut_ptr();
        let mut rem: uint32_t = (0 as libc::c_uint).wrapping_rem(len);
        let mut b01: *mut uint8_t = input.offset(input_len as isize);
        let mut bl0: *mut uint8_t = b_0;
        memcpy(
            bl0 as *mut libc::c_void,
            b01.offset(0 as libc::c_uint as isize).offset(-(rem as isize))
                as *const libc::c_void,
            (rem as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut b02: *mut uint8_t = b_0;
        *b02.offset((0 as libc::c_uint).wrapping_rem(len) as isize) = suffix;
        let mut ws: [uint64_t; 32] = [
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
        ];
        let mut b: *mut uint8_t = b_0;
        let mut u: uint64_t = load64(b);
        ws[0 as libc::c_uint as usize] = u;
        let mut u0: uint64_t = load64(b.offset(8 as libc::c_uint as isize));
        ws[1 as libc::c_uint as usize] = u0;
        let mut u1: uint64_t = load64(b.offset(16 as libc::c_uint as isize));
        ws[2 as libc::c_uint as usize] = u1;
        let mut u2: uint64_t = load64(b.offset(24 as libc::c_uint as isize));
        ws[3 as libc::c_uint as usize] = u2;
        let mut u3: uint64_t = load64(b.offset(32 as libc::c_uint as isize));
        ws[4 as libc::c_uint as usize] = u3;
        let mut u4: uint64_t = load64(b.offset(40 as libc::c_uint as isize));
        ws[5 as libc::c_uint as usize] = u4;
        let mut u5: uint64_t = load64(b.offset(48 as libc::c_uint as isize));
        ws[6 as libc::c_uint as usize] = u5;
        let mut u6: uint64_t = load64(b.offset(56 as libc::c_uint as isize));
        ws[7 as libc::c_uint as usize] = u6;
        let mut u7: uint64_t = load64(b.offset(64 as libc::c_uint as isize));
        ws[8 as libc::c_uint as usize] = u7;
        let mut u8: uint64_t = load64(b.offset(72 as libc::c_uint as isize));
        ws[9 as libc::c_uint as usize] = u8;
        let mut u9: uint64_t = load64(b.offset(80 as libc::c_uint as isize));
        ws[10 as libc::c_uint as usize] = u9;
        let mut u10: uint64_t = load64(b.offset(88 as libc::c_uint as isize));
        ws[11 as libc::c_uint as usize] = u10;
        let mut u11: uint64_t = load64(b.offset(96 as libc::c_uint as isize));
        ws[12 as libc::c_uint as usize] = u11;
        let mut u12: uint64_t = load64(b.offset(104 as libc::c_uint as isize));
        ws[13 as libc::c_uint as usize] = u12;
        let mut u13: uint64_t = load64(b.offset(112 as libc::c_uint as isize));
        ws[14 as libc::c_uint as usize] = u13;
        let mut u14: uint64_t = load64(b.offset(120 as libc::c_uint as isize));
        ws[15 as libc::c_uint as usize] = u14;
        let mut u15: uint64_t = load64(b.offset(128 as libc::c_uint as isize));
        ws[16 as libc::c_uint as usize] = u15;
        let mut u16: uint64_t = load64(b.offset(136 as libc::c_uint as isize));
        ws[17 as libc::c_uint as usize] = u16;
        let mut u17: uint64_t = load64(b.offset(144 as libc::c_uint as isize));
        ws[18 as libc::c_uint as usize] = u17;
        let mut u18: uint64_t = load64(b.offset(152 as libc::c_uint as isize));
        ws[19 as libc::c_uint as usize] = u18;
        let mut u19: uint64_t = load64(b.offset(160 as libc::c_uint as isize));
        ws[20 as libc::c_uint as usize] = u19;
        let mut u20: uint64_t = load64(b.offset(168 as libc::c_uint as isize));
        ws[21 as libc::c_uint as usize] = u20;
        let mut u21: uint64_t = load64(b.offset(176 as libc::c_uint as isize));
        ws[22 as libc::c_uint as usize] = u21;
        let mut u22: uint64_t = load64(b.offset(184 as libc::c_uint as isize));
        ws[23 as libc::c_uint as usize] = u22;
        let mut u23: uint64_t = load64(b.offset(192 as libc::c_uint as isize));
        ws[24 as libc::c_uint as usize] = u23;
        let mut u24: uint64_t = load64(b.offset(200 as libc::c_uint as isize));
        ws[25 as libc::c_uint as usize] = u24;
        let mut u25: uint64_t = load64(b.offset(208 as libc::c_uint as isize));
        ws[26 as libc::c_uint as usize] = u25;
        let mut u26: uint64_t = load64(b.offset(216 as libc::c_uint as isize));
        ws[27 as libc::c_uint as usize] = u26;
        let mut u27: uint64_t = load64(b.offset(224 as libc::c_uint as isize));
        ws[28 as libc::c_uint as usize] = u27;
        let mut u28: uint64_t = load64(b.offset(232 as libc::c_uint as isize));
        ws[29 as libc::c_uint as usize] = u28;
        let mut u29: uint64_t = load64(b.offset(240 as libc::c_uint as isize));
        ws[30 as libc::c_uint as usize] = u29;
        let mut u30: uint64_t = load64(b.offset(248 as libc::c_uint as isize));
        ws[31 as libc::c_uint as usize] = u30;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < 25 as libc::c_uint {
            *s.offset(i as isize) = *s.offset(i as isize) ^ ws[i as usize];
            i = i.wrapping_add(1);
            i;
        }
        if !(suffix as uint32_t & 0x80 as libc::c_uint == 0 as libc::c_uint)
            && (0 as libc::c_uint).wrapping_rem(len)
                == len.wrapping_sub(1 as libc::c_uint)
        {
            let mut i0: uint32_t = 0 as libc::c_uint;
            while i0 < 24 as libc::c_uint {
                let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
                let mut i_0: uint32_t = 0 as libc::c_uint;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut i1: uint32_t = 0 as libc::c_uint;
                let mut uu____0: uint64_t = _C[i1
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D: uint64_t = _C[i1
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
                let mut i_1: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____0_0: uint64_t = _C[i1
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_0: uint64_t = _C[i1
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
                let mut i_2: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____0_1: uint64_t = _C[i1
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_1: uint64_t = _C[i1
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
                let mut i_3: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____0_2: uint64_t = _C[i1
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_2: uint64_t = _C[i1
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
                let mut i_4: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____0_3: uint64_t = _C[i1
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_3: uint64_t = _C[i1
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
                let mut i_5: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut x: uint64_t = *s.offset(1 as libc::c_uint as isize);
                let mut current: uint64_t = x;
                let mut i_6: uint32_t = 0 as libc::c_uint;
                while i_6 < 24 as libc::c_uint {
                    let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_6 as usize];
                    let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_6 as usize];
                    let mut temp: uint64_t = *s.offset(_Y as isize);
                    let mut uu____1: uint64_t = current;
                    *s
                        .offset(
                            _Y as isize,
                        ) = uu____1 << r
                        | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                    current = temp;
                    i_6 = i_6.wrapping_add(1);
                    i_6;
                }
                let mut i_7: uint32_t = 0 as libc::c_uint;
                let mut v0: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_0: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_0: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_0: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_0: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_0: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_0;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_0;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_0;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_0;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_0;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_1: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_1: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_1: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_1: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_1: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_1;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_1;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_1;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_1;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_1;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_2: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_2: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_2: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_2: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_2: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_2;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_2;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_2;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_2;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_2;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_3: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_3: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_3: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_3: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_3: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_3;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_3;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_3;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_3;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_3;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i0 as usize];
                *s
                    .offset(
                        0 as libc::c_uint as isize,
                    ) = *s.offset(0 as libc::c_uint as isize) ^ c;
                i0 = i0.wrapping_add(1);
                i0;
            }
        }
        let mut b3: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b4: *mut uint8_t = b3.as_mut_ptr();
        let mut b0: *mut uint8_t = b4;
        *b0
            .offset(
                len.wrapping_sub(1 as libc::c_uint) as isize,
            ) = 0x80 as libc::c_uint as uint8_t;
        absorb_inner_32(b4, s);
        return;
    }
    let mut b1_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1_0.as_mut_ptr();
    let mut rem_0: uint32_t = input_len % len;
    let mut b00_0: *mut uint8_t = input;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00_0.offset(input_len as isize).offset(-(rem_0 as isize))
            as *const libc::c_void,
        (rem_0 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01_0: *mut uint8_t = b__0;
    *b01_0.offset((input_len % len) as isize) = suffix;
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    let mut b_1: *mut uint8_t = b__0;
    let mut u_0: uint64_t = load64(b_1);
    ws_0[0 as libc::c_uint as usize] = u_0;
    let mut u0_0: uint64_t = load64(b_1.offset(8 as libc::c_uint as isize));
    ws_0[1 as libc::c_uint as usize] = u0_0;
    let mut u1_0: uint64_t = load64(b_1.offset(16 as libc::c_uint as isize));
    ws_0[2 as libc::c_uint as usize] = u1_0;
    let mut u2_0: uint64_t = load64(b_1.offset(24 as libc::c_uint as isize));
    ws_0[3 as libc::c_uint as usize] = u2_0;
    let mut u3_0: uint64_t = load64(b_1.offset(32 as libc::c_uint as isize));
    ws_0[4 as libc::c_uint as usize] = u3_0;
    let mut u4_0: uint64_t = load64(b_1.offset(40 as libc::c_uint as isize));
    ws_0[5 as libc::c_uint as usize] = u4_0;
    let mut u5_0: uint64_t = load64(b_1.offset(48 as libc::c_uint as isize));
    ws_0[6 as libc::c_uint as usize] = u5_0;
    let mut u6_0: uint64_t = load64(b_1.offset(56 as libc::c_uint as isize));
    ws_0[7 as libc::c_uint as usize] = u6_0;
    let mut u7_0: uint64_t = load64(b_1.offset(64 as libc::c_uint as isize));
    ws_0[8 as libc::c_uint as usize] = u7_0;
    let mut u8_0: uint64_t = load64(b_1.offset(72 as libc::c_uint as isize));
    ws_0[9 as libc::c_uint as usize] = u8_0;
    let mut u9_0: uint64_t = load64(b_1.offset(80 as libc::c_uint as isize));
    ws_0[10 as libc::c_uint as usize] = u9_0;
    let mut u10_0: uint64_t = load64(b_1.offset(88 as libc::c_uint as isize));
    ws_0[11 as libc::c_uint as usize] = u10_0;
    let mut u11_0: uint64_t = load64(b_1.offset(96 as libc::c_uint as isize));
    ws_0[12 as libc::c_uint as usize] = u11_0;
    let mut u12_0: uint64_t = load64(b_1.offset(104 as libc::c_uint as isize));
    ws_0[13 as libc::c_uint as usize] = u12_0;
    let mut u13_0: uint64_t = load64(b_1.offset(112 as libc::c_uint as isize));
    ws_0[14 as libc::c_uint as usize] = u13_0;
    let mut u14_0: uint64_t = load64(b_1.offset(120 as libc::c_uint as isize));
    ws_0[15 as libc::c_uint as usize] = u14_0;
    let mut u15_0: uint64_t = load64(b_1.offset(128 as libc::c_uint as isize));
    ws_0[16 as libc::c_uint as usize] = u15_0;
    let mut u16_0: uint64_t = load64(b_1.offset(136 as libc::c_uint as isize));
    ws_0[17 as libc::c_uint as usize] = u16_0;
    let mut u17_0: uint64_t = load64(b_1.offset(144 as libc::c_uint as isize));
    ws_0[18 as libc::c_uint as usize] = u17_0;
    let mut u18_0: uint64_t = load64(b_1.offset(152 as libc::c_uint as isize));
    ws_0[19 as libc::c_uint as usize] = u18_0;
    let mut u19_0: uint64_t = load64(b_1.offset(160 as libc::c_uint as isize));
    ws_0[20 as libc::c_uint as usize] = u19_0;
    let mut u20_0: uint64_t = load64(b_1.offset(168 as libc::c_uint as isize));
    ws_0[21 as libc::c_uint as usize] = u20_0;
    let mut u21_0: uint64_t = load64(b_1.offset(176 as libc::c_uint as isize));
    ws_0[22 as libc::c_uint as usize] = u21_0;
    let mut u22_0: uint64_t = load64(b_1.offset(184 as libc::c_uint as isize));
    ws_0[23 as libc::c_uint as usize] = u22_0;
    let mut u23_0: uint64_t = load64(b_1.offset(192 as libc::c_uint as isize));
    ws_0[24 as libc::c_uint as usize] = u23_0;
    let mut u24_0: uint64_t = load64(b_1.offset(200 as libc::c_uint as isize));
    ws_0[25 as libc::c_uint as usize] = u24_0;
    let mut u25_0: uint64_t = load64(b_1.offset(208 as libc::c_uint as isize));
    ws_0[26 as libc::c_uint as usize] = u25_0;
    let mut u26_0: uint64_t = load64(b_1.offset(216 as libc::c_uint as isize));
    ws_0[27 as libc::c_uint as usize] = u26_0;
    let mut u27_0: uint64_t = load64(b_1.offset(224 as libc::c_uint as isize));
    ws_0[28 as libc::c_uint as usize] = u27_0;
    let mut u28_0: uint64_t = load64(b_1.offset(232 as libc::c_uint as isize));
    ws_0[29 as libc::c_uint as usize] = u28_0;
    let mut u29_0: uint64_t = load64(b_1.offset(240 as libc::c_uint as isize));
    ws_0[30 as libc::c_uint as usize] = u29_0;
    let mut u30_0: uint64_t = load64(b_1.offset(248 as libc::c_uint as isize));
    ws_0[31 as libc::c_uint as usize] = u30_0;
    let mut i_8: uint32_t = 0 as libc::c_uint;
    while i_8 < 25 as libc::c_uint {
        *s.offset(i_8 as isize) = *s.offset(i_8 as isize) ^ ws_0[i_8 as usize];
        i_8 = i_8.wrapping_add(1);
        i_8;
    }
    if !(suffix as uint32_t & 0x80 as libc::c_uint == 0 as libc::c_uint)
        && input_len % len == len.wrapping_sub(1 as libc::c_uint)
    {
        let mut i0_0: uint32_t = 0 as libc::c_uint;
        while i0_0 < 24 as libc::c_uint {
            let mut _C_0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_9: uint32_t = 0 as libc::c_uint;
            _C_0[i_9
                as usize] = *s.offset(i_9.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_9.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_9.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_9.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_9.wrapping_add(20 as libc::c_uint) as isize))));
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_9
                as usize] = *s.offset(i_9.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_9.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_9.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_9.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_9.wrapping_add(20 as libc::c_uint) as isize))));
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_9
                as usize] = *s.offset(i_9.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_9.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_9.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_9.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_9.wrapping_add(20 as libc::c_uint) as isize))));
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_9
                as usize] = *s.offset(i_9.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_9.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_9.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_9.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_9.wrapping_add(20 as libc::c_uint) as isize))));
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_9
                as usize] = *s.offset(i_9.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_9.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_9.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_9.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_9.wrapping_add(20 as libc::c_uint) as isize))));
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i1_0: uint32_t = 0 as libc::c_uint;
            let mut uu____2: uint64_t = _C_0[i1_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_4: uint64_t = _C_0[i1_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____2 << 1 as libc::c_uint | uu____2 >> 63 as libc::c_uint);
            let mut i_10: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) ^ _D_4;
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) ^ _D_4;
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) ^ _D_4;
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) ^ _D_4;
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_10)) as isize,
                ) ^ _D_4;
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____2_0: uint64_t = _C_0[i1_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_5: uint64_t = _C_0[i1_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____2_0 << 1 as libc::c_uint | uu____2_0 >> 63 as libc::c_uint);
            let mut i_11: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_5;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_5;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_5;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_5;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_5;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____2_1: uint64_t = _C_0[i1_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_6: uint64_t = _C_0[i1_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____2_1 << 1 as libc::c_uint | uu____2_1 >> 63 as libc::c_uint);
            let mut i_12: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_6;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_6;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_6;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_6;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_6;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____2_2: uint64_t = _C_0[i1_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_7: uint64_t = _C_0[i1_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____2_2 << 1 as libc::c_uint | uu____2_2 >> 63 as libc::c_uint);
            let mut i_13: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_7;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_7;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_7;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_7;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_7;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____2_3: uint64_t = _C_0[i1_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_8: uint64_t = _C_0[i1_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____2_3 << 1 as libc::c_uint | uu____2_3 >> 63 as libc::c_uint);
            let mut i_14: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_8;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_8;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_8;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_8;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i1_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_8;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x_0: uint64_t = *s.offset(1 as libc::c_uint as isize);
            let mut current_0: uint64_t = x_0;
            let mut i_15: uint32_t = 0 as libc::c_uint;
            while i_15 < 24 as libc::c_uint {
                let mut _Y_0: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_15 as usize];
                let mut r_0: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_15 as usize];
                let mut temp_0: uint64_t = *s.offset(_Y_0 as isize);
                let mut uu____3: uint64_t = current_0;
                *s
                    .offset(
                        _Y_0 as isize,
                    ) = uu____3 << r_0
                    | uu____3 >> (64 as libc::c_uint).wrapping_sub(r_0);
                current_0 = temp_0;
                i_15 = i_15.wrapping_add(1);
                i_15;
            }
            let mut i_16: uint32_t = 0 as libc::c_uint;
            let mut v0_4: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v1_4: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v2_4: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v3_4: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v4_4: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v0_4;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v1_4;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v2_4;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v3_4;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v4_4;
            i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_5: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v1_5: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v2_5: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v3_5: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v4_5: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v0_5;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v1_5;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v2_5;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v3_5;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v4_5;
            i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_6: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v1_6: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v2_6: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v3_6: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v4_6: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v0_6;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v1_6;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v2_6;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v3_6;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v4_6;
            i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_7: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v1_7: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v2_7: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v3_7: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v4_7: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v0_7;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v1_7;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v2_7;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v3_7;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v4_7;
            i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_8: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v1_8: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v2_8: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v3_8: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            let mut v4_8: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v0_8;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v1_8;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v2_8;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v3_8;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_16)) as isize,
                ) = v4_8;
            i_16 = (i_16 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_0: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i0_0 as usize];
            *s
                .offset(
                    0 as libc::c_uint as isize,
                ) = *s.offset(0 as libc::c_uint as isize) ^ c_0;
            i0_0 = i0_0.wrapping_add(1);
            i0_0;
        }
    }
    let mut b2_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3_0: *mut uint8_t = b2_0.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3_0;
    *b0_0
        .offset(
            len.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    absorb_inner_32(b3_0, s);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_get_alg(
    mut s: *mut Hacl_Hash_SHA3_state_t,
) -> Spec_Hash_Definitions_hash_alg {
    let mut block_state: Hacl_Hash_SHA3_hash_buf = (*s).block_state;
    return block_state.fst;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_malloc(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> *mut Hacl_Hash_SHA3_state_t {
    if block_len(a) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Hash_SHA3.c\0" as *const u8 as *const libc::c_char,
            556 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut buf0: *mut uint8_t = calloc(
        block_len(a) as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut buf: *mut uint64_t = calloc(
        25 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    let mut block_state: Hacl_Hash_SHA3_hash_buf = {
        let mut init = Hacl_Hash_SHA3_hash_buf_s {
            fst: a,
            snd: buf,
        };
        init
    };
    let mut s: *mut uint64_t = block_state.snd;
    memset(
        s as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut s0: Hacl_Hash_SHA3_state_t = {
        let mut init = Hacl_Hash_SHA3_state_t_s {
            block_state: block_state,
            buf: buf0,
            total_len: 0 as libc::c_uint as uint64_t,
        };
        init
    };
    let mut p: *mut Hacl_Hash_SHA3_state_t = malloc(
        ::core::mem::size_of::<Hacl_Hash_SHA3_state_t>() as libc::c_ulong,
    ) as *mut Hacl_Hash_SHA3_state_t;
    *p.offset(0 as libc::c_uint as isize) = s0;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_free(mut state: *mut Hacl_Hash_SHA3_state_t) {
    let mut scrut: Hacl_Hash_SHA3_state_t = *state;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: Hacl_Hash_SHA3_hash_buf = scrut.block_state;
    let mut s: *mut uint64_t = block_state.snd;
    free(s as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_copy(
    mut state: *mut Hacl_Hash_SHA3_state_t,
) -> *mut Hacl_Hash_SHA3_state_t {
    let mut block_state0: Hacl_Hash_SHA3_hash_buf = (*state).block_state;
    let mut buf0: *mut uint8_t = (*state).buf;
    let mut total_len0: uint64_t = (*state).total_len;
    let mut i: Spec_Hash_Definitions_hash_alg = block_state0.fst;
    if block_len(i) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_Hash_SHA3.c\0" as *const u8 as *const libc::c_char,
            587 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut buf1: *mut uint8_t = calloc(
        block_len(i) as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    memcpy(
        buf1 as *mut libc::c_void,
        buf0 as *const libc::c_void,
        (block_len(i) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut buf: *mut uint64_t = calloc(
        25 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    let mut block_state: Hacl_Hash_SHA3_hash_buf = {
        let mut init = Hacl_Hash_SHA3_hash_buf_s {
            fst: i,
            snd: buf,
        };
        init
    };
    let mut s_src: *mut uint64_t = block_state0.snd;
    let mut s_dst: *mut uint64_t = block_state.snd;
    memcpy(
        s_dst as *mut libc::c_void,
        s_src as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut s: Hacl_Hash_SHA3_state_t = {
        let mut init = Hacl_Hash_SHA3_state_t_s {
            block_state: block_state,
            buf: buf1,
            total_len: total_len0,
        };
        init
    };
    let mut p: *mut Hacl_Hash_SHA3_state_t = malloc(
        ::core::mem::size_of::<Hacl_Hash_SHA3_state_t>() as libc::c_ulong,
    ) as *mut Hacl_Hash_SHA3_state_t;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_reset(mut state: *mut Hacl_Hash_SHA3_state_t) {
    let mut block_state: Hacl_Hash_SHA3_hash_buf = (*state).block_state;
    let mut s: *mut uint64_t = block_state.snd;
    memset(
        s as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_update(
    mut state: *mut Hacl_Hash_SHA3_state_t,
    mut chunk: *mut uint8_t,
    mut chunk_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut block_state: Hacl_Hash_SHA3_hash_buf = (*state).block_state;
    let mut total_len: uint64_t = (*state).total_len;
    let mut i: Spec_Hash_Definitions_hash_alg = block_state.fst;
    if chunk_len as uint64_t
        > (0xffffffffffffffff as libc::c_ulonglong).wrapping_sub(total_len)
    {
        return 3 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    let mut sz: uint32_t = 0;
    if total_len % block_len(i) as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        sz = block_len(i);
    } else {
        sz = (total_len % block_len(i) as uint64_t) as uint32_t;
    }
    if chunk_len <= (block_len(i)).wrapping_sub(sz) {
        let mut buf: *mut uint8_t = (*state).buf;
        let mut total_len1: uint64_t = (*state).total_len;
        let mut sz1: uint32_t = 0;
        if total_len1 % block_len(i) as uint64_t == 0 as libc::c_ulonglong
            && total_len1 > 0 as libc::c_ulonglong
        {
            sz1 = block_len(i);
        } else {
            sz1 = (total_len1 % block_len(i) as uint64_t) as uint32_t;
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
        if total_len1_0 % block_len(i) as uint64_t == 0 as libc::c_ulonglong
            && total_len1_0 > 0 as libc::c_ulonglong
        {
            sz1_0 = block_len(i);
        } else {
            sz1_0 = (total_len1_0 % block_len(i) as uint64_t) as uint32_t;
        }
        if !(sz1_0 == 0 as libc::c_uint) {
            let mut a1: Spec_Hash_Definitions_hash_alg = block_state.fst;
            let mut s1: *mut uint64_t = block_state.snd;
            Hacl_Hash_SHA3_update_multi_sha3(
                a1,
                s1,
                buf_0,
                block_len(i) / block_len(a1),
            );
        }
        let mut ite: uint32_t = 0;
        if chunk_len as uint64_t % block_len(i) as uint64_t == 0 as libc::c_ulonglong
            && chunk_len as uint64_t > 0 as libc::c_ulonglong
        {
            ite = block_len(i);
        } else {
            ite = (chunk_len as uint64_t % block_len(i) as uint64_t) as uint32_t;
        }
        let mut n_blocks: uint32_t = chunk_len.wrapping_sub(ite) / block_len(i);
        let mut data1_len: uint32_t = n_blocks * block_len(i);
        let mut data2_len: uint32_t = chunk_len.wrapping_sub(data1_len);
        let mut data1: *mut uint8_t = chunk;
        let mut data2: *mut uint8_t = chunk.offset(data1_len as isize);
        let mut a1_0: Spec_Hash_Definitions_hash_alg = block_state.fst;
        let mut s1_0: *mut uint64_t = block_state.snd;
        Hacl_Hash_SHA3_update_multi_sha3(a1_0, s1_0, data1, data1_len / block_len(a1_0));
        let mut dst: *mut uint8_t = buf_0;
        memcpy(
            dst as *mut libc::c_void,
            data2 as *const libc::c_void,
            (data2_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        (*state).total_len = total_len1_0.wrapping_add(chunk_len as uint64_t);
    } else {
        let mut diff: uint32_t = (block_len(i)).wrapping_sub(sz);
        let mut chunk1: *mut uint8_t = chunk;
        let mut chunk2: *mut uint8_t = chunk.offset(diff as isize);
        let mut buf_1: *mut uint8_t = (*state).buf;
        let mut total_len10: uint64_t = (*state).total_len;
        let mut sz10: uint32_t = 0;
        if total_len10 % block_len(i) as uint64_t == 0 as libc::c_ulonglong
            && total_len10 > 0 as libc::c_ulonglong
        {
            sz10 = block_len(i);
        } else {
            sz10 = (total_len10 % block_len(i) as uint64_t) as uint32_t;
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
        if total_len1_1 % block_len(i) as uint64_t == 0 as libc::c_ulonglong
            && total_len1_1 > 0 as libc::c_ulonglong
        {
            sz1_1 = block_len(i);
        } else {
            sz1_1 = (total_len1_1 % block_len(i) as uint64_t) as uint32_t;
        }
        if !(sz1_1 == 0 as libc::c_uint) {
            let mut a1_1: Spec_Hash_Definitions_hash_alg = block_state.fst;
            let mut s1_1: *mut uint64_t = block_state.snd;
            Hacl_Hash_SHA3_update_multi_sha3(
                a1_1,
                s1_1,
                buf0,
                block_len(i) / block_len(a1_1),
            );
        }
        let mut ite_0: uint32_t = 0;
        if chunk_len.wrapping_sub(diff) as uint64_t % block_len(i) as uint64_t
            == 0 as libc::c_ulonglong
            && chunk_len.wrapping_sub(diff) as uint64_t > 0 as libc::c_ulonglong
        {
            ite_0 = block_len(i);
        } else {
            ite_0 = (chunk_len.wrapping_sub(diff) as uint64_t % block_len(i) as uint64_t)
                as uint32_t;
        }
        let mut n_blocks_0: uint32_t = chunk_len.wrapping_sub(diff).wrapping_sub(ite_0)
            / block_len(i);
        let mut data1_len_0: uint32_t = n_blocks_0 * block_len(i);
        let mut data2_len_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(data1_len_0);
        let mut data1_0: *mut uint8_t = chunk2;
        let mut data2_0: *mut uint8_t = chunk2.offset(data1_len_0 as isize);
        let mut a1_2: Spec_Hash_Definitions_hash_alg = block_state.fst;
        let mut s1_2: *mut uint64_t = block_state.snd;
        Hacl_Hash_SHA3_update_multi_sha3(
            a1_2,
            s1_2,
            data1_0,
            data1_len_0 / block_len(a1_2),
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
unsafe extern "C" fn digest_(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut state: *mut Hacl_Hash_SHA3_state_t,
    mut output: *mut uint8_t,
    mut l: uint32_t,
) {
    let mut block_state: Hacl_Hash_SHA3_hash_buf = (*state).block_state;
    let mut buf_: *mut uint8_t = (*state).buf;
    let mut total_len: uint64_t = (*state).total_len;
    let mut r: uint32_t = 0;
    if total_len % block_len(a) as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        r = block_len(a);
    } else {
        r = (total_len % block_len(a) as uint64_t) as uint32_t;
    }
    let mut buf_1: *mut uint8_t = buf_;
    let mut buf: [uint64_t; 25] = [
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
    let mut tmp_block_state: Hacl_Hash_SHA3_hash_buf = {
        let mut init = Hacl_Hash_SHA3_hash_buf_s {
            fst: a,
            snd: buf.as_mut_ptr(),
        };
        init
    };
    let mut s_src: *mut uint64_t = block_state.snd;
    let mut s_dst: *mut uint64_t = tmp_block_state.snd;
    memcpy(
        s_dst as *mut libc::c_void,
        s_src as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut buf_multi: *mut uint8_t = buf_1;
    let mut ite: uint32_t = 0;
    if r % block_len(a) == 0 as libc::c_uint && r > 0 as libc::c_uint {
        ite = block_len(a);
    } else {
        ite = r % block_len(a);
    }
    let mut buf_last: *mut uint8_t = buf_1.offset(r as isize).offset(-(ite as isize));
    let mut a1: Spec_Hash_Definitions_hash_alg = tmp_block_state.fst;
    let mut s0: *mut uint64_t = tmp_block_state.snd;
    Hacl_Hash_SHA3_update_multi_sha3(
        a1,
        s0,
        buf_multi,
        (0 as libc::c_uint).wrapping_div(block_len(a1)),
    );
    let mut a10: Spec_Hash_Definitions_hash_alg = tmp_block_state.fst;
    let mut s1: *mut uint64_t = tmp_block_state.snd;
    Hacl_Hash_SHA3_update_last_sha3(a10, s1, buf_last, r);
    let mut a11: Spec_Hash_Definitions_hash_alg = tmp_block_state.fst;
    let mut s: *mut uint64_t = tmp_block_state.snd;
    if a11 as libc::c_int == 12 as libc::c_int || a11 as libc::c_int == 13 as libc::c_int
    {
        let mut i0: uint32_t = 0 as libc::c_uint;
        while i0 < l / block_len(a11) {
            let mut hbuf: [uint8_t; 256] = [
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
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
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
            let mut ws: [uint64_t; 32] = [
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
            ];
            memcpy(
                ws.as_mut_ptr() as *mut libc::c_void,
                s as *const libc::c_void,
                (25 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
            );
            let mut i: uint32_t = 0 as libc::c_uint;
            while i < 32 as libc::c_uint {
                store64(
                    hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
                    ws[i as usize],
                );
                i = i.wrapping_add(1);
                i;
            }
            let mut b0: *mut uint8_t = output;
            let mut uu____0: *mut uint8_t = hbuf.as_mut_ptr();
            memcpy(
                b0.offset((i0 * block_len(a11)) as isize) as *mut libc::c_void,
                uu____0 as *const libc::c_void,
                (block_len(a11) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut i1: uint32_t = 0 as libc::c_uint;
            while i1 < 24 as libc::c_uint {
                let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
                let mut i_0: uint32_t = 0 as libc::c_uint;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                _C[i_0
                    as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                        ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                            ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                                ^ *s
                                    .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
                i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut i2: uint32_t = 0 as libc::c_uint;
                let mut uu____1: uint64_t = _C[i2
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D: uint64_t = _C[i2
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____1 << 1 as libc::c_uint | uu____1 >> 63 as libc::c_uint);
                let mut i_1: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                    ) ^ _D;
                i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____1_0: uint64_t = _C[i2
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_0: uint64_t = _C[i2
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____1_0 << 1 as libc::c_uint | uu____1_0 >> 63 as libc::c_uint);
                let mut i_2: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                    ) ^ _D_0;
                i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____1_1: uint64_t = _C[i2
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_1: uint64_t = _C[i2
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____1_1 << 1 as libc::c_uint | uu____1_1 >> 63 as libc::c_uint);
                let mut i_3: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                    ) ^ _D_1;
                i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____1_2: uint64_t = _C[i2
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_2: uint64_t = _C[i2
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____1_2 << 1 as libc::c_uint | uu____1_2 >> 63 as libc::c_uint);
                let mut i_4: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                    ) ^ _D_2;
                i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut uu____1_3: uint64_t = _C[i2
                    .wrapping_add(1 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize];
                let mut _D_3: uint64_t = _C[i2
                    .wrapping_add(4 as libc::c_uint)
                    .wrapping_rem(5 as libc::c_uint) as usize]
                    ^ (uu____1_3 << 1 as libc::c_uint | uu____1_3 >> 63 as libc::c_uint);
                let mut i_5: uint32_t = 0 as libc::c_uint;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) = *s
                    .offset(
                        i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                    ) ^ _D_3;
                i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut x: uint64_t = *s.offset(1 as libc::c_uint as isize);
                let mut current: uint64_t = x;
                let mut i_6: uint32_t = 0 as libc::c_uint;
                while i_6 < 24 as libc::c_uint {
                    let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_6 as usize];
                    let mut r1: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_6 as usize];
                    let mut temp: uint64_t = *s.offset(_Y as isize);
                    let mut uu____2: uint64_t = current;
                    *s
                        .offset(
                            _Y as isize,
                        ) = uu____2 << r1
                        | uu____2 >> (64 as libc::c_uint).wrapping_sub(r1);
                    current = temp;
                    i_6 = i_6.wrapping_add(1);
                    i_6;
                }
                let mut i_7: uint32_t = 0 as libc::c_uint;
                let mut v0: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_0: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_0: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_0: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_0: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_0: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_0;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_0;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_0;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_0;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_0;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_1: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_1: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_1: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_1: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_1: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_1;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_1;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_1;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_1;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_1;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_2: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_2: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_2: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_2: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_2: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_2;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_2;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_2;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_2;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_2;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut v0_3: uint64_t = *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (2 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v1_3: uint64_t = *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (3 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v2_3: uint64_t = *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (4 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v3_3: uint64_t = *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (0 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                let mut v4_3: uint64_t = *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    ^ !*s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        )
                        & *s
                            .offset(
                                (1 as libc::c_uint)
                                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                    as isize,
                            );
                *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v0_3;
                *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v1_3;
                *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v2_3;
                *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v3_3;
                *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    ) = v4_3;
                i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                    as uint32_t;
                let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
                *s
                    .offset(
                        0 as libc::c_uint as isize,
                    ) = *s.offset(0 as libc::c_uint as isize) ^ c;
                i1 = i1.wrapping_add(1);
                i1;
            }
            i0 = i0.wrapping_add(1);
            i0;
        }
        let mut remOut: uint32_t = l % block_len(a11);
        let mut hbuf_0: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws_0: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws_0.as_mut_ptr() as *mut libc::c_void,
            s as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_8: uint32_t = 0 as libc::c_uint;
        while i_8 < 32 as libc::c_uint {
            store64(
                hbuf_0.as_mut_ptr().offset(i_8.wrapping_mul(8 as libc::c_uint) as isize),
                ws_0[i_8 as usize],
            );
            i_8 = i_8.wrapping_add(1);
            i_8;
        }
        memcpy(
            output.offset(l as isize).offset(-(remOut as isize)) as *mut libc::c_void,
            hbuf_0.as_mut_ptr() as *const libc::c_void,
            (remOut as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        return;
    }
    let mut i0_0: uint32_t = 0 as libc::c_uint;
    while i0_0 < hash_len(a11) / block_len(a11) {
        let mut hbuf_1: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws_1: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws_1.as_mut_ptr() as *mut libc::c_void,
            s as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_9: uint32_t = 0 as libc::c_uint;
        while i_9 < 32 as libc::c_uint {
            store64(
                hbuf_1.as_mut_ptr().offset(i_9.wrapping_mul(8 as libc::c_uint) as isize),
                ws_1[i_9 as usize],
            );
            i_9 = i_9.wrapping_add(1);
            i_9;
        }
        let mut b0_0: *mut uint8_t = output;
        let mut uu____3: *mut uint8_t = hbuf_1.as_mut_ptr();
        memcpy(
            b0_0.offset((i0_0 * block_len(a11)) as isize) as *mut libc::c_void,
            uu____3 as *const libc::c_void,
            (block_len(a11) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1_0: uint32_t = 0 as libc::c_uint;
        while i1_0 < 24 as libc::c_uint {
            let mut _C_0: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_10: uint32_t = 0 as libc::c_uint;
            _C_0[i_10
                as usize] = *s.offset(i_10.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_10.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_10.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_10.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_10.wrapping_add(20 as libc::c_uint) as isize))));
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_10
                as usize] = *s.offset(i_10.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_10.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_10.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_10.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_10.wrapping_add(20 as libc::c_uint) as isize))));
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_10
                as usize] = *s.offset(i_10.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_10.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_10.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_10.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_10.wrapping_add(20 as libc::c_uint) as isize))));
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_10
                as usize] = *s.offset(i_10.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_10.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_10.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_10.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_10.wrapping_add(20 as libc::c_uint) as isize))));
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C_0[i_10
                as usize] = *s.offset(i_10.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*s.offset(i_10.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*s.offset(i_10.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*s.offset(i_10.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *s
                                .offset(i_10.wrapping_add(20 as libc::c_uint) as isize))));
            i_10 = (i_10 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2_0: uint32_t = 0 as libc::c_uint;
            let mut uu____4: uint64_t = _C_0[i2_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_4: uint64_t = _C_0[i2_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____4 << 1 as libc::c_uint | uu____4 >> 63 as libc::c_uint);
            let mut i_11: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_4;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_4;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_4;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_4;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_11)) as isize,
                ) ^ _D_4;
            i_11 = (i_11 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2_0 = (i2_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____4_0: uint64_t = _C_0[i2_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_5: uint64_t = _C_0[i2_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____4_0 << 1 as libc::c_uint | uu____4_0 >> 63 as libc::c_uint);
            let mut i_12: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_5;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_5;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_5;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_5;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_12)) as isize,
                ) ^ _D_5;
            i_12 = (i_12 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2_0 = (i2_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____4_1: uint64_t = _C_0[i2_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_6: uint64_t = _C_0[i2_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____4_1 << 1 as libc::c_uint | uu____4_1 >> 63 as libc::c_uint);
            let mut i_13: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_6;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_6;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_6;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_6;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_13)) as isize,
                ) ^ _D_6;
            i_13 = (i_13 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2_0 = (i2_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____4_2: uint64_t = _C_0[i2_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_7: uint64_t = _C_0[i2_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____4_2 << 1 as libc::c_uint | uu____4_2 >> 63 as libc::c_uint);
            let mut i_14: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_7;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_7;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_7;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_7;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_14)) as isize,
                ) ^ _D_7;
            i_14 = (i_14 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2_0 = (i2_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____4_3: uint64_t = _C_0[i2_0
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_8: uint64_t = _C_0[i2_0
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____4_3 << 1 as libc::c_uint | uu____4_3 >> 63 as libc::c_uint);
            let mut i_15: uint32_t = 0 as libc::c_uint;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) ^ _D_8;
            i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) ^ _D_8;
            i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) ^ _D_8;
            i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) ^ _D_8;
            i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) = *s
                .offset(
                    i2_0.wrapping_add((5 as libc::c_uint).wrapping_mul(i_15)) as isize,
                ) ^ _D_8;
            i_15 = (i_15 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2_0 = (i2_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x_0: uint64_t = *s.offset(1 as libc::c_uint as isize);
            let mut current_0: uint64_t = x_0;
            let mut i_16: uint32_t = 0 as libc::c_uint;
            while i_16 < 24 as libc::c_uint {
                let mut _Y_0: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_16 as usize];
                let mut r1_0: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_16 as usize];
                let mut temp_0: uint64_t = *s.offset(_Y_0 as isize);
                let mut uu____5: uint64_t = current_0;
                *s
                    .offset(
                        _Y_0 as isize,
                    ) = uu____5 << r1_0
                    | uu____5 >> (64 as libc::c_uint).wrapping_sub(r1_0);
                current_0 = temp_0;
                i_16 = i_16.wrapping_add(1);
                i_16;
            }
            let mut i_17: uint32_t = 0 as libc::c_uint;
            let mut v0_4: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v1_4: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v2_4: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v3_4: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v4_4: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v0_4;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v1_4;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v2_4;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v3_4;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v4_4;
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_5: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v1_5: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v2_5: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v3_5: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v4_5: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v0_5;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v1_5;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v2_5;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v3_5;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v4_5;
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_6: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v1_6: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v2_6: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v3_6: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v4_6: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v0_6;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v1_6;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v2_6;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v3_6;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v4_6;
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_7: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v1_7: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v2_7: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v3_7: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v4_7: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v0_7;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v1_7;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v2_7;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v3_7;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v4_7;
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_8: uint64_t = *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v1_8: uint64_t = *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v2_8: uint64_t = *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v3_8: uint64_t = *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            let mut v4_8: uint64_t = *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                )
                ^ !*s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                            as isize,
                    )
                    & *s
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17))
                                as isize,
                        );
            *s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v0_8;
            *s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v1_8;
            *s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v2_8;
            *s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v3_8;
            *s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_17)) as isize,
                ) = v4_8;
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_0: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1_0 as usize];
            *s
                .offset(
                    0 as libc::c_uint as isize,
                ) = *s.offset(0 as libc::c_uint as isize) ^ c_0;
            i1_0 = i1_0.wrapping_add(1);
            i1_0;
        }
        i0_0 = i0_0.wrapping_add(1);
        i0_0;
    }
    let mut remOut_0: uint32_t = hash_len(a11) % block_len(a11);
    let mut hbuf_2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_2: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_2.as_mut_ptr() as *mut libc::c_void,
        s as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_18: uint32_t = 0 as libc::c_uint;
    while i_18 < 32 as libc::c_uint {
        store64(
            hbuf_2.as_mut_ptr().offset(i_18.wrapping_mul(8 as libc::c_uint) as isize),
            ws_2[i_18 as usize],
        );
        i_18 = i_18.wrapping_add(1);
        i_18;
    }
    let mut uu____6: *mut uint8_t = hbuf_2.as_mut_ptr();
    memcpy(
        output.offset(hash_len(a11) as isize).offset(-(remOut_0 as isize))
            as *mut libc::c_void,
        uu____6 as *const libc::c_void,
        (remOut_0 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_digest(
    mut state: *mut Hacl_Hash_SHA3_state_t,
    mut output: *mut uint8_t,
) -> Hacl_Streaming_Types_error_code {
    let mut a1: Spec_Hash_Definitions_hash_alg = Hacl_Hash_SHA3_get_alg(state);
    if a1 as libc::c_int == 12 as libc::c_int || a1 as libc::c_int == 13 as libc::c_int {
        return 1 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    digest_(a1, state, output, hash_len(a1));
    return 0 as libc::c_int as Hacl_Streaming_Types_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_squeeze(
    mut s: *mut Hacl_Hash_SHA3_state_t,
    mut dst: *mut uint8_t,
    mut l: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut a1: Spec_Hash_Definitions_hash_alg = Hacl_Hash_SHA3_get_alg(s);
    if !(a1 as libc::c_int == 12 as libc::c_int
        || a1 as libc::c_int == 13 as libc::c_int)
    {
        return 1 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    if l == 0 as libc::c_uint {
        return 2 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    digest_(a1, s, dst, l);
    return 0 as libc::c_int as Hacl_Streaming_Types_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_block_len(
    mut s: *mut Hacl_Hash_SHA3_state_t,
) -> uint32_t {
    let mut a1: Spec_Hash_Definitions_hash_alg = Hacl_Hash_SHA3_get_alg(s);
    return block_len(a1);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_hash_len(
    mut s: *mut Hacl_Hash_SHA3_state_t,
) -> uint32_t {
    let mut a1: Spec_Hash_Definitions_hash_alg = Hacl_Hash_SHA3_get_alg(s);
    return hash_len(a1);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_is_shake(
    mut s: *mut Hacl_Hash_SHA3_state_t,
) -> bool {
    let mut uu____0: Spec_Hash_Definitions_hash_alg = Hacl_Hash_SHA3_get_alg(s);
    return uu____0 as libc::c_int == 12 as libc::c_int
        || uu____0 as libc::c_int == 13 as libc::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_absorb_inner_32(
    mut rateInBytes: uint32_t,
    mut b: *mut uint8_t,
    mut s: *mut uint64_t,
) {
    let mut ws: [uint64_t; 32] = [
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
    ];
    let mut b1: *mut uint8_t = b;
    let mut u: uint64_t = load64(b1);
    ws[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b1.offset(8 as libc::c_uint as isize));
    ws[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b1.offset(16 as libc::c_uint as isize));
    ws[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b1.offset(24 as libc::c_uint as isize));
    ws[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b1.offset(32 as libc::c_uint as isize));
    ws[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b1.offset(40 as libc::c_uint as isize));
    ws[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b1.offset(48 as libc::c_uint as isize));
    ws[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b1.offset(56 as libc::c_uint as isize));
    ws[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b1.offset(64 as libc::c_uint as isize));
    ws[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b1.offset(72 as libc::c_uint as isize));
    ws[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b1.offset(80 as libc::c_uint as isize));
    ws[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b1.offset(88 as libc::c_uint as isize));
    ws[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b1.offset(96 as libc::c_uint as isize));
    ws[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b1.offset(104 as libc::c_uint as isize));
    ws[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b1.offset(112 as libc::c_uint as isize));
    ws[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b1.offset(120 as libc::c_uint as isize));
    ws[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b1.offset(128 as libc::c_uint as isize));
    ws[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b1.offset(136 as libc::c_uint as isize));
    ws[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b1.offset(144 as libc::c_uint as isize));
    ws[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b1.offset(152 as libc::c_uint as isize));
    ws[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b1.offset(160 as libc::c_uint as isize));
    ws[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b1.offset(168 as libc::c_uint as isize));
    ws[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b1.offset(176 as libc::c_uint as isize));
    ws[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b1.offset(184 as libc::c_uint as isize));
    ws[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b1.offset(192 as libc::c_uint as isize));
    ws[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b1.offset(200 as libc::c_uint as isize));
    ws[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b1.offset(208 as libc::c_uint as isize));
    ws[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b1.offset(216 as libc::c_uint as isize));
    ws[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b1.offset(224 as libc::c_uint as isize));
    ws[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b1.offset(232 as libc::c_uint as isize));
    ws[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b1.offset(240 as libc::c_uint as isize));
    ws[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b1.offset(248 as libc::c_uint as isize));
    ws[31 as libc::c_uint as usize] = u30;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 25 as libc::c_uint {
        *s.offset(i as isize) = *s.offset(i as isize) ^ ws[i as usize];
        i = i.wrapping_add(1);
        i;
    }
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < 24 as libc::c_uint {
        let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
        let mut i_0: uint32_t = 0 as libc::c_uint;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        _C[i_0
            as usize] = *s.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
            ^ (*s.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                ^ (*s.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                    ^ (*s.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                        ^ *s.offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut i1: uint32_t = 0 as libc::c_uint;
        let mut uu____0: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
        let mut i_1: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
            ^ _D;
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_0: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_0: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
        let mut i_2: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
            ^ _D_0;
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_1: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_1: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
        let mut i_3: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
            ^ _D_1;
        i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_2: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_2: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
        let mut i_4: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
            ^ _D_2;
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut uu____0_3: uint64_t = _C[i1
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize];
        let mut _D_3: uint64_t = _C[i1
            .wrapping_add(4 as libc::c_uint)
            .wrapping_rem(5 as libc::c_uint) as usize]
            ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
        let mut i_5: uint32_t = 0 as libc::c_uint;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        *s
            .offset(
                i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
            ) = *s
            .offset(i1.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
            ^ _D_3;
        i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        i1 = (i1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut x: uint64_t = *s.offset(1 as libc::c_uint as isize);
        let mut current: uint64_t = x;
        let mut i_6: uint32_t = 0 as libc::c_uint;
        while i_6 < 24 as libc::c_uint {
            let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_6 as usize];
            let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_6 as usize];
            let mut temp: uint64_t = *s.offset(_Y as isize);
            let mut uu____1: uint64_t = current;
            *s
                .offset(
                    _Y as isize,
                ) = uu____1 << r | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
            current = temp;
            i_6 = i_6.wrapping_add(1);
            i_6;
        }
        let mut i_7: uint32_t = 0 as libc::c_uint;
        let mut v0: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_0: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_0: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_0: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_0: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_0: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_0;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_0;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_0;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_0;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_0;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_1: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_1: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_1: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_1: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_1: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_1;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_1;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_1;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_1;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_1;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_2: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_2: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_2: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_2: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_2: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_2;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_2;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_2;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_2;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_2;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut v0_3: uint64_t = *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v1_3: uint64_t = *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v2_3: uint64_t = *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v3_3: uint64_t = *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        let mut v4_3: uint64_t = *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            )
            ^ !*s
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                & *s
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    );
        *s
            .offset(
                (0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v0_3;
        *s
            .offset(
                (1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v1_3;
        *s
            .offset(
                (2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v2_3;
        *s
            .offset(
                (3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v3_3;
        *s
            .offset(
                (4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                    as isize,
            ) = v4_3;
        i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i0 as usize];
        *s
            .offset(
                0 as libc::c_uint as isize,
            ) = *s.offset(0 as libc::c_uint as isize) ^ c;
        i0 = i0.wrapping_add(1);
        i0;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_shake128(
    mut output: *mut uint8_t,
    mut outputByteLen: uint32_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut s: [uint64_t; 25] = [
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
    let mut rateInBytes1: uint32_t = 168 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen / rateInBytes1 {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = ib;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset((i * rateInBytes1) as isize) as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b_, s.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen % rateInBytes1;
    let mut b00: *mut uint8_t = ib;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b__0;
    *b01
        .offset(
            (inputByteLen % rateInBytes1) as isize,
        ) = 0x1f as libc::c_uint as uint8_t;
    let mut ws0: [uint64_t; 32] = [
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
    ];
    let mut b_0: *mut uint8_t = b__0;
    let mut u: uint64_t = load64(b_0);
    ws0[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b_0.offset(8 as libc::c_uint as isize));
    ws0[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b_0.offset(16 as libc::c_uint as isize));
    ws0[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b_0.offset(24 as libc::c_uint as isize));
    ws0[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b_0.offset(32 as libc::c_uint as isize));
    ws0[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b_0.offset(40 as libc::c_uint as isize));
    ws0[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b_0.offset(48 as libc::c_uint as isize));
    ws0[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b_0.offset(56 as libc::c_uint as isize));
    ws0[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b_0.offset(64 as libc::c_uint as isize));
    ws0[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b_0.offset(72 as libc::c_uint as isize));
    ws0[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b_0.offset(80 as libc::c_uint as isize));
    ws0[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b_0.offset(88 as libc::c_uint as isize));
    ws0[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b_0.offset(96 as libc::c_uint as isize));
    ws0[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b_0.offset(104 as libc::c_uint as isize));
    ws0[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b_0.offset(112 as libc::c_uint as isize));
    ws0[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b_0.offset(120 as libc::c_uint as isize));
    ws0[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b_0.offset(128 as libc::c_uint as isize));
    ws0[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b_0.offset(136 as libc::c_uint as isize));
    ws0[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b_0.offset(144 as libc::c_uint as isize));
    ws0[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b_0.offset(152 as libc::c_uint as isize));
    ws0[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b_0.offset(160 as libc::c_uint as isize));
    ws0[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b_0.offset(168 as libc::c_uint as isize));
    ws0[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b_0.offset(176 as libc::c_uint as isize));
    ws0[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b_0.offset(184 as libc::c_uint as isize));
    ws0[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b_0.offset(192 as libc::c_uint as isize));
    ws0[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b_0.offset(200 as libc::c_uint as isize));
    ws0[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b_0.offset(208 as libc::c_uint as isize));
    ws0[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b_0.offset(216 as libc::c_uint as isize));
    ws0[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b_0.offset(224 as libc::c_uint as isize));
    ws0[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b_0.offset(232 as libc::c_uint as isize));
    ws0[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b_0.offset(240 as libc::c_uint as isize));
    ws0[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b_0.offset(248 as libc::c_uint as isize));
    ws0[31 as libc::c_uint as usize] = u30;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        s[i_0 as usize] = s[i_0 as usize] ^ ws0[i_0 as usize];
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3;
    *b0_0
        .offset(
            rateInBytes1.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b3, s.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < outputByteLen / rateInBytes1 {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            s.as_mut_ptr() as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i_1.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i_1 as usize],
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut b02: *mut uint8_t = rb;
        memcpy(
            b02.offset((i0 * rateInBytes1) as isize) as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_2: uint32_t = 0 as libc::c_uint;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_6: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_7: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = s[1 as libc::c_uint as usize];
            let mut current: uint64_t = x;
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_8 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_8 as usize];
                let mut temp: uint64_t = s[_Y as usize];
                let mut uu____1: uint64_t = current;
                s[_Y
                    as usize] = uu____1 << r
                    | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            let mut i_9: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_0: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_0: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_0: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_0: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_0;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_0;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_0;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_0;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_1: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_1: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_1: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_1;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_1;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_1;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_1;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_2: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_2: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_2: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_2;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_2;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_2;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_2;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_3: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_3: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_3: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_3;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_3;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_3;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_3;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            s[0 as libc::c_uint as usize] = s[0 as libc::c_uint as usize] ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
    let mut remOut: uint32_t = outputByteLen % rateInBytes1;
    let mut hbuf_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_0.as_mut_ptr() as *mut libc::c_void,
        s.as_mut_ptr() as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    while i_10 < 32 as libc::c_uint {
        store64(
            hbuf_0.as_mut_ptr().offset(i_10.wrapping_mul(8 as libc::c_uint) as isize),
            ws_0[i_10 as usize],
        );
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    memcpy(
        rb.offset(outputByteLen as isize).offset(-(remOut as isize))
            as *mut libc::c_void,
        hbuf_0.as_mut_ptr() as *const libc::c_void,
        (remOut as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_shake256(
    mut output: *mut uint8_t,
    mut outputByteLen: uint32_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut s: [uint64_t; 25] = [
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
    let mut rateInBytes1: uint32_t = 136 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen / rateInBytes1 {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = ib;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset((i * rateInBytes1) as isize) as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b_, s.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen % rateInBytes1;
    let mut b00: *mut uint8_t = ib;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b__0;
    *b01
        .offset(
            (inputByteLen % rateInBytes1) as isize,
        ) = 0x1f as libc::c_uint as uint8_t;
    let mut ws0: [uint64_t; 32] = [
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
    ];
    let mut b_0: *mut uint8_t = b__0;
    let mut u: uint64_t = load64(b_0);
    ws0[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b_0.offset(8 as libc::c_uint as isize));
    ws0[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b_0.offset(16 as libc::c_uint as isize));
    ws0[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b_0.offset(24 as libc::c_uint as isize));
    ws0[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b_0.offset(32 as libc::c_uint as isize));
    ws0[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b_0.offset(40 as libc::c_uint as isize));
    ws0[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b_0.offset(48 as libc::c_uint as isize));
    ws0[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b_0.offset(56 as libc::c_uint as isize));
    ws0[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b_0.offset(64 as libc::c_uint as isize));
    ws0[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b_0.offset(72 as libc::c_uint as isize));
    ws0[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b_0.offset(80 as libc::c_uint as isize));
    ws0[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b_0.offset(88 as libc::c_uint as isize));
    ws0[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b_0.offset(96 as libc::c_uint as isize));
    ws0[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b_0.offset(104 as libc::c_uint as isize));
    ws0[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b_0.offset(112 as libc::c_uint as isize));
    ws0[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b_0.offset(120 as libc::c_uint as isize));
    ws0[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b_0.offset(128 as libc::c_uint as isize));
    ws0[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b_0.offset(136 as libc::c_uint as isize));
    ws0[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b_0.offset(144 as libc::c_uint as isize));
    ws0[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b_0.offset(152 as libc::c_uint as isize));
    ws0[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b_0.offset(160 as libc::c_uint as isize));
    ws0[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b_0.offset(168 as libc::c_uint as isize));
    ws0[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b_0.offset(176 as libc::c_uint as isize));
    ws0[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b_0.offset(184 as libc::c_uint as isize));
    ws0[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b_0.offset(192 as libc::c_uint as isize));
    ws0[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b_0.offset(200 as libc::c_uint as isize));
    ws0[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b_0.offset(208 as libc::c_uint as isize));
    ws0[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b_0.offset(216 as libc::c_uint as isize));
    ws0[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b_0.offset(224 as libc::c_uint as isize));
    ws0[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b_0.offset(232 as libc::c_uint as isize));
    ws0[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b_0.offset(240 as libc::c_uint as isize));
    ws0[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b_0.offset(248 as libc::c_uint as isize));
    ws0[31 as libc::c_uint as usize] = u30;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        s[i_0 as usize] = s[i_0 as usize] ^ ws0[i_0 as usize];
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3;
    *b0_0
        .offset(
            rateInBytes1.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b3, s.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < outputByteLen / rateInBytes1 {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            s.as_mut_ptr() as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i_1.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i_1 as usize],
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut b02: *mut uint8_t = rb;
        memcpy(
            b02.offset((i0 * rateInBytes1) as isize) as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_2: uint32_t = 0 as libc::c_uint;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_6: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_7: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = s[1 as libc::c_uint as usize];
            let mut current: uint64_t = x;
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_8 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_8 as usize];
                let mut temp: uint64_t = s[_Y as usize];
                let mut uu____1: uint64_t = current;
                s[_Y
                    as usize] = uu____1 << r
                    | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            let mut i_9: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_0: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_0: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_0: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_0: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_0;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_0;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_0;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_0;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_1: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_1: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_1: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_1;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_1;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_1;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_1;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_2: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_2: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_2: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_2;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_2;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_2;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_2;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_3: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_3: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_3: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_3;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_3;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_3;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_3;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            s[0 as libc::c_uint as usize] = s[0 as libc::c_uint as usize] ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
    let mut remOut: uint32_t = outputByteLen % rateInBytes1;
    let mut hbuf_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_0.as_mut_ptr() as *mut libc::c_void,
        s.as_mut_ptr() as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    while i_10 < 32 as libc::c_uint {
        store64(
            hbuf_0.as_mut_ptr().offset(i_10.wrapping_mul(8 as libc::c_uint) as isize),
            ws_0[i_10 as usize],
        );
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    memcpy(
        rb.offset(outputByteLen as isize).offset(-(remOut as isize))
            as *mut libc::c_void,
        hbuf_0.as_mut_ptr() as *const libc::c_void,
        (remOut as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_sha3_224(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut s: [uint64_t; 25] = [
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
    let mut rateInBytes1: uint32_t = 144 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen / rateInBytes1 {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = ib;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset((i * rateInBytes1) as isize) as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b_, s.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen % rateInBytes1;
    let mut b00: *mut uint8_t = ib;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b__0;
    *b01.offset((inputByteLen % rateInBytes1) as isize) = 0x6 as libc::c_uint as uint8_t;
    let mut ws0: [uint64_t; 32] = [
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
    ];
    let mut b_0: *mut uint8_t = b__0;
    let mut u: uint64_t = load64(b_0);
    ws0[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b_0.offset(8 as libc::c_uint as isize));
    ws0[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b_0.offset(16 as libc::c_uint as isize));
    ws0[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b_0.offset(24 as libc::c_uint as isize));
    ws0[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b_0.offset(32 as libc::c_uint as isize));
    ws0[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b_0.offset(40 as libc::c_uint as isize));
    ws0[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b_0.offset(48 as libc::c_uint as isize));
    ws0[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b_0.offset(56 as libc::c_uint as isize));
    ws0[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b_0.offset(64 as libc::c_uint as isize));
    ws0[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b_0.offset(72 as libc::c_uint as isize));
    ws0[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b_0.offset(80 as libc::c_uint as isize));
    ws0[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b_0.offset(88 as libc::c_uint as isize));
    ws0[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b_0.offset(96 as libc::c_uint as isize));
    ws0[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b_0.offset(104 as libc::c_uint as isize));
    ws0[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b_0.offset(112 as libc::c_uint as isize));
    ws0[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b_0.offset(120 as libc::c_uint as isize));
    ws0[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b_0.offset(128 as libc::c_uint as isize));
    ws0[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b_0.offset(136 as libc::c_uint as isize));
    ws0[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b_0.offset(144 as libc::c_uint as isize));
    ws0[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b_0.offset(152 as libc::c_uint as isize));
    ws0[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b_0.offset(160 as libc::c_uint as isize));
    ws0[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b_0.offset(168 as libc::c_uint as isize));
    ws0[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b_0.offset(176 as libc::c_uint as isize));
    ws0[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b_0.offset(184 as libc::c_uint as isize));
    ws0[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b_0.offset(192 as libc::c_uint as isize));
    ws0[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b_0.offset(200 as libc::c_uint as isize));
    ws0[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b_0.offset(208 as libc::c_uint as isize));
    ws0[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b_0.offset(216 as libc::c_uint as isize));
    ws0[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b_0.offset(224 as libc::c_uint as isize));
    ws0[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b_0.offset(232 as libc::c_uint as isize));
    ws0[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b_0.offset(240 as libc::c_uint as isize));
    ws0[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b_0.offset(248 as libc::c_uint as isize));
    ws0[31 as libc::c_uint as usize] = u30;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        s[i_0 as usize] = s[i_0 as usize] ^ ws0[i_0 as usize];
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3;
    *b0_0
        .offset(
            rateInBytes1.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b3, s.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (28 as libc::c_uint).wrapping_div(rateInBytes1) {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            s.as_mut_ptr() as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i_1.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i_1 as usize],
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut b02: *mut uint8_t = rb;
        memcpy(
            b02.offset((i0 * rateInBytes1) as isize) as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_2: uint32_t = 0 as libc::c_uint;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_6: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_7: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = s[1 as libc::c_uint as usize];
            let mut current: uint64_t = x;
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_8 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_8 as usize];
                let mut temp: uint64_t = s[_Y as usize];
                let mut uu____1: uint64_t = current;
                s[_Y
                    as usize] = uu____1 << r
                    | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            let mut i_9: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_0: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_0: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_0: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_0: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_0;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_0;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_0;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_0;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_1: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_1: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_1: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_1;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_1;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_1;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_1;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_2: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_2: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_2: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_2;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_2;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_2;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_2;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_3: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_3: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_3: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_3;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_3;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_3;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_3;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            s[0 as libc::c_uint as usize] = s[0 as libc::c_uint as usize] ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
    let mut remOut: uint32_t = (28 as libc::c_uint).wrapping_rem(rateInBytes1);
    let mut hbuf_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_0.as_mut_ptr() as *mut libc::c_void,
        s.as_mut_ptr() as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    while i_10 < 32 as libc::c_uint {
        store64(
            hbuf_0.as_mut_ptr().offset(i_10.wrapping_mul(8 as libc::c_uint) as isize),
            ws_0[i_10 as usize],
        );
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    memcpy(
        rb.offset(28 as libc::c_uint as isize).offset(-(remOut as isize))
            as *mut libc::c_void,
        hbuf_0.as_mut_ptr() as *const libc::c_void,
        (remOut as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_sha3_256(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut s: [uint64_t; 25] = [
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
    let mut rateInBytes1: uint32_t = 136 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen / rateInBytes1 {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = ib;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset((i * rateInBytes1) as isize) as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b_, s.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen % rateInBytes1;
    let mut b00: *mut uint8_t = ib;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b__0;
    *b01.offset((inputByteLen % rateInBytes1) as isize) = 0x6 as libc::c_uint as uint8_t;
    let mut ws0: [uint64_t; 32] = [
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
    ];
    let mut b_0: *mut uint8_t = b__0;
    let mut u: uint64_t = load64(b_0);
    ws0[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b_0.offset(8 as libc::c_uint as isize));
    ws0[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b_0.offset(16 as libc::c_uint as isize));
    ws0[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b_0.offset(24 as libc::c_uint as isize));
    ws0[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b_0.offset(32 as libc::c_uint as isize));
    ws0[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b_0.offset(40 as libc::c_uint as isize));
    ws0[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b_0.offset(48 as libc::c_uint as isize));
    ws0[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b_0.offset(56 as libc::c_uint as isize));
    ws0[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b_0.offset(64 as libc::c_uint as isize));
    ws0[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b_0.offset(72 as libc::c_uint as isize));
    ws0[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b_0.offset(80 as libc::c_uint as isize));
    ws0[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b_0.offset(88 as libc::c_uint as isize));
    ws0[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b_0.offset(96 as libc::c_uint as isize));
    ws0[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b_0.offset(104 as libc::c_uint as isize));
    ws0[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b_0.offset(112 as libc::c_uint as isize));
    ws0[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b_0.offset(120 as libc::c_uint as isize));
    ws0[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b_0.offset(128 as libc::c_uint as isize));
    ws0[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b_0.offset(136 as libc::c_uint as isize));
    ws0[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b_0.offset(144 as libc::c_uint as isize));
    ws0[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b_0.offset(152 as libc::c_uint as isize));
    ws0[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b_0.offset(160 as libc::c_uint as isize));
    ws0[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b_0.offset(168 as libc::c_uint as isize));
    ws0[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b_0.offset(176 as libc::c_uint as isize));
    ws0[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b_0.offset(184 as libc::c_uint as isize));
    ws0[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b_0.offset(192 as libc::c_uint as isize));
    ws0[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b_0.offset(200 as libc::c_uint as isize));
    ws0[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b_0.offset(208 as libc::c_uint as isize));
    ws0[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b_0.offset(216 as libc::c_uint as isize));
    ws0[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b_0.offset(224 as libc::c_uint as isize));
    ws0[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b_0.offset(232 as libc::c_uint as isize));
    ws0[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b_0.offset(240 as libc::c_uint as isize));
    ws0[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b_0.offset(248 as libc::c_uint as isize));
    ws0[31 as libc::c_uint as usize] = u30;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        s[i_0 as usize] = s[i_0 as usize] ^ ws0[i_0 as usize];
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3;
    *b0_0
        .offset(
            rateInBytes1.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b3, s.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (32 as libc::c_uint).wrapping_div(rateInBytes1) {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            s.as_mut_ptr() as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i_1.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i_1 as usize],
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut b02: *mut uint8_t = rb;
        memcpy(
            b02.offset((i0 * rateInBytes1) as isize) as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_2: uint32_t = 0 as libc::c_uint;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_6: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_7: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = s[1 as libc::c_uint as usize];
            let mut current: uint64_t = x;
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_8 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_8 as usize];
                let mut temp: uint64_t = s[_Y as usize];
                let mut uu____1: uint64_t = current;
                s[_Y
                    as usize] = uu____1 << r
                    | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            let mut i_9: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_0: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_0: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_0: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_0: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_0;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_0;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_0;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_0;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_1: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_1: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_1: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_1;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_1;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_1;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_1;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_2: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_2: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_2: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_2;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_2;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_2;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_2;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_3: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_3: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_3: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_3;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_3;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_3;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_3;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            s[0 as libc::c_uint as usize] = s[0 as libc::c_uint as usize] ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
    let mut remOut: uint32_t = (32 as libc::c_uint).wrapping_rem(rateInBytes1);
    let mut hbuf_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_0.as_mut_ptr() as *mut libc::c_void,
        s.as_mut_ptr() as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    while i_10 < 32 as libc::c_uint {
        store64(
            hbuf_0.as_mut_ptr().offset(i_10.wrapping_mul(8 as libc::c_uint) as isize),
            ws_0[i_10 as usize],
        );
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    memcpy(
        rb.offset(32 as libc::c_uint as isize).offset(-(remOut as isize))
            as *mut libc::c_void,
        hbuf_0.as_mut_ptr() as *const libc::c_void,
        (remOut as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_sha3_384(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut s: [uint64_t; 25] = [
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
    let mut rateInBytes1: uint32_t = 104 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen / rateInBytes1 {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = ib;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset((i * rateInBytes1) as isize) as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b_, s.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen % rateInBytes1;
    let mut b00: *mut uint8_t = ib;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b__0;
    *b01.offset((inputByteLen % rateInBytes1) as isize) = 0x6 as libc::c_uint as uint8_t;
    let mut ws0: [uint64_t; 32] = [
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
    ];
    let mut b_0: *mut uint8_t = b__0;
    let mut u: uint64_t = load64(b_0);
    ws0[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b_0.offset(8 as libc::c_uint as isize));
    ws0[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b_0.offset(16 as libc::c_uint as isize));
    ws0[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b_0.offset(24 as libc::c_uint as isize));
    ws0[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b_0.offset(32 as libc::c_uint as isize));
    ws0[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b_0.offset(40 as libc::c_uint as isize));
    ws0[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b_0.offset(48 as libc::c_uint as isize));
    ws0[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b_0.offset(56 as libc::c_uint as isize));
    ws0[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b_0.offset(64 as libc::c_uint as isize));
    ws0[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b_0.offset(72 as libc::c_uint as isize));
    ws0[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b_0.offset(80 as libc::c_uint as isize));
    ws0[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b_0.offset(88 as libc::c_uint as isize));
    ws0[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b_0.offset(96 as libc::c_uint as isize));
    ws0[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b_0.offset(104 as libc::c_uint as isize));
    ws0[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b_0.offset(112 as libc::c_uint as isize));
    ws0[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b_0.offset(120 as libc::c_uint as isize));
    ws0[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b_0.offset(128 as libc::c_uint as isize));
    ws0[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b_0.offset(136 as libc::c_uint as isize));
    ws0[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b_0.offset(144 as libc::c_uint as isize));
    ws0[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b_0.offset(152 as libc::c_uint as isize));
    ws0[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b_0.offset(160 as libc::c_uint as isize));
    ws0[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b_0.offset(168 as libc::c_uint as isize));
    ws0[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b_0.offset(176 as libc::c_uint as isize));
    ws0[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b_0.offset(184 as libc::c_uint as isize));
    ws0[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b_0.offset(192 as libc::c_uint as isize));
    ws0[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b_0.offset(200 as libc::c_uint as isize));
    ws0[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b_0.offset(208 as libc::c_uint as isize));
    ws0[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b_0.offset(216 as libc::c_uint as isize));
    ws0[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b_0.offset(224 as libc::c_uint as isize));
    ws0[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b_0.offset(232 as libc::c_uint as isize));
    ws0[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b_0.offset(240 as libc::c_uint as isize));
    ws0[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b_0.offset(248 as libc::c_uint as isize));
    ws0[31 as libc::c_uint as usize] = u30;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        s[i_0 as usize] = s[i_0 as usize] ^ ws0[i_0 as usize];
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3;
    *b0_0
        .offset(
            rateInBytes1.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b3, s.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (48 as libc::c_uint).wrapping_div(rateInBytes1) {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            s.as_mut_ptr() as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i_1.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i_1 as usize],
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut b02: *mut uint8_t = rb;
        memcpy(
            b02.offset((i0 * rateInBytes1) as isize) as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_2: uint32_t = 0 as libc::c_uint;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_6: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_7: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = s[1 as libc::c_uint as usize];
            let mut current: uint64_t = x;
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_8 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_8 as usize];
                let mut temp: uint64_t = s[_Y as usize];
                let mut uu____1: uint64_t = current;
                s[_Y
                    as usize] = uu____1 << r
                    | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            let mut i_9: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_0: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_0: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_0: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_0: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_0;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_0;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_0;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_0;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_1: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_1: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_1: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_1;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_1;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_1;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_1;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_2: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_2: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_2: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_2;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_2;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_2;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_2;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_3: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_3: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_3: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_3;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_3;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_3;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_3;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            s[0 as libc::c_uint as usize] = s[0 as libc::c_uint as usize] ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
    let mut remOut: uint32_t = (48 as libc::c_uint).wrapping_rem(rateInBytes1);
    let mut hbuf_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_0.as_mut_ptr() as *mut libc::c_void,
        s.as_mut_ptr() as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    while i_10 < 32 as libc::c_uint {
        store64(
            hbuf_0.as_mut_ptr().offset(i_10.wrapping_mul(8 as libc::c_uint) as isize),
            ws_0[i_10 as usize],
        );
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    memcpy(
        rb.offset(48 as libc::c_uint as isize).offset(-(remOut as isize))
            as *mut libc::c_void,
        hbuf_0.as_mut_ptr() as *const libc::c_void,
        (remOut as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_sha3_512(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut s: [uint64_t; 25] = [
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
    let mut rateInBytes1: uint32_t = 72 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen / rateInBytes1 {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = ib;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset((i * rateInBytes1) as isize) as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b_, s.as_mut_ptr());
        i = i.wrapping_add(1);
        i;
    }
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b__0: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen % rateInBytes1;
    let mut b00: *mut uint8_t = ib;
    let mut bl0_0: *mut uint8_t = b__0;
    memcpy(
        bl0_0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b__0;
    *b01.offset((inputByteLen % rateInBytes1) as isize) = 0x6 as libc::c_uint as uint8_t;
    let mut ws0: [uint64_t; 32] = [
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
    ];
    let mut b_0: *mut uint8_t = b__0;
    let mut u: uint64_t = load64(b_0);
    ws0[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b_0.offset(8 as libc::c_uint as isize));
    ws0[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b_0.offset(16 as libc::c_uint as isize));
    ws0[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b_0.offset(24 as libc::c_uint as isize));
    ws0[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b_0.offset(32 as libc::c_uint as isize));
    ws0[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b_0.offset(40 as libc::c_uint as isize));
    ws0[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b_0.offset(48 as libc::c_uint as isize));
    ws0[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b_0.offset(56 as libc::c_uint as isize));
    ws0[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b_0.offset(64 as libc::c_uint as isize));
    ws0[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b_0.offset(72 as libc::c_uint as isize));
    ws0[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b_0.offset(80 as libc::c_uint as isize));
    ws0[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b_0.offset(88 as libc::c_uint as isize));
    ws0[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b_0.offset(96 as libc::c_uint as isize));
    ws0[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b_0.offset(104 as libc::c_uint as isize));
    ws0[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b_0.offset(112 as libc::c_uint as isize));
    ws0[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b_0.offset(120 as libc::c_uint as isize));
    ws0[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b_0.offset(128 as libc::c_uint as isize));
    ws0[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b_0.offset(136 as libc::c_uint as isize));
    ws0[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b_0.offset(144 as libc::c_uint as isize));
    ws0[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b_0.offset(152 as libc::c_uint as isize));
    ws0[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b_0.offset(160 as libc::c_uint as isize));
    ws0[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b_0.offset(168 as libc::c_uint as isize));
    ws0[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b_0.offset(176 as libc::c_uint as isize));
    ws0[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b_0.offset(184 as libc::c_uint as isize));
    ws0[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b_0.offset(192 as libc::c_uint as isize));
    ws0[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b_0.offset(200 as libc::c_uint as isize));
    ws0[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b_0.offset(208 as libc::c_uint as isize));
    ws0[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b_0.offset(216 as libc::c_uint as isize));
    ws0[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b_0.offset(224 as libc::c_uint as isize));
    ws0[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b_0.offset(232 as libc::c_uint as isize));
    ws0[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b_0.offset(240 as libc::c_uint as isize));
    ws0[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b_0.offset(248 as libc::c_uint as isize));
    ws0[31 as libc::c_uint as usize] = u30;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 25 as libc::c_uint {
        s[i_0 as usize] = s[i_0 as usize] ^ ws0[i_0 as usize];
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0_0: *mut uint8_t = b3;
    *b0_0
        .offset(
            rateInBytes1.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(rateInBytes1, b3, s.as_mut_ptr());
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < (64 as libc::c_uint).wrapping_div(rateInBytes1) {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            s.as_mut_ptr() as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        while i_1 < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i_1.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i_1 as usize],
            );
            i_1 = i_1.wrapping_add(1);
            i_1;
        }
        let mut b02: *mut uint8_t = rb;
        memcpy(
            b02.offset((i0 * rateInBytes1) as isize) as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (rateInBytes1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_2: uint32_t = 0 as libc::c_uint;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_2
                as usize] = s[i_2.wrapping_add(0 as libc::c_uint) as usize]
                ^ (s[i_2.wrapping_add(5 as libc::c_uint) as usize]
                    ^ (s[i_2.wrapping_add(10 as libc::c_uint) as usize]
                        ^ (s[i_2.wrapping_add(15 as libc::c_uint) as usize]
                            ^ s[i_2.wrapping_add(20 as libc::c_uint) as usize])));
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3))
                as usize] ^ _D;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4))
                as usize] ^ _D_0;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5))
                as usize] ^ _D_1;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_6: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_6))
                as usize] ^ _D_2;
            i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_7: uint32_t = 0 as libc::c_uint;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] = s[i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                as usize] ^ _D_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = s[1 as libc::c_uint as usize];
            let mut current: uint64_t = x;
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_8 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_8 as usize];
                let mut temp: uint64_t = s[_Y as usize];
                let mut uu____1: uint64_t = current;
                s[_Y
                    as usize] = uu____1 << r
                    | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            let mut i_9: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_0: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_0: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_0: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_0: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_0;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_0;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_0;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_0;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_0;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_1: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_1: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_1: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_1: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_1;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_1;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_1;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_1;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_1;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_2: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_2: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_2: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_2: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_2;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_2;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_2;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_2;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_2;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = s[(0 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(1 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v1_3: uint64_t = s[(1 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(2 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v2_3: uint64_t = s[(2 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(3 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v3_3: uint64_t = s[(3 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(4 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            let mut v4_3: uint64_t = s[(4 as libc::c_uint)
                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                ^ !s[(0 as libc::c_uint)
                    .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize]
                    & s[(1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_9)) as usize];
            s[(0 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v0_3;
            s[(1 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v1_3;
            s[(2 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v2_3;
            s[(3 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v3_3;
            s[(4 as libc::c_uint).wrapping_add((5 as libc::c_uint).wrapping_mul(i_9))
                as usize] = v4_3;
            i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            s[0 as libc::c_uint as usize] = s[0 as libc::c_uint as usize] ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
    let mut remOut: uint32_t = (64 as libc::c_uint).wrapping_rem(rateInBytes1);
    let mut hbuf_0: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut ws_0: [uint64_t; 32] = [
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
    ];
    memcpy(
        ws_0.as_mut_ptr() as *mut libc::c_void,
        s.as_mut_ptr() as *const libc::c_void,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i_10: uint32_t = 0 as libc::c_uint;
    while i_10 < 32 as libc::c_uint {
        store64(
            hbuf_0.as_mut_ptr().offset(i_10.wrapping_mul(8 as libc::c_uint) as isize),
            ws_0[i_10 as usize],
        );
        i_10 = i_10.wrapping_add(1);
        i_10;
    }
    memcpy(
        rb.offset(64 as libc::c_uint as isize).offset(-(remOut as isize))
            as *mut libc::c_void,
        hbuf_0.as_mut_ptr() as *const libc::c_void,
        (remOut as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_state_malloc() -> *mut uint64_t {
    let mut buf: *mut uint64_t = calloc(
        25 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    return buf;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_state_free(mut s: *mut uint64_t) {
    free(s as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_shake128_absorb_nblocks(
    mut state: *mut uint64_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < inputByteLen.wrapping_div(168 as libc::c_uint) {
        let mut b: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut b_: *mut uint8_t = b.as_mut_ptr();
        let mut b0: *mut uint8_t = input;
        let mut bl0: *mut uint8_t = b_;
        memcpy(
            bl0 as *mut libc::c_void,
            b0.offset(i.wrapping_mul(168 as libc::c_uint) as isize)
                as *const libc::c_void,
            (168 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_Hash_SHA3_absorb_inner_32(168 as libc::c_uint, b_, state);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_shake128_absorb_final(
    mut state: *mut uint64_t,
    mut input: *mut uint8_t,
    mut inputByteLen: uint32_t,
) {
    let mut b1: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b_: *mut uint8_t = b1.as_mut_ptr();
    let mut rem: uint32_t = inputByteLen.wrapping_rem(168 as libc::c_uint);
    let mut b00: *mut uint8_t = input;
    let mut bl0: *mut uint8_t = b_;
    memcpy(
        bl0 as *mut libc::c_void,
        b00.offset(inputByteLen as isize).offset(-(rem as isize)) as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut b01: *mut uint8_t = b_;
    *b01
        .offset(
            inputByteLen.wrapping_rem(168 as libc::c_uint) as isize,
        ) = 0x1f as libc::c_uint as uint8_t;
    let mut ws: [uint64_t; 32] = [
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
    ];
    let mut b: *mut uint8_t = b_;
    let mut u: uint64_t = load64(b);
    ws[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = load64(b.offset(8 as libc::c_uint as isize));
    ws[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = load64(b.offset(16 as libc::c_uint as isize));
    ws[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = load64(b.offset(24 as libc::c_uint as isize));
    ws[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = load64(b.offset(32 as libc::c_uint as isize));
    ws[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = load64(b.offset(40 as libc::c_uint as isize));
    ws[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = load64(b.offset(48 as libc::c_uint as isize));
    ws[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = load64(b.offset(56 as libc::c_uint as isize));
    ws[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = load64(b.offset(64 as libc::c_uint as isize));
    ws[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = load64(b.offset(72 as libc::c_uint as isize));
    ws[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = load64(b.offset(80 as libc::c_uint as isize));
    ws[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = load64(b.offset(88 as libc::c_uint as isize));
    ws[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = load64(b.offset(96 as libc::c_uint as isize));
    ws[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = load64(b.offset(104 as libc::c_uint as isize));
    ws[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = load64(b.offset(112 as libc::c_uint as isize));
    ws[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = load64(b.offset(120 as libc::c_uint as isize));
    ws[15 as libc::c_uint as usize] = u14;
    let mut u15: uint64_t = load64(b.offset(128 as libc::c_uint as isize));
    ws[16 as libc::c_uint as usize] = u15;
    let mut u16: uint64_t = load64(b.offset(136 as libc::c_uint as isize));
    ws[17 as libc::c_uint as usize] = u16;
    let mut u17: uint64_t = load64(b.offset(144 as libc::c_uint as isize));
    ws[18 as libc::c_uint as usize] = u17;
    let mut u18: uint64_t = load64(b.offset(152 as libc::c_uint as isize));
    ws[19 as libc::c_uint as usize] = u18;
    let mut u19: uint64_t = load64(b.offset(160 as libc::c_uint as isize));
    ws[20 as libc::c_uint as usize] = u19;
    let mut u20: uint64_t = load64(b.offset(168 as libc::c_uint as isize));
    ws[21 as libc::c_uint as usize] = u20;
    let mut u21: uint64_t = load64(b.offset(176 as libc::c_uint as isize));
    ws[22 as libc::c_uint as usize] = u21;
    let mut u22: uint64_t = load64(b.offset(184 as libc::c_uint as isize));
    ws[23 as libc::c_uint as usize] = u22;
    let mut u23: uint64_t = load64(b.offset(192 as libc::c_uint as isize));
    ws[24 as libc::c_uint as usize] = u23;
    let mut u24: uint64_t = load64(b.offset(200 as libc::c_uint as isize));
    ws[25 as libc::c_uint as usize] = u24;
    let mut u25: uint64_t = load64(b.offset(208 as libc::c_uint as isize));
    ws[26 as libc::c_uint as usize] = u25;
    let mut u26: uint64_t = load64(b.offset(216 as libc::c_uint as isize));
    ws[27 as libc::c_uint as usize] = u26;
    let mut u27: uint64_t = load64(b.offset(224 as libc::c_uint as isize));
    ws[28 as libc::c_uint as usize] = u27;
    let mut u28: uint64_t = load64(b.offset(232 as libc::c_uint as isize));
    ws[29 as libc::c_uint as usize] = u28;
    let mut u29: uint64_t = load64(b.offset(240 as libc::c_uint as isize));
    ws[30 as libc::c_uint as usize] = u29;
    let mut u30: uint64_t = load64(b.offset(248 as libc::c_uint as isize));
    ws[31 as libc::c_uint as usize] = u30;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 25 as libc::c_uint {
        *state.offset(i as isize) = *state.offset(i as isize) ^ ws[i as usize];
        i = i.wrapping_add(1);
        i;
    }
    let mut b2: [uint8_t; 256] = [
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
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
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
    let mut b3: *mut uint8_t = b2.as_mut_ptr();
    let mut b0: *mut uint8_t = b3;
    *b0.offset(167 as libc::c_uint as isize) = 0x80 as libc::c_uint as uint8_t;
    Hacl_Hash_SHA3_absorb_inner_32(168 as libc::c_uint, b3, state);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA3_shake128_squeeze_nblocks(
    mut state: *mut uint64_t,
    mut output: *mut uint8_t,
    mut outputByteLen: uint32_t,
) {
    let mut i0: uint32_t = 0 as libc::c_uint;
    while i0 < outputByteLen.wrapping_div(168 as libc::c_uint) {
        let mut hbuf: [uint8_t; 256] = [
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
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
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
        let mut ws: [uint64_t; 32] = [
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
        ];
        memcpy(
            ws.as_mut_ptr() as *mut libc::c_void,
            state as *const libc::c_void,
            (25 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < 32 as libc::c_uint {
            store64(
                hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
                ws[i as usize],
            );
            i = i.wrapping_add(1);
            i;
        }
        let mut b0: *mut uint8_t = output;
        memcpy(
            b0.offset(i0.wrapping_mul(168 as libc::c_uint) as isize)
                as *mut libc::c_void,
            hbuf.as_mut_ptr() as *const libc::c_void,
            (168 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut i1: uint32_t = 0 as libc::c_uint;
        while i1 < 24 as libc::c_uint {
            let mut _C: [uint64_t; 5] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0];
            let mut i_0: uint32_t = 0 as libc::c_uint;
            _C[i_0
                as usize] = *state.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*state.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*state.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*state.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *state
                                .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
            i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_0
                as usize] = *state.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*state.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*state.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*state.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *state
                                .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
            i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_0
                as usize] = *state.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*state.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*state.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*state.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *state
                                .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
            i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_0
                as usize] = *state.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*state.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*state.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*state.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *state
                                .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
            i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            _C[i_0
                as usize] = *state.offset(i_0.wrapping_add(0 as libc::c_uint) as isize)
                ^ (*state.offset(i_0.wrapping_add(5 as libc::c_uint) as isize)
                    ^ (*state.offset(i_0.wrapping_add(10 as libc::c_uint) as isize)
                        ^ (*state.offset(i_0.wrapping_add(15 as libc::c_uint) as isize)
                            ^ *state
                                .offset(i_0.wrapping_add(20 as libc::c_uint) as isize))));
            i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut i2: uint32_t = 0 as libc::c_uint;
            let mut uu____0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0 << 1 as libc::c_uint | uu____0 >> 63 as libc::c_uint);
            let mut i_1: uint32_t = 0 as libc::c_uint;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
                ^ _D;
            i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
                ^ _D;
            i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
                ^ _D;
            i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
                ^ _D;
            i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_1)) as isize)
                ^ _D;
            i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_0: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_0: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_0 << 1 as libc::c_uint | uu____0_0 >> 63 as libc::c_uint);
            let mut i_2: uint32_t = 0 as libc::c_uint;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
                ^ _D_0;
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
                ^ _D_0;
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
                ^ _D_0;
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
                ^ _D_0;
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_2)) as isize)
                ^ _D_0;
            i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_1: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_1: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_1 << 1 as libc::c_uint | uu____0_1 >> 63 as libc::c_uint);
            let mut i_3: uint32_t = 0 as libc::c_uint;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
                ^ _D_1;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
                ^ _D_1;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
                ^ _D_1;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
                ^ _D_1;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_3)) as isize)
                ^ _D_1;
            i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_2: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_2: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_2 << 1 as libc::c_uint | uu____0_2 >> 63 as libc::c_uint);
            let mut i_4: uint32_t = 0 as libc::c_uint;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
                ^ _D_2;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
                ^ _D_2;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
                ^ _D_2;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
                ^ _D_2;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_4)) as isize)
                ^ _D_2;
            i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut uu____0_3: uint64_t = _C[i2
                .wrapping_add(1 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize];
            let mut _D_3: uint64_t = _C[i2
                .wrapping_add(4 as libc::c_uint)
                .wrapping_rem(5 as libc::c_uint) as usize]
                ^ (uu____0_3 << 1 as libc::c_uint | uu____0_3 >> 63 as libc::c_uint);
            let mut i_5: uint32_t = 0 as libc::c_uint;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
                ^ _D_3;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
                ^ _D_3;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
                ^ _D_3;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
                ^ _D_3;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            *state
                .offset(
                    i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize,
                ) = *state
                .offset(i2.wrapping_add((5 as libc::c_uint).wrapping_mul(i_5)) as isize)
                ^ _D_3;
            i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            i2 = (i2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut x: uint64_t = *state.offset(1 as libc::c_uint as isize);
            let mut current: uint64_t = x;
            let mut i_6: uint32_t = 0 as libc::c_uint;
            while i_6 < 24 as libc::c_uint {
                let mut _Y: uint32_t = Hacl_Hash_SHA3_keccak_piln[i_6 as usize];
                let mut r: uint32_t = Hacl_Hash_SHA3_keccak_rotc[i_6 as usize];
                let mut temp: uint64_t = *state.offset(_Y as isize);
                let mut uu____1: uint64_t = current;
                *state
                    .offset(
                        _Y as isize,
                    ) = uu____1 << r | uu____1 >> (64 as libc::c_uint).wrapping_sub(r);
                current = temp;
                i_6 = i_6.wrapping_add(1);
                i_6;
            }
            let mut i_7: uint32_t = 0 as libc::c_uint;
            let mut v0: uint64_t = *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v1: uint64_t = *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v2: uint64_t = *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v3: uint64_t = *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v4: uint64_t = *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v0;
            *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v1;
            *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v2;
            *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v3;
            *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v4;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_0: uint64_t = *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v1_0: uint64_t = *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v2_0: uint64_t = *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v3_0: uint64_t = *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v4_0: uint64_t = *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v0_0;
            *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v1_0;
            *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v2_0;
            *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v3_0;
            *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v4_0;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_1: uint64_t = *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v1_1: uint64_t = *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v2_1: uint64_t = *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v3_1: uint64_t = *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v4_1: uint64_t = *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v0_1;
            *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v1_1;
            *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v2_1;
            *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v3_1;
            *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v4_1;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_2: uint64_t = *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v1_2: uint64_t = *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v2_2: uint64_t = *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v3_2: uint64_t = *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v4_2: uint64_t = *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v0_2;
            *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v1_2;
            *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v2_2;
            *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v3_2;
            *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v4_2;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut v0_3: uint64_t = *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (1 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (2 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v1_3: uint64_t = *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (2 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (3 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v2_3: uint64_t = *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (3 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (4 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v3_3: uint64_t = *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (4 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (0 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            let mut v4_3: uint64_t = *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                )
                ^ !*state
                    .offset(
                        (0 as libc::c_uint)
                            .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                    )
                    & *state
                        .offset(
                            (1 as libc::c_uint)
                                .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7))
                                as isize,
                        );
            *state
                .offset(
                    (0 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v0_3;
            *state
                .offset(
                    (1 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v1_3;
            *state
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v2_3;
            *state
                .offset(
                    (3 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v3_3;
            *state
                .offset(
                    (4 as libc::c_uint)
                        .wrapping_add((5 as libc::c_uint).wrapping_mul(i_7)) as isize,
                ) = v4_3;
            i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c: uint64_t = Hacl_Hash_SHA3_keccak_rndc[i1 as usize];
            *state
                .offset(
                    0 as libc::c_uint as isize,
                ) = *state.offset(0 as libc::c_uint as isize) ^ c;
            i1 = i1.wrapping_add(1);
            i1;
        }
        i0 = i0.wrapping_add(1);
        i0;
    }
}
