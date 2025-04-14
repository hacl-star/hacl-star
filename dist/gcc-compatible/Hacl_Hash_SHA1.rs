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
pub type __uint32_t = libc::c_uint;
pub type __uint64_t = libc::c_ulonglong;
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
unsafe extern "C" fn _OSSwapInt32(mut _data: __uint32_t) -> __uint32_t {
    _data = _data.swap_bytes();
    return _data;
}
#[inline]
unsafe extern "C" fn _OSSwapInt64(mut _data: __uint64_t) -> __uint64_t {
    return _data.swap_bytes();
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
#[inline]
unsafe extern "C" fn store64(mut b: *mut uint8_t, mut i: uint64_t) {
    memcpy(
        b as *mut libc::c_void,
        &mut i as *mut uint64_t as *const libc::c_void,
        8 as libc::c_int as libc::c_ulong,
    );
}
static mut _h0: [uint32_t; 5] = [
    0x67452301 as libc::c_uint,
    0xefcdab89 as libc::c_uint,
    0x98badcfe as libc::c_uint,
    0x10325476 as libc::c_uint,
    0xc3d2e1f0 as libc::c_uint,
];
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_init(mut s: *mut uint32_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    *s.offset(i as isize) = _h0[i as usize];
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
unsafe extern "C" fn update(mut h: *mut uint32_t, mut l: *mut uint8_t) {
    let mut ha: uint32_t = *h.offset(0 as libc::c_uint as isize);
    let mut hb: uint32_t = *h.offset(1 as libc::c_uint as isize);
    let mut hc: uint32_t = *h.offset(2 as libc::c_uint as isize);
    let mut hd: uint32_t = *h.offset(3 as libc::c_uint as isize);
    let mut he: uint32_t = *h.offset(4 as libc::c_uint as isize);
    let mut _w: [uint32_t; 80] = [
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
    ];
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 80 as libc::c_uint {
        let mut v: uint32_t = 0;
        if i < 16 as libc::c_uint {
            let mut b: *mut uint8_t = l
                .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
            let mut u: uint32_t = if 0 != 0 {
                (load32(b) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                    | (load32(b) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                    | (load32(b) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                    | (load32(b) & 0xff as libc::c_uint) << 24 as libc::c_int
            } else {
                _OSSwapInt32(load32(b))
            };
            v = u;
        } else {
            let mut wmit3: uint32_t = _w[i.wrapping_sub(3 as libc::c_uint) as usize];
            let mut wmit8: uint32_t = _w[i.wrapping_sub(8 as libc::c_uint) as usize];
            let mut wmit14: uint32_t = _w[i.wrapping_sub(14 as libc::c_uint) as usize];
            let mut wmit16: uint32_t = _w[i.wrapping_sub(16 as libc::c_uint) as usize];
            v = (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) << 1 as libc::c_uint
                | (wmit3 ^ (wmit8 ^ (wmit14 ^ wmit16))) >> 31 as libc::c_uint;
        }
        _w[i as usize] = v;
        i = i.wrapping_add(1);
        i;
    }
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 80 as libc::c_uint {
        let mut _a: uint32_t = *h.offset(0 as libc::c_uint as isize);
        let mut _b: uint32_t = *h.offset(1 as libc::c_uint as isize);
        let mut _c: uint32_t = *h.offset(2 as libc::c_uint as isize);
        let mut _d: uint32_t = *h.offset(3 as libc::c_uint as isize);
        let mut _e: uint32_t = *h.offset(4 as libc::c_uint as isize);
        let mut wmit: uint32_t = _w[i_0 as usize];
        let mut ite0: uint32_t = 0;
        if i_0 < 20 as libc::c_uint {
            ite0 = _b & _c ^ !_b & _d;
        } else if (39 as libc::c_uint) < i_0 && i_0 < 60 as libc::c_uint {
            ite0 = _b & _c ^ (_b & _d ^ _c & _d);
        } else {
            ite0 = _b ^ (_c ^ _d);
        }
        let mut ite: uint32_t = 0;
        if i_0 < 20 as libc::c_uint {
            ite = 0x5a827999 as libc::c_uint;
        } else if i_0 < 40 as libc::c_uint {
            ite = 0x6ed9eba1 as libc::c_uint;
        } else if i_0 < 60 as libc::c_uint {
            ite = 0x8f1bbcdc as libc::c_uint;
        } else {
            ite = 0xca62c1d6 as libc::c_uint;
        }
        let mut _T: uint32_t = (_a << 5 as libc::c_uint | _a >> 27 as libc::c_uint)
            .wrapping_add(ite0)
            .wrapping_add(_e)
            .wrapping_add(ite)
            .wrapping_add(wmit);
        *h.offset(0 as libc::c_uint as isize) = _T;
        *h.offset(1 as libc::c_uint as isize) = _a;
        *h
            .offset(
                2 as libc::c_uint as isize,
            ) = _b << 30 as libc::c_uint | _b >> 2 as libc::c_uint;
        *h.offset(3 as libc::c_uint as isize) = _c;
        *h.offset(4 as libc::c_uint as isize) = _d;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < 80 as libc::c_uint {
        _w[i_1 as usize] = 0 as libc::c_uint;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut sta: uint32_t = *h.offset(0 as libc::c_uint as isize);
    let mut stb: uint32_t = *h.offset(1 as libc::c_uint as isize);
    let mut stc: uint32_t = *h.offset(2 as libc::c_uint as isize);
    let mut std: uint32_t = *h.offset(3 as libc::c_uint as isize);
    let mut ste: uint32_t = *h.offset(4 as libc::c_uint as isize);
    *h.offset(0 as libc::c_uint as isize) = sta.wrapping_add(ha);
    *h.offset(1 as libc::c_uint as isize) = stb.wrapping_add(hb);
    *h.offset(2 as libc::c_uint as isize) = stc.wrapping_add(hc);
    *h.offset(3 as libc::c_uint as isize) = std.wrapping_add(hd);
    *h.offset(4 as libc::c_uint as isize) = ste.wrapping_add(he);
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
    store64(
        dst3,
        if 0 != 0 {
            (len << 3 as libc::c_uint & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (len << 3 as libc::c_uint & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(len << 3 as libc::c_uint)
        },
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_finish(
    mut s: *mut uint32_t,
    mut dst: *mut uint8_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*s.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*s.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*s.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*s.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*s.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*s.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*s.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*s.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*s.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*s.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*s.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*s.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        dst.offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*s.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*s.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*s.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*s.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_update_multi(
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
pub unsafe extern "C" fn Hacl_Hash_SHA1_update_last(
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
    Hacl_Hash_SHA1_update_multi(s, blocks, blocks_n);
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
    Hacl_Hash_SHA1_update_multi(s, tmp, tmp_len.wrapping_div(64 as libc::c_uint));
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_hash_oneshot(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut s: [uint32_t; 5] = [
        0x67452301 as libc::c_uint,
        0xefcdab89 as libc::c_uint,
        0x98badcfe as libc::c_uint,
        0x10325476 as libc::c_uint,
        0xc3d2e1f0 as libc::c_uint,
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
    Hacl_Hash_SHA1_update_multi(s.as_mut_ptr(), blocks, blocks_n);
    Hacl_Hash_SHA1_update_last(s.as_mut_ptr(), blocks_len as uint64_t, rest, rest_len);
    Hacl_Hash_SHA1_finish(s.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_malloc() -> *mut Hacl_Streaming_MD_state_32 {
    let mut buf: *mut uint8_t = calloc(
        64 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut block_state: *mut uint32_t = calloc(
        5 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    Hacl_Hash_SHA1_init(block_state);
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
pub unsafe extern "C" fn Hacl_Hash_SHA1_reset(
    mut state: *mut Hacl_Streaming_MD_state_32,
) {
    let mut block_state: *mut uint32_t = (*state).block_state;
    Hacl_Hash_SHA1_init(block_state);
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_update(
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
            Hacl_Hash_SHA1_update_multi(block_state, buf_0, 1 as libc::c_uint);
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
        Hacl_Hash_SHA1_update_multi(
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
            Hacl_Hash_SHA1_update_multi(block_state, buf0, 1 as libc::c_uint);
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
        Hacl_Hash_SHA1_update_multi(
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
pub unsafe extern "C" fn Hacl_Hash_SHA1_digest(
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
    let mut tmp_block_state: [uint32_t; 5] = [0 as libc::c_uint, 0, 0, 0, 0];
    memcpy(
        tmp_block_state.as_mut_ptr() as *mut libc::c_void,
        block_state as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
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
    Hacl_Hash_SHA1_update_multi(
        tmp_block_state.as_mut_ptr(),
        buf_multi,
        0 as libc::c_uint,
    );
    let mut prev_len_last: uint64_t = total_len.wrapping_sub(r as uint64_t);
    Hacl_Hash_SHA1_update_last(tmp_block_state.as_mut_ptr(), prev_len_last, buf_last, r);
    Hacl_Hash_SHA1_finish(tmp_block_state.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_free(
    mut state: *mut Hacl_Streaming_MD_state_32,
) {
    let mut scrut: Hacl_Streaming_MD_state_32 = *state;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: *mut uint32_t = scrut.block_state;
    free(block_state as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA1_copy(
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
        5 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    memcpy(
        block_state as *mut libc::c_void,
        block_state0 as *const libc::c_void,
        (5 as libc::c_uint as libc::c_ulong)
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
pub unsafe extern "C" fn Hacl_Hash_SHA1_hash(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    Hacl_Hash_SHA1_hash_oneshot(output, input, input_len);
}
