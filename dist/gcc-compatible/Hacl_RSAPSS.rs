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
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
    fn Hacl_Hash_SHA2_hash_256(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
    fn Hacl_Hash_SHA2_hash_512(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
    fn Hacl_Hash_SHA2_hash_384(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
    fn Hacl_Bignum_ModInvLimb_mod_inv_uint64(n0: uint64_t) -> uint64_t;
    fn Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
        len: uint32_t,
        nBits: uint32_t,
        n: *mut uint64_t,
        res: *mut uint64_t,
    );
    fn Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
        len: uint32_t,
        n: *mut uint64_t,
        mu: uint64_t,
        r2: *mut uint64_t,
        a: *mut uint64_t,
        bBits: uint32_t,
        b: *mut uint64_t,
        res: *mut uint64_t,
    );
    fn Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
        len: uint32_t,
        n: *mut uint64_t,
        mu: uint64_t,
        r2: *mut uint64_t,
        a: *mut uint64_t,
        bBits: uint32_t,
        b: *mut uint64_t,
        res: *mut uint64_t,
    );
}
pub type __int64_t = libc::c_longlong;
pub type __uint64_t = libc::c_ulonglong;
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
unsafe extern "C" fn FStar_UInt8_eq_mask(mut a: uint8_t, mut b: uint8_t) -> uint8_t {
    let mut x: uint8_t = (a as uint32_t ^ b as uint32_t) as uint8_t;
    let mut minus_x: uint8_t = (!(x as libc::c_int) as uint32_t)
        .wrapping_add(1 as libc::c_uint) as uint8_t;
    let mut x_or_minus_x: uint8_t = (x as uint32_t | minus_x as uint32_t) as uint8_t;
    let mut xnx: uint8_t = (x_or_minus_x as uint32_t >> 7 as libc::c_uint) as uint8_t;
    return (xnx as uint32_t).wrapping_sub(1 as libc::c_uint) as uint8_t;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Convert_bn_from_bytes_be_uint64(
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut res: *mut uint64_t,
) {
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
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            69 as libc::c_int,
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
        let mut os: *mut uint64_t = res;
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Convert_bn_to_bytes_be_uint64(
    mut len: uint32_t,
    mut b: *mut uint64_t,
    mut res: *mut uint8_t,
) {
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
            b"./internal/Hacl_Bignum_Base.h\0" as *const u8 as *const libc::c_char,
            87 as libc::c_int,
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
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < bnLen {
        store64(
            tmp.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
            if 0 != 0 {
                (*b
                    .offset(
                        bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint) as isize,
                    ) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                    | (*b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
            } else {
                _OSSwapInt64(
                    *b
                        .offset(
                            bnLen.wrapping_sub(i).wrapping_sub(1 as libc::c_uint)
                                as isize,
                        ),
                )
            },
        );
        i = i.wrapping_add(1);
        i;
    }
    memcpy(
        res as *mut libc::c_void,
        tmp.as_mut_ptr().offset(tmpLen as isize).offset(-(len as isize))
            as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[inline]
unsafe extern "C" fn hash_len(mut a: Spec_Hash_Definitions_hash_alg) -> uint32_t {
    match a as libc::c_int {
        5 => return 16 as libc::c_uint,
        4 => return 20 as libc::c_uint,
        0 => return 28 as libc::c_uint,
        1 => return 32 as libc::c_uint,
        2 => return 48 as libc::c_uint,
        3 => return 64 as libc::c_uint,
        6 => return 32 as libc::c_uint,
        7 => return 64 as libc::c_uint,
        9 => return 28 as libc::c_uint,
        8 => return 32 as libc::c_uint,
        10 => return 48 as libc::c_uint,
        11 => return 64 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                86 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[inline]
unsafe extern "C" fn hash(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut mHash: *mut uint8_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
) {
    match a as libc::c_int {
        1 => {
            Hacl_Hash_SHA2_hash_256(mHash, msg, msgLen);
        }
        2 => {
            Hacl_Hash_SHA2_hash_384(mHash, msg, msgLen);
        }
        3 => {
            Hacl_Hash_SHA2_hash_512(mHash, msg, msgLen);
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                114 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[inline]
unsafe extern "C" fn mgf_hash(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut len: uint32_t,
    mut mgfseed: *mut uint8_t,
    mut maskLen: uint32_t,
    mut res: *mut uint8_t,
) {
    if len.wrapping_add(4 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            129 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len.wrapping_add(4 as libc::c_uint) as usize;
    let mut mgfseed_counter: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        mgfseed_counter.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len.wrapping_add(4 as libc::c_uint) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        mgfseed_counter.as_mut_ptr() as *mut libc::c_void,
        mgfseed as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut hLen: uint32_t = hash_len(a);
    let mut n: uint32_t = maskLen
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(hLen)
        .wrapping_add(1 as libc::c_uint);
    let mut accLen: uint32_t = n * hLen;
    if accLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            136 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = accLen as usize;
    let mut acc: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        acc.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (accLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < n {
        let mut acc_i: *mut uint8_t = acc.as_mut_ptr().offset((i * hLen) as isize);
        let mut c: *mut uint8_t = mgfseed_counter.as_mut_ptr().offset(len as isize);
        *c.offset(0 as libc::c_uint as isize) = (i >> 24 as libc::c_uint) as uint8_t;
        *c.offset(1 as libc::c_uint as isize) = (i >> 16 as libc::c_uint) as uint8_t;
        *c.offset(2 as libc::c_uint as isize) = (i >> 8 as libc::c_uint) as uint8_t;
        *c.offset(3 as libc::c_uint as isize) = i as uint8_t;
        hash(
            a,
            acc_i,
            len.wrapping_add(4 as libc::c_uint),
            mgfseed_counter.as_mut_ptr(),
        );
        i = i.wrapping_add(1);
        i;
    }
    memcpy(
        res as *mut libc::c_void,
        acc.as_mut_ptr() as *const libc::c_void,
        (maskLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[inline]
unsafe extern "C" fn check_num_bits_u64(
    mut bs: uint32_t,
    mut b: *mut uint64_t,
) -> uint64_t {
    let mut bLen: uint32_t = bs
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    if bs == (64 as libc::c_uint).wrapping_mul(bLen) {
        return 0xffffffffffffffff as libc::c_ulonglong;
    }
    if bLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            159 as libc::c_int,
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
    let mut i0: uint32_t = bs.wrapping_div(64 as libc::c_uint);
    let mut j: uint32_t = bs.wrapping_rem(64 as libc::c_uint);
    *b2
        .as_mut_ptr()
        .offset(
            i0 as isize,
        ) = *b2.as_mut_ptr().offset(i0 as isize) | (1 as libc::c_ulonglong) << j;
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < bLen {
        let mut beq: uint64_t = FStar_UInt64_eq_mask(
            *b.offset(i as isize),
            *b2.as_mut_ptr().offset(i as isize),
        );
        let mut blt: uint64_t = !FStar_UInt64_gte_mask(
            *b.offset(i as isize),
            *b2.as_mut_ptr().offset(i as isize),
        );
        acc = beq & acc | !beq & blt;
        i = i.wrapping_add(1);
        i;
    }
    let mut res: uint64_t = acc;
    return res;
}
#[inline]
unsafe extern "C" fn check_modulus_u64(
    mut modBits: uint32_t,
    mut n: *mut uint64_t,
) -> uint64_t {
    let mut nLen: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut bits0: uint64_t = *n.offset(0 as libc::c_uint as isize)
        & 1 as libc::c_ulonglong;
    let mut m0: uint64_t = (0 as libc::c_ulonglong).wrapping_sub(bits0);
    if nLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            181 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = nLen as usize;
    let mut b2: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        b2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (nLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut i0: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint);
    let mut j: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_rem(64 as libc::c_uint);
    *b2
        .as_mut_ptr()
        .offset(
            i0 as isize,
        ) = *b2.as_mut_ptr().offset(i0 as isize) | (1 as libc::c_ulonglong) << j;
    let mut acc: uint64_t = 0 as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < nLen {
        let mut beq: uint64_t = FStar_UInt64_eq_mask(
            *b2.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        let mut blt: uint64_t = !FStar_UInt64_gte_mask(
            *b2.as_mut_ptr().offset(i as isize),
            *n.offset(i as isize),
        );
        acc = beq & acc | !beq & blt;
        i = i.wrapping_add(1);
        i;
    }
    let mut res: uint64_t = acc;
    let mut m1: uint64_t = res;
    let mut m2: uint64_t = check_num_bits_u64(modBits, n);
    return m0 & (m1 & m2);
}
#[inline]
unsafe extern "C" fn check_exponent_u64(
    mut eBits: uint32_t,
    mut e: *mut uint64_t,
) -> uint64_t {
    let mut eLen: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    if eLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            203 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = eLen as usize;
    let mut bn_zero: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        bn_zero.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (eLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut mask: uint64_t = 0xffffffffffffffff as libc::c_ulonglong;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < eLen {
        let mut uu____0: uint64_t = FStar_UInt64_eq_mask(
            *e.offset(i as isize),
            *bn_zero.as_mut_ptr().offset(i as isize),
        );
        mask = uu____0 & mask;
        i = i.wrapping_add(1);
        i;
    }
    let mut mask1: uint64_t = mask;
    let mut res: uint64_t = mask1;
    let mut m0: uint64_t = res;
    let mut m1: uint64_t = check_num_bits_u64(eBits, e);
    return !m0 & m1;
}
#[inline]
unsafe extern "C" fn pss_encode(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut saltLen: uint32_t,
    mut salt: *mut uint8_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
    mut emBits: uint32_t,
    mut em: *mut uint8_t,
) {
    let mut hLen: uint32_t = hash_len(a);
    if hLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            231 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = hLen as usize;
    let mut m1Hash: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        m1Hash.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (hLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut m1Len: uint32_t = (8 as libc::c_uint)
        .wrapping_add(hLen)
        .wrapping_add(saltLen);
    if m1Len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            235 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = m1Len as usize;
    let mut m1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        m1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (m1Len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    hash(a, m1.as_mut_ptr().offset(8 as libc::c_uint as isize), msgLen, msg);
    memcpy(
        m1.as_mut_ptr().offset(8 as libc::c_uint as isize).offset(hLen as isize)
            as *mut libc::c_void,
        salt as *const libc::c_void,
        (saltLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    hash(a, m1Hash.as_mut_ptr(), m1Len, m1.as_mut_ptr());
    let mut emLen: uint32_t = emBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut dbLen: uint32_t = emLen.wrapping_sub(hLen).wrapping_sub(1 as libc::c_uint);
    if dbLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            243 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = dbLen as usize;
    let mut db: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        db.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (dbLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut last_before_salt: uint32_t = dbLen
        .wrapping_sub(saltLen)
        .wrapping_sub(1 as libc::c_uint);
    *db.as_mut_ptr().offset(last_before_salt as isize) = 1 as libc::c_uint as uint8_t;
    memcpy(
        db
            .as_mut_ptr()
            .offset(last_before_salt as isize)
            .offset(1 as libc::c_uint as isize) as *mut libc::c_void,
        salt as *const libc::c_void,
        (saltLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if dbLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            249 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_2 = dbLen as usize;
    let mut dbMask: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
    memset(
        dbMask.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (dbLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    mgf_hash(a, hLen, m1Hash.as_mut_ptr(), dbLen, dbMask.as_mut_ptr());
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < dbLen {
        let mut x: uint8_t = (*db.as_mut_ptr().offset(i as isize) as uint32_t
            ^ *dbMask.as_mut_ptr().offset(i as isize) as uint32_t) as uint8_t;
        let mut os: *mut uint8_t = db.as_mut_ptr();
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    let mut msBits: uint32_t = emBits.wrapping_rem(8 as libc::c_uint);
    if msBits > 0 as libc::c_uint {
        *db
            .as_mut_ptr()
            .offset(
                0 as libc::c_uint as isize,
            ) = (*db.as_mut_ptr().offset(0 as libc::c_uint as isize) as uint32_t
            & 0xff as libc::c_uint >> (8 as libc::c_uint).wrapping_sub(msBits))
            as uint8_t;
    }
    memcpy(
        em as *mut libc::c_void,
        db.as_mut_ptr() as *const libc::c_void,
        (dbLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        em.offset(dbLen as isize) as *mut libc::c_void,
        m1Hash.as_mut_ptr() as *const libc::c_void,
        (hLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    *em
        .offset(
            emLen.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0xbc as libc::c_uint as uint8_t;
}
#[inline]
unsafe extern "C" fn pss_verify(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut saltLen: uint32_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
    mut emBits: uint32_t,
    mut em: *mut uint8_t,
) -> bool {
    let mut emLen: uint32_t = emBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut msBits: uint32_t = emBits.wrapping_rem(8 as libc::c_uint);
    let mut em_0: uint8_t = 0;
    if msBits > 0 as libc::c_uint {
        em_0 = (*em.offset(0 as libc::c_uint as isize) as uint32_t
            & (0xff as libc::c_uint) << msBits) as uint8_t;
    } else {
        em_0 = 0 as libc::c_uint as uint8_t;
    }
    let mut em_last: uint8_t = *em
        .offset(emLen.wrapping_sub(1 as libc::c_uint) as isize);
    if emLen < saltLen.wrapping_add(hash_len(a)).wrapping_add(2 as libc::c_uint)
        || !(em_last as libc::c_uint == 0xbc as libc::c_uint
            && em_0 as libc::c_uint == 0 as libc::c_uint)
    {
        return 0 as libc::c_int != 0;
    }
    let mut emLen1: uint32_t = emBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut hLen: uint32_t = hash_len(a);
    if hLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            297 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = hLen as usize;
    let mut m1Hash0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        m1Hash0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (hLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut dbLen: uint32_t = emLen1.wrapping_sub(hLen).wrapping_sub(1 as libc::c_uint);
    let mut maskedDB: *mut uint8_t = em;
    let mut m1Hash: *mut uint8_t = em.offset(dbLen as isize);
    if dbLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            303 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = dbLen as usize;
    let mut dbMask: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        dbMask.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (dbLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    mgf_hash(a, hLen, m1Hash, dbLen, dbMask.as_mut_ptr());
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < dbLen {
        let mut x: uint8_t = (*dbMask.as_mut_ptr().offset(i as isize) as uint32_t
            ^ *maskedDB.offset(i as isize) as uint32_t) as uint8_t;
        let mut os: *mut uint8_t = dbMask.as_mut_ptr();
        *os.offset(i as isize) = x;
        i = i.wrapping_add(1);
        i;
    }
    let mut msBits1: uint32_t = emBits.wrapping_rem(8 as libc::c_uint);
    if msBits1 > 0 as libc::c_uint {
        *dbMask
            .as_mut_ptr()
            .offset(
                0 as libc::c_uint as isize,
            ) = (*dbMask.as_mut_ptr().offset(0 as libc::c_uint as isize) as uint32_t
            & 0xff as libc::c_uint >> (8 as libc::c_uint).wrapping_sub(msBits1))
            as uint8_t;
    }
    let mut padLen: uint32_t = emLen1
        .wrapping_sub(saltLen)
        .wrapping_sub(hLen)
        .wrapping_sub(1 as libc::c_uint);
    if padLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            319 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = padLen as usize;
    let mut pad2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        pad2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (padLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    *pad2
        .as_mut_ptr()
        .offset(
            padLen.wrapping_sub(1 as libc::c_uint) as isize,
        ) = 0x1 as libc::c_uint as uint8_t;
    let mut pad: *mut uint8_t = dbMask.as_mut_ptr();
    let mut salt: *mut uint8_t = dbMask.as_mut_ptr().offset(padLen as isize);
    let mut res: uint8_t = 255 as libc::c_uint as uint8_t;
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < padLen {
        let mut uu____0: uint8_t = FStar_UInt8_eq_mask(
            *pad.offset(i_0 as isize),
            *pad2.as_mut_ptr().offset(i_0 as isize),
        );
        res = (uu____0 as uint32_t & res as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut z: uint8_t = res;
    if !(z as libc::c_uint == 255 as libc::c_uint) {
        return 0 as libc::c_int != 0;
    }
    let mut m1Len: uint32_t = (8 as libc::c_uint)
        .wrapping_add(hLen)
        .wrapping_add(saltLen);
    if m1Len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            337 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_2 = m1Len as usize;
    let mut m1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
    memset(
        m1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (m1Len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    hash(a, m1.as_mut_ptr().offset(8 as libc::c_uint as isize), msgLen, msg);
    memcpy(
        m1.as_mut_ptr().offset(8 as libc::c_uint as isize).offset(hLen as isize)
            as *mut libc::c_void,
        salt as *const libc::c_void,
        (saltLen as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    hash(a, m1Hash0.as_mut_ptr(), m1Len, m1.as_mut_ptr());
    let mut res0: uint8_t = 255 as libc::c_uint as uint8_t;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    while i_1 < hLen {
        let mut uu____1: uint8_t = FStar_UInt8_eq_mask(
            *m1Hash0.as_mut_ptr().offset(i_1 as isize),
            *m1Hash.offset(i_1 as isize),
        );
        res0 = (uu____1 as uint32_t & res0 as uint32_t) as uint8_t;
        i_1 = i_1.wrapping_add(1);
        i_1;
    }
    let mut z0: uint8_t = res0;
    return z0 as libc::c_uint == 255 as libc::c_uint;
}
#[inline]
unsafe extern "C" fn load_pkey(
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut nb: *mut uint8_t,
    mut eb: *mut uint8_t,
    mut pkey: *mut uint64_t,
) -> bool {
    let mut nbLen: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut ebLen: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut nLen: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut n: *mut uint64_t = pkey;
    let mut r2: *mut uint64_t = pkey.offset(nLen as isize);
    let mut e: *mut uint64_t = pkey.offset(nLen as isize).offset(nLen as isize);
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen, nb, n);
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
        modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint),
        modBits.wrapping_sub(1 as libc::c_uint),
        n,
        r2,
    );
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen, eb, e);
    let mut m0: uint64_t = check_modulus_u64(modBits, n);
    let mut m1: uint64_t = check_exponent_u64(eBits, e);
    let mut m: uint64_t = m0 & m1;
    return m == 0xffffffffffffffff as libc::c_ulonglong;
}
#[inline]
unsafe extern "C" fn load_skey(
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut dBits: uint32_t,
    mut nb: *mut uint8_t,
    mut eb: *mut uint8_t,
    mut db: *mut uint8_t,
    mut skey: *mut uint64_t,
) -> bool {
    let mut dbLen: uint32_t = dBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut nLen: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut eLen: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut pkeyLen: uint32_t = nLen.wrapping_add(nLen).wrapping_add(eLen);
    let mut pkey: *mut uint64_t = skey;
    let mut d: *mut uint64_t = skey.offset(pkeyLen as isize);
    let mut b: bool = load_pkey(modBits, eBits, nb, eb, pkey);
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(dbLen, db, d);
    let mut m1: uint64_t = check_exponent_u64(dBits, d);
    return b as libc::c_int != 0 && m1 == 0xffffffffffffffff as libc::c_ulonglong;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_rsapss_sign(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut dBits: uint32_t,
    mut skey: *mut uint64_t,
    mut saltLen: uint32_t,
    mut salt: *mut uint8_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
    mut sgnt: *mut uint8_t,
) -> bool {
    let mut hLen: uint32_t = hash_len(a);
    let mut b: bool = saltLen
        <= (0xffffffff as libc::c_uint)
            .wrapping_sub(hLen)
            .wrapping_sub(8 as libc::c_uint)
        && saltLen.wrapping_add(hLen).wrapping_add(2 as libc::c_uint)
            <= modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(8 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint);
    if b {
        let mut nLen: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        if nLen as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                433 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = nLen as usize;
        let mut m: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
        memset(
            m.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (nLen as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut emBits: uint32_t = modBits.wrapping_sub(1 as libc::c_uint);
        let mut emLen: uint32_t = emBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        if emLen as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                438 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = emLen as usize;
        let mut em: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            em.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (emLen as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        pss_encode(a, saltLen, salt, msgLen, msg, emBits, em.as_mut_ptr());
        Hacl_Bignum_Convert_bn_from_bytes_be_uint64(
            emLen,
            em.as_mut_ptr(),
            m.as_mut_ptr(),
        );
        let mut nLen1: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut k: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        if nLen1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                445 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = nLen1 as usize;
        let mut s: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            s.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (nLen1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        if nLen1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                448 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = nLen1 as usize;
        let mut m_: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            m_.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (nLen1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut nLen2: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut eLen: uint32_t = eBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut n: *mut uint64_t = skey;
        let mut r2: *mut uint64_t = skey.offset(nLen2 as isize);
        let mut e: *mut uint64_t = skey.offset(nLen2 as isize).offset(nLen2 as isize);
        let mut d: *mut uint64_t = skey
            .offset(nLen2 as isize)
            .offset(nLen2 as isize)
            .offset(eLen as isize);
        let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
            *n.offset(0 as libc::c_uint as isize),
        );
        Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
            modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint),
            n,
            mu,
            r2,
            m.as_mut_ptr(),
            dBits,
            d,
            s.as_mut_ptr(),
        );
        let mut mu0: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
            *n.offset(0 as libc::c_uint as isize),
        );
        Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
            modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint),
            n,
            mu0,
            r2,
            s.as_mut_ptr(),
            eBits,
            e,
            m_.as_mut_ptr(),
        );
        let mut mask: uint64_t = 0xffffffffffffffff as libc::c_ulonglong;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < nLen2 {
            let mut uu____0: uint64_t = FStar_UInt64_eq_mask(
                *m.as_mut_ptr().offset(i as isize),
                *m_.as_mut_ptr().offset(i as isize),
            );
            mask = uu____0 & mask;
            i = i.wrapping_add(1);
            i;
        }
        let mut mask1: uint64_t = mask;
        let mut eq_m: uint64_t = mask1;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0 < nLen2 {
            let mut x: uint64_t = *s.as_mut_ptr().offset(i_0 as isize);
            let mut x0: uint64_t = eq_m & x;
            let mut os: *mut uint64_t = s.as_mut_ptr();
            *os.offset(i_0 as isize) = x0;
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut eq_b: bool = eq_m == 0xffffffffffffffff as libc::c_ulonglong;
        Hacl_Bignum_Convert_bn_to_bytes_be_uint64(k, s.as_mut_ptr(), sgnt);
        let mut eq_b0: bool = eq_b;
        return eq_b0;
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_rsapss_verify(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut pkey: *mut uint64_t,
    mut saltLen: uint32_t,
    mut sgntLen: uint32_t,
    mut sgnt: *mut uint8_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
) -> bool {
    let mut hLen: uint32_t = hash_len(a);
    let mut b: bool = saltLen
        <= (0xffffffff as libc::c_uint)
            .wrapping_sub(hLen)
            .wrapping_sub(8 as libc::c_uint)
        && sgntLen
            == modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(8 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint);
    if b {
        let mut nLen: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        if nLen as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                534 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = nLen as usize;
        let mut m: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
        memset(
            m.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (nLen as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        let mut nLen1: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut k: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(8 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        if nLen1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                539 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = nLen1 as usize;
        let mut s: Vec::<uint64_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            s.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (nLen1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
        );
        Hacl_Bignum_Convert_bn_from_bytes_be_uint64(k, sgnt, s.as_mut_ptr());
        let mut nLen2: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut n: *mut uint64_t = pkey;
        let mut r2: *mut uint64_t = pkey.offset(nLen2 as isize);
        let mut e: *mut uint64_t = pkey.offset(nLen2 as isize).offset(nLen2 as isize);
        let mut acc: uint64_t = 0 as libc::c_ulonglong;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < nLen2 {
            let mut beq: uint64_t = FStar_UInt64_eq_mask(
                *s.as_mut_ptr().offset(i as isize),
                *n.offset(i as isize),
            );
            let mut blt: uint64_t = !FStar_UInt64_gte_mask(
                *s.as_mut_ptr().offset(i as isize),
                *n.offset(i as isize),
            );
            acc = beq & acc | !beq & blt;
            i = i.wrapping_add(1);
            i;
        }
        let mut mask: uint64_t = acc;
        let mut res: bool = false;
        if mask == 0xffffffffffffffff as libc::c_ulonglong {
            let mut mu: uint64_t = Hacl_Bignum_ModInvLimb_mod_inv_uint64(
                *n.offset(0 as libc::c_uint as isize),
            );
            Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
                modBits
                    .wrapping_sub(1 as libc::c_uint)
                    .wrapping_div(64 as libc::c_uint)
                    .wrapping_add(1 as libc::c_uint),
                n,
                mu,
                r2,
                s.as_mut_ptr(),
                eBits,
                e,
                m.as_mut_ptr(),
            );
            if !(modBits.wrapping_sub(1 as libc::c_uint).wrapping_rem(8 as libc::c_uint)
                == 0 as libc::c_uint)
            {
                res = 1 as libc::c_int != 0;
            } else {
                let mut i_0: uint32_t = modBits
                    .wrapping_sub(1 as libc::c_uint)
                    .wrapping_div(64 as libc::c_uint);
                let mut j: uint32_t = modBits
                    .wrapping_sub(1 as libc::c_uint)
                    .wrapping_rem(64 as libc::c_uint);
                let mut tmp: uint64_t = *m.as_mut_ptr().offset(i_0 as isize);
                let mut get_bit: uint64_t = tmp >> j & 1 as libc::c_ulonglong;
                res = get_bit == 0 as libc::c_ulonglong;
            }
        } else {
            res = 0 as libc::c_int != 0;
        }
        let mut b1: bool = res;
        let mut b10: bool = b1;
        if b10 {
            let mut emBits: uint32_t = modBits.wrapping_sub(1 as libc::c_uint);
            let mut emLen: uint32_t = emBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(8 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint);
            if emLen as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
                    590 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = emLen as usize;
            let mut em: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                em.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (emLen as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut m1: *mut uint64_t = m.as_mut_ptr();
            Hacl_Bignum_Convert_bn_to_bytes_be_uint64(emLen, m1, em.as_mut_ptr());
            let mut res0: bool = pss_verify(
                a,
                saltLen,
                msgLen,
                msg,
                emBits,
                em.as_mut_ptr(),
            );
            return res0;
        }
        return 0 as libc::c_int != 0;
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_new_rsapss_load_pkey(
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut nb: *mut uint8_t,
    mut eb: *mut uint8_t,
) -> *mut uint64_t {
    let mut ite: bool = false;
    if (1 as libc::c_uint) < modBits && (0 as libc::c_uint) < eBits {
        let mut nLen: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut eLen: uint32_t = eBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        ite = nLen <= 33554431 as libc::c_uint && eLen <= 67108863 as libc::c_uint
            && nLen.wrapping_add(nLen)
                <= (0xffffffff as libc::c_uint).wrapping_sub(eLen);
    } else {
        ite = 0 as libc::c_int != 0;
    }
    if !ite {
        return 0 as *mut uint64_t;
    }
    let mut nLen_0: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut eLen_0: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut pkeyLen: uint32_t = nLen_0.wrapping_add(nLen_0).wrapping_add(eLen_0);
    if pkeyLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            634 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut pkey: *mut uint64_t = calloc(
        pkeyLen as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    if pkey.is_null() {
        return pkey;
    }
    let mut pkey1: *mut uint64_t = pkey;
    let mut pkey2: *mut uint64_t = pkey1;
    let mut nbLen: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut ebLen: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut nLen1: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut n: *mut uint64_t = pkey2;
    let mut r2: *mut uint64_t = pkey2.offset(nLen1 as isize);
    let mut e: *mut uint64_t = pkey2.offset(nLen1 as isize).offset(nLen1 as isize);
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen, nb, n);
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
        modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint),
        modBits.wrapping_sub(1 as libc::c_uint),
        n,
        r2,
    );
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen, eb, e);
    let mut m0: uint64_t = check_modulus_u64(modBits, n);
    let mut m1: uint64_t = check_exponent_u64(eBits, e);
    let mut m: uint64_t = m0 & m1;
    let mut b: bool = m == 0xffffffffffffffff as libc::c_ulonglong;
    if b {
        return pkey2;
    }
    free(pkey2 as *mut libc::c_void);
    return 0 as *mut uint64_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_new_rsapss_load_skey(
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut dBits: uint32_t,
    mut nb: *mut uint8_t,
    mut eb: *mut uint8_t,
    mut db: *mut uint8_t,
) -> *mut uint64_t {
    let mut ite0: bool = false;
    if (1 as libc::c_uint) < modBits && (0 as libc::c_uint) < eBits {
        let mut nLen: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut eLen: uint32_t = eBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        ite0 = nLen <= 33554431 as libc::c_uint && eLen <= 67108863 as libc::c_uint
            && nLen.wrapping_add(nLen)
                <= (0xffffffff as libc::c_uint).wrapping_sub(eLen);
    } else {
        ite0 = 0 as libc::c_int != 0;
    }
    let mut ite: bool = false;
    if ite0 as libc::c_int != 0 && (0 as libc::c_uint) < dBits {
        let mut nLen_0: uint32_t = modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut eLen_0: uint32_t = eBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        let mut dLen: uint32_t = dBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint);
        ite = dLen <= 67108863 as libc::c_uint
            && (2 as libc::c_uint).wrapping_mul(nLen_0)
                <= (0xffffffff as libc::c_uint).wrapping_sub(eLen_0).wrapping_sub(dLen);
    } else {
        ite = 0 as libc::c_int != 0;
    }
    if !ite {
        return 0 as *mut uint64_t;
    }
    let mut nLen_1: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut eLen_1: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut dLen_0: uint32_t = dBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut skeyLen: uint32_t = nLen_1
        .wrapping_add(nLen_1)
        .wrapping_add(eLen_1)
        .wrapping_add(dLen_0);
    if skeyLen as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            716 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut skey: *mut uint64_t = calloc(
        skeyLen as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    if skey.is_null() {
        return skey;
    }
    let mut skey1: *mut uint64_t = skey;
    let mut skey2: *mut uint64_t = skey1;
    let mut dbLen: uint32_t = dBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut nLen1: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut eLen1: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut pkeyLen: uint32_t = nLen1.wrapping_add(nLen1).wrapping_add(eLen1);
    let mut pkey: *mut uint64_t = skey2;
    let mut d: *mut uint64_t = skey2.offset(pkeyLen as isize);
    let mut nbLen1: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut ebLen1: uint32_t = eBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(8 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut nLen2: uint32_t = modBits
        .wrapping_sub(1 as libc::c_uint)
        .wrapping_div(64 as libc::c_uint)
        .wrapping_add(1 as libc::c_uint);
    let mut n: *mut uint64_t = pkey;
    let mut r2: *mut uint64_t = pkey.offset(nLen2 as isize);
    let mut e: *mut uint64_t = pkey.offset(nLen2 as isize).offset(nLen2 as isize);
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(nbLen1, nb, n);
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
        modBits
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(64 as libc::c_uint)
            .wrapping_add(1 as libc::c_uint),
        modBits.wrapping_sub(1 as libc::c_uint),
        n,
        r2,
    );
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(ebLen1, eb, e);
    let mut m0: uint64_t = check_modulus_u64(modBits, n);
    let mut m10: uint64_t = check_exponent_u64(eBits, e);
    let mut m: uint64_t = m0 & m10;
    let mut b: bool = m == 0xffffffffffffffff as libc::c_ulonglong;
    Hacl_Bignum_Convert_bn_from_bytes_be_uint64(dbLen, db, d);
    let mut m1: uint64_t = check_exponent_u64(dBits, d);
    let mut b0: bool = b as libc::c_int != 0
        && m1 == 0xffffffffffffffff as libc::c_ulonglong;
    if b0 {
        return skey2;
    }
    free(skey2 as *mut libc::c_void);
    return 0 as *mut uint64_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_rsapss_skey_sign(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut dBits: uint32_t,
    mut nb: *mut uint8_t,
    mut eb: *mut uint8_t,
    mut db: *mut uint8_t,
    mut saltLen: uint32_t,
    mut salt: *mut uint8_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
    mut sgnt: *mut uint8_t,
) -> bool {
    if (2 as libc::c_uint)
        .wrapping_mul(
            modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint),
        )
        .wrapping_add(
            eBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
        )
        .wrapping_add(1 as libc::c_uint)
        .wrapping_add(
            dBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
        )
        .wrapping_add(1 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            792 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = (2 as libc::c_uint)
        .wrapping_mul(
            modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint),
        )
        .wrapping_add(
            eBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
        )
        .wrapping_add(1 as libc::c_uint)
        .wrapping_add(
            dBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
        )
        .wrapping_add(1 as libc::c_uint) as usize;
    let mut skey: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        skey.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((2 as libc::c_uint)
            .wrapping_mul(
                modBits
                    .wrapping_sub(1 as libc::c_uint)
                    .wrapping_div(64 as libc::c_uint)
                    .wrapping_add(1 as libc::c_uint),
            )
            .wrapping_add(
                eBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
            )
            .wrapping_add(1 as libc::c_uint)
            .wrapping_add(
                dBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
            )
            .wrapping_add(1 as libc::c_uint) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut b: bool = load_skey(modBits, eBits, dBits, nb, eb, db, skey.as_mut_ptr());
    if b {
        return Hacl_RSAPSS_rsapss_sign(
            a,
            modBits,
            eBits,
            dBits,
            skey.as_mut_ptr(),
            saltLen,
            salt,
            msgLen,
            msg,
            sgnt,
        );
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_rsapss_pkey_verify(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut modBits: uint32_t,
    mut eBits: uint32_t,
    mut nb: *mut uint8_t,
    mut eb: *mut uint8_t,
    mut saltLen: uint32_t,
    mut sgntLen: uint32_t,
    mut sgnt: *mut uint8_t,
    mut msgLen: uint32_t,
    mut msg: *mut uint8_t,
) -> bool {
    if (2 as libc::c_uint)
        .wrapping_mul(
            modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint),
        )
        .wrapping_add(
            eBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
        )
        .wrapping_add(1 as libc::c_uint) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint64_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_RSAPSS.c\0" as *const u8 as *const libc::c_char,
            850 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = (2 as libc::c_uint)
        .wrapping_mul(
            modBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(64 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint),
        )
        .wrapping_add(
            eBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
        )
        .wrapping_add(1 as libc::c_uint) as usize;
    let mut pkey: Vec::<uint64_t> = ::std::vec::from_elem(0, vla);
    memset(
        pkey.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        ((2 as libc::c_uint)
            .wrapping_mul(
                modBits
                    .wrapping_sub(1 as libc::c_uint)
                    .wrapping_div(64 as libc::c_uint)
                    .wrapping_add(1 as libc::c_uint),
            )
            .wrapping_add(
                eBits.wrapping_sub(1 as libc::c_uint).wrapping_div(64 as libc::c_uint),
            )
            .wrapping_add(1 as libc::c_uint) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut b: bool = load_pkey(modBits, eBits, nb, eb, pkey.as_mut_ptr());
    if b {
        return Hacl_RSAPSS_rsapss_verify(
            a,
            modBits,
            eBits,
            pkey.as_mut_ptr(),
            saltLen,
            sgntLen,
            sgnt,
            msgLen,
            msg,
        );
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_RSAPSS_mgf_hash(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut len: uint32_t,
    mut mgfseed: *mut uint8_t,
    mut maskLen: uint32_t,
    mut res: *mut uint8_t,
) {
    mgf_hash(a, len, mgfseed, maskLen, res);
}
