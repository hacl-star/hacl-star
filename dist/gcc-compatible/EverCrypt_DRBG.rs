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
    fn Lib_RandomBuffer_System_randombytes(buf: *mut uint8_t, len: uint32_t) -> bool;
    static mut Hacl_HMAC_DRBG_reseed_interval: uint32_t;
    static mut Hacl_HMAC_DRBG_max_output_length: uint32_t;
    static mut Hacl_HMAC_DRBG_max_personalization_string_length: uint32_t;
    static mut Hacl_HMAC_DRBG_max_additional_input_length: uint32_t;
    fn Hacl_HMAC_DRBG_min_length(a: Spec_Hash_Definitions_hash_alg) -> uint32_t;
    fn EverCrypt_HMAC_compute_sha1(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn EverCrypt_HMAC_compute_sha2_256(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn EverCrypt_HMAC_compute_sha2_384(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn EverCrypt_HMAC_compute_sha2_512(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn Lib_Memzero0_memzero0(dst: *mut libc::c_void, len: uint64_t);
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
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_HMAC_DRBG_state_s {
    pub k: *mut uint8_t,
    pub v: *mut uint8_t,
    pub reseed_counter: *mut uint32_t,
}
pub type Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct EverCrypt_DRBG_state_s_s {
    pub tag: state_s_tags,
    pub c2rust_unnamed: C2RustUnnamed,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub union C2RustUnnamed {
    pub case_SHA1_s: Hacl_HMAC_DRBG_state,
    pub case_SHA2_256_s: Hacl_HMAC_DRBG_state,
    pub case_SHA2_384_s: Hacl_HMAC_DRBG_state,
    pub case_SHA2_512_s: Hacl_HMAC_DRBG_state,
}
pub type state_s_tags = uint8_t;
pub type EverCrypt_DRBG_state_s = EverCrypt_DRBG_state_s_s;
#[no_mangle]
pub static mut EverCrypt_DRBG_reseed_interval: uint32_t = 1024 as libc::c_uint;
#[no_mangle]
pub static mut EverCrypt_DRBG_max_output_length: uint32_t = 65536 as libc::c_uint;
#[no_mangle]
pub static mut EverCrypt_DRBG_max_length: uint32_t = 65536 as libc::c_uint;
#[no_mangle]
pub static mut EverCrypt_DRBG_max_personalization_string_length: uint32_t = 65536
    as libc::c_uint;
#[no_mangle]
pub static mut EverCrypt_DRBG_max_additional_input_length: uint32_t = 65536
    as libc::c_uint;
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_min_length(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> uint32_t {
    match a as libc::c_int {
        4 => return 16 as libc::c_uint,
        1 => return 32 as libc::c_uint,
        2 => return 32 as libc::c_uint,
        3 => return 32 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                63 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_uu___is_SHA1_s(
    mut uu___: Spec_Hash_Definitions_hash_alg,
    mut projectee: EverCrypt_DRBG_state_s,
) -> bool {
    if projectee.tag as libc::c_int == 0 as libc::c_int {
        return 1 as libc::c_int != 0;
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_uu___is_SHA2_256_s(
    mut uu___: Spec_Hash_Definitions_hash_alg,
    mut projectee: EverCrypt_DRBG_state_s,
) -> bool {
    if projectee.tag as libc::c_int == 1 as libc::c_int {
        return 1 as libc::c_int != 0;
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_uu___is_SHA2_384_s(
    mut uu___: Spec_Hash_Definitions_hash_alg,
    mut projectee: EverCrypt_DRBG_state_s,
) -> bool {
    if projectee.tag as libc::c_int == 2 as libc::c_int {
        return 1 as libc::c_int != 0;
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_uu___is_SHA2_512_s(
    mut uu___: Spec_Hash_Definitions_hash_alg,
    mut projectee: EverCrypt_DRBG_state_s,
) -> bool {
    if projectee.tag as libc::c_int == 3 as libc::c_int {
        return 1 as libc::c_int != 0;
    }
    return 0 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_create_in(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> *mut EverCrypt_DRBG_state_s {
    let mut st: EverCrypt_DRBG_state_s = EverCrypt_DRBG_state_s_s {
        tag: 0,
        c2rust_unnamed: C2RustUnnamed {
            case_SHA1_s: Hacl_HMAC_DRBG_state_s {
                k: 0 as *mut uint8_t,
                v: 0 as *mut uint8_t,
                reseed_counter: 0 as *mut uint32_t,
            },
        },
    };
    match a as libc::c_int {
        4 => {
            let mut k: *mut uint8_t = calloc(
                20 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut v: *mut uint8_t = calloc(
                20 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut ctr: *mut uint32_t = malloc(
                ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
            ) as *mut uint32_t;
            *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            st = {
                let mut init = EverCrypt_DRBG_state_s_s {
                    tag: 0 as libc::c_int as state_s_tags,
                    c2rust_unnamed: C2RustUnnamed {
                        case_SHA1_s: {
                            let mut init = Hacl_HMAC_DRBG_state_s {
                                k: k,
                                v: v,
                                reseed_counter: ctr,
                            };
                            init
                        },
                    },
                };
                init
            };
        }
        1 => {
            let mut k_0: *mut uint8_t = calloc(
                32 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut v_0: *mut uint8_t = calloc(
                32 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut ctr_0: *mut uint32_t = malloc(
                ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
            ) as *mut uint32_t;
            *ctr_0.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            st = {
                let mut init = EverCrypt_DRBG_state_s_s {
                    tag: 1 as libc::c_int as state_s_tags,
                    c2rust_unnamed: C2RustUnnamed {
                        case_SHA2_256_s: {
                            let mut init = Hacl_HMAC_DRBG_state_s {
                                k: k_0,
                                v: v_0,
                                reseed_counter: ctr_0,
                            };
                            init
                        },
                    },
                };
                init
            };
        }
        2 => {
            let mut k_1: *mut uint8_t = calloc(
                48 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut v_1: *mut uint8_t = calloc(
                48 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut ctr_1: *mut uint32_t = malloc(
                ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
            ) as *mut uint32_t;
            *ctr_1.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            st = {
                let mut init = EverCrypt_DRBG_state_s_s {
                    tag: 2 as libc::c_int as state_s_tags,
                    c2rust_unnamed: C2RustUnnamed {
                        case_SHA2_384_s: {
                            let mut init = Hacl_HMAC_DRBG_state_s {
                                k: k_1,
                                v: v_1,
                                reseed_counter: ctr_1,
                            };
                            init
                        },
                    },
                };
                init
            };
        }
        3 => {
            let mut k_2: *mut uint8_t = calloc(
                64 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut v_2: *mut uint8_t = calloc(
                64 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            let mut ctr_2: *mut uint32_t = malloc(
                ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
            ) as *mut uint32_t;
            *ctr_2.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            st = {
                let mut init = EverCrypt_DRBG_state_s_s {
                    tag: 3 as libc::c_int as state_s_tags,
                    c2rust_unnamed: C2RustUnnamed {
                        case_SHA2_512_s: {
                            let mut init = Hacl_HMAC_DRBG_state_s {
                                k: k_2,
                                v: v_2,
                                reseed_counter: ctr_2,
                            };
                            init
                        },
                    },
                };
                init
            };
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                212 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    }
    let mut buf: *mut EverCrypt_DRBG_state_s = malloc(
        ::core::mem::size_of::<EverCrypt_DRBG_state_s>() as libc::c_ulong,
    ) as *mut EverCrypt_DRBG_state_s;
    *buf.offset(0 as libc::c_uint as isize) = st;
    return buf;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_create(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> *mut EverCrypt_DRBG_state_s {
    return EverCrypt_DRBG_create_in(a);
}
unsafe extern "C" fn instantiate_sha1(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut personalization_string: *mut uint8_t,
    mut personalization_string_len: uint32_t,
) -> bool {
    if personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        4 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    let mut nonce_len: uint32_t = (Hacl_HMAC_DRBG_min_length(
        4 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    ))
        .wrapping_div(2 as libc::c_uint);
    let mut min_entropy: uint32_t = entropy_input_len.wrapping_add(nonce_len);
    if min_entropy as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            252 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = min_entropy as usize;
    let mut entropy: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (min_entropy as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy.as_mut_ptr(),
        min_entropy,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input: *mut uint8_t = entropy.as_mut_ptr();
    let mut nonce: *mut uint8_t = entropy
        .as_mut_ptr()
        .offset(entropy_input_len as isize);
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            263 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        nonce as *const libc::c_void,
        (nonce_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material
            .as_mut_ptr()
            .offset(entropy_input_len as isize)
            .offset(nonce_len as isize) as *mut libc::c_void,
        personalization_string as *const libc::c_void,
        (personalization_string_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 0 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA1_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            280 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    memset(
        k as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memset(
        v as *mut libc::c_void,
        1 as libc::c_uint as libc::c_int,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    let mut input_len: uint32_t = (21 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            289 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        memcpy(
            input0.as_mut_ptr().offset(21 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha1(
        k_,
        k,
        20 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha1(v, k_, 20 as libc::c_uint, v, 20 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        let mut input_len0: uint32_t = (21 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                307 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) != 0 as libc::c_uint
        {
            memcpy(
                input.as_mut_ptr().offset(21 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha1(
            k_0,
            k,
            20 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha1(v, k_0, 20 as libc::c_uint, v, 20 as libc::c_uint);
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn instantiate_sha2_256(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut personalization_string: *mut uint8_t,
    mut personalization_string_len: uint32_t,
) -> bool {
    if personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        1 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    let mut nonce_len: uint32_t = (Hacl_HMAC_DRBG_min_length(
        1 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    ))
        .wrapping_div(2 as libc::c_uint);
    let mut min_entropy: uint32_t = entropy_input_len.wrapping_add(nonce_len);
    if min_entropy as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            340 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = min_entropy as usize;
    let mut entropy: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (min_entropy as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy.as_mut_ptr(),
        min_entropy,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input: *mut uint8_t = entropy.as_mut_ptr();
    let mut nonce: *mut uint8_t = entropy
        .as_mut_ptr()
        .offset(entropy_input_len as isize);
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            351 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        nonce as *const libc::c_void,
        (nonce_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material
            .as_mut_ptr()
            .offset(entropy_input_len as isize)
            .offset(nonce_len as isize) as *mut libc::c_void,
        personalization_string as *const libc::c_void,
        (personalization_string_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 1 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA2_256_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            368 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    memset(
        k as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memset(
        v as *mut libc::c_void,
        1 as libc::c_uint as libc::c_int,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    let mut input_len: uint32_t = (33 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            377 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        memcpy(
            input0.as_mut_ptr().offset(33 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_256(
        k_,
        k,
        32 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha2_256(v, k_, 32 as libc::c_uint, v, 32 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        let mut input_len0: uint32_t = (33 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                395 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) != 0 as libc::c_uint
        {
            memcpy(
                input.as_mut_ptr().offset(33 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_256(
            k_0,
            k,
            32 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha2_256(
            v,
            k_0,
            32 as libc::c_uint,
            v,
            32 as libc::c_uint,
        );
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn instantiate_sha2_384(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut personalization_string: *mut uint8_t,
    mut personalization_string_len: uint32_t,
) -> bool {
    if personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        2 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    let mut nonce_len: uint32_t = (Hacl_HMAC_DRBG_min_length(
        2 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    ))
        .wrapping_div(2 as libc::c_uint);
    let mut min_entropy: uint32_t = entropy_input_len.wrapping_add(nonce_len);
    if min_entropy as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            428 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = min_entropy as usize;
    let mut entropy: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (min_entropy as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy.as_mut_ptr(),
        min_entropy,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input: *mut uint8_t = entropy.as_mut_ptr();
    let mut nonce: *mut uint8_t = entropy
        .as_mut_ptr()
        .offset(entropy_input_len as isize);
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            439 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        nonce as *const libc::c_void,
        (nonce_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material
            .as_mut_ptr()
            .offset(entropy_input_len as isize)
            .offset(nonce_len as isize) as *mut libc::c_void,
        personalization_string as *const libc::c_void,
        (personalization_string_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 2 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA2_384_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            456 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    memset(
        k as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memset(
        v as *mut libc::c_void,
        1 as libc::c_uint as libc::c_int,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    let mut input_len: uint32_t = (49 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            465 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        memcpy(
            input0.as_mut_ptr().offset(49 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_384(
        k_,
        k,
        48 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha2_384(v, k_, 48 as libc::c_uint, v, 48 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        let mut input_len0: uint32_t = (49 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                483 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) != 0 as libc::c_uint
        {
            memcpy(
                input.as_mut_ptr().offset(49 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_384(
            k_0,
            k,
            48 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha2_384(
            v,
            k_0,
            48 as libc::c_uint,
            v,
            48 as libc::c_uint,
        );
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn instantiate_sha2_512(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut personalization_string: *mut uint8_t,
    mut personalization_string_len: uint32_t,
) -> bool {
    if personalization_string_len > Hacl_HMAC_DRBG_max_personalization_string_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        3 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    let mut nonce_len: uint32_t = (Hacl_HMAC_DRBG_min_length(
        3 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    ))
        .wrapping_div(2 as libc::c_uint);
    let mut min_entropy: uint32_t = entropy_input_len.wrapping_add(nonce_len);
    if min_entropy as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            516 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = min_entropy as usize;
    let mut entropy: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (min_entropy as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy.as_mut_ptr(),
        min_entropy,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input: *mut uint8_t = entropy.as_mut_ptr();
    let mut nonce: *mut uint8_t = entropy
        .as_mut_ptr()
        .offset(entropy_input_len as isize);
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            527 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        nonce as *const libc::c_void,
        (nonce_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material
            .as_mut_ptr()
            .offset(entropy_input_len as isize)
            .offset(nonce_len as isize) as *mut libc::c_void,
        personalization_string as *const libc::c_void,
        (personalization_string_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 3 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA2_512_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            544 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    memset(
        k as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memset(
        v as *mut libc::c_void,
        1 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    let mut input_len: uint32_t = (65 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(nonce_len)
        .wrapping_add(personalization_string_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            553 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        memcpy(
            input0.as_mut_ptr().offset(65 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_512(
        k_,
        k,
        64 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha2_512(v, k_, 64 as libc::c_uint, v, 64 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
        != 0 as libc::c_uint
    {
        let mut input_len0: uint32_t = (65 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                571 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len
            .wrapping_add(nonce_len)
            .wrapping_add(personalization_string_len) != 0 as libc::c_uint
        {
            memcpy(
                input.as_mut_ptr().offset(65 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_512(
            k_0,
            k,
            64 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha2_512(
            v,
            k_0,
            64 as libc::c_uint,
            v,
            64 as libc::c_uint,
        );
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn reseed_sha1(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        4 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    if entropy_input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            602 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = entropy_input_len as usize;
    let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy_input.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy_input.as_mut_ptr(),
        entropy_input_len,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(additional_input_len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            611 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input.as_mut_ptr() as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        additional_input as *const libc::c_void,
        (additional_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 0 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA1_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            625 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    let mut input_len: uint32_t = (21 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(additional_input_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            631 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        memcpy(
            input0.as_mut_ptr().offset(21 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha1(
        k_,
        k,
        20 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha1(v, k_, 20 as libc::c_uint, v, 20 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        let mut input_len0: uint32_t = (21 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(additional_input_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                649 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
            memcpy(
                input.as_mut_ptr().offset(21 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha1(
            k_0,
            k,
            20 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha1(v, k_0, 20 as libc::c_uint, v, 20 as libc::c_uint);
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn reseed_sha2_256(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        1 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    if entropy_input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            681 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = entropy_input_len as usize;
    let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy_input.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy_input.as_mut_ptr(),
        entropy_input_len,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(additional_input_len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            690 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input.as_mut_ptr() as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        additional_input as *const libc::c_void,
        (additional_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 1 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA2_256_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            704 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    let mut input_len: uint32_t = (33 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(additional_input_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            710 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        memcpy(
            input0.as_mut_ptr().offset(33 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_256(
        k_,
        k,
        32 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha2_256(v, k_, 32 as libc::c_uint, v, 32 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        let mut input_len0: uint32_t = (33 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(additional_input_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                728 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
            memcpy(
                input.as_mut_ptr().offset(33 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_256(
            k_0,
            k,
            32 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha2_256(
            v,
            k_0,
            32 as libc::c_uint,
            v,
            32 as libc::c_uint,
        );
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn reseed_sha2_384(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        2 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    if entropy_input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            760 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = entropy_input_len as usize;
    let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy_input.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy_input.as_mut_ptr(),
        entropy_input_len,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(additional_input_len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            769 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input.as_mut_ptr() as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        additional_input as *const libc::c_void,
        (additional_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 2 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA2_384_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            783 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    let mut input_len: uint32_t = (49 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(additional_input_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            789 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        memcpy(
            input0.as_mut_ptr().offset(49 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_384(
        k_,
        k,
        48 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha2_384(v, k_, 48 as libc::c_uint, v, 48 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        let mut input_len0: uint32_t = (49 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(additional_input_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                807 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
            memcpy(
                input.as_mut_ptr().offset(49 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_384(
            k_0,
            k,
            48 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha2_384(
            v,
            k_0,
            48 as libc::c_uint,
            v,
            48 as libc::c_uint,
        );
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn reseed_sha2_512(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        return 0 as libc::c_int != 0;
    }
    let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
        3 as libc::c_int as Spec_Hash_Definitions_hash_alg,
    );
    if entropy_input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            839 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = entropy_input_len as usize;
    let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
    memset(
        entropy_input.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut ok: bool = Lib_RandomBuffer_System_randombytes(
        entropy_input.as_mut_ptr(),
        entropy_input_len,
    );
    if !ok {
        return 0 as libc::c_int != 0;
    }
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    if entropy_input_len.wrapping_add(additional_input_len) as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            848 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
    let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr() as *mut libc::c_void,
        entropy_input.as_mut_ptr() as *const libc::c_void,
        (entropy_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    memcpy(
        seed_material.as_mut_ptr().offset(entropy_input_len as isize)
            as *mut libc::c_void,
        additional_input as *const libc::c_void,
        (additional_input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 3 as libc::c_int {
        scrut = st_s.c2rust_unnamed.case_SHA2_512_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            862 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = scrut.k;
    let mut v: *mut uint8_t = scrut.v;
    let mut ctr: *mut uint32_t = scrut.reseed_counter;
    let mut input_len: uint32_t = (65 as libc::c_uint)
        .wrapping_add(entropy_input_len)
        .wrapping_add(additional_input_len);
    if input_len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            868 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_1 = input_len as usize;
    let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
    memset(
        input0.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_: *mut uint8_t = input0.as_mut_ptr();
    memcpy(
        k_ as *mut libc::c_void,
        v as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        memcpy(
            input0.as_mut_ptr().offset(65 as libc::c_uint as isize) as *mut libc::c_void,
            seed_material.as_mut_ptr() as *const libc::c_void,
            (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0
        .as_mut_ptr()
        .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_512(
        k_,
        k,
        64 as libc::c_uint,
        input0.as_mut_ptr(),
        input_len,
    );
    EverCrypt_HMAC_compute_sha2_512(v, k_, 64 as libc::c_uint, v, 64 as libc::c_uint);
    memcpy(
        k as *mut libc::c_void,
        k_ as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
        let mut input_len0: uint32_t = (65 as libc::c_uint)
            .wrapping_add(entropy_input_len)
            .wrapping_add(additional_input_len);
        if input_len0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                886 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = input_len0 as usize;
        let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0: *mut uint8_t = input.as_mut_ptr();
        memcpy(
            k_0 as *mut libc::c_void,
            v as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint {
            memcpy(
                input.as_mut_ptr().offset(65 as libc::c_uint as isize)
                    as *mut libc::c_void,
                seed_material.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input
            .as_mut_ptr()
            .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_512(
            k_0,
            k,
            64 as libc::c_uint,
            input.as_mut_ptr(),
            input_len0,
        );
        EverCrypt_HMAC_compute_sha2_512(
            v,
            k_0,
            64 as libc::c_uint,
            v,
            64 as libc::c_uint,
        );
        memcpy(
            k as *mut libc::c_void,
            k_0 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn generate_sha1(
    mut output: *mut uint8_t,
    mut st: *mut EverCrypt_DRBG_state_s,
    mut n: uint32_t,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length
        || n > Hacl_HMAC_DRBG_max_output_length
    {
        return 0 as libc::c_int != 0;
    }
    let mut ok0: bool = false;
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        ok0 = 0 as libc::c_int != 0;
    } else {
        let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
            4 as libc::c_int as Spec_Hash_Definitions_hash_alg,
        );
        if entropy_input_len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                932 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = entropy_input_len as usize;
        let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
        memset(
            entropy_input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (entropy_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut ok: bool = Lib_RandomBuffer_System_randombytes(
            entropy_input.as_mut_ptr(),
            entropy_input_len,
        );
        let mut result: bool = false;
        if !ok {
            result = 0 as libc::c_int != 0;
        } else {
            let mut st_s: EverCrypt_DRBG_state_s = *st;
            if entropy_input_len.wrapping_add(additional_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    944 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
            let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
            memset(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                entropy_input.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
                k: 0 as *mut uint8_t,
                v: 0 as *mut uint8_t,
                reseed_counter: 0 as *mut uint32_t,
            };
            if st_s.tag as libc::c_int == 0 as libc::c_int {
                scrut = st_s.c2rust_unnamed.case_SHA1_s;
            } else {
                printf(
                    b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8
                        as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    960 as libc::c_int,
                    b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                        as *const libc::c_char,
                );
                exit(255 as libc::c_int);
                scrut = *(malloc(
                    ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
                ) as *mut Hacl_HMAC_DRBG_state);
            }
            let mut k: *mut uint8_t = scrut.k;
            let mut v: *mut uint8_t = scrut.v;
            let mut ctr: *mut uint32_t = scrut.reseed_counter;
            let mut input_len: uint32_t = (21 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_len);
            if input_len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    966 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = input_len as usize;
            let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                input0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_: *mut uint8_t = input0.as_mut_ptr();
            memcpy(
                k_ as *mut libc::c_void,
                v as *const libc::c_void,
                (20 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0
                .as_mut_ptr()
                .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha1(
                k_,
                k,
                20 as libc::c_uint,
                input0.as_mut_ptr(),
                input_len,
            );
            EverCrypt_HMAC_compute_sha1(
                v,
                k_,
                20 as libc::c_uint,
                v,
                20 as libc::c_uint,
            );
            memcpy(
                k as *mut libc::c_void,
                k_ as *const libc::c_void,
                (20 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                let mut input_len0: uint32_t = (21 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_len);
                if input_len0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                        984 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = input_len0 as usize;
                let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    input.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0: *mut uint8_t = input.as_mut_ptr();
                memcpy(
                    k_0 as *mut libc::c_void,
                    v as *const libc::c_void,
                    (20 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len.wrapping_add(additional_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input.as_mut_ptr().offset(21 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input
                    .as_mut_ptr()
                    .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                EverCrypt_HMAC_compute_sha1(
                    k_0,
                    k,
                    20 as libc::c_uint,
                    input.as_mut_ptr(),
                    input_len0,
                );
                EverCrypt_HMAC_compute_sha1(
                    v,
                    k_0,
                    20 as libc::c_uint,
                    v,
                    20 as libc::c_uint,
                );
                memcpy(
                    k as *mut libc::c_void,
                    k_0 as *const libc::c_void,
                    (20 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            result = 1 as libc::c_int != 0;
        }
        ok0 = result;
    }
    if !ok0 {
        return 0 as libc::c_int != 0;
    }
    let mut st_s_0: EverCrypt_DRBG_state_s = *st;
    let mut ite: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 0 as libc::c_int {
        ite = st_s_0.c2rust_unnamed.case_SHA1_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1017 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        ite = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    if *(ite.reseed_counter).offset(0 as libc::c_uint as isize)
        > Hacl_HMAC_DRBG_reseed_interval
    {
        return 0 as libc::c_int != 0;
    }
    let mut scrut_0: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 0 as libc::c_int {
        scrut_0 = st_s_0.c2rust_unnamed.case_SHA1_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1030 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut_0 = *(malloc(
            ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
        ) as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k_1: *mut uint8_t = scrut_0.k;
    let mut v_0: *mut uint8_t = scrut_0.v;
    let mut ctr_0: *mut uint32_t = scrut_0.reseed_counter;
    if additional_input_len > 0 as libc::c_uint {
        let mut input_len_0: uint32_t = (21 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len_0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1038 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = input_len_0 as usize;
        let mut input0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            input0_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k__0: *mut uint8_t = input0_0.as_mut_ptr();
        memcpy(
            k__0 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input0_0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input0_0
            .as_mut_ptr()
            .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha1(
            k__0,
            k_1,
            20 as libc::c_uint,
            input0_0.as_mut_ptr(),
            input_len_0,
        );
        EverCrypt_HMAC_compute_sha1(
            v_0,
            k__0,
            20 as libc::c_uint,
            v_0,
            20 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k__0 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            let mut input_len0_0: uint32_t = (21 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len0_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1054 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_4 = input_len0_0 as usize;
            let mut input_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
            memset(
                input_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len0_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_0_0: *mut uint8_t = input_0.as_mut_ptr();
            memcpy(
                k_0_0 as *mut libc::c_void,
                v_0 as *const libc::c_void,
                (20 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input_0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input_0
                .as_mut_ptr()
                .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha1(
                k_0_0,
                k_1,
                20 as libc::c_uint,
                input_0.as_mut_ptr(),
                input_len0_0,
            );
            EverCrypt_HMAC_compute_sha1(
                v_0,
                k_0_0,
                20 as libc::c_uint,
                v_0,
                20 as libc::c_uint,
            );
            memcpy(
                k_1 as *mut libc::c_void,
                k_0_0 as *const libc::c_void,
                (20 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
    }
    let mut output1: *mut uint8_t = output;
    let mut max: uint32_t = n.wrapping_div(20 as libc::c_uint);
    let mut out: *mut uint8_t = output1;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < max {
        EverCrypt_HMAC_compute_sha1(
            v_0,
            k_1,
            20 as libc::c_uint,
            v_0,
            20 as libc::c_uint,
        );
        memcpy(
            out.offset(i.wrapping_mul(20 as libc::c_uint) as isize) as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        i = i.wrapping_add(1);
        i;
    }
    if max.wrapping_mul(20 as libc::c_uint) < n {
        let mut block: *mut uint8_t = output1
            .offset(max.wrapping_mul(20 as libc::c_uint) as isize);
        EverCrypt_HMAC_compute_sha1(
            v_0,
            k_1,
            20 as libc::c_uint,
            v_0,
            20 as libc::c_uint,
        );
        memcpy(
            block as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (n.wrapping_sub(max.wrapping_mul(20 as libc::c_uint)) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut input_len_1: uint32_t = (21 as libc::c_uint)
        .wrapping_add(additional_input_len);
    if input_len_1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1084 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = input_len_1 as usize;
    let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        input0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len_1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k__1: *mut uint8_t = input0_1.as_mut_ptr();
    memcpy(
        k__1 as *mut libc::c_void,
        v_0 as *const libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        memcpy(
            input0_1.as_mut_ptr().offset(21 as libc::c_uint as isize)
                as *mut libc::c_void,
            additional_input as *const libc::c_void,
            (additional_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0_1
        .as_mut_ptr()
        .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha1(
        k__1,
        k_1,
        20 as libc::c_uint,
        input0_1.as_mut_ptr(),
        input_len_1,
    );
    EverCrypt_HMAC_compute_sha1(v_0, k__1, 20 as libc::c_uint, v_0, 20 as libc::c_uint);
    memcpy(
        k_1 as *mut libc::c_void,
        k__1 as *const libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        let mut input_len0_1: uint32_t = (21 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len0_1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1100 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_6 = input_len0_1 as usize;
        let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
        memset(
            input_1.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0_1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
        memcpy(
            k_0_1 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input_1.as_mut_ptr().offset(21 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input_1
            .as_mut_ptr()
            .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha1(
            k_0_1,
            k_1,
            20 as libc::c_uint,
            input_1.as_mut_ptr(),
            input_len0_1,
        );
        EverCrypt_HMAC_compute_sha1(
            v_0,
            k_0_1,
            20 as libc::c_uint,
            v_0,
            20 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k_0_1 as *const libc::c_void,
            (20 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut old_ctr: uint32_t = *ctr_0.offset(0 as libc::c_uint as isize);
    *ctr_0.offset(0 as libc::c_uint as isize) = old_ctr.wrapping_add(1 as libc::c_uint);
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn generate_sha2_256(
    mut output: *mut uint8_t,
    mut st: *mut EverCrypt_DRBG_state_s,
    mut n: uint32_t,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length
        || n > Hacl_HMAC_DRBG_max_output_length
    {
        return 0 as libc::c_int != 0;
    }
    let mut ok0: bool = false;
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        ok0 = 0 as libc::c_int != 0;
    } else {
        let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
            1 as libc::c_int as Spec_Hash_Definitions_hash_alg,
        );
        if entropy_input_len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1145 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = entropy_input_len as usize;
        let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
        memset(
            entropy_input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (entropy_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut ok: bool = Lib_RandomBuffer_System_randombytes(
            entropy_input.as_mut_ptr(),
            entropy_input_len,
        );
        let mut result: bool = false;
        if !ok {
            result = 0 as libc::c_int != 0;
        } else {
            let mut st_s: EverCrypt_DRBG_state_s = *st;
            if entropy_input_len.wrapping_add(additional_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1157 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
            let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
            memset(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                entropy_input.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
                k: 0 as *mut uint8_t,
                v: 0 as *mut uint8_t,
                reseed_counter: 0 as *mut uint32_t,
            };
            if st_s.tag as libc::c_int == 1 as libc::c_int {
                scrut = st_s.c2rust_unnamed.case_SHA2_256_s;
            } else {
                printf(
                    b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8
                        as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1173 as libc::c_int,
                    b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                        as *const libc::c_char,
                );
                exit(255 as libc::c_int);
                scrut = *(malloc(
                    ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
                ) as *mut Hacl_HMAC_DRBG_state);
            }
            let mut k: *mut uint8_t = scrut.k;
            let mut v: *mut uint8_t = scrut.v;
            let mut ctr: *mut uint32_t = scrut.reseed_counter;
            let mut input_len: uint32_t = (33 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_len);
            if input_len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1179 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = input_len as usize;
            let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                input0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_: *mut uint8_t = input0.as_mut_ptr();
            memcpy(
                k_ as *mut libc::c_void,
                v as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha2_256(
                k_,
                k,
                32 as libc::c_uint,
                input0.as_mut_ptr(),
                input_len,
            );
            EverCrypt_HMAC_compute_sha2_256(
                v,
                k_,
                32 as libc::c_uint,
                v,
                32 as libc::c_uint,
            );
            memcpy(
                k as *mut libc::c_void,
                k_ as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                let mut input_len0: uint32_t = (33 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_len);
                if input_len0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                        1197 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = input_len0 as usize;
                let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    input.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0: *mut uint8_t = input.as_mut_ptr();
                memcpy(
                    k_0 as *mut libc::c_void,
                    v as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len.wrapping_add(additional_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input.as_mut_ptr().offset(33 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input
                    .as_mut_ptr()
                    .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                EverCrypt_HMAC_compute_sha2_256(
                    k_0,
                    k,
                    32 as libc::c_uint,
                    input.as_mut_ptr(),
                    input_len0,
                );
                EverCrypt_HMAC_compute_sha2_256(
                    v,
                    k_0,
                    32 as libc::c_uint,
                    v,
                    32 as libc::c_uint,
                );
                memcpy(
                    k as *mut libc::c_void,
                    k_0 as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            result = 1 as libc::c_int != 0;
        }
        ok0 = result;
    }
    if !ok0 {
        return 0 as libc::c_int != 0;
    }
    let mut st_s_0: EverCrypt_DRBG_state_s = *st;
    let mut ite: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 1 as libc::c_int {
        ite = st_s_0.c2rust_unnamed.case_SHA2_256_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1230 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        ite = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    if *(ite.reseed_counter).offset(0 as libc::c_uint as isize)
        > Hacl_HMAC_DRBG_reseed_interval
    {
        return 0 as libc::c_int != 0;
    }
    let mut scrut_0: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 1 as libc::c_int {
        scrut_0 = st_s_0.c2rust_unnamed.case_SHA2_256_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1243 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut_0 = *(malloc(
            ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
        ) as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k_1: *mut uint8_t = scrut_0.k;
    let mut v_0: *mut uint8_t = scrut_0.v;
    let mut ctr_0: *mut uint32_t = scrut_0.reseed_counter;
    if additional_input_len > 0 as libc::c_uint {
        let mut input_len_0: uint32_t = (33 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len_0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1251 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = input_len_0 as usize;
        let mut input0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            input0_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k__0: *mut uint8_t = input0_0.as_mut_ptr();
        memcpy(
            k__0 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input0_0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input0_0
            .as_mut_ptr()
            .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_256(
            k__0,
            k_1,
            32 as libc::c_uint,
            input0_0.as_mut_ptr(),
            input_len_0,
        );
        EverCrypt_HMAC_compute_sha2_256(
            v_0,
            k__0,
            32 as libc::c_uint,
            v_0,
            32 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k__0 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            let mut input_len0_0: uint32_t = (33 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len0_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1267 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_4 = input_len0_0 as usize;
            let mut input_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
            memset(
                input_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len0_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_0_0: *mut uint8_t = input_0.as_mut_ptr();
            memcpy(
                k_0_0 as *mut libc::c_void,
                v_0 as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input_0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input_0
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha2_256(
                k_0_0,
                k_1,
                32 as libc::c_uint,
                input_0.as_mut_ptr(),
                input_len0_0,
            );
            EverCrypt_HMAC_compute_sha2_256(
                v_0,
                k_0_0,
                32 as libc::c_uint,
                v_0,
                32 as libc::c_uint,
            );
            memcpy(
                k_1 as *mut libc::c_void,
                k_0_0 as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
    }
    let mut output1: *mut uint8_t = output;
    let mut max: uint32_t = n.wrapping_div(32 as libc::c_uint);
    let mut out: *mut uint8_t = output1;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < max {
        EverCrypt_HMAC_compute_sha2_256(
            v_0,
            k_1,
            32 as libc::c_uint,
            v_0,
            32 as libc::c_uint,
        );
        memcpy(
            out.offset(i.wrapping_mul(32 as libc::c_uint) as isize) as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        i = i.wrapping_add(1);
        i;
    }
    if max.wrapping_mul(32 as libc::c_uint) < n {
        let mut block: *mut uint8_t = output1
            .offset(max.wrapping_mul(32 as libc::c_uint) as isize);
        EverCrypt_HMAC_compute_sha2_256(
            v_0,
            k_1,
            32 as libc::c_uint,
            v_0,
            32 as libc::c_uint,
        );
        memcpy(
            block as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (n.wrapping_sub(max.wrapping_mul(32 as libc::c_uint)) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut input_len_1: uint32_t = (33 as libc::c_uint)
        .wrapping_add(additional_input_len);
    if input_len_1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1297 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = input_len_1 as usize;
    let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        input0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len_1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k__1: *mut uint8_t = input0_1.as_mut_ptr();
    memcpy(
        k__1 as *mut libc::c_void,
        v_0 as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        memcpy(
            input0_1.as_mut_ptr().offset(33 as libc::c_uint as isize)
                as *mut libc::c_void,
            additional_input as *const libc::c_void,
            (additional_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0_1
        .as_mut_ptr()
        .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_256(
        k__1,
        k_1,
        32 as libc::c_uint,
        input0_1.as_mut_ptr(),
        input_len_1,
    );
    EverCrypt_HMAC_compute_sha2_256(
        v_0,
        k__1,
        32 as libc::c_uint,
        v_0,
        32 as libc::c_uint,
    );
    memcpy(
        k_1 as *mut libc::c_void,
        k__1 as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        let mut input_len0_1: uint32_t = (33 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len0_1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1313 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_6 = input_len0_1 as usize;
        let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
        memset(
            input_1.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0_1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
        memcpy(
            k_0_1 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input_1.as_mut_ptr().offset(33 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input_1
            .as_mut_ptr()
            .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_256(
            k_0_1,
            k_1,
            32 as libc::c_uint,
            input_1.as_mut_ptr(),
            input_len0_1,
        );
        EverCrypt_HMAC_compute_sha2_256(
            v_0,
            k_0_1,
            32 as libc::c_uint,
            v_0,
            32 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k_0_1 as *const libc::c_void,
            (32 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut old_ctr: uint32_t = *ctr_0.offset(0 as libc::c_uint as isize);
    *ctr_0.offset(0 as libc::c_uint as isize) = old_ctr.wrapping_add(1 as libc::c_uint);
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn generate_sha2_384(
    mut output: *mut uint8_t,
    mut st: *mut EverCrypt_DRBG_state_s,
    mut n: uint32_t,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length
        || n > Hacl_HMAC_DRBG_max_output_length
    {
        return 0 as libc::c_int != 0;
    }
    let mut ok0: bool = false;
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        ok0 = 0 as libc::c_int != 0;
    } else {
        let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
            2 as libc::c_int as Spec_Hash_Definitions_hash_alg,
        );
        if entropy_input_len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1358 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = entropy_input_len as usize;
        let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
        memset(
            entropy_input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (entropy_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut ok: bool = Lib_RandomBuffer_System_randombytes(
            entropy_input.as_mut_ptr(),
            entropy_input_len,
        );
        let mut result: bool = false;
        if !ok {
            result = 0 as libc::c_int != 0;
        } else {
            let mut st_s: EverCrypt_DRBG_state_s = *st;
            if entropy_input_len.wrapping_add(additional_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1370 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
            let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
            memset(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                entropy_input.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
                k: 0 as *mut uint8_t,
                v: 0 as *mut uint8_t,
                reseed_counter: 0 as *mut uint32_t,
            };
            if st_s.tag as libc::c_int == 2 as libc::c_int {
                scrut = st_s.c2rust_unnamed.case_SHA2_384_s;
            } else {
                printf(
                    b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8
                        as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1386 as libc::c_int,
                    b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                        as *const libc::c_char,
                );
                exit(255 as libc::c_int);
                scrut = *(malloc(
                    ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
                ) as *mut Hacl_HMAC_DRBG_state);
            }
            let mut k: *mut uint8_t = scrut.k;
            let mut v: *mut uint8_t = scrut.v;
            let mut ctr: *mut uint32_t = scrut.reseed_counter;
            let mut input_len: uint32_t = (49 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_len);
            if input_len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1392 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = input_len as usize;
            let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                input0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_: *mut uint8_t = input0.as_mut_ptr();
            memcpy(
                k_ as *mut libc::c_void,
                v as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0.as_mut_ptr().offset(49 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0
                .as_mut_ptr()
                .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha2_384(
                k_,
                k,
                48 as libc::c_uint,
                input0.as_mut_ptr(),
                input_len,
            );
            EverCrypt_HMAC_compute_sha2_384(
                v,
                k_,
                48 as libc::c_uint,
                v,
                48 as libc::c_uint,
            );
            memcpy(
                k as *mut libc::c_void,
                k_ as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                let mut input_len0: uint32_t = (49 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_len);
                if input_len0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                        1410 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = input_len0 as usize;
                let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    input.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0: *mut uint8_t = input.as_mut_ptr();
                memcpy(
                    k_0 as *mut libc::c_void,
                    v as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len.wrapping_add(additional_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input.as_mut_ptr().offset(49 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input
                    .as_mut_ptr()
                    .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                EverCrypt_HMAC_compute_sha2_384(
                    k_0,
                    k,
                    48 as libc::c_uint,
                    input.as_mut_ptr(),
                    input_len0,
                );
                EverCrypt_HMAC_compute_sha2_384(
                    v,
                    k_0,
                    48 as libc::c_uint,
                    v,
                    48 as libc::c_uint,
                );
                memcpy(
                    k as *mut libc::c_void,
                    k_0 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            result = 1 as libc::c_int != 0;
        }
        ok0 = result;
    }
    if !ok0 {
        return 0 as libc::c_int != 0;
    }
    let mut st_s_0: EverCrypt_DRBG_state_s = *st;
    let mut ite: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 2 as libc::c_int {
        ite = st_s_0.c2rust_unnamed.case_SHA2_384_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1443 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        ite = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    if *(ite.reseed_counter).offset(0 as libc::c_uint as isize)
        > Hacl_HMAC_DRBG_reseed_interval
    {
        return 0 as libc::c_int != 0;
    }
    let mut scrut_0: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 2 as libc::c_int {
        scrut_0 = st_s_0.c2rust_unnamed.case_SHA2_384_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1456 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut_0 = *(malloc(
            ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
        ) as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k_1: *mut uint8_t = scrut_0.k;
    let mut v_0: *mut uint8_t = scrut_0.v;
    let mut ctr_0: *mut uint32_t = scrut_0.reseed_counter;
    if additional_input_len > 0 as libc::c_uint {
        let mut input_len_0: uint32_t = (49 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len_0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1464 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = input_len_0 as usize;
        let mut input0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            input0_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k__0: *mut uint8_t = input0_0.as_mut_ptr();
        memcpy(
            k__0 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input0_0.as_mut_ptr().offset(49 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input0_0
            .as_mut_ptr()
            .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_384(
            k__0,
            k_1,
            48 as libc::c_uint,
            input0_0.as_mut_ptr(),
            input_len_0,
        );
        EverCrypt_HMAC_compute_sha2_384(
            v_0,
            k__0,
            48 as libc::c_uint,
            v_0,
            48 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k__0 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            let mut input_len0_0: uint32_t = (49 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len0_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1480 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_4 = input_len0_0 as usize;
            let mut input_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
            memset(
                input_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len0_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_0_0: *mut uint8_t = input_0.as_mut_ptr();
            memcpy(
                k_0_0 as *mut libc::c_void,
                v_0 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input_0.as_mut_ptr().offset(49 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input_0
                .as_mut_ptr()
                .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha2_384(
                k_0_0,
                k_1,
                48 as libc::c_uint,
                input_0.as_mut_ptr(),
                input_len0_0,
            );
            EverCrypt_HMAC_compute_sha2_384(
                v_0,
                k_0_0,
                48 as libc::c_uint,
                v_0,
                48 as libc::c_uint,
            );
            memcpy(
                k_1 as *mut libc::c_void,
                k_0_0 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
    }
    let mut output1: *mut uint8_t = output;
    let mut max: uint32_t = n.wrapping_div(48 as libc::c_uint);
    let mut out: *mut uint8_t = output1;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < max {
        EverCrypt_HMAC_compute_sha2_384(
            v_0,
            k_1,
            48 as libc::c_uint,
            v_0,
            48 as libc::c_uint,
        );
        memcpy(
            out.offset(i.wrapping_mul(48 as libc::c_uint) as isize) as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        i = i.wrapping_add(1);
        i;
    }
    if max.wrapping_mul(48 as libc::c_uint) < n {
        let mut block: *mut uint8_t = output1
            .offset(max.wrapping_mul(48 as libc::c_uint) as isize);
        EverCrypt_HMAC_compute_sha2_384(
            v_0,
            k_1,
            48 as libc::c_uint,
            v_0,
            48 as libc::c_uint,
        );
        memcpy(
            block as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (n.wrapping_sub(max.wrapping_mul(48 as libc::c_uint)) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut input_len_1: uint32_t = (49 as libc::c_uint)
        .wrapping_add(additional_input_len);
    if input_len_1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1510 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = input_len_1 as usize;
    let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        input0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len_1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k__1: *mut uint8_t = input0_1.as_mut_ptr();
    memcpy(
        k__1 as *mut libc::c_void,
        v_0 as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        memcpy(
            input0_1.as_mut_ptr().offset(49 as libc::c_uint as isize)
                as *mut libc::c_void,
            additional_input as *const libc::c_void,
            (additional_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0_1
        .as_mut_ptr()
        .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_384(
        k__1,
        k_1,
        48 as libc::c_uint,
        input0_1.as_mut_ptr(),
        input_len_1,
    );
    EverCrypt_HMAC_compute_sha2_384(
        v_0,
        k__1,
        48 as libc::c_uint,
        v_0,
        48 as libc::c_uint,
    );
    memcpy(
        k_1 as *mut libc::c_void,
        k__1 as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        let mut input_len0_1: uint32_t = (49 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len0_1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1526 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_6 = input_len0_1 as usize;
        let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
        memset(
            input_1.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0_1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
        memcpy(
            k_0_1 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input_1.as_mut_ptr().offset(49 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input_1
            .as_mut_ptr()
            .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_384(
            k_0_1,
            k_1,
            48 as libc::c_uint,
            input_1.as_mut_ptr(),
            input_len0_1,
        );
        EverCrypt_HMAC_compute_sha2_384(
            v_0,
            k_0_1,
            48 as libc::c_uint,
            v_0,
            48 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k_0_1 as *const libc::c_void,
            (48 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut old_ctr: uint32_t = *ctr_0.offset(0 as libc::c_uint as isize);
    *ctr_0.offset(0 as libc::c_uint as isize) = old_ctr.wrapping_add(1 as libc::c_uint);
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn generate_sha2_512(
    mut output: *mut uint8_t,
    mut st: *mut EverCrypt_DRBG_state_s,
    mut n: uint32_t,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length
        || n > Hacl_HMAC_DRBG_max_output_length
    {
        return 0 as libc::c_int != 0;
    }
    let mut ok0: bool = false;
    if additional_input_len > Hacl_HMAC_DRBG_max_additional_input_length {
        ok0 = 0 as libc::c_int != 0;
    } else {
        let mut entropy_input_len: uint32_t = Hacl_HMAC_DRBG_min_length(
            3 as libc::c_int as Spec_Hash_Definitions_hash_alg,
        );
        if entropy_input_len as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1571 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla = entropy_input_len as usize;
        let mut entropy_input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
        memset(
            entropy_input.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (entropy_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut ok: bool = Lib_RandomBuffer_System_randombytes(
            entropy_input.as_mut_ptr(),
            entropy_input_len,
        );
        let mut result: bool = false;
        if !ok {
            result = 0 as libc::c_int != 0;
        } else {
            let mut st_s: EverCrypt_DRBG_state_s = *st;
            if entropy_input_len.wrapping_add(additional_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1583 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = entropy_input_len.wrapping_add(additional_input_len) as usize;
            let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
            memset(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                entropy_input.as_mut_ptr() as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut scrut: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
                k: 0 as *mut uint8_t,
                v: 0 as *mut uint8_t,
                reseed_counter: 0 as *mut uint32_t,
            };
            if st_s.tag as libc::c_int == 3 as libc::c_int {
                scrut = st_s.c2rust_unnamed.case_SHA2_512_s;
            } else {
                printf(
                    b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8
                        as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1599 as libc::c_int,
                    b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                        as *const libc::c_char,
                );
                exit(255 as libc::c_int);
                scrut = *(malloc(
                    ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
                ) as *mut Hacl_HMAC_DRBG_state);
            }
            let mut k: *mut uint8_t = scrut.k;
            let mut v: *mut uint8_t = scrut.v;
            let mut ctr: *mut uint32_t = scrut.reseed_counter;
            let mut input_len: uint32_t = (65 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_len);
            if input_len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1605 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = input_len as usize;
            let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                input0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_: *mut uint8_t = input0.as_mut_ptr();
            memcpy(
                k_ as *mut libc::c_void,
                v as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0.as_mut_ptr().offset(65 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0
                .as_mut_ptr()
                .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha2_512(
                k_,
                k,
                64 as libc::c_uint,
                input0.as_mut_ptr(),
                input_len,
            );
            EverCrypt_HMAC_compute_sha2_512(
                v,
                k_,
                64 as libc::c_uint,
                v,
                64 as libc::c_uint,
            );
            memcpy(
                k as *mut libc::c_void,
                k_ as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_len) != 0 as libc::c_uint
            {
                let mut input_len0: uint32_t = (65 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_len);
                if input_len0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                        1623 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = input_len0 as usize;
                let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    input.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0: *mut uint8_t = input.as_mut_ptr();
                memcpy(
                    k_0 as *mut libc::c_void,
                    v as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len.wrapping_add(additional_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input.as_mut_ptr().offset(65 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input
                    .as_mut_ptr()
                    .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                EverCrypt_HMAC_compute_sha2_512(
                    k_0,
                    k,
                    64 as libc::c_uint,
                    input.as_mut_ptr(),
                    input_len0,
                );
                EverCrypt_HMAC_compute_sha2_512(
                    v,
                    k_0,
                    64 as libc::c_uint,
                    v,
                    64 as libc::c_uint,
                );
                memcpy(
                    k as *mut libc::c_void,
                    k_0 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            result = 1 as libc::c_int != 0;
        }
        ok0 = result;
    }
    if !ok0 {
        return 0 as libc::c_int != 0;
    }
    let mut st_s_0: EverCrypt_DRBG_state_s = *st;
    let mut ite: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 3 as libc::c_int {
        ite = st_s_0.c2rust_unnamed.case_SHA2_512_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1656 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        ite = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    if *(ite.reseed_counter).offset(0 as libc::c_uint as isize)
        > Hacl_HMAC_DRBG_reseed_interval
    {
        return 0 as libc::c_int != 0;
    }
    let mut scrut_0: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s_0.tag as libc::c_int == 3 as libc::c_int {
        scrut_0 = st_s_0.c2rust_unnamed.case_SHA2_512_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1669 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        scrut_0 = *(malloc(
            ::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong,
        ) as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k_1: *mut uint8_t = scrut_0.k;
    let mut v_0: *mut uint8_t = scrut_0.v;
    let mut ctr_0: *mut uint32_t = scrut_0.reseed_counter;
    if additional_input_len > 0 as libc::c_uint {
        let mut input_len_0: uint32_t = (65 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len_0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1677 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = input_len_0 as usize;
        let mut input0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            input0_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k__0: *mut uint8_t = input0_0.as_mut_ptr();
        memcpy(
            k__0 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input0_0.as_mut_ptr().offset(65 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input0_0
            .as_mut_ptr()
            .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_512(
            k__0,
            k_1,
            64 as libc::c_uint,
            input0_0.as_mut_ptr(),
            input_len_0,
        );
        EverCrypt_HMAC_compute_sha2_512(
            v_0,
            k__0,
            64 as libc::c_uint,
            v_0,
            64 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k__0 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            let mut input_len0_0: uint32_t = (65 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len0_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1693 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_4 = input_len0_0 as usize;
            let mut input_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
            memset(
                input_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len0_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_0_0: *mut uint8_t = input_0.as_mut_ptr();
            memcpy(
                k_0_0 as *mut libc::c_void,
                v_0 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input_0.as_mut_ptr().offset(65 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input_0
                .as_mut_ptr()
                .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
            EverCrypt_HMAC_compute_sha2_512(
                k_0_0,
                k_1,
                64 as libc::c_uint,
                input_0.as_mut_ptr(),
                input_len0_0,
            );
            EverCrypt_HMAC_compute_sha2_512(
                v_0,
                k_0_0,
                64 as libc::c_uint,
                v_0,
                64 as libc::c_uint,
            );
            memcpy(
                k_1 as *mut libc::c_void,
                k_0_0 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
    }
    let mut output1: *mut uint8_t = output;
    let mut max: uint32_t = n.wrapping_div(64 as libc::c_uint);
    let mut out: *mut uint8_t = output1;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < max {
        EverCrypt_HMAC_compute_sha2_512(
            v_0,
            k_1,
            64 as libc::c_uint,
            v_0,
            64 as libc::c_uint,
        );
        memcpy(
            out.offset(i.wrapping_mul(64 as libc::c_uint) as isize) as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        i = i.wrapping_add(1);
        i;
    }
    if max.wrapping_mul(64 as libc::c_uint) < n {
        let mut block: *mut uint8_t = output1
            .offset(max.wrapping_mul(64 as libc::c_uint) as isize);
        EverCrypt_HMAC_compute_sha2_512(
            v_0,
            k_1,
            64 as libc::c_uint,
            v_0,
            64 as libc::c_uint,
        );
        memcpy(
            block as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (n.wrapping_sub(max.wrapping_mul(64 as libc::c_uint)) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut input_len_1: uint32_t = (65 as libc::c_uint)
        .wrapping_add(additional_input_len);
    if input_len_1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1723 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_5 = input_len_1 as usize;
    let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
    memset(
        input0_1.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (input_len_1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k__1: *mut uint8_t = input0_1.as_mut_ptr();
    memcpy(
        k__1 as *mut libc::c_void,
        v_0 as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        memcpy(
            input0_1.as_mut_ptr().offset(65 as libc::c_uint as isize)
                as *mut libc::c_void,
            additional_input as *const libc::c_void,
            (additional_input_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    *input0_1
        .as_mut_ptr()
        .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
    EverCrypt_HMAC_compute_sha2_512(
        k__1,
        k_1,
        64 as libc::c_uint,
        input0_1.as_mut_ptr(),
        input_len_1,
    );
    EverCrypt_HMAC_compute_sha2_512(
        v_0,
        k__1,
        64 as libc::c_uint,
        v_0,
        64 as libc::c_uint,
    );
    memcpy(
        k_1 as *mut libc::c_void,
        k__1 as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if additional_input_len != 0 as libc::c_uint {
        let mut input_len0_1: uint32_t = (65 as libc::c_uint)
            .wrapping_add(additional_input_len);
        if input_len0_1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
                1739 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_6 = input_len0_1 as usize;
        let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
        memset(
            input_1.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (input_len0_1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
        memcpy(
            k_0_1 as *mut libc::c_void,
            v_0 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        if additional_input_len != 0 as libc::c_uint {
            memcpy(
                input_1.as_mut_ptr().offset(65 as libc::c_uint as isize)
                    as *mut libc::c_void,
                additional_input as *const libc::c_void,
                (additional_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
        }
        *input_1
            .as_mut_ptr()
            .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
        EverCrypt_HMAC_compute_sha2_512(
            k_0_1,
            k_1,
            64 as libc::c_uint,
            input_1.as_mut_ptr(),
            input_len0_1,
        );
        EverCrypt_HMAC_compute_sha2_512(
            v_0,
            k_0_1,
            64 as libc::c_uint,
            v_0,
            64 as libc::c_uint,
        );
        memcpy(
            k_1 as *mut libc::c_void,
            k_0_1 as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut old_ctr: uint32_t = *ctr_0.offset(0 as libc::c_uint as isize);
    *ctr_0.offset(0 as libc::c_uint as isize) = old_ctr.wrapping_add(1 as libc::c_uint);
    return 1 as libc::c_int != 0;
}
unsafe extern "C" fn uninstantiate_sha1(mut st: *mut EverCrypt_DRBG_state_s) {
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    let mut s: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 0 as libc::c_int {
        s = st_s.c2rust_unnamed.case_SHA1_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1768 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        s = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = s.k;
    let mut v: *mut uint8_t = s.v;
    let mut ctr: *mut uint32_t = s.reseed_counter;
    Lib_Memzero0_memzero0(
        k as *mut libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    Lib_Memzero0_memzero0(
        v as *mut libc::c_void,
        (20 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    *ctr.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint;
    free(k as *mut libc::c_void);
    free(v as *mut libc::c_void);
    free(ctr as *mut libc::c_void);
    free(st as *mut libc::c_void);
}
unsafe extern "C" fn uninstantiate_sha2_256(mut st: *mut EverCrypt_DRBG_state_s) {
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    let mut s: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 1 as libc::c_int {
        s = st_s.c2rust_unnamed.case_SHA2_256_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1792 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        s = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = s.k;
    let mut v: *mut uint8_t = s.v;
    let mut ctr: *mut uint32_t = s.reseed_counter;
    Lib_Memzero0_memzero0(
        k as *mut libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    Lib_Memzero0_memzero0(
        v as *mut libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    *ctr.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint;
    free(k as *mut libc::c_void);
    free(v as *mut libc::c_void);
    free(ctr as *mut libc::c_void);
    free(st as *mut libc::c_void);
}
unsafe extern "C" fn uninstantiate_sha2_384(mut st: *mut EverCrypt_DRBG_state_s) {
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    let mut s: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 2 as libc::c_int {
        s = st_s.c2rust_unnamed.case_SHA2_384_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1816 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        s = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = s.k;
    let mut v: *mut uint8_t = s.v;
    let mut ctr: *mut uint32_t = s.reseed_counter;
    Lib_Memzero0_memzero0(
        k as *mut libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    Lib_Memzero0_memzero0(
        v as *mut libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    *ctr.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint;
    free(k as *mut libc::c_void);
    free(v as *mut libc::c_void);
    free(ctr as *mut libc::c_void);
    free(st as *mut libc::c_void);
}
unsafe extern "C" fn uninstantiate_sha2_512(mut st: *mut EverCrypt_DRBG_state_s) {
    let mut st_s: EverCrypt_DRBG_state_s = *st;
    let mut s: Hacl_HMAC_DRBG_state = Hacl_HMAC_DRBG_state_s {
        k: 0 as *mut uint8_t,
        v: 0 as *mut uint8_t,
        reseed_counter: 0 as *mut uint32_t,
    };
    if st_s.tag as libc::c_int == 3 as libc::c_int {
        s = st_s.c2rust_unnamed.case_SHA2_512_s;
    } else {
        printf(
            b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
            b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
            1840 as libc::c_int,
            b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
                as *const libc::c_char,
        );
        exit(255 as libc::c_int);
        s = *(malloc(::core::mem::size_of::<Hacl_HMAC_DRBG_state>() as libc::c_ulong)
            as *mut Hacl_HMAC_DRBG_state);
    }
    let mut k: *mut uint8_t = s.k;
    let mut v: *mut uint8_t = s.v;
    let mut ctr: *mut uint32_t = s.reseed_counter;
    Lib_Memzero0_memzero0(
        k as *mut libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    Lib_Memzero0_memzero0(
        v as *mut libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
    *ctr.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint;
    free(k as *mut libc::c_void);
    free(v as *mut libc::c_void);
    free(ctr as *mut libc::c_void);
    free(st as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_instantiate(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut personalization_string: *mut uint8_t,
    mut personalization_string_len: uint32_t,
) -> bool {
    let mut scrut: EverCrypt_DRBG_state_s = *st;
    if scrut.tag as libc::c_int == 0 as libc::c_int {
        return instantiate_sha1(st, personalization_string, personalization_string_len);
    }
    if scrut.tag as libc::c_int == 1 as libc::c_int {
        return instantiate_sha2_256(
            st,
            personalization_string,
            personalization_string_len,
        );
    }
    if scrut.tag as libc::c_int == 2 as libc::c_int {
        return instantiate_sha2_384(
            st,
            personalization_string,
            personalization_string_len,
        );
    }
    if scrut.tag as libc::c_int == 3 as libc::c_int {
        return instantiate_sha2_512(
            st,
            personalization_string,
            personalization_string_len,
        );
    }
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
        1889 as libc::c_int,
        b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_reseed(
    mut st: *mut EverCrypt_DRBG_state_s,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    let mut scrut: EverCrypt_DRBG_state_s = *st;
    if scrut.tag as libc::c_int == 0 as libc::c_int {
        return reseed_sha1(st, additional_input, additional_input_len);
    }
    if scrut.tag as libc::c_int == 1 as libc::c_int {
        return reseed_sha2_256(st, additional_input, additional_input_len);
    }
    if scrut.tag as libc::c_int == 2 as libc::c_int {
        return reseed_sha2_384(st, additional_input, additional_input_len);
    }
    if scrut.tag as libc::c_int == 3 as libc::c_int {
        return reseed_sha2_512(st, additional_input, additional_input_len);
    }
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
        1929 as libc::c_int,
        b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_generate(
    mut output: *mut uint8_t,
    mut st: *mut EverCrypt_DRBG_state_s,
    mut n: uint32_t,
    mut additional_input: *mut uint8_t,
    mut additional_input_len: uint32_t,
) -> bool {
    let mut scrut: EverCrypt_DRBG_state_s = *st;
    if scrut.tag as libc::c_int == 0 as libc::c_int {
        return generate_sha1(output, st, n, additional_input, additional_input_len);
    }
    if scrut.tag as libc::c_int == 1 as libc::c_int {
        return generate_sha2_256(output, st, n, additional_input, additional_input_len);
    }
    if scrut.tag as libc::c_int == 2 as libc::c_int {
        return generate_sha2_384(output, st, n, additional_input, additional_input_len);
    }
    if scrut.tag as libc::c_int == 3 as libc::c_int {
        return generate_sha2_512(output, st, n, additional_input, additional_input_len);
    }
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
        1973 as libc::c_int,
        b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_DRBG_uninstantiate(
    mut st: *mut EverCrypt_DRBG_state_s,
) {
    let mut scrut: EverCrypt_DRBG_state_s = *st;
    if scrut.tag as libc::c_int == 0 as libc::c_int {
        uninstantiate_sha1(st);
        return;
    }
    if scrut.tag as libc::c_int == 1 as libc::c_int {
        uninstantiate_sha2_256(st);
        return;
    }
    if scrut.tag as libc::c_int == 2 as libc::c_int {
        uninstantiate_sha2_384(st);
        return;
    }
    if scrut.tag as libc::c_int == 3 as libc::c_int {
        uninstantiate_sha2_512(st);
        return;
    }
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_DRBG.c\0" as *const u8 as *const libc::c_char,
        2008 as libc::c_int,
        b"unreachable (pattern matches are exhaustive in F*)\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
