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
    fn Hacl_HMAC_compute_sha1(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn Hacl_HMAC_compute_sha2_256(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn Hacl_HMAC_compute_sha2_384(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
    fn Hacl_HMAC_compute_sha2_512(
        dst: *mut uint8_t,
        key: *mut uint8_t,
        key_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
    );
}
pub type __int64_t = libc::c_longlong;
pub type __darwin_size_t = libc::c_ulong;
pub type __darwin_off_t = __int64_t;
pub type size_t = __darwin_size_t;
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
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
#[no_mangle]
pub static mut Hacl_HMAC_DRBG_reseed_interval: uint32_t = 1024 as libc::c_uint;
#[no_mangle]
pub static mut Hacl_HMAC_DRBG_max_output_length: uint32_t = 65536 as libc::c_uint;
#[no_mangle]
pub static mut Hacl_HMAC_DRBG_max_length: uint32_t = 65536 as libc::c_uint;
#[no_mangle]
pub static mut Hacl_HMAC_DRBG_max_personalization_string_length: uint32_t = 65536
    as libc::c_uint;
#[no_mangle]
pub static mut Hacl_HMAC_DRBG_max_additional_input_length: uint32_t = 65536
    as libc::c_uint;
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_min_length(
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
                b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                65 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_uu___is_State(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut projectee: Hacl_HMAC_DRBG_state,
) -> bool {
    return 1 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_create_in(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> Hacl_HMAC_DRBG_state {
    let mut k: *mut uint8_t = 0 as *mut uint8_t;
    match a as libc::c_int {
        4 => {
            let mut buf: *mut uint8_t = calloc(
                20 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            k = buf;
        }
        1 => {
            let mut buf_0: *mut uint8_t = calloc(
                32 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            k = buf_0;
        }
        2 => {
            let mut buf_1: *mut uint8_t = calloc(
                48 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            k = buf_1;
        }
        3 => {
            let mut buf_2: *mut uint8_t = calloc(
                64 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            k = buf_2;
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                119 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    }
    let mut v: *mut uint8_t = 0 as *mut uint8_t;
    match a as libc::c_int {
        4 => {
            let mut buf_3: *mut uint8_t = calloc(
                20 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            v = buf_3;
        }
        1 => {
            let mut buf_4: *mut uint8_t = calloc(
                32 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            v = buf_4;
        }
        2 => {
            let mut buf_5: *mut uint8_t = calloc(
                48 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            v = buf_5;
        }
        3 => {
            let mut buf_6: *mut uint8_t = calloc(
                64 as libc::c_uint as libc::c_ulong,
                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
            ) as *mut uint8_t;
            v = buf_6;
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                152 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    }
    let mut ctr: *mut uint32_t = malloc(
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    *ctr.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
    return {
        let mut init = Hacl_HMAC_DRBG_state_s {
            k: k,
            v: v,
            reseed_counter: ctr,
        };
        init
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_instantiate(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut st: Hacl_HMAC_DRBG_state,
    mut entropy_input_len: uint32_t,
    mut entropy_input: *mut uint8_t,
    mut nonce_len: uint32_t,
    mut nonce: *mut uint8_t,
    mut personalization_string_len: uint32_t,
    mut personalization_string: *mut uint8_t,
) {
    match a as libc::c_int {
        4 => {
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    190 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla = entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as usize;
            let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
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
            let mut k: *mut uint8_t = st.k;
            let mut v: *mut uint8_t = st.v;
            let mut ctr: *mut uint32_t = st.reseed_counter;
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
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    207 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = input_len as usize;
            let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
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
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                        as *mut libc::c_void,
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
            Hacl_HMAC_compute_sha1(
                k_,
                k,
                20 as libc::c_uint,
                input0.as_mut_ptr(),
                input_len,
            );
            Hacl_HMAC_compute_sha1(v, k_, 20 as libc::c_uint, v, 20 as libc::c_uint);
            memcpy(
                k as *mut libc::c_void,
                k_ as *const libc::c_void,
                (20 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
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
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        225 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_1 = input_len0 as usize;
                let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
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
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input
                    .as_mut_ptr()
                    .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha1(
                    k_0,
                    k,
                    20 as libc::c_uint,
                    input.as_mut_ptr(),
                    input_len0,
                );
                Hacl_HMAC_compute_sha1(
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
        }
        1 => {
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    246 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_2 = entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as usize;
            let mut seed_material_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
            memset(
                seed_material_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_0.as_mut_ptr() as *mut libc::c_void,
                entropy_input as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_0.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                nonce as *const libc::c_void,
                (nonce_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_0
                    .as_mut_ptr()
                    .offset(entropy_input_len as isize)
                    .offset(nonce_len as isize) as *mut libc::c_void,
                personalization_string as *const libc::c_void,
                (personalization_string_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_1: *mut uint8_t = st.k;
            let mut v_0: *mut uint8_t = st.v;
            let mut ctr_0: *mut uint32_t = st.reseed_counter;
            memset(
                k_1 as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memset(
                v_0 as *mut libc::c_void,
                1 as libc::c_uint as libc::c_int,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            *ctr_0.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            let mut input_len_0: uint32_t = (33 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len);
            if input_len_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    263 as libc::c_int,
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
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0_0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material_0.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len
                        .wrapping_add(nonce_len)
                        .wrapping_add(personalization_string_len) as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_0
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_256(
                k__0,
                k_1,
                32 as libc::c_uint,
                input0_0.as_mut_ptr(),
                input_len_0,
            );
            Hacl_HMAC_compute_sha2_256(
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
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                let mut input_len0_0: uint32_t = (33 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len);
                if input_len0_0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        281 as libc::c_int,
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
                if entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) != 0 as libc::c_uint
                {
                    memcpy(
                        input_0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material_0.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len
                            .wrapping_add(nonce_len)
                            .wrapping_add(personalization_string_len) as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_0
                    .as_mut_ptr()
                    .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_256(
                    k_0_0,
                    k_1,
                    32 as libc::c_uint,
                    input_0.as_mut_ptr(),
                    input_len0_0,
                );
                Hacl_HMAC_compute_sha2_256(
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
        2 => {
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    302 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_5 = entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as usize;
            let mut seed_material_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
            memset(
                seed_material_1.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_1.as_mut_ptr() as *mut libc::c_void,
                entropy_input as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_1.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                nonce as *const libc::c_void,
                (nonce_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_1
                    .as_mut_ptr()
                    .offset(entropy_input_len as isize)
                    .offset(nonce_len as isize) as *mut libc::c_void,
                personalization_string as *const libc::c_void,
                (personalization_string_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_2: *mut uint8_t = st.k;
            let mut v_1: *mut uint8_t = st.v;
            let mut ctr_1: *mut uint32_t = st.reseed_counter;
            memset(
                k_2 as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memset(
                v_1 as *mut libc::c_void,
                1 as libc::c_uint as libc::c_int,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            *ctr_1.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            let mut input_len_1: uint32_t = (49 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len);
            if input_len_1 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    319 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_6 = input_len_1 as usize;
            let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
            memset(
                input0_1.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__1: *mut uint8_t = input0_1.as_mut_ptr();
            memcpy(
                k__1 as *mut libc::c_void,
                v_1 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0_1.as_mut_ptr().offset(49 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material_1.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len
                        .wrapping_add(nonce_len)
                        .wrapping_add(personalization_string_len) as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_1
                .as_mut_ptr()
                .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_384(
                k__1,
                k_2,
                48 as libc::c_uint,
                input0_1.as_mut_ptr(),
                input_len_1,
            );
            Hacl_HMAC_compute_sha2_384(
                v_1,
                k__1,
                48 as libc::c_uint,
                v_1,
                48 as libc::c_uint,
            );
            memcpy(
                k_2 as *mut libc::c_void,
                k__1 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                let mut input_len0_1: uint32_t = (49 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len);
                if input_len0_1 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        337 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_7 = input_len0_1 as usize;
                let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_7);
                memset(
                    input_1.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_1 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
                memcpy(
                    k_0_1 as *mut libc::c_void,
                    v_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) != 0 as libc::c_uint
                {
                    memcpy(
                        input_1.as_mut_ptr().offset(49 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material_1.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len
                            .wrapping_add(nonce_len)
                            .wrapping_add(personalization_string_len) as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_1
                    .as_mut_ptr()
                    .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_384(
                    k_0_1,
                    k_2,
                    48 as libc::c_uint,
                    input_1.as_mut_ptr(),
                    input_len0_1,
                );
                Hacl_HMAC_compute_sha2_384(
                    v_1,
                    k_0_1,
                    48 as libc::c_uint,
                    v_1,
                    48 as libc::c_uint,
                );
                memcpy(
                    k_2 as *mut libc::c_void,
                    k_0_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
        }
        3 => {
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    358 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_8 = entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) as usize;
            let mut seed_material_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_8);
            memset(
                seed_material_2.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_2.as_mut_ptr() as *mut libc::c_void,
                entropy_input as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_2.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                nonce as *const libc::c_void,
                (nonce_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_2
                    .as_mut_ptr()
                    .offset(entropy_input_len as isize)
                    .offset(nonce_len as isize) as *mut libc::c_void,
                personalization_string as *const libc::c_void,
                (personalization_string_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_3: *mut uint8_t = st.k;
            let mut v_2: *mut uint8_t = st.v;
            let mut ctr_2: *mut uint32_t = st.reseed_counter;
            memset(
                k_3 as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memset(
                v_2 as *mut libc::c_void,
                1 as libc::c_uint as libc::c_int,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            *ctr_2.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
            let mut input_len_2: uint32_t = (65 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len);
            if input_len_2 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    375 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_9 = input_len_2 as usize;
            let mut input0_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_9);
            memset(
                input0_2.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_2 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__2: *mut uint8_t = input0_2.as_mut_ptr();
            memcpy(
                k__2 as *mut libc::c_void,
                v_2 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                memcpy(
                    input0_2.as_mut_ptr().offset(65 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material_2.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len
                        .wrapping_add(nonce_len)
                        .wrapping_add(personalization_string_len) as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_2
                .as_mut_ptr()
                .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_512(
                k__2,
                k_3,
                64 as libc::c_uint,
                input0_2.as_mut_ptr(),
                input_len_2,
            );
            Hacl_HMAC_compute_sha2_512(
                v_2,
                k__2,
                64 as libc::c_uint,
                v_2,
                64 as libc::c_uint,
            );
            memcpy(
                k_3 as *mut libc::c_void,
                k__2 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len
                .wrapping_add(nonce_len)
                .wrapping_add(personalization_string_len) != 0 as libc::c_uint
            {
                let mut input_len0_2: uint32_t = (65 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len);
                if input_len0_2 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        393 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_10 = input_len0_2 as usize;
                let mut input_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_10);
                memset(
                    input_2.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_2 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_2: *mut uint8_t = input_2.as_mut_ptr();
                memcpy(
                    k_0_2 as *mut libc::c_void,
                    v_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len
                    .wrapping_add(nonce_len)
                    .wrapping_add(personalization_string_len) != 0 as libc::c_uint
                {
                    memcpy(
                        input_2.as_mut_ptr().offset(65 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material_2.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len
                            .wrapping_add(nonce_len)
                            .wrapping_add(personalization_string_len) as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_2
                    .as_mut_ptr()
                    .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_512(
                    k_0_2,
                    k_3,
                    64 as libc::c_uint,
                    input_2.as_mut_ptr(),
                    input_len0_2,
                );
                Hacl_HMAC_compute_sha2_512(
                    v_2,
                    k_0_2,
                    64 as libc::c_uint,
                    v_2,
                    64 as libc::c_uint,
                );
                memcpy(
                    k_3 as *mut libc::c_void,
                    k_0_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                413 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_reseed(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut st: Hacl_HMAC_DRBG_state,
    mut entropy_input_len: uint32_t,
    mut entropy_input: *mut uint8_t,
    mut additional_input_input_len: uint32_t,
    mut additional_input_input: *mut uint8_t,
) {
    match a as libc::c_int {
        4 => {
            if entropy_input_len.wrapping_add(additional_input_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    443 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla = entropy_input_len.wrapping_add(additional_input_input_len)
                as usize;
            let mut seed_material: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
            memset(
                seed_material.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_input_len)
                    as libc::c_ulong)
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
                additional_input_input as *const libc::c_void,
                (additional_input_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k: *mut uint8_t = st.k;
            let mut v: *mut uint8_t = st.v;
            let mut ctr: *mut uint32_t = st.reseed_counter;
            let mut input_len: uint32_t = (21 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_input_len);
            if input_len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    456 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = input_len as usize;
            let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
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
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                memcpy(
                    input0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0
                .as_mut_ptr()
                .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha1(
                k_,
                k,
                20 as libc::c_uint,
                input0.as_mut_ptr(),
                input_len,
            );
            Hacl_HMAC_compute_sha1(v, k_, 20 as libc::c_uint, v, 20 as libc::c_uint);
            memcpy(
                k as *mut libc::c_void,
                k_ as *const libc::c_void,
                (20 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                let mut input_len0: uint32_t = (21 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_input_len);
                if input_len0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        474 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_1 = input_len0 as usize;
                let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
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
                if entropy_input_len.wrapping_add(additional_input_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input.as_mut_ptr().offset(21 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input
                    .as_mut_ptr()
                    .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha1(
                    k_0,
                    k,
                    20 as libc::c_uint,
                    input.as_mut_ptr(),
                    input_len0,
                );
                Hacl_HMAC_compute_sha1(
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
        }
        1 => {
            if entropy_input_len.wrapping_add(additional_input_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    495 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_2 = entropy_input_len.wrapping_add(additional_input_input_len)
                as usize;
            let mut seed_material_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
            memset(
                seed_material_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_input_len)
                    as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_0.as_mut_ptr() as *mut libc::c_void,
                entropy_input as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_0.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input_input as *const libc::c_void,
                (additional_input_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_1: *mut uint8_t = st.k;
            let mut v_0: *mut uint8_t = st.v;
            let mut ctr_0: *mut uint32_t = st.reseed_counter;
            let mut input_len_0: uint32_t = (33 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_input_len);
            if input_len_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    508 as libc::c_int,
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
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                memcpy(
                    input0_0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material_0.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_0
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_256(
                k__0,
                k_1,
                32 as libc::c_uint,
                input0_0.as_mut_ptr(),
                input_len_0,
            );
            Hacl_HMAC_compute_sha2_256(
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
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                let mut input_len0_0: uint32_t = (33 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_input_len);
                if input_len0_0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        526 as libc::c_int,
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
                if entropy_input_len.wrapping_add(additional_input_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input_0.as_mut_ptr().offset(33 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material_0.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_0
                    .as_mut_ptr()
                    .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_256(
                    k_0_0,
                    k_1,
                    32 as libc::c_uint,
                    input_0.as_mut_ptr(),
                    input_len0_0,
                );
                Hacl_HMAC_compute_sha2_256(
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
            *ctr_0.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
        }
        2 => {
            if entropy_input_len.wrapping_add(additional_input_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    547 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_5 = entropy_input_len.wrapping_add(additional_input_input_len)
                as usize;
            let mut seed_material_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
            memset(
                seed_material_1.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_input_len)
                    as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_1.as_mut_ptr() as *mut libc::c_void,
                entropy_input as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_1.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input_input as *const libc::c_void,
                (additional_input_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_2: *mut uint8_t = st.k;
            let mut v_1: *mut uint8_t = st.v;
            let mut ctr_1: *mut uint32_t = st.reseed_counter;
            let mut input_len_1: uint32_t = (49 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_input_len);
            if input_len_1 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    560 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_6 = input_len_1 as usize;
            let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
            memset(
                input0_1.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__1: *mut uint8_t = input0_1.as_mut_ptr();
            memcpy(
                k__1 as *mut libc::c_void,
                v_1 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                memcpy(
                    input0_1.as_mut_ptr().offset(49 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material_1.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_1
                .as_mut_ptr()
                .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_384(
                k__1,
                k_2,
                48 as libc::c_uint,
                input0_1.as_mut_ptr(),
                input_len_1,
            );
            Hacl_HMAC_compute_sha2_384(
                v_1,
                k__1,
                48 as libc::c_uint,
                v_1,
                48 as libc::c_uint,
            );
            memcpy(
                k_2 as *mut libc::c_void,
                k__1 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                let mut input_len0_1: uint32_t = (49 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_input_len);
                if input_len0_1 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        578 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_7 = input_len0_1 as usize;
                let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_7);
                memset(
                    input_1.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_1 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
                memcpy(
                    k_0_1 as *mut libc::c_void,
                    v_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len.wrapping_add(additional_input_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input_1.as_mut_ptr().offset(49 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material_1.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_1
                    .as_mut_ptr()
                    .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_384(
                    k_0_1,
                    k_2,
                    48 as libc::c_uint,
                    input_1.as_mut_ptr(),
                    input_len0_1,
                );
                Hacl_HMAC_compute_sha2_384(
                    v_1,
                    k_0_1,
                    48 as libc::c_uint,
                    v_1,
                    48 as libc::c_uint,
                );
                memcpy(
                    k_2 as *mut libc::c_void,
                    k_0_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *ctr_1.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
        }
        3 => {
            if entropy_input_len.wrapping_add(additional_input_input_len) as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    599 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_8 = entropy_input_len.wrapping_add(additional_input_input_len)
                as usize;
            let mut seed_material_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_8);
            memset(
                seed_material_2.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (entropy_input_len.wrapping_add(additional_input_input_len)
                    as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_2.as_mut_ptr() as *mut libc::c_void,
                entropy_input as *const libc::c_void,
                (entropy_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                seed_material_2.as_mut_ptr().offset(entropy_input_len as isize)
                    as *mut libc::c_void,
                additional_input_input as *const libc::c_void,
                (additional_input_input_len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k_3: *mut uint8_t = st.k;
            let mut v_2: *mut uint8_t = st.v;
            let mut ctr_2: *mut uint32_t = st.reseed_counter;
            let mut input_len_2: uint32_t = (65 as libc::c_uint)
                .wrapping_add(entropy_input_len)
                .wrapping_add(additional_input_input_len);
            if input_len_2 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    612 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_9 = input_len_2 as usize;
            let mut input0_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_9);
            memset(
                input0_2.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_2 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__2: *mut uint8_t = input0_2.as_mut_ptr();
            memcpy(
                k__2 as *mut libc::c_void,
                v_2 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                memcpy(
                    input0_2.as_mut_ptr().offset(65 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    seed_material_2.as_mut_ptr() as *const libc::c_void,
                    (entropy_input_len.wrapping_add(additional_input_input_len)
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_2
                .as_mut_ptr()
                .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_512(
                k__2,
                k_3,
                64 as libc::c_uint,
                input0_2.as_mut_ptr(),
                input_len_2,
            );
            Hacl_HMAC_compute_sha2_512(
                v_2,
                k__2,
                64 as libc::c_uint,
                v_2,
                64 as libc::c_uint,
            );
            memcpy(
                k_3 as *mut libc::c_void,
                k__2 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if entropy_input_len.wrapping_add(additional_input_input_len)
                != 0 as libc::c_uint
            {
                let mut input_len0_2: uint32_t = (65 as libc::c_uint)
                    .wrapping_add(entropy_input_len)
                    .wrapping_add(additional_input_input_len);
                if input_len0_2 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        630 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_10 = input_len0_2 as usize;
                let mut input_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_10);
                memset(
                    input_2.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_2 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_2: *mut uint8_t = input_2.as_mut_ptr();
                memcpy(
                    k_0_2 as *mut libc::c_void,
                    v_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if entropy_input_len.wrapping_add(additional_input_input_len)
                    != 0 as libc::c_uint
                {
                    memcpy(
                        input_2.as_mut_ptr().offset(65 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        seed_material_2.as_mut_ptr() as *const libc::c_void,
                        (entropy_input_len.wrapping_add(additional_input_input_len)
                            as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_2
                    .as_mut_ptr()
                    .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_512(
                    k_0_2,
                    k_3,
                    64 as libc::c_uint,
                    input_2.as_mut_ptr(),
                    input_len0_2,
                );
                Hacl_HMAC_compute_sha2_512(
                    v_2,
                    k_0_2,
                    64 as libc::c_uint,
                    v_2,
                    64 as libc::c_uint,
                );
                memcpy(
                    k_3 as *mut libc::c_void,
                    k_0_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *ctr_2.offset(0 as libc::c_uint as isize) = 1 as libc::c_uint;
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                651 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_generate(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut output: *mut uint8_t,
    mut st: Hacl_HMAC_DRBG_state,
    mut n: uint32_t,
    mut additional_input_len: uint32_t,
    mut additional_input: *mut uint8_t,
) -> bool {
    match a as libc::c_int {
        4 => {
            if *(st.reseed_counter).offset(0 as libc::c_uint as isize)
                > Hacl_HMAC_DRBG_reseed_interval
            {
                return 0 as libc::c_int != 0;
            }
            let mut k: *mut uint8_t = st.k;
            let mut v: *mut uint8_t = st.v;
            let mut ctr: *mut uint32_t = st.reseed_counter;
            if additional_input_len > 0 as libc::c_uint {
                let mut input_len: uint32_t = (21 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        691 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla = input_len as usize;
                let mut input0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
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
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input0
                    .as_mut_ptr()
                    .offset(20 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha1(
                    k_,
                    k,
                    20 as libc::c_uint,
                    input0.as_mut_ptr(),
                    input_len,
                );
                Hacl_HMAC_compute_sha1(v, k_, 20 as libc::c_uint, v, 20 as libc::c_uint);
                memcpy(
                    k as *mut libc::c_void,
                    k_ as *const libc::c_void,
                    (20 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    let mut input_len0: uint32_t = (21 as libc::c_uint)
                        .wrapping_add(additional_input_len);
                    if input_len0 as size_t
                        > (18446744073709551615 as libc::c_ulong)
                            .wrapping_div(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            )
                    {
                        printf(
                            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                                as *const u8 as *const libc::c_char,
                            b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                            707 as libc::c_int,
                        );
                        exit(253 as libc::c_int);
                    }
                    let vla_0 = input_len0 as usize;
                    let mut input: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
                    memset(
                        input.as_mut_ptr() as *mut libc::c_void,
                        0 as libc::c_uint as libc::c_int,
                        (input_len0 as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    let mut k_0: *mut uint8_t = input.as_mut_ptr();
                    memcpy(
                        k_0 as *mut libc::c_void,
                        v as *const libc::c_void,
                        (20 as libc::c_uint as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    if additional_input_len != 0 as libc::c_uint {
                        memcpy(
                            input.as_mut_ptr().offset(21 as libc::c_uint as isize)
                                as *mut libc::c_void,
                            additional_input as *const libc::c_void,
                            (additional_input_len as libc::c_ulong)
                                .wrapping_mul(
                                    ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                                ),
                        );
                    }
                    *input
                        .as_mut_ptr()
                        .offset(
                            20 as libc::c_uint as isize,
                        ) = 1 as libc::c_uint as uint8_t;
                    Hacl_HMAC_compute_sha1(
                        k_0,
                        k,
                        20 as libc::c_uint,
                        input.as_mut_ptr(),
                        input_len0,
                    );
                    Hacl_HMAC_compute_sha1(
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
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
            }
            let mut output1: *mut uint8_t = output;
            let mut max: uint32_t = n.wrapping_div(20 as libc::c_uint);
            let mut out: *mut uint8_t = output1;
            let mut i: uint32_t = 0 as libc::c_uint;
            while i < max {
                Hacl_HMAC_compute_sha1(v, k, 20 as libc::c_uint, v, 20 as libc::c_uint);
                memcpy(
                    out.offset(i.wrapping_mul(20 as libc::c_uint) as isize)
                        as *mut libc::c_void,
                    v as *const libc::c_void,
                    (20 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                i = i.wrapping_add(1);
                i;
            }
            if max.wrapping_mul(20 as libc::c_uint) < n {
                let mut block: *mut uint8_t = output1
                    .offset(max.wrapping_mul(20 as libc::c_uint) as isize);
                Hacl_HMAC_compute_sha1(v, k, 20 as libc::c_uint, v, 20 as libc::c_uint);
                memcpy(
                    block as *mut libc::c_void,
                    v as *const libc::c_void,
                    (n.wrapping_sub(max.wrapping_mul(20 as libc::c_uint))
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut input_len_0: uint32_t = (21 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    737 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = input_len_0 as usize;
            let mut input0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                input0_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__0: *mut uint8_t = input0_0.as_mut_ptr();
            memcpy(
                k__0 as *mut libc::c_void,
                v as *const libc::c_void,
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
            Hacl_HMAC_compute_sha1(
                k__0,
                k,
                20 as libc::c_uint,
                input0_0.as_mut_ptr(),
                input_len_0,
            );
            Hacl_HMAC_compute_sha1(v, k__0, 20 as libc::c_uint, v, 20 as libc::c_uint);
            memcpy(
                k as *mut libc::c_void,
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
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        753 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_2 = input_len0_0 as usize;
                let mut input_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
                memset(
                    input_0.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_0 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_0: *mut uint8_t = input_0.as_mut_ptr();
                memcpy(
                    k_0_0 as *mut libc::c_void,
                    v as *const libc::c_void,
                    (20 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input_0.as_mut_ptr().offset(21 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_0
                    .as_mut_ptr()
                    .offset(20 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha1(
                    k_0_0,
                    k,
                    20 as libc::c_uint,
                    input_0.as_mut_ptr(),
                    input_len0_0,
                );
                Hacl_HMAC_compute_sha1(
                    v,
                    k_0_0,
                    20 as libc::c_uint,
                    v,
                    20 as libc::c_uint,
                );
                memcpy(
                    k as *mut libc::c_void,
                    k_0_0 as *const libc::c_void,
                    (20 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut old_ctr: uint32_t = *ctr.offset(0 as libc::c_uint as isize);
            *ctr
                .offset(
                    0 as libc::c_uint as isize,
                ) = old_ctr.wrapping_add(1 as libc::c_uint);
            return 1 as libc::c_int != 0;
        }
        1 => {
            if *(st.reseed_counter).offset(0 as libc::c_uint as isize)
                > Hacl_HMAC_DRBG_reseed_interval
            {
                return 0 as libc::c_int != 0;
            }
            let mut k_1: *mut uint8_t = st.k;
            let mut v_0: *mut uint8_t = st.v;
            let mut ctr_0: *mut uint32_t = st.reseed_counter;
            if additional_input_len > 0 as libc::c_uint {
                let mut input_len_1: uint32_t = (33 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len_1 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        783 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_3 = input_len_1 as usize;
                let mut input0_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
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
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input0_1
                    .as_mut_ptr()
                    .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_256(
                    k__1,
                    k_1,
                    32 as libc::c_uint,
                    input0_1.as_mut_ptr(),
                    input_len_1,
                );
                Hacl_HMAC_compute_sha2_256(
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
                            .wrapping_div(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            )
                    {
                        printf(
                            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                                as *const u8 as *const libc::c_char,
                            b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                            799 as libc::c_int,
                        );
                        exit(253 as libc::c_int);
                    }
                    let vla_4 = input_len0_1 as usize;
                    let mut input_1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
                    memset(
                        input_1.as_mut_ptr() as *mut libc::c_void,
                        0 as libc::c_uint as libc::c_int,
                        (input_len0_1 as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    let mut k_0_1: *mut uint8_t = input_1.as_mut_ptr();
                    memcpy(
                        k_0_1 as *mut libc::c_void,
                        v_0 as *const libc::c_void,
                        (32 as libc::c_uint as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    if additional_input_len != 0 as libc::c_uint {
                        memcpy(
                            input_1.as_mut_ptr().offset(33 as libc::c_uint as isize)
                                as *mut libc::c_void,
                            additional_input as *const libc::c_void,
                            (additional_input_len as libc::c_ulong)
                                .wrapping_mul(
                                    ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                                ),
                        );
                    }
                    *input_1
                        .as_mut_ptr()
                        .offset(
                            32 as libc::c_uint as isize,
                        ) = 1 as libc::c_uint as uint8_t;
                    Hacl_HMAC_compute_sha2_256(
                        k_0_1,
                        k_1,
                        32 as libc::c_uint,
                        input_1.as_mut_ptr(),
                        input_len0_1,
                    );
                    Hacl_HMAC_compute_sha2_256(
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
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
            }
            let mut output1_0: *mut uint8_t = output;
            let mut max_0: uint32_t = n.wrapping_div(32 as libc::c_uint);
            let mut out_0: *mut uint8_t = output1_0;
            let mut i_0: uint32_t = 0 as libc::c_uint;
            while i_0 < max_0 {
                Hacl_HMAC_compute_sha2_256(
                    v_0,
                    k_1,
                    32 as libc::c_uint,
                    v_0,
                    32 as libc::c_uint,
                );
                memcpy(
                    out_0.offset(i_0.wrapping_mul(32 as libc::c_uint) as isize)
                        as *mut libc::c_void,
                    v_0 as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                i_0 = i_0.wrapping_add(1);
                i_0;
            }
            if max_0.wrapping_mul(32 as libc::c_uint) < n {
                let mut block_0: *mut uint8_t = output1_0
                    .offset(max_0.wrapping_mul(32 as libc::c_uint) as isize);
                Hacl_HMAC_compute_sha2_256(
                    v_0,
                    k_1,
                    32 as libc::c_uint,
                    v_0,
                    32 as libc::c_uint,
                );
                memcpy(
                    block_0 as *mut libc::c_void,
                    v_0 as *const libc::c_void,
                    (n.wrapping_sub(max_0.wrapping_mul(32 as libc::c_uint))
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut input_len_2: uint32_t = (33 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len_2 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    829 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_5 = input_len_2 as usize;
            let mut input0_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
            memset(
                input0_2.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_2 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__2: *mut uint8_t = input0_2.as_mut_ptr();
            memcpy(
                k__2 as *mut libc::c_void,
                v_0 as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input0_2.as_mut_ptr().offset(33 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_2
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_256(
                k__2,
                k_1,
                32 as libc::c_uint,
                input0_2.as_mut_ptr(),
                input_len_2,
            );
            Hacl_HMAC_compute_sha2_256(
                v_0,
                k__2,
                32 as libc::c_uint,
                v_0,
                32 as libc::c_uint,
            );
            memcpy(
                k_1 as *mut libc::c_void,
                k__2 as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                let mut input_len0_2: uint32_t = (33 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len0_2 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        845 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_6 = input_len0_2 as usize;
                let mut input_2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
                memset(
                    input_2.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_2 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_2: *mut uint8_t = input_2.as_mut_ptr();
                memcpy(
                    k_0_2 as *mut libc::c_void,
                    v_0 as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input_2.as_mut_ptr().offset(33 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_2
                    .as_mut_ptr()
                    .offset(32 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_256(
                    k_0_2,
                    k_1,
                    32 as libc::c_uint,
                    input_2.as_mut_ptr(),
                    input_len0_2,
                );
                Hacl_HMAC_compute_sha2_256(
                    v_0,
                    k_0_2,
                    32 as libc::c_uint,
                    v_0,
                    32 as libc::c_uint,
                );
                memcpy(
                    k_1 as *mut libc::c_void,
                    k_0_2 as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut old_ctr_0: uint32_t = *ctr_0.offset(0 as libc::c_uint as isize);
            *ctr_0
                .offset(
                    0 as libc::c_uint as isize,
                ) = old_ctr_0.wrapping_add(1 as libc::c_uint);
            return 1 as libc::c_int != 0;
        }
        2 => {
            if *(st.reseed_counter).offset(0 as libc::c_uint as isize)
                > Hacl_HMAC_DRBG_reseed_interval
            {
                return 0 as libc::c_int != 0;
            }
            let mut k_2: *mut uint8_t = st.k;
            let mut v_1: *mut uint8_t = st.v;
            let mut ctr_1: *mut uint32_t = st.reseed_counter;
            if additional_input_len > 0 as libc::c_uint {
                let mut input_len_3: uint32_t = (49 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len_3 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        875 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_7 = input_len_3 as usize;
                let mut input0_3: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_7);
                memset(
                    input0_3.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len_3 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k__3: *mut uint8_t = input0_3.as_mut_ptr();
                memcpy(
                    k__3 as *mut libc::c_void,
                    v_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input0_3.as_mut_ptr().offset(49 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input0_3
                    .as_mut_ptr()
                    .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_384(
                    k__3,
                    k_2,
                    48 as libc::c_uint,
                    input0_3.as_mut_ptr(),
                    input_len_3,
                );
                Hacl_HMAC_compute_sha2_384(
                    v_1,
                    k__3,
                    48 as libc::c_uint,
                    v_1,
                    48 as libc::c_uint,
                );
                memcpy(
                    k_2 as *mut libc::c_void,
                    k__3 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    let mut input_len0_3: uint32_t = (49 as libc::c_uint)
                        .wrapping_add(additional_input_len);
                    if input_len0_3 as size_t
                        > (18446744073709551615 as libc::c_ulong)
                            .wrapping_div(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            )
                    {
                        printf(
                            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                                as *const u8 as *const libc::c_char,
                            b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                            891 as libc::c_int,
                        );
                        exit(253 as libc::c_int);
                    }
                    let vla_8 = input_len0_3 as usize;
                    let mut input_3: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_8);
                    memset(
                        input_3.as_mut_ptr() as *mut libc::c_void,
                        0 as libc::c_uint as libc::c_int,
                        (input_len0_3 as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    let mut k_0_3: *mut uint8_t = input_3.as_mut_ptr();
                    memcpy(
                        k_0_3 as *mut libc::c_void,
                        v_1 as *const libc::c_void,
                        (48 as libc::c_uint as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    if additional_input_len != 0 as libc::c_uint {
                        memcpy(
                            input_3.as_mut_ptr().offset(49 as libc::c_uint as isize)
                                as *mut libc::c_void,
                            additional_input as *const libc::c_void,
                            (additional_input_len as libc::c_ulong)
                                .wrapping_mul(
                                    ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                                ),
                        );
                    }
                    *input_3
                        .as_mut_ptr()
                        .offset(
                            48 as libc::c_uint as isize,
                        ) = 1 as libc::c_uint as uint8_t;
                    Hacl_HMAC_compute_sha2_384(
                        k_0_3,
                        k_2,
                        48 as libc::c_uint,
                        input_3.as_mut_ptr(),
                        input_len0_3,
                    );
                    Hacl_HMAC_compute_sha2_384(
                        v_1,
                        k_0_3,
                        48 as libc::c_uint,
                        v_1,
                        48 as libc::c_uint,
                    );
                    memcpy(
                        k_2 as *mut libc::c_void,
                        k_0_3 as *const libc::c_void,
                        (48 as libc::c_uint as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
            }
            let mut output1_1: *mut uint8_t = output;
            let mut max_1: uint32_t = n.wrapping_div(48 as libc::c_uint);
            let mut out_1: *mut uint8_t = output1_1;
            let mut i_1: uint32_t = 0 as libc::c_uint;
            while i_1 < max_1 {
                Hacl_HMAC_compute_sha2_384(
                    v_1,
                    k_2,
                    48 as libc::c_uint,
                    v_1,
                    48 as libc::c_uint,
                );
                memcpy(
                    out_1.offset(i_1.wrapping_mul(48 as libc::c_uint) as isize)
                        as *mut libc::c_void,
                    v_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                i_1 = i_1.wrapping_add(1);
                i_1;
            }
            if max_1.wrapping_mul(48 as libc::c_uint) < n {
                let mut block_1: *mut uint8_t = output1_1
                    .offset(max_1.wrapping_mul(48 as libc::c_uint) as isize);
                Hacl_HMAC_compute_sha2_384(
                    v_1,
                    k_2,
                    48 as libc::c_uint,
                    v_1,
                    48 as libc::c_uint,
                );
                memcpy(
                    block_1 as *mut libc::c_void,
                    v_1 as *const libc::c_void,
                    (n.wrapping_sub(max_1.wrapping_mul(48 as libc::c_uint))
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut input_len_4: uint32_t = (49 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len_4 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    921 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_9 = input_len_4 as usize;
            let mut input0_4: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_9);
            memset(
                input0_4.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_4 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__4: *mut uint8_t = input0_4.as_mut_ptr();
            memcpy(
                k__4 as *mut libc::c_void,
                v_1 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input0_4.as_mut_ptr().offset(49 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_4
                .as_mut_ptr()
                .offset(48 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_384(
                k__4,
                k_2,
                48 as libc::c_uint,
                input0_4.as_mut_ptr(),
                input_len_4,
            );
            Hacl_HMAC_compute_sha2_384(
                v_1,
                k__4,
                48 as libc::c_uint,
                v_1,
                48 as libc::c_uint,
            );
            memcpy(
                k_2 as *mut libc::c_void,
                k__4 as *const libc::c_void,
                (48 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                let mut input_len0_4: uint32_t = (49 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len0_4 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        937 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_10 = input_len0_4 as usize;
                let mut input_4: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_10);
                memset(
                    input_4.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_4 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_4: *mut uint8_t = input_4.as_mut_ptr();
                memcpy(
                    k_0_4 as *mut libc::c_void,
                    v_1 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input_4.as_mut_ptr().offset(49 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_4
                    .as_mut_ptr()
                    .offset(48 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_384(
                    k_0_4,
                    k_2,
                    48 as libc::c_uint,
                    input_4.as_mut_ptr(),
                    input_len0_4,
                );
                Hacl_HMAC_compute_sha2_384(
                    v_1,
                    k_0_4,
                    48 as libc::c_uint,
                    v_1,
                    48 as libc::c_uint,
                );
                memcpy(
                    k_2 as *mut libc::c_void,
                    k_0_4 as *const libc::c_void,
                    (48 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut old_ctr_1: uint32_t = *ctr_1.offset(0 as libc::c_uint as isize);
            *ctr_1
                .offset(
                    0 as libc::c_uint as isize,
                ) = old_ctr_1.wrapping_add(1 as libc::c_uint);
            return 1 as libc::c_int != 0;
        }
        3 => {
            if *(st.reseed_counter).offset(0 as libc::c_uint as isize)
                > Hacl_HMAC_DRBG_reseed_interval
            {
                return 0 as libc::c_int != 0;
            }
            let mut k_3: *mut uint8_t = st.k;
            let mut v_2: *mut uint8_t = st.v;
            let mut ctr_2: *mut uint32_t = st.reseed_counter;
            if additional_input_len > 0 as libc::c_uint {
                let mut input_len_5: uint32_t = (65 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len_5 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        967 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_11 = input_len_5 as usize;
                let mut input0_5: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_11);
                memset(
                    input0_5.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len_5 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k__5: *mut uint8_t = input0_5.as_mut_ptr();
                memcpy(
                    k__5 as *mut libc::c_void,
                    v_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input0_5.as_mut_ptr().offset(65 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input0_5
                    .as_mut_ptr()
                    .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_512(
                    k__5,
                    k_3,
                    64 as libc::c_uint,
                    input0_5.as_mut_ptr(),
                    input_len_5,
                );
                Hacl_HMAC_compute_sha2_512(
                    v_2,
                    k__5,
                    64 as libc::c_uint,
                    v_2,
                    64 as libc::c_uint,
                );
                memcpy(
                    k_3 as *mut libc::c_void,
                    k__5 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    let mut input_len0_5: uint32_t = (65 as libc::c_uint)
                        .wrapping_add(additional_input_len);
                    if input_len0_5 as size_t
                        > (18446744073709551615 as libc::c_ulong)
                            .wrapping_div(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            )
                    {
                        printf(
                            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                                as *const u8 as *const libc::c_char,
                            b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                            983 as libc::c_int,
                        );
                        exit(253 as libc::c_int);
                    }
                    let vla_12 = input_len0_5 as usize;
                    let mut input_5: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_12);
                    memset(
                        input_5.as_mut_ptr() as *mut libc::c_void,
                        0 as libc::c_uint as libc::c_int,
                        (input_len0_5 as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    let mut k_0_5: *mut uint8_t = input_5.as_mut_ptr();
                    memcpy(
                        k_0_5 as *mut libc::c_void,
                        v_2 as *const libc::c_void,
                        (64 as libc::c_uint as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                    if additional_input_len != 0 as libc::c_uint {
                        memcpy(
                            input_5.as_mut_ptr().offset(65 as libc::c_uint as isize)
                                as *mut libc::c_void,
                            additional_input as *const libc::c_void,
                            (additional_input_len as libc::c_ulong)
                                .wrapping_mul(
                                    ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                                ),
                        );
                    }
                    *input_5
                        .as_mut_ptr()
                        .offset(
                            64 as libc::c_uint as isize,
                        ) = 1 as libc::c_uint as uint8_t;
                    Hacl_HMAC_compute_sha2_512(
                        k_0_5,
                        k_3,
                        64 as libc::c_uint,
                        input_5.as_mut_ptr(),
                        input_len0_5,
                    );
                    Hacl_HMAC_compute_sha2_512(
                        v_2,
                        k_0_5,
                        64 as libc::c_uint,
                        v_2,
                        64 as libc::c_uint,
                    );
                    memcpy(
                        k_3 as *mut libc::c_void,
                        k_0_5 as *const libc::c_void,
                        (64 as libc::c_uint as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
            }
            let mut output1_2: *mut uint8_t = output;
            let mut max_2: uint32_t = n.wrapping_div(64 as libc::c_uint);
            let mut out_2: *mut uint8_t = output1_2;
            let mut i_2: uint32_t = 0 as libc::c_uint;
            while i_2 < max_2 {
                Hacl_HMAC_compute_sha2_512(
                    v_2,
                    k_3,
                    64 as libc::c_uint,
                    v_2,
                    64 as libc::c_uint,
                );
                memcpy(
                    out_2.offset(i_2.wrapping_mul(64 as libc::c_uint) as isize)
                        as *mut libc::c_void,
                    v_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                i_2 = i_2.wrapping_add(1);
                i_2;
            }
            if max_2.wrapping_mul(64 as libc::c_uint) < n {
                let mut block_2: *mut uint8_t = output1_2
                    .offset(max_2.wrapping_mul(64 as libc::c_uint) as isize);
                Hacl_HMAC_compute_sha2_512(
                    v_2,
                    k_3,
                    64 as libc::c_uint,
                    v_2,
                    64 as libc::c_uint,
                );
                memcpy(
                    block_2 as *mut libc::c_void,
                    v_2 as *const libc::c_void,
                    (n.wrapping_sub(max_2.wrapping_mul(64 as libc::c_uint))
                        as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut input_len_6: uint32_t = (65 as libc::c_uint)
                .wrapping_add(additional_input_len);
            if input_len_6 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                    1013 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_13 = input_len_6 as usize;
            let mut input0_6: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_13);
            memset(
                input0_6.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (input_len_6 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut k__6: *mut uint8_t = input0_6.as_mut_ptr();
            memcpy(
                k__6 as *mut libc::c_void,
                v_2 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                memcpy(
                    input0_6.as_mut_ptr().offset(65 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    additional_input as *const libc::c_void,
                    (additional_input_len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            *input0_6
                .as_mut_ptr()
                .offset(64 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            Hacl_HMAC_compute_sha2_512(
                k__6,
                k_3,
                64 as libc::c_uint,
                input0_6.as_mut_ptr(),
                input_len_6,
            );
            Hacl_HMAC_compute_sha2_512(
                v_2,
                k__6,
                64 as libc::c_uint,
                v_2,
                64 as libc::c_uint,
            );
            memcpy(
                k_3 as *mut libc::c_void,
                k__6 as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            if additional_input_len != 0 as libc::c_uint {
                let mut input_len0_6: uint32_t = (65 as libc::c_uint)
                    .wrapping_add(additional_input_len);
                if input_len0_6 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                        1029 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_14 = input_len0_6 as usize;
                let mut input_6: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_14);
                memset(
                    input_6.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (input_len0_6 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut k_0_6: *mut uint8_t = input_6.as_mut_ptr();
                memcpy(
                    k_0_6 as *mut libc::c_void,
                    v_2 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                if additional_input_len != 0 as libc::c_uint {
                    memcpy(
                        input_6.as_mut_ptr().offset(65 as libc::c_uint as isize)
                            as *mut libc::c_void,
                        additional_input as *const libc::c_void,
                        (additional_input_len as libc::c_ulong)
                            .wrapping_mul(
                                ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
                            ),
                    );
                }
                *input_6
                    .as_mut_ptr()
                    .offset(64 as libc::c_uint as isize) = 1 as libc::c_uint as uint8_t;
                Hacl_HMAC_compute_sha2_512(
                    k_0_6,
                    k_3,
                    64 as libc::c_uint,
                    input_6.as_mut_ptr(),
                    input_len0_6,
                );
                Hacl_HMAC_compute_sha2_512(
                    v_2,
                    k_0_6,
                    64 as libc::c_uint,
                    v_2,
                    64 as libc::c_uint,
                );
                memcpy(
                    k_3 as *mut libc::c_void,
                    k_0_6 as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
            }
            let mut old_ctr_2: uint32_t = *ctr_2.offset(0 as libc::c_uint as isize);
            *ctr_2
                .offset(
                    0 as libc::c_uint as isize,
                ) = old_ctr_2.wrapping_add(1 as libc::c_uint);
            return 1 as libc::c_int != 0;
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_HMAC_DRBG.c\0" as *const u8 as *const libc::c_char,
                1049 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HMAC_DRBG_free(
    mut uu___: Spec_Hash_Definitions_hash_alg,
    mut s: Hacl_HMAC_DRBG_state,
) {
    let mut k: *mut uint8_t = s.k;
    let mut v: *mut uint8_t = s.v;
    let mut ctr: *mut uint32_t = s.reseed_counter;
    free(k as *mut libc::c_void);
    free(v as *mut libc::c_void);
    free(ctr as *mut libc::c_void);
}
