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
    static mut __stderrp: *mut FILE;
    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
}
pub type __int64_t = libc::c_longlong;
pub type __darwin_off_t = __int64_t;
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
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Definitions_word_len(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> uint32_t {
    match a as libc::c_int {
        5 => return 4 as libc::c_uint,
        4 => return 4 as libc::c_uint,
        0 => return 4 as libc::c_uint,
        1 => return 4 as libc::c_uint,
        2 => return 8 as libc::c_uint,
        3 => return 8 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_Hash_Base.c\0" as *const u8 as *const libc::c_char,
                58 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Definitions_block_len(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> uint32_t {
    match a as libc::c_int {
        5 => return 64 as libc::c_uint,
        4 => return 64 as libc::c_uint,
        0 => return 64 as libc::c_uint,
        1 => return 64 as libc::c_uint,
        2 => return 128 as libc::c_uint,
        3 => return 128 as libc::c_uint,
        9 => return 144 as libc::c_uint,
        8 => return 136 as libc::c_uint,
        10 => return 104 as libc::c_uint,
        11 => return 72 as libc::c_uint,
        12 => return 168 as libc::c_uint,
        13 => return 136 as libc::c_uint,
        6 => return 64 as libc::c_uint,
        7 => return 128 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_Hash_Base.c\0" as *const u8 as *const libc::c_char,
                126 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Definitions_hash_word_len(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> uint32_t {
    match a as libc::c_int {
        5 => return 4 as libc::c_uint,
        4 => return 5 as libc::c_uint,
        0 => return 7 as libc::c_uint,
        1 => return 8 as libc::c_uint,
        2 => return 6 as libc::c_uint,
        3 => return 8 as libc::c_uint,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"Hacl_Hash_Base.c\0" as *const u8 as *const libc::c_char,
                162 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Definitions_hash_len(
    mut a: Spec_Hash_Definitions_hash_alg,
) -> uint32_t {
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
                b"Hacl_Hash_Base.c\0" as *const u8 as *const libc::c_char,
                222 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
