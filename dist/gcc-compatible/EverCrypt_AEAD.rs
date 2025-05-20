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
    static mut __stderrp: *mut FILE;
    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
    fn EverCrypt_Chacha20Poly1305_aead_encrypt(
        k: *mut uint8_t,
        n: *mut uint8_t,
        aadlen: uint32_t,
        aad: *mut uint8_t,
        mlen: uint32_t,
        m: *mut uint8_t,
        cipher: *mut uint8_t,
        tag: *mut uint8_t,
    );
    fn EverCrypt_Chacha20Poly1305_aead_decrypt(
        k: *mut uint8_t,
        n: *mut uint8_t,
        aadlen: uint32_t,
        aad: *mut uint8_t,
        mlen: uint32_t,
        m: *mut uint8_t,
        cipher: *mut uint8_t,
        tag: *mut uint8_t,
    ) -> uint32_t;
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
pub type Spec_Agile_AEAD_alg = uint8_t;
pub type EverCrypt_Error_error_code = uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct EverCrypt_AEAD_state_s_s {
    pub impl_0: Spec_Cipher_Expansion_impl,
    pub ek: *mut uint8_t,
}
pub type Spec_Cipher_Expansion_impl = uint8_t;
pub type EverCrypt_AEAD_state_s = EverCrypt_AEAD_state_s_s;
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_uu___is_Ek(
    mut a: Spec_Agile_AEAD_alg,
    mut projectee: EverCrypt_AEAD_state_s,
) -> bool {
    return 1 as libc::c_int != 0;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_alg_of_state(
    mut s: *mut EverCrypt_AEAD_state_s,
) -> Spec_Agile_AEAD_alg {
    let mut impl_0: Spec_Cipher_Expansion_impl = (*s).impl_0;
    match impl_0 as libc::c_int {
        0 => return 2 as libc::c_int as Spec_Agile_AEAD_alg,
        1 => return 0 as libc::c_int as Spec_Agile_AEAD_alg,
        2 => return 1 as libc::c_int as Spec_Agile_AEAD_alg,
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
                80 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
unsafe extern "C" fn create_in_chacha20_poly1305(
    mut dst: *mut *mut EverCrypt_AEAD_state_s,
    mut k: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    let mut ek: *mut uint8_t = calloc(
        32 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut p: *mut EverCrypt_AEAD_state_s = malloc(
        ::core::mem::size_of::<EverCrypt_AEAD_state_s>() as libc::c_ulong,
    ) as *mut EverCrypt_AEAD_state_s;
    *p
        .offset(
            0 as libc::c_uint as isize,
        ) = {
        let mut init = EverCrypt_AEAD_state_s_s {
            impl_0: 0 as libc::c_int as Spec_Cipher_Expansion_impl,
            ek: ek,
        };
        init
    };
    memcpy(
        ek as *mut libc::c_void,
        k as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let ref mut fresh0 = *dst.offset(0 as libc::c_uint as isize);
    *fresh0 = p;
    return 0 as libc::c_int as EverCrypt_Error_error_code;
}
unsafe extern "C" fn create_in_aes128_gcm(
    mut dst: *mut *mut EverCrypt_AEAD_state_s,
    mut k: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    return 1 as libc::c_int as EverCrypt_Error_error_code;
}
unsafe extern "C" fn create_in_aes256_gcm(
    mut dst: *mut *mut EverCrypt_AEAD_state_s,
    mut k: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    return 1 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_create_in(
    mut a: Spec_Agile_AEAD_alg,
    mut dst: *mut *mut EverCrypt_AEAD_state_s,
    mut k: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    match a as libc::c_int {
        0 => return create_in_aes128_gcm(dst, k),
        1 => return create_in_aes256_gcm(dst, k),
        2 => return create_in_chacha20_poly1305(dst, k),
        _ => return 1 as libc::c_int as EverCrypt_Error_error_code,
    };
}
unsafe extern "C" fn encrypt_aes128_gcm(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        315 as libc::c_int,
        b"statically unreachable\0" as *const u8 as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
unsafe extern "C" fn encrypt_aes256_gcm(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        438 as libc::c_int,
        b"statically unreachable\0" as *const u8 as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    if s.is_null() {
        return 2 as libc::c_int as EverCrypt_Error_error_code;
    }
    let mut scrut: EverCrypt_AEAD_state_s = *s;
    let mut i: Spec_Cipher_Expansion_impl = scrut.impl_0;
    let mut ek: *mut uint8_t = scrut.ek;
    match i as libc::c_int {
        1 => {
            return encrypt_aes128_gcm(
                s,
                iv,
                iv_len,
                ad,
                ad_len,
                plain,
                plain_len,
                cipher,
                tag,
            );
        }
        2 => {
            return encrypt_aes256_gcm(
                s,
                iv,
                iv_len,
                ad,
                ad_len,
                plain,
                plain_len,
                cipher,
                tag,
            );
        }
        0 => {
            if iv_len != 12 as libc::c_uint {
                return 4 as libc::c_int as EverCrypt_Error_error_code;
            }
            EverCrypt_Chacha20Poly1305_aead_encrypt(
                ek,
                iv,
                ad_len,
                ad,
                plain_len,
                plain,
                cipher,
                tag,
            );
            return 0 as libc::c_int as EverCrypt_Error_error_code;
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
                504 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        648 as libc::c_int,
        b"EverCrypt was compiled on a system which doesn't support Vale\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        792 as libc::c_int,
        b"EverCrypt was compiled on a system which doesn't support Vale\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt_expand_aes128_gcm(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    return 1 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt_expand_aes256_gcm(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    return 1 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    let mut ek: [uint8_t; 32] = [
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
    ];
    let mut p: EverCrypt_AEAD_state_s = {
        let mut init = EverCrypt_AEAD_state_s_s {
            impl_0: 0 as libc::c_int as Spec_Cipher_Expansion_impl,
            ek: ek.as_mut_ptr(),
        };
        init
    };
    memcpy(
        ek.as_mut_ptr() as *mut libc::c_void,
        k as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut s: *mut EverCrypt_AEAD_state_s = &mut p;
    let mut ek0: *mut uint8_t = (*s).ek;
    EverCrypt_Chacha20Poly1305_aead_encrypt(
        ek0,
        iv,
        ad_len,
        ad,
        plain_len,
        plain,
        cipher,
        tag,
    );
    return 0 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_encrypt_expand(
    mut a: Spec_Agile_AEAD_alg,
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut plain: *mut uint8_t,
    mut plain_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut tag: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    match a as libc::c_int {
        0 => {
            return EverCrypt_AEAD_encrypt_expand_aes128_gcm(
                k,
                iv,
                iv_len,
                ad,
                ad_len,
                plain,
                plain_len,
                cipher,
                tag,
            );
        }
        1 => {
            return EverCrypt_AEAD_encrypt_expand_aes256_gcm(
                k,
                iv,
                iv_len,
                ad,
                ad_len,
                plain,
                plain_len,
                cipher,
                tag,
            );
        }
        2 => {
            return EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
                k,
                iv,
                iv_len,
                ad,
                ad_len,
                plain,
                plain_len,
                cipher,
                tag,
            );
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
                1160 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
unsafe extern "C" fn decrypt_aes128_gcm(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        1295 as libc::c_int,
        b"statically unreachable\0" as *const u8 as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
unsafe extern "C" fn decrypt_aes256_gcm(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        1430 as libc::c_int,
        b"statically unreachable\0" as *const u8 as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
unsafe extern "C" fn decrypt_chacha20_poly1305(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    if s.is_null() {
        return 2 as libc::c_int as EverCrypt_Error_error_code;
    }
    if iv_len != 12 as libc::c_uint {
        return 4 as libc::c_int as EverCrypt_Error_error_code;
    }
    let mut ek: *mut uint8_t = (*s).ek;
    let mut r: uint32_t = EverCrypt_Chacha20Poly1305_aead_decrypt(
        ek,
        iv,
        ad_len,
        ad,
        cipher_len,
        dst,
        cipher,
        tag,
    );
    if r == 0 as libc::c_uint {
        return 0 as libc::c_int as EverCrypt_Error_error_code;
    }
    return 3 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt(
    mut s: *mut EverCrypt_AEAD_state_s,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    if s.is_null() {
        return 2 as libc::c_int as EverCrypt_Error_error_code;
    }
    let mut i: Spec_Cipher_Expansion_impl = (*s).impl_0;
    match i as libc::c_int {
        1 => {
            return decrypt_aes128_gcm(
                s,
                iv,
                iv_len,
                ad,
                ad_len,
                cipher,
                cipher_len,
                tag,
                dst,
            );
        }
        2 => {
            return decrypt_aes256_gcm(
                s,
                iv,
                iv_len,
                ad,
                ad_len,
                cipher,
                cipher_len,
                tag,
                dst,
            );
        }
        0 => {
            return decrypt_chacha20_poly1305(
                s,
                iv,
                iv_len,
                ad,
                ad_len,
                cipher,
                cipher_len,
                tag,
                dst,
            );
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
                1532 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        1682 as libc::c_int,
        b"EverCrypt was compiled on a system which doesn't support Vale\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    fprintf(
        __stderrp,
        b"KaRaMeL abort at %s:%d\n%s\n\0" as *const u8 as *const libc::c_char,
        b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
        1832 as libc::c_int,
        b"EverCrypt was compiled on a system which doesn't support Vale\0" as *const u8
            as *const libc::c_char,
    );
    exit(255 as libc::c_uint as libc::c_int);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt_expand_aes128_gcm(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    return 1 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt_expand_aes256_gcm(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    return 1 as libc::c_int as EverCrypt_Error_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    let mut ek: [uint8_t; 32] = [
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
    ];
    let mut p: EverCrypt_AEAD_state_s = {
        let mut init = EverCrypt_AEAD_state_s_s {
            impl_0: 0 as libc::c_int as Spec_Cipher_Expansion_impl,
            ek: ek.as_mut_ptr(),
        };
        init
    };
    memcpy(
        ek.as_mut_ptr() as *mut libc::c_void,
        k as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut s: *mut EverCrypt_AEAD_state_s = &mut p;
    let mut r: EverCrypt_Error_error_code = decrypt_chacha20_poly1305(
        s,
        iv,
        iv_len,
        ad,
        ad_len,
        cipher,
        cipher_len,
        tag,
        dst,
    );
    return r;
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_decrypt_expand(
    mut a: Spec_Agile_AEAD_alg,
    mut k: *mut uint8_t,
    mut iv: *mut uint8_t,
    mut iv_len: uint32_t,
    mut ad: *mut uint8_t,
    mut ad_len: uint32_t,
    mut cipher: *mut uint8_t,
    mut cipher_len: uint32_t,
    mut tag: *mut uint8_t,
    mut dst: *mut uint8_t,
) -> EverCrypt_Error_error_code {
    match a as libc::c_int {
        0 => {
            return EverCrypt_AEAD_decrypt_expand_aes128_gcm(
                k,
                iv,
                iv_len,
                ad,
                ad_len,
                cipher,
                cipher_len,
                tag,
                dst,
            );
        }
        1 => {
            return EverCrypt_AEAD_decrypt_expand_aes256_gcm(
                k,
                iv,
                iv_len,
                ad,
                ad_len,
                cipher,
                cipher_len,
                tag,
                dst,
            );
        }
        2 => {
            return EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
                k,
                iv,
                iv_len,
                ad,
                ad_len,
                cipher,
                cipher_len,
                tag,
                dst,
            );
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_AEAD.c\0" as *const u8 as *const libc::c_char,
                2211 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_AEAD_free(mut s: *mut EverCrypt_AEAD_state_s) {
    let mut ek: *mut uint8_t = (*s).ek;
    free(ek as *mut libc::c_void);
    free(s as *mut libc::c_void);
}
