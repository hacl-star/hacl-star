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
    fn memset(
        _: *mut libc::c_void,
        _: libc::c_int,
        _: libc::c_ulong,
    ) -> *mut libc::c_void;
    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
    fn Hacl_HKDF_expand_sha2_256(
        okm: *mut uint8_t,
        prk: *mut uint8_t,
        prklen: uint32_t,
        info: *mut uint8_t,
        infolen: uint32_t,
        len: uint32_t,
    );
    fn Hacl_HKDF_extract_sha2_256(
        prk: *mut uint8_t,
        salt: *mut uint8_t,
        saltlen: uint32_t,
        ikm: *mut uint8_t,
        ikmlen: uint32_t,
    );
    fn Hacl_HKDF_expand_sha2_512(
        okm: *mut uint8_t,
        prk: *mut uint8_t,
        prklen: uint32_t,
        info: *mut uint8_t,
        infolen: uint32_t,
        len: uint32_t,
    );
    fn Hacl_HKDF_extract_sha2_512(
        prk: *mut uint8_t,
        salt: *mut uint8_t,
        saltlen: uint32_t,
        ikm: *mut uint8_t,
        ikmlen: uint32_t,
    );
    fn Hacl_Curve25519_51_scalarmult(
        out: *mut uint8_t,
        priv_0: *mut uint8_t,
        pub_0: *mut uint8_t,
    );
    fn Hacl_Curve25519_51_secret_to_public(pub_0: *mut uint8_t, priv_0: *mut uint8_t);
    fn Hacl_AEAD_Chacha20Poly1305_encrypt(
        output: *mut uint8_t,
        tag: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
        key: *mut uint8_t,
        nonce: *mut uint8_t,
    );
    fn Hacl_AEAD_Chacha20Poly1305_decrypt(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
        data: *mut uint8_t,
        data_len: uint32_t,
        key: *mut uint8_t,
        nonce: *mut uint8_t,
        tag: *mut uint8_t,
    ) -> uint32_t;
}
pub type __uint16_t = libc::c_ushort;
pub type __uint64_t = libc::c_ulonglong;
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
pub type uint8_t = libc::c_uchar;
pub type uint16_t = libc::c_ushort;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Impl_HPKE_context_s_s {
    pub ctx_key: *mut uint8_t,
    pub ctx_nonce: *mut uint8_t,
    pub ctx_seq: *mut uint64_t,
    pub ctx_exporter: *mut uint8_t,
}
pub type Hacl_Impl_HPKE_context_s = Hacl_Impl_HPKE_context_s_s;
#[inline]
unsafe extern "C" fn _OSSwapInt16(mut _data: __uint16_t) -> __uint16_t {
    return ((_data as libc::c_int) << 8 as libc::c_int
        | _data as libc::c_int >> 8 as libc::c_int) as __uint16_t;
}
#[inline]
unsafe extern "C" fn _OSSwapInt64(mut _data: __uint64_t) -> __uint64_t {
    return _data.swap_bytes();
}
#[inline]
unsafe extern "C" fn store16(mut b: *mut uint8_t, mut i: uint16_t) {
    memcpy(
        b as *mut libc::c_void,
        &mut i as *mut uint16_t as *const libc::c_void,
        2 as libc::c_int as libc::c_ulong,
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
#[inline(never)]
unsafe extern "C" fn FStar_UInt8_eq_mask(mut a: uint8_t, mut b: uint8_t) -> uint8_t {
    let mut x: uint8_t = (a as uint32_t ^ b as uint32_t) as uint8_t;
    let mut minus_x: uint8_t = (!(x as libc::c_int) as uint32_t)
        .wrapping_add(1 as libc::c_uint) as uint8_t;
    let mut x_or_minus_x: uint8_t = (x as uint32_t | minus_x as uint32_t) as uint8_t;
    let mut xnx: uint8_t = (x_or_minus_x as uint32_t >> 7 as libc::c_uint) as uint8_t;
    return (xnx as uint32_t).wrapping_sub(1 as libc::c_uint) as uint8_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HPKE_Curve51_CP32_SHA512_setupBaseS(
    mut o_pkE: *mut uint8_t,
    mut o_ctx: Hacl_Impl_HPKE_context_s,
    mut skE: *mut uint8_t,
    mut pkR: *mut uint8_t,
    mut infolen: uint32_t,
    mut info: *mut uint8_t,
) -> uint32_t {
    let mut o_shared: [uint8_t; 32] = [
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
    let mut o_pkE1: *mut uint8_t = o_pkE;
    Hacl_Curve25519_51_secret_to_public(o_pkE1, skE);
    let mut res1: uint32_t = 0 as libc::c_uint;
    let mut res0: uint32_t = 0;
    if res1 == 0 as libc::c_uint {
        let mut o_dh: [uint8_t; 32] = [
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
        let mut zeros: [uint8_t; 32] = [
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
        Hacl_Curve25519_51_scalarmult(o_dh.as_mut_ptr(), skE, pkR);
        let mut res2: uint8_t = 255 as libc::c_uint as uint8_t;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < 32 as libc::c_uint {
            let mut uu____0: uint8_t = FStar_UInt8_eq_mask(
                o_dh[i as usize],
                zeros[i as usize],
            );
            res2 = (uu____0 as uint32_t & res2 as uint32_t) as uint8_t;
            i = i.wrapping_add(1);
            i;
        }
        let mut z: uint8_t = res2;
        let mut res: uint32_t = 0;
        if z as libc::c_uint == 255 as libc::c_uint {
            res = 1 as libc::c_uint;
        } else {
            res = 0 as libc::c_uint;
        }
        let mut res20: uint32_t = res;
        let mut o_kemcontext: [uint8_t; 64] = [
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
        if res20 == 0 as libc::c_uint {
            memcpy(
                o_kemcontext.as_mut_ptr() as *mut libc::c_void,
                o_pkE as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut o_pkRm: *mut uint8_t = o_kemcontext
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize);
            let mut o_pkR: *mut uint8_t = o_pkRm;
            memcpy(
                o_pkR as *mut libc::c_void,
                pkR as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut o_dhm: *mut uint8_t = o_dh.as_mut_ptr();
            let mut o_eae_prk: [uint8_t; 32] = [
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
            let mut suite_id_kem: [uint8_t; 5] = [
                0 as libc::c_uint as uint8_t,
                0,
                0,
                0,
                0,
            ];
            let mut uu____1: *mut uint8_t = suite_id_kem.as_mut_ptr();
            *uu____1
                .offset(0 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____1
                .offset(1 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____1
                .offset(2 as libc::c_uint as isize) = 0x4d as libc::c_uint as uint8_t;
            let mut uu____2: *mut uint8_t = suite_id_kem
                .as_mut_ptr()
                .offset(3 as libc::c_uint as isize);
            *uu____2.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            *uu____2.offset(1 as libc::c_uint as isize) = 32 as libc::c_uint as uint8_t;
            let mut empty: *mut uint8_t = suite_id_kem.as_mut_ptr();
            let mut label_eae_prk: [uint8_t; 7] = [
                0x65 as libc::c_uint as uint8_t,
                0x61 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x5f as libc::c_uint as uint8_t,
                0x70 as libc::c_uint as uint8_t,
                0x72 as libc::c_uint as uint8_t,
                0x6b as libc::c_uint as uint8_t,
            ];
            let mut len0: uint32_t = 51 as libc::c_uint;
            if len0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    87 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla = len0 as usize;
            let mut tmp0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
            memset(
                tmp0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut uu____3: *mut uint8_t = tmp0.as_mut_ptr();
            *uu____3
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____3
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____3
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____3
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____3
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____3
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____3
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp0.as_mut_ptr().offset(7 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id_kem.as_mut_ptr() as *const libc::c_void,
                (5 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp0.as_mut_ptr().offset(12 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_eae_prk.as_mut_ptr() as *const libc::c_void,
                (7 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp0.as_mut_ptr().offset(19 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_dhm as *const libc::c_void,
                (32 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_extract_sha2_256(
                o_eae_prk.as_mut_ptr(),
                empty,
                0 as libc::c_uint,
                tmp0.as_mut_ptr(),
                len0,
            );
            let mut label_shared_secret: [uint8_t; 13] = [
                0x73 as libc::c_uint as uint8_t,
                0x68 as libc::c_uint as uint8_t,
                0x61 as libc::c_uint as uint8_t,
                0x72 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x64 as libc::c_uint as uint8_t,
                0x5f as libc::c_uint as uint8_t,
                0x73 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x63 as libc::c_uint as uint8_t,
                0x72 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x74 as libc::c_uint as uint8_t,
            ];
            let mut len: uint32_t = 91 as libc::c_uint;
            if len as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    108 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_0 = len as usize;
            let mut tmp: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
            memset(
                tmp.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            store16(
                tmp.as_mut_ptr(),
                (if 0 != 0 {
                    ((32 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                        | (32 as libc::c_uint as uint16_t as libc::c_uint
                            & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                        as libc::c_int
                } else {
                    _OSSwapInt16(32 as libc::c_uint as uint16_t) as libc::c_int
                }) as __uint16_t,
            );
            let mut uu____4: *mut uint8_t = tmp
                .as_mut_ptr()
                .offset(2 as libc::c_uint as isize);
            *uu____4
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____4
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____4
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____4
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____4
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____4
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____4
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp.as_mut_ptr().offset(9 as libc::c_uint as isize) as *mut libc::c_void,
                suite_id_kem.as_mut_ptr() as *const libc::c_void,
                (5 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp.as_mut_ptr().offset(14 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_shared_secret.as_mut_ptr() as *const libc::c_void,
                (13 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp.as_mut_ptr().offset(27 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_kemcontext.as_mut_ptr() as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_expand_sha2_256(
                o_shared.as_mut_ptr(),
                o_eae_prk.as_mut_ptr(),
                32 as libc::c_uint,
                tmp.as_mut_ptr(),
                len,
                32 as libc::c_uint,
            );
            res0 = 0 as libc::c_uint;
        } else {
            res0 = 1 as libc::c_uint;
        }
    } else {
        res0 = 1 as libc::c_uint;
    }
    if res0 == 0 as libc::c_uint {
        let mut o_context: [uint8_t; 129] = [
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
        ];
        let mut o_secret: [uint8_t; 64] = [
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
        let mut suite_id: [uint8_t; 10] = [
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
        ];
        let mut uu____5: *mut uint8_t = suite_id.as_mut_ptr();
        *uu____5.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____5.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____5.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____5.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        let mut uu____6: *mut uint8_t = suite_id
            .as_mut_ptr()
            .offset(4 as libc::c_uint as isize);
        *uu____6.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        *uu____6.offset(1 as libc::c_uint as isize) = 32 as libc::c_uint as uint8_t;
        let mut uu____7: *mut uint8_t = suite_id
            .as_mut_ptr()
            .offset(6 as libc::c_uint as isize);
        *uu____7.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        *uu____7.offset(1 as libc::c_uint as isize) = 3 as libc::c_uint as uint8_t;
        let mut uu____8: *mut uint8_t = suite_id
            .as_mut_ptr()
            .offset(8 as libc::c_uint as isize);
        *uu____8.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
        *uu____8.offset(1 as libc::c_uint as isize) = 3 as libc::c_uint as uint8_t;
        let mut label_psk_id_hash: [uint8_t; 11] = [
            0x70 as libc::c_uint as uint8_t,
            0x73 as libc::c_uint as uint8_t,
            0x6b as libc::c_uint as uint8_t,
            0x5f as libc::c_uint as uint8_t,
            0x69 as libc::c_uint as uint8_t,
            0x64 as libc::c_uint as uint8_t,
            0x5f as libc::c_uint as uint8_t,
            0x68 as libc::c_uint as uint8_t,
            0x61 as libc::c_uint as uint8_t,
            0x73 as libc::c_uint as uint8_t,
            0x68 as libc::c_uint as uint8_t,
        ];
        let mut o_psk_id_hash: [uint8_t; 64] = [
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
        let mut empty_0: *mut uint8_t = suite_id.as_mut_ptr();
        let mut len0_0: uint32_t = 28 as libc::c_uint;
        if len0_0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8 as *const libc::c_char,
                160 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len0_0 as usize;
        let mut tmp0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            tmp0_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len0_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut uu____9: *mut uint8_t = tmp0_0.as_mut_ptr();
        *uu____9.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____9.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____9.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____9.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        *uu____9.offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
        *uu____9.offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
        *uu____9.offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
        memcpy(
            tmp0_0.as_mut_ptr().offset(7 as libc::c_uint as isize) as *mut libc::c_void,
            suite_id.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp0_0.as_mut_ptr().offset(17 as libc::c_uint as isize) as *mut libc::c_void,
            label_psk_id_hash.as_mut_ptr() as *const libc::c_void,
            (11 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp0_0.as_mut_ptr().offset(28 as libc::c_uint as isize) as *mut libc::c_void,
            empty_0 as *const libc::c_void,
            (0 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_HKDF_extract_sha2_512(
            o_psk_id_hash.as_mut_ptr(),
            empty_0,
            0 as libc::c_uint,
            tmp0_0.as_mut_ptr(),
            len0_0,
        );
        let mut label_info_hash: [uint8_t; 9] = [
            0x69 as libc::c_uint as uint8_t,
            0x6e as libc::c_uint as uint8_t,
            0x66 as libc::c_uint as uint8_t,
            0x6f as libc::c_uint as uint8_t,
            0x5f as libc::c_uint as uint8_t,
            0x68 as libc::c_uint as uint8_t,
            0x61 as libc::c_uint as uint8_t,
            0x73 as libc::c_uint as uint8_t,
            0x68 as libc::c_uint as uint8_t,
        ];
        let mut o_info_hash: [uint8_t; 64] = [
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
        let mut len1: uint32_t = (26 as libc::c_uint).wrapping_add(infolen);
        if len1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8 as *const libc::c_char,
                179 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = len1 as usize;
        let mut tmp1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            tmp1.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut uu____10: *mut uint8_t = tmp1.as_mut_ptr();
        *uu____10.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____10.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____10.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____10.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        *uu____10.offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
        *uu____10.offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
        *uu____10.offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
        memcpy(
            tmp1.as_mut_ptr().offset(7 as libc::c_uint as isize) as *mut libc::c_void,
            suite_id.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp1.as_mut_ptr().offset(17 as libc::c_uint as isize) as *mut libc::c_void,
            label_info_hash.as_mut_ptr() as *const libc::c_void,
            (9 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp1.as_mut_ptr().offset(26 as libc::c_uint as isize) as *mut libc::c_void,
            info as *const libc::c_void,
            (infolen as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_HKDF_extract_sha2_512(
            o_info_hash.as_mut_ptr(),
            empty_0,
            0 as libc::c_uint,
            tmp1.as_mut_ptr(),
            len1,
        );
        o_context[0 as libc::c_uint as usize] = 0 as libc::c_uint as uint8_t;
        memcpy(
            o_context.as_mut_ptr().offset(1 as libc::c_uint as isize)
                as *mut libc::c_void,
            o_psk_id_hash.as_mut_ptr() as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            o_context.as_mut_ptr().offset(65 as libc::c_uint as isize)
                as *mut libc::c_void,
            o_info_hash.as_mut_ptr() as *const libc::c_void,
            (64 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut label_secret: [uint8_t; 6] = [
            0x73 as libc::c_uint as uint8_t,
            0x65 as libc::c_uint as uint8_t,
            0x63 as libc::c_uint as uint8_t,
            0x72 as libc::c_uint as uint8_t,
            0x65 as libc::c_uint as uint8_t,
            0x74 as libc::c_uint as uint8_t,
        ];
        let mut len2: uint32_t = 23 as libc::c_uint;
        if len2 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8 as *const libc::c_char,
                199 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = len2 as usize;
        let mut tmp2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            tmp2.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len2 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        let mut uu____11: *mut uint8_t = tmp2.as_mut_ptr();
        *uu____11.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____11.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____11.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____11.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        *uu____11.offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
        *uu____11.offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
        *uu____11.offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
        memcpy(
            tmp2.as_mut_ptr().offset(7 as libc::c_uint as isize) as *mut libc::c_void,
            suite_id.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp2.as_mut_ptr().offset(17 as libc::c_uint as isize) as *mut libc::c_void,
            label_secret.as_mut_ptr() as *const libc::c_void,
            (6 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp2.as_mut_ptr().offset(23 as libc::c_uint as isize) as *mut libc::c_void,
            empty_0 as *const libc::c_void,
            (0 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_HKDF_extract_sha2_512(
            o_secret.as_mut_ptr(),
            o_shared.as_mut_ptr(),
            32 as libc::c_uint,
            tmp2.as_mut_ptr(),
            len2,
        );
        let mut label_exp: [uint8_t; 3] = [
            0x65 as libc::c_uint as uint8_t,
            0x78 as libc::c_uint as uint8_t,
            0x70 as libc::c_uint as uint8_t,
        ];
        let mut len3: uint32_t = 151 as libc::c_uint;
        if len3 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8 as *const libc::c_char,
                216 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_4 = len3 as usize;
        let mut tmp3: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
        memset(
            tmp3.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len3 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        store16(
            tmp3.as_mut_ptr(),
            (if 0 != 0 {
                ((64 as libc::c_uint as uint16_t as libc::c_uint
                    & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                    | (64 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                    as libc::c_int
            } else {
                _OSSwapInt16(64 as libc::c_uint as uint16_t) as libc::c_int
            }) as __uint16_t,
        );
        let mut uu____12: *mut uint8_t = tmp3
            .as_mut_ptr()
            .offset(2 as libc::c_uint as isize);
        *uu____12.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____12.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____12.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____12.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        *uu____12.offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
        *uu____12.offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
        *uu____12.offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
        memcpy(
            tmp3.as_mut_ptr().offset(9 as libc::c_uint as isize) as *mut libc::c_void,
            suite_id.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp3.as_mut_ptr().offset(19 as libc::c_uint as isize) as *mut libc::c_void,
            label_exp.as_mut_ptr() as *const libc::c_void,
            (3 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp3.as_mut_ptr().offset(22 as libc::c_uint as isize) as *mut libc::c_void,
            o_context.as_mut_ptr() as *const libc::c_void,
            (129 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_HKDF_expand_sha2_512(
            o_ctx.ctx_exporter,
            o_secret.as_mut_ptr(),
            64 as libc::c_uint,
            tmp3.as_mut_ptr(),
            len3,
            64 as libc::c_uint,
        );
        let mut label_key: [uint8_t; 3] = [
            0x6b as libc::c_uint as uint8_t,
            0x65 as libc::c_uint as uint8_t,
            0x79 as libc::c_uint as uint8_t,
        ];
        let mut len4: uint32_t = 151 as libc::c_uint;
        if len4 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8 as *const libc::c_char,
                234 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_5 = len4 as usize;
        let mut tmp4: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
        memset(
            tmp4.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len4 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        store16(
            tmp4.as_mut_ptr(),
            (if 0 != 0 {
                ((32 as libc::c_uint as uint16_t as libc::c_uint
                    & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                    | (32 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                    as libc::c_int
            } else {
                _OSSwapInt16(32 as libc::c_uint as uint16_t) as libc::c_int
            }) as __uint16_t,
        );
        let mut uu____13: *mut uint8_t = tmp4
            .as_mut_ptr()
            .offset(2 as libc::c_uint as isize);
        *uu____13.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____13.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____13.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____13.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        *uu____13.offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
        *uu____13.offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
        *uu____13.offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
        memcpy(
            tmp4.as_mut_ptr().offset(9 as libc::c_uint as isize) as *mut libc::c_void,
            suite_id.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp4.as_mut_ptr().offset(19 as libc::c_uint as isize) as *mut libc::c_void,
            label_key.as_mut_ptr() as *const libc::c_void,
            (3 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp4.as_mut_ptr().offset(22 as libc::c_uint as isize) as *mut libc::c_void,
            o_context.as_mut_ptr() as *const libc::c_void,
            (129 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_HKDF_expand_sha2_512(
            o_ctx.ctx_key,
            o_secret.as_mut_ptr(),
            64 as libc::c_uint,
            tmp4.as_mut_ptr(),
            len4,
            32 as libc::c_uint,
        );
        let mut label_base_nonce: [uint8_t; 10] = [
            0x62 as libc::c_uint as uint8_t,
            0x61 as libc::c_uint as uint8_t,
            0x73 as libc::c_uint as uint8_t,
            0x65 as libc::c_uint as uint8_t,
            0x5f as libc::c_uint as uint8_t,
            0x6e as libc::c_uint as uint8_t,
            0x6f as libc::c_uint as uint8_t,
            0x6e as libc::c_uint as uint8_t,
            0x63 as libc::c_uint as uint8_t,
            0x65 as libc::c_uint as uint8_t,
        ];
        let mut len_0: uint32_t = 158 as libc::c_uint;
        if len_0 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8 as *const libc::c_char,
                254 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_6 = len_0 as usize;
        let mut tmp_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
        memset(
            tmp_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len_0 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        store16(
            tmp_0.as_mut_ptr(),
            (if 0 != 0 {
                ((12 as libc::c_uint as uint16_t as libc::c_uint
                    & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                    | (12 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                    as libc::c_int
            } else {
                _OSSwapInt16(12 as libc::c_uint as uint16_t) as libc::c_int
            }) as __uint16_t,
        );
        let mut uu____14: *mut uint8_t = tmp_0
            .as_mut_ptr()
            .offset(2 as libc::c_uint as isize);
        *uu____14.offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
        *uu____14.offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
        *uu____14.offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
        *uu____14.offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
        *uu____14.offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
        *uu____14.offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
        *uu____14.offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
        memcpy(
            tmp_0.as_mut_ptr().offset(9 as libc::c_uint as isize) as *mut libc::c_void,
            suite_id.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp_0.as_mut_ptr().offset(19 as libc::c_uint as isize) as *mut libc::c_void,
            label_base_nonce.as_mut_ptr() as *const libc::c_void,
            (10 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            tmp_0.as_mut_ptr().offset(29 as libc::c_uint as isize) as *mut libc::c_void,
            o_context.as_mut_ptr() as *const libc::c_void,
            (129 as libc::c_uint as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        Hacl_HKDF_expand_sha2_512(
            o_ctx.ctx_nonce,
            o_secret.as_mut_ptr(),
            64 as libc::c_uint,
            tmp_0.as_mut_ptr(),
            len_0,
            12 as libc::c_uint,
        );
        *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
        return res0;
    }
    return res0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HPKE_Curve51_CP32_SHA512_setupBaseR(
    mut o_ctx: Hacl_Impl_HPKE_context_s,
    mut enc: *mut uint8_t,
    mut skR: *mut uint8_t,
    mut infolen: uint32_t,
    mut info: *mut uint8_t,
) -> uint32_t {
    let mut pkR: [uint8_t; 32] = [
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
    Hacl_Curve25519_51_secret_to_public(pkR.as_mut_ptr(), skR);
    let mut res1: uint32_t = 0 as libc::c_uint;
    let mut shared: [uint8_t; 32] = [
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
    if res1 == 0 as libc::c_uint {
        let mut pkE: *mut uint8_t = enc;
        let mut dh: [uint8_t; 32] = [
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
        let mut zeros: [uint8_t; 32] = [
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
        Hacl_Curve25519_51_scalarmult(dh.as_mut_ptr(), skR, pkE);
        let mut res0: uint8_t = 255 as libc::c_uint as uint8_t;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < 32 as libc::c_uint {
            let mut uu____0: uint8_t = FStar_UInt8_eq_mask(
                dh[i as usize],
                zeros[i as usize],
            );
            res0 = (uu____0 as uint32_t & res0 as uint32_t) as uint8_t;
            i = i.wrapping_add(1);
            i;
        }
        let mut z: uint8_t = res0;
        let mut res: uint32_t = 0;
        if z as libc::c_uint == 255 as libc::c_uint {
            res = 1 as libc::c_uint;
        } else {
            res = 0 as libc::c_uint;
        }
        let mut res11: uint32_t = res;
        let mut res2: uint32_t = 0;
        let mut kemcontext: [uint8_t; 64] = [
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
        if res11 == 0 as libc::c_uint {
            let mut pkRm: *mut uint8_t = kemcontext
                .as_mut_ptr()
                .offset(32 as libc::c_uint as isize);
            let mut pkR1: *mut uint8_t = pkRm;
            Hacl_Curve25519_51_secret_to_public(pkR1, skR);
            let mut res20: uint32_t = 0 as libc::c_uint;
            if res20 == 0 as libc::c_uint {
                memcpy(
                    kemcontext.as_mut_ptr() as *mut libc::c_void,
                    enc as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut dhm: *mut uint8_t = dh.as_mut_ptr();
                let mut o_eae_prk: [uint8_t; 32] = [
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
                let mut suite_id_kem: [uint8_t; 5] = [
                    0 as libc::c_uint as uint8_t,
                    0,
                    0,
                    0,
                    0,
                ];
                let mut uu____1: *mut uint8_t = suite_id_kem.as_mut_ptr();
                *uu____1
                    .offset(
                        0 as libc::c_uint as isize,
                    ) = 0x4b as libc::c_uint as uint8_t;
                *uu____1
                    .offset(
                        1 as libc::c_uint as isize,
                    ) = 0x45 as libc::c_uint as uint8_t;
                *uu____1
                    .offset(
                        2 as libc::c_uint as isize,
                    ) = 0x4d as libc::c_uint as uint8_t;
                let mut uu____2: *mut uint8_t = suite_id_kem
                    .as_mut_ptr()
                    .offset(3 as libc::c_uint as isize);
                *uu____2
                    .offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
                *uu____2
                    .offset(1 as libc::c_uint as isize) = 32 as libc::c_uint as uint8_t;
                let mut empty: *mut uint8_t = suite_id_kem.as_mut_ptr();
                let mut label_eae_prk: [uint8_t; 7] = [
                    0x65 as libc::c_uint as uint8_t,
                    0x61 as libc::c_uint as uint8_t,
                    0x65 as libc::c_uint as uint8_t,
                    0x5f as libc::c_uint as uint8_t,
                    0x70 as libc::c_uint as uint8_t,
                    0x72 as libc::c_uint as uint8_t,
                    0x6b as libc::c_uint as uint8_t,
                ];
                let mut len0: uint32_t = 51 as libc::c_uint;
                if len0 as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                            as *const libc::c_char,
                        336 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla = len0 as usize;
                let mut tmp0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla);
                memset(
                    tmp0.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (len0 as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                let mut uu____3: *mut uint8_t = tmp0.as_mut_ptr();
                *uu____3
                    .offset(
                        0 as libc::c_uint as isize,
                    ) = 0x48 as libc::c_uint as uint8_t;
                *uu____3
                    .offset(
                        1 as libc::c_uint as isize,
                    ) = 0x50 as libc::c_uint as uint8_t;
                *uu____3
                    .offset(
                        2 as libc::c_uint as isize,
                    ) = 0x4b as libc::c_uint as uint8_t;
                *uu____3
                    .offset(
                        3 as libc::c_uint as isize,
                    ) = 0x45 as libc::c_uint as uint8_t;
                *uu____3
                    .offset(
                        4 as libc::c_uint as isize,
                    ) = 0x2d as libc::c_uint as uint8_t;
                *uu____3
                    .offset(
                        5 as libc::c_uint as isize,
                    ) = 0x76 as libc::c_uint as uint8_t;
                *uu____3
                    .offset(
                        6 as libc::c_uint as isize,
                    ) = 0x31 as libc::c_uint as uint8_t;
                memcpy(
                    tmp0.as_mut_ptr().offset(7 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    suite_id_kem.as_mut_ptr() as *const libc::c_void,
                    (5 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                memcpy(
                    tmp0.as_mut_ptr().offset(12 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    label_eae_prk.as_mut_ptr() as *const libc::c_void,
                    (7 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                memcpy(
                    tmp0.as_mut_ptr().offset(19 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    dhm as *const libc::c_void,
                    (32 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                Hacl_HKDF_extract_sha2_256(
                    o_eae_prk.as_mut_ptr(),
                    empty,
                    0 as libc::c_uint,
                    tmp0.as_mut_ptr(),
                    len0,
                );
                let mut label_shared_secret: [uint8_t; 13] = [
                    0x73 as libc::c_uint as uint8_t,
                    0x68 as libc::c_uint as uint8_t,
                    0x61 as libc::c_uint as uint8_t,
                    0x72 as libc::c_uint as uint8_t,
                    0x65 as libc::c_uint as uint8_t,
                    0x64 as libc::c_uint as uint8_t,
                    0x5f as libc::c_uint as uint8_t,
                    0x73 as libc::c_uint as uint8_t,
                    0x65 as libc::c_uint as uint8_t,
                    0x63 as libc::c_uint as uint8_t,
                    0x72 as libc::c_uint as uint8_t,
                    0x65 as libc::c_uint as uint8_t,
                    0x74 as libc::c_uint as uint8_t,
                ];
                let mut len: uint32_t = 91 as libc::c_uint;
                if len as size_t
                    > (18446744073709551615 as libc::c_ulong)
                        .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
                {
                    printf(
                        b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                            as *const u8 as *const libc::c_char,
                        b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                            as *const libc::c_char,
                        358 as libc::c_int,
                    );
                    exit(253 as libc::c_int);
                }
                let vla_0 = len as usize;
                let mut tmp: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_0);
                memset(
                    tmp.as_mut_ptr() as *mut libc::c_void,
                    0 as libc::c_uint as libc::c_int,
                    (len as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                store16(
                    tmp.as_mut_ptr(),
                    (if 0 != 0 {
                        ((32 as libc::c_uint as uint16_t as libc::c_uint
                            & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                            | (32 as libc::c_uint as uint16_t as libc::c_uint
                                & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                            as libc::c_int
                    } else {
                        _OSSwapInt16(32 as libc::c_uint as uint16_t) as libc::c_int
                    }) as __uint16_t,
                );
                let mut uu____4: *mut uint8_t = tmp
                    .as_mut_ptr()
                    .offset(2 as libc::c_uint as isize);
                *uu____4
                    .offset(
                        0 as libc::c_uint as isize,
                    ) = 0x48 as libc::c_uint as uint8_t;
                *uu____4
                    .offset(
                        1 as libc::c_uint as isize,
                    ) = 0x50 as libc::c_uint as uint8_t;
                *uu____4
                    .offset(
                        2 as libc::c_uint as isize,
                    ) = 0x4b as libc::c_uint as uint8_t;
                *uu____4
                    .offset(
                        3 as libc::c_uint as isize,
                    ) = 0x45 as libc::c_uint as uint8_t;
                *uu____4
                    .offset(
                        4 as libc::c_uint as isize,
                    ) = 0x2d as libc::c_uint as uint8_t;
                *uu____4
                    .offset(
                        5 as libc::c_uint as isize,
                    ) = 0x76 as libc::c_uint as uint8_t;
                *uu____4
                    .offset(
                        6 as libc::c_uint as isize,
                    ) = 0x31 as libc::c_uint as uint8_t;
                memcpy(
                    tmp.as_mut_ptr().offset(9 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    suite_id_kem.as_mut_ptr() as *const libc::c_void,
                    (5 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                memcpy(
                    tmp.as_mut_ptr().offset(14 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    label_shared_secret.as_mut_ptr() as *const libc::c_void,
                    (13 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                memcpy(
                    tmp.as_mut_ptr().offset(27 as libc::c_uint as isize)
                        as *mut libc::c_void,
                    kemcontext.as_mut_ptr() as *const libc::c_void,
                    (64 as libc::c_uint as libc::c_ulong)
                        .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
                );
                Hacl_HKDF_expand_sha2_256(
                    shared.as_mut_ptr(),
                    o_eae_prk.as_mut_ptr(),
                    32 as libc::c_uint,
                    tmp.as_mut_ptr(),
                    len,
                    32 as libc::c_uint,
                );
                res2 = 0 as libc::c_uint;
            } else {
                res2 = 1 as libc::c_uint;
            }
        } else {
            res2 = 1 as libc::c_uint;
        }
        if res2 == 0 as libc::c_uint {
            let mut o_context: [uint8_t; 129] = [
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
            ];
            let mut o_secret: [uint8_t; 64] = [
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
            let mut suite_id: [uint8_t; 10] = [
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
            ];
            let mut uu____5: *mut uint8_t = suite_id.as_mut_ptr();
            *uu____5
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____5
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____5
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____5
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            let mut uu____6: *mut uint8_t = suite_id
                .as_mut_ptr()
                .offset(4 as libc::c_uint as isize);
            *uu____6.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            *uu____6.offset(1 as libc::c_uint as isize) = 32 as libc::c_uint as uint8_t;
            let mut uu____7: *mut uint8_t = suite_id
                .as_mut_ptr()
                .offset(6 as libc::c_uint as isize);
            *uu____7.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            *uu____7.offset(1 as libc::c_uint as isize) = 3 as libc::c_uint as uint8_t;
            let mut uu____8: *mut uint8_t = suite_id
                .as_mut_ptr()
                .offset(8 as libc::c_uint as isize);
            *uu____8.offset(0 as libc::c_uint as isize) = 0 as libc::c_uint as uint8_t;
            *uu____8.offset(1 as libc::c_uint as isize) = 3 as libc::c_uint as uint8_t;
            let mut label_psk_id_hash: [uint8_t; 11] = [
                0x70 as libc::c_uint as uint8_t,
                0x73 as libc::c_uint as uint8_t,
                0x6b as libc::c_uint as uint8_t,
                0x5f as libc::c_uint as uint8_t,
                0x69 as libc::c_uint as uint8_t,
                0x64 as libc::c_uint as uint8_t,
                0x5f as libc::c_uint as uint8_t,
                0x68 as libc::c_uint as uint8_t,
                0x61 as libc::c_uint as uint8_t,
                0x73 as libc::c_uint as uint8_t,
                0x68 as libc::c_uint as uint8_t,
            ];
            let mut o_psk_id_hash: [uint8_t; 64] = [
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
            let mut empty_0: *mut uint8_t = suite_id.as_mut_ptr();
            let mut len0_0: uint32_t = 28 as libc::c_uint;
            if len0_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    410 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_1 = len0_0 as usize;
            let mut tmp0_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_1);
            memset(
                tmp0_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len0_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut uu____9: *mut uint8_t = tmp0_0.as_mut_ptr();
            *uu____9
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____9
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____9
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____9
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____9
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____9
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____9
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp0_0.as_mut_ptr().offset(7 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp0_0.as_mut_ptr().offset(17 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_psk_id_hash.as_mut_ptr() as *const libc::c_void,
                (11 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp0_0.as_mut_ptr().offset(28 as libc::c_uint as isize)
                    as *mut libc::c_void,
                empty_0 as *const libc::c_void,
                (0 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_extract_sha2_512(
                o_psk_id_hash.as_mut_ptr(),
                empty_0,
                0 as libc::c_uint,
                tmp0_0.as_mut_ptr(),
                len0_0,
            );
            let mut label_info_hash: [uint8_t; 9] = [
                0x69 as libc::c_uint as uint8_t,
                0x6e as libc::c_uint as uint8_t,
                0x66 as libc::c_uint as uint8_t,
                0x6f as libc::c_uint as uint8_t,
                0x5f as libc::c_uint as uint8_t,
                0x68 as libc::c_uint as uint8_t,
                0x61 as libc::c_uint as uint8_t,
                0x73 as libc::c_uint as uint8_t,
                0x68 as libc::c_uint as uint8_t,
            ];
            let mut o_info_hash: [uint8_t; 64] = [
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
            let mut len1: uint32_t = (26 as libc::c_uint).wrapping_add(infolen);
            if len1 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    429 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_2 = len1 as usize;
            let mut tmp1: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_2);
            memset(
                tmp1.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut uu____10: *mut uint8_t = tmp1.as_mut_ptr();
            *uu____10
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____10
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____10
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____10
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____10
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____10
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____10
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp1.as_mut_ptr().offset(7 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp1.as_mut_ptr().offset(17 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_info_hash.as_mut_ptr() as *const libc::c_void,
                (9 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp1.as_mut_ptr().offset(26 as libc::c_uint as isize)
                    as *mut libc::c_void,
                info as *const libc::c_void,
                (infolen as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_extract_sha2_512(
                o_info_hash.as_mut_ptr(),
                empty_0,
                0 as libc::c_uint,
                tmp1.as_mut_ptr(),
                len1,
            );
            o_context[0 as libc::c_uint as usize] = 0 as libc::c_uint as uint8_t;
            memcpy(
                o_context.as_mut_ptr().offset(1 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_psk_id_hash.as_mut_ptr() as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                o_context.as_mut_ptr().offset(65 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_info_hash.as_mut_ptr() as *const libc::c_void,
                (64 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut label_secret: [uint8_t; 6] = [
                0x73 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x63 as libc::c_uint as uint8_t,
                0x72 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x74 as libc::c_uint as uint8_t,
            ];
            let mut len2: uint32_t = 23 as libc::c_uint;
            if len2 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    449 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_3 = len2 as usize;
            let mut tmp2: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_3);
            memset(
                tmp2.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len2 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            let mut uu____11: *mut uint8_t = tmp2.as_mut_ptr();
            *uu____11
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____11
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____11
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____11
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____11
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____11
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____11
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp2.as_mut_ptr().offset(7 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp2.as_mut_ptr().offset(17 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_secret.as_mut_ptr() as *const libc::c_void,
                (6 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp2.as_mut_ptr().offset(23 as libc::c_uint as isize)
                    as *mut libc::c_void,
                empty_0 as *const libc::c_void,
                (0 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_extract_sha2_512(
                o_secret.as_mut_ptr(),
                shared.as_mut_ptr(),
                32 as libc::c_uint,
                tmp2.as_mut_ptr(),
                len2,
            );
            let mut label_exp: [uint8_t; 3] = [
                0x65 as libc::c_uint as uint8_t,
                0x78 as libc::c_uint as uint8_t,
                0x70 as libc::c_uint as uint8_t,
            ];
            let mut len3: uint32_t = 151 as libc::c_uint;
            if len3 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    466 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_4 = len3 as usize;
            let mut tmp3: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_4);
            memset(
                tmp3.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len3 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            store16(
                tmp3.as_mut_ptr(),
                (if 0 != 0 {
                    ((64 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                        | (64 as libc::c_uint as uint16_t as libc::c_uint
                            & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                        as libc::c_int
                } else {
                    _OSSwapInt16(64 as libc::c_uint as uint16_t) as libc::c_int
                }) as __uint16_t,
            );
            let mut uu____12: *mut uint8_t = tmp3
                .as_mut_ptr()
                .offset(2 as libc::c_uint as isize);
            *uu____12
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____12
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____12
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____12
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____12
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____12
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____12
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp3.as_mut_ptr().offset(9 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp3.as_mut_ptr().offset(19 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_exp.as_mut_ptr() as *const libc::c_void,
                (3 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp3.as_mut_ptr().offset(22 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_context.as_mut_ptr() as *const libc::c_void,
                (129 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_expand_sha2_512(
                o_ctx.ctx_exporter,
                o_secret.as_mut_ptr(),
                64 as libc::c_uint,
                tmp3.as_mut_ptr(),
                len3,
                64 as libc::c_uint,
            );
            let mut label_key: [uint8_t; 3] = [
                0x6b as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x79 as libc::c_uint as uint8_t,
            ];
            let mut len4: uint32_t = 151 as libc::c_uint;
            if len4 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    484 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_5 = len4 as usize;
            let mut tmp4: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_5);
            memset(
                tmp4.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len4 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            store16(
                tmp4.as_mut_ptr(),
                (if 0 != 0 {
                    ((32 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                        | (32 as libc::c_uint as uint16_t as libc::c_uint
                            & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                        as libc::c_int
                } else {
                    _OSSwapInt16(32 as libc::c_uint as uint16_t) as libc::c_int
                }) as __uint16_t,
            );
            let mut uu____13: *mut uint8_t = tmp4
                .as_mut_ptr()
                .offset(2 as libc::c_uint as isize);
            *uu____13
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____13
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____13
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____13
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____13
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____13
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____13
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp4.as_mut_ptr().offset(9 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp4.as_mut_ptr().offset(19 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_key.as_mut_ptr() as *const libc::c_void,
                (3 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp4.as_mut_ptr().offset(22 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_context.as_mut_ptr() as *const libc::c_void,
                (129 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_expand_sha2_512(
                o_ctx.ctx_key,
                o_secret.as_mut_ptr(),
                64 as libc::c_uint,
                tmp4.as_mut_ptr(),
                len4,
                32 as libc::c_uint,
            );
            let mut label_base_nonce: [uint8_t; 10] = [
                0x62 as libc::c_uint as uint8_t,
                0x61 as libc::c_uint as uint8_t,
                0x73 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
                0x5f as libc::c_uint as uint8_t,
                0x6e as libc::c_uint as uint8_t,
                0x6f as libc::c_uint as uint8_t,
                0x6e as libc::c_uint as uint8_t,
                0x63 as libc::c_uint as uint8_t,
                0x65 as libc::c_uint as uint8_t,
            ];
            let mut len_0: uint32_t = 158 as libc::c_uint;
            if len_0 as size_t
                > (18446744073709551615 as libc::c_ulong)
                    .wrapping_div(::core::mem::size_of::<uint8_t>() as libc::c_ulong)
            {
                printf(
                    b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                        as *const u8 as *const libc::c_char,
                    b"Hacl_HPKE_Curve51_CP32_SHA512.c\0" as *const u8
                        as *const libc::c_char,
                    504 as libc::c_int,
                );
                exit(253 as libc::c_int);
            }
            let vla_6 = len_0 as usize;
            let mut tmp_0: Vec::<uint8_t> = ::std::vec::from_elem(0, vla_6);
            memset(
                tmp_0.as_mut_ptr() as *mut libc::c_void,
                0 as libc::c_uint as libc::c_int,
                (len_0 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            store16(
                tmp_0.as_mut_ptr(),
                (if 0 != 0 {
                    ((12 as libc::c_uint as uint16_t as libc::c_uint
                        & 0xff00 as libc::c_uint) >> 8 as libc::c_int
                        | (12 as libc::c_uint as uint16_t as libc::c_uint
                            & 0xff as libc::c_uint) << 8 as libc::c_int) as __uint16_t
                        as libc::c_int
                } else {
                    _OSSwapInt16(12 as libc::c_uint as uint16_t) as libc::c_int
                }) as __uint16_t,
            );
            let mut uu____14: *mut uint8_t = tmp_0
                .as_mut_ptr()
                .offset(2 as libc::c_uint as isize);
            *uu____14
                .offset(0 as libc::c_uint as isize) = 0x48 as libc::c_uint as uint8_t;
            *uu____14
                .offset(1 as libc::c_uint as isize) = 0x50 as libc::c_uint as uint8_t;
            *uu____14
                .offset(2 as libc::c_uint as isize) = 0x4b as libc::c_uint as uint8_t;
            *uu____14
                .offset(3 as libc::c_uint as isize) = 0x45 as libc::c_uint as uint8_t;
            *uu____14
                .offset(4 as libc::c_uint as isize) = 0x2d as libc::c_uint as uint8_t;
            *uu____14
                .offset(5 as libc::c_uint as isize) = 0x76 as libc::c_uint as uint8_t;
            *uu____14
                .offset(6 as libc::c_uint as isize) = 0x31 as libc::c_uint as uint8_t;
            memcpy(
                tmp_0.as_mut_ptr().offset(9 as libc::c_uint as isize)
                    as *mut libc::c_void,
                suite_id.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp_0.as_mut_ptr().offset(19 as libc::c_uint as isize)
                    as *mut libc::c_void,
                label_base_nonce.as_mut_ptr() as *const libc::c_void,
                (10 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            memcpy(
                tmp_0.as_mut_ptr().offset(29 as libc::c_uint as isize)
                    as *mut libc::c_void,
                o_context.as_mut_ptr() as *const libc::c_void,
                (129 as libc::c_uint as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
            );
            Hacl_HKDF_expand_sha2_512(
                o_ctx.ctx_nonce,
                o_secret.as_mut_ptr(),
                64 as libc::c_uint,
                tmp_0.as_mut_ptr(),
                len_0,
                12 as libc::c_uint,
            );
            *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize) = 0 as libc::c_ulonglong;
            return 0 as libc::c_uint;
        }
        return 1 as libc::c_uint;
    }
    return 1 as libc::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HPKE_Curve51_CP32_SHA512_sealBase(
    mut skE: *mut uint8_t,
    mut pkR: *mut uint8_t,
    mut infolen: uint32_t,
    mut info: *mut uint8_t,
    mut aadlen: uint32_t,
    mut aad: *mut uint8_t,
    mut plainlen: uint32_t,
    mut plain: *mut uint8_t,
    mut o_enc: *mut uint8_t,
    mut o_ct: *mut uint8_t,
) -> uint32_t {
    let mut ctx_key: [uint8_t; 32] = [
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
    let mut ctx_nonce: [uint8_t; 12] = [
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
    ];
    let mut ctx_seq: uint64_t = 0 as libc::c_ulonglong;
    let mut ctx_exporter: [uint8_t; 64] = [
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
    let mut o_ctx: Hacl_Impl_HPKE_context_s = {
        let mut init = Hacl_Impl_HPKE_context_s_s {
            ctx_key: ctx_key.as_mut_ptr(),
            ctx_nonce: ctx_nonce.as_mut_ptr(),
            ctx_seq: &mut ctx_seq,
            ctx_exporter: ctx_exporter.as_mut_ptr(),
        };
        init
    };
    let mut res: uint32_t = Hacl_HPKE_Curve51_CP32_SHA512_setupBaseS(
        o_enc,
        o_ctx,
        skE,
        pkR,
        infolen,
        info,
    );
    if res == 0 as libc::c_uint {
        let mut nonce: [uint8_t; 12] = [
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
        ];
        let mut s: uint64_t = *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize);
        let mut enc: [uint8_t; 12] = [
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
        ];
        store64(
            enc.as_mut_ptr().offset(4 as libc::c_uint as isize),
            if 0 != 0 {
                (s & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                    | (s & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                    | (s & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                    | (s & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                    | (s & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                    | (s & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                    | (s & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                    | (s & 0xff as libc::c_ulonglong) << 56 as libc::c_int
            } else {
                _OSSwapInt64(s)
            },
        );
        let mut i: uint32_t = 0 as libc::c_uint;
        let mut xi: uint8_t = enc[i as usize];
        let mut yi: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_0: uint8_t = enc[i as usize];
        let mut yi_0: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_1: uint8_t = enc[i as usize];
        let mut yi_1: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_1 as uint32_t ^ yi_1 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_2: uint8_t = enc[i as usize];
        let mut yi_2: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_2 as uint32_t ^ yi_2 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_3: uint8_t = enc[i as usize];
        let mut yi_3: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_3 as uint32_t ^ yi_3 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_4: uint8_t = enc[i as usize];
        let mut yi_4: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_4 as uint32_t ^ yi_4 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_5: uint8_t = enc[i as usize];
        let mut yi_5: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_5 as uint32_t ^ yi_5 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_6: uint8_t = enc[i as usize];
        let mut yi_6: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_6 as uint32_t ^ yi_6 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_7: uint8_t = enc[i as usize];
        let mut yi_7: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_7 as uint32_t ^ yi_7 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_8: uint8_t = enc[i as usize];
        let mut yi_8: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_8 as uint32_t ^ yi_8 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_9: uint8_t = enc[i as usize];
        let mut yi_9: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_9 as uint32_t ^ yi_9 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_10: uint8_t = enc[i as usize];
        let mut yi_10: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_10 as uint32_t ^ yi_10 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut cipher: *mut uint8_t = o_ct;
        let mut tag: *mut uint8_t = o_ct.offset(plainlen as isize);
        Hacl_AEAD_Chacha20Poly1305_encrypt(
            cipher,
            tag,
            plain,
            plainlen,
            aad,
            aadlen,
            o_ctx.ctx_key,
            nonce.as_mut_ptr(),
        );
        let mut s1: uint64_t = *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize);
        let mut res1: uint32_t = 0;
        if s1 == 18446744073709551615 as libc::c_ulonglong {
            res1 = 1 as libc::c_uint;
        } else {
            let mut s_: uint64_t = s1.wrapping_add(1 as libc::c_ulonglong);
            *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize) = s_;
            res1 = 0 as libc::c_uint;
        }
        let mut res10: uint32_t = res1;
        return res10;
    }
    return 1 as libc::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_HPKE_Curve51_CP32_SHA512_openBase(
    mut pkE: *mut uint8_t,
    mut skR: *mut uint8_t,
    mut infolen: uint32_t,
    mut info: *mut uint8_t,
    mut aadlen: uint32_t,
    mut aad: *mut uint8_t,
    mut ctlen: uint32_t,
    mut ct: *mut uint8_t,
    mut o_pt: *mut uint8_t,
) -> uint32_t {
    let mut ctx_key: [uint8_t; 32] = [
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
    let mut ctx_nonce: [uint8_t; 12] = [
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
    ];
    let mut ctx_seq: uint64_t = 0 as libc::c_ulonglong;
    let mut ctx_exporter: [uint8_t; 64] = [
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
    let mut o_ctx: Hacl_Impl_HPKE_context_s = {
        let mut init = Hacl_Impl_HPKE_context_s_s {
            ctx_key: ctx_key.as_mut_ptr(),
            ctx_nonce: ctx_nonce.as_mut_ptr(),
            ctx_seq: &mut ctx_seq,
            ctx_exporter: ctx_exporter.as_mut_ptr(),
        };
        init
    };
    let mut res: uint32_t = Hacl_HPKE_Curve51_CP32_SHA512_setupBaseR(
        o_ctx,
        pkE,
        skR,
        infolen,
        info,
    );
    if res == 0 as libc::c_uint {
        let mut nonce: [uint8_t; 12] = [
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
        ];
        let mut s: uint64_t = *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize);
        let mut enc: [uint8_t; 12] = [
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
        ];
        store64(
            enc.as_mut_ptr().offset(4 as libc::c_uint as isize),
            if 0 != 0 {
                (s & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                    | (s & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                    | (s & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                    | (s & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                    | (s & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                    | (s & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                    | (s & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                    | (s & 0xff as libc::c_ulonglong) << 56 as libc::c_int
            } else {
                _OSSwapInt64(s)
            },
        );
        let mut i: uint32_t = 0 as libc::c_uint;
        let mut xi: uint8_t = enc[i as usize];
        let mut yi: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_0: uint8_t = enc[i as usize];
        let mut yi_0: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_1: uint8_t = enc[i as usize];
        let mut yi_1: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_1 as uint32_t ^ yi_1 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_2: uint8_t = enc[i as usize];
        let mut yi_2: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_2 as uint32_t ^ yi_2 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_3: uint8_t = enc[i as usize];
        let mut yi_3: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_3 as uint32_t ^ yi_3 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_4: uint8_t = enc[i as usize];
        let mut yi_4: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_4 as uint32_t ^ yi_4 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_5: uint8_t = enc[i as usize];
        let mut yi_5: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_5 as uint32_t ^ yi_5 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_6: uint8_t = enc[i as usize];
        let mut yi_6: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_6 as uint32_t ^ yi_6 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_7: uint8_t = enc[i as usize];
        let mut yi_7: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_7 as uint32_t ^ yi_7 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_8: uint8_t = enc[i as usize];
        let mut yi_8: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_8 as uint32_t ^ yi_8 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_9: uint8_t = enc[i as usize];
        let mut yi_9: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_9 as uint32_t ^ yi_9 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut xi_10: uint8_t = enc[i as usize];
        let mut yi_10: uint8_t = *(o_ctx.ctx_nonce).offset(i as isize);
        nonce[i as usize] = (xi_10 as uint32_t ^ yi_10 as uint32_t) as uint8_t;
        i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
        let mut cipher: *mut uint8_t = ct;
        let mut tag: *mut uint8_t = ct
            .offset(ctlen as isize)
            .offset(-(16 as libc::c_uint as isize));
        let mut res1: uint32_t = Hacl_AEAD_Chacha20Poly1305_decrypt(
            o_pt,
            cipher,
            ctlen.wrapping_sub(16 as libc::c_uint),
            aad,
            aadlen,
            o_ctx.ctx_key,
            nonce.as_mut_ptr(),
            tag,
        );
        if res1 == 0 as libc::c_uint {
            let mut s1: uint64_t = *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize);
            if s1 == 18446744073709551615 as libc::c_ulonglong {
                return 1 as libc::c_uint;
            }
            let mut s_: uint64_t = s1.wrapping_add(1 as libc::c_ulonglong);
            *(o_ctx.ctx_seq).offset(0 as libc::c_uint as isize) = s_;
            return 0 as libc::c_uint;
        }
        return 1 as libc::c_uint;
    }
    return 1 as libc::c_uint;
}
