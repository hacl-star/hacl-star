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
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
    fn Hacl_Bignum_bn_add_mod_n_u32(
        len1: uint32_t,
        n: *mut uint32_t,
        a: *mut uint32_t,
        b: *mut uint32_t,
        res: *mut uint32_t,
    );
    fn Hacl_Bignum_bn_sub_mod_n_u32(
        len1: uint32_t,
        n: *mut uint32_t,
        a: *mut uint32_t,
        b: *mut uint32_t,
        res: *mut uint32_t,
    );
    fn Hacl_Bignum_ModInvLimb_mod_inv_uint32(n0: uint32_t) -> uint32_t;
    fn Hacl_Bignum_Montgomery_bn_check_modulus_u32(
        len: uint32_t,
        n: *mut uint32_t,
    ) -> uint32_t;
    fn Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(
        len: uint32_t,
        nBits: uint32_t,
        n: *mut uint32_t,
        res: *mut uint32_t,
    );
    fn Hacl_Bignum_Montgomery_bn_to_mont_u32(
        len: uint32_t,
        n: *mut uint32_t,
        nInv: uint32_t,
        r2: *mut uint32_t,
        a: *mut uint32_t,
        aM: *mut uint32_t,
    );
    fn Hacl_Bignum_Montgomery_bn_from_mont_u32(
        len: uint32_t,
        n: *mut uint32_t,
        nInv_u64: uint32_t,
        aM: *mut uint32_t,
        a: *mut uint32_t,
    );
    fn Hacl_Bignum_Montgomery_bn_mont_mul_u32(
        len: uint32_t,
        n: *mut uint32_t,
        nInv_u64: uint32_t,
        aM: *mut uint32_t,
        bM: *mut uint32_t,
        resM: *mut uint32_t,
    );
    fn Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
        len: uint32_t,
        n: *mut uint32_t,
        nInv_u64: uint32_t,
        aM: *mut uint32_t,
        resM: *mut uint32_t,
    );
}
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s {
    pub len: uint32_t,
    pub n: *mut uint32_t,
    pub mu: uint32_t,
    pub r2: *mut uint32_t,
}
pub type Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s;
#[inline(never)]
unsafe extern "C" fn FStar_UInt32_eq_mask(mut a: uint32_t, mut b: uint32_t) -> uint32_t {
    let mut x: uint32_t = a ^ b;
    let mut minus_x: uint32_t = (!x).wrapping_add(1 as libc::c_uint);
    let mut x_or_minus_x: uint32_t = x | minus_x;
    let mut xnx: uint32_t = x_or_minus_x >> 31 as libc::c_uint;
    return xnx.wrapping_sub(1 as libc::c_uint);
}
#[inline]
unsafe extern "C" fn Hacl_IntTypes_Intrinsics_sub_borrow_u32(
    mut cin: uint32_t,
    mut x: uint32_t,
    mut y: uint32_t,
    mut r: *mut uint32_t,
) -> uint32_t {
    let mut res: uint64_t = (x as uint64_t)
        .wrapping_sub(y as uint64_t)
        .wrapping_sub(cin as uint64_t);
    let mut c: uint32_t = (res >> 32 as libc::c_uint) as uint32_t & 1 as libc::c_uint;
    *r.offset(0 as libc::c_uint as isize) = res as uint32_t;
    return c;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_top_index_u32(
    mut len: uint32_t,
    mut b: *mut uint32_t,
) -> uint32_t {
    let mut priv_0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < len {
        let mut mask: uint32_t = FStar_UInt32_eq_mask(
            *b.offset(i as isize),
            0 as libc::c_uint,
        );
        priv_0 = mask & priv_0 | !mask & i;
        i = i.wrapping_add(1);
        i;
    }
    return priv_0;
}
#[inline]
unsafe extern "C" fn Hacl_Bignum_Lib_bn_get_bits_u32(
    mut len: uint32_t,
    mut b: *mut uint32_t,
    mut i: uint32_t,
    mut l: uint32_t,
) -> uint32_t {
    let mut i1: uint32_t = i.wrapping_div(32 as libc::c_uint);
    let mut j: uint32_t = i.wrapping_rem(32 as libc::c_uint);
    let mut p1: uint32_t = *b.offset(i1 as isize) >> j;
    let mut ite: uint32_t = 0;
    if i1.wrapping_add(1 as libc::c_uint) < len && (0 as libc::c_uint) < j {
        ite = p1
            | *b.offset(i1.wrapping_add(1 as libc::c_uint) as isize)
                << (32 as libc::c_uint).wrapping_sub(j);
    } else {
        ite = p1;
    }
    return ite & ((1 as libc::c_uint) << l).wrapping_sub(1 as libc::c_uint);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_field_modulus_check(
    mut len: uint32_t,
    mut n: *mut uint32_t,
) -> bool {
    let mut m: uint32_t = Hacl_Bignum_Montgomery_bn_check_modulus_u32(len, n);
    return m == 0xffffffff as libc::c_uint;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_field_init(
    mut len: uint32_t,
    mut n: *mut uint32_t,
) -> *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 {
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            78 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut r2: *mut uint32_t = calloc(
        len as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    if len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            80 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let mut n1: *mut uint32_t = calloc(
        len as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    let mut r21: *mut uint32_t = r2;
    let mut n11: *mut uint32_t = n1;
    memcpy(
        n11 as *mut libc::c_void,
        n as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut nBits: uint32_t = (32 as libc::c_uint)
        .wrapping_mul(Hacl_Bignum_Lib_bn_get_top_index_u32(len, n));
    Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(len, nBits, n, r21);
    let mut mu: uint32_t = Hacl_Bignum_ModInvLimb_mod_inv_uint32(
        *n.offset(0 as libc::c_uint as isize),
    );
    let mut res: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = {
        let mut init = Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s {
            len: len,
            n: n11,
            mu: mu,
            r2: r21,
        };
        init
    };
    let mut buf: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = malloc(
        ::core::mem::size_of::<Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32>()
            as libc::c_ulong,
    ) as *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32;
    *buf.offset(0 as libc::c_uint as isize) = res;
    return buf;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_field_free(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
) {
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    let mut n: *mut uint32_t = uu____0.n;
    let mut r2: *mut uint32_t = uu____0.r2;
    free(n as *mut libc::c_void);
    free(r2 as *mut libc::c_void);
    free(k as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_field_get_len(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
) -> uint32_t {
    return (*k).len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_to_field(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut a: *mut uint32_t,
    mut aM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    Hacl_Bignum_Montgomery_bn_to_mont_u32(
        len1,
        uu____0.n,
        uu____0.mu,
        uu____0.r2,
        a,
        aM,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_from_field(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut a: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    Hacl_Bignum_Montgomery_bn_from_mont_u32(len1, uu____0.n, uu____0.mu, aM, a);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_add(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut bM: *mut uint32_t,
    mut cM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            180 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len1 as usize;
    let mut a_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            183 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla_0 = len1 as usize;
    let mut b_copy: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
    memset(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        a_copy.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        b_copy.as_mut_ptr() as *mut libc::c_void,
        bM as *const libc::c_void,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    Hacl_Bignum_bn_add_mod_n_u32(
        len1,
        uu____0.n,
        a_copy.as_mut_ptr(),
        b_copy.as_mut_ptr(),
        cM,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_sub(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut bM: *mut uint32_t,
    mut cM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    Hacl_Bignum_bn_sub_mod_n_u32(len1, (*k).n, aM, bM, cM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_mul(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut bM: *mut uint32_t,
    mut cM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    Hacl_Bignum_Montgomery_bn_mont_mul_u32(len1, uu____0.n, uu____0.mu, aM, bM, cM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_sqr(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut cM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    Hacl_Bignum_Montgomery_bn_mont_sqr_u32(len1, uu____0.n, uu____0.mu, aM, cM);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_one(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut oneM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    Hacl_Bignum_Montgomery_bn_from_mont_u32(
        len1,
        uu____0.n,
        uu____0.mu,
        uu____0.r2,
        oneM,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_exp_consttime(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    if uu____0.len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            288 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = uu____0.len as usize;
    let mut aMc: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        aMc.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (uu____0.len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aMc.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (uu____0.len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if bBits < 200 as libc::c_uint {
        if len1.wrapping_add(len1) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                294 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len1.wrapping_add(len1) as usize;
        let mut ctx: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            ctx.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1.wrapping_add(len1) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            uu____0.n as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(len1 as isize) as *mut libc::c_void,
            uu____0.r2 as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut sw: uint32_t = 0 as libc::c_uint;
        let mut ctx_n: *mut uint32_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint32_t = ctx.as_mut_ptr().offset(len1 as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(len1, ctx_n, uu____0.mu, ctx_r2, resM);
        let mut i0: uint32_t = 0 as libc::c_uint;
        while i0 < bBits {
            let mut i1: uint32_t = bBits
                .wrapping_sub(i0)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(32 as libc::c_uint);
            let mut j: uint32_t = bBits
                .wrapping_sub(i0)
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_rem(32 as libc::c_uint);
            let mut tmp: uint32_t = *b.offset(i1 as isize);
            let mut bit: uint32_t = tmp >> j & 1 as libc::c_uint;
            let mut sw1: uint32_t = bit ^ sw;
            let mut i: uint32_t = 0 as libc::c_uint;
            while i < len1 {
                let mut dummy: uint32_t = (0 as libc::c_uint).wrapping_sub(sw1)
                    & (*resM.offset(i as isize) ^ *aMc.as_mut_ptr().offset(i as isize));
                *resM.offset(i as isize) = *resM.offset(i as isize) ^ dummy;
                *aMc
                    .as_mut_ptr()
                    .offset(i as isize) = *aMc.as_mut_ptr().offset(i as isize) ^ dummy;
                i = i.wrapping_add(1);
                i;
            }
            let mut ctx_n0: *mut uint32_t = ctx.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_mul_u32(
                len1,
                ctx_n0,
                uu____0.mu,
                aMc.as_mut_ptr(),
                resM,
                aMc.as_mut_ptr(),
            );
            let mut ctx_n1: *mut uint32_t = ctx.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(len1, ctx_n1, uu____0.mu, resM, resM);
            sw = bit;
            i0 = i0.wrapping_add(1);
            i0;
        }
        let mut sw0: uint32_t = sw;
        let mut i_0: uint32_t = 0 as libc::c_uint;
        while i_0 < len1 {
            let mut dummy_0: uint32_t = (0 as libc::c_uint).wrapping_sub(sw0)
                & (*resM.offset(i_0 as isize) ^ *aMc.as_mut_ptr().offset(i_0 as isize));
            *resM.offset(i_0 as isize) = *resM.offset(i_0 as isize) ^ dummy_0;
            *aMc
                .as_mut_ptr()
                .offset(i_0 as isize) = *aMc.as_mut_ptr().offset(i_0 as isize) ^ dummy_0;
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
    } else {
        let mut bLen: uint32_t = 0;
        if bBits == 0 as libc::c_uint {
            bLen = 1 as libc::c_uint;
        } else {
            bLen = bBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(32 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint);
        }
        if len1.wrapping_add(len1) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                341 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len1.wrapping_add(len1) as usize;
        let mut ctx_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            ctx_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1.wrapping_add(len1) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx_0.as_mut_ptr() as *mut libc::c_void,
            uu____0.n as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx_0.as_mut_ptr().offset(len1 as isize) as *mut libc::c_void,
            uu____0.r2 as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if (16 as libc::c_uint).wrapping_mul(len1) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                346 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = (16 as libc::c_uint).wrapping_mul(len1) as usize;
        let mut table: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            table.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            ((16 as libc::c_uint).wrapping_mul(len1) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if len1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                349 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = len1 as usize;
        let mut tmp_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            tmp_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t0: *mut uint32_t = table.as_mut_ptr();
        let mut t1: *mut uint32_t = table.as_mut_ptr().offset(len1 as isize);
        let mut ctx_n0_0: *mut uint32_t = ctx_0.as_mut_ptr();
        let mut ctx_r20: *mut uint32_t = ctx_0.as_mut_ptr().offset(len1 as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(len1, ctx_n0_0, uu____0.mu, ctx_r20, t0);
        memcpy(
            t1 as *mut libc::c_void,
            aMc.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i_1: uint32_t = 0 as libc::c_uint;
        let mut t11: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_0: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_0,
            uu____0.mu,
            t11,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_0: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_0,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_0: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_1: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_1,
            uu____0.mu,
            t11_0,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_0: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_1: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_1,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_0,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_1: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_2: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_2,
            uu____0.mu,
            t11_1,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_1: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_2: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_2,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_1,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_2: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_3: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_3,
            uu____0.mu,
            t11_2,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_2: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_3: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_3,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_2,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_3: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_4: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_4,
            uu____0.mu,
            t11_3,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_3: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_4: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_4,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_3,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_4: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_5: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_5,
            uu____0.mu,
            t11_4,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_4: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_5: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_5,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_4,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_5: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_6: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_6,
            uu____0.mu,
            t11_5,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_5: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_1)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_6: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_6,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_5,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_1)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if bBits.wrapping_rem(4 as libc::c_uint) != 0 as libc::c_uint {
            let mut i0_0: uint32_t = bBits
                .wrapping_div(4 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint);
            let mut bits_c: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
                bLen,
                b,
                i0_0,
                4 as libc::c_uint,
            );
            memcpy(
                resM as *mut libc::c_void,
                table
                    .as_mut_ptr()
                    .offset((0 as libc::c_uint).wrapping_mul(len1) as isize)
                    as *const libc::c_void,
                (len1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut i1_0: uint32_t = 0 as libc::c_uint;
            let mut c: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_2: uint32_t = 0 as libc::c_uint;
            while i_2 < len1 {
                let mut x: uint32_t = c & *res_j.offset(i_2 as isize)
                    | !c & *resM.offset(i_2 as isize);
                let mut os: *mut uint32_t = resM;
                *os.offset(i_2 as isize) = x;
                i_2 = i_2.wrapping_add(1);
                i_2;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_0: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_0: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_3: uint32_t = 0 as libc::c_uint;
            while i_3 < len1 {
                let mut x_0: uint32_t = c_0 & *res_j_0.offset(i_3 as isize)
                    | !c_0 & *resM.offset(i_3 as isize);
                let mut os_0: *mut uint32_t = resM;
                *os_0.offset(i_3 as isize) = x_0;
                i_3 = i_3.wrapping_add(1);
                i_3;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_1: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_1: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_4: uint32_t = 0 as libc::c_uint;
            while i_4 < len1 {
                let mut x_1: uint32_t = c_1 & *res_j_1.offset(i_4 as isize)
                    | !c_1 & *resM.offset(i_4 as isize);
                let mut os_1: *mut uint32_t = resM;
                *os_1.offset(i_4 as isize) = x_1;
                i_4 = i_4.wrapping_add(1);
                i_4;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_2: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_2: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_5: uint32_t = 0 as libc::c_uint;
            while i_5 < len1 {
                let mut x_2: uint32_t = c_2 & *res_j_2.offset(i_5 as isize)
                    | !c_2 & *resM.offset(i_5 as isize);
                let mut os_2: *mut uint32_t = resM;
                *os_2.offset(i_5 as isize) = x_2;
                i_5 = i_5.wrapping_add(1);
                i_5;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_3: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_3: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_6: uint32_t = 0 as libc::c_uint;
            while i_6 < len1 {
                let mut x_3: uint32_t = c_3 & *res_j_3.offset(i_6 as isize)
                    | !c_3 & *resM.offset(i_6 as isize);
                let mut os_3: *mut uint32_t = resM;
                *os_3.offset(i_6 as isize) = x_3;
                i_6 = i_6.wrapping_add(1);
                i_6;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_4: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_4: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_7: uint32_t = 0 as libc::c_uint;
            while i_7 < len1 {
                let mut x_4: uint32_t = c_4 & *res_j_4.offset(i_7 as isize)
                    | !c_4 & *resM.offset(i_7 as isize);
                let mut os_4: *mut uint32_t = resM;
                *os_4.offset(i_7 as isize) = x_4;
                i_7 = i_7.wrapping_add(1);
                i_7;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_5: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_5: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_8: uint32_t = 0 as libc::c_uint;
            while i_8 < len1 {
                let mut x_5: uint32_t = c_5 & *res_j_5.offset(i_8 as isize)
                    | !c_5 & *resM.offset(i_8 as isize);
                let mut os_5: *mut uint32_t = resM;
                *os_5.offset(i_8 as isize) = x_5;
                i_8 = i_8.wrapping_add(1);
                i_8;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_6: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_6: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_9: uint32_t = 0 as libc::c_uint;
            while i_9 < len1 {
                let mut x_6: uint32_t = c_6 & *res_j_6.offset(i_9 as isize)
                    | !c_6 & *resM.offset(i_9 as isize);
                let mut os_6: *mut uint32_t = resM;
                *os_6.offset(i_9 as isize) = x_6;
                i_9 = i_9.wrapping_add(1);
                i_9;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_7: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_7: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_10: uint32_t = 0 as libc::c_uint;
            while i_10 < len1 {
                let mut x_7: uint32_t = c_7 & *res_j_7.offset(i_10 as isize)
                    | !c_7 & *resM.offset(i_10 as isize);
                let mut os_7: *mut uint32_t = resM;
                *os_7.offset(i_10 as isize) = x_7;
                i_10 = i_10.wrapping_add(1);
                i_10;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_8: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_8: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_11: uint32_t = 0 as libc::c_uint;
            while i_11 < len1 {
                let mut x_8: uint32_t = c_8 & *res_j_8.offset(i_11 as isize)
                    | !c_8 & *resM.offset(i_11 as isize);
                let mut os_8: *mut uint32_t = resM;
                *os_8.offset(i_11 as isize) = x_8;
                i_11 = i_11.wrapping_add(1);
                i_11;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_9: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_9: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_12: uint32_t = 0 as libc::c_uint;
            while i_12 < len1 {
                let mut x_9: uint32_t = c_9 & *res_j_9.offset(i_12 as isize)
                    | !c_9 & *resM.offset(i_12 as isize);
                let mut os_9: *mut uint32_t = resM;
                *os_9.offset(i_12 as isize) = x_9;
                i_12 = i_12.wrapping_add(1);
                i_12;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_10: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_10: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_13: uint32_t = 0 as libc::c_uint;
            while i_13 < len1 {
                let mut x_10: uint32_t = c_10 & *res_j_10.offset(i_13 as isize)
                    | !c_10 & *resM.offset(i_13 as isize);
                let mut os_10: *mut uint32_t = resM;
                *os_10.offset(i_13 as isize) = x_10;
                i_13 = i_13.wrapping_add(1);
                i_13;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_11: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_11: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_14: uint32_t = 0 as libc::c_uint;
            while i_14 < len1 {
                let mut x_11: uint32_t = c_11 & *res_j_11.offset(i_14 as isize)
                    | !c_11 & *resM.offset(i_14 as isize);
                let mut os_11: *mut uint32_t = resM;
                *os_11.offset(i_14 as isize) = x_11;
                i_14 = i_14.wrapping_add(1);
                i_14;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_12: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_12: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_15: uint32_t = 0 as libc::c_uint;
            while i_15 < len1 {
                let mut x_12: uint32_t = c_12 & *res_j_12.offset(i_15 as isize)
                    | !c_12 & *resM.offset(i_15 as isize);
                let mut os_12: *mut uint32_t = resM;
                *os_12.offset(i_15 as isize) = x_12;
                i_15 = i_15.wrapping_add(1);
                i_15;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_13: uint32_t = FStar_UInt32_eq_mask(
                bits_c,
                i1_0.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_13: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_16: uint32_t = 0 as libc::c_uint;
            while i_16 < len1 {
                let mut x_13: uint32_t = c_13 & *res_j_13.offset(i_16 as isize)
                    | !c_13 & *resM.offset(i_16 as isize);
                let mut os_13: *mut uint32_t = resM;
                *os_13.offset(i_16 as isize) = x_13;
                i_16 = i_16.wrapping_add(1);
                i_16;
            }
            i1_0 = (i1_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
        } else {
            let mut ctx_n_7: *mut uint32_t = ctx_0.as_mut_ptr();
            let mut ctx_r2_0: *mut uint32_t = ctx_0.as_mut_ptr().offset(len1 as isize);
            Hacl_Bignum_Montgomery_bn_from_mont_u32(
                len1,
                ctx_n_7,
                uu____0.mu,
                ctx_r2_0,
                resM,
            );
        }
        if len1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                395 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_4 = len1 as usize;
        let mut tmp0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_4);
        memset(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i0_1: uint32_t = 0 as libc::c_uint;
        while i0_1 < bBits.wrapping_div(4 as libc::c_uint) {
            let mut i_17: uint32_t = 0 as libc::c_uint;
            let mut ctx_n_8: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_8,
                uu____0.mu,
                resM,
                resM,
            );
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_9: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_9,
                uu____0.mu,
                resM,
                resM,
            );
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_10: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_10,
                uu____0.mu,
                resM,
                resM,
            );
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_11: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_11,
                uu____0.mu,
                resM,
                resM,
            );
            i_17 = (i_17 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut k2: uint32_t = bBits
                .wrapping_sub(bBits.wrapping_rem(4 as libc::c_uint))
                .wrapping_sub((4 as libc::c_uint).wrapping_mul(i0_1))
                .wrapping_sub(4 as libc::c_uint);
            let mut bits_l: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
                bLen,
                b,
                k2,
                4 as libc::c_uint,
            );
            memcpy(
                tmp0.as_mut_ptr() as *mut libc::c_void,
                table
                    .as_mut_ptr()
                    .offset((0 as libc::c_uint).wrapping_mul(len1) as isize)
                    as *const libc::c_void,
                (len1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut i1_1: uint32_t = 0 as libc::c_uint;
            let mut c_14: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_14: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_18: uint32_t = 0 as libc::c_uint;
            while i_18 < len1 {
                let mut x_14: uint32_t = c_14 & *res_j_14.offset(i_18 as isize)
                    | !c_14 & *tmp0.as_mut_ptr().offset(i_18 as isize);
                let mut os_14: *mut uint32_t = tmp0.as_mut_ptr();
                *os_14.offset(i_18 as isize) = x_14;
                i_18 = i_18.wrapping_add(1);
                i_18;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_15: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_15: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_19: uint32_t = 0 as libc::c_uint;
            while i_19 < len1 {
                let mut x_15: uint32_t = c_15 & *res_j_15.offset(i_19 as isize)
                    | !c_15 & *tmp0.as_mut_ptr().offset(i_19 as isize);
                let mut os_15: *mut uint32_t = tmp0.as_mut_ptr();
                *os_15.offset(i_19 as isize) = x_15;
                i_19 = i_19.wrapping_add(1);
                i_19;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_16: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_16: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_20: uint32_t = 0 as libc::c_uint;
            while i_20 < len1 {
                let mut x_16: uint32_t = c_16 & *res_j_16.offset(i_20 as isize)
                    | !c_16 & *tmp0.as_mut_ptr().offset(i_20 as isize);
                let mut os_16: *mut uint32_t = tmp0.as_mut_ptr();
                *os_16.offset(i_20 as isize) = x_16;
                i_20 = i_20.wrapping_add(1);
                i_20;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_17: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_17: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_21: uint32_t = 0 as libc::c_uint;
            while i_21 < len1 {
                let mut x_17: uint32_t = c_17 & *res_j_17.offset(i_21 as isize)
                    | !c_17 & *tmp0.as_mut_ptr().offset(i_21 as isize);
                let mut os_17: *mut uint32_t = tmp0.as_mut_ptr();
                *os_17.offset(i_21 as isize) = x_17;
                i_21 = i_21.wrapping_add(1);
                i_21;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_18: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_18: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_22: uint32_t = 0 as libc::c_uint;
            while i_22 < len1 {
                let mut x_18: uint32_t = c_18 & *res_j_18.offset(i_22 as isize)
                    | !c_18 & *tmp0.as_mut_ptr().offset(i_22 as isize);
                let mut os_18: *mut uint32_t = tmp0.as_mut_ptr();
                *os_18.offset(i_22 as isize) = x_18;
                i_22 = i_22.wrapping_add(1);
                i_22;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_19: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_19: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_23: uint32_t = 0 as libc::c_uint;
            while i_23 < len1 {
                let mut x_19: uint32_t = c_19 & *res_j_19.offset(i_23 as isize)
                    | !c_19 & *tmp0.as_mut_ptr().offset(i_23 as isize);
                let mut os_19: *mut uint32_t = tmp0.as_mut_ptr();
                *os_19.offset(i_23 as isize) = x_19;
                i_23 = i_23.wrapping_add(1);
                i_23;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_20: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_20: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_24: uint32_t = 0 as libc::c_uint;
            while i_24 < len1 {
                let mut x_20: uint32_t = c_20 & *res_j_20.offset(i_24 as isize)
                    | !c_20 & *tmp0.as_mut_ptr().offset(i_24 as isize);
                let mut os_20: *mut uint32_t = tmp0.as_mut_ptr();
                *os_20.offset(i_24 as isize) = x_20;
                i_24 = i_24.wrapping_add(1);
                i_24;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_21: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_21: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_25: uint32_t = 0 as libc::c_uint;
            while i_25 < len1 {
                let mut x_21: uint32_t = c_21 & *res_j_21.offset(i_25 as isize)
                    | !c_21 & *tmp0.as_mut_ptr().offset(i_25 as isize);
                let mut os_21: *mut uint32_t = tmp0.as_mut_ptr();
                *os_21.offset(i_25 as isize) = x_21;
                i_25 = i_25.wrapping_add(1);
                i_25;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_22: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_22: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_26: uint32_t = 0 as libc::c_uint;
            while i_26 < len1 {
                let mut x_22: uint32_t = c_22 & *res_j_22.offset(i_26 as isize)
                    | !c_22 & *tmp0.as_mut_ptr().offset(i_26 as isize);
                let mut os_22: *mut uint32_t = tmp0.as_mut_ptr();
                *os_22.offset(i_26 as isize) = x_22;
                i_26 = i_26.wrapping_add(1);
                i_26;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_23: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_23: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_27: uint32_t = 0 as libc::c_uint;
            while i_27 < len1 {
                let mut x_23: uint32_t = c_23 & *res_j_23.offset(i_27 as isize)
                    | !c_23 & *tmp0.as_mut_ptr().offset(i_27 as isize);
                let mut os_23: *mut uint32_t = tmp0.as_mut_ptr();
                *os_23.offset(i_27 as isize) = x_23;
                i_27 = i_27.wrapping_add(1);
                i_27;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_24: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_24: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_28: uint32_t = 0 as libc::c_uint;
            while i_28 < len1 {
                let mut x_24: uint32_t = c_24 & *res_j_24.offset(i_28 as isize)
                    | !c_24 & *tmp0.as_mut_ptr().offset(i_28 as isize);
                let mut os_24: *mut uint32_t = tmp0.as_mut_ptr();
                *os_24.offset(i_28 as isize) = x_24;
                i_28 = i_28.wrapping_add(1);
                i_28;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_25: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_25: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_29: uint32_t = 0 as libc::c_uint;
            while i_29 < len1 {
                let mut x_25: uint32_t = c_25 & *res_j_25.offset(i_29 as isize)
                    | !c_25 & *tmp0.as_mut_ptr().offset(i_29 as isize);
                let mut os_25: *mut uint32_t = tmp0.as_mut_ptr();
                *os_25.offset(i_29 as isize) = x_25;
                i_29 = i_29.wrapping_add(1);
                i_29;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_26: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_26: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_30: uint32_t = 0 as libc::c_uint;
            while i_30 < len1 {
                let mut x_26: uint32_t = c_26 & *res_j_26.offset(i_30 as isize)
                    | !c_26 & *tmp0.as_mut_ptr().offset(i_30 as isize);
                let mut os_26: *mut uint32_t = tmp0.as_mut_ptr();
                *os_26.offset(i_30 as isize) = x_26;
                i_30 = i_30.wrapping_add(1);
                i_30;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_27: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_27: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_31: uint32_t = 0 as libc::c_uint;
            while i_31 < len1 {
                let mut x_27: uint32_t = c_27 & *res_j_27.offset(i_31 as isize)
                    | !c_27 & *tmp0.as_mut_ptr().offset(i_31 as isize);
                let mut os_27: *mut uint32_t = tmp0.as_mut_ptr();
                *os_27.offset(i_31 as isize) = x_27;
                i_31 = i_31.wrapping_add(1);
                i_31;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut c_28: uint32_t = FStar_UInt32_eq_mask(
                bits_l,
                i1_1.wrapping_add(1 as libc::c_uint),
            );
            let mut res_j_28: *const uint32_t = table
                .as_mut_ptr()
                .offset(
                    i1_1.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize,
                );
            let mut i_32: uint32_t = 0 as libc::c_uint;
            while i_32 < len1 {
                let mut x_28: uint32_t = c_28 & *res_j_28.offset(i_32 as isize)
                    | !c_28 & *tmp0.as_mut_ptr().offset(i_32 as isize);
                let mut os_28: *mut uint32_t = tmp0.as_mut_ptr();
                *os_28.offset(i_32 as isize) = x_28;
                i_32 = i_32.wrapping_add(1);
                i_32;
            }
            i1_1 = (i1_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_12: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_mul_u32(
                len1,
                ctx_n_12,
                uu____0.mu,
                resM,
                tmp0.as_mut_ptr(),
                resM,
            );
            i0_1 = i0_1.wrapping_add(1);
            i0_1;
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_exp_vartime(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut bBits: uint32_t,
    mut b: *mut uint32_t,
    mut resM: *mut uint32_t,
) {
    let mut len1: uint32_t = Hacl_GenericField32_field_get_len(k);
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    if uu____0.len as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            457 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = uu____0.len as usize;
    let mut aMc: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        aMc.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (uu____0.len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    memcpy(
        aMc.as_mut_ptr() as *mut libc::c_void,
        aM as *const libc::c_void,
        (uu____0.len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    if bBits < 200 as libc::c_uint {
        if len1.wrapping_add(len1) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                463 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_0 = len1.wrapping_add(len1) as usize;
        let mut ctx: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_0);
        memset(
            ctx.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1.wrapping_add(len1) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr() as *mut libc::c_void,
            uu____0.n as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx.as_mut_ptr().offset(len1 as isize) as *mut libc::c_void,
            uu____0.r2 as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut ctx_n: *mut uint32_t = ctx.as_mut_ptr();
        let mut ctx_r2: *mut uint32_t = ctx.as_mut_ptr().offset(len1 as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(len1, ctx_n, uu____0.mu, ctx_r2, resM);
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < bBits {
            let mut i1: uint32_t = i.wrapping_div(32 as libc::c_uint);
            let mut j: uint32_t = i.wrapping_rem(32 as libc::c_uint);
            let mut tmp: uint32_t = *b.offset(i1 as isize);
            let mut bit: uint32_t = tmp >> j & 1 as libc::c_uint;
            if !(bit == 0 as libc::c_uint) {
                let mut ctx_n0: *mut uint32_t = ctx.as_mut_ptr();
                Hacl_Bignum_Montgomery_bn_mont_mul_u32(
                    len1,
                    ctx_n0,
                    uu____0.mu,
                    resM,
                    aMc.as_mut_ptr(),
                    resM,
                );
            }
            let mut ctx_n0_0: *mut uint32_t = ctx.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n0_0,
                uu____0.mu,
                aMc.as_mut_ptr(),
                aMc.as_mut_ptr(),
            );
            i = i.wrapping_add(1);
            i;
        }
    } else {
        let mut bLen: uint32_t = 0;
        if bBits == 0 as libc::c_uint {
            bLen = 1 as libc::c_uint;
        } else {
            bLen = bBits
                .wrapping_sub(1 as libc::c_uint)
                .wrapping_div(32 as libc::c_uint)
                .wrapping_add(1 as libc::c_uint);
        }
        if len1.wrapping_add(len1) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                497 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_1 = len1.wrapping_add(len1) as usize;
        let mut ctx_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_1);
        memset(
            ctx_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1.wrapping_add(len1) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx_0.as_mut_ptr() as *mut libc::c_void,
            uu____0.n as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        memcpy(
            ctx_0.as_mut_ptr().offset(len1 as isize) as *mut libc::c_void,
            uu____0.r2 as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if (16 as libc::c_uint).wrapping_mul(len1) as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                502 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_2 = (16 as libc::c_uint).wrapping_mul(len1) as usize;
        let mut table: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_2);
        memset(
            table.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            ((16 as libc::c_uint).wrapping_mul(len1) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        if len1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                505 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_3 = len1 as usize;
        let mut tmp_0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_3);
        memset(
            tmp_0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t0: *mut uint32_t = table.as_mut_ptr();
        let mut t1: *mut uint32_t = table.as_mut_ptr().offset(len1 as isize);
        let mut ctx_n0_1: *mut uint32_t = ctx_0.as_mut_ptr();
        let mut ctx_r20: *mut uint32_t = ctx_0.as_mut_ptr().offset(len1 as isize);
        Hacl_Bignum_Montgomery_bn_from_mont_u32(len1, ctx_n0_1, uu____0.mu, ctx_r20, t0);
        memcpy(
            t1 as *mut libc::c_void,
            aMc.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i_0: uint32_t = 0 as libc::c_uint;
        let mut t11: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1,
            uu____0.mu,
            t11,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_0: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_0,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_0: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_0: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_0,
            uu____0.mu,
            t11_0,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_0: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_1: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_1,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_0,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_1: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_1: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_1,
            uu____0.mu,
            t11_1,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_1: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_2: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_2,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_1,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_2: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_2: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_2,
            uu____0.mu,
            t11_2,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_2: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_3: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_3,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_2,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_3: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_3: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_3,
            uu____0.mu,
            t11_3,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_3: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_4: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_4,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_3,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_4: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_4: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_4,
            uu____0.mu,
            t11_4,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_4: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_5: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_5,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_4,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t11_5: *mut uint32_t = table
            .as_mut_ptr()
            .offset(i_0.wrapping_add(1 as libc::c_uint).wrapping_mul(len1) as isize);
        let mut ctx_n1_5: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
            len1,
            ctx_n1_5,
            uu____0.mu,
            t11_5,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(2 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut t2_5: *mut uint32_t = table
            .as_mut_ptr()
            .offset(
                (2 as libc::c_uint)
                    .wrapping_mul(i_0)
                    .wrapping_add(2 as libc::c_uint)
                    .wrapping_mul(len1) as isize,
            );
        let mut ctx_n_6: *mut uint32_t = ctx_0.as_mut_ptr();
        Hacl_Bignum_Montgomery_bn_mont_mul_u32(
            len1,
            ctx_n_6,
            uu____0.mu,
            aMc.as_mut_ptr(),
            t2_5,
            tmp_0.as_mut_ptr(),
        );
        memcpy(
            table
                .as_mut_ptr()
                .offset(
                    (2 as libc::c_uint)
                        .wrapping_mul(i_0)
                        .wrapping_add(3 as libc::c_uint)
                        .wrapping_mul(len1) as isize,
                ) as *mut libc::c_void,
            tmp_0.as_mut_ptr() as *const libc::c_void,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        if bBits.wrapping_rem(4 as libc::c_uint) != 0 as libc::c_uint {
            let mut i_1: uint32_t = bBits
                .wrapping_div(4 as libc::c_uint)
                .wrapping_mul(4 as libc::c_uint);
            let mut bits_c: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
                bLen,
                b,
                i_1,
                4 as libc::c_uint,
            );
            let mut bits_l32: uint32_t = bits_c;
            let mut a_bits_l: *const uint32_t = table
                .as_mut_ptr()
                .offset((bits_l32 * len1) as isize);
            memcpy(
                resM as *mut libc::c_void,
                a_bits_l as *mut uint32_t as *const libc::c_void,
                (len1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
        } else {
            let mut ctx_n_7: *mut uint32_t = ctx_0.as_mut_ptr();
            let mut ctx_r2_0: *mut uint32_t = ctx_0.as_mut_ptr().offset(len1 as isize);
            Hacl_Bignum_Montgomery_bn_from_mont_u32(
                len1,
                ctx_n_7,
                uu____0.mu,
                ctx_r2_0,
                resM,
            );
        }
        if len1 as size_t
            > (18446744073709551615 as libc::c_ulong)
                .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
        {
            printf(
                b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                    as *const u8 as *const libc::c_char,
                b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
                541 as libc::c_int,
            );
            exit(253 as libc::c_int);
        }
        let vla_4 = len1 as usize;
        let mut tmp0: Vec::<uint32_t> = ::std::vec::from_elem(0, vla_4);
        memset(
            tmp0.as_mut_ptr() as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            (len1 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
        );
        let mut i_2: uint32_t = 0 as libc::c_uint;
        while i_2 < bBits.wrapping_div(4 as libc::c_uint) {
            let mut i0: uint32_t = 0 as libc::c_uint;
            let mut ctx_n_8: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_8,
                uu____0.mu,
                resM,
                resM,
            );
            i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_9: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_9,
                uu____0.mu,
                resM,
                resM,
            );
            i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_10: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_10,
                uu____0.mu,
                resM,
                resM,
            );
            i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut ctx_n_11: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
                len1,
                ctx_n_11,
                uu____0.mu,
                resM,
                resM,
            );
            i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
                as uint32_t;
            let mut k2: uint32_t = bBits
                .wrapping_sub(bBits.wrapping_rem(4 as libc::c_uint))
                .wrapping_sub((4 as libc::c_uint).wrapping_mul(i_2))
                .wrapping_sub(4 as libc::c_uint);
            let mut bits_l: uint32_t = Hacl_Bignum_Lib_bn_get_bits_u32(
                bLen,
                b,
                k2,
                4 as libc::c_uint,
            );
            let mut bits_l32_0: uint32_t = bits_l;
            let mut a_bits_l_0: *const uint32_t = table
                .as_mut_ptr()
                .offset((bits_l32_0 * len1) as isize);
            memcpy(
                tmp0.as_mut_ptr() as *mut libc::c_void,
                a_bits_l_0 as *mut uint32_t as *const libc::c_void,
                (len1 as libc::c_ulong)
                    .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
            );
            let mut ctx_n_12: *mut uint32_t = ctx_0.as_mut_ptr();
            Hacl_Bignum_Montgomery_bn_mont_mul_u32(
                len1,
                ctx_n_12,
                uu____0.mu,
                resM,
                tmp0.as_mut_ptr(),
                resM,
            );
            i_2 = i_2.wrapping_add(1);
            i_2;
        }
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_GenericField32_inverse(
    mut k: *mut Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32,
    mut aM: *mut uint32_t,
    mut aInvM: *mut uint32_t,
) {
    let mut uu____0: Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 = *k;
    let mut len1: uint32_t = uu____0.len;
    if len1 as size_t
        > (18446744073709551615 as libc::c_ulong)
            .wrapping_div(::core::mem::size_of::<uint32_t>() as libc::c_ulong)
    {
        printf(
            b"Maximum allocatable size exceeded, aborting before overflow at %s:%d\n\0"
                as *const u8 as *const libc::c_char,
            b"Hacl_GenericField32.c\0" as *const u8 as *const libc::c_char,
            584 as libc::c_int,
        );
        exit(253 as libc::c_int);
    }
    let vla = len1 as usize;
    let mut n2: Vec::<uint32_t> = ::std::vec::from_elem(0, vla);
    memset(
        n2.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (len1 as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut c0: uint32_t = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
        0 as libc::c_uint,
        *(uu____0.n).offset(0 as libc::c_uint as isize),
        2 as libc::c_uint,
        n2.as_mut_ptr(),
    );
    let mut c1: uint32_t = 0;
    if (1 as libc::c_uint) < len1 {
        let mut a1: *mut uint32_t = (uu____0.n).offset(1 as libc::c_uint as isize);
        let mut res1: *mut uint32_t = n2.as_mut_ptr().offset(1 as libc::c_uint as isize);
        let mut c: uint32_t = c0;
        let mut i: uint32_t = 0 as libc::c_uint;
        while i < len1.wrapping_sub(1 as libc::c_uint).wrapping_div(4 as libc::c_uint) {
            let mut t1: uint32_t = *a1
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            let mut res_i0: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize);
            c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
                c,
                t1,
                0 as libc::c_uint,
                res_i0,
            );
            let mut t10: uint32_t = *a1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(1 as libc::c_uint)
                        as isize,
                );
            let mut res_i1: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(1 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
                c,
                t10,
                0 as libc::c_uint,
                res_i1,
            );
            let mut t11: uint32_t = *a1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(2 as libc::c_uint)
                        as isize,
                );
            let mut res_i2: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(2 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
                c,
                t11,
                0 as libc::c_uint,
                res_i2,
            );
            let mut t12: uint32_t = *a1
                .offset(
                    (4 as libc::c_uint).wrapping_mul(i).wrapping_add(3 as libc::c_uint)
                        as isize,
                );
            let mut res_i: *mut uint32_t = res1
                .offset((4 as libc::c_uint).wrapping_mul(i) as isize)
                .offset(3 as libc::c_uint as isize);
            c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
                c,
                t12,
                0 as libc::c_uint,
                res_i,
            );
            i = i.wrapping_add(1);
            i;
        }
        let mut i_0: uint32_t = len1
            .wrapping_sub(1 as libc::c_uint)
            .wrapping_div(4 as libc::c_uint)
            .wrapping_mul(4 as libc::c_uint);
        while i_0 < len1.wrapping_sub(1 as libc::c_uint) {
            let mut t1_0: uint32_t = *a1.offset(i_0 as isize);
            let mut res_i_0: *mut uint32_t = res1.offset(i_0 as isize);
            c = Hacl_IntTypes_Intrinsics_sub_borrow_u32(
                c,
                t1_0,
                0 as libc::c_uint,
                res_i_0,
            );
            i_0 = i_0.wrapping_add(1);
            i_0;
        }
        let mut c10: uint32_t = c;
        c1 = c10;
    } else {
        c1 = c0;
    }
    Hacl_GenericField32_exp_vartime(
        k,
        aM,
        (uu____0.len).wrapping_mul(32 as libc::c_uint),
        n2.as_mut_ptr(),
        aInvM,
    );
}
