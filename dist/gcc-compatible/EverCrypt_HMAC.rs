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
    static mut __stderrp: *mut FILE;
    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;
    fn exit(_: libc::c_int) -> !;
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
    fn Hacl_Hash_SHA2_sha256_init(hash: *mut uint32_t);
    fn Hacl_Hash_SHA2_sha256_update_last(
        totlen: uint64_t,
        len: uint32_t,
        b: *mut uint8_t,
        hash: *mut uint32_t,
    );
    fn Hacl_Hash_SHA2_sha256_finish(st: *mut uint32_t, h: *mut uint8_t);
    fn Hacl_Hash_SHA2_sha512_init(hash: *mut uint64_t);
    fn Hacl_Hash_SHA2_sha512_update_nblocks(
        len: uint32_t,
        b: *mut uint8_t,
        st: *mut uint64_t,
    );
    fn Hacl_Hash_SHA2_sha512_update_last(
        totlen: FStar_UInt128_uint128,
        len: uint32_t,
        b: *mut uint8_t,
        hash: *mut uint64_t,
    );
    fn Hacl_Hash_SHA2_sha512_finish(st: *mut uint64_t, h: *mut uint8_t);
    fn Hacl_Hash_SHA2_sha384_init(hash: *mut uint64_t);
    fn Hacl_Hash_SHA2_sha384_update_nblocks(
        len: uint32_t,
        b: *mut uint8_t,
        st: *mut uint64_t,
    );
    fn Hacl_Hash_SHA2_sha384_update_last(
        totlen: FStar_UInt128_uint128,
        len: uint32_t,
        b: *mut uint8_t,
        st: *mut uint64_t,
    );
    fn Hacl_Hash_SHA2_sha384_finish(st: *mut uint64_t, h: *mut uint8_t);
    fn Hacl_Hash_SHA1_init(s: *mut uint32_t);
    fn Hacl_Hash_SHA1_finish(s: *mut uint32_t, dst: *mut uint8_t);
    fn Hacl_Hash_SHA1_update_multi(
        s: *mut uint32_t,
        blocks: *mut uint8_t,
        n_blocks: uint32_t,
    );
    fn Hacl_Hash_SHA1_update_last(
        s: *mut uint32_t,
        prev_len: uint64_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
    fn Hacl_Hash_SHA1_hash_oneshot(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
    fn Hacl_Hash_Blake2b_hash_with_key(
        output: *mut uint8_t,
        output_len: uint32_t,
        input: *mut uint8_t,
        input_len: uint32_t,
        key: *mut uint8_t,
        key_len: uint32_t,
    );
    fn Hacl_Hash_Blake2b_init(hash: *mut uint64_t, kk: uint32_t, nn: uint32_t);
    fn Hacl_Hash_Blake2b_update_multi(
        len: uint32_t,
        wv: *mut uint64_t,
        hash: *mut uint64_t,
        prev: FStar_UInt128_uint128,
        blocks: *mut uint8_t,
        nb: uint32_t,
    );
    fn Hacl_Hash_Blake2b_update_last(
        len: uint32_t,
        wv: *mut uint64_t,
        hash: *mut uint64_t,
        last_node: bool,
        prev: FStar_UInt128_uint128,
        rem: uint32_t,
        d: *mut uint8_t,
    );
    fn Hacl_Hash_Blake2b_finish(nn: uint32_t, output: *mut uint8_t, hash: *mut uint64_t);
    fn Hacl_Hash_Blake2s_hash_with_key(
        output: *mut uint8_t,
        output_len: uint32_t,
        input: *mut uint8_t,
        input_len: uint32_t,
        key: *mut uint8_t,
        key_len: uint32_t,
    );
    fn Hacl_Hash_Blake2s_init(hash: *mut uint32_t, kk: uint32_t, nn: uint32_t);
    fn Hacl_Hash_Blake2s_update_multi(
        len: uint32_t,
        wv: *mut uint32_t,
        hash: *mut uint32_t,
        prev: uint64_t,
        blocks: *mut uint8_t,
        nb: uint32_t,
    );
    fn Hacl_Hash_Blake2s_update_last(
        len: uint32_t,
        wv: *mut uint32_t,
        hash: *mut uint32_t,
        last_node: bool,
        prev: uint64_t,
        rem: uint32_t,
        d: *mut uint8_t,
    );
    fn Hacl_Hash_Blake2s_finish(nn: uint32_t, output: *mut uint8_t, hash: *mut uint32_t);
    fn EverCrypt_Hash_update_multi_256(
        s: *mut uint32_t,
        blocks: *mut uint8_t,
        n: uint32_t,
    );
    fn EverCrypt_Hash_Incremental_hash_256(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
    );
}
pub type __int64_t = libc::c_longlong;
pub type __darwin_off_t = __int64_t;
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
pub type FStar_UInt128_uint128 = u128;
pub type uint128_t = FStar_UInt128_uint128;
pub type Spec_Hash_Definitions_hash_alg = uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct K___uint32_t_uint32_t_s {
    pub fst: uint32_t,
    pub snd: uint32_t,
}
pub type K___uint32_t_uint32_t = K___uint32_t_uint32_t_s;
#[inline]
unsafe extern "C" fn FStar_UInt128_add(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_add(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_uint64_to_uint128(
    mut x: uint64_t,
) -> FStar_UInt128_uint128 {
    return x as uint128_t;
}
static mut Hacl_Hash_SHA2_h256: [uint32_t; 8] = [
    0x6a09e667 as libc::c_uint,
    0xbb67ae85 as libc::c_uint,
    0x3c6ef372 as libc::c_uint,
    0xa54ff53a as libc::c_uint,
    0x510e527f as libc::c_uint,
    0x9b05688c as libc::c_uint,
    0x1f83d9ab as libc::c_uint,
    0x5be0cd19 as libc::c_uint,
];
static mut Hacl_Hash_SHA2_h384: [uint64_t; 8] = [
    0xcbbb9d5dc1059ed8 as libc::c_ulonglong,
    0x629a292a367cd507 as libc::c_ulonglong,
    0x9159015a3070dd17 as libc::c_ulonglong,
    0x152fecd8f70e5939 as libc::c_ulonglong,
    0x67332667ffc00b31 as libc::c_ulonglong,
    0x8eb44a8768581511 as libc::c_ulonglong,
    0xdb0c2e0d64f98fa7 as libc::c_ulonglong,
    0x47b5481dbefa4fa4 as libc::c_ulonglong,
];
static mut Hacl_Hash_SHA2_h512: [uint64_t; 8] = [
    0x6a09e667f3bcc908 as libc::c_ulonglong,
    0xbb67ae8584caa73b as libc::c_ulonglong,
    0x3c6ef372fe94f82b as libc::c_ulonglong,
    0xa54ff53a5f1d36f1 as libc::c_ulonglong,
    0x510e527fade682d1 as libc::c_ulonglong,
    0x9b05688c2b3e6c1f as libc::c_ulonglong,
    0x1f83d9abfb41bd6b as libc::c_ulonglong,
    0x5be0cd19137e2179 as libc::c_ulonglong,
];
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_is_supported_alg(
    mut uu___: Spec_Hash_Definitions_hash_alg,
) -> bool {
    match uu___ as libc::c_int {
        4 => return 1 as libc::c_int != 0,
        1 => return 1 as libc::c_int != 0,
        2 => return 1 as libc::c_int != 0,
        3 => return 1 as libc::c_int != 0,
        6 => return 1 as libc::c_int != 0,
        7 => return 1 as libc::c_int != 0,
        _ => return 0 as libc::c_int != 0,
    };
}
#[no_mangle]
pub static mut EverCrypt_HMAC_hash_256: Option::<
    unsafe extern "C" fn(*mut uint8_t, *mut uint8_t, uint32_t) -> (),
> = unsafe {
    Some(
        EverCrypt_Hash_Incremental_hash_256
            as unsafe extern "C" fn(*mut uint8_t, *mut uint8_t, uint32_t) -> (),
    )
};
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute_sha1(
    mut dst: *mut uint8_t,
    mut key: *mut uint8_t,
    mut key_len: uint32_t,
    mut data: *mut uint8_t,
    mut data_len: uint32_t,
) {
    let mut key_block: [uint8_t; 64] = [0; 64];
    memset(
        key_block.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut nkey: *mut uint8_t = key_block.as_mut_ptr();
    let mut ite: uint32_t = 0;
    if key_len <= 64 as libc::c_uint {
        ite = key_len;
    } else {
        ite = 20 as libc::c_uint;
    }
    let mut zeroes: *mut uint8_t = key_block.as_mut_ptr().offset(ite as isize);
    if key_len <= 64 as libc::c_uint {
        memcpy(
            nkey as *mut libc::c_void,
            key as *const libc::c_void,
            (key_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    } else {
        Hacl_Hash_SHA1_hash_oneshot(nkey, key, key_len);
    }
    let mut ipad: [uint8_t; 64] = [0; 64];
    memset(
        ipad.as_mut_ptr() as *mut libc::c_void,
        0x36 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 64 as libc::c_uint {
        let mut xi: uint8_t = ipad[i as usize];
        let mut yi: uint8_t = key_block[i as usize];
        ipad[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut opad: [uint8_t; 64] = [0; 64];
    memset(
        opad.as_mut_ptr() as *mut libc::c_void,
        0x5c as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 64 as libc::c_uint {
        let mut xi_0: uint8_t = opad[i_0 as usize];
        let mut yi_0: uint8_t = key_block[i_0 as usize];
        opad[i_0 as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut s: [uint32_t; 5] = [
        0x67452301 as libc::c_uint,
        0xefcdab89 as libc::c_uint,
        0x98badcfe as libc::c_uint,
        0x10325476 as libc::c_uint,
        0xc3d2e1f0 as libc::c_uint,
    ];
    if data_len == 0 as libc::c_uint {
        Hacl_Hash_SHA1_update_last(
            s.as_mut_ptr(),
            0 as libc::c_ulonglong,
            ipad.as_mut_ptr(),
            64 as libc::c_uint,
        );
    } else {
        let mut block_len: uint32_t = 64 as libc::c_uint;
        let mut n_blocks0: uint32_t = data_len / block_len;
        let mut rem0: uint32_t = data_len % block_len;
        let mut scrut: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
            fst: 0,
            snd: 0,
        };
        if n_blocks0 > 0 as libc::c_uint && rem0 == 0 as libc::c_uint {
            let mut n_blocks_: uint32_t = n_blocks0.wrapping_sub(1 as libc::c_uint);
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks_,
                    snd: data_len.wrapping_sub(n_blocks_ * block_len),
                };
                init
            };
        } else {
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks0,
                    snd: rem0,
                };
                init
            };
        }
        let mut n_blocks: uint32_t = scrut.fst;
        let mut rem_len: uint32_t = scrut.snd;
        let mut full_blocks_len: uint32_t = n_blocks * block_len;
        let mut full_blocks: *mut uint8_t = data;
        let mut rem: *mut uint8_t = data.offset(full_blocks_len as isize);
        Hacl_Hash_SHA1_update_multi(
            s.as_mut_ptr(),
            ipad.as_mut_ptr(),
            1 as libc::c_uint,
        );
        Hacl_Hash_SHA1_update_multi(s.as_mut_ptr(), full_blocks, n_blocks);
        Hacl_Hash_SHA1_update_last(
            s.as_mut_ptr(),
            (64 as libc::c_uint as uint64_t).wrapping_add(full_blocks_len as uint64_t),
            rem,
            rem_len,
        );
    }
    let mut dst1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA1_finish(s.as_mut_ptr(), dst1);
    let mut hash1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA1_init(s.as_mut_ptr());
    let mut block_len_0: uint32_t = 64 as libc::c_uint;
    let mut n_blocks0_0: uint32_t = (20 as libc::c_uint).wrapping_div(block_len_0);
    let mut rem0_0: uint32_t = (20 as libc::c_uint).wrapping_rem(block_len_0);
    let mut scrut_0: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
        fst: 0,
        snd: 0,
    };
    if n_blocks0_0 > 0 as libc::c_uint && rem0_0 == 0 as libc::c_uint {
        let mut n_blocks__0: uint32_t = n_blocks0_0.wrapping_sub(1 as libc::c_uint);
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks__0,
                snd: (20 as libc::c_uint).wrapping_sub(n_blocks__0 * block_len_0),
            };
            init
        };
    } else {
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks0_0,
                snd: rem0_0,
            };
            init
        };
    }
    let mut n_blocks_0: uint32_t = scrut_0.fst;
    let mut rem_len_0: uint32_t = scrut_0.snd;
    let mut full_blocks_len_0: uint32_t = n_blocks_0 * block_len_0;
    let mut full_blocks_0: *mut uint8_t = hash1;
    let mut rem_0: *mut uint8_t = hash1.offset(full_blocks_len_0 as isize);
    Hacl_Hash_SHA1_update_multi(s.as_mut_ptr(), opad.as_mut_ptr(), 1 as libc::c_uint);
    Hacl_Hash_SHA1_update_multi(s.as_mut_ptr(), full_blocks_0, n_blocks_0);
    Hacl_Hash_SHA1_update_last(
        s.as_mut_ptr(),
        (64 as libc::c_uint as uint64_t).wrapping_add(full_blocks_len_0 as uint64_t),
        rem_0,
        rem_len_0,
    );
    Hacl_Hash_SHA1_finish(s.as_mut_ptr(), dst);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute_sha2_256(
    mut dst: *mut uint8_t,
    mut key: *mut uint8_t,
    mut key_len: uint32_t,
    mut data: *mut uint8_t,
    mut data_len: uint32_t,
) {
    let mut key_block: [uint8_t; 64] = [0; 64];
    memset(
        key_block.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut nkey: *mut uint8_t = key_block.as_mut_ptr();
    let mut ite: uint32_t = 0;
    if key_len <= 64 as libc::c_uint {
        ite = key_len;
    } else {
        ite = 32 as libc::c_uint;
    }
    let mut zeroes: *mut uint8_t = key_block.as_mut_ptr().offset(ite as isize);
    if key_len <= 64 as libc::c_uint {
        memcpy(
            nkey as *mut libc::c_void,
            key as *const libc::c_void,
            (key_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    } else {
        EverCrypt_HMAC_hash_256.expect("non-null function pointer")(nkey, key, key_len);
    }
    let mut ipad: [uint8_t; 64] = [0; 64];
    memset(
        ipad.as_mut_ptr() as *mut libc::c_void,
        0x36 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 64 as libc::c_uint {
        let mut xi: uint8_t = ipad[i as usize];
        let mut yi: uint8_t = key_block[i as usize];
        ipad[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut opad: [uint8_t; 64] = [0; 64];
    memset(
        opad.as_mut_ptr() as *mut libc::c_void,
        0x5c as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 64 as libc::c_uint {
        let mut xi_0: uint8_t = opad[i_0 as usize];
        let mut yi_0: uint8_t = key_block[i_0 as usize];
        opad[i_0 as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut st: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os: *mut uint32_t = st.as_mut_ptr();
    *os.offset(i_1 as isize) = x;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_0: *mut uint32_t = st.as_mut_ptr();
    *os_0.offset(i_1 as isize) = x_0;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_1: *mut uint32_t = st.as_mut_ptr();
    *os_1.offset(i_1 as isize) = x_1;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_2: *mut uint32_t = st.as_mut_ptr();
    *os_2.offset(i_1 as isize) = x_2;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_3: *mut uint32_t = st.as_mut_ptr();
    *os_3.offset(i_1 as isize) = x_3;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_4: *mut uint32_t = st.as_mut_ptr();
    *os_4.offset(i_1 as isize) = x_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_5: *mut uint32_t = st.as_mut_ptr();
    *os_5.offset(i_1 as isize) = x_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = Hacl_Hash_SHA2_h256[i_1 as usize];
    let mut os_6: *mut uint32_t = st.as_mut_ptr();
    *os_6.offset(i_1 as isize) = x_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut s: *mut uint32_t = st.as_mut_ptr();
    if data_len == 0 as libc::c_uint {
        Hacl_Hash_SHA2_sha256_update_last(
            (0 as libc::c_ulonglong).wrapping_add(64 as libc::c_uint as uint64_t),
            64 as libc::c_uint,
            ipad.as_mut_ptr(),
            s,
        );
    } else {
        let mut block_len: uint32_t = 64 as libc::c_uint;
        let mut n_blocks0: uint32_t = data_len / block_len;
        let mut rem0: uint32_t = data_len % block_len;
        let mut scrut: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
            fst: 0,
            snd: 0,
        };
        if n_blocks0 > 0 as libc::c_uint && rem0 == 0 as libc::c_uint {
            let mut n_blocks_: uint32_t = n_blocks0.wrapping_sub(1 as libc::c_uint);
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks_,
                    snd: data_len.wrapping_sub(n_blocks_ * block_len),
                };
                init
            };
        } else {
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks0,
                    snd: rem0,
                };
                init
            };
        }
        let mut n_blocks: uint32_t = scrut.fst;
        let mut rem_len: uint32_t = scrut.snd;
        let mut full_blocks_len: uint32_t = n_blocks * block_len;
        let mut full_blocks: *mut uint8_t = data;
        let mut rem: *mut uint8_t = data.offset(full_blocks_len as isize);
        EverCrypt_Hash_update_multi_256(s, ipad.as_mut_ptr(), 1 as libc::c_uint);
        EverCrypt_Hash_update_multi_256(s, full_blocks, n_blocks);
        Hacl_Hash_SHA2_sha256_update_last(
            (64 as libc::c_uint as uint64_t)
                .wrapping_add(full_blocks_len as uint64_t)
                .wrapping_add(rem_len as uint64_t),
            rem_len,
            rem,
            s,
        );
    }
    let mut dst1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA2_sha256_finish(s, dst1);
    let mut hash1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA2_sha256_init(s);
    let mut block_len_0: uint32_t = 64 as libc::c_uint;
    let mut n_blocks0_0: uint32_t = (32 as libc::c_uint).wrapping_div(block_len_0);
    let mut rem0_0: uint32_t = (32 as libc::c_uint).wrapping_rem(block_len_0);
    let mut scrut_0: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
        fst: 0,
        snd: 0,
    };
    if n_blocks0_0 > 0 as libc::c_uint && rem0_0 == 0 as libc::c_uint {
        let mut n_blocks__0: uint32_t = n_blocks0_0.wrapping_sub(1 as libc::c_uint);
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks__0,
                snd: (32 as libc::c_uint).wrapping_sub(n_blocks__0 * block_len_0),
            };
            init
        };
    } else {
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks0_0,
                snd: rem0_0,
            };
            init
        };
    }
    let mut n_blocks_0: uint32_t = scrut_0.fst;
    let mut rem_len_0: uint32_t = scrut_0.snd;
    let mut full_blocks_len_0: uint32_t = n_blocks_0 * block_len_0;
    let mut full_blocks_0: *mut uint8_t = hash1;
    let mut rem_0: *mut uint8_t = hash1.offset(full_blocks_len_0 as isize);
    EverCrypt_Hash_update_multi_256(s, opad.as_mut_ptr(), 1 as libc::c_uint);
    EverCrypt_Hash_update_multi_256(s, full_blocks_0, n_blocks_0);
    Hacl_Hash_SHA2_sha256_update_last(
        (64 as libc::c_uint as uint64_t)
            .wrapping_add(full_blocks_len_0 as uint64_t)
            .wrapping_add(rem_len_0 as uint64_t),
        rem_len_0,
        rem_0,
        s,
    );
    Hacl_Hash_SHA2_sha256_finish(s, dst);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute_sha2_384(
    mut dst: *mut uint8_t,
    mut key: *mut uint8_t,
    mut key_len: uint32_t,
    mut data: *mut uint8_t,
    mut data_len: uint32_t,
) {
    let mut key_block: [uint8_t; 128] = [0; 128];
    memset(
        key_block.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut nkey: *mut uint8_t = key_block.as_mut_ptr();
    let mut ite: uint32_t = 0;
    if key_len <= 128 as libc::c_uint {
        ite = key_len;
    } else {
        ite = 48 as libc::c_uint;
    }
    let mut zeroes: *mut uint8_t = key_block.as_mut_ptr().offset(ite as isize);
    if key_len <= 128 as libc::c_uint {
        memcpy(
            nkey as *mut libc::c_void,
            key as *const libc::c_void,
            (key_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    } else {
        Hacl_Hash_SHA2_hash_384(nkey, key, key_len);
    }
    let mut ipad: [uint8_t; 128] = [0; 128];
    memset(
        ipad.as_mut_ptr() as *mut libc::c_void,
        0x36 as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 128 as libc::c_uint {
        let mut xi: uint8_t = ipad[i as usize];
        let mut yi: uint8_t = key_block[i as usize];
        ipad[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut opad: [uint8_t; 128] = [0; 128];
    memset(
        opad.as_mut_ptr() as *mut libc::c_void,
        0x5c as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 128 as libc::c_uint {
        let mut xi_0: uint8_t = opad[i_0 as usize];
        let mut yi_0: uint8_t = key_block[i_0 as usize];
        opad[i_0 as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut st: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os: *mut uint64_t = st.as_mut_ptr();
    *os.offset(i_1 as isize) = x;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_0: *mut uint64_t = st.as_mut_ptr();
    *os_0.offset(i_1 as isize) = x_0;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_1: *mut uint64_t = st.as_mut_ptr();
    *os_1.offset(i_1 as isize) = x_1;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_2: *mut uint64_t = st.as_mut_ptr();
    *os_2.offset(i_1 as isize) = x_2;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_3: *mut uint64_t = st.as_mut_ptr();
    *os_3.offset(i_1 as isize) = x_3;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_4: *mut uint64_t = st.as_mut_ptr();
    *os_4.offset(i_1 as isize) = x_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_5: *mut uint64_t = st.as_mut_ptr();
    *os_5.offset(i_1 as isize) = x_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint64_t = Hacl_Hash_SHA2_h384[i_1 as usize];
    let mut os_6: *mut uint64_t = st.as_mut_ptr();
    *os_6.offset(i_1 as isize) = x_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut s: *mut uint64_t = st.as_mut_ptr();
    if data_len == 0 as libc::c_uint {
        Hacl_Hash_SHA2_sha384_update_last(
            FStar_UInt128_add(
                FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
                FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
            ),
            128 as libc::c_uint,
            ipad.as_mut_ptr(),
            s,
        );
    } else {
        let mut block_len: uint32_t = 128 as libc::c_uint;
        let mut n_blocks0: uint32_t = data_len / block_len;
        let mut rem0: uint32_t = data_len % block_len;
        let mut scrut: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
            fst: 0,
            snd: 0,
        };
        if n_blocks0 > 0 as libc::c_uint && rem0 == 0 as libc::c_uint {
            let mut n_blocks_: uint32_t = n_blocks0.wrapping_sub(1 as libc::c_uint);
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks_,
                    snd: data_len.wrapping_sub(n_blocks_ * block_len),
                };
                init
            };
        } else {
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks0,
                    snd: rem0,
                };
                init
            };
        }
        let mut n_blocks: uint32_t = scrut.fst;
        let mut rem_len: uint32_t = scrut.snd;
        let mut full_blocks_len: uint32_t = n_blocks * block_len;
        let mut full_blocks: *mut uint8_t = data;
        let mut rem: *mut uint8_t = data.offset(full_blocks_len as isize);
        Hacl_Hash_SHA2_sha384_update_nblocks(128 as libc::c_uint, ipad.as_mut_ptr(), s);
        Hacl_Hash_SHA2_sha384_update_nblocks(
            n_blocks.wrapping_mul(128 as libc::c_uint),
            full_blocks,
            s,
        );
        Hacl_Hash_SHA2_sha384_update_last(
            FStar_UInt128_add(
                FStar_UInt128_add(
                    FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
                    FStar_UInt128_uint64_to_uint128(full_blocks_len as uint64_t),
                ),
                FStar_UInt128_uint64_to_uint128(rem_len as uint64_t),
            ),
            rem_len,
            rem,
            s,
        );
    }
    let mut dst1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA2_sha384_finish(s, dst1);
    let mut hash1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA2_sha384_init(s);
    let mut block_len_0: uint32_t = 128 as libc::c_uint;
    let mut n_blocks0_0: uint32_t = (48 as libc::c_uint).wrapping_div(block_len_0);
    let mut rem0_0: uint32_t = (48 as libc::c_uint).wrapping_rem(block_len_0);
    let mut scrut_0: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
        fst: 0,
        snd: 0,
    };
    if n_blocks0_0 > 0 as libc::c_uint && rem0_0 == 0 as libc::c_uint {
        let mut n_blocks__0: uint32_t = n_blocks0_0.wrapping_sub(1 as libc::c_uint);
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks__0,
                snd: (48 as libc::c_uint).wrapping_sub(n_blocks__0 * block_len_0),
            };
            init
        };
    } else {
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks0_0,
                snd: rem0_0,
            };
            init
        };
    }
    let mut n_blocks_0: uint32_t = scrut_0.fst;
    let mut rem_len_0: uint32_t = scrut_0.snd;
    let mut full_blocks_len_0: uint32_t = n_blocks_0 * block_len_0;
    let mut full_blocks_0: *mut uint8_t = hash1;
    let mut rem_0: *mut uint8_t = hash1.offset(full_blocks_len_0 as isize);
    Hacl_Hash_SHA2_sha384_update_nblocks(128 as libc::c_uint, opad.as_mut_ptr(), s);
    Hacl_Hash_SHA2_sha384_update_nblocks(
        n_blocks_0.wrapping_mul(128 as libc::c_uint),
        full_blocks_0,
        s,
    );
    Hacl_Hash_SHA2_sha384_update_last(
        FStar_UInt128_add(
            FStar_UInt128_add(
                FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
                FStar_UInt128_uint64_to_uint128(full_blocks_len_0 as uint64_t),
            ),
            FStar_UInt128_uint64_to_uint128(rem_len_0 as uint64_t),
        ),
        rem_len_0,
        rem_0,
        s,
    );
    Hacl_Hash_SHA2_sha384_finish(s, dst);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute_sha2_512(
    mut dst: *mut uint8_t,
    mut key: *mut uint8_t,
    mut key_len: uint32_t,
    mut data: *mut uint8_t,
    mut data_len: uint32_t,
) {
    let mut key_block: [uint8_t; 128] = [0; 128];
    memset(
        key_block.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut nkey: *mut uint8_t = key_block.as_mut_ptr();
    let mut ite: uint32_t = 0;
    if key_len <= 128 as libc::c_uint {
        ite = key_len;
    } else {
        ite = 64 as libc::c_uint;
    }
    let mut zeroes: *mut uint8_t = key_block.as_mut_ptr().offset(ite as isize);
    if key_len <= 128 as libc::c_uint {
        memcpy(
            nkey as *mut libc::c_void,
            key as *const libc::c_void,
            (key_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    } else {
        Hacl_Hash_SHA2_hash_512(nkey, key, key_len);
    }
    let mut ipad: [uint8_t; 128] = [0; 128];
    memset(
        ipad.as_mut_ptr() as *mut libc::c_void,
        0x36 as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 128 as libc::c_uint {
        let mut xi: uint8_t = ipad[i as usize];
        let mut yi: uint8_t = key_block[i as usize];
        ipad[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut opad: [uint8_t; 128] = [0; 128];
    memset(
        opad.as_mut_ptr() as *mut libc::c_void,
        0x5c as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 128 as libc::c_uint {
        let mut xi_0: uint8_t = opad[i_0 as usize];
        let mut yi_0: uint8_t = key_block[i_0 as usize];
        opad[i_0 as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut st: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os: *mut uint64_t = st.as_mut_ptr();
    *os.offset(i_1 as isize) = x;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_0: *mut uint64_t = st.as_mut_ptr();
    *os_0.offset(i_1 as isize) = x_0;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_1: *mut uint64_t = st.as_mut_ptr();
    *os_1.offset(i_1 as isize) = x_1;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_2: *mut uint64_t = st.as_mut_ptr();
    *os_2.offset(i_1 as isize) = x_2;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_3: *mut uint64_t = st.as_mut_ptr();
    *os_3.offset(i_1 as isize) = x_3;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_4: *mut uint64_t = st.as_mut_ptr();
    *os_4.offset(i_1 as isize) = x_4;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_5: *mut uint64_t = st.as_mut_ptr();
    *os_5.offset(i_1 as isize) = x_5;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint64_t = Hacl_Hash_SHA2_h512[i_1 as usize];
    let mut os_6: *mut uint64_t = st.as_mut_ptr();
    *os_6.offset(i_1 as isize) = x_6;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut s: *mut uint64_t = st.as_mut_ptr();
    if data_len == 0 as libc::c_uint {
        Hacl_Hash_SHA2_sha512_update_last(
            FStar_UInt128_add(
                FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
                FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
            ),
            128 as libc::c_uint,
            ipad.as_mut_ptr(),
            s,
        );
    } else {
        let mut block_len: uint32_t = 128 as libc::c_uint;
        let mut n_blocks0: uint32_t = data_len / block_len;
        let mut rem0: uint32_t = data_len % block_len;
        let mut scrut: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
            fst: 0,
            snd: 0,
        };
        if n_blocks0 > 0 as libc::c_uint && rem0 == 0 as libc::c_uint {
            let mut n_blocks_: uint32_t = n_blocks0.wrapping_sub(1 as libc::c_uint);
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks_,
                    snd: data_len.wrapping_sub(n_blocks_ * block_len),
                };
                init
            };
        } else {
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks0,
                    snd: rem0,
                };
                init
            };
        }
        let mut n_blocks: uint32_t = scrut.fst;
        let mut rem_len: uint32_t = scrut.snd;
        let mut full_blocks_len: uint32_t = n_blocks * block_len;
        let mut full_blocks: *mut uint8_t = data;
        let mut rem: *mut uint8_t = data.offset(full_blocks_len as isize);
        Hacl_Hash_SHA2_sha512_update_nblocks(128 as libc::c_uint, ipad.as_mut_ptr(), s);
        Hacl_Hash_SHA2_sha512_update_nblocks(
            n_blocks.wrapping_mul(128 as libc::c_uint),
            full_blocks,
            s,
        );
        Hacl_Hash_SHA2_sha512_update_last(
            FStar_UInt128_add(
                FStar_UInt128_add(
                    FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
                    FStar_UInt128_uint64_to_uint128(full_blocks_len as uint64_t),
                ),
                FStar_UInt128_uint64_to_uint128(rem_len as uint64_t),
            ),
            rem_len,
            rem,
            s,
        );
    }
    let mut dst1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA2_sha512_finish(s, dst1);
    let mut hash1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_SHA2_sha512_init(s);
    let mut block_len_0: uint32_t = 128 as libc::c_uint;
    let mut n_blocks0_0: uint32_t = (64 as libc::c_uint).wrapping_div(block_len_0);
    let mut rem0_0: uint32_t = (64 as libc::c_uint).wrapping_rem(block_len_0);
    let mut scrut_0: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
        fst: 0,
        snd: 0,
    };
    if n_blocks0_0 > 0 as libc::c_uint && rem0_0 == 0 as libc::c_uint {
        let mut n_blocks__0: uint32_t = n_blocks0_0.wrapping_sub(1 as libc::c_uint);
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks__0,
                snd: (64 as libc::c_uint).wrapping_sub(n_blocks__0 * block_len_0),
            };
            init
        };
    } else {
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks0_0,
                snd: rem0_0,
            };
            init
        };
    }
    let mut n_blocks_0: uint32_t = scrut_0.fst;
    let mut rem_len_0: uint32_t = scrut_0.snd;
    let mut full_blocks_len_0: uint32_t = n_blocks_0 * block_len_0;
    let mut full_blocks_0: *mut uint8_t = hash1;
    let mut rem_0: *mut uint8_t = hash1.offset(full_blocks_len_0 as isize);
    Hacl_Hash_SHA2_sha512_update_nblocks(128 as libc::c_uint, opad.as_mut_ptr(), s);
    Hacl_Hash_SHA2_sha512_update_nblocks(
        n_blocks_0.wrapping_mul(128 as libc::c_uint),
        full_blocks_0,
        s,
    );
    Hacl_Hash_SHA2_sha512_update_last(
        FStar_UInt128_add(
            FStar_UInt128_add(
                FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
                FStar_UInt128_uint64_to_uint128(full_blocks_len_0 as uint64_t),
            ),
            FStar_UInt128_uint64_to_uint128(rem_len_0 as uint64_t),
        ),
        rem_len_0,
        rem_0,
        s,
    );
    Hacl_Hash_SHA2_sha512_finish(s, dst);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute_blake2s(
    mut dst: *mut uint8_t,
    mut key: *mut uint8_t,
    mut key_len: uint32_t,
    mut data: *mut uint8_t,
    mut data_len: uint32_t,
) {
    let mut key_block: [uint8_t; 64] = [0; 64];
    memset(
        key_block.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut nkey: *mut uint8_t = key_block.as_mut_ptr();
    let mut ite: uint32_t = 0;
    if key_len <= 64 as libc::c_uint {
        ite = key_len;
    } else {
        ite = 32 as libc::c_uint;
    }
    let mut zeroes: *mut uint8_t = key_block.as_mut_ptr().offset(ite as isize);
    if key_len <= 64 as libc::c_uint {
        memcpy(
            nkey as *mut libc::c_void,
            key as *const libc::c_void,
            (key_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    } else {
        Hacl_Hash_Blake2s_hash_with_key(
            nkey,
            32 as libc::c_uint,
            key,
            key_len,
            0 as *mut uint8_t,
            0 as libc::c_uint,
        );
    }
    let mut ipad: [uint8_t; 64] = [0; 64];
    memset(
        ipad.as_mut_ptr() as *mut libc::c_void,
        0x36 as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 64 as libc::c_uint {
        let mut xi: uint8_t = ipad[i as usize];
        let mut yi: uint8_t = key_block[i as usize];
        ipad[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut opad: [uint8_t; 64] = [0; 64];
    memset(
        opad.as_mut_ptr() as *mut libc::c_void,
        0x5c as libc::c_uint as libc::c_int,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 64 as libc::c_uint {
        let mut xi_0: uint8_t = opad[i_0 as usize];
        let mut yi_0: uint8_t = key_block[i_0 as usize];
        opad[i_0 as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut s: [uint32_t; 16] = [
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
    ];
    Hacl_Hash_Blake2s_init(s.as_mut_ptr(), 0 as libc::c_uint, 32 as libc::c_uint);
    let mut s0: *mut uint32_t = s.as_mut_ptr();
    if data_len == 0 as libc::c_uint {
        let mut wv: [uint32_t; 16] = [
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
        ];
        Hacl_Hash_Blake2s_update_last(
            64 as libc::c_uint,
            wv.as_mut_ptr(),
            s0,
            0 as libc::c_int != 0,
            0 as libc::c_ulonglong,
            64 as libc::c_uint,
            ipad.as_mut_ptr(),
        );
    } else {
        let mut block_len: uint32_t = 64 as libc::c_uint;
        let mut n_blocks0: uint32_t = data_len / block_len;
        let mut rem0: uint32_t = data_len % block_len;
        let mut scrut: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
            fst: 0,
            snd: 0,
        };
        if n_blocks0 > 0 as libc::c_uint && rem0 == 0 as libc::c_uint {
            let mut n_blocks_: uint32_t = n_blocks0.wrapping_sub(1 as libc::c_uint);
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks_,
                    snd: data_len.wrapping_sub(n_blocks_ * block_len),
                };
                init
            };
        } else {
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks0,
                    snd: rem0,
                };
                init
            };
        }
        let mut n_blocks: uint32_t = scrut.fst;
        let mut rem_len: uint32_t = scrut.snd;
        let mut full_blocks_len: uint32_t = n_blocks * block_len;
        let mut full_blocks: *mut uint8_t = data;
        let mut rem: *mut uint8_t = data.offset(full_blocks_len as isize);
        let mut wv_0: [uint32_t; 16] = [
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
        ];
        Hacl_Hash_Blake2s_update_multi(
            64 as libc::c_uint,
            wv_0.as_mut_ptr(),
            s0,
            0 as libc::c_ulonglong,
            ipad.as_mut_ptr(),
            1 as libc::c_uint,
        );
        let mut wv0: [uint32_t; 16] = [
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
        ];
        Hacl_Hash_Blake2s_update_multi(
            n_blocks.wrapping_mul(64 as libc::c_uint),
            wv0.as_mut_ptr(),
            s0,
            block_len as uint64_t,
            full_blocks,
            n_blocks,
        );
        let mut wv1: [uint32_t; 16] = [
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
        ];
        Hacl_Hash_Blake2s_update_last(
            rem_len,
            wv1.as_mut_ptr(),
            s0,
            0 as libc::c_int != 0,
            (64 as libc::c_uint as uint64_t).wrapping_add(full_blocks_len as uint64_t),
            rem_len,
            rem,
        );
    }
    let mut dst1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_Blake2s_finish(32 as libc::c_uint, dst1, s0);
    let mut hash1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_Blake2s_init(s0, 0 as libc::c_uint, 32 as libc::c_uint);
    let mut block_len_0: uint32_t = 64 as libc::c_uint;
    let mut n_blocks0_0: uint32_t = (32 as libc::c_uint).wrapping_div(block_len_0);
    let mut rem0_0: uint32_t = (32 as libc::c_uint).wrapping_rem(block_len_0);
    let mut scrut_0: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
        fst: 0,
        snd: 0,
    };
    if n_blocks0_0 > 0 as libc::c_uint && rem0_0 == 0 as libc::c_uint {
        let mut n_blocks__0: uint32_t = n_blocks0_0.wrapping_sub(1 as libc::c_uint);
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks__0,
                snd: (32 as libc::c_uint).wrapping_sub(n_blocks__0 * block_len_0),
            };
            init
        };
    } else {
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks0_0,
                snd: rem0_0,
            };
            init
        };
    }
    let mut n_blocks_0: uint32_t = scrut_0.fst;
    let mut rem_len_0: uint32_t = scrut_0.snd;
    let mut full_blocks_len_0: uint32_t = n_blocks_0 * block_len_0;
    let mut full_blocks_0: *mut uint8_t = hash1;
    let mut rem_0: *mut uint8_t = hash1.offset(full_blocks_len_0 as isize);
    let mut wv_1: [uint32_t; 16] = [
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
    ];
    Hacl_Hash_Blake2s_update_multi(
        64 as libc::c_uint,
        wv_1.as_mut_ptr(),
        s0,
        0 as libc::c_ulonglong,
        opad.as_mut_ptr(),
        1 as libc::c_uint,
    );
    let mut wv0_0: [uint32_t; 16] = [
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
    ];
    Hacl_Hash_Blake2s_update_multi(
        n_blocks_0.wrapping_mul(64 as libc::c_uint),
        wv0_0.as_mut_ptr(),
        s0,
        block_len_0 as uint64_t,
        full_blocks_0,
        n_blocks_0,
    );
    let mut wv1_0: [uint32_t; 16] = [
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
    ];
    Hacl_Hash_Blake2s_update_last(
        rem_len_0,
        wv1_0.as_mut_ptr(),
        s0,
        0 as libc::c_int != 0,
        (64 as libc::c_uint as uint64_t).wrapping_add(full_blocks_len_0 as uint64_t),
        rem_len_0,
        rem_0,
    );
    Hacl_Hash_Blake2s_finish(32 as libc::c_uint, dst, s0);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute_blake2b(
    mut dst: *mut uint8_t,
    mut key: *mut uint8_t,
    mut key_len: uint32_t,
    mut data: *mut uint8_t,
    mut data_len: uint32_t,
) {
    let mut key_block: [uint8_t; 128] = [0; 128];
    memset(
        key_block.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut nkey: *mut uint8_t = key_block.as_mut_ptr();
    let mut ite: uint32_t = 0;
    if key_len <= 128 as libc::c_uint {
        ite = key_len;
    } else {
        ite = 64 as libc::c_uint;
    }
    let mut zeroes: *mut uint8_t = key_block.as_mut_ptr().offset(ite as isize);
    if key_len <= 128 as libc::c_uint {
        memcpy(
            nkey as *mut libc::c_void,
            key as *const libc::c_void,
            (key_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    } else {
        Hacl_Hash_Blake2b_hash_with_key(
            nkey,
            64 as libc::c_uint,
            key,
            key_len,
            0 as *mut uint8_t,
            0 as libc::c_uint,
        );
    }
    let mut ipad: [uint8_t; 128] = [0; 128];
    memset(
        ipad.as_mut_ptr() as *mut libc::c_void,
        0x36 as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < 128 as libc::c_uint {
        let mut xi: uint8_t = ipad[i as usize];
        let mut yi: uint8_t = key_block[i as usize];
        ipad[i as usize] = (xi as uint32_t ^ yi as uint32_t) as uint8_t;
        i = i.wrapping_add(1);
        i;
    }
    let mut opad: [uint8_t; 128] = [0; 128];
    memset(
        opad.as_mut_ptr() as *mut libc::c_void,
        0x5c as libc::c_uint as libc::c_int,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut i_0: uint32_t = 0 as libc::c_uint;
    while i_0 < 128 as libc::c_uint {
        let mut xi_0: uint8_t = opad[i_0 as usize];
        let mut yi_0: uint8_t = key_block[i_0 as usize];
        opad[i_0 as usize] = (xi_0 as uint32_t ^ yi_0 as uint32_t) as uint8_t;
        i_0 = i_0.wrapping_add(1);
        i_0;
    }
    let mut s: [uint64_t; 16] = [
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
    ];
    Hacl_Hash_Blake2b_init(s.as_mut_ptr(), 0 as libc::c_uint, 64 as libc::c_uint);
    let mut s0: *mut uint64_t = s.as_mut_ptr();
    if data_len == 0 as libc::c_uint {
        let mut wv: [uint64_t; 16] = [
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
        ];
        Hacl_Hash_Blake2b_update_last(
            128 as libc::c_uint,
            wv.as_mut_ptr(),
            s0,
            0 as libc::c_int != 0,
            FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
            128 as libc::c_uint,
            ipad.as_mut_ptr(),
        );
    } else {
        let mut block_len: uint32_t = 128 as libc::c_uint;
        let mut n_blocks0: uint32_t = data_len / block_len;
        let mut rem0: uint32_t = data_len % block_len;
        let mut scrut: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
            fst: 0,
            snd: 0,
        };
        if n_blocks0 > 0 as libc::c_uint && rem0 == 0 as libc::c_uint {
            let mut n_blocks_: uint32_t = n_blocks0.wrapping_sub(1 as libc::c_uint);
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks_,
                    snd: data_len.wrapping_sub(n_blocks_ * block_len),
                };
                init
            };
        } else {
            scrut = {
                let mut init = K___uint32_t_uint32_t_s {
                    fst: n_blocks0,
                    snd: rem0,
                };
                init
            };
        }
        let mut n_blocks: uint32_t = scrut.fst;
        let mut rem_len: uint32_t = scrut.snd;
        let mut full_blocks_len: uint32_t = n_blocks * block_len;
        let mut full_blocks: *mut uint8_t = data;
        let mut rem: *mut uint8_t = data.offset(full_blocks_len as isize);
        let mut wv_0: [uint64_t; 16] = [
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
        ];
        Hacl_Hash_Blake2b_update_multi(
            128 as libc::c_uint,
            wv_0.as_mut_ptr(),
            s0,
            FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
            ipad.as_mut_ptr(),
            1 as libc::c_uint,
        );
        let mut wv0: [uint64_t; 16] = [
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
        ];
        Hacl_Hash_Blake2b_update_multi(
            n_blocks.wrapping_mul(128 as libc::c_uint),
            wv0.as_mut_ptr(),
            s0,
            FStar_UInt128_uint64_to_uint128(block_len as uint64_t),
            full_blocks,
            n_blocks,
        );
        let mut wv1: [uint64_t; 16] = [
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
        ];
        Hacl_Hash_Blake2b_update_last(
            rem_len,
            wv1.as_mut_ptr(),
            s0,
            0 as libc::c_int != 0,
            FStar_UInt128_add(
                FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
                FStar_UInt128_uint64_to_uint128(full_blocks_len as uint64_t),
            ),
            rem_len,
            rem,
        );
    }
    let mut dst1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_Blake2b_finish(64 as libc::c_uint, dst1, s0);
    let mut hash1: *mut uint8_t = ipad.as_mut_ptr();
    Hacl_Hash_Blake2b_init(s0, 0 as libc::c_uint, 64 as libc::c_uint);
    let mut block_len_0: uint32_t = 128 as libc::c_uint;
    let mut n_blocks0_0: uint32_t = (64 as libc::c_uint).wrapping_div(block_len_0);
    let mut rem0_0: uint32_t = (64 as libc::c_uint).wrapping_rem(block_len_0);
    let mut scrut_0: K___uint32_t_uint32_t = K___uint32_t_uint32_t_s {
        fst: 0,
        snd: 0,
    };
    if n_blocks0_0 > 0 as libc::c_uint && rem0_0 == 0 as libc::c_uint {
        let mut n_blocks__0: uint32_t = n_blocks0_0.wrapping_sub(1 as libc::c_uint);
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks__0,
                snd: (64 as libc::c_uint).wrapping_sub(n_blocks__0 * block_len_0),
            };
            init
        };
    } else {
        scrut_0 = {
            let mut init = K___uint32_t_uint32_t_s {
                fst: n_blocks0_0,
                snd: rem0_0,
            };
            init
        };
    }
    let mut n_blocks_0: uint32_t = scrut_0.fst;
    let mut rem_len_0: uint32_t = scrut_0.snd;
    let mut full_blocks_len_0: uint32_t = n_blocks_0 * block_len_0;
    let mut full_blocks_0: *mut uint8_t = hash1;
    let mut rem_0: *mut uint8_t = hash1.offset(full_blocks_len_0 as isize);
    let mut wv_1: [uint64_t; 16] = [
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
    ];
    Hacl_Hash_Blake2b_update_multi(
        128 as libc::c_uint,
        wv_1.as_mut_ptr(),
        s0,
        FStar_UInt128_uint64_to_uint128(0 as libc::c_ulonglong),
        opad.as_mut_ptr(),
        1 as libc::c_uint,
    );
    let mut wv0_0: [uint64_t; 16] = [
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
    ];
    Hacl_Hash_Blake2b_update_multi(
        n_blocks_0.wrapping_mul(128 as libc::c_uint),
        wv0_0.as_mut_ptr(),
        s0,
        FStar_UInt128_uint64_to_uint128(block_len_0 as uint64_t),
        full_blocks_0,
        n_blocks_0,
    );
    let mut wv1_0: [uint64_t; 16] = [
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
    ];
    Hacl_Hash_Blake2b_update_last(
        rem_len_0,
        wv1_0.as_mut_ptr(),
        s0,
        0 as libc::c_int != 0,
        FStar_UInt128_add(
            FStar_UInt128_uint64_to_uint128(128 as libc::c_uint as uint64_t),
            FStar_UInt128_uint64_to_uint128(full_blocks_len_0 as uint64_t),
        ),
        rem_len_0,
        rem_0,
    );
    Hacl_Hash_Blake2b_finish(64 as libc::c_uint, dst, s0);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_HMAC_compute(
    mut a: Spec_Hash_Definitions_hash_alg,
    mut mac: *mut uint8_t,
    mut key: *mut uint8_t,
    mut keylen: uint32_t,
    mut data: *mut uint8_t,
    mut datalen: uint32_t,
) {
    match a as libc::c_int {
        4 => {
            EverCrypt_HMAC_compute_sha1(mac, key, keylen, data, datalen);
        }
        1 => {
            EverCrypt_HMAC_compute_sha2_256(mac, key, keylen, data, datalen);
        }
        2 => {
            EverCrypt_HMAC_compute_sha2_384(mac, key, keylen, data, datalen);
        }
        3 => {
            EverCrypt_HMAC_compute_sha2_512(mac, key, keylen, data, datalen);
        }
        6 => {
            EverCrypt_HMAC_compute_blake2s(mac, key, keylen, data, datalen);
        }
        7 => {
            EverCrypt_HMAC_compute_blake2b(mac, key, keylen, data, datalen);
        }
        _ => {
            fprintf(
                __stderrp,
                b"KaRaMeL incomplete match at %s:%d\n\0" as *const u8
                    as *const libc::c_char,
                b"EverCrypt_HMAC.c\0" as *const u8 as *const libc::c_char,
                871 as libc::c_int,
            );
            exit(253 as libc::c_uint as libc::c_int);
        }
    };
}
