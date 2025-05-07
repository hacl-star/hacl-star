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
pub type FStar_UInt128_uint128 = u128;
pub type uint128_t = FStar_UInt128_uint128;
pub type Hacl_Streaming_Types_error_code = uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Streaming_MD_state_32_s {
    pub block_state: *mut uint32_t,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
}
pub type Hacl_Streaming_MD_state_32 = Hacl_Streaming_MD_state_32_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Streaming_MD_state_64_s {
    pub block_state: *mut uint64_t,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
}
pub type Hacl_Streaming_MD_state_64 = Hacl_Streaming_MD_state_64_s;
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
#[inline]
unsafe extern "C" fn store128_be(mut b: *mut uint8_t, mut n: uint128_t) {
    store64(
        b,
        if 0 != 0 {
            ((n >> 64 as libc::c_int) as uint64_t
                & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t
                    & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t
                    & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t
                    & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t
                    & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | ((n >> 64 as libc::c_int) as uint64_t & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64((n >> 64 as libc::c_int) as uint64_t)
        },
    );
    store64(
        b.offset(8 as libc::c_int as isize),
        if 0 != 0 {
            (n as uint64_t & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (n as uint64_t & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (n as uint64_t & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (n as uint64_t & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
                | (n as uint64_t & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (n as uint64_t & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (n as uint64_t & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (n as uint64_t & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(n as uint64_t)
        },
    );
}
#[inline]
unsafe extern "C" fn FStar_UInt128_add(
    mut x: uint128_t,
    mut y: uint128_t,
) -> FStar_UInt128_uint128 {
    return x.wrapping_add(y);
}
#[inline]
unsafe extern "C" fn FStar_UInt128_shift_left(
    mut x: uint128_t,
    mut y: uint32_t,
) -> FStar_UInt128_uint128 {
    return x << y;
}
#[inline]
unsafe extern "C" fn FStar_UInt128_uint64_to_uint128(
    mut x: uint64_t,
) -> FStar_UInt128_uint128 {
    return x as uint128_t;
}
static mut Hacl_Hash_SHA2_h224: [uint32_t; 8] = [
    0xc1059ed8 as libc::c_uint,
    0x367cd507 as libc::c_uint,
    0x3070dd17 as libc::c_uint,
    0xf70e5939 as libc::c_uint,
    0xffc00b31 as libc::c_uint,
    0x68581511 as libc::c_uint,
    0x64f98fa7 as libc::c_uint,
    0xbefa4fa4 as libc::c_uint,
];
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
static mut Hacl_Hash_SHA2_k224_256: [uint32_t; 64] = [
    0x428a2f98 as libc::c_uint,
    0x71374491 as libc::c_uint,
    0xb5c0fbcf as libc::c_uint,
    0xe9b5dba5 as libc::c_uint,
    0x3956c25b as libc::c_uint,
    0x59f111f1 as libc::c_uint,
    0x923f82a4 as libc::c_uint,
    0xab1c5ed5 as libc::c_uint,
    0xd807aa98 as libc::c_uint,
    0x12835b01 as libc::c_uint,
    0x243185be as libc::c_uint,
    0x550c7dc3 as libc::c_uint,
    0x72be5d74 as libc::c_uint,
    0x80deb1fe as libc::c_uint,
    0x9bdc06a7 as libc::c_uint,
    0xc19bf174 as libc::c_uint,
    0xe49b69c1 as libc::c_uint,
    0xefbe4786 as libc::c_uint,
    0xfc19dc6 as libc::c_uint,
    0x240ca1cc as libc::c_uint,
    0x2de92c6f as libc::c_uint,
    0x4a7484aa as libc::c_uint,
    0x5cb0a9dc as libc::c_uint,
    0x76f988da as libc::c_uint,
    0x983e5152 as libc::c_uint,
    0xa831c66d as libc::c_uint,
    0xb00327c8 as libc::c_uint,
    0xbf597fc7 as libc::c_uint,
    0xc6e00bf3 as libc::c_uint,
    0xd5a79147 as libc::c_uint,
    0x6ca6351 as libc::c_uint,
    0x14292967 as libc::c_uint,
    0x27b70a85 as libc::c_uint,
    0x2e1b2138 as libc::c_uint,
    0x4d2c6dfc as libc::c_uint,
    0x53380d13 as libc::c_uint,
    0x650a7354 as libc::c_uint,
    0x766a0abb as libc::c_uint,
    0x81c2c92e as libc::c_uint,
    0x92722c85 as libc::c_uint,
    0xa2bfe8a1 as libc::c_uint,
    0xa81a664b as libc::c_uint,
    0xc24b8b70 as libc::c_uint,
    0xc76c51a3 as libc::c_uint,
    0xd192e819 as libc::c_uint,
    0xd6990624 as libc::c_uint,
    0xf40e3585 as libc::c_uint,
    0x106aa070 as libc::c_uint,
    0x19a4c116 as libc::c_uint,
    0x1e376c08 as libc::c_uint,
    0x2748774c as libc::c_uint,
    0x34b0bcb5 as libc::c_uint,
    0x391c0cb3 as libc::c_uint,
    0x4ed8aa4a as libc::c_uint,
    0x5b9cca4f as libc::c_uint,
    0x682e6ff3 as libc::c_uint,
    0x748f82ee as libc::c_uint,
    0x78a5636f as libc::c_uint,
    0x84c87814 as libc::c_uint,
    0x8cc70208 as libc::c_uint,
    0x90befffa as libc::c_uint,
    0xa4506ceb as libc::c_uint,
    0xbef9a3f7 as libc::c_uint,
    0xc67178f2 as libc::c_uint,
];
static mut Hacl_Hash_SHA2_k384_512: [uint64_t; 80] = [
    0x428a2f98d728ae22 as libc::c_ulonglong,
    0x7137449123ef65cd as libc::c_ulonglong,
    0xb5c0fbcfec4d3b2f as libc::c_ulonglong,
    0xe9b5dba58189dbbc as libc::c_ulonglong,
    0x3956c25bf348b538 as libc::c_ulonglong,
    0x59f111f1b605d019 as libc::c_ulonglong,
    0x923f82a4af194f9b as libc::c_ulonglong,
    0xab1c5ed5da6d8118 as libc::c_ulonglong,
    0xd807aa98a3030242 as libc::c_ulonglong,
    0x12835b0145706fbe as libc::c_ulonglong,
    0x243185be4ee4b28c as libc::c_ulonglong,
    0x550c7dc3d5ffb4e2 as libc::c_ulonglong,
    0x72be5d74f27b896f as libc::c_ulonglong,
    0x80deb1fe3b1696b1 as libc::c_ulonglong,
    0x9bdc06a725c71235 as libc::c_ulonglong,
    0xc19bf174cf692694 as libc::c_ulonglong,
    0xe49b69c19ef14ad2 as libc::c_ulonglong,
    0xefbe4786384f25e3 as libc::c_ulonglong,
    0xfc19dc68b8cd5b5 as libc::c_ulonglong,
    0x240ca1cc77ac9c65 as libc::c_ulonglong,
    0x2de92c6f592b0275 as libc::c_ulonglong,
    0x4a7484aa6ea6e483 as libc::c_ulonglong,
    0x5cb0a9dcbd41fbd4 as libc::c_ulonglong,
    0x76f988da831153b5 as libc::c_ulonglong,
    0x983e5152ee66dfab as libc::c_ulonglong,
    0xa831c66d2db43210 as libc::c_ulonglong,
    0xb00327c898fb213f as libc::c_ulonglong,
    0xbf597fc7beef0ee4 as libc::c_ulonglong,
    0xc6e00bf33da88fc2 as libc::c_ulonglong,
    0xd5a79147930aa725 as libc::c_ulonglong,
    0x6ca6351e003826f as libc::c_ulonglong,
    0x142929670a0e6e70 as libc::c_ulonglong,
    0x27b70a8546d22ffc as libc::c_ulonglong,
    0x2e1b21385c26c926 as libc::c_ulonglong,
    0x4d2c6dfc5ac42aed as libc::c_ulonglong,
    0x53380d139d95b3df as libc::c_ulonglong,
    0x650a73548baf63de as libc::c_ulonglong,
    0x766a0abb3c77b2a8 as libc::c_ulonglong,
    0x81c2c92e47edaee6 as libc::c_ulonglong,
    0x92722c851482353b as libc::c_ulonglong,
    0xa2bfe8a14cf10364 as libc::c_ulonglong,
    0xa81a664bbc423001 as libc::c_ulonglong,
    0xc24b8b70d0f89791 as libc::c_ulonglong,
    0xc76c51a30654be30 as libc::c_ulonglong,
    0xd192e819d6ef5218 as libc::c_ulonglong,
    0xd69906245565a910 as libc::c_ulonglong,
    0xf40e35855771202a as libc::c_ulonglong,
    0x106aa07032bbd1b8 as libc::c_ulonglong,
    0x19a4c116b8d2d0c8 as libc::c_ulonglong,
    0x1e376c085141ab53 as libc::c_ulonglong,
    0x2748774cdf8eeb99 as libc::c_ulonglong,
    0x34b0bcb5e19b48a8 as libc::c_ulonglong,
    0x391c0cb3c5c95a63 as libc::c_ulonglong,
    0x4ed8aa4ae3418acb as libc::c_ulonglong,
    0x5b9cca4f7763e373 as libc::c_ulonglong,
    0x682e6ff3d6b2b8a3 as libc::c_ulonglong,
    0x748f82ee5defb2fc as libc::c_ulonglong,
    0x78a5636f43172f60 as libc::c_ulonglong,
    0x84c87814a1f0ab72 as libc::c_ulonglong,
    0x8cc702081a6439ec as libc::c_ulonglong,
    0x90befffa23631e28 as libc::c_ulonglong,
    0xa4506cebde82bde9 as libc::c_ulonglong,
    0xbef9a3f7b2c67915 as libc::c_ulonglong,
    0xc67178f2e372532b as libc::c_ulonglong,
    0xca273eceea26619c as libc::c_ulonglong,
    0xd186b8c721c0c207 as libc::c_ulonglong,
    0xeada7dd6cde0eb1e as libc::c_ulonglong,
    0xf57d4f7fee6ed178 as libc::c_ulonglong,
    0x6f067aa72176fba as libc::c_ulonglong,
    0xa637dc5a2c898a6 as libc::c_ulonglong,
    0x113f9804bef90dae as libc::c_ulonglong,
    0x1b710b35131c471b as libc::c_ulonglong,
    0x28db77f523047d84 as libc::c_ulonglong,
    0x32caab7b40c72493 as libc::c_ulonglong,
    0x3c9ebe0a15c9bebc as libc::c_ulonglong,
    0x431d67c49c100d4c as libc::c_ulonglong,
    0x4cc5d4becb3e42b6 as libc::c_ulonglong,
    0x597f299cfc657e2a as libc::c_ulonglong,
    0x5fcb6fab3ad6faec as libc::c_ulonglong,
    0x6c44198c4a475817 as libc::c_ulonglong,
];
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha256_init(mut hash: *mut uint32_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os: *mut uint32_t = hash;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_0: *mut uint32_t = hash;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_1: *mut uint32_t = hash;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_2: *mut uint32_t = hash;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_3: *mut uint32_t = hash;
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_4: *mut uint32_t = hash;
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_5: *mut uint32_t = hash;
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = Hacl_Hash_SHA2_h256[i as usize];
    let mut os_6: *mut uint32_t = hash;
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn sha256_update(mut b: *mut uint8_t, mut hash: *mut uint32_t) {
    let mut hash_old: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut ws: [uint32_t; 16] = [
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
    memcpy(
        hash_old.as_mut_ptr() as *mut libc::c_void,
        hash as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint32_t>() as libc::c_ulong),
    );
    let mut b10: *mut uint8_t = b;
    let mut u: uint32_t = if 0 != 0 {
        (load32(b10) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
            | (load32(b10) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10) & 0xff00 as libc::c_uint) << 8 as libc::c_int
            | (load32(b10) & 0xff as libc::c_uint) << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10))
    };
    ws[0 as libc::c_uint as usize] = u;
    let mut u0: uint32_t = if 0 != 0 {
        (load32(b10.offset(4 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(4 as libc::c_uint as isize)) & 0xff0000 as libc::c_uint)
                >> 8 as libc::c_int
            | (load32(b10.offset(4 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(4 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(4 as libc::c_uint as isize)))
    };
    ws[1 as libc::c_uint as usize] = u0;
    let mut u1: uint32_t = if 0 != 0 {
        (load32(b10.offset(8 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(8 as libc::c_uint as isize)) & 0xff0000 as libc::c_uint)
                >> 8 as libc::c_int
            | (load32(b10.offset(8 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(8 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(8 as libc::c_uint as isize)))
    };
    ws[2 as libc::c_uint as usize] = u1;
    let mut u2: uint32_t = if 0 != 0 {
        (load32(b10.offset(12 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(12 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(12 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(12 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(12 as libc::c_uint as isize)))
    };
    ws[3 as libc::c_uint as usize] = u2;
    let mut u3: uint32_t = if 0 != 0 {
        (load32(b10.offset(16 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(16 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(16 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(16 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(16 as libc::c_uint as isize)))
    };
    ws[4 as libc::c_uint as usize] = u3;
    let mut u4: uint32_t = if 0 != 0 {
        (load32(b10.offset(20 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(20 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(20 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(20 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(20 as libc::c_uint as isize)))
    };
    ws[5 as libc::c_uint as usize] = u4;
    let mut u5: uint32_t = if 0 != 0 {
        (load32(b10.offset(24 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(24 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(24 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(24 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(24 as libc::c_uint as isize)))
    };
    ws[6 as libc::c_uint as usize] = u5;
    let mut u6: uint32_t = if 0 != 0 {
        (load32(b10.offset(28 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(28 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(28 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(28 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(28 as libc::c_uint as isize)))
    };
    ws[7 as libc::c_uint as usize] = u6;
    let mut u7: uint32_t = if 0 != 0 {
        (load32(b10.offset(32 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(32 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(32 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(32 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(32 as libc::c_uint as isize)))
    };
    ws[8 as libc::c_uint as usize] = u7;
    let mut u8: uint32_t = if 0 != 0 {
        (load32(b10.offset(36 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(36 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(36 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(36 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(36 as libc::c_uint as isize)))
    };
    ws[9 as libc::c_uint as usize] = u8;
    let mut u9: uint32_t = if 0 != 0 {
        (load32(b10.offset(40 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(40 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(40 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(40 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(40 as libc::c_uint as isize)))
    };
    ws[10 as libc::c_uint as usize] = u9;
    let mut u10: uint32_t = if 0 != 0 {
        (load32(b10.offset(44 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(44 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(44 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(44 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(44 as libc::c_uint as isize)))
    };
    ws[11 as libc::c_uint as usize] = u10;
    let mut u11: uint32_t = if 0 != 0 {
        (load32(b10.offset(48 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(48 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(48 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(48 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(48 as libc::c_uint as isize)))
    };
    ws[12 as libc::c_uint as usize] = u11;
    let mut u12: uint32_t = if 0 != 0 {
        (load32(b10.offset(52 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(52 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(52 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(52 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(52 as libc::c_uint as isize)))
    };
    ws[13 as libc::c_uint as usize] = u12;
    let mut u13: uint32_t = if 0 != 0 {
        (load32(b10.offset(56 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(56 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(56 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(56 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(56 as libc::c_uint as isize)))
    };
    ws[14 as libc::c_uint as usize] = u13;
    let mut u14: uint32_t = if 0 != 0 {
        (load32(b10.offset(60 as libc::c_uint as isize)) & 0xff000000 as libc::c_uint)
            >> 24 as libc::c_int
            | (load32(b10.offset(60 as libc::c_uint as isize))
                & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
            | (load32(b10.offset(60 as libc::c_uint as isize)) & 0xff00 as libc::c_uint)
                << 8 as libc::c_int
            | (load32(b10.offset(60 as libc::c_uint as isize)) & 0xff as libc::c_uint)
                << 24 as libc::c_int
    } else {
        _OSSwapInt32(load32(b10.offset(60 as libc::c_uint as isize)))
    };
    ws[15 as libc::c_uint as usize] = u14;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut k_t: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t: uint32_t = ws[i as usize];
    let mut a0: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t: uint32_t = k_t;
    let mut t1: uint32_t = h02
        .wrapping_add(
            (e0 << 26 as libc::c_uint | e0 >> 6 as libc::c_uint)
                ^ ((e0 << 21 as libc::c_uint | e0 >> 11 as libc::c_uint)
                    ^ (e0 << 7 as libc::c_uint | e0 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0 & f0 ^ !e0 & g0)
        .wrapping_add(k_e_t)
        .wrapping_add(ws_t);
    let mut t2: uint32_t = ((a0 << 30 as libc::c_uint | a0 >> 2 as libc::c_uint)
        ^ ((a0 << 19 as libc::c_uint | a0 >> 13 as libc::c_uint)
            ^ (a0 << 10 as libc::c_uint | a0 >> 22 as libc::c_uint)))
        .wrapping_add(a0 & b0 ^ (a0 & c0 ^ b0 & c0));
    let mut a1: uint32_t = t1.wrapping_add(t2);
    let mut b1: uint32_t = a0;
    let mut c1: uint32_t = b0;
    let mut d1: uint32_t = c0;
    let mut e1: uint32_t = d0.wrapping_add(t1);
    let mut f1: uint32_t = e0;
    let mut g1: uint32_t = f0;
    let mut h12: uint32_t = g0;
    *hash.offset(0 as libc::c_uint as isize) = a1;
    *hash.offset(1 as libc::c_uint as isize) = b1;
    *hash.offset(2 as libc::c_uint as isize) = c1;
    *hash.offset(3 as libc::c_uint as isize) = d1;
    *hash.offset(4 as libc::c_uint as isize) = e1;
    *hash.offset(5 as libc::c_uint as isize) = f1;
    *hash.offset(6 as libc::c_uint as isize) = g1;
    *hash.offset(7 as libc::c_uint as isize) = h12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_0: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_0: uint32_t = ws[i as usize];
    let mut a0_0: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_0: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_0: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_0: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_0: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_0: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_0: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_0: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_0: uint32_t = k_t_0;
    let mut t1_0: uint32_t = h02_0
        .wrapping_add(
            (e0_0 << 26 as libc::c_uint | e0_0 >> 6 as libc::c_uint)
                ^ ((e0_0 << 21 as libc::c_uint | e0_0 >> 11 as libc::c_uint)
                    ^ (e0_0 << 7 as libc::c_uint | e0_0 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_0 & f0_0 ^ !e0_0 & g0_0)
        .wrapping_add(k_e_t_0)
        .wrapping_add(ws_t_0);
    let mut t2_0: uint32_t = ((a0_0 << 30 as libc::c_uint | a0_0 >> 2 as libc::c_uint)
        ^ ((a0_0 << 19 as libc::c_uint | a0_0 >> 13 as libc::c_uint)
            ^ (a0_0 << 10 as libc::c_uint | a0_0 >> 22 as libc::c_uint)))
        .wrapping_add(a0_0 & b0_0 ^ (a0_0 & c0_0 ^ b0_0 & c0_0));
    let mut a1_0: uint32_t = t1_0.wrapping_add(t2_0);
    let mut b1_0: uint32_t = a0_0;
    let mut c1_0: uint32_t = b0_0;
    let mut d1_0: uint32_t = c0_0;
    let mut e1_0: uint32_t = d0_0.wrapping_add(t1_0);
    let mut f1_0: uint32_t = e0_0;
    let mut g1_0: uint32_t = f0_0;
    let mut h12_0: uint32_t = g0_0;
    *hash.offset(0 as libc::c_uint as isize) = a1_0;
    *hash.offset(1 as libc::c_uint as isize) = b1_0;
    *hash.offset(2 as libc::c_uint as isize) = c1_0;
    *hash.offset(3 as libc::c_uint as isize) = d1_0;
    *hash.offset(4 as libc::c_uint as isize) = e1_0;
    *hash.offset(5 as libc::c_uint as isize) = f1_0;
    *hash.offset(6 as libc::c_uint as isize) = g1_0;
    *hash.offset(7 as libc::c_uint as isize) = h12_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_1: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_1: uint32_t = ws[i as usize];
    let mut a0_1: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_1: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_1: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_1: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_1: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_1: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_1: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_1: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_1: uint32_t = k_t_1;
    let mut t1_1: uint32_t = h02_1
        .wrapping_add(
            (e0_1 << 26 as libc::c_uint | e0_1 >> 6 as libc::c_uint)
                ^ ((e0_1 << 21 as libc::c_uint | e0_1 >> 11 as libc::c_uint)
                    ^ (e0_1 << 7 as libc::c_uint | e0_1 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_1 & f0_1 ^ !e0_1 & g0_1)
        .wrapping_add(k_e_t_1)
        .wrapping_add(ws_t_1);
    let mut t2_1: uint32_t = ((a0_1 << 30 as libc::c_uint | a0_1 >> 2 as libc::c_uint)
        ^ ((a0_1 << 19 as libc::c_uint | a0_1 >> 13 as libc::c_uint)
            ^ (a0_1 << 10 as libc::c_uint | a0_1 >> 22 as libc::c_uint)))
        .wrapping_add(a0_1 & b0_1 ^ (a0_1 & c0_1 ^ b0_1 & c0_1));
    let mut a1_1: uint32_t = t1_1.wrapping_add(t2_1);
    let mut b1_1: uint32_t = a0_1;
    let mut c1_1: uint32_t = b0_1;
    let mut d1_1: uint32_t = c0_1;
    let mut e1_1: uint32_t = d0_1.wrapping_add(t1_1);
    let mut f1_1: uint32_t = e0_1;
    let mut g1_1: uint32_t = f0_1;
    let mut h12_1: uint32_t = g0_1;
    *hash.offset(0 as libc::c_uint as isize) = a1_1;
    *hash.offset(1 as libc::c_uint as isize) = b1_1;
    *hash.offset(2 as libc::c_uint as isize) = c1_1;
    *hash.offset(3 as libc::c_uint as isize) = d1_1;
    *hash.offset(4 as libc::c_uint as isize) = e1_1;
    *hash.offset(5 as libc::c_uint as isize) = f1_1;
    *hash.offset(6 as libc::c_uint as isize) = g1_1;
    *hash.offset(7 as libc::c_uint as isize) = h12_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_2: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_2: uint32_t = ws[i as usize];
    let mut a0_2: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_2: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_2: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_2: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_2: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_2: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_2: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_2: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_2: uint32_t = k_t_2;
    let mut t1_2: uint32_t = h02_2
        .wrapping_add(
            (e0_2 << 26 as libc::c_uint | e0_2 >> 6 as libc::c_uint)
                ^ ((e0_2 << 21 as libc::c_uint | e0_2 >> 11 as libc::c_uint)
                    ^ (e0_2 << 7 as libc::c_uint | e0_2 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_2 & f0_2 ^ !e0_2 & g0_2)
        .wrapping_add(k_e_t_2)
        .wrapping_add(ws_t_2);
    let mut t2_2: uint32_t = ((a0_2 << 30 as libc::c_uint | a0_2 >> 2 as libc::c_uint)
        ^ ((a0_2 << 19 as libc::c_uint | a0_2 >> 13 as libc::c_uint)
            ^ (a0_2 << 10 as libc::c_uint | a0_2 >> 22 as libc::c_uint)))
        .wrapping_add(a0_2 & b0_2 ^ (a0_2 & c0_2 ^ b0_2 & c0_2));
    let mut a1_2: uint32_t = t1_2.wrapping_add(t2_2);
    let mut b1_2: uint32_t = a0_2;
    let mut c1_2: uint32_t = b0_2;
    let mut d1_2: uint32_t = c0_2;
    let mut e1_2: uint32_t = d0_2.wrapping_add(t1_2);
    let mut f1_2: uint32_t = e0_2;
    let mut g1_2: uint32_t = f0_2;
    let mut h12_2: uint32_t = g0_2;
    *hash.offset(0 as libc::c_uint as isize) = a1_2;
    *hash.offset(1 as libc::c_uint as isize) = b1_2;
    *hash.offset(2 as libc::c_uint as isize) = c1_2;
    *hash.offset(3 as libc::c_uint as isize) = d1_2;
    *hash.offset(4 as libc::c_uint as isize) = e1_2;
    *hash.offset(5 as libc::c_uint as isize) = f1_2;
    *hash.offset(6 as libc::c_uint as isize) = g1_2;
    *hash.offset(7 as libc::c_uint as isize) = h12_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_3: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_3: uint32_t = ws[i as usize];
    let mut a0_3: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_3: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_3: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_3: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_3: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_3: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_3: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_3: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_3: uint32_t = k_t_3;
    let mut t1_3: uint32_t = h02_3
        .wrapping_add(
            (e0_3 << 26 as libc::c_uint | e0_3 >> 6 as libc::c_uint)
                ^ ((e0_3 << 21 as libc::c_uint | e0_3 >> 11 as libc::c_uint)
                    ^ (e0_3 << 7 as libc::c_uint | e0_3 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_3 & f0_3 ^ !e0_3 & g0_3)
        .wrapping_add(k_e_t_3)
        .wrapping_add(ws_t_3);
    let mut t2_3: uint32_t = ((a0_3 << 30 as libc::c_uint | a0_3 >> 2 as libc::c_uint)
        ^ ((a0_3 << 19 as libc::c_uint | a0_3 >> 13 as libc::c_uint)
            ^ (a0_3 << 10 as libc::c_uint | a0_3 >> 22 as libc::c_uint)))
        .wrapping_add(a0_3 & b0_3 ^ (a0_3 & c0_3 ^ b0_3 & c0_3));
    let mut a1_3: uint32_t = t1_3.wrapping_add(t2_3);
    let mut b1_3: uint32_t = a0_3;
    let mut c1_3: uint32_t = b0_3;
    let mut d1_3: uint32_t = c0_3;
    let mut e1_3: uint32_t = d0_3.wrapping_add(t1_3);
    let mut f1_3: uint32_t = e0_3;
    let mut g1_3: uint32_t = f0_3;
    let mut h12_3: uint32_t = g0_3;
    *hash.offset(0 as libc::c_uint as isize) = a1_3;
    *hash.offset(1 as libc::c_uint as isize) = b1_3;
    *hash.offset(2 as libc::c_uint as isize) = c1_3;
    *hash.offset(3 as libc::c_uint as isize) = d1_3;
    *hash.offset(4 as libc::c_uint as isize) = e1_3;
    *hash.offset(5 as libc::c_uint as isize) = f1_3;
    *hash.offset(6 as libc::c_uint as isize) = g1_3;
    *hash.offset(7 as libc::c_uint as isize) = h12_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_4: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_4: uint32_t = ws[i as usize];
    let mut a0_4: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_4: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_4: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_4: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_4: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_4: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_4: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_4: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_4: uint32_t = k_t_4;
    let mut t1_4: uint32_t = h02_4
        .wrapping_add(
            (e0_4 << 26 as libc::c_uint | e0_4 >> 6 as libc::c_uint)
                ^ ((e0_4 << 21 as libc::c_uint | e0_4 >> 11 as libc::c_uint)
                    ^ (e0_4 << 7 as libc::c_uint | e0_4 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_4 & f0_4 ^ !e0_4 & g0_4)
        .wrapping_add(k_e_t_4)
        .wrapping_add(ws_t_4);
    let mut t2_4: uint32_t = ((a0_4 << 30 as libc::c_uint | a0_4 >> 2 as libc::c_uint)
        ^ ((a0_4 << 19 as libc::c_uint | a0_4 >> 13 as libc::c_uint)
            ^ (a0_4 << 10 as libc::c_uint | a0_4 >> 22 as libc::c_uint)))
        .wrapping_add(a0_4 & b0_4 ^ (a0_4 & c0_4 ^ b0_4 & c0_4));
    let mut a1_4: uint32_t = t1_4.wrapping_add(t2_4);
    let mut b1_4: uint32_t = a0_4;
    let mut c1_4: uint32_t = b0_4;
    let mut d1_4: uint32_t = c0_4;
    let mut e1_4: uint32_t = d0_4.wrapping_add(t1_4);
    let mut f1_4: uint32_t = e0_4;
    let mut g1_4: uint32_t = f0_4;
    let mut h12_4: uint32_t = g0_4;
    *hash.offset(0 as libc::c_uint as isize) = a1_4;
    *hash.offset(1 as libc::c_uint as isize) = b1_4;
    *hash.offset(2 as libc::c_uint as isize) = c1_4;
    *hash.offset(3 as libc::c_uint as isize) = d1_4;
    *hash.offset(4 as libc::c_uint as isize) = e1_4;
    *hash.offset(5 as libc::c_uint as isize) = f1_4;
    *hash.offset(6 as libc::c_uint as isize) = g1_4;
    *hash.offset(7 as libc::c_uint as isize) = h12_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_5: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_5: uint32_t = ws[i as usize];
    let mut a0_5: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_5: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_5: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_5: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_5: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_5: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_5: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_5: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_5: uint32_t = k_t_5;
    let mut t1_5: uint32_t = h02_5
        .wrapping_add(
            (e0_5 << 26 as libc::c_uint | e0_5 >> 6 as libc::c_uint)
                ^ ((e0_5 << 21 as libc::c_uint | e0_5 >> 11 as libc::c_uint)
                    ^ (e0_5 << 7 as libc::c_uint | e0_5 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_5 & f0_5 ^ !e0_5 & g0_5)
        .wrapping_add(k_e_t_5)
        .wrapping_add(ws_t_5);
    let mut t2_5: uint32_t = ((a0_5 << 30 as libc::c_uint | a0_5 >> 2 as libc::c_uint)
        ^ ((a0_5 << 19 as libc::c_uint | a0_5 >> 13 as libc::c_uint)
            ^ (a0_5 << 10 as libc::c_uint | a0_5 >> 22 as libc::c_uint)))
        .wrapping_add(a0_5 & b0_5 ^ (a0_5 & c0_5 ^ b0_5 & c0_5));
    let mut a1_5: uint32_t = t1_5.wrapping_add(t2_5);
    let mut b1_5: uint32_t = a0_5;
    let mut c1_5: uint32_t = b0_5;
    let mut d1_5: uint32_t = c0_5;
    let mut e1_5: uint32_t = d0_5.wrapping_add(t1_5);
    let mut f1_5: uint32_t = e0_5;
    let mut g1_5: uint32_t = f0_5;
    let mut h12_5: uint32_t = g0_5;
    *hash.offset(0 as libc::c_uint as isize) = a1_5;
    *hash.offset(1 as libc::c_uint as isize) = b1_5;
    *hash.offset(2 as libc::c_uint as isize) = c1_5;
    *hash.offset(3 as libc::c_uint as isize) = d1_5;
    *hash.offset(4 as libc::c_uint as isize) = e1_5;
    *hash.offset(5 as libc::c_uint as isize) = f1_5;
    *hash.offset(6 as libc::c_uint as isize) = g1_5;
    *hash.offset(7 as libc::c_uint as isize) = h12_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_6: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_6: uint32_t = ws[i as usize];
    let mut a0_6: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_6: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_6: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_6: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_6: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_6: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_6: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_6: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_6: uint32_t = k_t_6;
    let mut t1_6: uint32_t = h02_6
        .wrapping_add(
            (e0_6 << 26 as libc::c_uint | e0_6 >> 6 as libc::c_uint)
                ^ ((e0_6 << 21 as libc::c_uint | e0_6 >> 11 as libc::c_uint)
                    ^ (e0_6 << 7 as libc::c_uint | e0_6 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_6 & f0_6 ^ !e0_6 & g0_6)
        .wrapping_add(k_e_t_6)
        .wrapping_add(ws_t_6);
    let mut t2_6: uint32_t = ((a0_6 << 30 as libc::c_uint | a0_6 >> 2 as libc::c_uint)
        ^ ((a0_6 << 19 as libc::c_uint | a0_6 >> 13 as libc::c_uint)
            ^ (a0_6 << 10 as libc::c_uint | a0_6 >> 22 as libc::c_uint)))
        .wrapping_add(a0_6 & b0_6 ^ (a0_6 & c0_6 ^ b0_6 & c0_6));
    let mut a1_6: uint32_t = t1_6.wrapping_add(t2_6);
    let mut b1_6: uint32_t = a0_6;
    let mut c1_6: uint32_t = b0_6;
    let mut d1_6: uint32_t = c0_6;
    let mut e1_6: uint32_t = d0_6.wrapping_add(t1_6);
    let mut f1_6: uint32_t = e0_6;
    let mut g1_6: uint32_t = f0_6;
    let mut h12_6: uint32_t = g0_6;
    *hash.offset(0 as libc::c_uint as isize) = a1_6;
    *hash.offset(1 as libc::c_uint as isize) = b1_6;
    *hash.offset(2 as libc::c_uint as isize) = c1_6;
    *hash.offset(3 as libc::c_uint as isize) = d1_6;
    *hash.offset(4 as libc::c_uint as isize) = e1_6;
    *hash.offset(5 as libc::c_uint as isize) = f1_6;
    *hash.offset(6 as libc::c_uint as isize) = g1_6;
    *hash.offset(7 as libc::c_uint as isize) = h12_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_7: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_7: uint32_t = ws[i as usize];
    let mut a0_7: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_7: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_7: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_7: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_7: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_7: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_7: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_7: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_7: uint32_t = k_t_7;
    let mut t1_7: uint32_t = h02_7
        .wrapping_add(
            (e0_7 << 26 as libc::c_uint | e0_7 >> 6 as libc::c_uint)
                ^ ((e0_7 << 21 as libc::c_uint | e0_7 >> 11 as libc::c_uint)
                    ^ (e0_7 << 7 as libc::c_uint | e0_7 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_7 & f0_7 ^ !e0_7 & g0_7)
        .wrapping_add(k_e_t_7)
        .wrapping_add(ws_t_7);
    let mut t2_7: uint32_t = ((a0_7 << 30 as libc::c_uint | a0_7 >> 2 as libc::c_uint)
        ^ ((a0_7 << 19 as libc::c_uint | a0_7 >> 13 as libc::c_uint)
            ^ (a0_7 << 10 as libc::c_uint | a0_7 >> 22 as libc::c_uint)))
        .wrapping_add(a0_7 & b0_7 ^ (a0_7 & c0_7 ^ b0_7 & c0_7));
    let mut a1_7: uint32_t = t1_7.wrapping_add(t2_7);
    let mut b1_7: uint32_t = a0_7;
    let mut c1_7: uint32_t = b0_7;
    let mut d1_7: uint32_t = c0_7;
    let mut e1_7: uint32_t = d0_7.wrapping_add(t1_7);
    let mut f1_7: uint32_t = e0_7;
    let mut g1_7: uint32_t = f0_7;
    let mut h12_7: uint32_t = g0_7;
    *hash.offset(0 as libc::c_uint as isize) = a1_7;
    *hash.offset(1 as libc::c_uint as isize) = b1_7;
    *hash.offset(2 as libc::c_uint as isize) = c1_7;
    *hash.offset(3 as libc::c_uint as isize) = d1_7;
    *hash.offset(4 as libc::c_uint as isize) = e1_7;
    *hash.offset(5 as libc::c_uint as isize) = f1_7;
    *hash.offset(6 as libc::c_uint as isize) = g1_7;
    *hash.offset(7 as libc::c_uint as isize) = h12_7;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_8: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_8: uint32_t = ws[i as usize];
    let mut a0_8: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_8: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_8: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_8: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_8: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_8: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_8: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_8: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_8: uint32_t = k_t_8;
    let mut t1_8: uint32_t = h02_8
        .wrapping_add(
            (e0_8 << 26 as libc::c_uint | e0_8 >> 6 as libc::c_uint)
                ^ ((e0_8 << 21 as libc::c_uint | e0_8 >> 11 as libc::c_uint)
                    ^ (e0_8 << 7 as libc::c_uint | e0_8 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_8 & f0_8 ^ !e0_8 & g0_8)
        .wrapping_add(k_e_t_8)
        .wrapping_add(ws_t_8);
    let mut t2_8: uint32_t = ((a0_8 << 30 as libc::c_uint | a0_8 >> 2 as libc::c_uint)
        ^ ((a0_8 << 19 as libc::c_uint | a0_8 >> 13 as libc::c_uint)
            ^ (a0_8 << 10 as libc::c_uint | a0_8 >> 22 as libc::c_uint)))
        .wrapping_add(a0_8 & b0_8 ^ (a0_8 & c0_8 ^ b0_8 & c0_8));
    let mut a1_8: uint32_t = t1_8.wrapping_add(t2_8);
    let mut b1_8: uint32_t = a0_8;
    let mut c1_8: uint32_t = b0_8;
    let mut d1_8: uint32_t = c0_8;
    let mut e1_8: uint32_t = d0_8.wrapping_add(t1_8);
    let mut f1_8: uint32_t = e0_8;
    let mut g1_8: uint32_t = f0_8;
    let mut h12_8: uint32_t = g0_8;
    *hash.offset(0 as libc::c_uint as isize) = a1_8;
    *hash.offset(1 as libc::c_uint as isize) = b1_8;
    *hash.offset(2 as libc::c_uint as isize) = c1_8;
    *hash.offset(3 as libc::c_uint as isize) = d1_8;
    *hash.offset(4 as libc::c_uint as isize) = e1_8;
    *hash.offset(5 as libc::c_uint as isize) = f1_8;
    *hash.offset(6 as libc::c_uint as isize) = g1_8;
    *hash.offset(7 as libc::c_uint as isize) = h12_8;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_9: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_9: uint32_t = ws[i as usize];
    let mut a0_9: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_9: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_9: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_9: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_9: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_9: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_9: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_9: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_9: uint32_t = k_t_9;
    let mut t1_9: uint32_t = h02_9
        .wrapping_add(
            (e0_9 << 26 as libc::c_uint | e0_9 >> 6 as libc::c_uint)
                ^ ((e0_9 << 21 as libc::c_uint | e0_9 >> 11 as libc::c_uint)
                    ^ (e0_9 << 7 as libc::c_uint | e0_9 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_9 & f0_9 ^ !e0_9 & g0_9)
        .wrapping_add(k_e_t_9)
        .wrapping_add(ws_t_9);
    let mut t2_9: uint32_t = ((a0_9 << 30 as libc::c_uint | a0_9 >> 2 as libc::c_uint)
        ^ ((a0_9 << 19 as libc::c_uint | a0_9 >> 13 as libc::c_uint)
            ^ (a0_9 << 10 as libc::c_uint | a0_9 >> 22 as libc::c_uint)))
        .wrapping_add(a0_9 & b0_9 ^ (a0_9 & c0_9 ^ b0_9 & c0_9));
    let mut a1_9: uint32_t = t1_9.wrapping_add(t2_9);
    let mut b1_9: uint32_t = a0_9;
    let mut c1_9: uint32_t = b0_9;
    let mut d1_9: uint32_t = c0_9;
    let mut e1_9: uint32_t = d0_9.wrapping_add(t1_9);
    let mut f1_9: uint32_t = e0_9;
    let mut g1_9: uint32_t = f0_9;
    let mut h12_9: uint32_t = g0_9;
    *hash.offset(0 as libc::c_uint as isize) = a1_9;
    *hash.offset(1 as libc::c_uint as isize) = b1_9;
    *hash.offset(2 as libc::c_uint as isize) = c1_9;
    *hash.offset(3 as libc::c_uint as isize) = d1_9;
    *hash.offset(4 as libc::c_uint as isize) = e1_9;
    *hash.offset(5 as libc::c_uint as isize) = f1_9;
    *hash.offset(6 as libc::c_uint as isize) = g1_9;
    *hash.offset(7 as libc::c_uint as isize) = h12_9;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_10: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_10: uint32_t = ws[i as usize];
    let mut a0_10: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_10: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_10: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_10: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_10: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_10: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_10: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_10: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_10: uint32_t = k_t_10;
    let mut t1_10: uint32_t = h02_10
        .wrapping_add(
            (e0_10 << 26 as libc::c_uint | e0_10 >> 6 as libc::c_uint)
                ^ ((e0_10 << 21 as libc::c_uint | e0_10 >> 11 as libc::c_uint)
                    ^ (e0_10 << 7 as libc::c_uint | e0_10 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_10 & f0_10 ^ !e0_10 & g0_10)
        .wrapping_add(k_e_t_10)
        .wrapping_add(ws_t_10);
    let mut t2_10: uint32_t = ((a0_10 << 30 as libc::c_uint | a0_10 >> 2 as libc::c_uint)
        ^ ((a0_10 << 19 as libc::c_uint | a0_10 >> 13 as libc::c_uint)
            ^ (a0_10 << 10 as libc::c_uint | a0_10 >> 22 as libc::c_uint)))
        .wrapping_add(a0_10 & b0_10 ^ (a0_10 & c0_10 ^ b0_10 & c0_10));
    let mut a1_10: uint32_t = t1_10.wrapping_add(t2_10);
    let mut b1_10: uint32_t = a0_10;
    let mut c1_10: uint32_t = b0_10;
    let mut d1_10: uint32_t = c0_10;
    let mut e1_10: uint32_t = d0_10.wrapping_add(t1_10);
    let mut f1_10: uint32_t = e0_10;
    let mut g1_10: uint32_t = f0_10;
    let mut h12_10: uint32_t = g0_10;
    *hash.offset(0 as libc::c_uint as isize) = a1_10;
    *hash.offset(1 as libc::c_uint as isize) = b1_10;
    *hash.offset(2 as libc::c_uint as isize) = c1_10;
    *hash.offset(3 as libc::c_uint as isize) = d1_10;
    *hash.offset(4 as libc::c_uint as isize) = e1_10;
    *hash.offset(5 as libc::c_uint as isize) = f1_10;
    *hash.offset(6 as libc::c_uint as isize) = g1_10;
    *hash.offset(7 as libc::c_uint as isize) = h12_10;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_11: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_11: uint32_t = ws[i as usize];
    let mut a0_11: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_11: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_11: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_11: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_11: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_11: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_11: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_11: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_11: uint32_t = k_t_11;
    let mut t1_11: uint32_t = h02_11
        .wrapping_add(
            (e0_11 << 26 as libc::c_uint | e0_11 >> 6 as libc::c_uint)
                ^ ((e0_11 << 21 as libc::c_uint | e0_11 >> 11 as libc::c_uint)
                    ^ (e0_11 << 7 as libc::c_uint | e0_11 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_11 & f0_11 ^ !e0_11 & g0_11)
        .wrapping_add(k_e_t_11)
        .wrapping_add(ws_t_11);
    let mut t2_11: uint32_t = ((a0_11 << 30 as libc::c_uint | a0_11 >> 2 as libc::c_uint)
        ^ ((a0_11 << 19 as libc::c_uint | a0_11 >> 13 as libc::c_uint)
            ^ (a0_11 << 10 as libc::c_uint | a0_11 >> 22 as libc::c_uint)))
        .wrapping_add(a0_11 & b0_11 ^ (a0_11 & c0_11 ^ b0_11 & c0_11));
    let mut a1_11: uint32_t = t1_11.wrapping_add(t2_11);
    let mut b1_11: uint32_t = a0_11;
    let mut c1_11: uint32_t = b0_11;
    let mut d1_11: uint32_t = c0_11;
    let mut e1_11: uint32_t = d0_11.wrapping_add(t1_11);
    let mut f1_11: uint32_t = e0_11;
    let mut g1_11: uint32_t = f0_11;
    let mut h12_11: uint32_t = g0_11;
    *hash.offset(0 as libc::c_uint as isize) = a1_11;
    *hash.offset(1 as libc::c_uint as isize) = b1_11;
    *hash.offset(2 as libc::c_uint as isize) = c1_11;
    *hash.offset(3 as libc::c_uint as isize) = d1_11;
    *hash.offset(4 as libc::c_uint as isize) = e1_11;
    *hash.offset(5 as libc::c_uint as isize) = f1_11;
    *hash.offset(6 as libc::c_uint as isize) = g1_11;
    *hash.offset(7 as libc::c_uint as isize) = h12_11;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_12: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_12: uint32_t = ws[i as usize];
    let mut a0_12: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_12: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_12: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_12: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_12: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_12: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_12: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_12: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_12: uint32_t = k_t_12;
    let mut t1_12: uint32_t = h02_12
        .wrapping_add(
            (e0_12 << 26 as libc::c_uint | e0_12 >> 6 as libc::c_uint)
                ^ ((e0_12 << 21 as libc::c_uint | e0_12 >> 11 as libc::c_uint)
                    ^ (e0_12 << 7 as libc::c_uint | e0_12 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_12 & f0_12 ^ !e0_12 & g0_12)
        .wrapping_add(k_e_t_12)
        .wrapping_add(ws_t_12);
    let mut t2_12: uint32_t = ((a0_12 << 30 as libc::c_uint | a0_12 >> 2 as libc::c_uint)
        ^ ((a0_12 << 19 as libc::c_uint | a0_12 >> 13 as libc::c_uint)
            ^ (a0_12 << 10 as libc::c_uint | a0_12 >> 22 as libc::c_uint)))
        .wrapping_add(a0_12 & b0_12 ^ (a0_12 & c0_12 ^ b0_12 & c0_12));
    let mut a1_12: uint32_t = t1_12.wrapping_add(t2_12);
    let mut b1_12: uint32_t = a0_12;
    let mut c1_12: uint32_t = b0_12;
    let mut d1_12: uint32_t = c0_12;
    let mut e1_12: uint32_t = d0_12.wrapping_add(t1_12);
    let mut f1_12: uint32_t = e0_12;
    let mut g1_12: uint32_t = f0_12;
    let mut h12_12: uint32_t = g0_12;
    *hash.offset(0 as libc::c_uint as isize) = a1_12;
    *hash.offset(1 as libc::c_uint as isize) = b1_12;
    *hash.offset(2 as libc::c_uint as isize) = c1_12;
    *hash.offset(3 as libc::c_uint as isize) = d1_12;
    *hash.offset(4 as libc::c_uint as isize) = e1_12;
    *hash.offset(5 as libc::c_uint as isize) = f1_12;
    *hash.offset(6 as libc::c_uint as isize) = g1_12;
    *hash.offset(7 as libc::c_uint as isize) = h12_12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_13: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_13: uint32_t = ws[i as usize];
    let mut a0_13: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_13: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_13: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_13: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_13: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_13: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_13: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_13: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_13: uint32_t = k_t_13;
    let mut t1_13: uint32_t = h02_13
        .wrapping_add(
            (e0_13 << 26 as libc::c_uint | e0_13 >> 6 as libc::c_uint)
                ^ ((e0_13 << 21 as libc::c_uint | e0_13 >> 11 as libc::c_uint)
                    ^ (e0_13 << 7 as libc::c_uint | e0_13 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_13 & f0_13 ^ !e0_13 & g0_13)
        .wrapping_add(k_e_t_13)
        .wrapping_add(ws_t_13);
    let mut t2_13: uint32_t = ((a0_13 << 30 as libc::c_uint | a0_13 >> 2 as libc::c_uint)
        ^ ((a0_13 << 19 as libc::c_uint | a0_13 >> 13 as libc::c_uint)
            ^ (a0_13 << 10 as libc::c_uint | a0_13 >> 22 as libc::c_uint)))
        .wrapping_add(a0_13 & b0_13 ^ (a0_13 & c0_13 ^ b0_13 & c0_13));
    let mut a1_13: uint32_t = t1_13.wrapping_add(t2_13);
    let mut b1_13: uint32_t = a0_13;
    let mut c1_13: uint32_t = b0_13;
    let mut d1_13: uint32_t = c0_13;
    let mut e1_13: uint32_t = d0_13.wrapping_add(t1_13);
    let mut f1_13: uint32_t = e0_13;
    let mut g1_13: uint32_t = f0_13;
    let mut h12_13: uint32_t = g0_13;
    *hash.offset(0 as libc::c_uint as isize) = a1_13;
    *hash.offset(1 as libc::c_uint as isize) = b1_13;
    *hash.offset(2 as libc::c_uint as isize) = c1_13;
    *hash.offset(3 as libc::c_uint as isize) = d1_13;
    *hash.offset(4 as libc::c_uint as isize) = e1_13;
    *hash.offset(5 as libc::c_uint as isize) = f1_13;
    *hash.offset(6 as libc::c_uint as isize) = g1_13;
    *hash.offset(7 as libc::c_uint as isize) = h12_13;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_14: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_14: uint32_t = ws[i as usize];
    let mut a0_14: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_14: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_14: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_14: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_14: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_14: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_14: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_14: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_14: uint32_t = k_t_14;
    let mut t1_14: uint32_t = h02_14
        .wrapping_add(
            (e0_14 << 26 as libc::c_uint | e0_14 >> 6 as libc::c_uint)
                ^ ((e0_14 << 21 as libc::c_uint | e0_14 >> 11 as libc::c_uint)
                    ^ (e0_14 << 7 as libc::c_uint | e0_14 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_14 & f0_14 ^ !e0_14 & g0_14)
        .wrapping_add(k_e_t_14)
        .wrapping_add(ws_t_14);
    let mut t2_14: uint32_t = ((a0_14 << 30 as libc::c_uint | a0_14 >> 2 as libc::c_uint)
        ^ ((a0_14 << 19 as libc::c_uint | a0_14 >> 13 as libc::c_uint)
            ^ (a0_14 << 10 as libc::c_uint | a0_14 >> 22 as libc::c_uint)))
        .wrapping_add(a0_14 & b0_14 ^ (a0_14 & c0_14 ^ b0_14 & c0_14));
    let mut a1_14: uint32_t = t1_14.wrapping_add(t2_14);
    let mut b1_14: uint32_t = a0_14;
    let mut c1_14: uint32_t = b0_14;
    let mut d1_14: uint32_t = c0_14;
    let mut e1_14: uint32_t = d0_14.wrapping_add(t1_14);
    let mut f1_14: uint32_t = e0_14;
    let mut g1_14: uint32_t = f0_14;
    let mut h12_14: uint32_t = g0_14;
    *hash.offset(0 as libc::c_uint as isize) = a1_14;
    *hash.offset(1 as libc::c_uint as isize) = b1_14;
    *hash.offset(2 as libc::c_uint as isize) = c1_14;
    *hash.offset(3 as libc::c_uint as isize) = d1_14;
    *hash.offset(4 as libc::c_uint as isize) = e1_14;
    *hash.offset(5 as libc::c_uint as isize) = f1_14;
    *hash.offset(6 as libc::c_uint as isize) = g1_14;
    *hash.offset(7 as libc::c_uint as isize) = h12_14;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 3 as libc::c_uint {
        let mut i_0: uint32_t = 0 as libc::c_uint;
        let mut t16: uint32_t = ws[i_0 as usize];
        let mut t15: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_15: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1: uint32_t = (t2_15 << 15 as libc::c_uint
            | t2_15 >> 17 as libc::c_uint)
            ^ ((t2_15 << 13 as libc::c_uint | t2_15 >> 19 as libc::c_uint)
                ^ t2_15 >> 10 as libc::c_uint);
        let mut s0: uint32_t = (t15 << 25 as libc::c_uint | t15 >> 7 as libc::c_uint)
            ^ ((t15 << 14 as libc::c_uint | t15 >> 18 as libc::c_uint)
                ^ t15 >> 3 as libc::c_uint);
        ws[i_0 as usize] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_0: uint32_t = ws[i_0 as usize];
        let mut t15_0: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_0: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_16: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_0: uint32_t = (t2_16 << 15 as libc::c_uint
            | t2_16 >> 17 as libc::c_uint)
            ^ ((t2_16 << 13 as libc::c_uint | t2_16 >> 19 as libc::c_uint)
                ^ t2_16 >> 10 as libc::c_uint);
        let mut s0_0: uint32_t = (t15_0 << 25 as libc::c_uint
            | t15_0 >> 7 as libc::c_uint)
            ^ ((t15_0 << 14 as libc::c_uint | t15_0 >> 18 as libc::c_uint)
                ^ t15_0 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_0.wrapping_add(t7_0).wrapping_add(s0_0).wrapping_add(t16_0);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_1: uint32_t = ws[i_0 as usize];
        let mut t15_1: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_1: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_17: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_1: uint32_t = (t2_17 << 15 as libc::c_uint
            | t2_17 >> 17 as libc::c_uint)
            ^ ((t2_17 << 13 as libc::c_uint | t2_17 >> 19 as libc::c_uint)
                ^ t2_17 >> 10 as libc::c_uint);
        let mut s0_1: uint32_t = (t15_1 << 25 as libc::c_uint
            | t15_1 >> 7 as libc::c_uint)
            ^ ((t15_1 << 14 as libc::c_uint | t15_1 >> 18 as libc::c_uint)
                ^ t15_1 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_1.wrapping_add(t7_1).wrapping_add(s0_1).wrapping_add(t16_1);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_2: uint32_t = ws[i_0 as usize];
        let mut t15_2: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_2: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_18: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_2: uint32_t = (t2_18 << 15 as libc::c_uint
            | t2_18 >> 17 as libc::c_uint)
            ^ ((t2_18 << 13 as libc::c_uint | t2_18 >> 19 as libc::c_uint)
                ^ t2_18 >> 10 as libc::c_uint);
        let mut s0_2: uint32_t = (t15_2 << 25 as libc::c_uint
            | t15_2 >> 7 as libc::c_uint)
            ^ ((t15_2 << 14 as libc::c_uint | t15_2 >> 18 as libc::c_uint)
                ^ t15_2 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_2.wrapping_add(t7_2).wrapping_add(s0_2).wrapping_add(t16_2);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_3: uint32_t = ws[i_0 as usize];
        let mut t15_3: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_3: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_19: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_3: uint32_t = (t2_19 << 15 as libc::c_uint
            | t2_19 >> 17 as libc::c_uint)
            ^ ((t2_19 << 13 as libc::c_uint | t2_19 >> 19 as libc::c_uint)
                ^ t2_19 >> 10 as libc::c_uint);
        let mut s0_3: uint32_t = (t15_3 << 25 as libc::c_uint
            | t15_3 >> 7 as libc::c_uint)
            ^ ((t15_3 << 14 as libc::c_uint | t15_3 >> 18 as libc::c_uint)
                ^ t15_3 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_3.wrapping_add(t7_3).wrapping_add(s0_3).wrapping_add(t16_3);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_4: uint32_t = ws[i_0 as usize];
        let mut t15_4: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_4: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_20: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_4: uint32_t = (t2_20 << 15 as libc::c_uint
            | t2_20 >> 17 as libc::c_uint)
            ^ ((t2_20 << 13 as libc::c_uint | t2_20 >> 19 as libc::c_uint)
                ^ t2_20 >> 10 as libc::c_uint);
        let mut s0_4: uint32_t = (t15_4 << 25 as libc::c_uint
            | t15_4 >> 7 as libc::c_uint)
            ^ ((t15_4 << 14 as libc::c_uint | t15_4 >> 18 as libc::c_uint)
                ^ t15_4 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_4.wrapping_add(t7_4).wrapping_add(s0_4).wrapping_add(t16_4);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_5: uint32_t = ws[i_0 as usize];
        let mut t15_5: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_5: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_21: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_5: uint32_t = (t2_21 << 15 as libc::c_uint
            | t2_21 >> 17 as libc::c_uint)
            ^ ((t2_21 << 13 as libc::c_uint | t2_21 >> 19 as libc::c_uint)
                ^ t2_21 >> 10 as libc::c_uint);
        let mut s0_5: uint32_t = (t15_5 << 25 as libc::c_uint
            | t15_5 >> 7 as libc::c_uint)
            ^ ((t15_5 << 14 as libc::c_uint | t15_5 >> 18 as libc::c_uint)
                ^ t15_5 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_5.wrapping_add(t7_5).wrapping_add(s0_5).wrapping_add(t16_5);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_6: uint32_t = ws[i_0 as usize];
        let mut t15_6: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_6: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_22: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_6: uint32_t = (t2_22 << 15 as libc::c_uint
            | t2_22 >> 17 as libc::c_uint)
            ^ ((t2_22 << 13 as libc::c_uint | t2_22 >> 19 as libc::c_uint)
                ^ t2_22 >> 10 as libc::c_uint);
        let mut s0_6: uint32_t = (t15_6 << 25 as libc::c_uint
            | t15_6 >> 7 as libc::c_uint)
            ^ ((t15_6 << 14 as libc::c_uint | t15_6 >> 18 as libc::c_uint)
                ^ t15_6 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_6.wrapping_add(t7_6).wrapping_add(s0_6).wrapping_add(t16_6);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_7: uint32_t = ws[i_0 as usize];
        let mut t15_7: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_7: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_23: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_7: uint32_t = (t2_23 << 15 as libc::c_uint
            | t2_23 >> 17 as libc::c_uint)
            ^ ((t2_23 << 13 as libc::c_uint | t2_23 >> 19 as libc::c_uint)
                ^ t2_23 >> 10 as libc::c_uint);
        let mut s0_7: uint32_t = (t15_7 << 25 as libc::c_uint
            | t15_7 >> 7 as libc::c_uint)
            ^ ((t15_7 << 14 as libc::c_uint | t15_7 >> 18 as libc::c_uint)
                ^ t15_7 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_7.wrapping_add(t7_7).wrapping_add(s0_7).wrapping_add(t16_7);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_8: uint32_t = ws[i_0 as usize];
        let mut t15_8: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_8: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_24: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_8: uint32_t = (t2_24 << 15 as libc::c_uint
            | t2_24 >> 17 as libc::c_uint)
            ^ ((t2_24 << 13 as libc::c_uint | t2_24 >> 19 as libc::c_uint)
                ^ t2_24 >> 10 as libc::c_uint);
        let mut s0_8: uint32_t = (t15_8 << 25 as libc::c_uint
            | t15_8 >> 7 as libc::c_uint)
            ^ ((t15_8 << 14 as libc::c_uint | t15_8 >> 18 as libc::c_uint)
                ^ t15_8 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_8.wrapping_add(t7_8).wrapping_add(s0_8).wrapping_add(t16_8);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_9: uint32_t = ws[i_0 as usize];
        let mut t15_9: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_9: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_25: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_9: uint32_t = (t2_25 << 15 as libc::c_uint
            | t2_25 >> 17 as libc::c_uint)
            ^ ((t2_25 << 13 as libc::c_uint | t2_25 >> 19 as libc::c_uint)
                ^ t2_25 >> 10 as libc::c_uint);
        let mut s0_9: uint32_t = (t15_9 << 25 as libc::c_uint
            | t15_9 >> 7 as libc::c_uint)
            ^ ((t15_9 << 14 as libc::c_uint | t15_9 >> 18 as libc::c_uint)
                ^ t15_9 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_9.wrapping_add(t7_9).wrapping_add(s0_9).wrapping_add(t16_9);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_10: uint32_t = ws[i_0 as usize];
        let mut t15_10: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_10: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_26: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_10: uint32_t = (t2_26 << 15 as libc::c_uint
            | t2_26 >> 17 as libc::c_uint)
            ^ ((t2_26 << 13 as libc::c_uint | t2_26 >> 19 as libc::c_uint)
                ^ t2_26 >> 10 as libc::c_uint);
        let mut s0_10: uint32_t = (t15_10 << 25 as libc::c_uint
            | t15_10 >> 7 as libc::c_uint)
            ^ ((t15_10 << 14 as libc::c_uint | t15_10 >> 18 as libc::c_uint)
                ^ t15_10 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_10
            .wrapping_add(t7_10)
            .wrapping_add(s0_10)
            .wrapping_add(t16_10);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_11: uint32_t = ws[i_0 as usize];
        let mut t15_11: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_11: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_27: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_11: uint32_t = (t2_27 << 15 as libc::c_uint
            | t2_27 >> 17 as libc::c_uint)
            ^ ((t2_27 << 13 as libc::c_uint | t2_27 >> 19 as libc::c_uint)
                ^ t2_27 >> 10 as libc::c_uint);
        let mut s0_11: uint32_t = (t15_11 << 25 as libc::c_uint
            | t15_11 >> 7 as libc::c_uint)
            ^ ((t15_11 << 14 as libc::c_uint | t15_11 >> 18 as libc::c_uint)
                ^ t15_11 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_11
            .wrapping_add(t7_11)
            .wrapping_add(s0_11)
            .wrapping_add(t16_11);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_12: uint32_t = ws[i_0 as usize];
        let mut t15_12: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_12: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_28: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_12: uint32_t = (t2_28 << 15 as libc::c_uint
            | t2_28 >> 17 as libc::c_uint)
            ^ ((t2_28 << 13 as libc::c_uint | t2_28 >> 19 as libc::c_uint)
                ^ t2_28 >> 10 as libc::c_uint);
        let mut s0_12: uint32_t = (t15_12 << 25 as libc::c_uint
            | t15_12 >> 7 as libc::c_uint)
            ^ ((t15_12 << 14 as libc::c_uint | t15_12 >> 18 as libc::c_uint)
                ^ t15_12 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_12
            .wrapping_add(t7_12)
            .wrapping_add(s0_12)
            .wrapping_add(t16_12);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_13: uint32_t = ws[i_0 as usize];
        let mut t15_13: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_13: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_29: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_13: uint32_t = (t2_29 << 15 as libc::c_uint
            | t2_29 >> 17 as libc::c_uint)
            ^ ((t2_29 << 13 as libc::c_uint | t2_29 >> 19 as libc::c_uint)
                ^ t2_29 >> 10 as libc::c_uint);
        let mut s0_13: uint32_t = (t15_13 << 25 as libc::c_uint
            | t15_13 >> 7 as libc::c_uint)
            ^ ((t15_13 << 14 as libc::c_uint | t15_13 >> 18 as libc::c_uint)
                ^ t15_13 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_13
            .wrapping_add(t7_13)
            .wrapping_add(s0_13)
            .wrapping_add(t16_13);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_14: uint32_t = ws[i_0 as usize];
        let mut t15_14: uint32_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_14: uint32_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_30: uint32_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_14: uint32_t = (t2_30 << 15 as libc::c_uint
            | t2_30 >> 17 as libc::c_uint)
            ^ ((t2_30 << 13 as libc::c_uint | t2_30 >> 19 as libc::c_uint)
                ^ t2_30 >> 10 as libc::c_uint);
        let mut s0_14: uint32_t = (t15_14 << 25 as libc::c_uint
            | t15_14 >> 7 as libc::c_uint)
            ^ ((t15_14 << 14 as libc::c_uint | t15_14 >> 18 as libc::c_uint)
                ^ t15_14 >> 3 as libc::c_uint);
        ws[i_0
            as usize] = s1_14
            .wrapping_add(t7_14)
            .wrapping_add(s0_14)
            .wrapping_add(t16_14);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut k_t_15: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_15: uint32_t = ws[i_1 as usize];
    let mut a0_15: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_15: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_15: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_15: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_15: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_15: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_15: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_15: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_15: uint32_t = k_t_15;
    let mut t1_15: uint32_t = h02_15
        .wrapping_add(
            (e0_15 << 26 as libc::c_uint | e0_15 >> 6 as libc::c_uint)
                ^ ((e0_15 << 21 as libc::c_uint | e0_15 >> 11 as libc::c_uint)
                    ^ (e0_15 << 7 as libc::c_uint | e0_15 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_15 & f0_15 ^ !e0_15 & g0_15)
        .wrapping_add(k_e_t_15)
        .wrapping_add(ws_t_15);
    let mut t2_31: uint32_t = ((a0_15 << 30 as libc::c_uint | a0_15 >> 2 as libc::c_uint)
        ^ ((a0_15 << 19 as libc::c_uint | a0_15 >> 13 as libc::c_uint)
            ^ (a0_15 << 10 as libc::c_uint | a0_15 >> 22 as libc::c_uint)))
        .wrapping_add(a0_15 & b0_15 ^ (a0_15 & c0_15 ^ b0_15 & c0_15));
    let mut a1_15: uint32_t = t1_15.wrapping_add(t2_31);
    let mut b1_15: uint32_t = a0_15;
    let mut c1_15: uint32_t = b0_15;
    let mut d1_15: uint32_t = c0_15;
    let mut e1_15: uint32_t = d0_15.wrapping_add(t1_15);
    let mut f1_15: uint32_t = e0_15;
    let mut g1_15: uint32_t = f0_15;
    let mut h12_15: uint32_t = g0_15;
    *hash.offset(0 as libc::c_uint as isize) = a1_15;
    *hash.offset(1 as libc::c_uint as isize) = b1_15;
    *hash.offset(2 as libc::c_uint as isize) = c1_15;
    *hash.offset(3 as libc::c_uint as isize) = d1_15;
    *hash.offset(4 as libc::c_uint as isize) = e1_15;
    *hash.offset(5 as libc::c_uint as isize) = f1_15;
    *hash.offset(6 as libc::c_uint as isize) = g1_15;
    *hash.offset(7 as libc::c_uint as isize) = h12_15;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_16: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_16: uint32_t = ws[i_1 as usize];
    let mut a0_16: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_16: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_16: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_16: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_16: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_16: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_16: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_16: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_16: uint32_t = k_t_16;
    let mut t1_16: uint32_t = h02_16
        .wrapping_add(
            (e0_16 << 26 as libc::c_uint | e0_16 >> 6 as libc::c_uint)
                ^ ((e0_16 << 21 as libc::c_uint | e0_16 >> 11 as libc::c_uint)
                    ^ (e0_16 << 7 as libc::c_uint | e0_16 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_16 & f0_16 ^ !e0_16 & g0_16)
        .wrapping_add(k_e_t_16)
        .wrapping_add(ws_t_16);
    let mut t2_32: uint32_t = ((a0_16 << 30 as libc::c_uint | a0_16 >> 2 as libc::c_uint)
        ^ ((a0_16 << 19 as libc::c_uint | a0_16 >> 13 as libc::c_uint)
            ^ (a0_16 << 10 as libc::c_uint | a0_16 >> 22 as libc::c_uint)))
        .wrapping_add(a0_16 & b0_16 ^ (a0_16 & c0_16 ^ b0_16 & c0_16));
    let mut a1_16: uint32_t = t1_16.wrapping_add(t2_32);
    let mut b1_16: uint32_t = a0_16;
    let mut c1_16: uint32_t = b0_16;
    let mut d1_16: uint32_t = c0_16;
    let mut e1_16: uint32_t = d0_16.wrapping_add(t1_16);
    let mut f1_16: uint32_t = e0_16;
    let mut g1_16: uint32_t = f0_16;
    let mut h12_16: uint32_t = g0_16;
    *hash.offset(0 as libc::c_uint as isize) = a1_16;
    *hash.offset(1 as libc::c_uint as isize) = b1_16;
    *hash.offset(2 as libc::c_uint as isize) = c1_16;
    *hash.offset(3 as libc::c_uint as isize) = d1_16;
    *hash.offset(4 as libc::c_uint as isize) = e1_16;
    *hash.offset(5 as libc::c_uint as isize) = f1_16;
    *hash.offset(6 as libc::c_uint as isize) = g1_16;
    *hash.offset(7 as libc::c_uint as isize) = h12_16;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_17: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_17: uint32_t = ws[i_1 as usize];
    let mut a0_17: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_17: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_17: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_17: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_17: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_17: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_17: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_17: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_17: uint32_t = k_t_17;
    let mut t1_17: uint32_t = h02_17
        .wrapping_add(
            (e0_17 << 26 as libc::c_uint | e0_17 >> 6 as libc::c_uint)
                ^ ((e0_17 << 21 as libc::c_uint | e0_17 >> 11 as libc::c_uint)
                    ^ (e0_17 << 7 as libc::c_uint | e0_17 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_17 & f0_17 ^ !e0_17 & g0_17)
        .wrapping_add(k_e_t_17)
        .wrapping_add(ws_t_17);
    let mut t2_33: uint32_t = ((a0_17 << 30 as libc::c_uint | a0_17 >> 2 as libc::c_uint)
        ^ ((a0_17 << 19 as libc::c_uint | a0_17 >> 13 as libc::c_uint)
            ^ (a0_17 << 10 as libc::c_uint | a0_17 >> 22 as libc::c_uint)))
        .wrapping_add(a0_17 & b0_17 ^ (a0_17 & c0_17 ^ b0_17 & c0_17));
    let mut a1_17: uint32_t = t1_17.wrapping_add(t2_33);
    let mut b1_17: uint32_t = a0_17;
    let mut c1_17: uint32_t = b0_17;
    let mut d1_17: uint32_t = c0_17;
    let mut e1_17: uint32_t = d0_17.wrapping_add(t1_17);
    let mut f1_17: uint32_t = e0_17;
    let mut g1_17: uint32_t = f0_17;
    let mut h12_17: uint32_t = g0_17;
    *hash.offset(0 as libc::c_uint as isize) = a1_17;
    *hash.offset(1 as libc::c_uint as isize) = b1_17;
    *hash.offset(2 as libc::c_uint as isize) = c1_17;
    *hash.offset(3 as libc::c_uint as isize) = d1_17;
    *hash.offset(4 as libc::c_uint as isize) = e1_17;
    *hash.offset(5 as libc::c_uint as isize) = f1_17;
    *hash.offset(6 as libc::c_uint as isize) = g1_17;
    *hash.offset(7 as libc::c_uint as isize) = h12_17;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_18: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_18: uint32_t = ws[i_1 as usize];
    let mut a0_18: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_18: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_18: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_18: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_18: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_18: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_18: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_18: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_18: uint32_t = k_t_18;
    let mut t1_18: uint32_t = h02_18
        .wrapping_add(
            (e0_18 << 26 as libc::c_uint | e0_18 >> 6 as libc::c_uint)
                ^ ((e0_18 << 21 as libc::c_uint | e0_18 >> 11 as libc::c_uint)
                    ^ (e0_18 << 7 as libc::c_uint | e0_18 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_18 & f0_18 ^ !e0_18 & g0_18)
        .wrapping_add(k_e_t_18)
        .wrapping_add(ws_t_18);
    let mut t2_34: uint32_t = ((a0_18 << 30 as libc::c_uint | a0_18 >> 2 as libc::c_uint)
        ^ ((a0_18 << 19 as libc::c_uint | a0_18 >> 13 as libc::c_uint)
            ^ (a0_18 << 10 as libc::c_uint | a0_18 >> 22 as libc::c_uint)))
        .wrapping_add(a0_18 & b0_18 ^ (a0_18 & c0_18 ^ b0_18 & c0_18));
    let mut a1_18: uint32_t = t1_18.wrapping_add(t2_34);
    let mut b1_18: uint32_t = a0_18;
    let mut c1_18: uint32_t = b0_18;
    let mut d1_18: uint32_t = c0_18;
    let mut e1_18: uint32_t = d0_18.wrapping_add(t1_18);
    let mut f1_18: uint32_t = e0_18;
    let mut g1_18: uint32_t = f0_18;
    let mut h12_18: uint32_t = g0_18;
    *hash.offset(0 as libc::c_uint as isize) = a1_18;
    *hash.offset(1 as libc::c_uint as isize) = b1_18;
    *hash.offset(2 as libc::c_uint as isize) = c1_18;
    *hash.offset(3 as libc::c_uint as isize) = d1_18;
    *hash.offset(4 as libc::c_uint as isize) = e1_18;
    *hash.offset(5 as libc::c_uint as isize) = f1_18;
    *hash.offset(6 as libc::c_uint as isize) = g1_18;
    *hash.offset(7 as libc::c_uint as isize) = h12_18;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_19: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_19: uint32_t = ws[i_1 as usize];
    let mut a0_19: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_19: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_19: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_19: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_19: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_19: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_19: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_19: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_19: uint32_t = k_t_19;
    let mut t1_19: uint32_t = h02_19
        .wrapping_add(
            (e0_19 << 26 as libc::c_uint | e0_19 >> 6 as libc::c_uint)
                ^ ((e0_19 << 21 as libc::c_uint | e0_19 >> 11 as libc::c_uint)
                    ^ (e0_19 << 7 as libc::c_uint | e0_19 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_19 & f0_19 ^ !e0_19 & g0_19)
        .wrapping_add(k_e_t_19)
        .wrapping_add(ws_t_19);
    let mut t2_35: uint32_t = ((a0_19 << 30 as libc::c_uint | a0_19 >> 2 as libc::c_uint)
        ^ ((a0_19 << 19 as libc::c_uint | a0_19 >> 13 as libc::c_uint)
            ^ (a0_19 << 10 as libc::c_uint | a0_19 >> 22 as libc::c_uint)))
        .wrapping_add(a0_19 & b0_19 ^ (a0_19 & c0_19 ^ b0_19 & c0_19));
    let mut a1_19: uint32_t = t1_19.wrapping_add(t2_35);
    let mut b1_19: uint32_t = a0_19;
    let mut c1_19: uint32_t = b0_19;
    let mut d1_19: uint32_t = c0_19;
    let mut e1_19: uint32_t = d0_19.wrapping_add(t1_19);
    let mut f1_19: uint32_t = e0_19;
    let mut g1_19: uint32_t = f0_19;
    let mut h12_19: uint32_t = g0_19;
    *hash.offset(0 as libc::c_uint as isize) = a1_19;
    *hash.offset(1 as libc::c_uint as isize) = b1_19;
    *hash.offset(2 as libc::c_uint as isize) = c1_19;
    *hash.offset(3 as libc::c_uint as isize) = d1_19;
    *hash.offset(4 as libc::c_uint as isize) = e1_19;
    *hash.offset(5 as libc::c_uint as isize) = f1_19;
    *hash.offset(6 as libc::c_uint as isize) = g1_19;
    *hash.offset(7 as libc::c_uint as isize) = h12_19;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_20: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_20: uint32_t = ws[i_1 as usize];
    let mut a0_20: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_20: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_20: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_20: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_20: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_20: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_20: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_20: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_20: uint32_t = k_t_20;
    let mut t1_20: uint32_t = h02_20
        .wrapping_add(
            (e0_20 << 26 as libc::c_uint | e0_20 >> 6 as libc::c_uint)
                ^ ((e0_20 << 21 as libc::c_uint | e0_20 >> 11 as libc::c_uint)
                    ^ (e0_20 << 7 as libc::c_uint | e0_20 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_20 & f0_20 ^ !e0_20 & g0_20)
        .wrapping_add(k_e_t_20)
        .wrapping_add(ws_t_20);
    let mut t2_36: uint32_t = ((a0_20 << 30 as libc::c_uint | a0_20 >> 2 as libc::c_uint)
        ^ ((a0_20 << 19 as libc::c_uint | a0_20 >> 13 as libc::c_uint)
            ^ (a0_20 << 10 as libc::c_uint | a0_20 >> 22 as libc::c_uint)))
        .wrapping_add(a0_20 & b0_20 ^ (a0_20 & c0_20 ^ b0_20 & c0_20));
    let mut a1_20: uint32_t = t1_20.wrapping_add(t2_36);
    let mut b1_20: uint32_t = a0_20;
    let mut c1_20: uint32_t = b0_20;
    let mut d1_20: uint32_t = c0_20;
    let mut e1_20: uint32_t = d0_20.wrapping_add(t1_20);
    let mut f1_20: uint32_t = e0_20;
    let mut g1_20: uint32_t = f0_20;
    let mut h12_20: uint32_t = g0_20;
    *hash.offset(0 as libc::c_uint as isize) = a1_20;
    *hash.offset(1 as libc::c_uint as isize) = b1_20;
    *hash.offset(2 as libc::c_uint as isize) = c1_20;
    *hash.offset(3 as libc::c_uint as isize) = d1_20;
    *hash.offset(4 as libc::c_uint as isize) = e1_20;
    *hash.offset(5 as libc::c_uint as isize) = f1_20;
    *hash.offset(6 as libc::c_uint as isize) = g1_20;
    *hash.offset(7 as libc::c_uint as isize) = h12_20;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_21: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_21: uint32_t = ws[i_1 as usize];
    let mut a0_21: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_21: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_21: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_21: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_21: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_21: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_21: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_21: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_21: uint32_t = k_t_21;
    let mut t1_21: uint32_t = h02_21
        .wrapping_add(
            (e0_21 << 26 as libc::c_uint | e0_21 >> 6 as libc::c_uint)
                ^ ((e0_21 << 21 as libc::c_uint | e0_21 >> 11 as libc::c_uint)
                    ^ (e0_21 << 7 as libc::c_uint | e0_21 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_21 & f0_21 ^ !e0_21 & g0_21)
        .wrapping_add(k_e_t_21)
        .wrapping_add(ws_t_21);
    let mut t2_37: uint32_t = ((a0_21 << 30 as libc::c_uint | a0_21 >> 2 as libc::c_uint)
        ^ ((a0_21 << 19 as libc::c_uint | a0_21 >> 13 as libc::c_uint)
            ^ (a0_21 << 10 as libc::c_uint | a0_21 >> 22 as libc::c_uint)))
        .wrapping_add(a0_21 & b0_21 ^ (a0_21 & c0_21 ^ b0_21 & c0_21));
    let mut a1_21: uint32_t = t1_21.wrapping_add(t2_37);
    let mut b1_21: uint32_t = a0_21;
    let mut c1_21: uint32_t = b0_21;
    let mut d1_21: uint32_t = c0_21;
    let mut e1_21: uint32_t = d0_21.wrapping_add(t1_21);
    let mut f1_21: uint32_t = e0_21;
    let mut g1_21: uint32_t = f0_21;
    let mut h12_21: uint32_t = g0_21;
    *hash.offset(0 as libc::c_uint as isize) = a1_21;
    *hash.offset(1 as libc::c_uint as isize) = b1_21;
    *hash.offset(2 as libc::c_uint as isize) = c1_21;
    *hash.offset(3 as libc::c_uint as isize) = d1_21;
    *hash.offset(4 as libc::c_uint as isize) = e1_21;
    *hash.offset(5 as libc::c_uint as isize) = f1_21;
    *hash.offset(6 as libc::c_uint as isize) = g1_21;
    *hash.offset(7 as libc::c_uint as isize) = h12_21;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_22: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_22: uint32_t = ws[i_1 as usize];
    let mut a0_22: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_22: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_22: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_22: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_22: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_22: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_22: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_22: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_22: uint32_t = k_t_22;
    let mut t1_22: uint32_t = h02_22
        .wrapping_add(
            (e0_22 << 26 as libc::c_uint | e0_22 >> 6 as libc::c_uint)
                ^ ((e0_22 << 21 as libc::c_uint | e0_22 >> 11 as libc::c_uint)
                    ^ (e0_22 << 7 as libc::c_uint | e0_22 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_22 & f0_22 ^ !e0_22 & g0_22)
        .wrapping_add(k_e_t_22)
        .wrapping_add(ws_t_22);
    let mut t2_38: uint32_t = ((a0_22 << 30 as libc::c_uint | a0_22 >> 2 as libc::c_uint)
        ^ ((a0_22 << 19 as libc::c_uint | a0_22 >> 13 as libc::c_uint)
            ^ (a0_22 << 10 as libc::c_uint | a0_22 >> 22 as libc::c_uint)))
        .wrapping_add(a0_22 & b0_22 ^ (a0_22 & c0_22 ^ b0_22 & c0_22));
    let mut a1_22: uint32_t = t1_22.wrapping_add(t2_38);
    let mut b1_22: uint32_t = a0_22;
    let mut c1_22: uint32_t = b0_22;
    let mut d1_22: uint32_t = c0_22;
    let mut e1_22: uint32_t = d0_22.wrapping_add(t1_22);
    let mut f1_22: uint32_t = e0_22;
    let mut g1_22: uint32_t = f0_22;
    let mut h12_22: uint32_t = g0_22;
    *hash.offset(0 as libc::c_uint as isize) = a1_22;
    *hash.offset(1 as libc::c_uint as isize) = b1_22;
    *hash.offset(2 as libc::c_uint as isize) = c1_22;
    *hash.offset(3 as libc::c_uint as isize) = d1_22;
    *hash.offset(4 as libc::c_uint as isize) = e1_22;
    *hash.offset(5 as libc::c_uint as isize) = f1_22;
    *hash.offset(6 as libc::c_uint as isize) = g1_22;
    *hash.offset(7 as libc::c_uint as isize) = h12_22;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_23: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_23: uint32_t = ws[i_1 as usize];
    let mut a0_23: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_23: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_23: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_23: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_23: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_23: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_23: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_23: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_23: uint32_t = k_t_23;
    let mut t1_23: uint32_t = h02_23
        .wrapping_add(
            (e0_23 << 26 as libc::c_uint | e0_23 >> 6 as libc::c_uint)
                ^ ((e0_23 << 21 as libc::c_uint | e0_23 >> 11 as libc::c_uint)
                    ^ (e0_23 << 7 as libc::c_uint | e0_23 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_23 & f0_23 ^ !e0_23 & g0_23)
        .wrapping_add(k_e_t_23)
        .wrapping_add(ws_t_23);
    let mut t2_39: uint32_t = ((a0_23 << 30 as libc::c_uint | a0_23 >> 2 as libc::c_uint)
        ^ ((a0_23 << 19 as libc::c_uint | a0_23 >> 13 as libc::c_uint)
            ^ (a0_23 << 10 as libc::c_uint | a0_23 >> 22 as libc::c_uint)))
        .wrapping_add(a0_23 & b0_23 ^ (a0_23 & c0_23 ^ b0_23 & c0_23));
    let mut a1_23: uint32_t = t1_23.wrapping_add(t2_39);
    let mut b1_23: uint32_t = a0_23;
    let mut c1_23: uint32_t = b0_23;
    let mut d1_23: uint32_t = c0_23;
    let mut e1_23: uint32_t = d0_23.wrapping_add(t1_23);
    let mut f1_23: uint32_t = e0_23;
    let mut g1_23: uint32_t = f0_23;
    let mut h12_23: uint32_t = g0_23;
    *hash.offset(0 as libc::c_uint as isize) = a1_23;
    *hash.offset(1 as libc::c_uint as isize) = b1_23;
    *hash.offset(2 as libc::c_uint as isize) = c1_23;
    *hash.offset(3 as libc::c_uint as isize) = d1_23;
    *hash.offset(4 as libc::c_uint as isize) = e1_23;
    *hash.offset(5 as libc::c_uint as isize) = f1_23;
    *hash.offset(6 as libc::c_uint as isize) = g1_23;
    *hash.offset(7 as libc::c_uint as isize) = h12_23;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_24: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_24: uint32_t = ws[i_1 as usize];
    let mut a0_24: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_24: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_24: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_24: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_24: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_24: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_24: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_24: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_24: uint32_t = k_t_24;
    let mut t1_24: uint32_t = h02_24
        .wrapping_add(
            (e0_24 << 26 as libc::c_uint | e0_24 >> 6 as libc::c_uint)
                ^ ((e0_24 << 21 as libc::c_uint | e0_24 >> 11 as libc::c_uint)
                    ^ (e0_24 << 7 as libc::c_uint | e0_24 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_24 & f0_24 ^ !e0_24 & g0_24)
        .wrapping_add(k_e_t_24)
        .wrapping_add(ws_t_24);
    let mut t2_40: uint32_t = ((a0_24 << 30 as libc::c_uint | a0_24 >> 2 as libc::c_uint)
        ^ ((a0_24 << 19 as libc::c_uint | a0_24 >> 13 as libc::c_uint)
            ^ (a0_24 << 10 as libc::c_uint | a0_24 >> 22 as libc::c_uint)))
        .wrapping_add(a0_24 & b0_24 ^ (a0_24 & c0_24 ^ b0_24 & c0_24));
    let mut a1_24: uint32_t = t1_24.wrapping_add(t2_40);
    let mut b1_24: uint32_t = a0_24;
    let mut c1_24: uint32_t = b0_24;
    let mut d1_24: uint32_t = c0_24;
    let mut e1_24: uint32_t = d0_24.wrapping_add(t1_24);
    let mut f1_24: uint32_t = e0_24;
    let mut g1_24: uint32_t = f0_24;
    let mut h12_24: uint32_t = g0_24;
    *hash.offset(0 as libc::c_uint as isize) = a1_24;
    *hash.offset(1 as libc::c_uint as isize) = b1_24;
    *hash.offset(2 as libc::c_uint as isize) = c1_24;
    *hash.offset(3 as libc::c_uint as isize) = d1_24;
    *hash.offset(4 as libc::c_uint as isize) = e1_24;
    *hash.offset(5 as libc::c_uint as isize) = f1_24;
    *hash.offset(6 as libc::c_uint as isize) = g1_24;
    *hash.offset(7 as libc::c_uint as isize) = h12_24;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_25: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_25: uint32_t = ws[i_1 as usize];
    let mut a0_25: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_25: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_25: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_25: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_25: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_25: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_25: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_25: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_25: uint32_t = k_t_25;
    let mut t1_25: uint32_t = h02_25
        .wrapping_add(
            (e0_25 << 26 as libc::c_uint | e0_25 >> 6 as libc::c_uint)
                ^ ((e0_25 << 21 as libc::c_uint | e0_25 >> 11 as libc::c_uint)
                    ^ (e0_25 << 7 as libc::c_uint | e0_25 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_25 & f0_25 ^ !e0_25 & g0_25)
        .wrapping_add(k_e_t_25)
        .wrapping_add(ws_t_25);
    let mut t2_41: uint32_t = ((a0_25 << 30 as libc::c_uint | a0_25 >> 2 as libc::c_uint)
        ^ ((a0_25 << 19 as libc::c_uint | a0_25 >> 13 as libc::c_uint)
            ^ (a0_25 << 10 as libc::c_uint | a0_25 >> 22 as libc::c_uint)))
        .wrapping_add(a0_25 & b0_25 ^ (a0_25 & c0_25 ^ b0_25 & c0_25));
    let mut a1_25: uint32_t = t1_25.wrapping_add(t2_41);
    let mut b1_25: uint32_t = a0_25;
    let mut c1_25: uint32_t = b0_25;
    let mut d1_25: uint32_t = c0_25;
    let mut e1_25: uint32_t = d0_25.wrapping_add(t1_25);
    let mut f1_25: uint32_t = e0_25;
    let mut g1_25: uint32_t = f0_25;
    let mut h12_25: uint32_t = g0_25;
    *hash.offset(0 as libc::c_uint as isize) = a1_25;
    *hash.offset(1 as libc::c_uint as isize) = b1_25;
    *hash.offset(2 as libc::c_uint as isize) = c1_25;
    *hash.offset(3 as libc::c_uint as isize) = d1_25;
    *hash.offset(4 as libc::c_uint as isize) = e1_25;
    *hash.offset(5 as libc::c_uint as isize) = f1_25;
    *hash.offset(6 as libc::c_uint as isize) = g1_25;
    *hash.offset(7 as libc::c_uint as isize) = h12_25;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_26: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_26: uint32_t = ws[i_1 as usize];
    let mut a0_26: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_26: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_26: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_26: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_26: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_26: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_26: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_26: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_26: uint32_t = k_t_26;
    let mut t1_26: uint32_t = h02_26
        .wrapping_add(
            (e0_26 << 26 as libc::c_uint | e0_26 >> 6 as libc::c_uint)
                ^ ((e0_26 << 21 as libc::c_uint | e0_26 >> 11 as libc::c_uint)
                    ^ (e0_26 << 7 as libc::c_uint | e0_26 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_26 & f0_26 ^ !e0_26 & g0_26)
        .wrapping_add(k_e_t_26)
        .wrapping_add(ws_t_26);
    let mut t2_42: uint32_t = ((a0_26 << 30 as libc::c_uint | a0_26 >> 2 as libc::c_uint)
        ^ ((a0_26 << 19 as libc::c_uint | a0_26 >> 13 as libc::c_uint)
            ^ (a0_26 << 10 as libc::c_uint | a0_26 >> 22 as libc::c_uint)))
        .wrapping_add(a0_26 & b0_26 ^ (a0_26 & c0_26 ^ b0_26 & c0_26));
    let mut a1_26: uint32_t = t1_26.wrapping_add(t2_42);
    let mut b1_26: uint32_t = a0_26;
    let mut c1_26: uint32_t = b0_26;
    let mut d1_26: uint32_t = c0_26;
    let mut e1_26: uint32_t = d0_26.wrapping_add(t1_26);
    let mut f1_26: uint32_t = e0_26;
    let mut g1_26: uint32_t = f0_26;
    let mut h12_26: uint32_t = g0_26;
    *hash.offset(0 as libc::c_uint as isize) = a1_26;
    *hash.offset(1 as libc::c_uint as isize) = b1_26;
    *hash.offset(2 as libc::c_uint as isize) = c1_26;
    *hash.offset(3 as libc::c_uint as isize) = d1_26;
    *hash.offset(4 as libc::c_uint as isize) = e1_26;
    *hash.offset(5 as libc::c_uint as isize) = f1_26;
    *hash.offset(6 as libc::c_uint as isize) = g1_26;
    *hash.offset(7 as libc::c_uint as isize) = h12_26;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_27: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_27: uint32_t = ws[i_1 as usize];
    let mut a0_27: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_27: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_27: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_27: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_27: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_27: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_27: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_27: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_27: uint32_t = k_t_27;
    let mut t1_27: uint32_t = h02_27
        .wrapping_add(
            (e0_27 << 26 as libc::c_uint | e0_27 >> 6 as libc::c_uint)
                ^ ((e0_27 << 21 as libc::c_uint | e0_27 >> 11 as libc::c_uint)
                    ^ (e0_27 << 7 as libc::c_uint | e0_27 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_27 & f0_27 ^ !e0_27 & g0_27)
        .wrapping_add(k_e_t_27)
        .wrapping_add(ws_t_27);
    let mut t2_43: uint32_t = ((a0_27 << 30 as libc::c_uint | a0_27 >> 2 as libc::c_uint)
        ^ ((a0_27 << 19 as libc::c_uint | a0_27 >> 13 as libc::c_uint)
            ^ (a0_27 << 10 as libc::c_uint | a0_27 >> 22 as libc::c_uint)))
        .wrapping_add(a0_27 & b0_27 ^ (a0_27 & c0_27 ^ b0_27 & c0_27));
    let mut a1_27: uint32_t = t1_27.wrapping_add(t2_43);
    let mut b1_27: uint32_t = a0_27;
    let mut c1_27: uint32_t = b0_27;
    let mut d1_27: uint32_t = c0_27;
    let mut e1_27: uint32_t = d0_27.wrapping_add(t1_27);
    let mut f1_27: uint32_t = e0_27;
    let mut g1_27: uint32_t = f0_27;
    let mut h12_27: uint32_t = g0_27;
    *hash.offset(0 as libc::c_uint as isize) = a1_27;
    *hash.offset(1 as libc::c_uint as isize) = b1_27;
    *hash.offset(2 as libc::c_uint as isize) = c1_27;
    *hash.offset(3 as libc::c_uint as isize) = d1_27;
    *hash.offset(4 as libc::c_uint as isize) = e1_27;
    *hash.offset(5 as libc::c_uint as isize) = f1_27;
    *hash.offset(6 as libc::c_uint as isize) = g1_27;
    *hash.offset(7 as libc::c_uint as isize) = h12_27;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_28: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_28: uint32_t = ws[i_1 as usize];
    let mut a0_28: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_28: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_28: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_28: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_28: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_28: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_28: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_28: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_28: uint32_t = k_t_28;
    let mut t1_28: uint32_t = h02_28
        .wrapping_add(
            (e0_28 << 26 as libc::c_uint | e0_28 >> 6 as libc::c_uint)
                ^ ((e0_28 << 21 as libc::c_uint | e0_28 >> 11 as libc::c_uint)
                    ^ (e0_28 << 7 as libc::c_uint | e0_28 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_28 & f0_28 ^ !e0_28 & g0_28)
        .wrapping_add(k_e_t_28)
        .wrapping_add(ws_t_28);
    let mut t2_44: uint32_t = ((a0_28 << 30 as libc::c_uint | a0_28 >> 2 as libc::c_uint)
        ^ ((a0_28 << 19 as libc::c_uint | a0_28 >> 13 as libc::c_uint)
            ^ (a0_28 << 10 as libc::c_uint | a0_28 >> 22 as libc::c_uint)))
        .wrapping_add(a0_28 & b0_28 ^ (a0_28 & c0_28 ^ b0_28 & c0_28));
    let mut a1_28: uint32_t = t1_28.wrapping_add(t2_44);
    let mut b1_28: uint32_t = a0_28;
    let mut c1_28: uint32_t = b0_28;
    let mut d1_28: uint32_t = c0_28;
    let mut e1_28: uint32_t = d0_28.wrapping_add(t1_28);
    let mut f1_28: uint32_t = e0_28;
    let mut g1_28: uint32_t = f0_28;
    let mut h12_28: uint32_t = g0_28;
    *hash.offset(0 as libc::c_uint as isize) = a1_28;
    *hash.offset(1 as libc::c_uint as isize) = b1_28;
    *hash.offset(2 as libc::c_uint as isize) = c1_28;
    *hash.offset(3 as libc::c_uint as isize) = d1_28;
    *hash.offset(4 as libc::c_uint as isize) = e1_28;
    *hash.offset(5 as libc::c_uint as isize) = f1_28;
    *hash.offset(6 as libc::c_uint as isize) = g1_28;
    *hash.offset(7 as libc::c_uint as isize) = h12_28;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_29: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_29: uint32_t = ws[i_1 as usize];
    let mut a0_29: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_29: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_29: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_29: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_29: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_29: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_29: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_29: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_29: uint32_t = k_t_29;
    let mut t1_29: uint32_t = h02_29
        .wrapping_add(
            (e0_29 << 26 as libc::c_uint | e0_29 >> 6 as libc::c_uint)
                ^ ((e0_29 << 21 as libc::c_uint | e0_29 >> 11 as libc::c_uint)
                    ^ (e0_29 << 7 as libc::c_uint | e0_29 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_29 & f0_29 ^ !e0_29 & g0_29)
        .wrapping_add(k_e_t_29)
        .wrapping_add(ws_t_29);
    let mut t2_45: uint32_t = ((a0_29 << 30 as libc::c_uint | a0_29 >> 2 as libc::c_uint)
        ^ ((a0_29 << 19 as libc::c_uint | a0_29 >> 13 as libc::c_uint)
            ^ (a0_29 << 10 as libc::c_uint | a0_29 >> 22 as libc::c_uint)))
        .wrapping_add(a0_29 & b0_29 ^ (a0_29 & c0_29 ^ b0_29 & c0_29));
    let mut a1_29: uint32_t = t1_29.wrapping_add(t2_45);
    let mut b1_29: uint32_t = a0_29;
    let mut c1_29: uint32_t = b0_29;
    let mut d1_29: uint32_t = c0_29;
    let mut e1_29: uint32_t = d0_29.wrapping_add(t1_29);
    let mut f1_29: uint32_t = e0_29;
    let mut g1_29: uint32_t = f0_29;
    let mut h12_29: uint32_t = g0_29;
    *hash.offset(0 as libc::c_uint as isize) = a1_29;
    *hash.offset(1 as libc::c_uint as isize) = b1_29;
    *hash.offset(2 as libc::c_uint as isize) = c1_29;
    *hash.offset(3 as libc::c_uint as isize) = d1_29;
    *hash.offset(4 as libc::c_uint as isize) = e1_29;
    *hash.offset(5 as libc::c_uint as isize) = f1_29;
    *hash.offset(6 as libc::c_uint as isize) = g1_29;
    *hash.offset(7 as libc::c_uint as isize) = h12_29;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_30: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_30: uint32_t = ws[i_1 as usize];
    let mut a0_30: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_30: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_30: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_30: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_30: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_30: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_30: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_30: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_30: uint32_t = k_t_30;
    let mut t1_30: uint32_t = h02_30
        .wrapping_add(
            (e0_30 << 26 as libc::c_uint | e0_30 >> 6 as libc::c_uint)
                ^ ((e0_30 << 21 as libc::c_uint | e0_30 >> 11 as libc::c_uint)
                    ^ (e0_30 << 7 as libc::c_uint | e0_30 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_30 & f0_30 ^ !e0_30 & g0_30)
        .wrapping_add(k_e_t_30)
        .wrapping_add(ws_t_30);
    let mut t2_46: uint32_t = ((a0_30 << 30 as libc::c_uint | a0_30 >> 2 as libc::c_uint)
        ^ ((a0_30 << 19 as libc::c_uint | a0_30 >> 13 as libc::c_uint)
            ^ (a0_30 << 10 as libc::c_uint | a0_30 >> 22 as libc::c_uint)))
        .wrapping_add(a0_30 & b0_30 ^ (a0_30 & c0_30 ^ b0_30 & c0_30));
    let mut a1_30: uint32_t = t1_30.wrapping_add(t2_46);
    let mut b1_30: uint32_t = a0_30;
    let mut c1_30: uint32_t = b0_30;
    let mut d1_30: uint32_t = c0_30;
    let mut e1_30: uint32_t = d0_30.wrapping_add(t1_30);
    let mut f1_30: uint32_t = e0_30;
    let mut g1_30: uint32_t = f0_30;
    let mut h12_30: uint32_t = g0_30;
    *hash.offset(0 as libc::c_uint as isize) = a1_30;
    *hash.offset(1 as libc::c_uint as isize) = b1_30;
    *hash.offset(2 as libc::c_uint as isize) = c1_30;
    *hash.offset(3 as libc::c_uint as isize) = d1_30;
    *hash.offset(4 as libc::c_uint as isize) = e1_30;
    *hash.offset(5 as libc::c_uint as isize) = f1_30;
    *hash.offset(6 as libc::c_uint as isize) = g1_30;
    *hash.offset(7 as libc::c_uint as isize) = h12_30;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 3 as libc::c_uint {
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut t16_15: uint32_t = ws[i_2 as usize];
        let mut t15_15: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_15: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_47: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_15: uint32_t = (t2_47 << 15 as libc::c_uint
            | t2_47 >> 17 as libc::c_uint)
            ^ ((t2_47 << 13 as libc::c_uint | t2_47 >> 19 as libc::c_uint)
                ^ t2_47 >> 10 as libc::c_uint);
        let mut s0_15: uint32_t = (t15_15 << 25 as libc::c_uint
            | t15_15 >> 7 as libc::c_uint)
            ^ ((t15_15 << 14 as libc::c_uint | t15_15 >> 18 as libc::c_uint)
                ^ t15_15 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_15
            .wrapping_add(t7_15)
            .wrapping_add(s0_15)
            .wrapping_add(t16_15);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_16: uint32_t = ws[i_2 as usize];
        let mut t15_16: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_16: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_48: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_16: uint32_t = (t2_48 << 15 as libc::c_uint
            | t2_48 >> 17 as libc::c_uint)
            ^ ((t2_48 << 13 as libc::c_uint | t2_48 >> 19 as libc::c_uint)
                ^ t2_48 >> 10 as libc::c_uint);
        let mut s0_16: uint32_t = (t15_16 << 25 as libc::c_uint
            | t15_16 >> 7 as libc::c_uint)
            ^ ((t15_16 << 14 as libc::c_uint | t15_16 >> 18 as libc::c_uint)
                ^ t15_16 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_16
            .wrapping_add(t7_16)
            .wrapping_add(s0_16)
            .wrapping_add(t16_16);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_17: uint32_t = ws[i_2 as usize];
        let mut t15_17: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_17: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_49: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_17: uint32_t = (t2_49 << 15 as libc::c_uint
            | t2_49 >> 17 as libc::c_uint)
            ^ ((t2_49 << 13 as libc::c_uint | t2_49 >> 19 as libc::c_uint)
                ^ t2_49 >> 10 as libc::c_uint);
        let mut s0_17: uint32_t = (t15_17 << 25 as libc::c_uint
            | t15_17 >> 7 as libc::c_uint)
            ^ ((t15_17 << 14 as libc::c_uint | t15_17 >> 18 as libc::c_uint)
                ^ t15_17 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_17
            .wrapping_add(t7_17)
            .wrapping_add(s0_17)
            .wrapping_add(t16_17);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_18: uint32_t = ws[i_2 as usize];
        let mut t15_18: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_18: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_50: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_18: uint32_t = (t2_50 << 15 as libc::c_uint
            | t2_50 >> 17 as libc::c_uint)
            ^ ((t2_50 << 13 as libc::c_uint | t2_50 >> 19 as libc::c_uint)
                ^ t2_50 >> 10 as libc::c_uint);
        let mut s0_18: uint32_t = (t15_18 << 25 as libc::c_uint
            | t15_18 >> 7 as libc::c_uint)
            ^ ((t15_18 << 14 as libc::c_uint | t15_18 >> 18 as libc::c_uint)
                ^ t15_18 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_18
            .wrapping_add(t7_18)
            .wrapping_add(s0_18)
            .wrapping_add(t16_18);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_19: uint32_t = ws[i_2 as usize];
        let mut t15_19: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_19: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_51: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_19: uint32_t = (t2_51 << 15 as libc::c_uint
            | t2_51 >> 17 as libc::c_uint)
            ^ ((t2_51 << 13 as libc::c_uint | t2_51 >> 19 as libc::c_uint)
                ^ t2_51 >> 10 as libc::c_uint);
        let mut s0_19: uint32_t = (t15_19 << 25 as libc::c_uint
            | t15_19 >> 7 as libc::c_uint)
            ^ ((t15_19 << 14 as libc::c_uint | t15_19 >> 18 as libc::c_uint)
                ^ t15_19 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_19
            .wrapping_add(t7_19)
            .wrapping_add(s0_19)
            .wrapping_add(t16_19);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_20: uint32_t = ws[i_2 as usize];
        let mut t15_20: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_20: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_52: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_20: uint32_t = (t2_52 << 15 as libc::c_uint
            | t2_52 >> 17 as libc::c_uint)
            ^ ((t2_52 << 13 as libc::c_uint | t2_52 >> 19 as libc::c_uint)
                ^ t2_52 >> 10 as libc::c_uint);
        let mut s0_20: uint32_t = (t15_20 << 25 as libc::c_uint
            | t15_20 >> 7 as libc::c_uint)
            ^ ((t15_20 << 14 as libc::c_uint | t15_20 >> 18 as libc::c_uint)
                ^ t15_20 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_20
            .wrapping_add(t7_20)
            .wrapping_add(s0_20)
            .wrapping_add(t16_20);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_21: uint32_t = ws[i_2 as usize];
        let mut t15_21: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_21: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_53: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_21: uint32_t = (t2_53 << 15 as libc::c_uint
            | t2_53 >> 17 as libc::c_uint)
            ^ ((t2_53 << 13 as libc::c_uint | t2_53 >> 19 as libc::c_uint)
                ^ t2_53 >> 10 as libc::c_uint);
        let mut s0_21: uint32_t = (t15_21 << 25 as libc::c_uint
            | t15_21 >> 7 as libc::c_uint)
            ^ ((t15_21 << 14 as libc::c_uint | t15_21 >> 18 as libc::c_uint)
                ^ t15_21 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_21
            .wrapping_add(t7_21)
            .wrapping_add(s0_21)
            .wrapping_add(t16_21);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_22: uint32_t = ws[i_2 as usize];
        let mut t15_22: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_22: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_54: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_22: uint32_t = (t2_54 << 15 as libc::c_uint
            | t2_54 >> 17 as libc::c_uint)
            ^ ((t2_54 << 13 as libc::c_uint | t2_54 >> 19 as libc::c_uint)
                ^ t2_54 >> 10 as libc::c_uint);
        let mut s0_22: uint32_t = (t15_22 << 25 as libc::c_uint
            | t15_22 >> 7 as libc::c_uint)
            ^ ((t15_22 << 14 as libc::c_uint | t15_22 >> 18 as libc::c_uint)
                ^ t15_22 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_22
            .wrapping_add(t7_22)
            .wrapping_add(s0_22)
            .wrapping_add(t16_22);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_23: uint32_t = ws[i_2 as usize];
        let mut t15_23: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_23: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_55: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_23: uint32_t = (t2_55 << 15 as libc::c_uint
            | t2_55 >> 17 as libc::c_uint)
            ^ ((t2_55 << 13 as libc::c_uint | t2_55 >> 19 as libc::c_uint)
                ^ t2_55 >> 10 as libc::c_uint);
        let mut s0_23: uint32_t = (t15_23 << 25 as libc::c_uint
            | t15_23 >> 7 as libc::c_uint)
            ^ ((t15_23 << 14 as libc::c_uint | t15_23 >> 18 as libc::c_uint)
                ^ t15_23 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_23
            .wrapping_add(t7_23)
            .wrapping_add(s0_23)
            .wrapping_add(t16_23);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_24: uint32_t = ws[i_2 as usize];
        let mut t15_24: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_24: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_56: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_24: uint32_t = (t2_56 << 15 as libc::c_uint
            | t2_56 >> 17 as libc::c_uint)
            ^ ((t2_56 << 13 as libc::c_uint | t2_56 >> 19 as libc::c_uint)
                ^ t2_56 >> 10 as libc::c_uint);
        let mut s0_24: uint32_t = (t15_24 << 25 as libc::c_uint
            | t15_24 >> 7 as libc::c_uint)
            ^ ((t15_24 << 14 as libc::c_uint | t15_24 >> 18 as libc::c_uint)
                ^ t15_24 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_24
            .wrapping_add(t7_24)
            .wrapping_add(s0_24)
            .wrapping_add(t16_24);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_25: uint32_t = ws[i_2 as usize];
        let mut t15_25: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_25: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_57: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_25: uint32_t = (t2_57 << 15 as libc::c_uint
            | t2_57 >> 17 as libc::c_uint)
            ^ ((t2_57 << 13 as libc::c_uint | t2_57 >> 19 as libc::c_uint)
                ^ t2_57 >> 10 as libc::c_uint);
        let mut s0_25: uint32_t = (t15_25 << 25 as libc::c_uint
            | t15_25 >> 7 as libc::c_uint)
            ^ ((t15_25 << 14 as libc::c_uint | t15_25 >> 18 as libc::c_uint)
                ^ t15_25 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_25
            .wrapping_add(t7_25)
            .wrapping_add(s0_25)
            .wrapping_add(t16_25);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_26: uint32_t = ws[i_2 as usize];
        let mut t15_26: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_26: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_58: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_26: uint32_t = (t2_58 << 15 as libc::c_uint
            | t2_58 >> 17 as libc::c_uint)
            ^ ((t2_58 << 13 as libc::c_uint | t2_58 >> 19 as libc::c_uint)
                ^ t2_58 >> 10 as libc::c_uint);
        let mut s0_26: uint32_t = (t15_26 << 25 as libc::c_uint
            | t15_26 >> 7 as libc::c_uint)
            ^ ((t15_26 << 14 as libc::c_uint | t15_26 >> 18 as libc::c_uint)
                ^ t15_26 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_26
            .wrapping_add(t7_26)
            .wrapping_add(s0_26)
            .wrapping_add(t16_26);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_27: uint32_t = ws[i_2 as usize];
        let mut t15_27: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_27: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_59: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_27: uint32_t = (t2_59 << 15 as libc::c_uint
            | t2_59 >> 17 as libc::c_uint)
            ^ ((t2_59 << 13 as libc::c_uint | t2_59 >> 19 as libc::c_uint)
                ^ t2_59 >> 10 as libc::c_uint);
        let mut s0_27: uint32_t = (t15_27 << 25 as libc::c_uint
            | t15_27 >> 7 as libc::c_uint)
            ^ ((t15_27 << 14 as libc::c_uint | t15_27 >> 18 as libc::c_uint)
                ^ t15_27 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_27
            .wrapping_add(t7_27)
            .wrapping_add(s0_27)
            .wrapping_add(t16_27);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_28: uint32_t = ws[i_2 as usize];
        let mut t15_28: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_28: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_60: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_28: uint32_t = (t2_60 << 15 as libc::c_uint
            | t2_60 >> 17 as libc::c_uint)
            ^ ((t2_60 << 13 as libc::c_uint | t2_60 >> 19 as libc::c_uint)
                ^ t2_60 >> 10 as libc::c_uint);
        let mut s0_28: uint32_t = (t15_28 << 25 as libc::c_uint
            | t15_28 >> 7 as libc::c_uint)
            ^ ((t15_28 << 14 as libc::c_uint | t15_28 >> 18 as libc::c_uint)
                ^ t15_28 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_28
            .wrapping_add(t7_28)
            .wrapping_add(s0_28)
            .wrapping_add(t16_28);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_29: uint32_t = ws[i_2 as usize];
        let mut t15_29: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_29: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_61: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_29: uint32_t = (t2_61 << 15 as libc::c_uint
            | t2_61 >> 17 as libc::c_uint)
            ^ ((t2_61 << 13 as libc::c_uint | t2_61 >> 19 as libc::c_uint)
                ^ t2_61 >> 10 as libc::c_uint);
        let mut s0_29: uint32_t = (t15_29 << 25 as libc::c_uint
            | t15_29 >> 7 as libc::c_uint)
            ^ ((t15_29 << 14 as libc::c_uint | t15_29 >> 18 as libc::c_uint)
                ^ t15_29 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_29
            .wrapping_add(t7_29)
            .wrapping_add(s0_29)
            .wrapping_add(t16_29);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_30: uint32_t = ws[i_2 as usize];
        let mut t15_30: uint32_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_30: uint32_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_62: uint32_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_30: uint32_t = (t2_62 << 15 as libc::c_uint
            | t2_62 >> 17 as libc::c_uint)
            ^ ((t2_62 << 13 as libc::c_uint | t2_62 >> 19 as libc::c_uint)
                ^ t2_62 >> 10 as libc::c_uint);
        let mut s0_30: uint32_t = (t15_30 << 25 as libc::c_uint
            | t15_30 >> 7 as libc::c_uint)
            ^ ((t15_30 << 14 as libc::c_uint | t15_30 >> 18 as libc::c_uint)
                ^ t15_30 >> 3 as libc::c_uint);
        ws[i_2
            as usize] = s1_30
            .wrapping_add(t7_30)
            .wrapping_add(s0_30)
            .wrapping_add(t16_30);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    let mut k_t_31: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_31: uint32_t = ws[i_3 as usize];
    let mut a0_31: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_31: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_31: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_31: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_31: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_31: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_31: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_31: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_31: uint32_t = k_t_31;
    let mut t1_31: uint32_t = h02_31
        .wrapping_add(
            (e0_31 << 26 as libc::c_uint | e0_31 >> 6 as libc::c_uint)
                ^ ((e0_31 << 21 as libc::c_uint | e0_31 >> 11 as libc::c_uint)
                    ^ (e0_31 << 7 as libc::c_uint | e0_31 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_31 & f0_31 ^ !e0_31 & g0_31)
        .wrapping_add(k_e_t_31)
        .wrapping_add(ws_t_31);
    let mut t2_63: uint32_t = ((a0_31 << 30 as libc::c_uint | a0_31 >> 2 as libc::c_uint)
        ^ ((a0_31 << 19 as libc::c_uint | a0_31 >> 13 as libc::c_uint)
            ^ (a0_31 << 10 as libc::c_uint | a0_31 >> 22 as libc::c_uint)))
        .wrapping_add(a0_31 & b0_31 ^ (a0_31 & c0_31 ^ b0_31 & c0_31));
    let mut a1_31: uint32_t = t1_31.wrapping_add(t2_63);
    let mut b1_31: uint32_t = a0_31;
    let mut c1_31: uint32_t = b0_31;
    let mut d1_31: uint32_t = c0_31;
    let mut e1_31: uint32_t = d0_31.wrapping_add(t1_31);
    let mut f1_31: uint32_t = e0_31;
    let mut g1_31: uint32_t = f0_31;
    let mut h12_31: uint32_t = g0_31;
    *hash.offset(0 as libc::c_uint as isize) = a1_31;
    *hash.offset(1 as libc::c_uint as isize) = b1_31;
    *hash.offset(2 as libc::c_uint as isize) = c1_31;
    *hash.offset(3 as libc::c_uint as isize) = d1_31;
    *hash.offset(4 as libc::c_uint as isize) = e1_31;
    *hash.offset(5 as libc::c_uint as isize) = f1_31;
    *hash.offset(6 as libc::c_uint as isize) = g1_31;
    *hash.offset(7 as libc::c_uint as isize) = h12_31;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_32: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_32: uint32_t = ws[i_3 as usize];
    let mut a0_32: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_32: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_32: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_32: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_32: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_32: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_32: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_32: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_32: uint32_t = k_t_32;
    let mut t1_32: uint32_t = h02_32
        .wrapping_add(
            (e0_32 << 26 as libc::c_uint | e0_32 >> 6 as libc::c_uint)
                ^ ((e0_32 << 21 as libc::c_uint | e0_32 >> 11 as libc::c_uint)
                    ^ (e0_32 << 7 as libc::c_uint | e0_32 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_32 & f0_32 ^ !e0_32 & g0_32)
        .wrapping_add(k_e_t_32)
        .wrapping_add(ws_t_32);
    let mut t2_64: uint32_t = ((a0_32 << 30 as libc::c_uint | a0_32 >> 2 as libc::c_uint)
        ^ ((a0_32 << 19 as libc::c_uint | a0_32 >> 13 as libc::c_uint)
            ^ (a0_32 << 10 as libc::c_uint | a0_32 >> 22 as libc::c_uint)))
        .wrapping_add(a0_32 & b0_32 ^ (a0_32 & c0_32 ^ b0_32 & c0_32));
    let mut a1_32: uint32_t = t1_32.wrapping_add(t2_64);
    let mut b1_32: uint32_t = a0_32;
    let mut c1_32: uint32_t = b0_32;
    let mut d1_32: uint32_t = c0_32;
    let mut e1_32: uint32_t = d0_32.wrapping_add(t1_32);
    let mut f1_32: uint32_t = e0_32;
    let mut g1_32: uint32_t = f0_32;
    let mut h12_32: uint32_t = g0_32;
    *hash.offset(0 as libc::c_uint as isize) = a1_32;
    *hash.offset(1 as libc::c_uint as isize) = b1_32;
    *hash.offset(2 as libc::c_uint as isize) = c1_32;
    *hash.offset(3 as libc::c_uint as isize) = d1_32;
    *hash.offset(4 as libc::c_uint as isize) = e1_32;
    *hash.offset(5 as libc::c_uint as isize) = f1_32;
    *hash.offset(6 as libc::c_uint as isize) = g1_32;
    *hash.offset(7 as libc::c_uint as isize) = h12_32;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_33: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_33: uint32_t = ws[i_3 as usize];
    let mut a0_33: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_33: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_33: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_33: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_33: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_33: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_33: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_33: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_33: uint32_t = k_t_33;
    let mut t1_33: uint32_t = h02_33
        .wrapping_add(
            (e0_33 << 26 as libc::c_uint | e0_33 >> 6 as libc::c_uint)
                ^ ((e0_33 << 21 as libc::c_uint | e0_33 >> 11 as libc::c_uint)
                    ^ (e0_33 << 7 as libc::c_uint | e0_33 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_33 & f0_33 ^ !e0_33 & g0_33)
        .wrapping_add(k_e_t_33)
        .wrapping_add(ws_t_33);
    let mut t2_65: uint32_t = ((a0_33 << 30 as libc::c_uint | a0_33 >> 2 as libc::c_uint)
        ^ ((a0_33 << 19 as libc::c_uint | a0_33 >> 13 as libc::c_uint)
            ^ (a0_33 << 10 as libc::c_uint | a0_33 >> 22 as libc::c_uint)))
        .wrapping_add(a0_33 & b0_33 ^ (a0_33 & c0_33 ^ b0_33 & c0_33));
    let mut a1_33: uint32_t = t1_33.wrapping_add(t2_65);
    let mut b1_33: uint32_t = a0_33;
    let mut c1_33: uint32_t = b0_33;
    let mut d1_33: uint32_t = c0_33;
    let mut e1_33: uint32_t = d0_33.wrapping_add(t1_33);
    let mut f1_33: uint32_t = e0_33;
    let mut g1_33: uint32_t = f0_33;
    let mut h12_33: uint32_t = g0_33;
    *hash.offset(0 as libc::c_uint as isize) = a1_33;
    *hash.offset(1 as libc::c_uint as isize) = b1_33;
    *hash.offset(2 as libc::c_uint as isize) = c1_33;
    *hash.offset(3 as libc::c_uint as isize) = d1_33;
    *hash.offset(4 as libc::c_uint as isize) = e1_33;
    *hash.offset(5 as libc::c_uint as isize) = f1_33;
    *hash.offset(6 as libc::c_uint as isize) = g1_33;
    *hash.offset(7 as libc::c_uint as isize) = h12_33;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_34: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_34: uint32_t = ws[i_3 as usize];
    let mut a0_34: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_34: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_34: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_34: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_34: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_34: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_34: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_34: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_34: uint32_t = k_t_34;
    let mut t1_34: uint32_t = h02_34
        .wrapping_add(
            (e0_34 << 26 as libc::c_uint | e0_34 >> 6 as libc::c_uint)
                ^ ((e0_34 << 21 as libc::c_uint | e0_34 >> 11 as libc::c_uint)
                    ^ (e0_34 << 7 as libc::c_uint | e0_34 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_34 & f0_34 ^ !e0_34 & g0_34)
        .wrapping_add(k_e_t_34)
        .wrapping_add(ws_t_34);
    let mut t2_66: uint32_t = ((a0_34 << 30 as libc::c_uint | a0_34 >> 2 as libc::c_uint)
        ^ ((a0_34 << 19 as libc::c_uint | a0_34 >> 13 as libc::c_uint)
            ^ (a0_34 << 10 as libc::c_uint | a0_34 >> 22 as libc::c_uint)))
        .wrapping_add(a0_34 & b0_34 ^ (a0_34 & c0_34 ^ b0_34 & c0_34));
    let mut a1_34: uint32_t = t1_34.wrapping_add(t2_66);
    let mut b1_34: uint32_t = a0_34;
    let mut c1_34: uint32_t = b0_34;
    let mut d1_34: uint32_t = c0_34;
    let mut e1_34: uint32_t = d0_34.wrapping_add(t1_34);
    let mut f1_34: uint32_t = e0_34;
    let mut g1_34: uint32_t = f0_34;
    let mut h12_34: uint32_t = g0_34;
    *hash.offset(0 as libc::c_uint as isize) = a1_34;
    *hash.offset(1 as libc::c_uint as isize) = b1_34;
    *hash.offset(2 as libc::c_uint as isize) = c1_34;
    *hash.offset(3 as libc::c_uint as isize) = d1_34;
    *hash.offset(4 as libc::c_uint as isize) = e1_34;
    *hash.offset(5 as libc::c_uint as isize) = f1_34;
    *hash.offset(6 as libc::c_uint as isize) = g1_34;
    *hash.offset(7 as libc::c_uint as isize) = h12_34;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_35: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_35: uint32_t = ws[i_3 as usize];
    let mut a0_35: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_35: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_35: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_35: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_35: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_35: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_35: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_35: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_35: uint32_t = k_t_35;
    let mut t1_35: uint32_t = h02_35
        .wrapping_add(
            (e0_35 << 26 as libc::c_uint | e0_35 >> 6 as libc::c_uint)
                ^ ((e0_35 << 21 as libc::c_uint | e0_35 >> 11 as libc::c_uint)
                    ^ (e0_35 << 7 as libc::c_uint | e0_35 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_35 & f0_35 ^ !e0_35 & g0_35)
        .wrapping_add(k_e_t_35)
        .wrapping_add(ws_t_35);
    let mut t2_67: uint32_t = ((a0_35 << 30 as libc::c_uint | a0_35 >> 2 as libc::c_uint)
        ^ ((a0_35 << 19 as libc::c_uint | a0_35 >> 13 as libc::c_uint)
            ^ (a0_35 << 10 as libc::c_uint | a0_35 >> 22 as libc::c_uint)))
        .wrapping_add(a0_35 & b0_35 ^ (a0_35 & c0_35 ^ b0_35 & c0_35));
    let mut a1_35: uint32_t = t1_35.wrapping_add(t2_67);
    let mut b1_35: uint32_t = a0_35;
    let mut c1_35: uint32_t = b0_35;
    let mut d1_35: uint32_t = c0_35;
    let mut e1_35: uint32_t = d0_35.wrapping_add(t1_35);
    let mut f1_35: uint32_t = e0_35;
    let mut g1_35: uint32_t = f0_35;
    let mut h12_35: uint32_t = g0_35;
    *hash.offset(0 as libc::c_uint as isize) = a1_35;
    *hash.offset(1 as libc::c_uint as isize) = b1_35;
    *hash.offset(2 as libc::c_uint as isize) = c1_35;
    *hash.offset(3 as libc::c_uint as isize) = d1_35;
    *hash.offset(4 as libc::c_uint as isize) = e1_35;
    *hash.offset(5 as libc::c_uint as isize) = f1_35;
    *hash.offset(6 as libc::c_uint as isize) = g1_35;
    *hash.offset(7 as libc::c_uint as isize) = h12_35;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_36: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_36: uint32_t = ws[i_3 as usize];
    let mut a0_36: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_36: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_36: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_36: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_36: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_36: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_36: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_36: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_36: uint32_t = k_t_36;
    let mut t1_36: uint32_t = h02_36
        .wrapping_add(
            (e0_36 << 26 as libc::c_uint | e0_36 >> 6 as libc::c_uint)
                ^ ((e0_36 << 21 as libc::c_uint | e0_36 >> 11 as libc::c_uint)
                    ^ (e0_36 << 7 as libc::c_uint | e0_36 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_36 & f0_36 ^ !e0_36 & g0_36)
        .wrapping_add(k_e_t_36)
        .wrapping_add(ws_t_36);
    let mut t2_68: uint32_t = ((a0_36 << 30 as libc::c_uint | a0_36 >> 2 as libc::c_uint)
        ^ ((a0_36 << 19 as libc::c_uint | a0_36 >> 13 as libc::c_uint)
            ^ (a0_36 << 10 as libc::c_uint | a0_36 >> 22 as libc::c_uint)))
        .wrapping_add(a0_36 & b0_36 ^ (a0_36 & c0_36 ^ b0_36 & c0_36));
    let mut a1_36: uint32_t = t1_36.wrapping_add(t2_68);
    let mut b1_36: uint32_t = a0_36;
    let mut c1_36: uint32_t = b0_36;
    let mut d1_36: uint32_t = c0_36;
    let mut e1_36: uint32_t = d0_36.wrapping_add(t1_36);
    let mut f1_36: uint32_t = e0_36;
    let mut g1_36: uint32_t = f0_36;
    let mut h12_36: uint32_t = g0_36;
    *hash.offset(0 as libc::c_uint as isize) = a1_36;
    *hash.offset(1 as libc::c_uint as isize) = b1_36;
    *hash.offset(2 as libc::c_uint as isize) = c1_36;
    *hash.offset(3 as libc::c_uint as isize) = d1_36;
    *hash.offset(4 as libc::c_uint as isize) = e1_36;
    *hash.offset(5 as libc::c_uint as isize) = f1_36;
    *hash.offset(6 as libc::c_uint as isize) = g1_36;
    *hash.offset(7 as libc::c_uint as isize) = h12_36;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_37: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_37: uint32_t = ws[i_3 as usize];
    let mut a0_37: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_37: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_37: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_37: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_37: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_37: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_37: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_37: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_37: uint32_t = k_t_37;
    let mut t1_37: uint32_t = h02_37
        .wrapping_add(
            (e0_37 << 26 as libc::c_uint | e0_37 >> 6 as libc::c_uint)
                ^ ((e0_37 << 21 as libc::c_uint | e0_37 >> 11 as libc::c_uint)
                    ^ (e0_37 << 7 as libc::c_uint | e0_37 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_37 & f0_37 ^ !e0_37 & g0_37)
        .wrapping_add(k_e_t_37)
        .wrapping_add(ws_t_37);
    let mut t2_69: uint32_t = ((a0_37 << 30 as libc::c_uint | a0_37 >> 2 as libc::c_uint)
        ^ ((a0_37 << 19 as libc::c_uint | a0_37 >> 13 as libc::c_uint)
            ^ (a0_37 << 10 as libc::c_uint | a0_37 >> 22 as libc::c_uint)))
        .wrapping_add(a0_37 & b0_37 ^ (a0_37 & c0_37 ^ b0_37 & c0_37));
    let mut a1_37: uint32_t = t1_37.wrapping_add(t2_69);
    let mut b1_37: uint32_t = a0_37;
    let mut c1_37: uint32_t = b0_37;
    let mut d1_37: uint32_t = c0_37;
    let mut e1_37: uint32_t = d0_37.wrapping_add(t1_37);
    let mut f1_37: uint32_t = e0_37;
    let mut g1_37: uint32_t = f0_37;
    let mut h12_37: uint32_t = g0_37;
    *hash.offset(0 as libc::c_uint as isize) = a1_37;
    *hash.offset(1 as libc::c_uint as isize) = b1_37;
    *hash.offset(2 as libc::c_uint as isize) = c1_37;
    *hash.offset(3 as libc::c_uint as isize) = d1_37;
    *hash.offset(4 as libc::c_uint as isize) = e1_37;
    *hash.offset(5 as libc::c_uint as isize) = f1_37;
    *hash.offset(6 as libc::c_uint as isize) = g1_37;
    *hash.offset(7 as libc::c_uint as isize) = h12_37;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_38: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_38: uint32_t = ws[i_3 as usize];
    let mut a0_38: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_38: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_38: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_38: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_38: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_38: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_38: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_38: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_38: uint32_t = k_t_38;
    let mut t1_38: uint32_t = h02_38
        .wrapping_add(
            (e0_38 << 26 as libc::c_uint | e0_38 >> 6 as libc::c_uint)
                ^ ((e0_38 << 21 as libc::c_uint | e0_38 >> 11 as libc::c_uint)
                    ^ (e0_38 << 7 as libc::c_uint | e0_38 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_38 & f0_38 ^ !e0_38 & g0_38)
        .wrapping_add(k_e_t_38)
        .wrapping_add(ws_t_38);
    let mut t2_70: uint32_t = ((a0_38 << 30 as libc::c_uint | a0_38 >> 2 as libc::c_uint)
        ^ ((a0_38 << 19 as libc::c_uint | a0_38 >> 13 as libc::c_uint)
            ^ (a0_38 << 10 as libc::c_uint | a0_38 >> 22 as libc::c_uint)))
        .wrapping_add(a0_38 & b0_38 ^ (a0_38 & c0_38 ^ b0_38 & c0_38));
    let mut a1_38: uint32_t = t1_38.wrapping_add(t2_70);
    let mut b1_38: uint32_t = a0_38;
    let mut c1_38: uint32_t = b0_38;
    let mut d1_38: uint32_t = c0_38;
    let mut e1_38: uint32_t = d0_38.wrapping_add(t1_38);
    let mut f1_38: uint32_t = e0_38;
    let mut g1_38: uint32_t = f0_38;
    let mut h12_38: uint32_t = g0_38;
    *hash.offset(0 as libc::c_uint as isize) = a1_38;
    *hash.offset(1 as libc::c_uint as isize) = b1_38;
    *hash.offset(2 as libc::c_uint as isize) = c1_38;
    *hash.offset(3 as libc::c_uint as isize) = d1_38;
    *hash.offset(4 as libc::c_uint as isize) = e1_38;
    *hash.offset(5 as libc::c_uint as isize) = f1_38;
    *hash.offset(6 as libc::c_uint as isize) = g1_38;
    *hash.offset(7 as libc::c_uint as isize) = h12_38;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_39: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_39: uint32_t = ws[i_3 as usize];
    let mut a0_39: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_39: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_39: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_39: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_39: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_39: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_39: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_39: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_39: uint32_t = k_t_39;
    let mut t1_39: uint32_t = h02_39
        .wrapping_add(
            (e0_39 << 26 as libc::c_uint | e0_39 >> 6 as libc::c_uint)
                ^ ((e0_39 << 21 as libc::c_uint | e0_39 >> 11 as libc::c_uint)
                    ^ (e0_39 << 7 as libc::c_uint | e0_39 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_39 & f0_39 ^ !e0_39 & g0_39)
        .wrapping_add(k_e_t_39)
        .wrapping_add(ws_t_39);
    let mut t2_71: uint32_t = ((a0_39 << 30 as libc::c_uint | a0_39 >> 2 as libc::c_uint)
        ^ ((a0_39 << 19 as libc::c_uint | a0_39 >> 13 as libc::c_uint)
            ^ (a0_39 << 10 as libc::c_uint | a0_39 >> 22 as libc::c_uint)))
        .wrapping_add(a0_39 & b0_39 ^ (a0_39 & c0_39 ^ b0_39 & c0_39));
    let mut a1_39: uint32_t = t1_39.wrapping_add(t2_71);
    let mut b1_39: uint32_t = a0_39;
    let mut c1_39: uint32_t = b0_39;
    let mut d1_39: uint32_t = c0_39;
    let mut e1_39: uint32_t = d0_39.wrapping_add(t1_39);
    let mut f1_39: uint32_t = e0_39;
    let mut g1_39: uint32_t = f0_39;
    let mut h12_39: uint32_t = g0_39;
    *hash.offset(0 as libc::c_uint as isize) = a1_39;
    *hash.offset(1 as libc::c_uint as isize) = b1_39;
    *hash.offset(2 as libc::c_uint as isize) = c1_39;
    *hash.offset(3 as libc::c_uint as isize) = d1_39;
    *hash.offset(4 as libc::c_uint as isize) = e1_39;
    *hash.offset(5 as libc::c_uint as isize) = f1_39;
    *hash.offset(6 as libc::c_uint as isize) = g1_39;
    *hash.offset(7 as libc::c_uint as isize) = h12_39;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_40: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_40: uint32_t = ws[i_3 as usize];
    let mut a0_40: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_40: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_40: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_40: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_40: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_40: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_40: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_40: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_40: uint32_t = k_t_40;
    let mut t1_40: uint32_t = h02_40
        .wrapping_add(
            (e0_40 << 26 as libc::c_uint | e0_40 >> 6 as libc::c_uint)
                ^ ((e0_40 << 21 as libc::c_uint | e0_40 >> 11 as libc::c_uint)
                    ^ (e0_40 << 7 as libc::c_uint | e0_40 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_40 & f0_40 ^ !e0_40 & g0_40)
        .wrapping_add(k_e_t_40)
        .wrapping_add(ws_t_40);
    let mut t2_72: uint32_t = ((a0_40 << 30 as libc::c_uint | a0_40 >> 2 as libc::c_uint)
        ^ ((a0_40 << 19 as libc::c_uint | a0_40 >> 13 as libc::c_uint)
            ^ (a0_40 << 10 as libc::c_uint | a0_40 >> 22 as libc::c_uint)))
        .wrapping_add(a0_40 & b0_40 ^ (a0_40 & c0_40 ^ b0_40 & c0_40));
    let mut a1_40: uint32_t = t1_40.wrapping_add(t2_72);
    let mut b1_40: uint32_t = a0_40;
    let mut c1_40: uint32_t = b0_40;
    let mut d1_40: uint32_t = c0_40;
    let mut e1_40: uint32_t = d0_40.wrapping_add(t1_40);
    let mut f1_40: uint32_t = e0_40;
    let mut g1_40: uint32_t = f0_40;
    let mut h12_40: uint32_t = g0_40;
    *hash.offset(0 as libc::c_uint as isize) = a1_40;
    *hash.offset(1 as libc::c_uint as isize) = b1_40;
    *hash.offset(2 as libc::c_uint as isize) = c1_40;
    *hash.offset(3 as libc::c_uint as isize) = d1_40;
    *hash.offset(4 as libc::c_uint as isize) = e1_40;
    *hash.offset(5 as libc::c_uint as isize) = f1_40;
    *hash.offset(6 as libc::c_uint as isize) = g1_40;
    *hash.offset(7 as libc::c_uint as isize) = h12_40;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_41: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_41: uint32_t = ws[i_3 as usize];
    let mut a0_41: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_41: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_41: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_41: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_41: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_41: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_41: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_41: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_41: uint32_t = k_t_41;
    let mut t1_41: uint32_t = h02_41
        .wrapping_add(
            (e0_41 << 26 as libc::c_uint | e0_41 >> 6 as libc::c_uint)
                ^ ((e0_41 << 21 as libc::c_uint | e0_41 >> 11 as libc::c_uint)
                    ^ (e0_41 << 7 as libc::c_uint | e0_41 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_41 & f0_41 ^ !e0_41 & g0_41)
        .wrapping_add(k_e_t_41)
        .wrapping_add(ws_t_41);
    let mut t2_73: uint32_t = ((a0_41 << 30 as libc::c_uint | a0_41 >> 2 as libc::c_uint)
        ^ ((a0_41 << 19 as libc::c_uint | a0_41 >> 13 as libc::c_uint)
            ^ (a0_41 << 10 as libc::c_uint | a0_41 >> 22 as libc::c_uint)))
        .wrapping_add(a0_41 & b0_41 ^ (a0_41 & c0_41 ^ b0_41 & c0_41));
    let mut a1_41: uint32_t = t1_41.wrapping_add(t2_73);
    let mut b1_41: uint32_t = a0_41;
    let mut c1_41: uint32_t = b0_41;
    let mut d1_41: uint32_t = c0_41;
    let mut e1_41: uint32_t = d0_41.wrapping_add(t1_41);
    let mut f1_41: uint32_t = e0_41;
    let mut g1_41: uint32_t = f0_41;
    let mut h12_41: uint32_t = g0_41;
    *hash.offset(0 as libc::c_uint as isize) = a1_41;
    *hash.offset(1 as libc::c_uint as isize) = b1_41;
    *hash.offset(2 as libc::c_uint as isize) = c1_41;
    *hash.offset(3 as libc::c_uint as isize) = d1_41;
    *hash.offset(4 as libc::c_uint as isize) = e1_41;
    *hash.offset(5 as libc::c_uint as isize) = f1_41;
    *hash.offset(6 as libc::c_uint as isize) = g1_41;
    *hash.offset(7 as libc::c_uint as isize) = h12_41;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_42: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_42: uint32_t = ws[i_3 as usize];
    let mut a0_42: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_42: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_42: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_42: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_42: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_42: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_42: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_42: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_42: uint32_t = k_t_42;
    let mut t1_42: uint32_t = h02_42
        .wrapping_add(
            (e0_42 << 26 as libc::c_uint | e0_42 >> 6 as libc::c_uint)
                ^ ((e0_42 << 21 as libc::c_uint | e0_42 >> 11 as libc::c_uint)
                    ^ (e0_42 << 7 as libc::c_uint | e0_42 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_42 & f0_42 ^ !e0_42 & g0_42)
        .wrapping_add(k_e_t_42)
        .wrapping_add(ws_t_42);
    let mut t2_74: uint32_t = ((a0_42 << 30 as libc::c_uint | a0_42 >> 2 as libc::c_uint)
        ^ ((a0_42 << 19 as libc::c_uint | a0_42 >> 13 as libc::c_uint)
            ^ (a0_42 << 10 as libc::c_uint | a0_42 >> 22 as libc::c_uint)))
        .wrapping_add(a0_42 & b0_42 ^ (a0_42 & c0_42 ^ b0_42 & c0_42));
    let mut a1_42: uint32_t = t1_42.wrapping_add(t2_74);
    let mut b1_42: uint32_t = a0_42;
    let mut c1_42: uint32_t = b0_42;
    let mut d1_42: uint32_t = c0_42;
    let mut e1_42: uint32_t = d0_42.wrapping_add(t1_42);
    let mut f1_42: uint32_t = e0_42;
    let mut g1_42: uint32_t = f0_42;
    let mut h12_42: uint32_t = g0_42;
    *hash.offset(0 as libc::c_uint as isize) = a1_42;
    *hash.offset(1 as libc::c_uint as isize) = b1_42;
    *hash.offset(2 as libc::c_uint as isize) = c1_42;
    *hash.offset(3 as libc::c_uint as isize) = d1_42;
    *hash.offset(4 as libc::c_uint as isize) = e1_42;
    *hash.offset(5 as libc::c_uint as isize) = f1_42;
    *hash.offset(6 as libc::c_uint as isize) = g1_42;
    *hash.offset(7 as libc::c_uint as isize) = h12_42;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_43: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_43: uint32_t = ws[i_3 as usize];
    let mut a0_43: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_43: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_43: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_43: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_43: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_43: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_43: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_43: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_43: uint32_t = k_t_43;
    let mut t1_43: uint32_t = h02_43
        .wrapping_add(
            (e0_43 << 26 as libc::c_uint | e0_43 >> 6 as libc::c_uint)
                ^ ((e0_43 << 21 as libc::c_uint | e0_43 >> 11 as libc::c_uint)
                    ^ (e0_43 << 7 as libc::c_uint | e0_43 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_43 & f0_43 ^ !e0_43 & g0_43)
        .wrapping_add(k_e_t_43)
        .wrapping_add(ws_t_43);
    let mut t2_75: uint32_t = ((a0_43 << 30 as libc::c_uint | a0_43 >> 2 as libc::c_uint)
        ^ ((a0_43 << 19 as libc::c_uint | a0_43 >> 13 as libc::c_uint)
            ^ (a0_43 << 10 as libc::c_uint | a0_43 >> 22 as libc::c_uint)))
        .wrapping_add(a0_43 & b0_43 ^ (a0_43 & c0_43 ^ b0_43 & c0_43));
    let mut a1_43: uint32_t = t1_43.wrapping_add(t2_75);
    let mut b1_43: uint32_t = a0_43;
    let mut c1_43: uint32_t = b0_43;
    let mut d1_43: uint32_t = c0_43;
    let mut e1_43: uint32_t = d0_43.wrapping_add(t1_43);
    let mut f1_43: uint32_t = e0_43;
    let mut g1_43: uint32_t = f0_43;
    let mut h12_43: uint32_t = g0_43;
    *hash.offset(0 as libc::c_uint as isize) = a1_43;
    *hash.offset(1 as libc::c_uint as isize) = b1_43;
    *hash.offset(2 as libc::c_uint as isize) = c1_43;
    *hash.offset(3 as libc::c_uint as isize) = d1_43;
    *hash.offset(4 as libc::c_uint as isize) = e1_43;
    *hash.offset(5 as libc::c_uint as isize) = f1_43;
    *hash.offset(6 as libc::c_uint as isize) = g1_43;
    *hash.offset(7 as libc::c_uint as isize) = h12_43;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_44: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_44: uint32_t = ws[i_3 as usize];
    let mut a0_44: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_44: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_44: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_44: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_44: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_44: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_44: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_44: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_44: uint32_t = k_t_44;
    let mut t1_44: uint32_t = h02_44
        .wrapping_add(
            (e0_44 << 26 as libc::c_uint | e0_44 >> 6 as libc::c_uint)
                ^ ((e0_44 << 21 as libc::c_uint | e0_44 >> 11 as libc::c_uint)
                    ^ (e0_44 << 7 as libc::c_uint | e0_44 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_44 & f0_44 ^ !e0_44 & g0_44)
        .wrapping_add(k_e_t_44)
        .wrapping_add(ws_t_44);
    let mut t2_76: uint32_t = ((a0_44 << 30 as libc::c_uint | a0_44 >> 2 as libc::c_uint)
        ^ ((a0_44 << 19 as libc::c_uint | a0_44 >> 13 as libc::c_uint)
            ^ (a0_44 << 10 as libc::c_uint | a0_44 >> 22 as libc::c_uint)))
        .wrapping_add(a0_44 & b0_44 ^ (a0_44 & c0_44 ^ b0_44 & c0_44));
    let mut a1_44: uint32_t = t1_44.wrapping_add(t2_76);
    let mut b1_44: uint32_t = a0_44;
    let mut c1_44: uint32_t = b0_44;
    let mut d1_44: uint32_t = c0_44;
    let mut e1_44: uint32_t = d0_44.wrapping_add(t1_44);
    let mut f1_44: uint32_t = e0_44;
    let mut g1_44: uint32_t = f0_44;
    let mut h12_44: uint32_t = g0_44;
    *hash.offset(0 as libc::c_uint as isize) = a1_44;
    *hash.offset(1 as libc::c_uint as isize) = b1_44;
    *hash.offset(2 as libc::c_uint as isize) = c1_44;
    *hash.offset(3 as libc::c_uint as isize) = d1_44;
    *hash.offset(4 as libc::c_uint as isize) = e1_44;
    *hash.offset(5 as libc::c_uint as isize) = f1_44;
    *hash.offset(6 as libc::c_uint as isize) = g1_44;
    *hash.offset(7 as libc::c_uint as isize) = h12_44;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_45: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_45: uint32_t = ws[i_3 as usize];
    let mut a0_45: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_45: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_45: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_45: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_45: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_45: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_45: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_45: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_45: uint32_t = k_t_45;
    let mut t1_45: uint32_t = h02_45
        .wrapping_add(
            (e0_45 << 26 as libc::c_uint | e0_45 >> 6 as libc::c_uint)
                ^ ((e0_45 << 21 as libc::c_uint | e0_45 >> 11 as libc::c_uint)
                    ^ (e0_45 << 7 as libc::c_uint | e0_45 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_45 & f0_45 ^ !e0_45 & g0_45)
        .wrapping_add(k_e_t_45)
        .wrapping_add(ws_t_45);
    let mut t2_77: uint32_t = ((a0_45 << 30 as libc::c_uint | a0_45 >> 2 as libc::c_uint)
        ^ ((a0_45 << 19 as libc::c_uint | a0_45 >> 13 as libc::c_uint)
            ^ (a0_45 << 10 as libc::c_uint | a0_45 >> 22 as libc::c_uint)))
        .wrapping_add(a0_45 & b0_45 ^ (a0_45 & c0_45 ^ b0_45 & c0_45));
    let mut a1_45: uint32_t = t1_45.wrapping_add(t2_77);
    let mut b1_45: uint32_t = a0_45;
    let mut c1_45: uint32_t = b0_45;
    let mut d1_45: uint32_t = c0_45;
    let mut e1_45: uint32_t = d0_45.wrapping_add(t1_45);
    let mut f1_45: uint32_t = e0_45;
    let mut g1_45: uint32_t = f0_45;
    let mut h12_45: uint32_t = g0_45;
    *hash.offset(0 as libc::c_uint as isize) = a1_45;
    *hash.offset(1 as libc::c_uint as isize) = b1_45;
    *hash.offset(2 as libc::c_uint as isize) = c1_45;
    *hash.offset(3 as libc::c_uint as isize) = d1_45;
    *hash.offset(4 as libc::c_uint as isize) = e1_45;
    *hash.offset(5 as libc::c_uint as isize) = f1_45;
    *hash.offset(6 as libc::c_uint as isize) = g1_45;
    *hash.offset(7 as libc::c_uint as isize) = h12_45;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_46: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_46: uint32_t = ws[i_3 as usize];
    let mut a0_46: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_46: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_46: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_46: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_46: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_46: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_46: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_46: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_46: uint32_t = k_t_46;
    let mut t1_46: uint32_t = h02_46
        .wrapping_add(
            (e0_46 << 26 as libc::c_uint | e0_46 >> 6 as libc::c_uint)
                ^ ((e0_46 << 21 as libc::c_uint | e0_46 >> 11 as libc::c_uint)
                    ^ (e0_46 << 7 as libc::c_uint | e0_46 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_46 & f0_46 ^ !e0_46 & g0_46)
        .wrapping_add(k_e_t_46)
        .wrapping_add(ws_t_46);
    let mut t2_78: uint32_t = ((a0_46 << 30 as libc::c_uint | a0_46 >> 2 as libc::c_uint)
        ^ ((a0_46 << 19 as libc::c_uint | a0_46 >> 13 as libc::c_uint)
            ^ (a0_46 << 10 as libc::c_uint | a0_46 >> 22 as libc::c_uint)))
        .wrapping_add(a0_46 & b0_46 ^ (a0_46 & c0_46 ^ b0_46 & c0_46));
    let mut a1_46: uint32_t = t1_46.wrapping_add(t2_78);
    let mut b1_46: uint32_t = a0_46;
    let mut c1_46: uint32_t = b0_46;
    let mut d1_46: uint32_t = c0_46;
    let mut e1_46: uint32_t = d0_46.wrapping_add(t1_46);
    let mut f1_46: uint32_t = e0_46;
    let mut g1_46: uint32_t = f0_46;
    let mut h12_46: uint32_t = g0_46;
    *hash.offset(0 as libc::c_uint as isize) = a1_46;
    *hash.offset(1 as libc::c_uint as isize) = b1_46;
    *hash.offset(2 as libc::c_uint as isize) = c1_46;
    *hash.offset(3 as libc::c_uint as isize) = d1_46;
    *hash.offset(4 as libc::c_uint as isize) = e1_46;
    *hash.offset(5 as libc::c_uint as isize) = f1_46;
    *hash.offset(6 as libc::c_uint as isize) = g1_46;
    *hash.offset(7 as libc::c_uint as isize) = h12_46;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 3 as libc::c_uint {
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut t16_31: uint32_t = ws[i_4 as usize];
        let mut t15_31: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_31: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_79: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_31: uint32_t = (t2_79 << 15 as libc::c_uint
            | t2_79 >> 17 as libc::c_uint)
            ^ ((t2_79 << 13 as libc::c_uint | t2_79 >> 19 as libc::c_uint)
                ^ t2_79 >> 10 as libc::c_uint);
        let mut s0_31: uint32_t = (t15_31 << 25 as libc::c_uint
            | t15_31 >> 7 as libc::c_uint)
            ^ ((t15_31 << 14 as libc::c_uint | t15_31 >> 18 as libc::c_uint)
                ^ t15_31 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_31
            .wrapping_add(t7_31)
            .wrapping_add(s0_31)
            .wrapping_add(t16_31);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_32: uint32_t = ws[i_4 as usize];
        let mut t15_32: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_32: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_80: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_32: uint32_t = (t2_80 << 15 as libc::c_uint
            | t2_80 >> 17 as libc::c_uint)
            ^ ((t2_80 << 13 as libc::c_uint | t2_80 >> 19 as libc::c_uint)
                ^ t2_80 >> 10 as libc::c_uint);
        let mut s0_32: uint32_t = (t15_32 << 25 as libc::c_uint
            | t15_32 >> 7 as libc::c_uint)
            ^ ((t15_32 << 14 as libc::c_uint | t15_32 >> 18 as libc::c_uint)
                ^ t15_32 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_32
            .wrapping_add(t7_32)
            .wrapping_add(s0_32)
            .wrapping_add(t16_32);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_33: uint32_t = ws[i_4 as usize];
        let mut t15_33: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_33: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_81: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_33: uint32_t = (t2_81 << 15 as libc::c_uint
            | t2_81 >> 17 as libc::c_uint)
            ^ ((t2_81 << 13 as libc::c_uint | t2_81 >> 19 as libc::c_uint)
                ^ t2_81 >> 10 as libc::c_uint);
        let mut s0_33: uint32_t = (t15_33 << 25 as libc::c_uint
            | t15_33 >> 7 as libc::c_uint)
            ^ ((t15_33 << 14 as libc::c_uint | t15_33 >> 18 as libc::c_uint)
                ^ t15_33 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_33
            .wrapping_add(t7_33)
            .wrapping_add(s0_33)
            .wrapping_add(t16_33);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_34: uint32_t = ws[i_4 as usize];
        let mut t15_34: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_34: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_82: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_34: uint32_t = (t2_82 << 15 as libc::c_uint
            | t2_82 >> 17 as libc::c_uint)
            ^ ((t2_82 << 13 as libc::c_uint | t2_82 >> 19 as libc::c_uint)
                ^ t2_82 >> 10 as libc::c_uint);
        let mut s0_34: uint32_t = (t15_34 << 25 as libc::c_uint
            | t15_34 >> 7 as libc::c_uint)
            ^ ((t15_34 << 14 as libc::c_uint | t15_34 >> 18 as libc::c_uint)
                ^ t15_34 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_34
            .wrapping_add(t7_34)
            .wrapping_add(s0_34)
            .wrapping_add(t16_34);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_35: uint32_t = ws[i_4 as usize];
        let mut t15_35: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_35: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_83: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_35: uint32_t = (t2_83 << 15 as libc::c_uint
            | t2_83 >> 17 as libc::c_uint)
            ^ ((t2_83 << 13 as libc::c_uint | t2_83 >> 19 as libc::c_uint)
                ^ t2_83 >> 10 as libc::c_uint);
        let mut s0_35: uint32_t = (t15_35 << 25 as libc::c_uint
            | t15_35 >> 7 as libc::c_uint)
            ^ ((t15_35 << 14 as libc::c_uint | t15_35 >> 18 as libc::c_uint)
                ^ t15_35 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_35
            .wrapping_add(t7_35)
            .wrapping_add(s0_35)
            .wrapping_add(t16_35);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_36: uint32_t = ws[i_4 as usize];
        let mut t15_36: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_36: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_84: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_36: uint32_t = (t2_84 << 15 as libc::c_uint
            | t2_84 >> 17 as libc::c_uint)
            ^ ((t2_84 << 13 as libc::c_uint | t2_84 >> 19 as libc::c_uint)
                ^ t2_84 >> 10 as libc::c_uint);
        let mut s0_36: uint32_t = (t15_36 << 25 as libc::c_uint
            | t15_36 >> 7 as libc::c_uint)
            ^ ((t15_36 << 14 as libc::c_uint | t15_36 >> 18 as libc::c_uint)
                ^ t15_36 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_36
            .wrapping_add(t7_36)
            .wrapping_add(s0_36)
            .wrapping_add(t16_36);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_37: uint32_t = ws[i_4 as usize];
        let mut t15_37: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_37: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_85: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_37: uint32_t = (t2_85 << 15 as libc::c_uint
            | t2_85 >> 17 as libc::c_uint)
            ^ ((t2_85 << 13 as libc::c_uint | t2_85 >> 19 as libc::c_uint)
                ^ t2_85 >> 10 as libc::c_uint);
        let mut s0_37: uint32_t = (t15_37 << 25 as libc::c_uint
            | t15_37 >> 7 as libc::c_uint)
            ^ ((t15_37 << 14 as libc::c_uint | t15_37 >> 18 as libc::c_uint)
                ^ t15_37 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_37
            .wrapping_add(t7_37)
            .wrapping_add(s0_37)
            .wrapping_add(t16_37);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_38: uint32_t = ws[i_4 as usize];
        let mut t15_38: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_38: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_86: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_38: uint32_t = (t2_86 << 15 as libc::c_uint
            | t2_86 >> 17 as libc::c_uint)
            ^ ((t2_86 << 13 as libc::c_uint | t2_86 >> 19 as libc::c_uint)
                ^ t2_86 >> 10 as libc::c_uint);
        let mut s0_38: uint32_t = (t15_38 << 25 as libc::c_uint
            | t15_38 >> 7 as libc::c_uint)
            ^ ((t15_38 << 14 as libc::c_uint | t15_38 >> 18 as libc::c_uint)
                ^ t15_38 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_38
            .wrapping_add(t7_38)
            .wrapping_add(s0_38)
            .wrapping_add(t16_38);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_39: uint32_t = ws[i_4 as usize];
        let mut t15_39: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_39: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_87: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_39: uint32_t = (t2_87 << 15 as libc::c_uint
            | t2_87 >> 17 as libc::c_uint)
            ^ ((t2_87 << 13 as libc::c_uint | t2_87 >> 19 as libc::c_uint)
                ^ t2_87 >> 10 as libc::c_uint);
        let mut s0_39: uint32_t = (t15_39 << 25 as libc::c_uint
            | t15_39 >> 7 as libc::c_uint)
            ^ ((t15_39 << 14 as libc::c_uint | t15_39 >> 18 as libc::c_uint)
                ^ t15_39 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_39
            .wrapping_add(t7_39)
            .wrapping_add(s0_39)
            .wrapping_add(t16_39);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_40: uint32_t = ws[i_4 as usize];
        let mut t15_40: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_40: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_88: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_40: uint32_t = (t2_88 << 15 as libc::c_uint
            | t2_88 >> 17 as libc::c_uint)
            ^ ((t2_88 << 13 as libc::c_uint | t2_88 >> 19 as libc::c_uint)
                ^ t2_88 >> 10 as libc::c_uint);
        let mut s0_40: uint32_t = (t15_40 << 25 as libc::c_uint
            | t15_40 >> 7 as libc::c_uint)
            ^ ((t15_40 << 14 as libc::c_uint | t15_40 >> 18 as libc::c_uint)
                ^ t15_40 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_40
            .wrapping_add(t7_40)
            .wrapping_add(s0_40)
            .wrapping_add(t16_40);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_41: uint32_t = ws[i_4 as usize];
        let mut t15_41: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_41: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_89: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_41: uint32_t = (t2_89 << 15 as libc::c_uint
            | t2_89 >> 17 as libc::c_uint)
            ^ ((t2_89 << 13 as libc::c_uint | t2_89 >> 19 as libc::c_uint)
                ^ t2_89 >> 10 as libc::c_uint);
        let mut s0_41: uint32_t = (t15_41 << 25 as libc::c_uint
            | t15_41 >> 7 as libc::c_uint)
            ^ ((t15_41 << 14 as libc::c_uint | t15_41 >> 18 as libc::c_uint)
                ^ t15_41 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_41
            .wrapping_add(t7_41)
            .wrapping_add(s0_41)
            .wrapping_add(t16_41);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_42: uint32_t = ws[i_4 as usize];
        let mut t15_42: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_42: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_90: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_42: uint32_t = (t2_90 << 15 as libc::c_uint
            | t2_90 >> 17 as libc::c_uint)
            ^ ((t2_90 << 13 as libc::c_uint | t2_90 >> 19 as libc::c_uint)
                ^ t2_90 >> 10 as libc::c_uint);
        let mut s0_42: uint32_t = (t15_42 << 25 as libc::c_uint
            | t15_42 >> 7 as libc::c_uint)
            ^ ((t15_42 << 14 as libc::c_uint | t15_42 >> 18 as libc::c_uint)
                ^ t15_42 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_42
            .wrapping_add(t7_42)
            .wrapping_add(s0_42)
            .wrapping_add(t16_42);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_43: uint32_t = ws[i_4 as usize];
        let mut t15_43: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_43: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_91: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_43: uint32_t = (t2_91 << 15 as libc::c_uint
            | t2_91 >> 17 as libc::c_uint)
            ^ ((t2_91 << 13 as libc::c_uint | t2_91 >> 19 as libc::c_uint)
                ^ t2_91 >> 10 as libc::c_uint);
        let mut s0_43: uint32_t = (t15_43 << 25 as libc::c_uint
            | t15_43 >> 7 as libc::c_uint)
            ^ ((t15_43 << 14 as libc::c_uint | t15_43 >> 18 as libc::c_uint)
                ^ t15_43 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_43
            .wrapping_add(t7_43)
            .wrapping_add(s0_43)
            .wrapping_add(t16_43);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_44: uint32_t = ws[i_4 as usize];
        let mut t15_44: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_44: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_92: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_44: uint32_t = (t2_92 << 15 as libc::c_uint
            | t2_92 >> 17 as libc::c_uint)
            ^ ((t2_92 << 13 as libc::c_uint | t2_92 >> 19 as libc::c_uint)
                ^ t2_92 >> 10 as libc::c_uint);
        let mut s0_44: uint32_t = (t15_44 << 25 as libc::c_uint
            | t15_44 >> 7 as libc::c_uint)
            ^ ((t15_44 << 14 as libc::c_uint | t15_44 >> 18 as libc::c_uint)
                ^ t15_44 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_44
            .wrapping_add(t7_44)
            .wrapping_add(s0_44)
            .wrapping_add(t16_44);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_45: uint32_t = ws[i_4 as usize];
        let mut t15_45: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_45: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_93: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_45: uint32_t = (t2_93 << 15 as libc::c_uint
            | t2_93 >> 17 as libc::c_uint)
            ^ ((t2_93 << 13 as libc::c_uint | t2_93 >> 19 as libc::c_uint)
                ^ t2_93 >> 10 as libc::c_uint);
        let mut s0_45: uint32_t = (t15_45 << 25 as libc::c_uint
            | t15_45 >> 7 as libc::c_uint)
            ^ ((t15_45 << 14 as libc::c_uint | t15_45 >> 18 as libc::c_uint)
                ^ t15_45 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_45
            .wrapping_add(t7_45)
            .wrapping_add(s0_45)
            .wrapping_add(t16_45);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_46: uint32_t = ws[i_4 as usize];
        let mut t15_46: uint32_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_46: uint32_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_94: uint32_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_46: uint32_t = (t2_94 << 15 as libc::c_uint
            | t2_94 >> 17 as libc::c_uint)
            ^ ((t2_94 << 13 as libc::c_uint | t2_94 >> 19 as libc::c_uint)
                ^ t2_94 >> 10 as libc::c_uint);
        let mut s0_46: uint32_t = (t15_46 << 25 as libc::c_uint
            | t15_46 >> 7 as libc::c_uint)
            ^ ((t15_46 << 14 as libc::c_uint | t15_46 >> 18 as libc::c_uint)
                ^ t15_46 >> 3 as libc::c_uint);
        ws[i_4
            as usize] = s1_46
            .wrapping_add(t7_46)
            .wrapping_add(s0_46)
            .wrapping_add(t16_46);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    let mut k_t_47: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_47: uint32_t = ws[i_5 as usize];
    let mut a0_47: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_47: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_47: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_47: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_47: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_47: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_47: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_47: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_47: uint32_t = k_t_47;
    let mut t1_47: uint32_t = h02_47
        .wrapping_add(
            (e0_47 << 26 as libc::c_uint | e0_47 >> 6 as libc::c_uint)
                ^ ((e0_47 << 21 as libc::c_uint | e0_47 >> 11 as libc::c_uint)
                    ^ (e0_47 << 7 as libc::c_uint | e0_47 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_47 & f0_47 ^ !e0_47 & g0_47)
        .wrapping_add(k_e_t_47)
        .wrapping_add(ws_t_47);
    let mut t2_95: uint32_t = ((a0_47 << 30 as libc::c_uint | a0_47 >> 2 as libc::c_uint)
        ^ ((a0_47 << 19 as libc::c_uint | a0_47 >> 13 as libc::c_uint)
            ^ (a0_47 << 10 as libc::c_uint | a0_47 >> 22 as libc::c_uint)))
        .wrapping_add(a0_47 & b0_47 ^ (a0_47 & c0_47 ^ b0_47 & c0_47));
    let mut a1_47: uint32_t = t1_47.wrapping_add(t2_95);
    let mut b1_47: uint32_t = a0_47;
    let mut c1_47: uint32_t = b0_47;
    let mut d1_47: uint32_t = c0_47;
    let mut e1_47: uint32_t = d0_47.wrapping_add(t1_47);
    let mut f1_47: uint32_t = e0_47;
    let mut g1_47: uint32_t = f0_47;
    let mut h12_47: uint32_t = g0_47;
    *hash.offset(0 as libc::c_uint as isize) = a1_47;
    *hash.offset(1 as libc::c_uint as isize) = b1_47;
    *hash.offset(2 as libc::c_uint as isize) = c1_47;
    *hash.offset(3 as libc::c_uint as isize) = d1_47;
    *hash.offset(4 as libc::c_uint as isize) = e1_47;
    *hash.offset(5 as libc::c_uint as isize) = f1_47;
    *hash.offset(6 as libc::c_uint as isize) = g1_47;
    *hash.offset(7 as libc::c_uint as isize) = h12_47;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_48: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_48: uint32_t = ws[i_5 as usize];
    let mut a0_48: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_48: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_48: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_48: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_48: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_48: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_48: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_48: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_48: uint32_t = k_t_48;
    let mut t1_48: uint32_t = h02_48
        .wrapping_add(
            (e0_48 << 26 as libc::c_uint | e0_48 >> 6 as libc::c_uint)
                ^ ((e0_48 << 21 as libc::c_uint | e0_48 >> 11 as libc::c_uint)
                    ^ (e0_48 << 7 as libc::c_uint | e0_48 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_48 & f0_48 ^ !e0_48 & g0_48)
        .wrapping_add(k_e_t_48)
        .wrapping_add(ws_t_48);
    let mut t2_96: uint32_t = ((a0_48 << 30 as libc::c_uint | a0_48 >> 2 as libc::c_uint)
        ^ ((a0_48 << 19 as libc::c_uint | a0_48 >> 13 as libc::c_uint)
            ^ (a0_48 << 10 as libc::c_uint | a0_48 >> 22 as libc::c_uint)))
        .wrapping_add(a0_48 & b0_48 ^ (a0_48 & c0_48 ^ b0_48 & c0_48));
    let mut a1_48: uint32_t = t1_48.wrapping_add(t2_96);
    let mut b1_48: uint32_t = a0_48;
    let mut c1_48: uint32_t = b0_48;
    let mut d1_48: uint32_t = c0_48;
    let mut e1_48: uint32_t = d0_48.wrapping_add(t1_48);
    let mut f1_48: uint32_t = e0_48;
    let mut g1_48: uint32_t = f0_48;
    let mut h12_48: uint32_t = g0_48;
    *hash.offset(0 as libc::c_uint as isize) = a1_48;
    *hash.offset(1 as libc::c_uint as isize) = b1_48;
    *hash.offset(2 as libc::c_uint as isize) = c1_48;
    *hash.offset(3 as libc::c_uint as isize) = d1_48;
    *hash.offset(4 as libc::c_uint as isize) = e1_48;
    *hash.offset(5 as libc::c_uint as isize) = f1_48;
    *hash.offset(6 as libc::c_uint as isize) = g1_48;
    *hash.offset(7 as libc::c_uint as isize) = h12_48;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_49: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_49: uint32_t = ws[i_5 as usize];
    let mut a0_49: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_49: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_49: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_49: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_49: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_49: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_49: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_49: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_49: uint32_t = k_t_49;
    let mut t1_49: uint32_t = h02_49
        .wrapping_add(
            (e0_49 << 26 as libc::c_uint | e0_49 >> 6 as libc::c_uint)
                ^ ((e0_49 << 21 as libc::c_uint | e0_49 >> 11 as libc::c_uint)
                    ^ (e0_49 << 7 as libc::c_uint | e0_49 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_49 & f0_49 ^ !e0_49 & g0_49)
        .wrapping_add(k_e_t_49)
        .wrapping_add(ws_t_49);
    let mut t2_97: uint32_t = ((a0_49 << 30 as libc::c_uint | a0_49 >> 2 as libc::c_uint)
        ^ ((a0_49 << 19 as libc::c_uint | a0_49 >> 13 as libc::c_uint)
            ^ (a0_49 << 10 as libc::c_uint | a0_49 >> 22 as libc::c_uint)))
        .wrapping_add(a0_49 & b0_49 ^ (a0_49 & c0_49 ^ b0_49 & c0_49));
    let mut a1_49: uint32_t = t1_49.wrapping_add(t2_97);
    let mut b1_49: uint32_t = a0_49;
    let mut c1_49: uint32_t = b0_49;
    let mut d1_49: uint32_t = c0_49;
    let mut e1_49: uint32_t = d0_49.wrapping_add(t1_49);
    let mut f1_49: uint32_t = e0_49;
    let mut g1_49: uint32_t = f0_49;
    let mut h12_49: uint32_t = g0_49;
    *hash.offset(0 as libc::c_uint as isize) = a1_49;
    *hash.offset(1 as libc::c_uint as isize) = b1_49;
    *hash.offset(2 as libc::c_uint as isize) = c1_49;
    *hash.offset(3 as libc::c_uint as isize) = d1_49;
    *hash.offset(4 as libc::c_uint as isize) = e1_49;
    *hash.offset(5 as libc::c_uint as isize) = f1_49;
    *hash.offset(6 as libc::c_uint as isize) = g1_49;
    *hash.offset(7 as libc::c_uint as isize) = h12_49;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_50: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_50: uint32_t = ws[i_5 as usize];
    let mut a0_50: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_50: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_50: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_50: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_50: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_50: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_50: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_50: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_50: uint32_t = k_t_50;
    let mut t1_50: uint32_t = h02_50
        .wrapping_add(
            (e0_50 << 26 as libc::c_uint | e0_50 >> 6 as libc::c_uint)
                ^ ((e0_50 << 21 as libc::c_uint | e0_50 >> 11 as libc::c_uint)
                    ^ (e0_50 << 7 as libc::c_uint | e0_50 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_50 & f0_50 ^ !e0_50 & g0_50)
        .wrapping_add(k_e_t_50)
        .wrapping_add(ws_t_50);
    let mut t2_98: uint32_t = ((a0_50 << 30 as libc::c_uint | a0_50 >> 2 as libc::c_uint)
        ^ ((a0_50 << 19 as libc::c_uint | a0_50 >> 13 as libc::c_uint)
            ^ (a0_50 << 10 as libc::c_uint | a0_50 >> 22 as libc::c_uint)))
        .wrapping_add(a0_50 & b0_50 ^ (a0_50 & c0_50 ^ b0_50 & c0_50));
    let mut a1_50: uint32_t = t1_50.wrapping_add(t2_98);
    let mut b1_50: uint32_t = a0_50;
    let mut c1_50: uint32_t = b0_50;
    let mut d1_50: uint32_t = c0_50;
    let mut e1_50: uint32_t = d0_50.wrapping_add(t1_50);
    let mut f1_50: uint32_t = e0_50;
    let mut g1_50: uint32_t = f0_50;
    let mut h12_50: uint32_t = g0_50;
    *hash.offset(0 as libc::c_uint as isize) = a1_50;
    *hash.offset(1 as libc::c_uint as isize) = b1_50;
    *hash.offset(2 as libc::c_uint as isize) = c1_50;
    *hash.offset(3 as libc::c_uint as isize) = d1_50;
    *hash.offset(4 as libc::c_uint as isize) = e1_50;
    *hash.offset(5 as libc::c_uint as isize) = f1_50;
    *hash.offset(6 as libc::c_uint as isize) = g1_50;
    *hash.offset(7 as libc::c_uint as isize) = h12_50;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_51: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_51: uint32_t = ws[i_5 as usize];
    let mut a0_51: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_51: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_51: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_51: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_51: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_51: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_51: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_51: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_51: uint32_t = k_t_51;
    let mut t1_51: uint32_t = h02_51
        .wrapping_add(
            (e0_51 << 26 as libc::c_uint | e0_51 >> 6 as libc::c_uint)
                ^ ((e0_51 << 21 as libc::c_uint | e0_51 >> 11 as libc::c_uint)
                    ^ (e0_51 << 7 as libc::c_uint | e0_51 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_51 & f0_51 ^ !e0_51 & g0_51)
        .wrapping_add(k_e_t_51)
        .wrapping_add(ws_t_51);
    let mut t2_99: uint32_t = ((a0_51 << 30 as libc::c_uint | a0_51 >> 2 as libc::c_uint)
        ^ ((a0_51 << 19 as libc::c_uint | a0_51 >> 13 as libc::c_uint)
            ^ (a0_51 << 10 as libc::c_uint | a0_51 >> 22 as libc::c_uint)))
        .wrapping_add(a0_51 & b0_51 ^ (a0_51 & c0_51 ^ b0_51 & c0_51));
    let mut a1_51: uint32_t = t1_51.wrapping_add(t2_99);
    let mut b1_51: uint32_t = a0_51;
    let mut c1_51: uint32_t = b0_51;
    let mut d1_51: uint32_t = c0_51;
    let mut e1_51: uint32_t = d0_51.wrapping_add(t1_51);
    let mut f1_51: uint32_t = e0_51;
    let mut g1_51: uint32_t = f0_51;
    let mut h12_51: uint32_t = g0_51;
    *hash.offset(0 as libc::c_uint as isize) = a1_51;
    *hash.offset(1 as libc::c_uint as isize) = b1_51;
    *hash.offset(2 as libc::c_uint as isize) = c1_51;
    *hash.offset(3 as libc::c_uint as isize) = d1_51;
    *hash.offset(4 as libc::c_uint as isize) = e1_51;
    *hash.offset(5 as libc::c_uint as isize) = f1_51;
    *hash.offset(6 as libc::c_uint as isize) = g1_51;
    *hash.offset(7 as libc::c_uint as isize) = h12_51;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_52: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_52: uint32_t = ws[i_5 as usize];
    let mut a0_52: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_52: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_52: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_52: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_52: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_52: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_52: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_52: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_52: uint32_t = k_t_52;
    let mut t1_52: uint32_t = h02_52
        .wrapping_add(
            (e0_52 << 26 as libc::c_uint | e0_52 >> 6 as libc::c_uint)
                ^ ((e0_52 << 21 as libc::c_uint | e0_52 >> 11 as libc::c_uint)
                    ^ (e0_52 << 7 as libc::c_uint | e0_52 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_52 & f0_52 ^ !e0_52 & g0_52)
        .wrapping_add(k_e_t_52)
        .wrapping_add(ws_t_52);
    let mut t2_100: uint32_t = ((a0_52 << 30 as libc::c_uint
        | a0_52 >> 2 as libc::c_uint)
        ^ ((a0_52 << 19 as libc::c_uint | a0_52 >> 13 as libc::c_uint)
            ^ (a0_52 << 10 as libc::c_uint | a0_52 >> 22 as libc::c_uint)))
        .wrapping_add(a0_52 & b0_52 ^ (a0_52 & c0_52 ^ b0_52 & c0_52));
    let mut a1_52: uint32_t = t1_52.wrapping_add(t2_100);
    let mut b1_52: uint32_t = a0_52;
    let mut c1_52: uint32_t = b0_52;
    let mut d1_52: uint32_t = c0_52;
    let mut e1_52: uint32_t = d0_52.wrapping_add(t1_52);
    let mut f1_52: uint32_t = e0_52;
    let mut g1_52: uint32_t = f0_52;
    let mut h12_52: uint32_t = g0_52;
    *hash.offset(0 as libc::c_uint as isize) = a1_52;
    *hash.offset(1 as libc::c_uint as isize) = b1_52;
    *hash.offset(2 as libc::c_uint as isize) = c1_52;
    *hash.offset(3 as libc::c_uint as isize) = d1_52;
    *hash.offset(4 as libc::c_uint as isize) = e1_52;
    *hash.offset(5 as libc::c_uint as isize) = f1_52;
    *hash.offset(6 as libc::c_uint as isize) = g1_52;
    *hash.offset(7 as libc::c_uint as isize) = h12_52;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_53: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_53: uint32_t = ws[i_5 as usize];
    let mut a0_53: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_53: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_53: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_53: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_53: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_53: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_53: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_53: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_53: uint32_t = k_t_53;
    let mut t1_53: uint32_t = h02_53
        .wrapping_add(
            (e0_53 << 26 as libc::c_uint | e0_53 >> 6 as libc::c_uint)
                ^ ((e0_53 << 21 as libc::c_uint | e0_53 >> 11 as libc::c_uint)
                    ^ (e0_53 << 7 as libc::c_uint | e0_53 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_53 & f0_53 ^ !e0_53 & g0_53)
        .wrapping_add(k_e_t_53)
        .wrapping_add(ws_t_53);
    let mut t2_101: uint32_t = ((a0_53 << 30 as libc::c_uint
        | a0_53 >> 2 as libc::c_uint)
        ^ ((a0_53 << 19 as libc::c_uint | a0_53 >> 13 as libc::c_uint)
            ^ (a0_53 << 10 as libc::c_uint | a0_53 >> 22 as libc::c_uint)))
        .wrapping_add(a0_53 & b0_53 ^ (a0_53 & c0_53 ^ b0_53 & c0_53));
    let mut a1_53: uint32_t = t1_53.wrapping_add(t2_101);
    let mut b1_53: uint32_t = a0_53;
    let mut c1_53: uint32_t = b0_53;
    let mut d1_53: uint32_t = c0_53;
    let mut e1_53: uint32_t = d0_53.wrapping_add(t1_53);
    let mut f1_53: uint32_t = e0_53;
    let mut g1_53: uint32_t = f0_53;
    let mut h12_53: uint32_t = g0_53;
    *hash.offset(0 as libc::c_uint as isize) = a1_53;
    *hash.offset(1 as libc::c_uint as isize) = b1_53;
    *hash.offset(2 as libc::c_uint as isize) = c1_53;
    *hash.offset(3 as libc::c_uint as isize) = d1_53;
    *hash.offset(4 as libc::c_uint as isize) = e1_53;
    *hash.offset(5 as libc::c_uint as isize) = f1_53;
    *hash.offset(6 as libc::c_uint as isize) = g1_53;
    *hash.offset(7 as libc::c_uint as isize) = h12_53;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_54: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_54: uint32_t = ws[i_5 as usize];
    let mut a0_54: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_54: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_54: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_54: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_54: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_54: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_54: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_54: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_54: uint32_t = k_t_54;
    let mut t1_54: uint32_t = h02_54
        .wrapping_add(
            (e0_54 << 26 as libc::c_uint | e0_54 >> 6 as libc::c_uint)
                ^ ((e0_54 << 21 as libc::c_uint | e0_54 >> 11 as libc::c_uint)
                    ^ (e0_54 << 7 as libc::c_uint | e0_54 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_54 & f0_54 ^ !e0_54 & g0_54)
        .wrapping_add(k_e_t_54)
        .wrapping_add(ws_t_54);
    let mut t2_102: uint32_t = ((a0_54 << 30 as libc::c_uint
        | a0_54 >> 2 as libc::c_uint)
        ^ ((a0_54 << 19 as libc::c_uint | a0_54 >> 13 as libc::c_uint)
            ^ (a0_54 << 10 as libc::c_uint | a0_54 >> 22 as libc::c_uint)))
        .wrapping_add(a0_54 & b0_54 ^ (a0_54 & c0_54 ^ b0_54 & c0_54));
    let mut a1_54: uint32_t = t1_54.wrapping_add(t2_102);
    let mut b1_54: uint32_t = a0_54;
    let mut c1_54: uint32_t = b0_54;
    let mut d1_54: uint32_t = c0_54;
    let mut e1_54: uint32_t = d0_54.wrapping_add(t1_54);
    let mut f1_54: uint32_t = e0_54;
    let mut g1_54: uint32_t = f0_54;
    let mut h12_54: uint32_t = g0_54;
    *hash.offset(0 as libc::c_uint as isize) = a1_54;
    *hash.offset(1 as libc::c_uint as isize) = b1_54;
    *hash.offset(2 as libc::c_uint as isize) = c1_54;
    *hash.offset(3 as libc::c_uint as isize) = d1_54;
    *hash.offset(4 as libc::c_uint as isize) = e1_54;
    *hash.offset(5 as libc::c_uint as isize) = f1_54;
    *hash.offset(6 as libc::c_uint as isize) = g1_54;
    *hash.offset(7 as libc::c_uint as isize) = h12_54;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_55: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_55: uint32_t = ws[i_5 as usize];
    let mut a0_55: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_55: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_55: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_55: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_55: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_55: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_55: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_55: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_55: uint32_t = k_t_55;
    let mut t1_55: uint32_t = h02_55
        .wrapping_add(
            (e0_55 << 26 as libc::c_uint | e0_55 >> 6 as libc::c_uint)
                ^ ((e0_55 << 21 as libc::c_uint | e0_55 >> 11 as libc::c_uint)
                    ^ (e0_55 << 7 as libc::c_uint | e0_55 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_55 & f0_55 ^ !e0_55 & g0_55)
        .wrapping_add(k_e_t_55)
        .wrapping_add(ws_t_55);
    let mut t2_103: uint32_t = ((a0_55 << 30 as libc::c_uint
        | a0_55 >> 2 as libc::c_uint)
        ^ ((a0_55 << 19 as libc::c_uint | a0_55 >> 13 as libc::c_uint)
            ^ (a0_55 << 10 as libc::c_uint | a0_55 >> 22 as libc::c_uint)))
        .wrapping_add(a0_55 & b0_55 ^ (a0_55 & c0_55 ^ b0_55 & c0_55));
    let mut a1_55: uint32_t = t1_55.wrapping_add(t2_103);
    let mut b1_55: uint32_t = a0_55;
    let mut c1_55: uint32_t = b0_55;
    let mut d1_55: uint32_t = c0_55;
    let mut e1_55: uint32_t = d0_55.wrapping_add(t1_55);
    let mut f1_55: uint32_t = e0_55;
    let mut g1_55: uint32_t = f0_55;
    let mut h12_55: uint32_t = g0_55;
    *hash.offset(0 as libc::c_uint as isize) = a1_55;
    *hash.offset(1 as libc::c_uint as isize) = b1_55;
    *hash.offset(2 as libc::c_uint as isize) = c1_55;
    *hash.offset(3 as libc::c_uint as isize) = d1_55;
    *hash.offset(4 as libc::c_uint as isize) = e1_55;
    *hash.offset(5 as libc::c_uint as isize) = f1_55;
    *hash.offset(6 as libc::c_uint as isize) = g1_55;
    *hash.offset(7 as libc::c_uint as isize) = h12_55;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_56: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_56: uint32_t = ws[i_5 as usize];
    let mut a0_56: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_56: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_56: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_56: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_56: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_56: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_56: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_56: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_56: uint32_t = k_t_56;
    let mut t1_56: uint32_t = h02_56
        .wrapping_add(
            (e0_56 << 26 as libc::c_uint | e0_56 >> 6 as libc::c_uint)
                ^ ((e0_56 << 21 as libc::c_uint | e0_56 >> 11 as libc::c_uint)
                    ^ (e0_56 << 7 as libc::c_uint | e0_56 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_56 & f0_56 ^ !e0_56 & g0_56)
        .wrapping_add(k_e_t_56)
        .wrapping_add(ws_t_56);
    let mut t2_104: uint32_t = ((a0_56 << 30 as libc::c_uint
        | a0_56 >> 2 as libc::c_uint)
        ^ ((a0_56 << 19 as libc::c_uint | a0_56 >> 13 as libc::c_uint)
            ^ (a0_56 << 10 as libc::c_uint | a0_56 >> 22 as libc::c_uint)))
        .wrapping_add(a0_56 & b0_56 ^ (a0_56 & c0_56 ^ b0_56 & c0_56));
    let mut a1_56: uint32_t = t1_56.wrapping_add(t2_104);
    let mut b1_56: uint32_t = a0_56;
    let mut c1_56: uint32_t = b0_56;
    let mut d1_56: uint32_t = c0_56;
    let mut e1_56: uint32_t = d0_56.wrapping_add(t1_56);
    let mut f1_56: uint32_t = e0_56;
    let mut g1_56: uint32_t = f0_56;
    let mut h12_56: uint32_t = g0_56;
    *hash.offset(0 as libc::c_uint as isize) = a1_56;
    *hash.offset(1 as libc::c_uint as isize) = b1_56;
    *hash.offset(2 as libc::c_uint as isize) = c1_56;
    *hash.offset(3 as libc::c_uint as isize) = d1_56;
    *hash.offset(4 as libc::c_uint as isize) = e1_56;
    *hash.offset(5 as libc::c_uint as isize) = f1_56;
    *hash.offset(6 as libc::c_uint as isize) = g1_56;
    *hash.offset(7 as libc::c_uint as isize) = h12_56;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_57: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_57: uint32_t = ws[i_5 as usize];
    let mut a0_57: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_57: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_57: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_57: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_57: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_57: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_57: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_57: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_57: uint32_t = k_t_57;
    let mut t1_57: uint32_t = h02_57
        .wrapping_add(
            (e0_57 << 26 as libc::c_uint | e0_57 >> 6 as libc::c_uint)
                ^ ((e0_57 << 21 as libc::c_uint | e0_57 >> 11 as libc::c_uint)
                    ^ (e0_57 << 7 as libc::c_uint | e0_57 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_57 & f0_57 ^ !e0_57 & g0_57)
        .wrapping_add(k_e_t_57)
        .wrapping_add(ws_t_57);
    let mut t2_105: uint32_t = ((a0_57 << 30 as libc::c_uint
        | a0_57 >> 2 as libc::c_uint)
        ^ ((a0_57 << 19 as libc::c_uint | a0_57 >> 13 as libc::c_uint)
            ^ (a0_57 << 10 as libc::c_uint | a0_57 >> 22 as libc::c_uint)))
        .wrapping_add(a0_57 & b0_57 ^ (a0_57 & c0_57 ^ b0_57 & c0_57));
    let mut a1_57: uint32_t = t1_57.wrapping_add(t2_105);
    let mut b1_57: uint32_t = a0_57;
    let mut c1_57: uint32_t = b0_57;
    let mut d1_57: uint32_t = c0_57;
    let mut e1_57: uint32_t = d0_57.wrapping_add(t1_57);
    let mut f1_57: uint32_t = e0_57;
    let mut g1_57: uint32_t = f0_57;
    let mut h12_57: uint32_t = g0_57;
    *hash.offset(0 as libc::c_uint as isize) = a1_57;
    *hash.offset(1 as libc::c_uint as isize) = b1_57;
    *hash.offset(2 as libc::c_uint as isize) = c1_57;
    *hash.offset(3 as libc::c_uint as isize) = d1_57;
    *hash.offset(4 as libc::c_uint as isize) = e1_57;
    *hash.offset(5 as libc::c_uint as isize) = f1_57;
    *hash.offset(6 as libc::c_uint as isize) = g1_57;
    *hash.offset(7 as libc::c_uint as isize) = h12_57;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_58: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_58: uint32_t = ws[i_5 as usize];
    let mut a0_58: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_58: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_58: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_58: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_58: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_58: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_58: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_58: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_58: uint32_t = k_t_58;
    let mut t1_58: uint32_t = h02_58
        .wrapping_add(
            (e0_58 << 26 as libc::c_uint | e0_58 >> 6 as libc::c_uint)
                ^ ((e0_58 << 21 as libc::c_uint | e0_58 >> 11 as libc::c_uint)
                    ^ (e0_58 << 7 as libc::c_uint | e0_58 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_58 & f0_58 ^ !e0_58 & g0_58)
        .wrapping_add(k_e_t_58)
        .wrapping_add(ws_t_58);
    let mut t2_106: uint32_t = ((a0_58 << 30 as libc::c_uint
        | a0_58 >> 2 as libc::c_uint)
        ^ ((a0_58 << 19 as libc::c_uint | a0_58 >> 13 as libc::c_uint)
            ^ (a0_58 << 10 as libc::c_uint | a0_58 >> 22 as libc::c_uint)))
        .wrapping_add(a0_58 & b0_58 ^ (a0_58 & c0_58 ^ b0_58 & c0_58));
    let mut a1_58: uint32_t = t1_58.wrapping_add(t2_106);
    let mut b1_58: uint32_t = a0_58;
    let mut c1_58: uint32_t = b0_58;
    let mut d1_58: uint32_t = c0_58;
    let mut e1_58: uint32_t = d0_58.wrapping_add(t1_58);
    let mut f1_58: uint32_t = e0_58;
    let mut g1_58: uint32_t = f0_58;
    let mut h12_58: uint32_t = g0_58;
    *hash.offset(0 as libc::c_uint as isize) = a1_58;
    *hash.offset(1 as libc::c_uint as isize) = b1_58;
    *hash.offset(2 as libc::c_uint as isize) = c1_58;
    *hash.offset(3 as libc::c_uint as isize) = d1_58;
    *hash.offset(4 as libc::c_uint as isize) = e1_58;
    *hash.offset(5 as libc::c_uint as isize) = f1_58;
    *hash.offset(6 as libc::c_uint as isize) = g1_58;
    *hash.offset(7 as libc::c_uint as isize) = h12_58;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_59: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_59: uint32_t = ws[i_5 as usize];
    let mut a0_59: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_59: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_59: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_59: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_59: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_59: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_59: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_59: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_59: uint32_t = k_t_59;
    let mut t1_59: uint32_t = h02_59
        .wrapping_add(
            (e0_59 << 26 as libc::c_uint | e0_59 >> 6 as libc::c_uint)
                ^ ((e0_59 << 21 as libc::c_uint | e0_59 >> 11 as libc::c_uint)
                    ^ (e0_59 << 7 as libc::c_uint | e0_59 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_59 & f0_59 ^ !e0_59 & g0_59)
        .wrapping_add(k_e_t_59)
        .wrapping_add(ws_t_59);
    let mut t2_107: uint32_t = ((a0_59 << 30 as libc::c_uint
        | a0_59 >> 2 as libc::c_uint)
        ^ ((a0_59 << 19 as libc::c_uint | a0_59 >> 13 as libc::c_uint)
            ^ (a0_59 << 10 as libc::c_uint | a0_59 >> 22 as libc::c_uint)))
        .wrapping_add(a0_59 & b0_59 ^ (a0_59 & c0_59 ^ b0_59 & c0_59));
    let mut a1_59: uint32_t = t1_59.wrapping_add(t2_107);
    let mut b1_59: uint32_t = a0_59;
    let mut c1_59: uint32_t = b0_59;
    let mut d1_59: uint32_t = c0_59;
    let mut e1_59: uint32_t = d0_59.wrapping_add(t1_59);
    let mut f1_59: uint32_t = e0_59;
    let mut g1_59: uint32_t = f0_59;
    let mut h12_59: uint32_t = g0_59;
    *hash.offset(0 as libc::c_uint as isize) = a1_59;
    *hash.offset(1 as libc::c_uint as isize) = b1_59;
    *hash.offset(2 as libc::c_uint as isize) = c1_59;
    *hash.offset(3 as libc::c_uint as isize) = d1_59;
    *hash.offset(4 as libc::c_uint as isize) = e1_59;
    *hash.offset(5 as libc::c_uint as isize) = f1_59;
    *hash.offset(6 as libc::c_uint as isize) = g1_59;
    *hash.offset(7 as libc::c_uint as isize) = h12_59;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_60: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_60: uint32_t = ws[i_5 as usize];
    let mut a0_60: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_60: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_60: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_60: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_60: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_60: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_60: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_60: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_60: uint32_t = k_t_60;
    let mut t1_60: uint32_t = h02_60
        .wrapping_add(
            (e0_60 << 26 as libc::c_uint | e0_60 >> 6 as libc::c_uint)
                ^ ((e0_60 << 21 as libc::c_uint | e0_60 >> 11 as libc::c_uint)
                    ^ (e0_60 << 7 as libc::c_uint | e0_60 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_60 & f0_60 ^ !e0_60 & g0_60)
        .wrapping_add(k_e_t_60)
        .wrapping_add(ws_t_60);
    let mut t2_108: uint32_t = ((a0_60 << 30 as libc::c_uint
        | a0_60 >> 2 as libc::c_uint)
        ^ ((a0_60 << 19 as libc::c_uint | a0_60 >> 13 as libc::c_uint)
            ^ (a0_60 << 10 as libc::c_uint | a0_60 >> 22 as libc::c_uint)))
        .wrapping_add(a0_60 & b0_60 ^ (a0_60 & c0_60 ^ b0_60 & c0_60));
    let mut a1_60: uint32_t = t1_60.wrapping_add(t2_108);
    let mut b1_60: uint32_t = a0_60;
    let mut c1_60: uint32_t = b0_60;
    let mut d1_60: uint32_t = c0_60;
    let mut e1_60: uint32_t = d0_60.wrapping_add(t1_60);
    let mut f1_60: uint32_t = e0_60;
    let mut g1_60: uint32_t = f0_60;
    let mut h12_60: uint32_t = g0_60;
    *hash.offset(0 as libc::c_uint as isize) = a1_60;
    *hash.offset(1 as libc::c_uint as isize) = b1_60;
    *hash.offset(2 as libc::c_uint as isize) = c1_60;
    *hash.offset(3 as libc::c_uint as isize) = d1_60;
    *hash.offset(4 as libc::c_uint as isize) = e1_60;
    *hash.offset(5 as libc::c_uint as isize) = f1_60;
    *hash.offset(6 as libc::c_uint as isize) = g1_60;
    *hash.offset(7 as libc::c_uint as isize) = h12_60;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_61: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_61: uint32_t = ws[i_5 as usize];
    let mut a0_61: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_61: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_61: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_61: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_61: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_61: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_61: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_61: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_61: uint32_t = k_t_61;
    let mut t1_61: uint32_t = h02_61
        .wrapping_add(
            (e0_61 << 26 as libc::c_uint | e0_61 >> 6 as libc::c_uint)
                ^ ((e0_61 << 21 as libc::c_uint | e0_61 >> 11 as libc::c_uint)
                    ^ (e0_61 << 7 as libc::c_uint | e0_61 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_61 & f0_61 ^ !e0_61 & g0_61)
        .wrapping_add(k_e_t_61)
        .wrapping_add(ws_t_61);
    let mut t2_109: uint32_t = ((a0_61 << 30 as libc::c_uint
        | a0_61 >> 2 as libc::c_uint)
        ^ ((a0_61 << 19 as libc::c_uint | a0_61 >> 13 as libc::c_uint)
            ^ (a0_61 << 10 as libc::c_uint | a0_61 >> 22 as libc::c_uint)))
        .wrapping_add(a0_61 & b0_61 ^ (a0_61 & c0_61 ^ b0_61 & c0_61));
    let mut a1_61: uint32_t = t1_61.wrapping_add(t2_109);
    let mut b1_61: uint32_t = a0_61;
    let mut c1_61: uint32_t = b0_61;
    let mut d1_61: uint32_t = c0_61;
    let mut e1_61: uint32_t = d0_61.wrapping_add(t1_61);
    let mut f1_61: uint32_t = e0_61;
    let mut g1_61: uint32_t = f0_61;
    let mut h12_61: uint32_t = g0_61;
    *hash.offset(0 as libc::c_uint as isize) = a1_61;
    *hash.offset(1 as libc::c_uint as isize) = b1_61;
    *hash.offset(2 as libc::c_uint as isize) = c1_61;
    *hash.offset(3 as libc::c_uint as isize) = d1_61;
    *hash.offset(4 as libc::c_uint as isize) = e1_61;
    *hash.offset(5 as libc::c_uint as isize) = f1_61;
    *hash.offset(6 as libc::c_uint as isize) = g1_61;
    *hash.offset(7 as libc::c_uint as isize) = h12_61;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_62: uint32_t = Hacl_Hash_SHA2_k224_256[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_62: uint32_t = ws[i_5 as usize];
    let mut a0_62: uint32_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_62: uint32_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_62: uint32_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_62: uint32_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_62: uint32_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_62: uint32_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_62: uint32_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_62: uint32_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_62: uint32_t = k_t_62;
    let mut t1_62: uint32_t = h02_62
        .wrapping_add(
            (e0_62 << 26 as libc::c_uint | e0_62 >> 6 as libc::c_uint)
                ^ ((e0_62 << 21 as libc::c_uint | e0_62 >> 11 as libc::c_uint)
                    ^ (e0_62 << 7 as libc::c_uint | e0_62 >> 25 as libc::c_uint)),
        )
        .wrapping_add(e0_62 & f0_62 ^ !e0_62 & g0_62)
        .wrapping_add(k_e_t_62)
        .wrapping_add(ws_t_62);
    let mut t2_110: uint32_t = ((a0_62 << 30 as libc::c_uint
        | a0_62 >> 2 as libc::c_uint)
        ^ ((a0_62 << 19 as libc::c_uint | a0_62 >> 13 as libc::c_uint)
            ^ (a0_62 << 10 as libc::c_uint | a0_62 >> 22 as libc::c_uint)))
        .wrapping_add(a0_62 & b0_62 ^ (a0_62 & c0_62 ^ b0_62 & c0_62));
    let mut a1_62: uint32_t = t1_62.wrapping_add(t2_110);
    let mut b1_62: uint32_t = a0_62;
    let mut c1_62: uint32_t = b0_62;
    let mut d1_62: uint32_t = c0_62;
    let mut e1_62: uint32_t = d0_62.wrapping_add(t1_62);
    let mut f1_62: uint32_t = e0_62;
    let mut g1_62: uint32_t = f0_62;
    let mut h12_62: uint32_t = g0_62;
    *hash.offset(0 as libc::c_uint as isize) = a1_62;
    *hash.offset(1 as libc::c_uint as isize) = b1_62;
    *hash.offset(2 as libc::c_uint as isize) = c1_62;
    *hash.offset(3 as libc::c_uint as isize) = d1_62;
    *hash.offset(4 as libc::c_uint as isize) = e1_62;
    *hash.offset(5 as libc::c_uint as isize) = f1_62;
    *hash.offset(6 as libc::c_uint as isize) = g1_62;
    *hash.offset(7 as libc::c_uint as isize) = h12_62;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 3 as libc::c_uint {
        let mut i_6: uint32_t = 0 as libc::c_uint;
        let mut t16_47: uint32_t = ws[i_6 as usize];
        let mut t15_47: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_47: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_111: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_47: uint32_t = (t2_111 << 15 as libc::c_uint
            | t2_111 >> 17 as libc::c_uint)
            ^ ((t2_111 << 13 as libc::c_uint | t2_111 >> 19 as libc::c_uint)
                ^ t2_111 >> 10 as libc::c_uint);
        let mut s0_47: uint32_t = (t15_47 << 25 as libc::c_uint
            | t15_47 >> 7 as libc::c_uint)
            ^ ((t15_47 << 14 as libc::c_uint | t15_47 >> 18 as libc::c_uint)
                ^ t15_47 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_47
            .wrapping_add(t7_47)
            .wrapping_add(s0_47)
            .wrapping_add(t16_47);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_48: uint32_t = ws[i_6 as usize];
        let mut t15_48: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_48: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_112: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_48: uint32_t = (t2_112 << 15 as libc::c_uint
            | t2_112 >> 17 as libc::c_uint)
            ^ ((t2_112 << 13 as libc::c_uint | t2_112 >> 19 as libc::c_uint)
                ^ t2_112 >> 10 as libc::c_uint);
        let mut s0_48: uint32_t = (t15_48 << 25 as libc::c_uint
            | t15_48 >> 7 as libc::c_uint)
            ^ ((t15_48 << 14 as libc::c_uint | t15_48 >> 18 as libc::c_uint)
                ^ t15_48 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_48
            .wrapping_add(t7_48)
            .wrapping_add(s0_48)
            .wrapping_add(t16_48);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_49: uint32_t = ws[i_6 as usize];
        let mut t15_49: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_49: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_113: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_49: uint32_t = (t2_113 << 15 as libc::c_uint
            | t2_113 >> 17 as libc::c_uint)
            ^ ((t2_113 << 13 as libc::c_uint | t2_113 >> 19 as libc::c_uint)
                ^ t2_113 >> 10 as libc::c_uint);
        let mut s0_49: uint32_t = (t15_49 << 25 as libc::c_uint
            | t15_49 >> 7 as libc::c_uint)
            ^ ((t15_49 << 14 as libc::c_uint | t15_49 >> 18 as libc::c_uint)
                ^ t15_49 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_49
            .wrapping_add(t7_49)
            .wrapping_add(s0_49)
            .wrapping_add(t16_49);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_50: uint32_t = ws[i_6 as usize];
        let mut t15_50: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_50: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_114: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_50: uint32_t = (t2_114 << 15 as libc::c_uint
            | t2_114 >> 17 as libc::c_uint)
            ^ ((t2_114 << 13 as libc::c_uint | t2_114 >> 19 as libc::c_uint)
                ^ t2_114 >> 10 as libc::c_uint);
        let mut s0_50: uint32_t = (t15_50 << 25 as libc::c_uint
            | t15_50 >> 7 as libc::c_uint)
            ^ ((t15_50 << 14 as libc::c_uint | t15_50 >> 18 as libc::c_uint)
                ^ t15_50 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_50
            .wrapping_add(t7_50)
            .wrapping_add(s0_50)
            .wrapping_add(t16_50);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_51: uint32_t = ws[i_6 as usize];
        let mut t15_51: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_51: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_115: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_51: uint32_t = (t2_115 << 15 as libc::c_uint
            | t2_115 >> 17 as libc::c_uint)
            ^ ((t2_115 << 13 as libc::c_uint | t2_115 >> 19 as libc::c_uint)
                ^ t2_115 >> 10 as libc::c_uint);
        let mut s0_51: uint32_t = (t15_51 << 25 as libc::c_uint
            | t15_51 >> 7 as libc::c_uint)
            ^ ((t15_51 << 14 as libc::c_uint | t15_51 >> 18 as libc::c_uint)
                ^ t15_51 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_51
            .wrapping_add(t7_51)
            .wrapping_add(s0_51)
            .wrapping_add(t16_51);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_52: uint32_t = ws[i_6 as usize];
        let mut t15_52: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_52: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_116: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_52: uint32_t = (t2_116 << 15 as libc::c_uint
            | t2_116 >> 17 as libc::c_uint)
            ^ ((t2_116 << 13 as libc::c_uint | t2_116 >> 19 as libc::c_uint)
                ^ t2_116 >> 10 as libc::c_uint);
        let mut s0_52: uint32_t = (t15_52 << 25 as libc::c_uint
            | t15_52 >> 7 as libc::c_uint)
            ^ ((t15_52 << 14 as libc::c_uint | t15_52 >> 18 as libc::c_uint)
                ^ t15_52 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_52
            .wrapping_add(t7_52)
            .wrapping_add(s0_52)
            .wrapping_add(t16_52);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_53: uint32_t = ws[i_6 as usize];
        let mut t15_53: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_53: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_117: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_53: uint32_t = (t2_117 << 15 as libc::c_uint
            | t2_117 >> 17 as libc::c_uint)
            ^ ((t2_117 << 13 as libc::c_uint | t2_117 >> 19 as libc::c_uint)
                ^ t2_117 >> 10 as libc::c_uint);
        let mut s0_53: uint32_t = (t15_53 << 25 as libc::c_uint
            | t15_53 >> 7 as libc::c_uint)
            ^ ((t15_53 << 14 as libc::c_uint | t15_53 >> 18 as libc::c_uint)
                ^ t15_53 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_53
            .wrapping_add(t7_53)
            .wrapping_add(s0_53)
            .wrapping_add(t16_53);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_54: uint32_t = ws[i_6 as usize];
        let mut t15_54: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_54: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_118: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_54: uint32_t = (t2_118 << 15 as libc::c_uint
            | t2_118 >> 17 as libc::c_uint)
            ^ ((t2_118 << 13 as libc::c_uint | t2_118 >> 19 as libc::c_uint)
                ^ t2_118 >> 10 as libc::c_uint);
        let mut s0_54: uint32_t = (t15_54 << 25 as libc::c_uint
            | t15_54 >> 7 as libc::c_uint)
            ^ ((t15_54 << 14 as libc::c_uint | t15_54 >> 18 as libc::c_uint)
                ^ t15_54 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_54
            .wrapping_add(t7_54)
            .wrapping_add(s0_54)
            .wrapping_add(t16_54);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_55: uint32_t = ws[i_6 as usize];
        let mut t15_55: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_55: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_119: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_55: uint32_t = (t2_119 << 15 as libc::c_uint
            | t2_119 >> 17 as libc::c_uint)
            ^ ((t2_119 << 13 as libc::c_uint | t2_119 >> 19 as libc::c_uint)
                ^ t2_119 >> 10 as libc::c_uint);
        let mut s0_55: uint32_t = (t15_55 << 25 as libc::c_uint
            | t15_55 >> 7 as libc::c_uint)
            ^ ((t15_55 << 14 as libc::c_uint | t15_55 >> 18 as libc::c_uint)
                ^ t15_55 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_55
            .wrapping_add(t7_55)
            .wrapping_add(s0_55)
            .wrapping_add(t16_55);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_56: uint32_t = ws[i_6 as usize];
        let mut t15_56: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_56: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_120: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_56: uint32_t = (t2_120 << 15 as libc::c_uint
            | t2_120 >> 17 as libc::c_uint)
            ^ ((t2_120 << 13 as libc::c_uint | t2_120 >> 19 as libc::c_uint)
                ^ t2_120 >> 10 as libc::c_uint);
        let mut s0_56: uint32_t = (t15_56 << 25 as libc::c_uint
            | t15_56 >> 7 as libc::c_uint)
            ^ ((t15_56 << 14 as libc::c_uint | t15_56 >> 18 as libc::c_uint)
                ^ t15_56 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_56
            .wrapping_add(t7_56)
            .wrapping_add(s0_56)
            .wrapping_add(t16_56);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_57: uint32_t = ws[i_6 as usize];
        let mut t15_57: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_57: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_121: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_57: uint32_t = (t2_121 << 15 as libc::c_uint
            | t2_121 >> 17 as libc::c_uint)
            ^ ((t2_121 << 13 as libc::c_uint | t2_121 >> 19 as libc::c_uint)
                ^ t2_121 >> 10 as libc::c_uint);
        let mut s0_57: uint32_t = (t15_57 << 25 as libc::c_uint
            | t15_57 >> 7 as libc::c_uint)
            ^ ((t15_57 << 14 as libc::c_uint | t15_57 >> 18 as libc::c_uint)
                ^ t15_57 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_57
            .wrapping_add(t7_57)
            .wrapping_add(s0_57)
            .wrapping_add(t16_57);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_58: uint32_t = ws[i_6 as usize];
        let mut t15_58: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_58: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_122: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_58: uint32_t = (t2_122 << 15 as libc::c_uint
            | t2_122 >> 17 as libc::c_uint)
            ^ ((t2_122 << 13 as libc::c_uint | t2_122 >> 19 as libc::c_uint)
                ^ t2_122 >> 10 as libc::c_uint);
        let mut s0_58: uint32_t = (t15_58 << 25 as libc::c_uint
            | t15_58 >> 7 as libc::c_uint)
            ^ ((t15_58 << 14 as libc::c_uint | t15_58 >> 18 as libc::c_uint)
                ^ t15_58 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_58
            .wrapping_add(t7_58)
            .wrapping_add(s0_58)
            .wrapping_add(t16_58);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_59: uint32_t = ws[i_6 as usize];
        let mut t15_59: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_59: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_123: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_59: uint32_t = (t2_123 << 15 as libc::c_uint
            | t2_123 >> 17 as libc::c_uint)
            ^ ((t2_123 << 13 as libc::c_uint | t2_123 >> 19 as libc::c_uint)
                ^ t2_123 >> 10 as libc::c_uint);
        let mut s0_59: uint32_t = (t15_59 << 25 as libc::c_uint
            | t15_59 >> 7 as libc::c_uint)
            ^ ((t15_59 << 14 as libc::c_uint | t15_59 >> 18 as libc::c_uint)
                ^ t15_59 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_59
            .wrapping_add(t7_59)
            .wrapping_add(s0_59)
            .wrapping_add(t16_59);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_60: uint32_t = ws[i_6 as usize];
        let mut t15_60: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_60: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_124: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_60: uint32_t = (t2_124 << 15 as libc::c_uint
            | t2_124 >> 17 as libc::c_uint)
            ^ ((t2_124 << 13 as libc::c_uint | t2_124 >> 19 as libc::c_uint)
                ^ t2_124 >> 10 as libc::c_uint);
        let mut s0_60: uint32_t = (t15_60 << 25 as libc::c_uint
            | t15_60 >> 7 as libc::c_uint)
            ^ ((t15_60 << 14 as libc::c_uint | t15_60 >> 18 as libc::c_uint)
                ^ t15_60 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_60
            .wrapping_add(t7_60)
            .wrapping_add(s0_60)
            .wrapping_add(t16_60);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_61: uint32_t = ws[i_6 as usize];
        let mut t15_61: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_61: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_125: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_61: uint32_t = (t2_125 << 15 as libc::c_uint
            | t2_125 >> 17 as libc::c_uint)
            ^ ((t2_125 << 13 as libc::c_uint | t2_125 >> 19 as libc::c_uint)
                ^ t2_125 >> 10 as libc::c_uint);
        let mut s0_61: uint32_t = (t15_61 << 25 as libc::c_uint
            | t15_61 >> 7 as libc::c_uint)
            ^ ((t15_61 << 14 as libc::c_uint | t15_61 >> 18 as libc::c_uint)
                ^ t15_61 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_61
            .wrapping_add(t7_61)
            .wrapping_add(s0_61)
            .wrapping_add(t16_61);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_62: uint32_t = ws[i_6 as usize];
        let mut t15_62: uint32_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_62: uint32_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_126: uint32_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_62: uint32_t = (t2_126 << 15 as libc::c_uint
            | t2_126 >> 17 as libc::c_uint)
            ^ ((t2_126 << 13 as libc::c_uint | t2_126 >> 19 as libc::c_uint)
                ^ t2_126 >> 10 as libc::c_uint);
        let mut s0_62: uint32_t = (t15_62 << 25 as libc::c_uint
            | t15_62 >> 7 as libc::c_uint)
            ^ ((t15_62 << 14 as libc::c_uint | t15_62 >> 18 as libc::c_uint)
                ^ t15_62 >> 3 as libc::c_uint);
        ws[i_6
            as usize] = s1_62
            .wrapping_add(t7_62)
            .wrapping_add(s0_62)
            .wrapping_add(t16_62);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os: *mut uint32_t = hash;
    *os.offset(i_7 as isize) = x;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_0: *mut uint32_t = hash;
    *os_0.offset(i_7 as isize) = x_0;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_1: *mut uint32_t = hash;
    *os_1.offset(i_7 as isize) = x_1;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_2: *mut uint32_t = hash;
    *os_2.offset(i_7 as isize) = x_2;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_3: *mut uint32_t = hash;
    *os_3.offset(i_7 as isize) = x_3;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_4: *mut uint32_t = hash;
    *os_4.offset(i_7 as isize) = x_4;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_5: *mut uint32_t = hash;
    *os_5.offset(i_7 as isize) = x_5;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = (*hash.offset(i_7 as isize))
        .wrapping_add(hash_old[i_7 as usize]);
    let mut os_6: *mut uint32_t = hash;
    *os_6.offset(i_7 as isize) = x_6;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha256_update_nblocks(
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut st: *mut uint32_t,
) {
    let mut blocks: uint32_t = len.wrapping_div(64 as libc::c_uint);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < blocks {
        let mut b0: *mut uint8_t = b;
        let mut mb: *mut uint8_t = b0
            .offset(i.wrapping_mul(64 as libc::c_uint) as isize);
        sha256_update(mb, st);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha256_update_last(
    mut totlen: uint64_t,
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut hash: *mut uint32_t,
) {
    let mut blocks: uint32_t = 0;
    if len.wrapping_add(8 as libc::c_uint).wrapping_add(1 as libc::c_uint)
        <= 64 as libc::c_uint
    {
        blocks = 1 as libc::c_uint;
    } else {
        blocks = 2 as libc::c_uint;
    }
    let mut fin: uint32_t = blocks.wrapping_mul(64 as libc::c_uint);
    let mut last: [uint8_t; 128] = [
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
    let mut totlen_buf: [uint8_t; 8] = [
        0 as libc::c_uint as uint8_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut total_len_bits: uint64_t = totlen << 3 as libc::c_uint;
    store64(
        totlen_buf.as_mut_ptr(),
        if 0 != 0 {
            (total_len_bits & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (total_len_bits & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (total_len_bits & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (total_len_bits & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (total_len_bits & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
                | (total_len_bits & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
                | (total_len_bits & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
                | (total_len_bits & 0xff as libc::c_ulonglong) << 56 as libc::c_int
        } else {
            _OSSwapInt64(total_len_bits)
        },
    );
    let mut b0: *mut uint8_t = b;
    memcpy(
        last.as_mut_ptr() as *mut libc::c_void,
        b0 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    last[len as usize] = 0x80 as libc::c_uint as uint8_t;
    memcpy(
        last.as_mut_ptr().offset(fin as isize).offset(-(8 as libc::c_uint as isize))
            as *mut libc::c_void,
        totlen_buf.as_mut_ptr() as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut last00: *mut uint8_t = last.as_mut_ptr();
    let mut last10: *mut uint8_t = last.as_mut_ptr().offset(64 as libc::c_uint as isize);
    let mut l0: *mut uint8_t = last00;
    let mut l1: *mut uint8_t = last10;
    let mut lb0: *mut uint8_t = l0;
    let mut lb1: *mut uint8_t = l1;
    let mut last0: *mut uint8_t = lb0;
    let mut last1: *mut uint8_t = lb1;
    sha256_update(last0, hash);
    if blocks > 1 as libc::c_uint {
        sha256_update(last1, hash);
        return;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha256_finish(
    mut st: *mut uint32_t,
    mut h: *mut uint8_t,
) {
    let mut hbuf: [uint8_t; 32] = [
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
    let mut i: uint32_t = 0 as libc::c_uint;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        h as *mut libc::c_void,
        hbuf.as_mut_ptr() as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha224_init(mut hash: *mut uint32_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os: *mut uint32_t = hash;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_0: *mut uint32_t = hash;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_1: *mut uint32_t = hash;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_2: *mut uint32_t = hash;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_3: *mut uint32_t = hash;
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_4: *mut uint32_t = hash;
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_5: *mut uint32_t = hash;
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint32_t = Hacl_Hash_SHA2_h224[i as usize];
    let mut os_6: *mut uint32_t = hash;
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha224_update_nblocks(
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut st: *mut uint32_t,
) {
    Hacl_Hash_SHA2_sha256_update_nblocks(len, b, st);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha224_update_last(
    mut totlen: uint64_t,
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut st: *mut uint32_t,
) {
    Hacl_Hash_SHA2_sha256_update_last(totlen, len, b, st);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha224_finish(
    mut st: *mut uint32_t,
    mut h: *mut uint8_t,
) {
    let mut hbuf: [uint8_t; 32] = [
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
    let mut i: uint32_t = 0 as libc::c_uint;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store32(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(4 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff000000 as libc::c_uint) >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_uint) >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_uint) << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_uint) << 24 as libc::c_int
        } else {
            _OSSwapInt32(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        h as *mut libc::c_void,
        hbuf.as_mut_ptr() as *const libc::c_void,
        (28 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha512_init(mut hash: *mut uint64_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os: *mut uint64_t = hash;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_0: *mut uint64_t = hash;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_1: *mut uint64_t = hash;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_2: *mut uint64_t = hash;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_3: *mut uint64_t = hash;
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_4: *mut uint64_t = hash;
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_5: *mut uint64_t = hash;
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint64_t = Hacl_Hash_SHA2_h512[i as usize];
    let mut os_6: *mut uint64_t = hash;
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[inline]
unsafe extern "C" fn sha512_update(mut b: *mut uint8_t, mut hash: *mut uint64_t) {
    let mut hash_old: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    let mut ws: [uint64_t; 16] = [
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
    memcpy(
        hash_old.as_mut_ptr() as *mut libc::c_void,
        hash as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut b10: *mut uint8_t = b;
    let mut u: uint64_t = if 0 != 0 {
        (load64(b10) & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10) & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10) & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10) & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10) & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10) & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10) & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10) & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10))
    };
    ws[0 as libc::c_uint as usize] = u;
    let mut u0: uint64_t = if 0 != 0 {
        (load64(b10.offset(8 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(8 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(8 as libc::c_uint as isize)))
    };
    ws[1 as libc::c_uint as usize] = u0;
    let mut u1: uint64_t = if 0 != 0 {
        (load64(b10.offset(16 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(16 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(16 as libc::c_uint as isize)))
    };
    ws[2 as libc::c_uint as usize] = u1;
    let mut u2: uint64_t = if 0 != 0 {
        (load64(b10.offset(24 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(24 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(24 as libc::c_uint as isize)))
    };
    ws[3 as libc::c_uint as usize] = u2;
    let mut u3: uint64_t = if 0 != 0 {
        (load64(b10.offset(32 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(32 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(32 as libc::c_uint as isize)))
    };
    ws[4 as libc::c_uint as usize] = u3;
    let mut u4: uint64_t = if 0 != 0 {
        (load64(b10.offset(40 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(40 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(40 as libc::c_uint as isize)))
    };
    ws[5 as libc::c_uint as usize] = u4;
    let mut u5: uint64_t = if 0 != 0 {
        (load64(b10.offset(48 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(48 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(48 as libc::c_uint as isize)))
    };
    ws[6 as libc::c_uint as usize] = u5;
    let mut u6: uint64_t = if 0 != 0 {
        (load64(b10.offset(56 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(56 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(56 as libc::c_uint as isize)))
    };
    ws[7 as libc::c_uint as usize] = u6;
    let mut u7: uint64_t = if 0 != 0 {
        (load64(b10.offset(64 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(64 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(64 as libc::c_uint as isize)))
    };
    ws[8 as libc::c_uint as usize] = u7;
    let mut u8: uint64_t = if 0 != 0 {
        (load64(b10.offset(72 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(72 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(72 as libc::c_uint as isize)))
    };
    ws[9 as libc::c_uint as usize] = u8;
    let mut u9: uint64_t = if 0 != 0 {
        (load64(b10.offset(80 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(80 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(80 as libc::c_uint as isize)))
    };
    ws[10 as libc::c_uint as usize] = u9;
    let mut u10: uint64_t = if 0 != 0 {
        (load64(b10.offset(88 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(88 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(88 as libc::c_uint as isize)))
    };
    ws[11 as libc::c_uint as usize] = u10;
    let mut u11: uint64_t = if 0 != 0 {
        (load64(b10.offset(96 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(96 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(96 as libc::c_uint as isize)))
    };
    ws[12 as libc::c_uint as usize] = u11;
    let mut u12: uint64_t = if 0 != 0 {
        (load64(b10.offset(104 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(104 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(104 as libc::c_uint as isize)))
    };
    ws[13 as libc::c_uint as usize] = u12;
    let mut u13: uint64_t = if 0 != 0 {
        (load64(b10.offset(112 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(112 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(112 as libc::c_uint as isize)))
    };
    ws[14 as libc::c_uint as usize] = u13;
    let mut u14: uint64_t = if 0 != 0 {
        (load64(b10.offset(120 as libc::c_uint as isize))
            & 0xff00000000000000 as libc::c_ulonglong) >> 56 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff000000000000 as libc::c_ulonglong) >> 40 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff0000000000 as libc::c_ulonglong) >> 24 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff00000000 as libc::c_ulonglong) >> 8 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff000000 as libc::c_ulonglong) << 8 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff0000 as libc::c_ulonglong) << 24 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff00 as libc::c_ulonglong) << 40 as libc::c_int
            | (load64(b10.offset(120 as libc::c_uint as isize))
                & 0xff as libc::c_ulonglong) << 56 as libc::c_int
    } else {
        _OSSwapInt64(load64(b10.offset(120 as libc::c_uint as isize)))
    };
    ws[15 as libc::c_uint as usize] = u14;
    let mut i0: uint32_t = 0 as libc::c_uint;
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut k_t: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t: uint64_t = ws[i as usize];
    let mut a0: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t: uint64_t = k_t;
    let mut t1: uint64_t = h02
        .wrapping_add(
            (e0 << 50 as libc::c_uint | e0 >> 14 as libc::c_uint)
                ^ ((e0 << 46 as libc::c_uint | e0 >> 18 as libc::c_uint)
                    ^ (e0 << 23 as libc::c_uint | e0 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0 & f0 ^ !e0 & g0)
        .wrapping_add(k_e_t)
        .wrapping_add(ws_t);
    let mut t2: uint64_t = ((a0 << 36 as libc::c_uint | a0 >> 28 as libc::c_uint)
        ^ ((a0 << 30 as libc::c_uint | a0 >> 34 as libc::c_uint)
            ^ (a0 << 25 as libc::c_uint | a0 >> 39 as libc::c_uint)))
        .wrapping_add(a0 & b0 ^ (a0 & c0 ^ b0 & c0));
    let mut a1: uint64_t = t1.wrapping_add(t2);
    let mut b1: uint64_t = a0;
    let mut c1: uint64_t = b0;
    let mut d1: uint64_t = c0;
    let mut e1: uint64_t = d0.wrapping_add(t1);
    let mut f1: uint64_t = e0;
    let mut g1: uint64_t = f0;
    let mut h12: uint64_t = g0;
    *hash.offset(0 as libc::c_uint as isize) = a1;
    *hash.offset(1 as libc::c_uint as isize) = b1;
    *hash.offset(2 as libc::c_uint as isize) = c1;
    *hash.offset(3 as libc::c_uint as isize) = d1;
    *hash.offset(4 as libc::c_uint as isize) = e1;
    *hash.offset(5 as libc::c_uint as isize) = f1;
    *hash.offset(6 as libc::c_uint as isize) = g1;
    *hash.offset(7 as libc::c_uint as isize) = h12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_0: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_0: uint64_t = ws[i as usize];
    let mut a0_0: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_0: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_0: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_0: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_0: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_0: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_0: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_0: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_0: uint64_t = k_t_0;
    let mut t1_0: uint64_t = h02_0
        .wrapping_add(
            (e0_0 << 50 as libc::c_uint | e0_0 >> 14 as libc::c_uint)
                ^ ((e0_0 << 46 as libc::c_uint | e0_0 >> 18 as libc::c_uint)
                    ^ (e0_0 << 23 as libc::c_uint | e0_0 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_0 & f0_0 ^ !e0_0 & g0_0)
        .wrapping_add(k_e_t_0)
        .wrapping_add(ws_t_0);
    let mut t2_0: uint64_t = ((a0_0 << 36 as libc::c_uint | a0_0 >> 28 as libc::c_uint)
        ^ ((a0_0 << 30 as libc::c_uint | a0_0 >> 34 as libc::c_uint)
            ^ (a0_0 << 25 as libc::c_uint | a0_0 >> 39 as libc::c_uint)))
        .wrapping_add(a0_0 & b0_0 ^ (a0_0 & c0_0 ^ b0_0 & c0_0));
    let mut a1_0: uint64_t = t1_0.wrapping_add(t2_0);
    let mut b1_0: uint64_t = a0_0;
    let mut c1_0: uint64_t = b0_0;
    let mut d1_0: uint64_t = c0_0;
    let mut e1_0: uint64_t = d0_0.wrapping_add(t1_0);
    let mut f1_0: uint64_t = e0_0;
    let mut g1_0: uint64_t = f0_0;
    let mut h12_0: uint64_t = g0_0;
    *hash.offset(0 as libc::c_uint as isize) = a1_0;
    *hash.offset(1 as libc::c_uint as isize) = b1_0;
    *hash.offset(2 as libc::c_uint as isize) = c1_0;
    *hash.offset(3 as libc::c_uint as isize) = d1_0;
    *hash.offset(4 as libc::c_uint as isize) = e1_0;
    *hash.offset(5 as libc::c_uint as isize) = f1_0;
    *hash.offset(6 as libc::c_uint as isize) = g1_0;
    *hash.offset(7 as libc::c_uint as isize) = h12_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_1: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_1: uint64_t = ws[i as usize];
    let mut a0_1: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_1: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_1: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_1: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_1: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_1: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_1: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_1: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_1: uint64_t = k_t_1;
    let mut t1_1: uint64_t = h02_1
        .wrapping_add(
            (e0_1 << 50 as libc::c_uint | e0_1 >> 14 as libc::c_uint)
                ^ ((e0_1 << 46 as libc::c_uint | e0_1 >> 18 as libc::c_uint)
                    ^ (e0_1 << 23 as libc::c_uint | e0_1 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_1 & f0_1 ^ !e0_1 & g0_1)
        .wrapping_add(k_e_t_1)
        .wrapping_add(ws_t_1);
    let mut t2_1: uint64_t = ((a0_1 << 36 as libc::c_uint | a0_1 >> 28 as libc::c_uint)
        ^ ((a0_1 << 30 as libc::c_uint | a0_1 >> 34 as libc::c_uint)
            ^ (a0_1 << 25 as libc::c_uint | a0_1 >> 39 as libc::c_uint)))
        .wrapping_add(a0_1 & b0_1 ^ (a0_1 & c0_1 ^ b0_1 & c0_1));
    let mut a1_1: uint64_t = t1_1.wrapping_add(t2_1);
    let mut b1_1: uint64_t = a0_1;
    let mut c1_1: uint64_t = b0_1;
    let mut d1_1: uint64_t = c0_1;
    let mut e1_1: uint64_t = d0_1.wrapping_add(t1_1);
    let mut f1_1: uint64_t = e0_1;
    let mut g1_1: uint64_t = f0_1;
    let mut h12_1: uint64_t = g0_1;
    *hash.offset(0 as libc::c_uint as isize) = a1_1;
    *hash.offset(1 as libc::c_uint as isize) = b1_1;
    *hash.offset(2 as libc::c_uint as isize) = c1_1;
    *hash.offset(3 as libc::c_uint as isize) = d1_1;
    *hash.offset(4 as libc::c_uint as isize) = e1_1;
    *hash.offset(5 as libc::c_uint as isize) = f1_1;
    *hash.offset(6 as libc::c_uint as isize) = g1_1;
    *hash.offset(7 as libc::c_uint as isize) = h12_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_2: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_2: uint64_t = ws[i as usize];
    let mut a0_2: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_2: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_2: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_2: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_2: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_2: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_2: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_2: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_2: uint64_t = k_t_2;
    let mut t1_2: uint64_t = h02_2
        .wrapping_add(
            (e0_2 << 50 as libc::c_uint | e0_2 >> 14 as libc::c_uint)
                ^ ((e0_2 << 46 as libc::c_uint | e0_2 >> 18 as libc::c_uint)
                    ^ (e0_2 << 23 as libc::c_uint | e0_2 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_2 & f0_2 ^ !e0_2 & g0_2)
        .wrapping_add(k_e_t_2)
        .wrapping_add(ws_t_2);
    let mut t2_2: uint64_t = ((a0_2 << 36 as libc::c_uint | a0_2 >> 28 as libc::c_uint)
        ^ ((a0_2 << 30 as libc::c_uint | a0_2 >> 34 as libc::c_uint)
            ^ (a0_2 << 25 as libc::c_uint | a0_2 >> 39 as libc::c_uint)))
        .wrapping_add(a0_2 & b0_2 ^ (a0_2 & c0_2 ^ b0_2 & c0_2));
    let mut a1_2: uint64_t = t1_2.wrapping_add(t2_2);
    let mut b1_2: uint64_t = a0_2;
    let mut c1_2: uint64_t = b0_2;
    let mut d1_2: uint64_t = c0_2;
    let mut e1_2: uint64_t = d0_2.wrapping_add(t1_2);
    let mut f1_2: uint64_t = e0_2;
    let mut g1_2: uint64_t = f0_2;
    let mut h12_2: uint64_t = g0_2;
    *hash.offset(0 as libc::c_uint as isize) = a1_2;
    *hash.offset(1 as libc::c_uint as isize) = b1_2;
    *hash.offset(2 as libc::c_uint as isize) = c1_2;
    *hash.offset(3 as libc::c_uint as isize) = d1_2;
    *hash.offset(4 as libc::c_uint as isize) = e1_2;
    *hash.offset(5 as libc::c_uint as isize) = f1_2;
    *hash.offset(6 as libc::c_uint as isize) = g1_2;
    *hash.offset(7 as libc::c_uint as isize) = h12_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_3: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_3: uint64_t = ws[i as usize];
    let mut a0_3: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_3: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_3: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_3: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_3: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_3: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_3: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_3: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_3: uint64_t = k_t_3;
    let mut t1_3: uint64_t = h02_3
        .wrapping_add(
            (e0_3 << 50 as libc::c_uint | e0_3 >> 14 as libc::c_uint)
                ^ ((e0_3 << 46 as libc::c_uint | e0_3 >> 18 as libc::c_uint)
                    ^ (e0_3 << 23 as libc::c_uint | e0_3 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_3 & f0_3 ^ !e0_3 & g0_3)
        .wrapping_add(k_e_t_3)
        .wrapping_add(ws_t_3);
    let mut t2_3: uint64_t = ((a0_3 << 36 as libc::c_uint | a0_3 >> 28 as libc::c_uint)
        ^ ((a0_3 << 30 as libc::c_uint | a0_3 >> 34 as libc::c_uint)
            ^ (a0_3 << 25 as libc::c_uint | a0_3 >> 39 as libc::c_uint)))
        .wrapping_add(a0_3 & b0_3 ^ (a0_3 & c0_3 ^ b0_3 & c0_3));
    let mut a1_3: uint64_t = t1_3.wrapping_add(t2_3);
    let mut b1_3: uint64_t = a0_3;
    let mut c1_3: uint64_t = b0_3;
    let mut d1_3: uint64_t = c0_3;
    let mut e1_3: uint64_t = d0_3.wrapping_add(t1_3);
    let mut f1_3: uint64_t = e0_3;
    let mut g1_3: uint64_t = f0_3;
    let mut h12_3: uint64_t = g0_3;
    *hash.offset(0 as libc::c_uint as isize) = a1_3;
    *hash.offset(1 as libc::c_uint as isize) = b1_3;
    *hash.offset(2 as libc::c_uint as isize) = c1_3;
    *hash.offset(3 as libc::c_uint as isize) = d1_3;
    *hash.offset(4 as libc::c_uint as isize) = e1_3;
    *hash.offset(5 as libc::c_uint as isize) = f1_3;
    *hash.offset(6 as libc::c_uint as isize) = g1_3;
    *hash.offset(7 as libc::c_uint as isize) = h12_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_4: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_4: uint64_t = ws[i as usize];
    let mut a0_4: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_4: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_4: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_4: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_4: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_4: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_4: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_4: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_4: uint64_t = k_t_4;
    let mut t1_4: uint64_t = h02_4
        .wrapping_add(
            (e0_4 << 50 as libc::c_uint | e0_4 >> 14 as libc::c_uint)
                ^ ((e0_4 << 46 as libc::c_uint | e0_4 >> 18 as libc::c_uint)
                    ^ (e0_4 << 23 as libc::c_uint | e0_4 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_4 & f0_4 ^ !e0_4 & g0_4)
        .wrapping_add(k_e_t_4)
        .wrapping_add(ws_t_4);
    let mut t2_4: uint64_t = ((a0_4 << 36 as libc::c_uint | a0_4 >> 28 as libc::c_uint)
        ^ ((a0_4 << 30 as libc::c_uint | a0_4 >> 34 as libc::c_uint)
            ^ (a0_4 << 25 as libc::c_uint | a0_4 >> 39 as libc::c_uint)))
        .wrapping_add(a0_4 & b0_4 ^ (a0_4 & c0_4 ^ b0_4 & c0_4));
    let mut a1_4: uint64_t = t1_4.wrapping_add(t2_4);
    let mut b1_4: uint64_t = a0_4;
    let mut c1_4: uint64_t = b0_4;
    let mut d1_4: uint64_t = c0_4;
    let mut e1_4: uint64_t = d0_4.wrapping_add(t1_4);
    let mut f1_4: uint64_t = e0_4;
    let mut g1_4: uint64_t = f0_4;
    let mut h12_4: uint64_t = g0_4;
    *hash.offset(0 as libc::c_uint as isize) = a1_4;
    *hash.offset(1 as libc::c_uint as isize) = b1_4;
    *hash.offset(2 as libc::c_uint as isize) = c1_4;
    *hash.offset(3 as libc::c_uint as isize) = d1_4;
    *hash.offset(4 as libc::c_uint as isize) = e1_4;
    *hash.offset(5 as libc::c_uint as isize) = f1_4;
    *hash.offset(6 as libc::c_uint as isize) = g1_4;
    *hash.offset(7 as libc::c_uint as isize) = h12_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_5: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_5: uint64_t = ws[i as usize];
    let mut a0_5: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_5: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_5: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_5: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_5: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_5: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_5: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_5: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_5: uint64_t = k_t_5;
    let mut t1_5: uint64_t = h02_5
        .wrapping_add(
            (e0_5 << 50 as libc::c_uint | e0_5 >> 14 as libc::c_uint)
                ^ ((e0_5 << 46 as libc::c_uint | e0_5 >> 18 as libc::c_uint)
                    ^ (e0_5 << 23 as libc::c_uint | e0_5 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_5 & f0_5 ^ !e0_5 & g0_5)
        .wrapping_add(k_e_t_5)
        .wrapping_add(ws_t_5);
    let mut t2_5: uint64_t = ((a0_5 << 36 as libc::c_uint | a0_5 >> 28 as libc::c_uint)
        ^ ((a0_5 << 30 as libc::c_uint | a0_5 >> 34 as libc::c_uint)
            ^ (a0_5 << 25 as libc::c_uint | a0_5 >> 39 as libc::c_uint)))
        .wrapping_add(a0_5 & b0_5 ^ (a0_5 & c0_5 ^ b0_5 & c0_5));
    let mut a1_5: uint64_t = t1_5.wrapping_add(t2_5);
    let mut b1_5: uint64_t = a0_5;
    let mut c1_5: uint64_t = b0_5;
    let mut d1_5: uint64_t = c0_5;
    let mut e1_5: uint64_t = d0_5.wrapping_add(t1_5);
    let mut f1_5: uint64_t = e0_5;
    let mut g1_5: uint64_t = f0_5;
    let mut h12_5: uint64_t = g0_5;
    *hash.offset(0 as libc::c_uint as isize) = a1_5;
    *hash.offset(1 as libc::c_uint as isize) = b1_5;
    *hash.offset(2 as libc::c_uint as isize) = c1_5;
    *hash.offset(3 as libc::c_uint as isize) = d1_5;
    *hash.offset(4 as libc::c_uint as isize) = e1_5;
    *hash.offset(5 as libc::c_uint as isize) = f1_5;
    *hash.offset(6 as libc::c_uint as isize) = g1_5;
    *hash.offset(7 as libc::c_uint as isize) = h12_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_6: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_6: uint64_t = ws[i as usize];
    let mut a0_6: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_6: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_6: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_6: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_6: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_6: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_6: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_6: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_6: uint64_t = k_t_6;
    let mut t1_6: uint64_t = h02_6
        .wrapping_add(
            (e0_6 << 50 as libc::c_uint | e0_6 >> 14 as libc::c_uint)
                ^ ((e0_6 << 46 as libc::c_uint | e0_6 >> 18 as libc::c_uint)
                    ^ (e0_6 << 23 as libc::c_uint | e0_6 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_6 & f0_6 ^ !e0_6 & g0_6)
        .wrapping_add(k_e_t_6)
        .wrapping_add(ws_t_6);
    let mut t2_6: uint64_t = ((a0_6 << 36 as libc::c_uint | a0_6 >> 28 as libc::c_uint)
        ^ ((a0_6 << 30 as libc::c_uint | a0_6 >> 34 as libc::c_uint)
            ^ (a0_6 << 25 as libc::c_uint | a0_6 >> 39 as libc::c_uint)))
        .wrapping_add(a0_6 & b0_6 ^ (a0_6 & c0_6 ^ b0_6 & c0_6));
    let mut a1_6: uint64_t = t1_6.wrapping_add(t2_6);
    let mut b1_6: uint64_t = a0_6;
    let mut c1_6: uint64_t = b0_6;
    let mut d1_6: uint64_t = c0_6;
    let mut e1_6: uint64_t = d0_6.wrapping_add(t1_6);
    let mut f1_6: uint64_t = e0_6;
    let mut g1_6: uint64_t = f0_6;
    let mut h12_6: uint64_t = g0_6;
    *hash.offset(0 as libc::c_uint as isize) = a1_6;
    *hash.offset(1 as libc::c_uint as isize) = b1_6;
    *hash.offset(2 as libc::c_uint as isize) = c1_6;
    *hash.offset(3 as libc::c_uint as isize) = d1_6;
    *hash.offset(4 as libc::c_uint as isize) = e1_6;
    *hash.offset(5 as libc::c_uint as isize) = f1_6;
    *hash.offset(6 as libc::c_uint as isize) = g1_6;
    *hash.offset(7 as libc::c_uint as isize) = h12_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_7: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_7: uint64_t = ws[i as usize];
    let mut a0_7: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_7: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_7: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_7: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_7: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_7: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_7: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_7: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_7: uint64_t = k_t_7;
    let mut t1_7: uint64_t = h02_7
        .wrapping_add(
            (e0_7 << 50 as libc::c_uint | e0_7 >> 14 as libc::c_uint)
                ^ ((e0_7 << 46 as libc::c_uint | e0_7 >> 18 as libc::c_uint)
                    ^ (e0_7 << 23 as libc::c_uint | e0_7 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_7 & f0_7 ^ !e0_7 & g0_7)
        .wrapping_add(k_e_t_7)
        .wrapping_add(ws_t_7);
    let mut t2_7: uint64_t = ((a0_7 << 36 as libc::c_uint | a0_7 >> 28 as libc::c_uint)
        ^ ((a0_7 << 30 as libc::c_uint | a0_7 >> 34 as libc::c_uint)
            ^ (a0_7 << 25 as libc::c_uint | a0_7 >> 39 as libc::c_uint)))
        .wrapping_add(a0_7 & b0_7 ^ (a0_7 & c0_7 ^ b0_7 & c0_7));
    let mut a1_7: uint64_t = t1_7.wrapping_add(t2_7);
    let mut b1_7: uint64_t = a0_7;
    let mut c1_7: uint64_t = b0_7;
    let mut d1_7: uint64_t = c0_7;
    let mut e1_7: uint64_t = d0_7.wrapping_add(t1_7);
    let mut f1_7: uint64_t = e0_7;
    let mut g1_7: uint64_t = f0_7;
    let mut h12_7: uint64_t = g0_7;
    *hash.offset(0 as libc::c_uint as isize) = a1_7;
    *hash.offset(1 as libc::c_uint as isize) = b1_7;
    *hash.offset(2 as libc::c_uint as isize) = c1_7;
    *hash.offset(3 as libc::c_uint as isize) = d1_7;
    *hash.offset(4 as libc::c_uint as isize) = e1_7;
    *hash.offset(5 as libc::c_uint as isize) = f1_7;
    *hash.offset(6 as libc::c_uint as isize) = g1_7;
    *hash.offset(7 as libc::c_uint as isize) = h12_7;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_8: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_8: uint64_t = ws[i as usize];
    let mut a0_8: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_8: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_8: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_8: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_8: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_8: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_8: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_8: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_8: uint64_t = k_t_8;
    let mut t1_8: uint64_t = h02_8
        .wrapping_add(
            (e0_8 << 50 as libc::c_uint | e0_8 >> 14 as libc::c_uint)
                ^ ((e0_8 << 46 as libc::c_uint | e0_8 >> 18 as libc::c_uint)
                    ^ (e0_8 << 23 as libc::c_uint | e0_8 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_8 & f0_8 ^ !e0_8 & g0_8)
        .wrapping_add(k_e_t_8)
        .wrapping_add(ws_t_8);
    let mut t2_8: uint64_t = ((a0_8 << 36 as libc::c_uint | a0_8 >> 28 as libc::c_uint)
        ^ ((a0_8 << 30 as libc::c_uint | a0_8 >> 34 as libc::c_uint)
            ^ (a0_8 << 25 as libc::c_uint | a0_8 >> 39 as libc::c_uint)))
        .wrapping_add(a0_8 & b0_8 ^ (a0_8 & c0_8 ^ b0_8 & c0_8));
    let mut a1_8: uint64_t = t1_8.wrapping_add(t2_8);
    let mut b1_8: uint64_t = a0_8;
    let mut c1_8: uint64_t = b0_8;
    let mut d1_8: uint64_t = c0_8;
    let mut e1_8: uint64_t = d0_8.wrapping_add(t1_8);
    let mut f1_8: uint64_t = e0_8;
    let mut g1_8: uint64_t = f0_8;
    let mut h12_8: uint64_t = g0_8;
    *hash.offset(0 as libc::c_uint as isize) = a1_8;
    *hash.offset(1 as libc::c_uint as isize) = b1_8;
    *hash.offset(2 as libc::c_uint as isize) = c1_8;
    *hash.offset(3 as libc::c_uint as isize) = d1_8;
    *hash.offset(4 as libc::c_uint as isize) = e1_8;
    *hash.offset(5 as libc::c_uint as isize) = f1_8;
    *hash.offset(6 as libc::c_uint as isize) = g1_8;
    *hash.offset(7 as libc::c_uint as isize) = h12_8;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_9: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_9: uint64_t = ws[i as usize];
    let mut a0_9: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_9: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_9: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_9: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_9: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_9: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_9: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_9: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_9: uint64_t = k_t_9;
    let mut t1_9: uint64_t = h02_9
        .wrapping_add(
            (e0_9 << 50 as libc::c_uint | e0_9 >> 14 as libc::c_uint)
                ^ ((e0_9 << 46 as libc::c_uint | e0_9 >> 18 as libc::c_uint)
                    ^ (e0_9 << 23 as libc::c_uint | e0_9 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_9 & f0_9 ^ !e0_9 & g0_9)
        .wrapping_add(k_e_t_9)
        .wrapping_add(ws_t_9);
    let mut t2_9: uint64_t = ((a0_9 << 36 as libc::c_uint | a0_9 >> 28 as libc::c_uint)
        ^ ((a0_9 << 30 as libc::c_uint | a0_9 >> 34 as libc::c_uint)
            ^ (a0_9 << 25 as libc::c_uint | a0_9 >> 39 as libc::c_uint)))
        .wrapping_add(a0_9 & b0_9 ^ (a0_9 & c0_9 ^ b0_9 & c0_9));
    let mut a1_9: uint64_t = t1_9.wrapping_add(t2_9);
    let mut b1_9: uint64_t = a0_9;
    let mut c1_9: uint64_t = b0_9;
    let mut d1_9: uint64_t = c0_9;
    let mut e1_9: uint64_t = d0_9.wrapping_add(t1_9);
    let mut f1_9: uint64_t = e0_9;
    let mut g1_9: uint64_t = f0_9;
    let mut h12_9: uint64_t = g0_9;
    *hash.offset(0 as libc::c_uint as isize) = a1_9;
    *hash.offset(1 as libc::c_uint as isize) = b1_9;
    *hash.offset(2 as libc::c_uint as isize) = c1_9;
    *hash.offset(3 as libc::c_uint as isize) = d1_9;
    *hash.offset(4 as libc::c_uint as isize) = e1_9;
    *hash.offset(5 as libc::c_uint as isize) = f1_9;
    *hash.offset(6 as libc::c_uint as isize) = g1_9;
    *hash.offset(7 as libc::c_uint as isize) = h12_9;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_10: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_10: uint64_t = ws[i as usize];
    let mut a0_10: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_10: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_10: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_10: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_10: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_10: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_10: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_10: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_10: uint64_t = k_t_10;
    let mut t1_10: uint64_t = h02_10
        .wrapping_add(
            (e0_10 << 50 as libc::c_uint | e0_10 >> 14 as libc::c_uint)
                ^ ((e0_10 << 46 as libc::c_uint | e0_10 >> 18 as libc::c_uint)
                    ^ (e0_10 << 23 as libc::c_uint | e0_10 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_10 & f0_10 ^ !e0_10 & g0_10)
        .wrapping_add(k_e_t_10)
        .wrapping_add(ws_t_10);
    let mut t2_10: uint64_t = ((a0_10 << 36 as libc::c_uint
        | a0_10 >> 28 as libc::c_uint)
        ^ ((a0_10 << 30 as libc::c_uint | a0_10 >> 34 as libc::c_uint)
            ^ (a0_10 << 25 as libc::c_uint | a0_10 >> 39 as libc::c_uint)))
        .wrapping_add(a0_10 & b0_10 ^ (a0_10 & c0_10 ^ b0_10 & c0_10));
    let mut a1_10: uint64_t = t1_10.wrapping_add(t2_10);
    let mut b1_10: uint64_t = a0_10;
    let mut c1_10: uint64_t = b0_10;
    let mut d1_10: uint64_t = c0_10;
    let mut e1_10: uint64_t = d0_10.wrapping_add(t1_10);
    let mut f1_10: uint64_t = e0_10;
    let mut g1_10: uint64_t = f0_10;
    let mut h12_10: uint64_t = g0_10;
    *hash.offset(0 as libc::c_uint as isize) = a1_10;
    *hash.offset(1 as libc::c_uint as isize) = b1_10;
    *hash.offset(2 as libc::c_uint as isize) = c1_10;
    *hash.offset(3 as libc::c_uint as isize) = d1_10;
    *hash.offset(4 as libc::c_uint as isize) = e1_10;
    *hash.offset(5 as libc::c_uint as isize) = f1_10;
    *hash.offset(6 as libc::c_uint as isize) = g1_10;
    *hash.offset(7 as libc::c_uint as isize) = h12_10;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_11: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_11: uint64_t = ws[i as usize];
    let mut a0_11: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_11: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_11: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_11: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_11: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_11: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_11: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_11: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_11: uint64_t = k_t_11;
    let mut t1_11: uint64_t = h02_11
        .wrapping_add(
            (e0_11 << 50 as libc::c_uint | e0_11 >> 14 as libc::c_uint)
                ^ ((e0_11 << 46 as libc::c_uint | e0_11 >> 18 as libc::c_uint)
                    ^ (e0_11 << 23 as libc::c_uint | e0_11 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_11 & f0_11 ^ !e0_11 & g0_11)
        .wrapping_add(k_e_t_11)
        .wrapping_add(ws_t_11);
    let mut t2_11: uint64_t = ((a0_11 << 36 as libc::c_uint
        | a0_11 >> 28 as libc::c_uint)
        ^ ((a0_11 << 30 as libc::c_uint | a0_11 >> 34 as libc::c_uint)
            ^ (a0_11 << 25 as libc::c_uint | a0_11 >> 39 as libc::c_uint)))
        .wrapping_add(a0_11 & b0_11 ^ (a0_11 & c0_11 ^ b0_11 & c0_11));
    let mut a1_11: uint64_t = t1_11.wrapping_add(t2_11);
    let mut b1_11: uint64_t = a0_11;
    let mut c1_11: uint64_t = b0_11;
    let mut d1_11: uint64_t = c0_11;
    let mut e1_11: uint64_t = d0_11.wrapping_add(t1_11);
    let mut f1_11: uint64_t = e0_11;
    let mut g1_11: uint64_t = f0_11;
    let mut h12_11: uint64_t = g0_11;
    *hash.offset(0 as libc::c_uint as isize) = a1_11;
    *hash.offset(1 as libc::c_uint as isize) = b1_11;
    *hash.offset(2 as libc::c_uint as isize) = c1_11;
    *hash.offset(3 as libc::c_uint as isize) = d1_11;
    *hash.offset(4 as libc::c_uint as isize) = e1_11;
    *hash.offset(5 as libc::c_uint as isize) = f1_11;
    *hash.offset(6 as libc::c_uint as isize) = g1_11;
    *hash.offset(7 as libc::c_uint as isize) = h12_11;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_12: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_12: uint64_t = ws[i as usize];
    let mut a0_12: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_12: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_12: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_12: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_12: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_12: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_12: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_12: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_12: uint64_t = k_t_12;
    let mut t1_12: uint64_t = h02_12
        .wrapping_add(
            (e0_12 << 50 as libc::c_uint | e0_12 >> 14 as libc::c_uint)
                ^ ((e0_12 << 46 as libc::c_uint | e0_12 >> 18 as libc::c_uint)
                    ^ (e0_12 << 23 as libc::c_uint | e0_12 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_12 & f0_12 ^ !e0_12 & g0_12)
        .wrapping_add(k_e_t_12)
        .wrapping_add(ws_t_12);
    let mut t2_12: uint64_t = ((a0_12 << 36 as libc::c_uint
        | a0_12 >> 28 as libc::c_uint)
        ^ ((a0_12 << 30 as libc::c_uint | a0_12 >> 34 as libc::c_uint)
            ^ (a0_12 << 25 as libc::c_uint | a0_12 >> 39 as libc::c_uint)))
        .wrapping_add(a0_12 & b0_12 ^ (a0_12 & c0_12 ^ b0_12 & c0_12));
    let mut a1_12: uint64_t = t1_12.wrapping_add(t2_12);
    let mut b1_12: uint64_t = a0_12;
    let mut c1_12: uint64_t = b0_12;
    let mut d1_12: uint64_t = c0_12;
    let mut e1_12: uint64_t = d0_12.wrapping_add(t1_12);
    let mut f1_12: uint64_t = e0_12;
    let mut g1_12: uint64_t = f0_12;
    let mut h12_12: uint64_t = g0_12;
    *hash.offset(0 as libc::c_uint as isize) = a1_12;
    *hash.offset(1 as libc::c_uint as isize) = b1_12;
    *hash.offset(2 as libc::c_uint as isize) = c1_12;
    *hash.offset(3 as libc::c_uint as isize) = d1_12;
    *hash.offset(4 as libc::c_uint as isize) = e1_12;
    *hash.offset(5 as libc::c_uint as isize) = f1_12;
    *hash.offset(6 as libc::c_uint as isize) = g1_12;
    *hash.offset(7 as libc::c_uint as isize) = h12_12;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_13: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_13: uint64_t = ws[i as usize];
    let mut a0_13: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_13: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_13: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_13: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_13: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_13: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_13: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_13: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_13: uint64_t = k_t_13;
    let mut t1_13: uint64_t = h02_13
        .wrapping_add(
            (e0_13 << 50 as libc::c_uint | e0_13 >> 14 as libc::c_uint)
                ^ ((e0_13 << 46 as libc::c_uint | e0_13 >> 18 as libc::c_uint)
                    ^ (e0_13 << 23 as libc::c_uint | e0_13 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_13 & f0_13 ^ !e0_13 & g0_13)
        .wrapping_add(k_e_t_13)
        .wrapping_add(ws_t_13);
    let mut t2_13: uint64_t = ((a0_13 << 36 as libc::c_uint
        | a0_13 >> 28 as libc::c_uint)
        ^ ((a0_13 << 30 as libc::c_uint | a0_13 >> 34 as libc::c_uint)
            ^ (a0_13 << 25 as libc::c_uint | a0_13 >> 39 as libc::c_uint)))
        .wrapping_add(a0_13 & b0_13 ^ (a0_13 & c0_13 ^ b0_13 & c0_13));
    let mut a1_13: uint64_t = t1_13.wrapping_add(t2_13);
    let mut b1_13: uint64_t = a0_13;
    let mut c1_13: uint64_t = b0_13;
    let mut d1_13: uint64_t = c0_13;
    let mut e1_13: uint64_t = d0_13.wrapping_add(t1_13);
    let mut f1_13: uint64_t = e0_13;
    let mut g1_13: uint64_t = f0_13;
    let mut h12_13: uint64_t = g0_13;
    *hash.offset(0 as libc::c_uint as isize) = a1_13;
    *hash.offset(1 as libc::c_uint as isize) = b1_13;
    *hash.offset(2 as libc::c_uint as isize) = c1_13;
    *hash.offset(3 as libc::c_uint as isize) = d1_13;
    *hash.offset(4 as libc::c_uint as isize) = e1_13;
    *hash.offset(5 as libc::c_uint as isize) = f1_13;
    *hash.offset(6 as libc::c_uint as isize) = g1_13;
    *hash.offset(7 as libc::c_uint as isize) = h12_13;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_14: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i) as usize];
    let mut ws_t_14: uint64_t = ws[i as usize];
    let mut a0_14: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_14: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_14: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_14: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_14: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_14: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_14: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_14: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_14: uint64_t = k_t_14;
    let mut t1_14: uint64_t = h02_14
        .wrapping_add(
            (e0_14 << 50 as libc::c_uint | e0_14 >> 14 as libc::c_uint)
                ^ ((e0_14 << 46 as libc::c_uint | e0_14 >> 18 as libc::c_uint)
                    ^ (e0_14 << 23 as libc::c_uint | e0_14 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_14 & f0_14 ^ !e0_14 & g0_14)
        .wrapping_add(k_e_t_14)
        .wrapping_add(ws_t_14);
    let mut t2_14: uint64_t = ((a0_14 << 36 as libc::c_uint
        | a0_14 >> 28 as libc::c_uint)
        ^ ((a0_14 << 30 as libc::c_uint | a0_14 >> 34 as libc::c_uint)
            ^ (a0_14 << 25 as libc::c_uint | a0_14 >> 39 as libc::c_uint)))
        .wrapping_add(a0_14 & b0_14 ^ (a0_14 & c0_14 ^ b0_14 & c0_14));
    let mut a1_14: uint64_t = t1_14.wrapping_add(t2_14);
    let mut b1_14: uint64_t = a0_14;
    let mut c1_14: uint64_t = b0_14;
    let mut d1_14: uint64_t = c0_14;
    let mut e1_14: uint64_t = d0_14.wrapping_add(t1_14);
    let mut f1_14: uint64_t = e0_14;
    let mut g1_14: uint64_t = f0_14;
    let mut h12_14: uint64_t = g0_14;
    *hash.offset(0 as libc::c_uint as isize) = a1_14;
    *hash.offset(1 as libc::c_uint as isize) = b1_14;
    *hash.offset(2 as libc::c_uint as isize) = c1_14;
    *hash.offset(3 as libc::c_uint as isize) = d1_14;
    *hash.offset(4 as libc::c_uint as isize) = e1_14;
    *hash.offset(5 as libc::c_uint as isize) = f1_14;
    *hash.offset(6 as libc::c_uint as isize) = g1_14;
    *hash.offset(7 as libc::c_uint as isize) = h12_14;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 4 as libc::c_uint {
        let mut i_0: uint32_t = 0 as libc::c_uint;
        let mut t16: uint64_t = ws[i_0 as usize];
        let mut t15: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_15: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1: uint64_t = (t2_15 << 45 as libc::c_uint
            | t2_15 >> 19 as libc::c_uint)
            ^ ((t2_15 << 3 as libc::c_uint | t2_15 >> 61 as libc::c_uint)
                ^ t2_15 >> 6 as libc::c_uint);
        let mut s0: uint64_t = (t15 << 63 as libc::c_uint | t15 >> 1 as libc::c_uint)
            ^ ((t15 << 56 as libc::c_uint | t15 >> 8 as libc::c_uint)
                ^ t15 >> 7 as libc::c_uint);
        ws[i_0 as usize] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_0: uint64_t = ws[i_0 as usize];
        let mut t15_0: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_0: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_16: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_0: uint64_t = (t2_16 << 45 as libc::c_uint
            | t2_16 >> 19 as libc::c_uint)
            ^ ((t2_16 << 3 as libc::c_uint | t2_16 >> 61 as libc::c_uint)
                ^ t2_16 >> 6 as libc::c_uint);
        let mut s0_0: uint64_t = (t15_0 << 63 as libc::c_uint
            | t15_0 >> 1 as libc::c_uint)
            ^ ((t15_0 << 56 as libc::c_uint | t15_0 >> 8 as libc::c_uint)
                ^ t15_0 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_0.wrapping_add(t7_0).wrapping_add(s0_0).wrapping_add(t16_0);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_1: uint64_t = ws[i_0 as usize];
        let mut t15_1: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_1: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_17: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_1: uint64_t = (t2_17 << 45 as libc::c_uint
            | t2_17 >> 19 as libc::c_uint)
            ^ ((t2_17 << 3 as libc::c_uint | t2_17 >> 61 as libc::c_uint)
                ^ t2_17 >> 6 as libc::c_uint);
        let mut s0_1: uint64_t = (t15_1 << 63 as libc::c_uint
            | t15_1 >> 1 as libc::c_uint)
            ^ ((t15_1 << 56 as libc::c_uint | t15_1 >> 8 as libc::c_uint)
                ^ t15_1 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_1.wrapping_add(t7_1).wrapping_add(s0_1).wrapping_add(t16_1);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_2: uint64_t = ws[i_0 as usize];
        let mut t15_2: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_2: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_18: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_2: uint64_t = (t2_18 << 45 as libc::c_uint
            | t2_18 >> 19 as libc::c_uint)
            ^ ((t2_18 << 3 as libc::c_uint | t2_18 >> 61 as libc::c_uint)
                ^ t2_18 >> 6 as libc::c_uint);
        let mut s0_2: uint64_t = (t15_2 << 63 as libc::c_uint
            | t15_2 >> 1 as libc::c_uint)
            ^ ((t15_2 << 56 as libc::c_uint | t15_2 >> 8 as libc::c_uint)
                ^ t15_2 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_2.wrapping_add(t7_2).wrapping_add(s0_2).wrapping_add(t16_2);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_3: uint64_t = ws[i_0 as usize];
        let mut t15_3: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_3: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_19: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_3: uint64_t = (t2_19 << 45 as libc::c_uint
            | t2_19 >> 19 as libc::c_uint)
            ^ ((t2_19 << 3 as libc::c_uint | t2_19 >> 61 as libc::c_uint)
                ^ t2_19 >> 6 as libc::c_uint);
        let mut s0_3: uint64_t = (t15_3 << 63 as libc::c_uint
            | t15_3 >> 1 as libc::c_uint)
            ^ ((t15_3 << 56 as libc::c_uint | t15_3 >> 8 as libc::c_uint)
                ^ t15_3 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_3.wrapping_add(t7_3).wrapping_add(s0_3).wrapping_add(t16_3);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_4: uint64_t = ws[i_0 as usize];
        let mut t15_4: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_4: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_20: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_4: uint64_t = (t2_20 << 45 as libc::c_uint
            | t2_20 >> 19 as libc::c_uint)
            ^ ((t2_20 << 3 as libc::c_uint | t2_20 >> 61 as libc::c_uint)
                ^ t2_20 >> 6 as libc::c_uint);
        let mut s0_4: uint64_t = (t15_4 << 63 as libc::c_uint
            | t15_4 >> 1 as libc::c_uint)
            ^ ((t15_4 << 56 as libc::c_uint | t15_4 >> 8 as libc::c_uint)
                ^ t15_4 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_4.wrapping_add(t7_4).wrapping_add(s0_4).wrapping_add(t16_4);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_5: uint64_t = ws[i_0 as usize];
        let mut t15_5: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_5: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_21: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_5: uint64_t = (t2_21 << 45 as libc::c_uint
            | t2_21 >> 19 as libc::c_uint)
            ^ ((t2_21 << 3 as libc::c_uint | t2_21 >> 61 as libc::c_uint)
                ^ t2_21 >> 6 as libc::c_uint);
        let mut s0_5: uint64_t = (t15_5 << 63 as libc::c_uint
            | t15_5 >> 1 as libc::c_uint)
            ^ ((t15_5 << 56 as libc::c_uint | t15_5 >> 8 as libc::c_uint)
                ^ t15_5 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_5.wrapping_add(t7_5).wrapping_add(s0_5).wrapping_add(t16_5);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_6: uint64_t = ws[i_0 as usize];
        let mut t15_6: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_6: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_22: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_6: uint64_t = (t2_22 << 45 as libc::c_uint
            | t2_22 >> 19 as libc::c_uint)
            ^ ((t2_22 << 3 as libc::c_uint | t2_22 >> 61 as libc::c_uint)
                ^ t2_22 >> 6 as libc::c_uint);
        let mut s0_6: uint64_t = (t15_6 << 63 as libc::c_uint
            | t15_6 >> 1 as libc::c_uint)
            ^ ((t15_6 << 56 as libc::c_uint | t15_6 >> 8 as libc::c_uint)
                ^ t15_6 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_6.wrapping_add(t7_6).wrapping_add(s0_6).wrapping_add(t16_6);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_7: uint64_t = ws[i_0 as usize];
        let mut t15_7: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_7: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_23: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_7: uint64_t = (t2_23 << 45 as libc::c_uint
            | t2_23 >> 19 as libc::c_uint)
            ^ ((t2_23 << 3 as libc::c_uint | t2_23 >> 61 as libc::c_uint)
                ^ t2_23 >> 6 as libc::c_uint);
        let mut s0_7: uint64_t = (t15_7 << 63 as libc::c_uint
            | t15_7 >> 1 as libc::c_uint)
            ^ ((t15_7 << 56 as libc::c_uint | t15_7 >> 8 as libc::c_uint)
                ^ t15_7 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_7.wrapping_add(t7_7).wrapping_add(s0_7).wrapping_add(t16_7);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_8: uint64_t = ws[i_0 as usize];
        let mut t15_8: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_8: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_24: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_8: uint64_t = (t2_24 << 45 as libc::c_uint
            | t2_24 >> 19 as libc::c_uint)
            ^ ((t2_24 << 3 as libc::c_uint | t2_24 >> 61 as libc::c_uint)
                ^ t2_24 >> 6 as libc::c_uint);
        let mut s0_8: uint64_t = (t15_8 << 63 as libc::c_uint
            | t15_8 >> 1 as libc::c_uint)
            ^ ((t15_8 << 56 as libc::c_uint | t15_8 >> 8 as libc::c_uint)
                ^ t15_8 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_8.wrapping_add(t7_8).wrapping_add(s0_8).wrapping_add(t16_8);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_9: uint64_t = ws[i_0 as usize];
        let mut t15_9: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_9: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_25: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_9: uint64_t = (t2_25 << 45 as libc::c_uint
            | t2_25 >> 19 as libc::c_uint)
            ^ ((t2_25 << 3 as libc::c_uint | t2_25 >> 61 as libc::c_uint)
                ^ t2_25 >> 6 as libc::c_uint);
        let mut s0_9: uint64_t = (t15_9 << 63 as libc::c_uint
            | t15_9 >> 1 as libc::c_uint)
            ^ ((t15_9 << 56 as libc::c_uint | t15_9 >> 8 as libc::c_uint)
                ^ t15_9 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_9.wrapping_add(t7_9).wrapping_add(s0_9).wrapping_add(t16_9);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_10: uint64_t = ws[i_0 as usize];
        let mut t15_10: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_10: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_26: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_10: uint64_t = (t2_26 << 45 as libc::c_uint
            | t2_26 >> 19 as libc::c_uint)
            ^ ((t2_26 << 3 as libc::c_uint | t2_26 >> 61 as libc::c_uint)
                ^ t2_26 >> 6 as libc::c_uint);
        let mut s0_10: uint64_t = (t15_10 << 63 as libc::c_uint
            | t15_10 >> 1 as libc::c_uint)
            ^ ((t15_10 << 56 as libc::c_uint | t15_10 >> 8 as libc::c_uint)
                ^ t15_10 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_10
            .wrapping_add(t7_10)
            .wrapping_add(s0_10)
            .wrapping_add(t16_10);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_11: uint64_t = ws[i_0 as usize];
        let mut t15_11: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_11: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_27: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_11: uint64_t = (t2_27 << 45 as libc::c_uint
            | t2_27 >> 19 as libc::c_uint)
            ^ ((t2_27 << 3 as libc::c_uint | t2_27 >> 61 as libc::c_uint)
                ^ t2_27 >> 6 as libc::c_uint);
        let mut s0_11: uint64_t = (t15_11 << 63 as libc::c_uint
            | t15_11 >> 1 as libc::c_uint)
            ^ ((t15_11 << 56 as libc::c_uint | t15_11 >> 8 as libc::c_uint)
                ^ t15_11 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_11
            .wrapping_add(t7_11)
            .wrapping_add(s0_11)
            .wrapping_add(t16_11);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_12: uint64_t = ws[i_0 as usize];
        let mut t15_12: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_12: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_28: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_12: uint64_t = (t2_28 << 45 as libc::c_uint
            | t2_28 >> 19 as libc::c_uint)
            ^ ((t2_28 << 3 as libc::c_uint | t2_28 >> 61 as libc::c_uint)
                ^ t2_28 >> 6 as libc::c_uint);
        let mut s0_12: uint64_t = (t15_12 << 63 as libc::c_uint
            | t15_12 >> 1 as libc::c_uint)
            ^ ((t15_12 << 56 as libc::c_uint | t15_12 >> 8 as libc::c_uint)
                ^ t15_12 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_12
            .wrapping_add(t7_12)
            .wrapping_add(s0_12)
            .wrapping_add(t16_12);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_13: uint64_t = ws[i_0 as usize];
        let mut t15_13: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_13: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_29: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_13: uint64_t = (t2_29 << 45 as libc::c_uint
            | t2_29 >> 19 as libc::c_uint)
            ^ ((t2_29 << 3 as libc::c_uint | t2_29 >> 61 as libc::c_uint)
                ^ t2_29 >> 6 as libc::c_uint);
        let mut s0_13: uint64_t = (t15_13 << 63 as libc::c_uint
            | t15_13 >> 1 as libc::c_uint)
            ^ ((t15_13 << 56 as libc::c_uint | t15_13 >> 8 as libc::c_uint)
                ^ t15_13 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_13
            .wrapping_add(t7_13)
            .wrapping_add(s0_13)
            .wrapping_add(t16_13);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_14: uint64_t = ws[i_0 as usize];
        let mut t15_14: uint64_t = ws[i_0
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_14: uint64_t = ws[i_0
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_30: uint64_t = ws[i_0
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_14: uint64_t = (t2_30 << 45 as libc::c_uint
            | t2_30 >> 19 as libc::c_uint)
            ^ ((t2_30 << 3 as libc::c_uint | t2_30 >> 61 as libc::c_uint)
                ^ t2_30 >> 6 as libc::c_uint);
        let mut s0_14: uint64_t = (t15_14 << 63 as libc::c_uint
            | t15_14 >> 1 as libc::c_uint)
            ^ ((t15_14 << 56 as libc::c_uint | t15_14 >> 8 as libc::c_uint)
                ^ t15_14 >> 7 as libc::c_uint);
        ws[i_0
            as usize] = s1_14
            .wrapping_add(t7_14)
            .wrapping_add(s0_14)
            .wrapping_add(t16_14);
        i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_1: uint32_t = 0 as libc::c_uint;
    let mut k_t_15: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_15: uint64_t = ws[i_1 as usize];
    let mut a0_15: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_15: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_15: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_15: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_15: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_15: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_15: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_15: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_15: uint64_t = k_t_15;
    let mut t1_15: uint64_t = h02_15
        .wrapping_add(
            (e0_15 << 50 as libc::c_uint | e0_15 >> 14 as libc::c_uint)
                ^ ((e0_15 << 46 as libc::c_uint | e0_15 >> 18 as libc::c_uint)
                    ^ (e0_15 << 23 as libc::c_uint | e0_15 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_15 & f0_15 ^ !e0_15 & g0_15)
        .wrapping_add(k_e_t_15)
        .wrapping_add(ws_t_15);
    let mut t2_31: uint64_t = ((a0_15 << 36 as libc::c_uint
        | a0_15 >> 28 as libc::c_uint)
        ^ ((a0_15 << 30 as libc::c_uint | a0_15 >> 34 as libc::c_uint)
            ^ (a0_15 << 25 as libc::c_uint | a0_15 >> 39 as libc::c_uint)))
        .wrapping_add(a0_15 & b0_15 ^ (a0_15 & c0_15 ^ b0_15 & c0_15));
    let mut a1_15: uint64_t = t1_15.wrapping_add(t2_31);
    let mut b1_15: uint64_t = a0_15;
    let mut c1_15: uint64_t = b0_15;
    let mut d1_15: uint64_t = c0_15;
    let mut e1_15: uint64_t = d0_15.wrapping_add(t1_15);
    let mut f1_15: uint64_t = e0_15;
    let mut g1_15: uint64_t = f0_15;
    let mut h12_15: uint64_t = g0_15;
    *hash.offset(0 as libc::c_uint as isize) = a1_15;
    *hash.offset(1 as libc::c_uint as isize) = b1_15;
    *hash.offset(2 as libc::c_uint as isize) = c1_15;
    *hash.offset(3 as libc::c_uint as isize) = d1_15;
    *hash.offset(4 as libc::c_uint as isize) = e1_15;
    *hash.offset(5 as libc::c_uint as isize) = f1_15;
    *hash.offset(6 as libc::c_uint as isize) = g1_15;
    *hash.offset(7 as libc::c_uint as isize) = h12_15;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_16: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_16: uint64_t = ws[i_1 as usize];
    let mut a0_16: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_16: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_16: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_16: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_16: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_16: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_16: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_16: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_16: uint64_t = k_t_16;
    let mut t1_16: uint64_t = h02_16
        .wrapping_add(
            (e0_16 << 50 as libc::c_uint | e0_16 >> 14 as libc::c_uint)
                ^ ((e0_16 << 46 as libc::c_uint | e0_16 >> 18 as libc::c_uint)
                    ^ (e0_16 << 23 as libc::c_uint | e0_16 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_16 & f0_16 ^ !e0_16 & g0_16)
        .wrapping_add(k_e_t_16)
        .wrapping_add(ws_t_16);
    let mut t2_32: uint64_t = ((a0_16 << 36 as libc::c_uint
        | a0_16 >> 28 as libc::c_uint)
        ^ ((a0_16 << 30 as libc::c_uint | a0_16 >> 34 as libc::c_uint)
            ^ (a0_16 << 25 as libc::c_uint | a0_16 >> 39 as libc::c_uint)))
        .wrapping_add(a0_16 & b0_16 ^ (a0_16 & c0_16 ^ b0_16 & c0_16));
    let mut a1_16: uint64_t = t1_16.wrapping_add(t2_32);
    let mut b1_16: uint64_t = a0_16;
    let mut c1_16: uint64_t = b0_16;
    let mut d1_16: uint64_t = c0_16;
    let mut e1_16: uint64_t = d0_16.wrapping_add(t1_16);
    let mut f1_16: uint64_t = e0_16;
    let mut g1_16: uint64_t = f0_16;
    let mut h12_16: uint64_t = g0_16;
    *hash.offset(0 as libc::c_uint as isize) = a1_16;
    *hash.offset(1 as libc::c_uint as isize) = b1_16;
    *hash.offset(2 as libc::c_uint as isize) = c1_16;
    *hash.offset(3 as libc::c_uint as isize) = d1_16;
    *hash.offset(4 as libc::c_uint as isize) = e1_16;
    *hash.offset(5 as libc::c_uint as isize) = f1_16;
    *hash.offset(6 as libc::c_uint as isize) = g1_16;
    *hash.offset(7 as libc::c_uint as isize) = h12_16;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_17: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_17: uint64_t = ws[i_1 as usize];
    let mut a0_17: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_17: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_17: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_17: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_17: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_17: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_17: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_17: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_17: uint64_t = k_t_17;
    let mut t1_17: uint64_t = h02_17
        .wrapping_add(
            (e0_17 << 50 as libc::c_uint | e0_17 >> 14 as libc::c_uint)
                ^ ((e0_17 << 46 as libc::c_uint | e0_17 >> 18 as libc::c_uint)
                    ^ (e0_17 << 23 as libc::c_uint | e0_17 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_17 & f0_17 ^ !e0_17 & g0_17)
        .wrapping_add(k_e_t_17)
        .wrapping_add(ws_t_17);
    let mut t2_33: uint64_t = ((a0_17 << 36 as libc::c_uint
        | a0_17 >> 28 as libc::c_uint)
        ^ ((a0_17 << 30 as libc::c_uint | a0_17 >> 34 as libc::c_uint)
            ^ (a0_17 << 25 as libc::c_uint | a0_17 >> 39 as libc::c_uint)))
        .wrapping_add(a0_17 & b0_17 ^ (a0_17 & c0_17 ^ b0_17 & c0_17));
    let mut a1_17: uint64_t = t1_17.wrapping_add(t2_33);
    let mut b1_17: uint64_t = a0_17;
    let mut c1_17: uint64_t = b0_17;
    let mut d1_17: uint64_t = c0_17;
    let mut e1_17: uint64_t = d0_17.wrapping_add(t1_17);
    let mut f1_17: uint64_t = e0_17;
    let mut g1_17: uint64_t = f0_17;
    let mut h12_17: uint64_t = g0_17;
    *hash.offset(0 as libc::c_uint as isize) = a1_17;
    *hash.offset(1 as libc::c_uint as isize) = b1_17;
    *hash.offset(2 as libc::c_uint as isize) = c1_17;
    *hash.offset(3 as libc::c_uint as isize) = d1_17;
    *hash.offset(4 as libc::c_uint as isize) = e1_17;
    *hash.offset(5 as libc::c_uint as isize) = f1_17;
    *hash.offset(6 as libc::c_uint as isize) = g1_17;
    *hash.offset(7 as libc::c_uint as isize) = h12_17;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_18: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_18: uint64_t = ws[i_1 as usize];
    let mut a0_18: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_18: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_18: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_18: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_18: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_18: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_18: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_18: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_18: uint64_t = k_t_18;
    let mut t1_18: uint64_t = h02_18
        .wrapping_add(
            (e0_18 << 50 as libc::c_uint | e0_18 >> 14 as libc::c_uint)
                ^ ((e0_18 << 46 as libc::c_uint | e0_18 >> 18 as libc::c_uint)
                    ^ (e0_18 << 23 as libc::c_uint | e0_18 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_18 & f0_18 ^ !e0_18 & g0_18)
        .wrapping_add(k_e_t_18)
        .wrapping_add(ws_t_18);
    let mut t2_34: uint64_t = ((a0_18 << 36 as libc::c_uint
        | a0_18 >> 28 as libc::c_uint)
        ^ ((a0_18 << 30 as libc::c_uint | a0_18 >> 34 as libc::c_uint)
            ^ (a0_18 << 25 as libc::c_uint | a0_18 >> 39 as libc::c_uint)))
        .wrapping_add(a0_18 & b0_18 ^ (a0_18 & c0_18 ^ b0_18 & c0_18));
    let mut a1_18: uint64_t = t1_18.wrapping_add(t2_34);
    let mut b1_18: uint64_t = a0_18;
    let mut c1_18: uint64_t = b0_18;
    let mut d1_18: uint64_t = c0_18;
    let mut e1_18: uint64_t = d0_18.wrapping_add(t1_18);
    let mut f1_18: uint64_t = e0_18;
    let mut g1_18: uint64_t = f0_18;
    let mut h12_18: uint64_t = g0_18;
    *hash.offset(0 as libc::c_uint as isize) = a1_18;
    *hash.offset(1 as libc::c_uint as isize) = b1_18;
    *hash.offset(2 as libc::c_uint as isize) = c1_18;
    *hash.offset(3 as libc::c_uint as isize) = d1_18;
    *hash.offset(4 as libc::c_uint as isize) = e1_18;
    *hash.offset(5 as libc::c_uint as isize) = f1_18;
    *hash.offset(6 as libc::c_uint as isize) = g1_18;
    *hash.offset(7 as libc::c_uint as isize) = h12_18;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_19: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_19: uint64_t = ws[i_1 as usize];
    let mut a0_19: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_19: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_19: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_19: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_19: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_19: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_19: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_19: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_19: uint64_t = k_t_19;
    let mut t1_19: uint64_t = h02_19
        .wrapping_add(
            (e0_19 << 50 as libc::c_uint | e0_19 >> 14 as libc::c_uint)
                ^ ((e0_19 << 46 as libc::c_uint | e0_19 >> 18 as libc::c_uint)
                    ^ (e0_19 << 23 as libc::c_uint | e0_19 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_19 & f0_19 ^ !e0_19 & g0_19)
        .wrapping_add(k_e_t_19)
        .wrapping_add(ws_t_19);
    let mut t2_35: uint64_t = ((a0_19 << 36 as libc::c_uint
        | a0_19 >> 28 as libc::c_uint)
        ^ ((a0_19 << 30 as libc::c_uint | a0_19 >> 34 as libc::c_uint)
            ^ (a0_19 << 25 as libc::c_uint | a0_19 >> 39 as libc::c_uint)))
        .wrapping_add(a0_19 & b0_19 ^ (a0_19 & c0_19 ^ b0_19 & c0_19));
    let mut a1_19: uint64_t = t1_19.wrapping_add(t2_35);
    let mut b1_19: uint64_t = a0_19;
    let mut c1_19: uint64_t = b0_19;
    let mut d1_19: uint64_t = c0_19;
    let mut e1_19: uint64_t = d0_19.wrapping_add(t1_19);
    let mut f1_19: uint64_t = e0_19;
    let mut g1_19: uint64_t = f0_19;
    let mut h12_19: uint64_t = g0_19;
    *hash.offset(0 as libc::c_uint as isize) = a1_19;
    *hash.offset(1 as libc::c_uint as isize) = b1_19;
    *hash.offset(2 as libc::c_uint as isize) = c1_19;
    *hash.offset(3 as libc::c_uint as isize) = d1_19;
    *hash.offset(4 as libc::c_uint as isize) = e1_19;
    *hash.offset(5 as libc::c_uint as isize) = f1_19;
    *hash.offset(6 as libc::c_uint as isize) = g1_19;
    *hash.offset(7 as libc::c_uint as isize) = h12_19;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_20: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_20: uint64_t = ws[i_1 as usize];
    let mut a0_20: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_20: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_20: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_20: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_20: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_20: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_20: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_20: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_20: uint64_t = k_t_20;
    let mut t1_20: uint64_t = h02_20
        .wrapping_add(
            (e0_20 << 50 as libc::c_uint | e0_20 >> 14 as libc::c_uint)
                ^ ((e0_20 << 46 as libc::c_uint | e0_20 >> 18 as libc::c_uint)
                    ^ (e0_20 << 23 as libc::c_uint | e0_20 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_20 & f0_20 ^ !e0_20 & g0_20)
        .wrapping_add(k_e_t_20)
        .wrapping_add(ws_t_20);
    let mut t2_36: uint64_t = ((a0_20 << 36 as libc::c_uint
        | a0_20 >> 28 as libc::c_uint)
        ^ ((a0_20 << 30 as libc::c_uint | a0_20 >> 34 as libc::c_uint)
            ^ (a0_20 << 25 as libc::c_uint | a0_20 >> 39 as libc::c_uint)))
        .wrapping_add(a0_20 & b0_20 ^ (a0_20 & c0_20 ^ b0_20 & c0_20));
    let mut a1_20: uint64_t = t1_20.wrapping_add(t2_36);
    let mut b1_20: uint64_t = a0_20;
    let mut c1_20: uint64_t = b0_20;
    let mut d1_20: uint64_t = c0_20;
    let mut e1_20: uint64_t = d0_20.wrapping_add(t1_20);
    let mut f1_20: uint64_t = e0_20;
    let mut g1_20: uint64_t = f0_20;
    let mut h12_20: uint64_t = g0_20;
    *hash.offset(0 as libc::c_uint as isize) = a1_20;
    *hash.offset(1 as libc::c_uint as isize) = b1_20;
    *hash.offset(2 as libc::c_uint as isize) = c1_20;
    *hash.offset(3 as libc::c_uint as isize) = d1_20;
    *hash.offset(4 as libc::c_uint as isize) = e1_20;
    *hash.offset(5 as libc::c_uint as isize) = f1_20;
    *hash.offset(6 as libc::c_uint as isize) = g1_20;
    *hash.offset(7 as libc::c_uint as isize) = h12_20;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_21: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_21: uint64_t = ws[i_1 as usize];
    let mut a0_21: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_21: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_21: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_21: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_21: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_21: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_21: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_21: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_21: uint64_t = k_t_21;
    let mut t1_21: uint64_t = h02_21
        .wrapping_add(
            (e0_21 << 50 as libc::c_uint | e0_21 >> 14 as libc::c_uint)
                ^ ((e0_21 << 46 as libc::c_uint | e0_21 >> 18 as libc::c_uint)
                    ^ (e0_21 << 23 as libc::c_uint | e0_21 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_21 & f0_21 ^ !e0_21 & g0_21)
        .wrapping_add(k_e_t_21)
        .wrapping_add(ws_t_21);
    let mut t2_37: uint64_t = ((a0_21 << 36 as libc::c_uint
        | a0_21 >> 28 as libc::c_uint)
        ^ ((a0_21 << 30 as libc::c_uint | a0_21 >> 34 as libc::c_uint)
            ^ (a0_21 << 25 as libc::c_uint | a0_21 >> 39 as libc::c_uint)))
        .wrapping_add(a0_21 & b0_21 ^ (a0_21 & c0_21 ^ b0_21 & c0_21));
    let mut a1_21: uint64_t = t1_21.wrapping_add(t2_37);
    let mut b1_21: uint64_t = a0_21;
    let mut c1_21: uint64_t = b0_21;
    let mut d1_21: uint64_t = c0_21;
    let mut e1_21: uint64_t = d0_21.wrapping_add(t1_21);
    let mut f1_21: uint64_t = e0_21;
    let mut g1_21: uint64_t = f0_21;
    let mut h12_21: uint64_t = g0_21;
    *hash.offset(0 as libc::c_uint as isize) = a1_21;
    *hash.offset(1 as libc::c_uint as isize) = b1_21;
    *hash.offset(2 as libc::c_uint as isize) = c1_21;
    *hash.offset(3 as libc::c_uint as isize) = d1_21;
    *hash.offset(4 as libc::c_uint as isize) = e1_21;
    *hash.offset(5 as libc::c_uint as isize) = f1_21;
    *hash.offset(6 as libc::c_uint as isize) = g1_21;
    *hash.offset(7 as libc::c_uint as isize) = h12_21;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_22: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_22: uint64_t = ws[i_1 as usize];
    let mut a0_22: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_22: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_22: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_22: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_22: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_22: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_22: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_22: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_22: uint64_t = k_t_22;
    let mut t1_22: uint64_t = h02_22
        .wrapping_add(
            (e0_22 << 50 as libc::c_uint | e0_22 >> 14 as libc::c_uint)
                ^ ((e0_22 << 46 as libc::c_uint | e0_22 >> 18 as libc::c_uint)
                    ^ (e0_22 << 23 as libc::c_uint | e0_22 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_22 & f0_22 ^ !e0_22 & g0_22)
        .wrapping_add(k_e_t_22)
        .wrapping_add(ws_t_22);
    let mut t2_38: uint64_t = ((a0_22 << 36 as libc::c_uint
        | a0_22 >> 28 as libc::c_uint)
        ^ ((a0_22 << 30 as libc::c_uint | a0_22 >> 34 as libc::c_uint)
            ^ (a0_22 << 25 as libc::c_uint | a0_22 >> 39 as libc::c_uint)))
        .wrapping_add(a0_22 & b0_22 ^ (a0_22 & c0_22 ^ b0_22 & c0_22));
    let mut a1_22: uint64_t = t1_22.wrapping_add(t2_38);
    let mut b1_22: uint64_t = a0_22;
    let mut c1_22: uint64_t = b0_22;
    let mut d1_22: uint64_t = c0_22;
    let mut e1_22: uint64_t = d0_22.wrapping_add(t1_22);
    let mut f1_22: uint64_t = e0_22;
    let mut g1_22: uint64_t = f0_22;
    let mut h12_22: uint64_t = g0_22;
    *hash.offset(0 as libc::c_uint as isize) = a1_22;
    *hash.offset(1 as libc::c_uint as isize) = b1_22;
    *hash.offset(2 as libc::c_uint as isize) = c1_22;
    *hash.offset(3 as libc::c_uint as isize) = d1_22;
    *hash.offset(4 as libc::c_uint as isize) = e1_22;
    *hash.offset(5 as libc::c_uint as isize) = f1_22;
    *hash.offset(6 as libc::c_uint as isize) = g1_22;
    *hash.offset(7 as libc::c_uint as isize) = h12_22;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_23: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_23: uint64_t = ws[i_1 as usize];
    let mut a0_23: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_23: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_23: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_23: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_23: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_23: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_23: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_23: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_23: uint64_t = k_t_23;
    let mut t1_23: uint64_t = h02_23
        .wrapping_add(
            (e0_23 << 50 as libc::c_uint | e0_23 >> 14 as libc::c_uint)
                ^ ((e0_23 << 46 as libc::c_uint | e0_23 >> 18 as libc::c_uint)
                    ^ (e0_23 << 23 as libc::c_uint | e0_23 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_23 & f0_23 ^ !e0_23 & g0_23)
        .wrapping_add(k_e_t_23)
        .wrapping_add(ws_t_23);
    let mut t2_39: uint64_t = ((a0_23 << 36 as libc::c_uint
        | a0_23 >> 28 as libc::c_uint)
        ^ ((a0_23 << 30 as libc::c_uint | a0_23 >> 34 as libc::c_uint)
            ^ (a0_23 << 25 as libc::c_uint | a0_23 >> 39 as libc::c_uint)))
        .wrapping_add(a0_23 & b0_23 ^ (a0_23 & c0_23 ^ b0_23 & c0_23));
    let mut a1_23: uint64_t = t1_23.wrapping_add(t2_39);
    let mut b1_23: uint64_t = a0_23;
    let mut c1_23: uint64_t = b0_23;
    let mut d1_23: uint64_t = c0_23;
    let mut e1_23: uint64_t = d0_23.wrapping_add(t1_23);
    let mut f1_23: uint64_t = e0_23;
    let mut g1_23: uint64_t = f0_23;
    let mut h12_23: uint64_t = g0_23;
    *hash.offset(0 as libc::c_uint as isize) = a1_23;
    *hash.offset(1 as libc::c_uint as isize) = b1_23;
    *hash.offset(2 as libc::c_uint as isize) = c1_23;
    *hash.offset(3 as libc::c_uint as isize) = d1_23;
    *hash.offset(4 as libc::c_uint as isize) = e1_23;
    *hash.offset(5 as libc::c_uint as isize) = f1_23;
    *hash.offset(6 as libc::c_uint as isize) = g1_23;
    *hash.offset(7 as libc::c_uint as isize) = h12_23;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_24: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_24: uint64_t = ws[i_1 as usize];
    let mut a0_24: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_24: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_24: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_24: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_24: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_24: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_24: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_24: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_24: uint64_t = k_t_24;
    let mut t1_24: uint64_t = h02_24
        .wrapping_add(
            (e0_24 << 50 as libc::c_uint | e0_24 >> 14 as libc::c_uint)
                ^ ((e0_24 << 46 as libc::c_uint | e0_24 >> 18 as libc::c_uint)
                    ^ (e0_24 << 23 as libc::c_uint | e0_24 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_24 & f0_24 ^ !e0_24 & g0_24)
        .wrapping_add(k_e_t_24)
        .wrapping_add(ws_t_24);
    let mut t2_40: uint64_t = ((a0_24 << 36 as libc::c_uint
        | a0_24 >> 28 as libc::c_uint)
        ^ ((a0_24 << 30 as libc::c_uint | a0_24 >> 34 as libc::c_uint)
            ^ (a0_24 << 25 as libc::c_uint | a0_24 >> 39 as libc::c_uint)))
        .wrapping_add(a0_24 & b0_24 ^ (a0_24 & c0_24 ^ b0_24 & c0_24));
    let mut a1_24: uint64_t = t1_24.wrapping_add(t2_40);
    let mut b1_24: uint64_t = a0_24;
    let mut c1_24: uint64_t = b0_24;
    let mut d1_24: uint64_t = c0_24;
    let mut e1_24: uint64_t = d0_24.wrapping_add(t1_24);
    let mut f1_24: uint64_t = e0_24;
    let mut g1_24: uint64_t = f0_24;
    let mut h12_24: uint64_t = g0_24;
    *hash.offset(0 as libc::c_uint as isize) = a1_24;
    *hash.offset(1 as libc::c_uint as isize) = b1_24;
    *hash.offset(2 as libc::c_uint as isize) = c1_24;
    *hash.offset(3 as libc::c_uint as isize) = d1_24;
    *hash.offset(4 as libc::c_uint as isize) = e1_24;
    *hash.offset(5 as libc::c_uint as isize) = f1_24;
    *hash.offset(6 as libc::c_uint as isize) = g1_24;
    *hash.offset(7 as libc::c_uint as isize) = h12_24;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_25: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_25: uint64_t = ws[i_1 as usize];
    let mut a0_25: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_25: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_25: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_25: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_25: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_25: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_25: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_25: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_25: uint64_t = k_t_25;
    let mut t1_25: uint64_t = h02_25
        .wrapping_add(
            (e0_25 << 50 as libc::c_uint | e0_25 >> 14 as libc::c_uint)
                ^ ((e0_25 << 46 as libc::c_uint | e0_25 >> 18 as libc::c_uint)
                    ^ (e0_25 << 23 as libc::c_uint | e0_25 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_25 & f0_25 ^ !e0_25 & g0_25)
        .wrapping_add(k_e_t_25)
        .wrapping_add(ws_t_25);
    let mut t2_41: uint64_t = ((a0_25 << 36 as libc::c_uint
        | a0_25 >> 28 as libc::c_uint)
        ^ ((a0_25 << 30 as libc::c_uint | a0_25 >> 34 as libc::c_uint)
            ^ (a0_25 << 25 as libc::c_uint | a0_25 >> 39 as libc::c_uint)))
        .wrapping_add(a0_25 & b0_25 ^ (a0_25 & c0_25 ^ b0_25 & c0_25));
    let mut a1_25: uint64_t = t1_25.wrapping_add(t2_41);
    let mut b1_25: uint64_t = a0_25;
    let mut c1_25: uint64_t = b0_25;
    let mut d1_25: uint64_t = c0_25;
    let mut e1_25: uint64_t = d0_25.wrapping_add(t1_25);
    let mut f1_25: uint64_t = e0_25;
    let mut g1_25: uint64_t = f0_25;
    let mut h12_25: uint64_t = g0_25;
    *hash.offset(0 as libc::c_uint as isize) = a1_25;
    *hash.offset(1 as libc::c_uint as isize) = b1_25;
    *hash.offset(2 as libc::c_uint as isize) = c1_25;
    *hash.offset(3 as libc::c_uint as isize) = d1_25;
    *hash.offset(4 as libc::c_uint as isize) = e1_25;
    *hash.offset(5 as libc::c_uint as isize) = f1_25;
    *hash.offset(6 as libc::c_uint as isize) = g1_25;
    *hash.offset(7 as libc::c_uint as isize) = h12_25;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_26: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_26: uint64_t = ws[i_1 as usize];
    let mut a0_26: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_26: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_26: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_26: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_26: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_26: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_26: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_26: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_26: uint64_t = k_t_26;
    let mut t1_26: uint64_t = h02_26
        .wrapping_add(
            (e0_26 << 50 as libc::c_uint | e0_26 >> 14 as libc::c_uint)
                ^ ((e0_26 << 46 as libc::c_uint | e0_26 >> 18 as libc::c_uint)
                    ^ (e0_26 << 23 as libc::c_uint | e0_26 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_26 & f0_26 ^ !e0_26 & g0_26)
        .wrapping_add(k_e_t_26)
        .wrapping_add(ws_t_26);
    let mut t2_42: uint64_t = ((a0_26 << 36 as libc::c_uint
        | a0_26 >> 28 as libc::c_uint)
        ^ ((a0_26 << 30 as libc::c_uint | a0_26 >> 34 as libc::c_uint)
            ^ (a0_26 << 25 as libc::c_uint | a0_26 >> 39 as libc::c_uint)))
        .wrapping_add(a0_26 & b0_26 ^ (a0_26 & c0_26 ^ b0_26 & c0_26));
    let mut a1_26: uint64_t = t1_26.wrapping_add(t2_42);
    let mut b1_26: uint64_t = a0_26;
    let mut c1_26: uint64_t = b0_26;
    let mut d1_26: uint64_t = c0_26;
    let mut e1_26: uint64_t = d0_26.wrapping_add(t1_26);
    let mut f1_26: uint64_t = e0_26;
    let mut g1_26: uint64_t = f0_26;
    let mut h12_26: uint64_t = g0_26;
    *hash.offset(0 as libc::c_uint as isize) = a1_26;
    *hash.offset(1 as libc::c_uint as isize) = b1_26;
    *hash.offset(2 as libc::c_uint as isize) = c1_26;
    *hash.offset(3 as libc::c_uint as isize) = d1_26;
    *hash.offset(4 as libc::c_uint as isize) = e1_26;
    *hash.offset(5 as libc::c_uint as isize) = f1_26;
    *hash.offset(6 as libc::c_uint as isize) = g1_26;
    *hash.offset(7 as libc::c_uint as isize) = h12_26;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_27: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_27: uint64_t = ws[i_1 as usize];
    let mut a0_27: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_27: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_27: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_27: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_27: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_27: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_27: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_27: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_27: uint64_t = k_t_27;
    let mut t1_27: uint64_t = h02_27
        .wrapping_add(
            (e0_27 << 50 as libc::c_uint | e0_27 >> 14 as libc::c_uint)
                ^ ((e0_27 << 46 as libc::c_uint | e0_27 >> 18 as libc::c_uint)
                    ^ (e0_27 << 23 as libc::c_uint | e0_27 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_27 & f0_27 ^ !e0_27 & g0_27)
        .wrapping_add(k_e_t_27)
        .wrapping_add(ws_t_27);
    let mut t2_43: uint64_t = ((a0_27 << 36 as libc::c_uint
        | a0_27 >> 28 as libc::c_uint)
        ^ ((a0_27 << 30 as libc::c_uint | a0_27 >> 34 as libc::c_uint)
            ^ (a0_27 << 25 as libc::c_uint | a0_27 >> 39 as libc::c_uint)))
        .wrapping_add(a0_27 & b0_27 ^ (a0_27 & c0_27 ^ b0_27 & c0_27));
    let mut a1_27: uint64_t = t1_27.wrapping_add(t2_43);
    let mut b1_27: uint64_t = a0_27;
    let mut c1_27: uint64_t = b0_27;
    let mut d1_27: uint64_t = c0_27;
    let mut e1_27: uint64_t = d0_27.wrapping_add(t1_27);
    let mut f1_27: uint64_t = e0_27;
    let mut g1_27: uint64_t = f0_27;
    let mut h12_27: uint64_t = g0_27;
    *hash.offset(0 as libc::c_uint as isize) = a1_27;
    *hash.offset(1 as libc::c_uint as isize) = b1_27;
    *hash.offset(2 as libc::c_uint as isize) = c1_27;
    *hash.offset(3 as libc::c_uint as isize) = d1_27;
    *hash.offset(4 as libc::c_uint as isize) = e1_27;
    *hash.offset(5 as libc::c_uint as isize) = f1_27;
    *hash.offset(6 as libc::c_uint as isize) = g1_27;
    *hash.offset(7 as libc::c_uint as isize) = h12_27;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_28: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_28: uint64_t = ws[i_1 as usize];
    let mut a0_28: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_28: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_28: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_28: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_28: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_28: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_28: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_28: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_28: uint64_t = k_t_28;
    let mut t1_28: uint64_t = h02_28
        .wrapping_add(
            (e0_28 << 50 as libc::c_uint | e0_28 >> 14 as libc::c_uint)
                ^ ((e0_28 << 46 as libc::c_uint | e0_28 >> 18 as libc::c_uint)
                    ^ (e0_28 << 23 as libc::c_uint | e0_28 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_28 & f0_28 ^ !e0_28 & g0_28)
        .wrapping_add(k_e_t_28)
        .wrapping_add(ws_t_28);
    let mut t2_44: uint64_t = ((a0_28 << 36 as libc::c_uint
        | a0_28 >> 28 as libc::c_uint)
        ^ ((a0_28 << 30 as libc::c_uint | a0_28 >> 34 as libc::c_uint)
            ^ (a0_28 << 25 as libc::c_uint | a0_28 >> 39 as libc::c_uint)))
        .wrapping_add(a0_28 & b0_28 ^ (a0_28 & c0_28 ^ b0_28 & c0_28));
    let mut a1_28: uint64_t = t1_28.wrapping_add(t2_44);
    let mut b1_28: uint64_t = a0_28;
    let mut c1_28: uint64_t = b0_28;
    let mut d1_28: uint64_t = c0_28;
    let mut e1_28: uint64_t = d0_28.wrapping_add(t1_28);
    let mut f1_28: uint64_t = e0_28;
    let mut g1_28: uint64_t = f0_28;
    let mut h12_28: uint64_t = g0_28;
    *hash.offset(0 as libc::c_uint as isize) = a1_28;
    *hash.offset(1 as libc::c_uint as isize) = b1_28;
    *hash.offset(2 as libc::c_uint as isize) = c1_28;
    *hash.offset(3 as libc::c_uint as isize) = d1_28;
    *hash.offset(4 as libc::c_uint as isize) = e1_28;
    *hash.offset(5 as libc::c_uint as isize) = f1_28;
    *hash.offset(6 as libc::c_uint as isize) = g1_28;
    *hash.offset(7 as libc::c_uint as isize) = h12_28;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_29: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_29: uint64_t = ws[i_1 as usize];
    let mut a0_29: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_29: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_29: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_29: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_29: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_29: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_29: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_29: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_29: uint64_t = k_t_29;
    let mut t1_29: uint64_t = h02_29
        .wrapping_add(
            (e0_29 << 50 as libc::c_uint | e0_29 >> 14 as libc::c_uint)
                ^ ((e0_29 << 46 as libc::c_uint | e0_29 >> 18 as libc::c_uint)
                    ^ (e0_29 << 23 as libc::c_uint | e0_29 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_29 & f0_29 ^ !e0_29 & g0_29)
        .wrapping_add(k_e_t_29)
        .wrapping_add(ws_t_29);
    let mut t2_45: uint64_t = ((a0_29 << 36 as libc::c_uint
        | a0_29 >> 28 as libc::c_uint)
        ^ ((a0_29 << 30 as libc::c_uint | a0_29 >> 34 as libc::c_uint)
            ^ (a0_29 << 25 as libc::c_uint | a0_29 >> 39 as libc::c_uint)))
        .wrapping_add(a0_29 & b0_29 ^ (a0_29 & c0_29 ^ b0_29 & c0_29));
    let mut a1_29: uint64_t = t1_29.wrapping_add(t2_45);
    let mut b1_29: uint64_t = a0_29;
    let mut c1_29: uint64_t = b0_29;
    let mut d1_29: uint64_t = c0_29;
    let mut e1_29: uint64_t = d0_29.wrapping_add(t1_29);
    let mut f1_29: uint64_t = e0_29;
    let mut g1_29: uint64_t = f0_29;
    let mut h12_29: uint64_t = g0_29;
    *hash.offset(0 as libc::c_uint as isize) = a1_29;
    *hash.offset(1 as libc::c_uint as isize) = b1_29;
    *hash.offset(2 as libc::c_uint as isize) = c1_29;
    *hash.offset(3 as libc::c_uint as isize) = d1_29;
    *hash.offset(4 as libc::c_uint as isize) = e1_29;
    *hash.offset(5 as libc::c_uint as isize) = f1_29;
    *hash.offset(6 as libc::c_uint as isize) = g1_29;
    *hash.offset(7 as libc::c_uint as isize) = h12_29;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_30: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_1) as usize];
    let mut ws_t_30: uint64_t = ws[i_1 as usize];
    let mut a0_30: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_30: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_30: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_30: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_30: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_30: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_30: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_30: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_30: uint64_t = k_t_30;
    let mut t1_30: uint64_t = h02_30
        .wrapping_add(
            (e0_30 << 50 as libc::c_uint | e0_30 >> 14 as libc::c_uint)
                ^ ((e0_30 << 46 as libc::c_uint | e0_30 >> 18 as libc::c_uint)
                    ^ (e0_30 << 23 as libc::c_uint | e0_30 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_30 & f0_30 ^ !e0_30 & g0_30)
        .wrapping_add(k_e_t_30)
        .wrapping_add(ws_t_30);
    let mut t2_46: uint64_t = ((a0_30 << 36 as libc::c_uint
        | a0_30 >> 28 as libc::c_uint)
        ^ ((a0_30 << 30 as libc::c_uint | a0_30 >> 34 as libc::c_uint)
            ^ (a0_30 << 25 as libc::c_uint | a0_30 >> 39 as libc::c_uint)))
        .wrapping_add(a0_30 & b0_30 ^ (a0_30 & c0_30 ^ b0_30 & c0_30));
    let mut a1_30: uint64_t = t1_30.wrapping_add(t2_46);
    let mut b1_30: uint64_t = a0_30;
    let mut c1_30: uint64_t = b0_30;
    let mut d1_30: uint64_t = c0_30;
    let mut e1_30: uint64_t = d0_30.wrapping_add(t1_30);
    let mut f1_30: uint64_t = e0_30;
    let mut g1_30: uint64_t = f0_30;
    let mut h12_30: uint64_t = g0_30;
    *hash.offset(0 as libc::c_uint as isize) = a1_30;
    *hash.offset(1 as libc::c_uint as isize) = b1_30;
    *hash.offset(2 as libc::c_uint as isize) = c1_30;
    *hash.offset(3 as libc::c_uint as isize) = d1_30;
    *hash.offset(4 as libc::c_uint as isize) = e1_30;
    *hash.offset(5 as libc::c_uint as isize) = f1_30;
    *hash.offset(6 as libc::c_uint as isize) = g1_30;
    *hash.offset(7 as libc::c_uint as isize) = h12_30;
    i_1 = (i_1 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 4 as libc::c_uint {
        let mut i_2: uint32_t = 0 as libc::c_uint;
        let mut t16_15: uint64_t = ws[i_2 as usize];
        let mut t15_15: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_15: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_47: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_15: uint64_t = (t2_47 << 45 as libc::c_uint
            | t2_47 >> 19 as libc::c_uint)
            ^ ((t2_47 << 3 as libc::c_uint | t2_47 >> 61 as libc::c_uint)
                ^ t2_47 >> 6 as libc::c_uint);
        let mut s0_15: uint64_t = (t15_15 << 63 as libc::c_uint
            | t15_15 >> 1 as libc::c_uint)
            ^ ((t15_15 << 56 as libc::c_uint | t15_15 >> 8 as libc::c_uint)
                ^ t15_15 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_15
            .wrapping_add(t7_15)
            .wrapping_add(s0_15)
            .wrapping_add(t16_15);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_16: uint64_t = ws[i_2 as usize];
        let mut t15_16: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_16: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_48: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_16: uint64_t = (t2_48 << 45 as libc::c_uint
            | t2_48 >> 19 as libc::c_uint)
            ^ ((t2_48 << 3 as libc::c_uint | t2_48 >> 61 as libc::c_uint)
                ^ t2_48 >> 6 as libc::c_uint);
        let mut s0_16: uint64_t = (t15_16 << 63 as libc::c_uint
            | t15_16 >> 1 as libc::c_uint)
            ^ ((t15_16 << 56 as libc::c_uint | t15_16 >> 8 as libc::c_uint)
                ^ t15_16 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_16
            .wrapping_add(t7_16)
            .wrapping_add(s0_16)
            .wrapping_add(t16_16);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_17: uint64_t = ws[i_2 as usize];
        let mut t15_17: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_17: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_49: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_17: uint64_t = (t2_49 << 45 as libc::c_uint
            | t2_49 >> 19 as libc::c_uint)
            ^ ((t2_49 << 3 as libc::c_uint | t2_49 >> 61 as libc::c_uint)
                ^ t2_49 >> 6 as libc::c_uint);
        let mut s0_17: uint64_t = (t15_17 << 63 as libc::c_uint
            | t15_17 >> 1 as libc::c_uint)
            ^ ((t15_17 << 56 as libc::c_uint | t15_17 >> 8 as libc::c_uint)
                ^ t15_17 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_17
            .wrapping_add(t7_17)
            .wrapping_add(s0_17)
            .wrapping_add(t16_17);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_18: uint64_t = ws[i_2 as usize];
        let mut t15_18: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_18: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_50: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_18: uint64_t = (t2_50 << 45 as libc::c_uint
            | t2_50 >> 19 as libc::c_uint)
            ^ ((t2_50 << 3 as libc::c_uint | t2_50 >> 61 as libc::c_uint)
                ^ t2_50 >> 6 as libc::c_uint);
        let mut s0_18: uint64_t = (t15_18 << 63 as libc::c_uint
            | t15_18 >> 1 as libc::c_uint)
            ^ ((t15_18 << 56 as libc::c_uint | t15_18 >> 8 as libc::c_uint)
                ^ t15_18 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_18
            .wrapping_add(t7_18)
            .wrapping_add(s0_18)
            .wrapping_add(t16_18);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_19: uint64_t = ws[i_2 as usize];
        let mut t15_19: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_19: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_51: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_19: uint64_t = (t2_51 << 45 as libc::c_uint
            | t2_51 >> 19 as libc::c_uint)
            ^ ((t2_51 << 3 as libc::c_uint | t2_51 >> 61 as libc::c_uint)
                ^ t2_51 >> 6 as libc::c_uint);
        let mut s0_19: uint64_t = (t15_19 << 63 as libc::c_uint
            | t15_19 >> 1 as libc::c_uint)
            ^ ((t15_19 << 56 as libc::c_uint | t15_19 >> 8 as libc::c_uint)
                ^ t15_19 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_19
            .wrapping_add(t7_19)
            .wrapping_add(s0_19)
            .wrapping_add(t16_19);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_20: uint64_t = ws[i_2 as usize];
        let mut t15_20: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_20: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_52: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_20: uint64_t = (t2_52 << 45 as libc::c_uint
            | t2_52 >> 19 as libc::c_uint)
            ^ ((t2_52 << 3 as libc::c_uint | t2_52 >> 61 as libc::c_uint)
                ^ t2_52 >> 6 as libc::c_uint);
        let mut s0_20: uint64_t = (t15_20 << 63 as libc::c_uint
            | t15_20 >> 1 as libc::c_uint)
            ^ ((t15_20 << 56 as libc::c_uint | t15_20 >> 8 as libc::c_uint)
                ^ t15_20 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_20
            .wrapping_add(t7_20)
            .wrapping_add(s0_20)
            .wrapping_add(t16_20);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_21: uint64_t = ws[i_2 as usize];
        let mut t15_21: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_21: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_53: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_21: uint64_t = (t2_53 << 45 as libc::c_uint
            | t2_53 >> 19 as libc::c_uint)
            ^ ((t2_53 << 3 as libc::c_uint | t2_53 >> 61 as libc::c_uint)
                ^ t2_53 >> 6 as libc::c_uint);
        let mut s0_21: uint64_t = (t15_21 << 63 as libc::c_uint
            | t15_21 >> 1 as libc::c_uint)
            ^ ((t15_21 << 56 as libc::c_uint | t15_21 >> 8 as libc::c_uint)
                ^ t15_21 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_21
            .wrapping_add(t7_21)
            .wrapping_add(s0_21)
            .wrapping_add(t16_21);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_22: uint64_t = ws[i_2 as usize];
        let mut t15_22: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_22: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_54: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_22: uint64_t = (t2_54 << 45 as libc::c_uint
            | t2_54 >> 19 as libc::c_uint)
            ^ ((t2_54 << 3 as libc::c_uint | t2_54 >> 61 as libc::c_uint)
                ^ t2_54 >> 6 as libc::c_uint);
        let mut s0_22: uint64_t = (t15_22 << 63 as libc::c_uint
            | t15_22 >> 1 as libc::c_uint)
            ^ ((t15_22 << 56 as libc::c_uint | t15_22 >> 8 as libc::c_uint)
                ^ t15_22 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_22
            .wrapping_add(t7_22)
            .wrapping_add(s0_22)
            .wrapping_add(t16_22);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_23: uint64_t = ws[i_2 as usize];
        let mut t15_23: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_23: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_55: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_23: uint64_t = (t2_55 << 45 as libc::c_uint
            | t2_55 >> 19 as libc::c_uint)
            ^ ((t2_55 << 3 as libc::c_uint | t2_55 >> 61 as libc::c_uint)
                ^ t2_55 >> 6 as libc::c_uint);
        let mut s0_23: uint64_t = (t15_23 << 63 as libc::c_uint
            | t15_23 >> 1 as libc::c_uint)
            ^ ((t15_23 << 56 as libc::c_uint | t15_23 >> 8 as libc::c_uint)
                ^ t15_23 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_23
            .wrapping_add(t7_23)
            .wrapping_add(s0_23)
            .wrapping_add(t16_23);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_24: uint64_t = ws[i_2 as usize];
        let mut t15_24: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_24: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_56: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_24: uint64_t = (t2_56 << 45 as libc::c_uint
            | t2_56 >> 19 as libc::c_uint)
            ^ ((t2_56 << 3 as libc::c_uint | t2_56 >> 61 as libc::c_uint)
                ^ t2_56 >> 6 as libc::c_uint);
        let mut s0_24: uint64_t = (t15_24 << 63 as libc::c_uint
            | t15_24 >> 1 as libc::c_uint)
            ^ ((t15_24 << 56 as libc::c_uint | t15_24 >> 8 as libc::c_uint)
                ^ t15_24 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_24
            .wrapping_add(t7_24)
            .wrapping_add(s0_24)
            .wrapping_add(t16_24);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_25: uint64_t = ws[i_2 as usize];
        let mut t15_25: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_25: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_57: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_25: uint64_t = (t2_57 << 45 as libc::c_uint
            | t2_57 >> 19 as libc::c_uint)
            ^ ((t2_57 << 3 as libc::c_uint | t2_57 >> 61 as libc::c_uint)
                ^ t2_57 >> 6 as libc::c_uint);
        let mut s0_25: uint64_t = (t15_25 << 63 as libc::c_uint
            | t15_25 >> 1 as libc::c_uint)
            ^ ((t15_25 << 56 as libc::c_uint | t15_25 >> 8 as libc::c_uint)
                ^ t15_25 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_25
            .wrapping_add(t7_25)
            .wrapping_add(s0_25)
            .wrapping_add(t16_25);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_26: uint64_t = ws[i_2 as usize];
        let mut t15_26: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_26: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_58: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_26: uint64_t = (t2_58 << 45 as libc::c_uint
            | t2_58 >> 19 as libc::c_uint)
            ^ ((t2_58 << 3 as libc::c_uint | t2_58 >> 61 as libc::c_uint)
                ^ t2_58 >> 6 as libc::c_uint);
        let mut s0_26: uint64_t = (t15_26 << 63 as libc::c_uint
            | t15_26 >> 1 as libc::c_uint)
            ^ ((t15_26 << 56 as libc::c_uint | t15_26 >> 8 as libc::c_uint)
                ^ t15_26 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_26
            .wrapping_add(t7_26)
            .wrapping_add(s0_26)
            .wrapping_add(t16_26);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_27: uint64_t = ws[i_2 as usize];
        let mut t15_27: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_27: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_59: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_27: uint64_t = (t2_59 << 45 as libc::c_uint
            | t2_59 >> 19 as libc::c_uint)
            ^ ((t2_59 << 3 as libc::c_uint | t2_59 >> 61 as libc::c_uint)
                ^ t2_59 >> 6 as libc::c_uint);
        let mut s0_27: uint64_t = (t15_27 << 63 as libc::c_uint
            | t15_27 >> 1 as libc::c_uint)
            ^ ((t15_27 << 56 as libc::c_uint | t15_27 >> 8 as libc::c_uint)
                ^ t15_27 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_27
            .wrapping_add(t7_27)
            .wrapping_add(s0_27)
            .wrapping_add(t16_27);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_28: uint64_t = ws[i_2 as usize];
        let mut t15_28: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_28: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_60: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_28: uint64_t = (t2_60 << 45 as libc::c_uint
            | t2_60 >> 19 as libc::c_uint)
            ^ ((t2_60 << 3 as libc::c_uint | t2_60 >> 61 as libc::c_uint)
                ^ t2_60 >> 6 as libc::c_uint);
        let mut s0_28: uint64_t = (t15_28 << 63 as libc::c_uint
            | t15_28 >> 1 as libc::c_uint)
            ^ ((t15_28 << 56 as libc::c_uint | t15_28 >> 8 as libc::c_uint)
                ^ t15_28 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_28
            .wrapping_add(t7_28)
            .wrapping_add(s0_28)
            .wrapping_add(t16_28);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_29: uint64_t = ws[i_2 as usize];
        let mut t15_29: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_29: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_61: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_29: uint64_t = (t2_61 << 45 as libc::c_uint
            | t2_61 >> 19 as libc::c_uint)
            ^ ((t2_61 << 3 as libc::c_uint | t2_61 >> 61 as libc::c_uint)
                ^ t2_61 >> 6 as libc::c_uint);
        let mut s0_29: uint64_t = (t15_29 << 63 as libc::c_uint
            | t15_29 >> 1 as libc::c_uint)
            ^ ((t15_29 << 56 as libc::c_uint | t15_29 >> 8 as libc::c_uint)
                ^ t15_29 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_29
            .wrapping_add(t7_29)
            .wrapping_add(s0_29)
            .wrapping_add(t16_29);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_30: uint64_t = ws[i_2 as usize];
        let mut t15_30: uint64_t = ws[i_2
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_30: uint64_t = ws[i_2
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_62: uint64_t = ws[i_2
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_30: uint64_t = (t2_62 << 45 as libc::c_uint
            | t2_62 >> 19 as libc::c_uint)
            ^ ((t2_62 << 3 as libc::c_uint | t2_62 >> 61 as libc::c_uint)
                ^ t2_62 >> 6 as libc::c_uint);
        let mut s0_30: uint64_t = (t15_30 << 63 as libc::c_uint
            | t15_30 >> 1 as libc::c_uint)
            ^ ((t15_30 << 56 as libc::c_uint | t15_30 >> 8 as libc::c_uint)
                ^ t15_30 >> 7 as libc::c_uint);
        ws[i_2
            as usize] = s1_30
            .wrapping_add(t7_30)
            .wrapping_add(s0_30)
            .wrapping_add(t16_30);
        i_2 = (i_2 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_3: uint32_t = 0 as libc::c_uint;
    let mut k_t_31: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_31: uint64_t = ws[i_3 as usize];
    let mut a0_31: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_31: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_31: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_31: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_31: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_31: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_31: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_31: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_31: uint64_t = k_t_31;
    let mut t1_31: uint64_t = h02_31
        .wrapping_add(
            (e0_31 << 50 as libc::c_uint | e0_31 >> 14 as libc::c_uint)
                ^ ((e0_31 << 46 as libc::c_uint | e0_31 >> 18 as libc::c_uint)
                    ^ (e0_31 << 23 as libc::c_uint | e0_31 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_31 & f0_31 ^ !e0_31 & g0_31)
        .wrapping_add(k_e_t_31)
        .wrapping_add(ws_t_31);
    let mut t2_63: uint64_t = ((a0_31 << 36 as libc::c_uint
        | a0_31 >> 28 as libc::c_uint)
        ^ ((a0_31 << 30 as libc::c_uint | a0_31 >> 34 as libc::c_uint)
            ^ (a0_31 << 25 as libc::c_uint | a0_31 >> 39 as libc::c_uint)))
        .wrapping_add(a0_31 & b0_31 ^ (a0_31 & c0_31 ^ b0_31 & c0_31));
    let mut a1_31: uint64_t = t1_31.wrapping_add(t2_63);
    let mut b1_31: uint64_t = a0_31;
    let mut c1_31: uint64_t = b0_31;
    let mut d1_31: uint64_t = c0_31;
    let mut e1_31: uint64_t = d0_31.wrapping_add(t1_31);
    let mut f1_31: uint64_t = e0_31;
    let mut g1_31: uint64_t = f0_31;
    let mut h12_31: uint64_t = g0_31;
    *hash.offset(0 as libc::c_uint as isize) = a1_31;
    *hash.offset(1 as libc::c_uint as isize) = b1_31;
    *hash.offset(2 as libc::c_uint as isize) = c1_31;
    *hash.offset(3 as libc::c_uint as isize) = d1_31;
    *hash.offset(4 as libc::c_uint as isize) = e1_31;
    *hash.offset(5 as libc::c_uint as isize) = f1_31;
    *hash.offset(6 as libc::c_uint as isize) = g1_31;
    *hash.offset(7 as libc::c_uint as isize) = h12_31;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_32: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_32: uint64_t = ws[i_3 as usize];
    let mut a0_32: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_32: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_32: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_32: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_32: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_32: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_32: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_32: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_32: uint64_t = k_t_32;
    let mut t1_32: uint64_t = h02_32
        .wrapping_add(
            (e0_32 << 50 as libc::c_uint | e0_32 >> 14 as libc::c_uint)
                ^ ((e0_32 << 46 as libc::c_uint | e0_32 >> 18 as libc::c_uint)
                    ^ (e0_32 << 23 as libc::c_uint | e0_32 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_32 & f0_32 ^ !e0_32 & g0_32)
        .wrapping_add(k_e_t_32)
        .wrapping_add(ws_t_32);
    let mut t2_64: uint64_t = ((a0_32 << 36 as libc::c_uint
        | a0_32 >> 28 as libc::c_uint)
        ^ ((a0_32 << 30 as libc::c_uint | a0_32 >> 34 as libc::c_uint)
            ^ (a0_32 << 25 as libc::c_uint | a0_32 >> 39 as libc::c_uint)))
        .wrapping_add(a0_32 & b0_32 ^ (a0_32 & c0_32 ^ b0_32 & c0_32));
    let mut a1_32: uint64_t = t1_32.wrapping_add(t2_64);
    let mut b1_32: uint64_t = a0_32;
    let mut c1_32: uint64_t = b0_32;
    let mut d1_32: uint64_t = c0_32;
    let mut e1_32: uint64_t = d0_32.wrapping_add(t1_32);
    let mut f1_32: uint64_t = e0_32;
    let mut g1_32: uint64_t = f0_32;
    let mut h12_32: uint64_t = g0_32;
    *hash.offset(0 as libc::c_uint as isize) = a1_32;
    *hash.offset(1 as libc::c_uint as isize) = b1_32;
    *hash.offset(2 as libc::c_uint as isize) = c1_32;
    *hash.offset(3 as libc::c_uint as isize) = d1_32;
    *hash.offset(4 as libc::c_uint as isize) = e1_32;
    *hash.offset(5 as libc::c_uint as isize) = f1_32;
    *hash.offset(6 as libc::c_uint as isize) = g1_32;
    *hash.offset(7 as libc::c_uint as isize) = h12_32;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_33: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_33: uint64_t = ws[i_3 as usize];
    let mut a0_33: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_33: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_33: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_33: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_33: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_33: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_33: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_33: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_33: uint64_t = k_t_33;
    let mut t1_33: uint64_t = h02_33
        .wrapping_add(
            (e0_33 << 50 as libc::c_uint | e0_33 >> 14 as libc::c_uint)
                ^ ((e0_33 << 46 as libc::c_uint | e0_33 >> 18 as libc::c_uint)
                    ^ (e0_33 << 23 as libc::c_uint | e0_33 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_33 & f0_33 ^ !e0_33 & g0_33)
        .wrapping_add(k_e_t_33)
        .wrapping_add(ws_t_33);
    let mut t2_65: uint64_t = ((a0_33 << 36 as libc::c_uint
        | a0_33 >> 28 as libc::c_uint)
        ^ ((a0_33 << 30 as libc::c_uint | a0_33 >> 34 as libc::c_uint)
            ^ (a0_33 << 25 as libc::c_uint | a0_33 >> 39 as libc::c_uint)))
        .wrapping_add(a0_33 & b0_33 ^ (a0_33 & c0_33 ^ b0_33 & c0_33));
    let mut a1_33: uint64_t = t1_33.wrapping_add(t2_65);
    let mut b1_33: uint64_t = a0_33;
    let mut c1_33: uint64_t = b0_33;
    let mut d1_33: uint64_t = c0_33;
    let mut e1_33: uint64_t = d0_33.wrapping_add(t1_33);
    let mut f1_33: uint64_t = e0_33;
    let mut g1_33: uint64_t = f0_33;
    let mut h12_33: uint64_t = g0_33;
    *hash.offset(0 as libc::c_uint as isize) = a1_33;
    *hash.offset(1 as libc::c_uint as isize) = b1_33;
    *hash.offset(2 as libc::c_uint as isize) = c1_33;
    *hash.offset(3 as libc::c_uint as isize) = d1_33;
    *hash.offset(4 as libc::c_uint as isize) = e1_33;
    *hash.offset(5 as libc::c_uint as isize) = f1_33;
    *hash.offset(6 as libc::c_uint as isize) = g1_33;
    *hash.offset(7 as libc::c_uint as isize) = h12_33;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_34: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_34: uint64_t = ws[i_3 as usize];
    let mut a0_34: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_34: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_34: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_34: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_34: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_34: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_34: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_34: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_34: uint64_t = k_t_34;
    let mut t1_34: uint64_t = h02_34
        .wrapping_add(
            (e0_34 << 50 as libc::c_uint | e0_34 >> 14 as libc::c_uint)
                ^ ((e0_34 << 46 as libc::c_uint | e0_34 >> 18 as libc::c_uint)
                    ^ (e0_34 << 23 as libc::c_uint | e0_34 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_34 & f0_34 ^ !e0_34 & g0_34)
        .wrapping_add(k_e_t_34)
        .wrapping_add(ws_t_34);
    let mut t2_66: uint64_t = ((a0_34 << 36 as libc::c_uint
        | a0_34 >> 28 as libc::c_uint)
        ^ ((a0_34 << 30 as libc::c_uint | a0_34 >> 34 as libc::c_uint)
            ^ (a0_34 << 25 as libc::c_uint | a0_34 >> 39 as libc::c_uint)))
        .wrapping_add(a0_34 & b0_34 ^ (a0_34 & c0_34 ^ b0_34 & c0_34));
    let mut a1_34: uint64_t = t1_34.wrapping_add(t2_66);
    let mut b1_34: uint64_t = a0_34;
    let mut c1_34: uint64_t = b0_34;
    let mut d1_34: uint64_t = c0_34;
    let mut e1_34: uint64_t = d0_34.wrapping_add(t1_34);
    let mut f1_34: uint64_t = e0_34;
    let mut g1_34: uint64_t = f0_34;
    let mut h12_34: uint64_t = g0_34;
    *hash.offset(0 as libc::c_uint as isize) = a1_34;
    *hash.offset(1 as libc::c_uint as isize) = b1_34;
    *hash.offset(2 as libc::c_uint as isize) = c1_34;
    *hash.offset(3 as libc::c_uint as isize) = d1_34;
    *hash.offset(4 as libc::c_uint as isize) = e1_34;
    *hash.offset(5 as libc::c_uint as isize) = f1_34;
    *hash.offset(6 as libc::c_uint as isize) = g1_34;
    *hash.offset(7 as libc::c_uint as isize) = h12_34;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_35: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_35: uint64_t = ws[i_3 as usize];
    let mut a0_35: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_35: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_35: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_35: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_35: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_35: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_35: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_35: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_35: uint64_t = k_t_35;
    let mut t1_35: uint64_t = h02_35
        .wrapping_add(
            (e0_35 << 50 as libc::c_uint | e0_35 >> 14 as libc::c_uint)
                ^ ((e0_35 << 46 as libc::c_uint | e0_35 >> 18 as libc::c_uint)
                    ^ (e0_35 << 23 as libc::c_uint | e0_35 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_35 & f0_35 ^ !e0_35 & g0_35)
        .wrapping_add(k_e_t_35)
        .wrapping_add(ws_t_35);
    let mut t2_67: uint64_t = ((a0_35 << 36 as libc::c_uint
        | a0_35 >> 28 as libc::c_uint)
        ^ ((a0_35 << 30 as libc::c_uint | a0_35 >> 34 as libc::c_uint)
            ^ (a0_35 << 25 as libc::c_uint | a0_35 >> 39 as libc::c_uint)))
        .wrapping_add(a0_35 & b0_35 ^ (a0_35 & c0_35 ^ b0_35 & c0_35));
    let mut a1_35: uint64_t = t1_35.wrapping_add(t2_67);
    let mut b1_35: uint64_t = a0_35;
    let mut c1_35: uint64_t = b0_35;
    let mut d1_35: uint64_t = c0_35;
    let mut e1_35: uint64_t = d0_35.wrapping_add(t1_35);
    let mut f1_35: uint64_t = e0_35;
    let mut g1_35: uint64_t = f0_35;
    let mut h12_35: uint64_t = g0_35;
    *hash.offset(0 as libc::c_uint as isize) = a1_35;
    *hash.offset(1 as libc::c_uint as isize) = b1_35;
    *hash.offset(2 as libc::c_uint as isize) = c1_35;
    *hash.offset(3 as libc::c_uint as isize) = d1_35;
    *hash.offset(4 as libc::c_uint as isize) = e1_35;
    *hash.offset(5 as libc::c_uint as isize) = f1_35;
    *hash.offset(6 as libc::c_uint as isize) = g1_35;
    *hash.offset(7 as libc::c_uint as isize) = h12_35;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_36: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_36: uint64_t = ws[i_3 as usize];
    let mut a0_36: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_36: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_36: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_36: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_36: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_36: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_36: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_36: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_36: uint64_t = k_t_36;
    let mut t1_36: uint64_t = h02_36
        .wrapping_add(
            (e0_36 << 50 as libc::c_uint | e0_36 >> 14 as libc::c_uint)
                ^ ((e0_36 << 46 as libc::c_uint | e0_36 >> 18 as libc::c_uint)
                    ^ (e0_36 << 23 as libc::c_uint | e0_36 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_36 & f0_36 ^ !e0_36 & g0_36)
        .wrapping_add(k_e_t_36)
        .wrapping_add(ws_t_36);
    let mut t2_68: uint64_t = ((a0_36 << 36 as libc::c_uint
        | a0_36 >> 28 as libc::c_uint)
        ^ ((a0_36 << 30 as libc::c_uint | a0_36 >> 34 as libc::c_uint)
            ^ (a0_36 << 25 as libc::c_uint | a0_36 >> 39 as libc::c_uint)))
        .wrapping_add(a0_36 & b0_36 ^ (a0_36 & c0_36 ^ b0_36 & c0_36));
    let mut a1_36: uint64_t = t1_36.wrapping_add(t2_68);
    let mut b1_36: uint64_t = a0_36;
    let mut c1_36: uint64_t = b0_36;
    let mut d1_36: uint64_t = c0_36;
    let mut e1_36: uint64_t = d0_36.wrapping_add(t1_36);
    let mut f1_36: uint64_t = e0_36;
    let mut g1_36: uint64_t = f0_36;
    let mut h12_36: uint64_t = g0_36;
    *hash.offset(0 as libc::c_uint as isize) = a1_36;
    *hash.offset(1 as libc::c_uint as isize) = b1_36;
    *hash.offset(2 as libc::c_uint as isize) = c1_36;
    *hash.offset(3 as libc::c_uint as isize) = d1_36;
    *hash.offset(4 as libc::c_uint as isize) = e1_36;
    *hash.offset(5 as libc::c_uint as isize) = f1_36;
    *hash.offset(6 as libc::c_uint as isize) = g1_36;
    *hash.offset(7 as libc::c_uint as isize) = h12_36;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_37: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_37: uint64_t = ws[i_3 as usize];
    let mut a0_37: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_37: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_37: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_37: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_37: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_37: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_37: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_37: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_37: uint64_t = k_t_37;
    let mut t1_37: uint64_t = h02_37
        .wrapping_add(
            (e0_37 << 50 as libc::c_uint | e0_37 >> 14 as libc::c_uint)
                ^ ((e0_37 << 46 as libc::c_uint | e0_37 >> 18 as libc::c_uint)
                    ^ (e0_37 << 23 as libc::c_uint | e0_37 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_37 & f0_37 ^ !e0_37 & g0_37)
        .wrapping_add(k_e_t_37)
        .wrapping_add(ws_t_37);
    let mut t2_69: uint64_t = ((a0_37 << 36 as libc::c_uint
        | a0_37 >> 28 as libc::c_uint)
        ^ ((a0_37 << 30 as libc::c_uint | a0_37 >> 34 as libc::c_uint)
            ^ (a0_37 << 25 as libc::c_uint | a0_37 >> 39 as libc::c_uint)))
        .wrapping_add(a0_37 & b0_37 ^ (a0_37 & c0_37 ^ b0_37 & c0_37));
    let mut a1_37: uint64_t = t1_37.wrapping_add(t2_69);
    let mut b1_37: uint64_t = a0_37;
    let mut c1_37: uint64_t = b0_37;
    let mut d1_37: uint64_t = c0_37;
    let mut e1_37: uint64_t = d0_37.wrapping_add(t1_37);
    let mut f1_37: uint64_t = e0_37;
    let mut g1_37: uint64_t = f0_37;
    let mut h12_37: uint64_t = g0_37;
    *hash.offset(0 as libc::c_uint as isize) = a1_37;
    *hash.offset(1 as libc::c_uint as isize) = b1_37;
    *hash.offset(2 as libc::c_uint as isize) = c1_37;
    *hash.offset(3 as libc::c_uint as isize) = d1_37;
    *hash.offset(4 as libc::c_uint as isize) = e1_37;
    *hash.offset(5 as libc::c_uint as isize) = f1_37;
    *hash.offset(6 as libc::c_uint as isize) = g1_37;
    *hash.offset(7 as libc::c_uint as isize) = h12_37;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_38: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_38: uint64_t = ws[i_3 as usize];
    let mut a0_38: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_38: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_38: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_38: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_38: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_38: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_38: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_38: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_38: uint64_t = k_t_38;
    let mut t1_38: uint64_t = h02_38
        .wrapping_add(
            (e0_38 << 50 as libc::c_uint | e0_38 >> 14 as libc::c_uint)
                ^ ((e0_38 << 46 as libc::c_uint | e0_38 >> 18 as libc::c_uint)
                    ^ (e0_38 << 23 as libc::c_uint | e0_38 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_38 & f0_38 ^ !e0_38 & g0_38)
        .wrapping_add(k_e_t_38)
        .wrapping_add(ws_t_38);
    let mut t2_70: uint64_t = ((a0_38 << 36 as libc::c_uint
        | a0_38 >> 28 as libc::c_uint)
        ^ ((a0_38 << 30 as libc::c_uint | a0_38 >> 34 as libc::c_uint)
            ^ (a0_38 << 25 as libc::c_uint | a0_38 >> 39 as libc::c_uint)))
        .wrapping_add(a0_38 & b0_38 ^ (a0_38 & c0_38 ^ b0_38 & c0_38));
    let mut a1_38: uint64_t = t1_38.wrapping_add(t2_70);
    let mut b1_38: uint64_t = a0_38;
    let mut c1_38: uint64_t = b0_38;
    let mut d1_38: uint64_t = c0_38;
    let mut e1_38: uint64_t = d0_38.wrapping_add(t1_38);
    let mut f1_38: uint64_t = e0_38;
    let mut g1_38: uint64_t = f0_38;
    let mut h12_38: uint64_t = g0_38;
    *hash.offset(0 as libc::c_uint as isize) = a1_38;
    *hash.offset(1 as libc::c_uint as isize) = b1_38;
    *hash.offset(2 as libc::c_uint as isize) = c1_38;
    *hash.offset(3 as libc::c_uint as isize) = d1_38;
    *hash.offset(4 as libc::c_uint as isize) = e1_38;
    *hash.offset(5 as libc::c_uint as isize) = f1_38;
    *hash.offset(6 as libc::c_uint as isize) = g1_38;
    *hash.offset(7 as libc::c_uint as isize) = h12_38;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_39: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_39: uint64_t = ws[i_3 as usize];
    let mut a0_39: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_39: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_39: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_39: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_39: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_39: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_39: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_39: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_39: uint64_t = k_t_39;
    let mut t1_39: uint64_t = h02_39
        .wrapping_add(
            (e0_39 << 50 as libc::c_uint | e0_39 >> 14 as libc::c_uint)
                ^ ((e0_39 << 46 as libc::c_uint | e0_39 >> 18 as libc::c_uint)
                    ^ (e0_39 << 23 as libc::c_uint | e0_39 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_39 & f0_39 ^ !e0_39 & g0_39)
        .wrapping_add(k_e_t_39)
        .wrapping_add(ws_t_39);
    let mut t2_71: uint64_t = ((a0_39 << 36 as libc::c_uint
        | a0_39 >> 28 as libc::c_uint)
        ^ ((a0_39 << 30 as libc::c_uint | a0_39 >> 34 as libc::c_uint)
            ^ (a0_39 << 25 as libc::c_uint | a0_39 >> 39 as libc::c_uint)))
        .wrapping_add(a0_39 & b0_39 ^ (a0_39 & c0_39 ^ b0_39 & c0_39));
    let mut a1_39: uint64_t = t1_39.wrapping_add(t2_71);
    let mut b1_39: uint64_t = a0_39;
    let mut c1_39: uint64_t = b0_39;
    let mut d1_39: uint64_t = c0_39;
    let mut e1_39: uint64_t = d0_39.wrapping_add(t1_39);
    let mut f1_39: uint64_t = e0_39;
    let mut g1_39: uint64_t = f0_39;
    let mut h12_39: uint64_t = g0_39;
    *hash.offset(0 as libc::c_uint as isize) = a1_39;
    *hash.offset(1 as libc::c_uint as isize) = b1_39;
    *hash.offset(2 as libc::c_uint as isize) = c1_39;
    *hash.offset(3 as libc::c_uint as isize) = d1_39;
    *hash.offset(4 as libc::c_uint as isize) = e1_39;
    *hash.offset(5 as libc::c_uint as isize) = f1_39;
    *hash.offset(6 as libc::c_uint as isize) = g1_39;
    *hash.offset(7 as libc::c_uint as isize) = h12_39;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_40: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_40: uint64_t = ws[i_3 as usize];
    let mut a0_40: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_40: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_40: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_40: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_40: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_40: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_40: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_40: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_40: uint64_t = k_t_40;
    let mut t1_40: uint64_t = h02_40
        .wrapping_add(
            (e0_40 << 50 as libc::c_uint | e0_40 >> 14 as libc::c_uint)
                ^ ((e0_40 << 46 as libc::c_uint | e0_40 >> 18 as libc::c_uint)
                    ^ (e0_40 << 23 as libc::c_uint | e0_40 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_40 & f0_40 ^ !e0_40 & g0_40)
        .wrapping_add(k_e_t_40)
        .wrapping_add(ws_t_40);
    let mut t2_72: uint64_t = ((a0_40 << 36 as libc::c_uint
        | a0_40 >> 28 as libc::c_uint)
        ^ ((a0_40 << 30 as libc::c_uint | a0_40 >> 34 as libc::c_uint)
            ^ (a0_40 << 25 as libc::c_uint | a0_40 >> 39 as libc::c_uint)))
        .wrapping_add(a0_40 & b0_40 ^ (a0_40 & c0_40 ^ b0_40 & c0_40));
    let mut a1_40: uint64_t = t1_40.wrapping_add(t2_72);
    let mut b1_40: uint64_t = a0_40;
    let mut c1_40: uint64_t = b0_40;
    let mut d1_40: uint64_t = c0_40;
    let mut e1_40: uint64_t = d0_40.wrapping_add(t1_40);
    let mut f1_40: uint64_t = e0_40;
    let mut g1_40: uint64_t = f0_40;
    let mut h12_40: uint64_t = g0_40;
    *hash.offset(0 as libc::c_uint as isize) = a1_40;
    *hash.offset(1 as libc::c_uint as isize) = b1_40;
    *hash.offset(2 as libc::c_uint as isize) = c1_40;
    *hash.offset(3 as libc::c_uint as isize) = d1_40;
    *hash.offset(4 as libc::c_uint as isize) = e1_40;
    *hash.offset(5 as libc::c_uint as isize) = f1_40;
    *hash.offset(6 as libc::c_uint as isize) = g1_40;
    *hash.offset(7 as libc::c_uint as isize) = h12_40;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_41: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_41: uint64_t = ws[i_3 as usize];
    let mut a0_41: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_41: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_41: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_41: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_41: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_41: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_41: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_41: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_41: uint64_t = k_t_41;
    let mut t1_41: uint64_t = h02_41
        .wrapping_add(
            (e0_41 << 50 as libc::c_uint | e0_41 >> 14 as libc::c_uint)
                ^ ((e0_41 << 46 as libc::c_uint | e0_41 >> 18 as libc::c_uint)
                    ^ (e0_41 << 23 as libc::c_uint | e0_41 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_41 & f0_41 ^ !e0_41 & g0_41)
        .wrapping_add(k_e_t_41)
        .wrapping_add(ws_t_41);
    let mut t2_73: uint64_t = ((a0_41 << 36 as libc::c_uint
        | a0_41 >> 28 as libc::c_uint)
        ^ ((a0_41 << 30 as libc::c_uint | a0_41 >> 34 as libc::c_uint)
            ^ (a0_41 << 25 as libc::c_uint | a0_41 >> 39 as libc::c_uint)))
        .wrapping_add(a0_41 & b0_41 ^ (a0_41 & c0_41 ^ b0_41 & c0_41));
    let mut a1_41: uint64_t = t1_41.wrapping_add(t2_73);
    let mut b1_41: uint64_t = a0_41;
    let mut c1_41: uint64_t = b0_41;
    let mut d1_41: uint64_t = c0_41;
    let mut e1_41: uint64_t = d0_41.wrapping_add(t1_41);
    let mut f1_41: uint64_t = e0_41;
    let mut g1_41: uint64_t = f0_41;
    let mut h12_41: uint64_t = g0_41;
    *hash.offset(0 as libc::c_uint as isize) = a1_41;
    *hash.offset(1 as libc::c_uint as isize) = b1_41;
    *hash.offset(2 as libc::c_uint as isize) = c1_41;
    *hash.offset(3 as libc::c_uint as isize) = d1_41;
    *hash.offset(4 as libc::c_uint as isize) = e1_41;
    *hash.offset(5 as libc::c_uint as isize) = f1_41;
    *hash.offset(6 as libc::c_uint as isize) = g1_41;
    *hash.offset(7 as libc::c_uint as isize) = h12_41;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_42: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_42: uint64_t = ws[i_3 as usize];
    let mut a0_42: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_42: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_42: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_42: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_42: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_42: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_42: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_42: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_42: uint64_t = k_t_42;
    let mut t1_42: uint64_t = h02_42
        .wrapping_add(
            (e0_42 << 50 as libc::c_uint | e0_42 >> 14 as libc::c_uint)
                ^ ((e0_42 << 46 as libc::c_uint | e0_42 >> 18 as libc::c_uint)
                    ^ (e0_42 << 23 as libc::c_uint | e0_42 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_42 & f0_42 ^ !e0_42 & g0_42)
        .wrapping_add(k_e_t_42)
        .wrapping_add(ws_t_42);
    let mut t2_74: uint64_t = ((a0_42 << 36 as libc::c_uint
        | a0_42 >> 28 as libc::c_uint)
        ^ ((a0_42 << 30 as libc::c_uint | a0_42 >> 34 as libc::c_uint)
            ^ (a0_42 << 25 as libc::c_uint | a0_42 >> 39 as libc::c_uint)))
        .wrapping_add(a0_42 & b0_42 ^ (a0_42 & c0_42 ^ b0_42 & c0_42));
    let mut a1_42: uint64_t = t1_42.wrapping_add(t2_74);
    let mut b1_42: uint64_t = a0_42;
    let mut c1_42: uint64_t = b0_42;
    let mut d1_42: uint64_t = c0_42;
    let mut e1_42: uint64_t = d0_42.wrapping_add(t1_42);
    let mut f1_42: uint64_t = e0_42;
    let mut g1_42: uint64_t = f0_42;
    let mut h12_42: uint64_t = g0_42;
    *hash.offset(0 as libc::c_uint as isize) = a1_42;
    *hash.offset(1 as libc::c_uint as isize) = b1_42;
    *hash.offset(2 as libc::c_uint as isize) = c1_42;
    *hash.offset(3 as libc::c_uint as isize) = d1_42;
    *hash.offset(4 as libc::c_uint as isize) = e1_42;
    *hash.offset(5 as libc::c_uint as isize) = f1_42;
    *hash.offset(6 as libc::c_uint as isize) = g1_42;
    *hash.offset(7 as libc::c_uint as isize) = h12_42;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_43: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_43: uint64_t = ws[i_3 as usize];
    let mut a0_43: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_43: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_43: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_43: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_43: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_43: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_43: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_43: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_43: uint64_t = k_t_43;
    let mut t1_43: uint64_t = h02_43
        .wrapping_add(
            (e0_43 << 50 as libc::c_uint | e0_43 >> 14 as libc::c_uint)
                ^ ((e0_43 << 46 as libc::c_uint | e0_43 >> 18 as libc::c_uint)
                    ^ (e0_43 << 23 as libc::c_uint | e0_43 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_43 & f0_43 ^ !e0_43 & g0_43)
        .wrapping_add(k_e_t_43)
        .wrapping_add(ws_t_43);
    let mut t2_75: uint64_t = ((a0_43 << 36 as libc::c_uint
        | a0_43 >> 28 as libc::c_uint)
        ^ ((a0_43 << 30 as libc::c_uint | a0_43 >> 34 as libc::c_uint)
            ^ (a0_43 << 25 as libc::c_uint | a0_43 >> 39 as libc::c_uint)))
        .wrapping_add(a0_43 & b0_43 ^ (a0_43 & c0_43 ^ b0_43 & c0_43));
    let mut a1_43: uint64_t = t1_43.wrapping_add(t2_75);
    let mut b1_43: uint64_t = a0_43;
    let mut c1_43: uint64_t = b0_43;
    let mut d1_43: uint64_t = c0_43;
    let mut e1_43: uint64_t = d0_43.wrapping_add(t1_43);
    let mut f1_43: uint64_t = e0_43;
    let mut g1_43: uint64_t = f0_43;
    let mut h12_43: uint64_t = g0_43;
    *hash.offset(0 as libc::c_uint as isize) = a1_43;
    *hash.offset(1 as libc::c_uint as isize) = b1_43;
    *hash.offset(2 as libc::c_uint as isize) = c1_43;
    *hash.offset(3 as libc::c_uint as isize) = d1_43;
    *hash.offset(4 as libc::c_uint as isize) = e1_43;
    *hash.offset(5 as libc::c_uint as isize) = f1_43;
    *hash.offset(6 as libc::c_uint as isize) = g1_43;
    *hash.offset(7 as libc::c_uint as isize) = h12_43;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_44: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_44: uint64_t = ws[i_3 as usize];
    let mut a0_44: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_44: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_44: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_44: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_44: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_44: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_44: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_44: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_44: uint64_t = k_t_44;
    let mut t1_44: uint64_t = h02_44
        .wrapping_add(
            (e0_44 << 50 as libc::c_uint | e0_44 >> 14 as libc::c_uint)
                ^ ((e0_44 << 46 as libc::c_uint | e0_44 >> 18 as libc::c_uint)
                    ^ (e0_44 << 23 as libc::c_uint | e0_44 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_44 & f0_44 ^ !e0_44 & g0_44)
        .wrapping_add(k_e_t_44)
        .wrapping_add(ws_t_44);
    let mut t2_76: uint64_t = ((a0_44 << 36 as libc::c_uint
        | a0_44 >> 28 as libc::c_uint)
        ^ ((a0_44 << 30 as libc::c_uint | a0_44 >> 34 as libc::c_uint)
            ^ (a0_44 << 25 as libc::c_uint | a0_44 >> 39 as libc::c_uint)))
        .wrapping_add(a0_44 & b0_44 ^ (a0_44 & c0_44 ^ b0_44 & c0_44));
    let mut a1_44: uint64_t = t1_44.wrapping_add(t2_76);
    let mut b1_44: uint64_t = a0_44;
    let mut c1_44: uint64_t = b0_44;
    let mut d1_44: uint64_t = c0_44;
    let mut e1_44: uint64_t = d0_44.wrapping_add(t1_44);
    let mut f1_44: uint64_t = e0_44;
    let mut g1_44: uint64_t = f0_44;
    let mut h12_44: uint64_t = g0_44;
    *hash.offset(0 as libc::c_uint as isize) = a1_44;
    *hash.offset(1 as libc::c_uint as isize) = b1_44;
    *hash.offset(2 as libc::c_uint as isize) = c1_44;
    *hash.offset(3 as libc::c_uint as isize) = d1_44;
    *hash.offset(4 as libc::c_uint as isize) = e1_44;
    *hash.offset(5 as libc::c_uint as isize) = f1_44;
    *hash.offset(6 as libc::c_uint as isize) = g1_44;
    *hash.offset(7 as libc::c_uint as isize) = h12_44;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_45: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_45: uint64_t = ws[i_3 as usize];
    let mut a0_45: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_45: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_45: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_45: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_45: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_45: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_45: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_45: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_45: uint64_t = k_t_45;
    let mut t1_45: uint64_t = h02_45
        .wrapping_add(
            (e0_45 << 50 as libc::c_uint | e0_45 >> 14 as libc::c_uint)
                ^ ((e0_45 << 46 as libc::c_uint | e0_45 >> 18 as libc::c_uint)
                    ^ (e0_45 << 23 as libc::c_uint | e0_45 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_45 & f0_45 ^ !e0_45 & g0_45)
        .wrapping_add(k_e_t_45)
        .wrapping_add(ws_t_45);
    let mut t2_77: uint64_t = ((a0_45 << 36 as libc::c_uint
        | a0_45 >> 28 as libc::c_uint)
        ^ ((a0_45 << 30 as libc::c_uint | a0_45 >> 34 as libc::c_uint)
            ^ (a0_45 << 25 as libc::c_uint | a0_45 >> 39 as libc::c_uint)))
        .wrapping_add(a0_45 & b0_45 ^ (a0_45 & c0_45 ^ b0_45 & c0_45));
    let mut a1_45: uint64_t = t1_45.wrapping_add(t2_77);
    let mut b1_45: uint64_t = a0_45;
    let mut c1_45: uint64_t = b0_45;
    let mut d1_45: uint64_t = c0_45;
    let mut e1_45: uint64_t = d0_45.wrapping_add(t1_45);
    let mut f1_45: uint64_t = e0_45;
    let mut g1_45: uint64_t = f0_45;
    let mut h12_45: uint64_t = g0_45;
    *hash.offset(0 as libc::c_uint as isize) = a1_45;
    *hash.offset(1 as libc::c_uint as isize) = b1_45;
    *hash.offset(2 as libc::c_uint as isize) = c1_45;
    *hash.offset(3 as libc::c_uint as isize) = d1_45;
    *hash.offset(4 as libc::c_uint as isize) = e1_45;
    *hash.offset(5 as libc::c_uint as isize) = f1_45;
    *hash.offset(6 as libc::c_uint as isize) = g1_45;
    *hash.offset(7 as libc::c_uint as isize) = h12_45;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_46: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_3) as usize];
    let mut ws_t_46: uint64_t = ws[i_3 as usize];
    let mut a0_46: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_46: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_46: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_46: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_46: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_46: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_46: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_46: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_46: uint64_t = k_t_46;
    let mut t1_46: uint64_t = h02_46
        .wrapping_add(
            (e0_46 << 50 as libc::c_uint | e0_46 >> 14 as libc::c_uint)
                ^ ((e0_46 << 46 as libc::c_uint | e0_46 >> 18 as libc::c_uint)
                    ^ (e0_46 << 23 as libc::c_uint | e0_46 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_46 & f0_46 ^ !e0_46 & g0_46)
        .wrapping_add(k_e_t_46)
        .wrapping_add(ws_t_46);
    let mut t2_78: uint64_t = ((a0_46 << 36 as libc::c_uint
        | a0_46 >> 28 as libc::c_uint)
        ^ ((a0_46 << 30 as libc::c_uint | a0_46 >> 34 as libc::c_uint)
            ^ (a0_46 << 25 as libc::c_uint | a0_46 >> 39 as libc::c_uint)))
        .wrapping_add(a0_46 & b0_46 ^ (a0_46 & c0_46 ^ b0_46 & c0_46));
    let mut a1_46: uint64_t = t1_46.wrapping_add(t2_78);
    let mut b1_46: uint64_t = a0_46;
    let mut c1_46: uint64_t = b0_46;
    let mut d1_46: uint64_t = c0_46;
    let mut e1_46: uint64_t = d0_46.wrapping_add(t1_46);
    let mut f1_46: uint64_t = e0_46;
    let mut g1_46: uint64_t = f0_46;
    let mut h12_46: uint64_t = g0_46;
    *hash.offset(0 as libc::c_uint as isize) = a1_46;
    *hash.offset(1 as libc::c_uint as isize) = b1_46;
    *hash.offset(2 as libc::c_uint as isize) = c1_46;
    *hash.offset(3 as libc::c_uint as isize) = d1_46;
    *hash.offset(4 as libc::c_uint as isize) = e1_46;
    *hash.offset(5 as libc::c_uint as isize) = f1_46;
    *hash.offset(6 as libc::c_uint as isize) = g1_46;
    *hash.offset(7 as libc::c_uint as isize) = h12_46;
    i_3 = (i_3 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 4 as libc::c_uint {
        let mut i_4: uint32_t = 0 as libc::c_uint;
        let mut t16_31: uint64_t = ws[i_4 as usize];
        let mut t15_31: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_31: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_79: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_31: uint64_t = (t2_79 << 45 as libc::c_uint
            | t2_79 >> 19 as libc::c_uint)
            ^ ((t2_79 << 3 as libc::c_uint | t2_79 >> 61 as libc::c_uint)
                ^ t2_79 >> 6 as libc::c_uint);
        let mut s0_31: uint64_t = (t15_31 << 63 as libc::c_uint
            | t15_31 >> 1 as libc::c_uint)
            ^ ((t15_31 << 56 as libc::c_uint | t15_31 >> 8 as libc::c_uint)
                ^ t15_31 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_31
            .wrapping_add(t7_31)
            .wrapping_add(s0_31)
            .wrapping_add(t16_31);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_32: uint64_t = ws[i_4 as usize];
        let mut t15_32: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_32: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_80: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_32: uint64_t = (t2_80 << 45 as libc::c_uint
            | t2_80 >> 19 as libc::c_uint)
            ^ ((t2_80 << 3 as libc::c_uint | t2_80 >> 61 as libc::c_uint)
                ^ t2_80 >> 6 as libc::c_uint);
        let mut s0_32: uint64_t = (t15_32 << 63 as libc::c_uint
            | t15_32 >> 1 as libc::c_uint)
            ^ ((t15_32 << 56 as libc::c_uint | t15_32 >> 8 as libc::c_uint)
                ^ t15_32 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_32
            .wrapping_add(t7_32)
            .wrapping_add(s0_32)
            .wrapping_add(t16_32);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_33: uint64_t = ws[i_4 as usize];
        let mut t15_33: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_33: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_81: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_33: uint64_t = (t2_81 << 45 as libc::c_uint
            | t2_81 >> 19 as libc::c_uint)
            ^ ((t2_81 << 3 as libc::c_uint | t2_81 >> 61 as libc::c_uint)
                ^ t2_81 >> 6 as libc::c_uint);
        let mut s0_33: uint64_t = (t15_33 << 63 as libc::c_uint
            | t15_33 >> 1 as libc::c_uint)
            ^ ((t15_33 << 56 as libc::c_uint | t15_33 >> 8 as libc::c_uint)
                ^ t15_33 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_33
            .wrapping_add(t7_33)
            .wrapping_add(s0_33)
            .wrapping_add(t16_33);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_34: uint64_t = ws[i_4 as usize];
        let mut t15_34: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_34: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_82: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_34: uint64_t = (t2_82 << 45 as libc::c_uint
            | t2_82 >> 19 as libc::c_uint)
            ^ ((t2_82 << 3 as libc::c_uint | t2_82 >> 61 as libc::c_uint)
                ^ t2_82 >> 6 as libc::c_uint);
        let mut s0_34: uint64_t = (t15_34 << 63 as libc::c_uint
            | t15_34 >> 1 as libc::c_uint)
            ^ ((t15_34 << 56 as libc::c_uint | t15_34 >> 8 as libc::c_uint)
                ^ t15_34 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_34
            .wrapping_add(t7_34)
            .wrapping_add(s0_34)
            .wrapping_add(t16_34);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_35: uint64_t = ws[i_4 as usize];
        let mut t15_35: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_35: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_83: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_35: uint64_t = (t2_83 << 45 as libc::c_uint
            | t2_83 >> 19 as libc::c_uint)
            ^ ((t2_83 << 3 as libc::c_uint | t2_83 >> 61 as libc::c_uint)
                ^ t2_83 >> 6 as libc::c_uint);
        let mut s0_35: uint64_t = (t15_35 << 63 as libc::c_uint
            | t15_35 >> 1 as libc::c_uint)
            ^ ((t15_35 << 56 as libc::c_uint | t15_35 >> 8 as libc::c_uint)
                ^ t15_35 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_35
            .wrapping_add(t7_35)
            .wrapping_add(s0_35)
            .wrapping_add(t16_35);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_36: uint64_t = ws[i_4 as usize];
        let mut t15_36: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_36: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_84: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_36: uint64_t = (t2_84 << 45 as libc::c_uint
            | t2_84 >> 19 as libc::c_uint)
            ^ ((t2_84 << 3 as libc::c_uint | t2_84 >> 61 as libc::c_uint)
                ^ t2_84 >> 6 as libc::c_uint);
        let mut s0_36: uint64_t = (t15_36 << 63 as libc::c_uint
            | t15_36 >> 1 as libc::c_uint)
            ^ ((t15_36 << 56 as libc::c_uint | t15_36 >> 8 as libc::c_uint)
                ^ t15_36 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_36
            .wrapping_add(t7_36)
            .wrapping_add(s0_36)
            .wrapping_add(t16_36);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_37: uint64_t = ws[i_4 as usize];
        let mut t15_37: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_37: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_85: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_37: uint64_t = (t2_85 << 45 as libc::c_uint
            | t2_85 >> 19 as libc::c_uint)
            ^ ((t2_85 << 3 as libc::c_uint | t2_85 >> 61 as libc::c_uint)
                ^ t2_85 >> 6 as libc::c_uint);
        let mut s0_37: uint64_t = (t15_37 << 63 as libc::c_uint
            | t15_37 >> 1 as libc::c_uint)
            ^ ((t15_37 << 56 as libc::c_uint | t15_37 >> 8 as libc::c_uint)
                ^ t15_37 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_37
            .wrapping_add(t7_37)
            .wrapping_add(s0_37)
            .wrapping_add(t16_37);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_38: uint64_t = ws[i_4 as usize];
        let mut t15_38: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_38: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_86: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_38: uint64_t = (t2_86 << 45 as libc::c_uint
            | t2_86 >> 19 as libc::c_uint)
            ^ ((t2_86 << 3 as libc::c_uint | t2_86 >> 61 as libc::c_uint)
                ^ t2_86 >> 6 as libc::c_uint);
        let mut s0_38: uint64_t = (t15_38 << 63 as libc::c_uint
            | t15_38 >> 1 as libc::c_uint)
            ^ ((t15_38 << 56 as libc::c_uint | t15_38 >> 8 as libc::c_uint)
                ^ t15_38 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_38
            .wrapping_add(t7_38)
            .wrapping_add(s0_38)
            .wrapping_add(t16_38);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_39: uint64_t = ws[i_4 as usize];
        let mut t15_39: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_39: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_87: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_39: uint64_t = (t2_87 << 45 as libc::c_uint
            | t2_87 >> 19 as libc::c_uint)
            ^ ((t2_87 << 3 as libc::c_uint | t2_87 >> 61 as libc::c_uint)
                ^ t2_87 >> 6 as libc::c_uint);
        let mut s0_39: uint64_t = (t15_39 << 63 as libc::c_uint
            | t15_39 >> 1 as libc::c_uint)
            ^ ((t15_39 << 56 as libc::c_uint | t15_39 >> 8 as libc::c_uint)
                ^ t15_39 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_39
            .wrapping_add(t7_39)
            .wrapping_add(s0_39)
            .wrapping_add(t16_39);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_40: uint64_t = ws[i_4 as usize];
        let mut t15_40: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_40: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_88: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_40: uint64_t = (t2_88 << 45 as libc::c_uint
            | t2_88 >> 19 as libc::c_uint)
            ^ ((t2_88 << 3 as libc::c_uint | t2_88 >> 61 as libc::c_uint)
                ^ t2_88 >> 6 as libc::c_uint);
        let mut s0_40: uint64_t = (t15_40 << 63 as libc::c_uint
            | t15_40 >> 1 as libc::c_uint)
            ^ ((t15_40 << 56 as libc::c_uint | t15_40 >> 8 as libc::c_uint)
                ^ t15_40 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_40
            .wrapping_add(t7_40)
            .wrapping_add(s0_40)
            .wrapping_add(t16_40);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_41: uint64_t = ws[i_4 as usize];
        let mut t15_41: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_41: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_89: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_41: uint64_t = (t2_89 << 45 as libc::c_uint
            | t2_89 >> 19 as libc::c_uint)
            ^ ((t2_89 << 3 as libc::c_uint | t2_89 >> 61 as libc::c_uint)
                ^ t2_89 >> 6 as libc::c_uint);
        let mut s0_41: uint64_t = (t15_41 << 63 as libc::c_uint
            | t15_41 >> 1 as libc::c_uint)
            ^ ((t15_41 << 56 as libc::c_uint | t15_41 >> 8 as libc::c_uint)
                ^ t15_41 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_41
            .wrapping_add(t7_41)
            .wrapping_add(s0_41)
            .wrapping_add(t16_41);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_42: uint64_t = ws[i_4 as usize];
        let mut t15_42: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_42: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_90: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_42: uint64_t = (t2_90 << 45 as libc::c_uint
            | t2_90 >> 19 as libc::c_uint)
            ^ ((t2_90 << 3 as libc::c_uint | t2_90 >> 61 as libc::c_uint)
                ^ t2_90 >> 6 as libc::c_uint);
        let mut s0_42: uint64_t = (t15_42 << 63 as libc::c_uint
            | t15_42 >> 1 as libc::c_uint)
            ^ ((t15_42 << 56 as libc::c_uint | t15_42 >> 8 as libc::c_uint)
                ^ t15_42 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_42
            .wrapping_add(t7_42)
            .wrapping_add(s0_42)
            .wrapping_add(t16_42);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_43: uint64_t = ws[i_4 as usize];
        let mut t15_43: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_43: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_91: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_43: uint64_t = (t2_91 << 45 as libc::c_uint
            | t2_91 >> 19 as libc::c_uint)
            ^ ((t2_91 << 3 as libc::c_uint | t2_91 >> 61 as libc::c_uint)
                ^ t2_91 >> 6 as libc::c_uint);
        let mut s0_43: uint64_t = (t15_43 << 63 as libc::c_uint
            | t15_43 >> 1 as libc::c_uint)
            ^ ((t15_43 << 56 as libc::c_uint | t15_43 >> 8 as libc::c_uint)
                ^ t15_43 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_43
            .wrapping_add(t7_43)
            .wrapping_add(s0_43)
            .wrapping_add(t16_43);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_44: uint64_t = ws[i_4 as usize];
        let mut t15_44: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_44: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_92: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_44: uint64_t = (t2_92 << 45 as libc::c_uint
            | t2_92 >> 19 as libc::c_uint)
            ^ ((t2_92 << 3 as libc::c_uint | t2_92 >> 61 as libc::c_uint)
                ^ t2_92 >> 6 as libc::c_uint);
        let mut s0_44: uint64_t = (t15_44 << 63 as libc::c_uint
            | t15_44 >> 1 as libc::c_uint)
            ^ ((t15_44 << 56 as libc::c_uint | t15_44 >> 8 as libc::c_uint)
                ^ t15_44 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_44
            .wrapping_add(t7_44)
            .wrapping_add(s0_44)
            .wrapping_add(t16_44);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_45: uint64_t = ws[i_4 as usize];
        let mut t15_45: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_45: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_93: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_45: uint64_t = (t2_93 << 45 as libc::c_uint
            | t2_93 >> 19 as libc::c_uint)
            ^ ((t2_93 << 3 as libc::c_uint | t2_93 >> 61 as libc::c_uint)
                ^ t2_93 >> 6 as libc::c_uint);
        let mut s0_45: uint64_t = (t15_45 << 63 as libc::c_uint
            | t15_45 >> 1 as libc::c_uint)
            ^ ((t15_45 << 56 as libc::c_uint | t15_45 >> 8 as libc::c_uint)
                ^ t15_45 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_45
            .wrapping_add(t7_45)
            .wrapping_add(s0_45)
            .wrapping_add(t16_45);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_46: uint64_t = ws[i_4 as usize];
        let mut t15_46: uint64_t = ws[i_4
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_46: uint64_t = ws[i_4
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_94: uint64_t = ws[i_4
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_46: uint64_t = (t2_94 << 45 as libc::c_uint
            | t2_94 >> 19 as libc::c_uint)
            ^ ((t2_94 << 3 as libc::c_uint | t2_94 >> 61 as libc::c_uint)
                ^ t2_94 >> 6 as libc::c_uint);
        let mut s0_46: uint64_t = (t15_46 << 63 as libc::c_uint
            | t15_46 >> 1 as libc::c_uint)
            ^ ((t15_46 << 56 as libc::c_uint | t15_46 >> 8 as libc::c_uint)
                ^ t15_46 >> 7 as libc::c_uint);
        ws[i_4
            as usize] = s1_46
            .wrapping_add(t7_46)
            .wrapping_add(s0_46)
            .wrapping_add(t16_46);
        i_4 = (i_4 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_5: uint32_t = 0 as libc::c_uint;
    let mut k_t_47: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_47: uint64_t = ws[i_5 as usize];
    let mut a0_47: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_47: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_47: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_47: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_47: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_47: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_47: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_47: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_47: uint64_t = k_t_47;
    let mut t1_47: uint64_t = h02_47
        .wrapping_add(
            (e0_47 << 50 as libc::c_uint | e0_47 >> 14 as libc::c_uint)
                ^ ((e0_47 << 46 as libc::c_uint | e0_47 >> 18 as libc::c_uint)
                    ^ (e0_47 << 23 as libc::c_uint | e0_47 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_47 & f0_47 ^ !e0_47 & g0_47)
        .wrapping_add(k_e_t_47)
        .wrapping_add(ws_t_47);
    let mut t2_95: uint64_t = ((a0_47 << 36 as libc::c_uint
        | a0_47 >> 28 as libc::c_uint)
        ^ ((a0_47 << 30 as libc::c_uint | a0_47 >> 34 as libc::c_uint)
            ^ (a0_47 << 25 as libc::c_uint | a0_47 >> 39 as libc::c_uint)))
        .wrapping_add(a0_47 & b0_47 ^ (a0_47 & c0_47 ^ b0_47 & c0_47));
    let mut a1_47: uint64_t = t1_47.wrapping_add(t2_95);
    let mut b1_47: uint64_t = a0_47;
    let mut c1_47: uint64_t = b0_47;
    let mut d1_47: uint64_t = c0_47;
    let mut e1_47: uint64_t = d0_47.wrapping_add(t1_47);
    let mut f1_47: uint64_t = e0_47;
    let mut g1_47: uint64_t = f0_47;
    let mut h12_47: uint64_t = g0_47;
    *hash.offset(0 as libc::c_uint as isize) = a1_47;
    *hash.offset(1 as libc::c_uint as isize) = b1_47;
    *hash.offset(2 as libc::c_uint as isize) = c1_47;
    *hash.offset(3 as libc::c_uint as isize) = d1_47;
    *hash.offset(4 as libc::c_uint as isize) = e1_47;
    *hash.offset(5 as libc::c_uint as isize) = f1_47;
    *hash.offset(6 as libc::c_uint as isize) = g1_47;
    *hash.offset(7 as libc::c_uint as isize) = h12_47;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_48: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_48: uint64_t = ws[i_5 as usize];
    let mut a0_48: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_48: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_48: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_48: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_48: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_48: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_48: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_48: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_48: uint64_t = k_t_48;
    let mut t1_48: uint64_t = h02_48
        .wrapping_add(
            (e0_48 << 50 as libc::c_uint | e0_48 >> 14 as libc::c_uint)
                ^ ((e0_48 << 46 as libc::c_uint | e0_48 >> 18 as libc::c_uint)
                    ^ (e0_48 << 23 as libc::c_uint | e0_48 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_48 & f0_48 ^ !e0_48 & g0_48)
        .wrapping_add(k_e_t_48)
        .wrapping_add(ws_t_48);
    let mut t2_96: uint64_t = ((a0_48 << 36 as libc::c_uint
        | a0_48 >> 28 as libc::c_uint)
        ^ ((a0_48 << 30 as libc::c_uint | a0_48 >> 34 as libc::c_uint)
            ^ (a0_48 << 25 as libc::c_uint | a0_48 >> 39 as libc::c_uint)))
        .wrapping_add(a0_48 & b0_48 ^ (a0_48 & c0_48 ^ b0_48 & c0_48));
    let mut a1_48: uint64_t = t1_48.wrapping_add(t2_96);
    let mut b1_48: uint64_t = a0_48;
    let mut c1_48: uint64_t = b0_48;
    let mut d1_48: uint64_t = c0_48;
    let mut e1_48: uint64_t = d0_48.wrapping_add(t1_48);
    let mut f1_48: uint64_t = e0_48;
    let mut g1_48: uint64_t = f0_48;
    let mut h12_48: uint64_t = g0_48;
    *hash.offset(0 as libc::c_uint as isize) = a1_48;
    *hash.offset(1 as libc::c_uint as isize) = b1_48;
    *hash.offset(2 as libc::c_uint as isize) = c1_48;
    *hash.offset(3 as libc::c_uint as isize) = d1_48;
    *hash.offset(4 as libc::c_uint as isize) = e1_48;
    *hash.offset(5 as libc::c_uint as isize) = f1_48;
    *hash.offset(6 as libc::c_uint as isize) = g1_48;
    *hash.offset(7 as libc::c_uint as isize) = h12_48;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_49: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_49: uint64_t = ws[i_5 as usize];
    let mut a0_49: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_49: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_49: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_49: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_49: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_49: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_49: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_49: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_49: uint64_t = k_t_49;
    let mut t1_49: uint64_t = h02_49
        .wrapping_add(
            (e0_49 << 50 as libc::c_uint | e0_49 >> 14 as libc::c_uint)
                ^ ((e0_49 << 46 as libc::c_uint | e0_49 >> 18 as libc::c_uint)
                    ^ (e0_49 << 23 as libc::c_uint | e0_49 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_49 & f0_49 ^ !e0_49 & g0_49)
        .wrapping_add(k_e_t_49)
        .wrapping_add(ws_t_49);
    let mut t2_97: uint64_t = ((a0_49 << 36 as libc::c_uint
        | a0_49 >> 28 as libc::c_uint)
        ^ ((a0_49 << 30 as libc::c_uint | a0_49 >> 34 as libc::c_uint)
            ^ (a0_49 << 25 as libc::c_uint | a0_49 >> 39 as libc::c_uint)))
        .wrapping_add(a0_49 & b0_49 ^ (a0_49 & c0_49 ^ b0_49 & c0_49));
    let mut a1_49: uint64_t = t1_49.wrapping_add(t2_97);
    let mut b1_49: uint64_t = a0_49;
    let mut c1_49: uint64_t = b0_49;
    let mut d1_49: uint64_t = c0_49;
    let mut e1_49: uint64_t = d0_49.wrapping_add(t1_49);
    let mut f1_49: uint64_t = e0_49;
    let mut g1_49: uint64_t = f0_49;
    let mut h12_49: uint64_t = g0_49;
    *hash.offset(0 as libc::c_uint as isize) = a1_49;
    *hash.offset(1 as libc::c_uint as isize) = b1_49;
    *hash.offset(2 as libc::c_uint as isize) = c1_49;
    *hash.offset(3 as libc::c_uint as isize) = d1_49;
    *hash.offset(4 as libc::c_uint as isize) = e1_49;
    *hash.offset(5 as libc::c_uint as isize) = f1_49;
    *hash.offset(6 as libc::c_uint as isize) = g1_49;
    *hash.offset(7 as libc::c_uint as isize) = h12_49;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_50: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_50: uint64_t = ws[i_5 as usize];
    let mut a0_50: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_50: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_50: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_50: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_50: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_50: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_50: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_50: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_50: uint64_t = k_t_50;
    let mut t1_50: uint64_t = h02_50
        .wrapping_add(
            (e0_50 << 50 as libc::c_uint | e0_50 >> 14 as libc::c_uint)
                ^ ((e0_50 << 46 as libc::c_uint | e0_50 >> 18 as libc::c_uint)
                    ^ (e0_50 << 23 as libc::c_uint | e0_50 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_50 & f0_50 ^ !e0_50 & g0_50)
        .wrapping_add(k_e_t_50)
        .wrapping_add(ws_t_50);
    let mut t2_98: uint64_t = ((a0_50 << 36 as libc::c_uint
        | a0_50 >> 28 as libc::c_uint)
        ^ ((a0_50 << 30 as libc::c_uint | a0_50 >> 34 as libc::c_uint)
            ^ (a0_50 << 25 as libc::c_uint | a0_50 >> 39 as libc::c_uint)))
        .wrapping_add(a0_50 & b0_50 ^ (a0_50 & c0_50 ^ b0_50 & c0_50));
    let mut a1_50: uint64_t = t1_50.wrapping_add(t2_98);
    let mut b1_50: uint64_t = a0_50;
    let mut c1_50: uint64_t = b0_50;
    let mut d1_50: uint64_t = c0_50;
    let mut e1_50: uint64_t = d0_50.wrapping_add(t1_50);
    let mut f1_50: uint64_t = e0_50;
    let mut g1_50: uint64_t = f0_50;
    let mut h12_50: uint64_t = g0_50;
    *hash.offset(0 as libc::c_uint as isize) = a1_50;
    *hash.offset(1 as libc::c_uint as isize) = b1_50;
    *hash.offset(2 as libc::c_uint as isize) = c1_50;
    *hash.offset(3 as libc::c_uint as isize) = d1_50;
    *hash.offset(4 as libc::c_uint as isize) = e1_50;
    *hash.offset(5 as libc::c_uint as isize) = f1_50;
    *hash.offset(6 as libc::c_uint as isize) = g1_50;
    *hash.offset(7 as libc::c_uint as isize) = h12_50;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_51: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_51: uint64_t = ws[i_5 as usize];
    let mut a0_51: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_51: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_51: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_51: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_51: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_51: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_51: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_51: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_51: uint64_t = k_t_51;
    let mut t1_51: uint64_t = h02_51
        .wrapping_add(
            (e0_51 << 50 as libc::c_uint | e0_51 >> 14 as libc::c_uint)
                ^ ((e0_51 << 46 as libc::c_uint | e0_51 >> 18 as libc::c_uint)
                    ^ (e0_51 << 23 as libc::c_uint | e0_51 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_51 & f0_51 ^ !e0_51 & g0_51)
        .wrapping_add(k_e_t_51)
        .wrapping_add(ws_t_51);
    let mut t2_99: uint64_t = ((a0_51 << 36 as libc::c_uint
        | a0_51 >> 28 as libc::c_uint)
        ^ ((a0_51 << 30 as libc::c_uint | a0_51 >> 34 as libc::c_uint)
            ^ (a0_51 << 25 as libc::c_uint | a0_51 >> 39 as libc::c_uint)))
        .wrapping_add(a0_51 & b0_51 ^ (a0_51 & c0_51 ^ b0_51 & c0_51));
    let mut a1_51: uint64_t = t1_51.wrapping_add(t2_99);
    let mut b1_51: uint64_t = a0_51;
    let mut c1_51: uint64_t = b0_51;
    let mut d1_51: uint64_t = c0_51;
    let mut e1_51: uint64_t = d0_51.wrapping_add(t1_51);
    let mut f1_51: uint64_t = e0_51;
    let mut g1_51: uint64_t = f0_51;
    let mut h12_51: uint64_t = g0_51;
    *hash.offset(0 as libc::c_uint as isize) = a1_51;
    *hash.offset(1 as libc::c_uint as isize) = b1_51;
    *hash.offset(2 as libc::c_uint as isize) = c1_51;
    *hash.offset(3 as libc::c_uint as isize) = d1_51;
    *hash.offset(4 as libc::c_uint as isize) = e1_51;
    *hash.offset(5 as libc::c_uint as isize) = f1_51;
    *hash.offset(6 as libc::c_uint as isize) = g1_51;
    *hash.offset(7 as libc::c_uint as isize) = h12_51;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_52: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_52: uint64_t = ws[i_5 as usize];
    let mut a0_52: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_52: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_52: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_52: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_52: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_52: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_52: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_52: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_52: uint64_t = k_t_52;
    let mut t1_52: uint64_t = h02_52
        .wrapping_add(
            (e0_52 << 50 as libc::c_uint | e0_52 >> 14 as libc::c_uint)
                ^ ((e0_52 << 46 as libc::c_uint | e0_52 >> 18 as libc::c_uint)
                    ^ (e0_52 << 23 as libc::c_uint | e0_52 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_52 & f0_52 ^ !e0_52 & g0_52)
        .wrapping_add(k_e_t_52)
        .wrapping_add(ws_t_52);
    let mut t2_100: uint64_t = ((a0_52 << 36 as libc::c_uint
        | a0_52 >> 28 as libc::c_uint)
        ^ ((a0_52 << 30 as libc::c_uint | a0_52 >> 34 as libc::c_uint)
            ^ (a0_52 << 25 as libc::c_uint | a0_52 >> 39 as libc::c_uint)))
        .wrapping_add(a0_52 & b0_52 ^ (a0_52 & c0_52 ^ b0_52 & c0_52));
    let mut a1_52: uint64_t = t1_52.wrapping_add(t2_100);
    let mut b1_52: uint64_t = a0_52;
    let mut c1_52: uint64_t = b0_52;
    let mut d1_52: uint64_t = c0_52;
    let mut e1_52: uint64_t = d0_52.wrapping_add(t1_52);
    let mut f1_52: uint64_t = e0_52;
    let mut g1_52: uint64_t = f0_52;
    let mut h12_52: uint64_t = g0_52;
    *hash.offset(0 as libc::c_uint as isize) = a1_52;
    *hash.offset(1 as libc::c_uint as isize) = b1_52;
    *hash.offset(2 as libc::c_uint as isize) = c1_52;
    *hash.offset(3 as libc::c_uint as isize) = d1_52;
    *hash.offset(4 as libc::c_uint as isize) = e1_52;
    *hash.offset(5 as libc::c_uint as isize) = f1_52;
    *hash.offset(6 as libc::c_uint as isize) = g1_52;
    *hash.offset(7 as libc::c_uint as isize) = h12_52;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_53: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_53: uint64_t = ws[i_5 as usize];
    let mut a0_53: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_53: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_53: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_53: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_53: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_53: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_53: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_53: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_53: uint64_t = k_t_53;
    let mut t1_53: uint64_t = h02_53
        .wrapping_add(
            (e0_53 << 50 as libc::c_uint | e0_53 >> 14 as libc::c_uint)
                ^ ((e0_53 << 46 as libc::c_uint | e0_53 >> 18 as libc::c_uint)
                    ^ (e0_53 << 23 as libc::c_uint | e0_53 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_53 & f0_53 ^ !e0_53 & g0_53)
        .wrapping_add(k_e_t_53)
        .wrapping_add(ws_t_53);
    let mut t2_101: uint64_t = ((a0_53 << 36 as libc::c_uint
        | a0_53 >> 28 as libc::c_uint)
        ^ ((a0_53 << 30 as libc::c_uint | a0_53 >> 34 as libc::c_uint)
            ^ (a0_53 << 25 as libc::c_uint | a0_53 >> 39 as libc::c_uint)))
        .wrapping_add(a0_53 & b0_53 ^ (a0_53 & c0_53 ^ b0_53 & c0_53));
    let mut a1_53: uint64_t = t1_53.wrapping_add(t2_101);
    let mut b1_53: uint64_t = a0_53;
    let mut c1_53: uint64_t = b0_53;
    let mut d1_53: uint64_t = c0_53;
    let mut e1_53: uint64_t = d0_53.wrapping_add(t1_53);
    let mut f1_53: uint64_t = e0_53;
    let mut g1_53: uint64_t = f0_53;
    let mut h12_53: uint64_t = g0_53;
    *hash.offset(0 as libc::c_uint as isize) = a1_53;
    *hash.offset(1 as libc::c_uint as isize) = b1_53;
    *hash.offset(2 as libc::c_uint as isize) = c1_53;
    *hash.offset(3 as libc::c_uint as isize) = d1_53;
    *hash.offset(4 as libc::c_uint as isize) = e1_53;
    *hash.offset(5 as libc::c_uint as isize) = f1_53;
    *hash.offset(6 as libc::c_uint as isize) = g1_53;
    *hash.offset(7 as libc::c_uint as isize) = h12_53;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_54: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_54: uint64_t = ws[i_5 as usize];
    let mut a0_54: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_54: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_54: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_54: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_54: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_54: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_54: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_54: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_54: uint64_t = k_t_54;
    let mut t1_54: uint64_t = h02_54
        .wrapping_add(
            (e0_54 << 50 as libc::c_uint | e0_54 >> 14 as libc::c_uint)
                ^ ((e0_54 << 46 as libc::c_uint | e0_54 >> 18 as libc::c_uint)
                    ^ (e0_54 << 23 as libc::c_uint | e0_54 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_54 & f0_54 ^ !e0_54 & g0_54)
        .wrapping_add(k_e_t_54)
        .wrapping_add(ws_t_54);
    let mut t2_102: uint64_t = ((a0_54 << 36 as libc::c_uint
        | a0_54 >> 28 as libc::c_uint)
        ^ ((a0_54 << 30 as libc::c_uint | a0_54 >> 34 as libc::c_uint)
            ^ (a0_54 << 25 as libc::c_uint | a0_54 >> 39 as libc::c_uint)))
        .wrapping_add(a0_54 & b0_54 ^ (a0_54 & c0_54 ^ b0_54 & c0_54));
    let mut a1_54: uint64_t = t1_54.wrapping_add(t2_102);
    let mut b1_54: uint64_t = a0_54;
    let mut c1_54: uint64_t = b0_54;
    let mut d1_54: uint64_t = c0_54;
    let mut e1_54: uint64_t = d0_54.wrapping_add(t1_54);
    let mut f1_54: uint64_t = e0_54;
    let mut g1_54: uint64_t = f0_54;
    let mut h12_54: uint64_t = g0_54;
    *hash.offset(0 as libc::c_uint as isize) = a1_54;
    *hash.offset(1 as libc::c_uint as isize) = b1_54;
    *hash.offset(2 as libc::c_uint as isize) = c1_54;
    *hash.offset(3 as libc::c_uint as isize) = d1_54;
    *hash.offset(4 as libc::c_uint as isize) = e1_54;
    *hash.offset(5 as libc::c_uint as isize) = f1_54;
    *hash.offset(6 as libc::c_uint as isize) = g1_54;
    *hash.offset(7 as libc::c_uint as isize) = h12_54;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_55: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_55: uint64_t = ws[i_5 as usize];
    let mut a0_55: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_55: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_55: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_55: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_55: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_55: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_55: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_55: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_55: uint64_t = k_t_55;
    let mut t1_55: uint64_t = h02_55
        .wrapping_add(
            (e0_55 << 50 as libc::c_uint | e0_55 >> 14 as libc::c_uint)
                ^ ((e0_55 << 46 as libc::c_uint | e0_55 >> 18 as libc::c_uint)
                    ^ (e0_55 << 23 as libc::c_uint | e0_55 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_55 & f0_55 ^ !e0_55 & g0_55)
        .wrapping_add(k_e_t_55)
        .wrapping_add(ws_t_55);
    let mut t2_103: uint64_t = ((a0_55 << 36 as libc::c_uint
        | a0_55 >> 28 as libc::c_uint)
        ^ ((a0_55 << 30 as libc::c_uint | a0_55 >> 34 as libc::c_uint)
            ^ (a0_55 << 25 as libc::c_uint | a0_55 >> 39 as libc::c_uint)))
        .wrapping_add(a0_55 & b0_55 ^ (a0_55 & c0_55 ^ b0_55 & c0_55));
    let mut a1_55: uint64_t = t1_55.wrapping_add(t2_103);
    let mut b1_55: uint64_t = a0_55;
    let mut c1_55: uint64_t = b0_55;
    let mut d1_55: uint64_t = c0_55;
    let mut e1_55: uint64_t = d0_55.wrapping_add(t1_55);
    let mut f1_55: uint64_t = e0_55;
    let mut g1_55: uint64_t = f0_55;
    let mut h12_55: uint64_t = g0_55;
    *hash.offset(0 as libc::c_uint as isize) = a1_55;
    *hash.offset(1 as libc::c_uint as isize) = b1_55;
    *hash.offset(2 as libc::c_uint as isize) = c1_55;
    *hash.offset(3 as libc::c_uint as isize) = d1_55;
    *hash.offset(4 as libc::c_uint as isize) = e1_55;
    *hash.offset(5 as libc::c_uint as isize) = f1_55;
    *hash.offset(6 as libc::c_uint as isize) = g1_55;
    *hash.offset(7 as libc::c_uint as isize) = h12_55;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_56: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_56: uint64_t = ws[i_5 as usize];
    let mut a0_56: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_56: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_56: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_56: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_56: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_56: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_56: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_56: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_56: uint64_t = k_t_56;
    let mut t1_56: uint64_t = h02_56
        .wrapping_add(
            (e0_56 << 50 as libc::c_uint | e0_56 >> 14 as libc::c_uint)
                ^ ((e0_56 << 46 as libc::c_uint | e0_56 >> 18 as libc::c_uint)
                    ^ (e0_56 << 23 as libc::c_uint | e0_56 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_56 & f0_56 ^ !e0_56 & g0_56)
        .wrapping_add(k_e_t_56)
        .wrapping_add(ws_t_56);
    let mut t2_104: uint64_t = ((a0_56 << 36 as libc::c_uint
        | a0_56 >> 28 as libc::c_uint)
        ^ ((a0_56 << 30 as libc::c_uint | a0_56 >> 34 as libc::c_uint)
            ^ (a0_56 << 25 as libc::c_uint | a0_56 >> 39 as libc::c_uint)))
        .wrapping_add(a0_56 & b0_56 ^ (a0_56 & c0_56 ^ b0_56 & c0_56));
    let mut a1_56: uint64_t = t1_56.wrapping_add(t2_104);
    let mut b1_56: uint64_t = a0_56;
    let mut c1_56: uint64_t = b0_56;
    let mut d1_56: uint64_t = c0_56;
    let mut e1_56: uint64_t = d0_56.wrapping_add(t1_56);
    let mut f1_56: uint64_t = e0_56;
    let mut g1_56: uint64_t = f0_56;
    let mut h12_56: uint64_t = g0_56;
    *hash.offset(0 as libc::c_uint as isize) = a1_56;
    *hash.offset(1 as libc::c_uint as isize) = b1_56;
    *hash.offset(2 as libc::c_uint as isize) = c1_56;
    *hash.offset(3 as libc::c_uint as isize) = d1_56;
    *hash.offset(4 as libc::c_uint as isize) = e1_56;
    *hash.offset(5 as libc::c_uint as isize) = f1_56;
    *hash.offset(6 as libc::c_uint as isize) = g1_56;
    *hash.offset(7 as libc::c_uint as isize) = h12_56;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_57: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_57: uint64_t = ws[i_5 as usize];
    let mut a0_57: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_57: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_57: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_57: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_57: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_57: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_57: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_57: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_57: uint64_t = k_t_57;
    let mut t1_57: uint64_t = h02_57
        .wrapping_add(
            (e0_57 << 50 as libc::c_uint | e0_57 >> 14 as libc::c_uint)
                ^ ((e0_57 << 46 as libc::c_uint | e0_57 >> 18 as libc::c_uint)
                    ^ (e0_57 << 23 as libc::c_uint | e0_57 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_57 & f0_57 ^ !e0_57 & g0_57)
        .wrapping_add(k_e_t_57)
        .wrapping_add(ws_t_57);
    let mut t2_105: uint64_t = ((a0_57 << 36 as libc::c_uint
        | a0_57 >> 28 as libc::c_uint)
        ^ ((a0_57 << 30 as libc::c_uint | a0_57 >> 34 as libc::c_uint)
            ^ (a0_57 << 25 as libc::c_uint | a0_57 >> 39 as libc::c_uint)))
        .wrapping_add(a0_57 & b0_57 ^ (a0_57 & c0_57 ^ b0_57 & c0_57));
    let mut a1_57: uint64_t = t1_57.wrapping_add(t2_105);
    let mut b1_57: uint64_t = a0_57;
    let mut c1_57: uint64_t = b0_57;
    let mut d1_57: uint64_t = c0_57;
    let mut e1_57: uint64_t = d0_57.wrapping_add(t1_57);
    let mut f1_57: uint64_t = e0_57;
    let mut g1_57: uint64_t = f0_57;
    let mut h12_57: uint64_t = g0_57;
    *hash.offset(0 as libc::c_uint as isize) = a1_57;
    *hash.offset(1 as libc::c_uint as isize) = b1_57;
    *hash.offset(2 as libc::c_uint as isize) = c1_57;
    *hash.offset(3 as libc::c_uint as isize) = d1_57;
    *hash.offset(4 as libc::c_uint as isize) = e1_57;
    *hash.offset(5 as libc::c_uint as isize) = f1_57;
    *hash.offset(6 as libc::c_uint as isize) = g1_57;
    *hash.offset(7 as libc::c_uint as isize) = h12_57;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_58: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_58: uint64_t = ws[i_5 as usize];
    let mut a0_58: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_58: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_58: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_58: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_58: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_58: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_58: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_58: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_58: uint64_t = k_t_58;
    let mut t1_58: uint64_t = h02_58
        .wrapping_add(
            (e0_58 << 50 as libc::c_uint | e0_58 >> 14 as libc::c_uint)
                ^ ((e0_58 << 46 as libc::c_uint | e0_58 >> 18 as libc::c_uint)
                    ^ (e0_58 << 23 as libc::c_uint | e0_58 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_58 & f0_58 ^ !e0_58 & g0_58)
        .wrapping_add(k_e_t_58)
        .wrapping_add(ws_t_58);
    let mut t2_106: uint64_t = ((a0_58 << 36 as libc::c_uint
        | a0_58 >> 28 as libc::c_uint)
        ^ ((a0_58 << 30 as libc::c_uint | a0_58 >> 34 as libc::c_uint)
            ^ (a0_58 << 25 as libc::c_uint | a0_58 >> 39 as libc::c_uint)))
        .wrapping_add(a0_58 & b0_58 ^ (a0_58 & c0_58 ^ b0_58 & c0_58));
    let mut a1_58: uint64_t = t1_58.wrapping_add(t2_106);
    let mut b1_58: uint64_t = a0_58;
    let mut c1_58: uint64_t = b0_58;
    let mut d1_58: uint64_t = c0_58;
    let mut e1_58: uint64_t = d0_58.wrapping_add(t1_58);
    let mut f1_58: uint64_t = e0_58;
    let mut g1_58: uint64_t = f0_58;
    let mut h12_58: uint64_t = g0_58;
    *hash.offset(0 as libc::c_uint as isize) = a1_58;
    *hash.offset(1 as libc::c_uint as isize) = b1_58;
    *hash.offset(2 as libc::c_uint as isize) = c1_58;
    *hash.offset(3 as libc::c_uint as isize) = d1_58;
    *hash.offset(4 as libc::c_uint as isize) = e1_58;
    *hash.offset(5 as libc::c_uint as isize) = f1_58;
    *hash.offset(6 as libc::c_uint as isize) = g1_58;
    *hash.offset(7 as libc::c_uint as isize) = h12_58;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_59: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_59: uint64_t = ws[i_5 as usize];
    let mut a0_59: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_59: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_59: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_59: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_59: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_59: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_59: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_59: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_59: uint64_t = k_t_59;
    let mut t1_59: uint64_t = h02_59
        .wrapping_add(
            (e0_59 << 50 as libc::c_uint | e0_59 >> 14 as libc::c_uint)
                ^ ((e0_59 << 46 as libc::c_uint | e0_59 >> 18 as libc::c_uint)
                    ^ (e0_59 << 23 as libc::c_uint | e0_59 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_59 & f0_59 ^ !e0_59 & g0_59)
        .wrapping_add(k_e_t_59)
        .wrapping_add(ws_t_59);
    let mut t2_107: uint64_t = ((a0_59 << 36 as libc::c_uint
        | a0_59 >> 28 as libc::c_uint)
        ^ ((a0_59 << 30 as libc::c_uint | a0_59 >> 34 as libc::c_uint)
            ^ (a0_59 << 25 as libc::c_uint | a0_59 >> 39 as libc::c_uint)))
        .wrapping_add(a0_59 & b0_59 ^ (a0_59 & c0_59 ^ b0_59 & c0_59));
    let mut a1_59: uint64_t = t1_59.wrapping_add(t2_107);
    let mut b1_59: uint64_t = a0_59;
    let mut c1_59: uint64_t = b0_59;
    let mut d1_59: uint64_t = c0_59;
    let mut e1_59: uint64_t = d0_59.wrapping_add(t1_59);
    let mut f1_59: uint64_t = e0_59;
    let mut g1_59: uint64_t = f0_59;
    let mut h12_59: uint64_t = g0_59;
    *hash.offset(0 as libc::c_uint as isize) = a1_59;
    *hash.offset(1 as libc::c_uint as isize) = b1_59;
    *hash.offset(2 as libc::c_uint as isize) = c1_59;
    *hash.offset(3 as libc::c_uint as isize) = d1_59;
    *hash.offset(4 as libc::c_uint as isize) = e1_59;
    *hash.offset(5 as libc::c_uint as isize) = f1_59;
    *hash.offset(6 as libc::c_uint as isize) = g1_59;
    *hash.offset(7 as libc::c_uint as isize) = h12_59;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_60: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_60: uint64_t = ws[i_5 as usize];
    let mut a0_60: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_60: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_60: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_60: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_60: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_60: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_60: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_60: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_60: uint64_t = k_t_60;
    let mut t1_60: uint64_t = h02_60
        .wrapping_add(
            (e0_60 << 50 as libc::c_uint | e0_60 >> 14 as libc::c_uint)
                ^ ((e0_60 << 46 as libc::c_uint | e0_60 >> 18 as libc::c_uint)
                    ^ (e0_60 << 23 as libc::c_uint | e0_60 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_60 & f0_60 ^ !e0_60 & g0_60)
        .wrapping_add(k_e_t_60)
        .wrapping_add(ws_t_60);
    let mut t2_108: uint64_t = ((a0_60 << 36 as libc::c_uint
        | a0_60 >> 28 as libc::c_uint)
        ^ ((a0_60 << 30 as libc::c_uint | a0_60 >> 34 as libc::c_uint)
            ^ (a0_60 << 25 as libc::c_uint | a0_60 >> 39 as libc::c_uint)))
        .wrapping_add(a0_60 & b0_60 ^ (a0_60 & c0_60 ^ b0_60 & c0_60));
    let mut a1_60: uint64_t = t1_60.wrapping_add(t2_108);
    let mut b1_60: uint64_t = a0_60;
    let mut c1_60: uint64_t = b0_60;
    let mut d1_60: uint64_t = c0_60;
    let mut e1_60: uint64_t = d0_60.wrapping_add(t1_60);
    let mut f1_60: uint64_t = e0_60;
    let mut g1_60: uint64_t = f0_60;
    let mut h12_60: uint64_t = g0_60;
    *hash.offset(0 as libc::c_uint as isize) = a1_60;
    *hash.offset(1 as libc::c_uint as isize) = b1_60;
    *hash.offset(2 as libc::c_uint as isize) = c1_60;
    *hash.offset(3 as libc::c_uint as isize) = d1_60;
    *hash.offset(4 as libc::c_uint as isize) = e1_60;
    *hash.offset(5 as libc::c_uint as isize) = f1_60;
    *hash.offset(6 as libc::c_uint as isize) = g1_60;
    *hash.offset(7 as libc::c_uint as isize) = h12_60;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_61: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_61: uint64_t = ws[i_5 as usize];
    let mut a0_61: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_61: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_61: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_61: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_61: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_61: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_61: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_61: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_61: uint64_t = k_t_61;
    let mut t1_61: uint64_t = h02_61
        .wrapping_add(
            (e0_61 << 50 as libc::c_uint | e0_61 >> 14 as libc::c_uint)
                ^ ((e0_61 << 46 as libc::c_uint | e0_61 >> 18 as libc::c_uint)
                    ^ (e0_61 << 23 as libc::c_uint | e0_61 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_61 & f0_61 ^ !e0_61 & g0_61)
        .wrapping_add(k_e_t_61)
        .wrapping_add(ws_t_61);
    let mut t2_109: uint64_t = ((a0_61 << 36 as libc::c_uint
        | a0_61 >> 28 as libc::c_uint)
        ^ ((a0_61 << 30 as libc::c_uint | a0_61 >> 34 as libc::c_uint)
            ^ (a0_61 << 25 as libc::c_uint | a0_61 >> 39 as libc::c_uint)))
        .wrapping_add(a0_61 & b0_61 ^ (a0_61 & c0_61 ^ b0_61 & c0_61));
    let mut a1_61: uint64_t = t1_61.wrapping_add(t2_109);
    let mut b1_61: uint64_t = a0_61;
    let mut c1_61: uint64_t = b0_61;
    let mut d1_61: uint64_t = c0_61;
    let mut e1_61: uint64_t = d0_61.wrapping_add(t1_61);
    let mut f1_61: uint64_t = e0_61;
    let mut g1_61: uint64_t = f0_61;
    let mut h12_61: uint64_t = g0_61;
    *hash.offset(0 as libc::c_uint as isize) = a1_61;
    *hash.offset(1 as libc::c_uint as isize) = b1_61;
    *hash.offset(2 as libc::c_uint as isize) = c1_61;
    *hash.offset(3 as libc::c_uint as isize) = d1_61;
    *hash.offset(4 as libc::c_uint as isize) = e1_61;
    *hash.offset(5 as libc::c_uint as isize) = f1_61;
    *hash.offset(6 as libc::c_uint as isize) = g1_61;
    *hash.offset(7 as libc::c_uint as isize) = h12_61;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_62: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_5) as usize];
    let mut ws_t_62: uint64_t = ws[i_5 as usize];
    let mut a0_62: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_62: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_62: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_62: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_62: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_62: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_62: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_62: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_62: uint64_t = k_t_62;
    let mut t1_62: uint64_t = h02_62
        .wrapping_add(
            (e0_62 << 50 as libc::c_uint | e0_62 >> 14 as libc::c_uint)
                ^ ((e0_62 << 46 as libc::c_uint | e0_62 >> 18 as libc::c_uint)
                    ^ (e0_62 << 23 as libc::c_uint | e0_62 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_62 & f0_62 ^ !e0_62 & g0_62)
        .wrapping_add(k_e_t_62)
        .wrapping_add(ws_t_62);
    let mut t2_110: uint64_t = ((a0_62 << 36 as libc::c_uint
        | a0_62 >> 28 as libc::c_uint)
        ^ ((a0_62 << 30 as libc::c_uint | a0_62 >> 34 as libc::c_uint)
            ^ (a0_62 << 25 as libc::c_uint | a0_62 >> 39 as libc::c_uint)))
        .wrapping_add(a0_62 & b0_62 ^ (a0_62 & c0_62 ^ b0_62 & c0_62));
    let mut a1_62: uint64_t = t1_62.wrapping_add(t2_110);
    let mut b1_62: uint64_t = a0_62;
    let mut c1_62: uint64_t = b0_62;
    let mut d1_62: uint64_t = c0_62;
    let mut e1_62: uint64_t = d0_62.wrapping_add(t1_62);
    let mut f1_62: uint64_t = e0_62;
    let mut g1_62: uint64_t = f0_62;
    let mut h12_62: uint64_t = g0_62;
    *hash.offset(0 as libc::c_uint as isize) = a1_62;
    *hash.offset(1 as libc::c_uint as isize) = b1_62;
    *hash.offset(2 as libc::c_uint as isize) = c1_62;
    *hash.offset(3 as libc::c_uint as isize) = d1_62;
    *hash.offset(4 as libc::c_uint as isize) = e1_62;
    *hash.offset(5 as libc::c_uint as isize) = f1_62;
    *hash.offset(6 as libc::c_uint as isize) = g1_62;
    *hash.offset(7 as libc::c_uint as isize) = h12_62;
    i_5 = (i_5 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 4 as libc::c_uint {
        let mut i_6: uint32_t = 0 as libc::c_uint;
        let mut t16_47: uint64_t = ws[i_6 as usize];
        let mut t15_47: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_47: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_111: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_47: uint64_t = (t2_111 << 45 as libc::c_uint
            | t2_111 >> 19 as libc::c_uint)
            ^ ((t2_111 << 3 as libc::c_uint | t2_111 >> 61 as libc::c_uint)
                ^ t2_111 >> 6 as libc::c_uint);
        let mut s0_47: uint64_t = (t15_47 << 63 as libc::c_uint
            | t15_47 >> 1 as libc::c_uint)
            ^ ((t15_47 << 56 as libc::c_uint | t15_47 >> 8 as libc::c_uint)
                ^ t15_47 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_47
            .wrapping_add(t7_47)
            .wrapping_add(s0_47)
            .wrapping_add(t16_47);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_48: uint64_t = ws[i_6 as usize];
        let mut t15_48: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_48: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_112: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_48: uint64_t = (t2_112 << 45 as libc::c_uint
            | t2_112 >> 19 as libc::c_uint)
            ^ ((t2_112 << 3 as libc::c_uint | t2_112 >> 61 as libc::c_uint)
                ^ t2_112 >> 6 as libc::c_uint);
        let mut s0_48: uint64_t = (t15_48 << 63 as libc::c_uint
            | t15_48 >> 1 as libc::c_uint)
            ^ ((t15_48 << 56 as libc::c_uint | t15_48 >> 8 as libc::c_uint)
                ^ t15_48 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_48
            .wrapping_add(t7_48)
            .wrapping_add(s0_48)
            .wrapping_add(t16_48);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_49: uint64_t = ws[i_6 as usize];
        let mut t15_49: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_49: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_113: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_49: uint64_t = (t2_113 << 45 as libc::c_uint
            | t2_113 >> 19 as libc::c_uint)
            ^ ((t2_113 << 3 as libc::c_uint | t2_113 >> 61 as libc::c_uint)
                ^ t2_113 >> 6 as libc::c_uint);
        let mut s0_49: uint64_t = (t15_49 << 63 as libc::c_uint
            | t15_49 >> 1 as libc::c_uint)
            ^ ((t15_49 << 56 as libc::c_uint | t15_49 >> 8 as libc::c_uint)
                ^ t15_49 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_49
            .wrapping_add(t7_49)
            .wrapping_add(s0_49)
            .wrapping_add(t16_49);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_50: uint64_t = ws[i_6 as usize];
        let mut t15_50: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_50: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_114: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_50: uint64_t = (t2_114 << 45 as libc::c_uint
            | t2_114 >> 19 as libc::c_uint)
            ^ ((t2_114 << 3 as libc::c_uint | t2_114 >> 61 as libc::c_uint)
                ^ t2_114 >> 6 as libc::c_uint);
        let mut s0_50: uint64_t = (t15_50 << 63 as libc::c_uint
            | t15_50 >> 1 as libc::c_uint)
            ^ ((t15_50 << 56 as libc::c_uint | t15_50 >> 8 as libc::c_uint)
                ^ t15_50 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_50
            .wrapping_add(t7_50)
            .wrapping_add(s0_50)
            .wrapping_add(t16_50);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_51: uint64_t = ws[i_6 as usize];
        let mut t15_51: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_51: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_115: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_51: uint64_t = (t2_115 << 45 as libc::c_uint
            | t2_115 >> 19 as libc::c_uint)
            ^ ((t2_115 << 3 as libc::c_uint | t2_115 >> 61 as libc::c_uint)
                ^ t2_115 >> 6 as libc::c_uint);
        let mut s0_51: uint64_t = (t15_51 << 63 as libc::c_uint
            | t15_51 >> 1 as libc::c_uint)
            ^ ((t15_51 << 56 as libc::c_uint | t15_51 >> 8 as libc::c_uint)
                ^ t15_51 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_51
            .wrapping_add(t7_51)
            .wrapping_add(s0_51)
            .wrapping_add(t16_51);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_52: uint64_t = ws[i_6 as usize];
        let mut t15_52: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_52: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_116: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_52: uint64_t = (t2_116 << 45 as libc::c_uint
            | t2_116 >> 19 as libc::c_uint)
            ^ ((t2_116 << 3 as libc::c_uint | t2_116 >> 61 as libc::c_uint)
                ^ t2_116 >> 6 as libc::c_uint);
        let mut s0_52: uint64_t = (t15_52 << 63 as libc::c_uint
            | t15_52 >> 1 as libc::c_uint)
            ^ ((t15_52 << 56 as libc::c_uint | t15_52 >> 8 as libc::c_uint)
                ^ t15_52 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_52
            .wrapping_add(t7_52)
            .wrapping_add(s0_52)
            .wrapping_add(t16_52);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_53: uint64_t = ws[i_6 as usize];
        let mut t15_53: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_53: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_117: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_53: uint64_t = (t2_117 << 45 as libc::c_uint
            | t2_117 >> 19 as libc::c_uint)
            ^ ((t2_117 << 3 as libc::c_uint | t2_117 >> 61 as libc::c_uint)
                ^ t2_117 >> 6 as libc::c_uint);
        let mut s0_53: uint64_t = (t15_53 << 63 as libc::c_uint
            | t15_53 >> 1 as libc::c_uint)
            ^ ((t15_53 << 56 as libc::c_uint | t15_53 >> 8 as libc::c_uint)
                ^ t15_53 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_53
            .wrapping_add(t7_53)
            .wrapping_add(s0_53)
            .wrapping_add(t16_53);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_54: uint64_t = ws[i_6 as usize];
        let mut t15_54: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_54: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_118: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_54: uint64_t = (t2_118 << 45 as libc::c_uint
            | t2_118 >> 19 as libc::c_uint)
            ^ ((t2_118 << 3 as libc::c_uint | t2_118 >> 61 as libc::c_uint)
                ^ t2_118 >> 6 as libc::c_uint);
        let mut s0_54: uint64_t = (t15_54 << 63 as libc::c_uint
            | t15_54 >> 1 as libc::c_uint)
            ^ ((t15_54 << 56 as libc::c_uint | t15_54 >> 8 as libc::c_uint)
                ^ t15_54 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_54
            .wrapping_add(t7_54)
            .wrapping_add(s0_54)
            .wrapping_add(t16_54);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_55: uint64_t = ws[i_6 as usize];
        let mut t15_55: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_55: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_119: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_55: uint64_t = (t2_119 << 45 as libc::c_uint
            | t2_119 >> 19 as libc::c_uint)
            ^ ((t2_119 << 3 as libc::c_uint | t2_119 >> 61 as libc::c_uint)
                ^ t2_119 >> 6 as libc::c_uint);
        let mut s0_55: uint64_t = (t15_55 << 63 as libc::c_uint
            | t15_55 >> 1 as libc::c_uint)
            ^ ((t15_55 << 56 as libc::c_uint | t15_55 >> 8 as libc::c_uint)
                ^ t15_55 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_55
            .wrapping_add(t7_55)
            .wrapping_add(s0_55)
            .wrapping_add(t16_55);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_56: uint64_t = ws[i_6 as usize];
        let mut t15_56: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_56: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_120: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_56: uint64_t = (t2_120 << 45 as libc::c_uint
            | t2_120 >> 19 as libc::c_uint)
            ^ ((t2_120 << 3 as libc::c_uint | t2_120 >> 61 as libc::c_uint)
                ^ t2_120 >> 6 as libc::c_uint);
        let mut s0_56: uint64_t = (t15_56 << 63 as libc::c_uint
            | t15_56 >> 1 as libc::c_uint)
            ^ ((t15_56 << 56 as libc::c_uint | t15_56 >> 8 as libc::c_uint)
                ^ t15_56 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_56
            .wrapping_add(t7_56)
            .wrapping_add(s0_56)
            .wrapping_add(t16_56);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_57: uint64_t = ws[i_6 as usize];
        let mut t15_57: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_57: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_121: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_57: uint64_t = (t2_121 << 45 as libc::c_uint
            | t2_121 >> 19 as libc::c_uint)
            ^ ((t2_121 << 3 as libc::c_uint | t2_121 >> 61 as libc::c_uint)
                ^ t2_121 >> 6 as libc::c_uint);
        let mut s0_57: uint64_t = (t15_57 << 63 as libc::c_uint
            | t15_57 >> 1 as libc::c_uint)
            ^ ((t15_57 << 56 as libc::c_uint | t15_57 >> 8 as libc::c_uint)
                ^ t15_57 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_57
            .wrapping_add(t7_57)
            .wrapping_add(s0_57)
            .wrapping_add(t16_57);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_58: uint64_t = ws[i_6 as usize];
        let mut t15_58: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_58: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_122: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_58: uint64_t = (t2_122 << 45 as libc::c_uint
            | t2_122 >> 19 as libc::c_uint)
            ^ ((t2_122 << 3 as libc::c_uint | t2_122 >> 61 as libc::c_uint)
                ^ t2_122 >> 6 as libc::c_uint);
        let mut s0_58: uint64_t = (t15_58 << 63 as libc::c_uint
            | t15_58 >> 1 as libc::c_uint)
            ^ ((t15_58 << 56 as libc::c_uint | t15_58 >> 8 as libc::c_uint)
                ^ t15_58 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_58
            .wrapping_add(t7_58)
            .wrapping_add(s0_58)
            .wrapping_add(t16_58);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_59: uint64_t = ws[i_6 as usize];
        let mut t15_59: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_59: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_123: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_59: uint64_t = (t2_123 << 45 as libc::c_uint
            | t2_123 >> 19 as libc::c_uint)
            ^ ((t2_123 << 3 as libc::c_uint | t2_123 >> 61 as libc::c_uint)
                ^ t2_123 >> 6 as libc::c_uint);
        let mut s0_59: uint64_t = (t15_59 << 63 as libc::c_uint
            | t15_59 >> 1 as libc::c_uint)
            ^ ((t15_59 << 56 as libc::c_uint | t15_59 >> 8 as libc::c_uint)
                ^ t15_59 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_59
            .wrapping_add(t7_59)
            .wrapping_add(s0_59)
            .wrapping_add(t16_59);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_60: uint64_t = ws[i_6 as usize];
        let mut t15_60: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_60: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_124: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_60: uint64_t = (t2_124 << 45 as libc::c_uint
            | t2_124 >> 19 as libc::c_uint)
            ^ ((t2_124 << 3 as libc::c_uint | t2_124 >> 61 as libc::c_uint)
                ^ t2_124 >> 6 as libc::c_uint);
        let mut s0_60: uint64_t = (t15_60 << 63 as libc::c_uint
            | t15_60 >> 1 as libc::c_uint)
            ^ ((t15_60 << 56 as libc::c_uint | t15_60 >> 8 as libc::c_uint)
                ^ t15_60 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_60
            .wrapping_add(t7_60)
            .wrapping_add(s0_60)
            .wrapping_add(t16_60);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_61: uint64_t = ws[i_6 as usize];
        let mut t15_61: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_61: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_125: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_61: uint64_t = (t2_125 << 45 as libc::c_uint
            | t2_125 >> 19 as libc::c_uint)
            ^ ((t2_125 << 3 as libc::c_uint | t2_125 >> 61 as libc::c_uint)
                ^ t2_125 >> 6 as libc::c_uint);
        let mut s0_61: uint64_t = (t15_61 << 63 as libc::c_uint
            | t15_61 >> 1 as libc::c_uint)
            ^ ((t15_61 << 56 as libc::c_uint | t15_61 >> 8 as libc::c_uint)
                ^ t15_61 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_61
            .wrapping_add(t7_61)
            .wrapping_add(s0_61)
            .wrapping_add(t16_61);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_62: uint64_t = ws[i_6 as usize];
        let mut t15_62: uint64_t = ws[i_6
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_62: uint64_t = ws[i_6
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_126: uint64_t = ws[i_6
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_62: uint64_t = (t2_126 << 45 as libc::c_uint
            | t2_126 >> 19 as libc::c_uint)
            ^ ((t2_126 << 3 as libc::c_uint | t2_126 >> 61 as libc::c_uint)
                ^ t2_126 >> 6 as libc::c_uint);
        let mut s0_62: uint64_t = (t15_62 << 63 as libc::c_uint
            | t15_62 >> 1 as libc::c_uint)
            ^ ((t15_62 << 56 as libc::c_uint | t15_62 >> 8 as libc::c_uint)
                ^ t15_62 >> 7 as libc::c_uint);
        ws[i_6
            as usize] = s1_62
            .wrapping_add(t7_62)
            .wrapping_add(s0_62)
            .wrapping_add(t16_62);
        i_6 = (i_6 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_7: uint32_t = 0 as libc::c_uint;
    let mut k_t_63: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_63: uint64_t = ws[i_7 as usize];
    let mut a0_63: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_63: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_63: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_63: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_63: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_63: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_63: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_63: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_63: uint64_t = k_t_63;
    let mut t1_63: uint64_t = h02_63
        .wrapping_add(
            (e0_63 << 50 as libc::c_uint | e0_63 >> 14 as libc::c_uint)
                ^ ((e0_63 << 46 as libc::c_uint | e0_63 >> 18 as libc::c_uint)
                    ^ (e0_63 << 23 as libc::c_uint | e0_63 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_63 & f0_63 ^ !e0_63 & g0_63)
        .wrapping_add(k_e_t_63)
        .wrapping_add(ws_t_63);
    let mut t2_127: uint64_t = ((a0_63 << 36 as libc::c_uint
        | a0_63 >> 28 as libc::c_uint)
        ^ ((a0_63 << 30 as libc::c_uint | a0_63 >> 34 as libc::c_uint)
            ^ (a0_63 << 25 as libc::c_uint | a0_63 >> 39 as libc::c_uint)))
        .wrapping_add(a0_63 & b0_63 ^ (a0_63 & c0_63 ^ b0_63 & c0_63));
    let mut a1_63: uint64_t = t1_63.wrapping_add(t2_127);
    let mut b1_63: uint64_t = a0_63;
    let mut c1_63: uint64_t = b0_63;
    let mut d1_63: uint64_t = c0_63;
    let mut e1_63: uint64_t = d0_63.wrapping_add(t1_63);
    let mut f1_63: uint64_t = e0_63;
    let mut g1_63: uint64_t = f0_63;
    let mut h12_63: uint64_t = g0_63;
    *hash.offset(0 as libc::c_uint as isize) = a1_63;
    *hash.offset(1 as libc::c_uint as isize) = b1_63;
    *hash.offset(2 as libc::c_uint as isize) = c1_63;
    *hash.offset(3 as libc::c_uint as isize) = d1_63;
    *hash.offset(4 as libc::c_uint as isize) = e1_63;
    *hash.offset(5 as libc::c_uint as isize) = f1_63;
    *hash.offset(6 as libc::c_uint as isize) = g1_63;
    *hash.offset(7 as libc::c_uint as isize) = h12_63;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_64: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_64: uint64_t = ws[i_7 as usize];
    let mut a0_64: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_64: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_64: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_64: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_64: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_64: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_64: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_64: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_64: uint64_t = k_t_64;
    let mut t1_64: uint64_t = h02_64
        .wrapping_add(
            (e0_64 << 50 as libc::c_uint | e0_64 >> 14 as libc::c_uint)
                ^ ((e0_64 << 46 as libc::c_uint | e0_64 >> 18 as libc::c_uint)
                    ^ (e0_64 << 23 as libc::c_uint | e0_64 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_64 & f0_64 ^ !e0_64 & g0_64)
        .wrapping_add(k_e_t_64)
        .wrapping_add(ws_t_64);
    let mut t2_128: uint64_t = ((a0_64 << 36 as libc::c_uint
        | a0_64 >> 28 as libc::c_uint)
        ^ ((a0_64 << 30 as libc::c_uint | a0_64 >> 34 as libc::c_uint)
            ^ (a0_64 << 25 as libc::c_uint | a0_64 >> 39 as libc::c_uint)))
        .wrapping_add(a0_64 & b0_64 ^ (a0_64 & c0_64 ^ b0_64 & c0_64));
    let mut a1_64: uint64_t = t1_64.wrapping_add(t2_128);
    let mut b1_64: uint64_t = a0_64;
    let mut c1_64: uint64_t = b0_64;
    let mut d1_64: uint64_t = c0_64;
    let mut e1_64: uint64_t = d0_64.wrapping_add(t1_64);
    let mut f1_64: uint64_t = e0_64;
    let mut g1_64: uint64_t = f0_64;
    let mut h12_64: uint64_t = g0_64;
    *hash.offset(0 as libc::c_uint as isize) = a1_64;
    *hash.offset(1 as libc::c_uint as isize) = b1_64;
    *hash.offset(2 as libc::c_uint as isize) = c1_64;
    *hash.offset(3 as libc::c_uint as isize) = d1_64;
    *hash.offset(4 as libc::c_uint as isize) = e1_64;
    *hash.offset(5 as libc::c_uint as isize) = f1_64;
    *hash.offset(6 as libc::c_uint as isize) = g1_64;
    *hash.offset(7 as libc::c_uint as isize) = h12_64;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_65: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_65: uint64_t = ws[i_7 as usize];
    let mut a0_65: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_65: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_65: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_65: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_65: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_65: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_65: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_65: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_65: uint64_t = k_t_65;
    let mut t1_65: uint64_t = h02_65
        .wrapping_add(
            (e0_65 << 50 as libc::c_uint | e0_65 >> 14 as libc::c_uint)
                ^ ((e0_65 << 46 as libc::c_uint | e0_65 >> 18 as libc::c_uint)
                    ^ (e0_65 << 23 as libc::c_uint | e0_65 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_65 & f0_65 ^ !e0_65 & g0_65)
        .wrapping_add(k_e_t_65)
        .wrapping_add(ws_t_65);
    let mut t2_129: uint64_t = ((a0_65 << 36 as libc::c_uint
        | a0_65 >> 28 as libc::c_uint)
        ^ ((a0_65 << 30 as libc::c_uint | a0_65 >> 34 as libc::c_uint)
            ^ (a0_65 << 25 as libc::c_uint | a0_65 >> 39 as libc::c_uint)))
        .wrapping_add(a0_65 & b0_65 ^ (a0_65 & c0_65 ^ b0_65 & c0_65));
    let mut a1_65: uint64_t = t1_65.wrapping_add(t2_129);
    let mut b1_65: uint64_t = a0_65;
    let mut c1_65: uint64_t = b0_65;
    let mut d1_65: uint64_t = c0_65;
    let mut e1_65: uint64_t = d0_65.wrapping_add(t1_65);
    let mut f1_65: uint64_t = e0_65;
    let mut g1_65: uint64_t = f0_65;
    let mut h12_65: uint64_t = g0_65;
    *hash.offset(0 as libc::c_uint as isize) = a1_65;
    *hash.offset(1 as libc::c_uint as isize) = b1_65;
    *hash.offset(2 as libc::c_uint as isize) = c1_65;
    *hash.offset(3 as libc::c_uint as isize) = d1_65;
    *hash.offset(4 as libc::c_uint as isize) = e1_65;
    *hash.offset(5 as libc::c_uint as isize) = f1_65;
    *hash.offset(6 as libc::c_uint as isize) = g1_65;
    *hash.offset(7 as libc::c_uint as isize) = h12_65;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_66: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_66: uint64_t = ws[i_7 as usize];
    let mut a0_66: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_66: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_66: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_66: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_66: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_66: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_66: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_66: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_66: uint64_t = k_t_66;
    let mut t1_66: uint64_t = h02_66
        .wrapping_add(
            (e0_66 << 50 as libc::c_uint | e0_66 >> 14 as libc::c_uint)
                ^ ((e0_66 << 46 as libc::c_uint | e0_66 >> 18 as libc::c_uint)
                    ^ (e0_66 << 23 as libc::c_uint | e0_66 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_66 & f0_66 ^ !e0_66 & g0_66)
        .wrapping_add(k_e_t_66)
        .wrapping_add(ws_t_66);
    let mut t2_130: uint64_t = ((a0_66 << 36 as libc::c_uint
        | a0_66 >> 28 as libc::c_uint)
        ^ ((a0_66 << 30 as libc::c_uint | a0_66 >> 34 as libc::c_uint)
            ^ (a0_66 << 25 as libc::c_uint | a0_66 >> 39 as libc::c_uint)))
        .wrapping_add(a0_66 & b0_66 ^ (a0_66 & c0_66 ^ b0_66 & c0_66));
    let mut a1_66: uint64_t = t1_66.wrapping_add(t2_130);
    let mut b1_66: uint64_t = a0_66;
    let mut c1_66: uint64_t = b0_66;
    let mut d1_66: uint64_t = c0_66;
    let mut e1_66: uint64_t = d0_66.wrapping_add(t1_66);
    let mut f1_66: uint64_t = e0_66;
    let mut g1_66: uint64_t = f0_66;
    let mut h12_66: uint64_t = g0_66;
    *hash.offset(0 as libc::c_uint as isize) = a1_66;
    *hash.offset(1 as libc::c_uint as isize) = b1_66;
    *hash.offset(2 as libc::c_uint as isize) = c1_66;
    *hash.offset(3 as libc::c_uint as isize) = d1_66;
    *hash.offset(4 as libc::c_uint as isize) = e1_66;
    *hash.offset(5 as libc::c_uint as isize) = f1_66;
    *hash.offset(6 as libc::c_uint as isize) = g1_66;
    *hash.offset(7 as libc::c_uint as isize) = h12_66;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_67: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_67: uint64_t = ws[i_7 as usize];
    let mut a0_67: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_67: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_67: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_67: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_67: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_67: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_67: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_67: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_67: uint64_t = k_t_67;
    let mut t1_67: uint64_t = h02_67
        .wrapping_add(
            (e0_67 << 50 as libc::c_uint | e0_67 >> 14 as libc::c_uint)
                ^ ((e0_67 << 46 as libc::c_uint | e0_67 >> 18 as libc::c_uint)
                    ^ (e0_67 << 23 as libc::c_uint | e0_67 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_67 & f0_67 ^ !e0_67 & g0_67)
        .wrapping_add(k_e_t_67)
        .wrapping_add(ws_t_67);
    let mut t2_131: uint64_t = ((a0_67 << 36 as libc::c_uint
        | a0_67 >> 28 as libc::c_uint)
        ^ ((a0_67 << 30 as libc::c_uint | a0_67 >> 34 as libc::c_uint)
            ^ (a0_67 << 25 as libc::c_uint | a0_67 >> 39 as libc::c_uint)))
        .wrapping_add(a0_67 & b0_67 ^ (a0_67 & c0_67 ^ b0_67 & c0_67));
    let mut a1_67: uint64_t = t1_67.wrapping_add(t2_131);
    let mut b1_67: uint64_t = a0_67;
    let mut c1_67: uint64_t = b0_67;
    let mut d1_67: uint64_t = c0_67;
    let mut e1_67: uint64_t = d0_67.wrapping_add(t1_67);
    let mut f1_67: uint64_t = e0_67;
    let mut g1_67: uint64_t = f0_67;
    let mut h12_67: uint64_t = g0_67;
    *hash.offset(0 as libc::c_uint as isize) = a1_67;
    *hash.offset(1 as libc::c_uint as isize) = b1_67;
    *hash.offset(2 as libc::c_uint as isize) = c1_67;
    *hash.offset(3 as libc::c_uint as isize) = d1_67;
    *hash.offset(4 as libc::c_uint as isize) = e1_67;
    *hash.offset(5 as libc::c_uint as isize) = f1_67;
    *hash.offset(6 as libc::c_uint as isize) = g1_67;
    *hash.offset(7 as libc::c_uint as isize) = h12_67;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_68: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_68: uint64_t = ws[i_7 as usize];
    let mut a0_68: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_68: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_68: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_68: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_68: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_68: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_68: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_68: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_68: uint64_t = k_t_68;
    let mut t1_68: uint64_t = h02_68
        .wrapping_add(
            (e0_68 << 50 as libc::c_uint | e0_68 >> 14 as libc::c_uint)
                ^ ((e0_68 << 46 as libc::c_uint | e0_68 >> 18 as libc::c_uint)
                    ^ (e0_68 << 23 as libc::c_uint | e0_68 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_68 & f0_68 ^ !e0_68 & g0_68)
        .wrapping_add(k_e_t_68)
        .wrapping_add(ws_t_68);
    let mut t2_132: uint64_t = ((a0_68 << 36 as libc::c_uint
        | a0_68 >> 28 as libc::c_uint)
        ^ ((a0_68 << 30 as libc::c_uint | a0_68 >> 34 as libc::c_uint)
            ^ (a0_68 << 25 as libc::c_uint | a0_68 >> 39 as libc::c_uint)))
        .wrapping_add(a0_68 & b0_68 ^ (a0_68 & c0_68 ^ b0_68 & c0_68));
    let mut a1_68: uint64_t = t1_68.wrapping_add(t2_132);
    let mut b1_68: uint64_t = a0_68;
    let mut c1_68: uint64_t = b0_68;
    let mut d1_68: uint64_t = c0_68;
    let mut e1_68: uint64_t = d0_68.wrapping_add(t1_68);
    let mut f1_68: uint64_t = e0_68;
    let mut g1_68: uint64_t = f0_68;
    let mut h12_68: uint64_t = g0_68;
    *hash.offset(0 as libc::c_uint as isize) = a1_68;
    *hash.offset(1 as libc::c_uint as isize) = b1_68;
    *hash.offset(2 as libc::c_uint as isize) = c1_68;
    *hash.offset(3 as libc::c_uint as isize) = d1_68;
    *hash.offset(4 as libc::c_uint as isize) = e1_68;
    *hash.offset(5 as libc::c_uint as isize) = f1_68;
    *hash.offset(6 as libc::c_uint as isize) = g1_68;
    *hash.offset(7 as libc::c_uint as isize) = h12_68;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_69: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_69: uint64_t = ws[i_7 as usize];
    let mut a0_69: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_69: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_69: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_69: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_69: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_69: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_69: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_69: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_69: uint64_t = k_t_69;
    let mut t1_69: uint64_t = h02_69
        .wrapping_add(
            (e0_69 << 50 as libc::c_uint | e0_69 >> 14 as libc::c_uint)
                ^ ((e0_69 << 46 as libc::c_uint | e0_69 >> 18 as libc::c_uint)
                    ^ (e0_69 << 23 as libc::c_uint | e0_69 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_69 & f0_69 ^ !e0_69 & g0_69)
        .wrapping_add(k_e_t_69)
        .wrapping_add(ws_t_69);
    let mut t2_133: uint64_t = ((a0_69 << 36 as libc::c_uint
        | a0_69 >> 28 as libc::c_uint)
        ^ ((a0_69 << 30 as libc::c_uint | a0_69 >> 34 as libc::c_uint)
            ^ (a0_69 << 25 as libc::c_uint | a0_69 >> 39 as libc::c_uint)))
        .wrapping_add(a0_69 & b0_69 ^ (a0_69 & c0_69 ^ b0_69 & c0_69));
    let mut a1_69: uint64_t = t1_69.wrapping_add(t2_133);
    let mut b1_69: uint64_t = a0_69;
    let mut c1_69: uint64_t = b0_69;
    let mut d1_69: uint64_t = c0_69;
    let mut e1_69: uint64_t = d0_69.wrapping_add(t1_69);
    let mut f1_69: uint64_t = e0_69;
    let mut g1_69: uint64_t = f0_69;
    let mut h12_69: uint64_t = g0_69;
    *hash.offset(0 as libc::c_uint as isize) = a1_69;
    *hash.offset(1 as libc::c_uint as isize) = b1_69;
    *hash.offset(2 as libc::c_uint as isize) = c1_69;
    *hash.offset(3 as libc::c_uint as isize) = d1_69;
    *hash.offset(4 as libc::c_uint as isize) = e1_69;
    *hash.offset(5 as libc::c_uint as isize) = f1_69;
    *hash.offset(6 as libc::c_uint as isize) = g1_69;
    *hash.offset(7 as libc::c_uint as isize) = h12_69;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_70: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_70: uint64_t = ws[i_7 as usize];
    let mut a0_70: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_70: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_70: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_70: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_70: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_70: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_70: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_70: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_70: uint64_t = k_t_70;
    let mut t1_70: uint64_t = h02_70
        .wrapping_add(
            (e0_70 << 50 as libc::c_uint | e0_70 >> 14 as libc::c_uint)
                ^ ((e0_70 << 46 as libc::c_uint | e0_70 >> 18 as libc::c_uint)
                    ^ (e0_70 << 23 as libc::c_uint | e0_70 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_70 & f0_70 ^ !e0_70 & g0_70)
        .wrapping_add(k_e_t_70)
        .wrapping_add(ws_t_70);
    let mut t2_134: uint64_t = ((a0_70 << 36 as libc::c_uint
        | a0_70 >> 28 as libc::c_uint)
        ^ ((a0_70 << 30 as libc::c_uint | a0_70 >> 34 as libc::c_uint)
            ^ (a0_70 << 25 as libc::c_uint | a0_70 >> 39 as libc::c_uint)))
        .wrapping_add(a0_70 & b0_70 ^ (a0_70 & c0_70 ^ b0_70 & c0_70));
    let mut a1_70: uint64_t = t1_70.wrapping_add(t2_134);
    let mut b1_70: uint64_t = a0_70;
    let mut c1_70: uint64_t = b0_70;
    let mut d1_70: uint64_t = c0_70;
    let mut e1_70: uint64_t = d0_70.wrapping_add(t1_70);
    let mut f1_70: uint64_t = e0_70;
    let mut g1_70: uint64_t = f0_70;
    let mut h12_70: uint64_t = g0_70;
    *hash.offset(0 as libc::c_uint as isize) = a1_70;
    *hash.offset(1 as libc::c_uint as isize) = b1_70;
    *hash.offset(2 as libc::c_uint as isize) = c1_70;
    *hash.offset(3 as libc::c_uint as isize) = d1_70;
    *hash.offset(4 as libc::c_uint as isize) = e1_70;
    *hash.offset(5 as libc::c_uint as isize) = f1_70;
    *hash.offset(6 as libc::c_uint as isize) = g1_70;
    *hash.offset(7 as libc::c_uint as isize) = h12_70;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_71: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_71: uint64_t = ws[i_7 as usize];
    let mut a0_71: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_71: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_71: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_71: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_71: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_71: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_71: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_71: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_71: uint64_t = k_t_71;
    let mut t1_71: uint64_t = h02_71
        .wrapping_add(
            (e0_71 << 50 as libc::c_uint | e0_71 >> 14 as libc::c_uint)
                ^ ((e0_71 << 46 as libc::c_uint | e0_71 >> 18 as libc::c_uint)
                    ^ (e0_71 << 23 as libc::c_uint | e0_71 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_71 & f0_71 ^ !e0_71 & g0_71)
        .wrapping_add(k_e_t_71)
        .wrapping_add(ws_t_71);
    let mut t2_135: uint64_t = ((a0_71 << 36 as libc::c_uint
        | a0_71 >> 28 as libc::c_uint)
        ^ ((a0_71 << 30 as libc::c_uint | a0_71 >> 34 as libc::c_uint)
            ^ (a0_71 << 25 as libc::c_uint | a0_71 >> 39 as libc::c_uint)))
        .wrapping_add(a0_71 & b0_71 ^ (a0_71 & c0_71 ^ b0_71 & c0_71));
    let mut a1_71: uint64_t = t1_71.wrapping_add(t2_135);
    let mut b1_71: uint64_t = a0_71;
    let mut c1_71: uint64_t = b0_71;
    let mut d1_71: uint64_t = c0_71;
    let mut e1_71: uint64_t = d0_71.wrapping_add(t1_71);
    let mut f1_71: uint64_t = e0_71;
    let mut g1_71: uint64_t = f0_71;
    let mut h12_71: uint64_t = g0_71;
    *hash.offset(0 as libc::c_uint as isize) = a1_71;
    *hash.offset(1 as libc::c_uint as isize) = b1_71;
    *hash.offset(2 as libc::c_uint as isize) = c1_71;
    *hash.offset(3 as libc::c_uint as isize) = d1_71;
    *hash.offset(4 as libc::c_uint as isize) = e1_71;
    *hash.offset(5 as libc::c_uint as isize) = f1_71;
    *hash.offset(6 as libc::c_uint as isize) = g1_71;
    *hash.offset(7 as libc::c_uint as isize) = h12_71;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_72: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_72: uint64_t = ws[i_7 as usize];
    let mut a0_72: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_72: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_72: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_72: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_72: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_72: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_72: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_72: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_72: uint64_t = k_t_72;
    let mut t1_72: uint64_t = h02_72
        .wrapping_add(
            (e0_72 << 50 as libc::c_uint | e0_72 >> 14 as libc::c_uint)
                ^ ((e0_72 << 46 as libc::c_uint | e0_72 >> 18 as libc::c_uint)
                    ^ (e0_72 << 23 as libc::c_uint | e0_72 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_72 & f0_72 ^ !e0_72 & g0_72)
        .wrapping_add(k_e_t_72)
        .wrapping_add(ws_t_72);
    let mut t2_136: uint64_t = ((a0_72 << 36 as libc::c_uint
        | a0_72 >> 28 as libc::c_uint)
        ^ ((a0_72 << 30 as libc::c_uint | a0_72 >> 34 as libc::c_uint)
            ^ (a0_72 << 25 as libc::c_uint | a0_72 >> 39 as libc::c_uint)))
        .wrapping_add(a0_72 & b0_72 ^ (a0_72 & c0_72 ^ b0_72 & c0_72));
    let mut a1_72: uint64_t = t1_72.wrapping_add(t2_136);
    let mut b1_72: uint64_t = a0_72;
    let mut c1_72: uint64_t = b0_72;
    let mut d1_72: uint64_t = c0_72;
    let mut e1_72: uint64_t = d0_72.wrapping_add(t1_72);
    let mut f1_72: uint64_t = e0_72;
    let mut g1_72: uint64_t = f0_72;
    let mut h12_72: uint64_t = g0_72;
    *hash.offset(0 as libc::c_uint as isize) = a1_72;
    *hash.offset(1 as libc::c_uint as isize) = b1_72;
    *hash.offset(2 as libc::c_uint as isize) = c1_72;
    *hash.offset(3 as libc::c_uint as isize) = d1_72;
    *hash.offset(4 as libc::c_uint as isize) = e1_72;
    *hash.offset(5 as libc::c_uint as isize) = f1_72;
    *hash.offset(6 as libc::c_uint as isize) = g1_72;
    *hash.offset(7 as libc::c_uint as isize) = h12_72;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_73: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_73: uint64_t = ws[i_7 as usize];
    let mut a0_73: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_73: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_73: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_73: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_73: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_73: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_73: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_73: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_73: uint64_t = k_t_73;
    let mut t1_73: uint64_t = h02_73
        .wrapping_add(
            (e0_73 << 50 as libc::c_uint | e0_73 >> 14 as libc::c_uint)
                ^ ((e0_73 << 46 as libc::c_uint | e0_73 >> 18 as libc::c_uint)
                    ^ (e0_73 << 23 as libc::c_uint | e0_73 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_73 & f0_73 ^ !e0_73 & g0_73)
        .wrapping_add(k_e_t_73)
        .wrapping_add(ws_t_73);
    let mut t2_137: uint64_t = ((a0_73 << 36 as libc::c_uint
        | a0_73 >> 28 as libc::c_uint)
        ^ ((a0_73 << 30 as libc::c_uint | a0_73 >> 34 as libc::c_uint)
            ^ (a0_73 << 25 as libc::c_uint | a0_73 >> 39 as libc::c_uint)))
        .wrapping_add(a0_73 & b0_73 ^ (a0_73 & c0_73 ^ b0_73 & c0_73));
    let mut a1_73: uint64_t = t1_73.wrapping_add(t2_137);
    let mut b1_73: uint64_t = a0_73;
    let mut c1_73: uint64_t = b0_73;
    let mut d1_73: uint64_t = c0_73;
    let mut e1_73: uint64_t = d0_73.wrapping_add(t1_73);
    let mut f1_73: uint64_t = e0_73;
    let mut g1_73: uint64_t = f0_73;
    let mut h12_73: uint64_t = g0_73;
    *hash.offset(0 as libc::c_uint as isize) = a1_73;
    *hash.offset(1 as libc::c_uint as isize) = b1_73;
    *hash.offset(2 as libc::c_uint as isize) = c1_73;
    *hash.offset(3 as libc::c_uint as isize) = d1_73;
    *hash.offset(4 as libc::c_uint as isize) = e1_73;
    *hash.offset(5 as libc::c_uint as isize) = f1_73;
    *hash.offset(6 as libc::c_uint as isize) = g1_73;
    *hash.offset(7 as libc::c_uint as isize) = h12_73;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_74: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_74: uint64_t = ws[i_7 as usize];
    let mut a0_74: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_74: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_74: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_74: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_74: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_74: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_74: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_74: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_74: uint64_t = k_t_74;
    let mut t1_74: uint64_t = h02_74
        .wrapping_add(
            (e0_74 << 50 as libc::c_uint | e0_74 >> 14 as libc::c_uint)
                ^ ((e0_74 << 46 as libc::c_uint | e0_74 >> 18 as libc::c_uint)
                    ^ (e0_74 << 23 as libc::c_uint | e0_74 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_74 & f0_74 ^ !e0_74 & g0_74)
        .wrapping_add(k_e_t_74)
        .wrapping_add(ws_t_74);
    let mut t2_138: uint64_t = ((a0_74 << 36 as libc::c_uint
        | a0_74 >> 28 as libc::c_uint)
        ^ ((a0_74 << 30 as libc::c_uint | a0_74 >> 34 as libc::c_uint)
            ^ (a0_74 << 25 as libc::c_uint | a0_74 >> 39 as libc::c_uint)))
        .wrapping_add(a0_74 & b0_74 ^ (a0_74 & c0_74 ^ b0_74 & c0_74));
    let mut a1_74: uint64_t = t1_74.wrapping_add(t2_138);
    let mut b1_74: uint64_t = a0_74;
    let mut c1_74: uint64_t = b0_74;
    let mut d1_74: uint64_t = c0_74;
    let mut e1_74: uint64_t = d0_74.wrapping_add(t1_74);
    let mut f1_74: uint64_t = e0_74;
    let mut g1_74: uint64_t = f0_74;
    let mut h12_74: uint64_t = g0_74;
    *hash.offset(0 as libc::c_uint as isize) = a1_74;
    *hash.offset(1 as libc::c_uint as isize) = b1_74;
    *hash.offset(2 as libc::c_uint as isize) = c1_74;
    *hash.offset(3 as libc::c_uint as isize) = d1_74;
    *hash.offset(4 as libc::c_uint as isize) = e1_74;
    *hash.offset(5 as libc::c_uint as isize) = f1_74;
    *hash.offset(6 as libc::c_uint as isize) = g1_74;
    *hash.offset(7 as libc::c_uint as isize) = h12_74;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_75: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_75: uint64_t = ws[i_7 as usize];
    let mut a0_75: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_75: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_75: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_75: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_75: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_75: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_75: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_75: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_75: uint64_t = k_t_75;
    let mut t1_75: uint64_t = h02_75
        .wrapping_add(
            (e0_75 << 50 as libc::c_uint | e0_75 >> 14 as libc::c_uint)
                ^ ((e0_75 << 46 as libc::c_uint | e0_75 >> 18 as libc::c_uint)
                    ^ (e0_75 << 23 as libc::c_uint | e0_75 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_75 & f0_75 ^ !e0_75 & g0_75)
        .wrapping_add(k_e_t_75)
        .wrapping_add(ws_t_75);
    let mut t2_139: uint64_t = ((a0_75 << 36 as libc::c_uint
        | a0_75 >> 28 as libc::c_uint)
        ^ ((a0_75 << 30 as libc::c_uint | a0_75 >> 34 as libc::c_uint)
            ^ (a0_75 << 25 as libc::c_uint | a0_75 >> 39 as libc::c_uint)))
        .wrapping_add(a0_75 & b0_75 ^ (a0_75 & c0_75 ^ b0_75 & c0_75));
    let mut a1_75: uint64_t = t1_75.wrapping_add(t2_139);
    let mut b1_75: uint64_t = a0_75;
    let mut c1_75: uint64_t = b0_75;
    let mut d1_75: uint64_t = c0_75;
    let mut e1_75: uint64_t = d0_75.wrapping_add(t1_75);
    let mut f1_75: uint64_t = e0_75;
    let mut g1_75: uint64_t = f0_75;
    let mut h12_75: uint64_t = g0_75;
    *hash.offset(0 as libc::c_uint as isize) = a1_75;
    *hash.offset(1 as libc::c_uint as isize) = b1_75;
    *hash.offset(2 as libc::c_uint as isize) = c1_75;
    *hash.offset(3 as libc::c_uint as isize) = d1_75;
    *hash.offset(4 as libc::c_uint as isize) = e1_75;
    *hash.offset(5 as libc::c_uint as isize) = f1_75;
    *hash.offset(6 as libc::c_uint as isize) = g1_75;
    *hash.offset(7 as libc::c_uint as isize) = h12_75;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_76: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_76: uint64_t = ws[i_7 as usize];
    let mut a0_76: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_76: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_76: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_76: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_76: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_76: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_76: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_76: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_76: uint64_t = k_t_76;
    let mut t1_76: uint64_t = h02_76
        .wrapping_add(
            (e0_76 << 50 as libc::c_uint | e0_76 >> 14 as libc::c_uint)
                ^ ((e0_76 << 46 as libc::c_uint | e0_76 >> 18 as libc::c_uint)
                    ^ (e0_76 << 23 as libc::c_uint | e0_76 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_76 & f0_76 ^ !e0_76 & g0_76)
        .wrapping_add(k_e_t_76)
        .wrapping_add(ws_t_76);
    let mut t2_140: uint64_t = ((a0_76 << 36 as libc::c_uint
        | a0_76 >> 28 as libc::c_uint)
        ^ ((a0_76 << 30 as libc::c_uint | a0_76 >> 34 as libc::c_uint)
            ^ (a0_76 << 25 as libc::c_uint | a0_76 >> 39 as libc::c_uint)))
        .wrapping_add(a0_76 & b0_76 ^ (a0_76 & c0_76 ^ b0_76 & c0_76));
    let mut a1_76: uint64_t = t1_76.wrapping_add(t2_140);
    let mut b1_76: uint64_t = a0_76;
    let mut c1_76: uint64_t = b0_76;
    let mut d1_76: uint64_t = c0_76;
    let mut e1_76: uint64_t = d0_76.wrapping_add(t1_76);
    let mut f1_76: uint64_t = e0_76;
    let mut g1_76: uint64_t = f0_76;
    let mut h12_76: uint64_t = g0_76;
    *hash.offset(0 as libc::c_uint as isize) = a1_76;
    *hash.offset(1 as libc::c_uint as isize) = b1_76;
    *hash.offset(2 as libc::c_uint as isize) = c1_76;
    *hash.offset(3 as libc::c_uint as isize) = d1_76;
    *hash.offset(4 as libc::c_uint as isize) = e1_76;
    *hash.offset(5 as libc::c_uint as isize) = f1_76;
    *hash.offset(6 as libc::c_uint as isize) = g1_76;
    *hash.offset(7 as libc::c_uint as isize) = h12_76;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_77: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_77: uint64_t = ws[i_7 as usize];
    let mut a0_77: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_77: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_77: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_77: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_77: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_77: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_77: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_77: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_77: uint64_t = k_t_77;
    let mut t1_77: uint64_t = h02_77
        .wrapping_add(
            (e0_77 << 50 as libc::c_uint | e0_77 >> 14 as libc::c_uint)
                ^ ((e0_77 << 46 as libc::c_uint | e0_77 >> 18 as libc::c_uint)
                    ^ (e0_77 << 23 as libc::c_uint | e0_77 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_77 & f0_77 ^ !e0_77 & g0_77)
        .wrapping_add(k_e_t_77)
        .wrapping_add(ws_t_77);
    let mut t2_141: uint64_t = ((a0_77 << 36 as libc::c_uint
        | a0_77 >> 28 as libc::c_uint)
        ^ ((a0_77 << 30 as libc::c_uint | a0_77 >> 34 as libc::c_uint)
            ^ (a0_77 << 25 as libc::c_uint | a0_77 >> 39 as libc::c_uint)))
        .wrapping_add(a0_77 & b0_77 ^ (a0_77 & c0_77 ^ b0_77 & c0_77));
    let mut a1_77: uint64_t = t1_77.wrapping_add(t2_141);
    let mut b1_77: uint64_t = a0_77;
    let mut c1_77: uint64_t = b0_77;
    let mut d1_77: uint64_t = c0_77;
    let mut e1_77: uint64_t = d0_77.wrapping_add(t1_77);
    let mut f1_77: uint64_t = e0_77;
    let mut g1_77: uint64_t = f0_77;
    let mut h12_77: uint64_t = g0_77;
    *hash.offset(0 as libc::c_uint as isize) = a1_77;
    *hash.offset(1 as libc::c_uint as isize) = b1_77;
    *hash.offset(2 as libc::c_uint as isize) = c1_77;
    *hash.offset(3 as libc::c_uint as isize) = d1_77;
    *hash.offset(4 as libc::c_uint as isize) = e1_77;
    *hash.offset(5 as libc::c_uint as isize) = f1_77;
    *hash.offset(6 as libc::c_uint as isize) = g1_77;
    *hash.offset(7 as libc::c_uint as isize) = h12_77;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut k_t_78: uint64_t = Hacl_Hash_SHA2_k384_512[(16 as libc::c_uint)
        .wrapping_mul(i0)
        .wrapping_add(i_7) as usize];
    let mut ws_t_78: uint64_t = ws[i_7 as usize];
    let mut a0_78: uint64_t = *hash.offset(0 as libc::c_uint as isize);
    let mut b0_78: uint64_t = *hash.offset(1 as libc::c_uint as isize);
    let mut c0_78: uint64_t = *hash.offset(2 as libc::c_uint as isize);
    let mut d0_78: uint64_t = *hash.offset(3 as libc::c_uint as isize);
    let mut e0_78: uint64_t = *hash.offset(4 as libc::c_uint as isize);
    let mut f0_78: uint64_t = *hash.offset(5 as libc::c_uint as isize);
    let mut g0_78: uint64_t = *hash.offset(6 as libc::c_uint as isize);
    let mut h02_78: uint64_t = *hash.offset(7 as libc::c_uint as isize);
    let mut k_e_t_78: uint64_t = k_t_78;
    let mut t1_78: uint64_t = h02_78
        .wrapping_add(
            (e0_78 << 50 as libc::c_uint | e0_78 >> 14 as libc::c_uint)
                ^ ((e0_78 << 46 as libc::c_uint | e0_78 >> 18 as libc::c_uint)
                    ^ (e0_78 << 23 as libc::c_uint | e0_78 >> 41 as libc::c_uint)),
        )
        .wrapping_add(e0_78 & f0_78 ^ !e0_78 & g0_78)
        .wrapping_add(k_e_t_78)
        .wrapping_add(ws_t_78);
    let mut t2_142: uint64_t = ((a0_78 << 36 as libc::c_uint
        | a0_78 >> 28 as libc::c_uint)
        ^ ((a0_78 << 30 as libc::c_uint | a0_78 >> 34 as libc::c_uint)
            ^ (a0_78 << 25 as libc::c_uint | a0_78 >> 39 as libc::c_uint)))
        .wrapping_add(a0_78 & b0_78 ^ (a0_78 & c0_78 ^ b0_78 & c0_78));
    let mut a1_78: uint64_t = t1_78.wrapping_add(t2_142);
    let mut b1_78: uint64_t = a0_78;
    let mut c1_78: uint64_t = b0_78;
    let mut d1_78: uint64_t = c0_78;
    let mut e1_78: uint64_t = d0_78.wrapping_add(t1_78);
    let mut f1_78: uint64_t = e0_78;
    let mut g1_78: uint64_t = f0_78;
    let mut h12_78: uint64_t = g0_78;
    *hash.offset(0 as libc::c_uint as isize) = a1_78;
    *hash.offset(1 as libc::c_uint as isize) = b1_78;
    *hash.offset(2 as libc::c_uint as isize) = c1_78;
    *hash.offset(3 as libc::c_uint as isize) = d1_78;
    *hash.offset(4 as libc::c_uint as isize) = e1_78;
    *hash.offset(5 as libc::c_uint as isize) = f1_78;
    *hash.offset(6 as libc::c_uint as isize) = g1_78;
    *hash.offset(7 as libc::c_uint as isize) = h12_78;
    i_7 = (i_7 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    if i0 < 4 as libc::c_uint {
        let mut i_8: uint32_t = 0 as libc::c_uint;
        let mut t16_63: uint64_t = ws[i_8 as usize];
        let mut t15_63: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_63: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_143: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_63: uint64_t = (t2_143 << 45 as libc::c_uint
            | t2_143 >> 19 as libc::c_uint)
            ^ ((t2_143 << 3 as libc::c_uint | t2_143 >> 61 as libc::c_uint)
                ^ t2_143 >> 6 as libc::c_uint);
        let mut s0_63: uint64_t = (t15_63 << 63 as libc::c_uint
            | t15_63 >> 1 as libc::c_uint)
            ^ ((t15_63 << 56 as libc::c_uint | t15_63 >> 8 as libc::c_uint)
                ^ t15_63 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_63
            .wrapping_add(t7_63)
            .wrapping_add(s0_63)
            .wrapping_add(t16_63);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_64: uint64_t = ws[i_8 as usize];
        let mut t15_64: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_64: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_144: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_64: uint64_t = (t2_144 << 45 as libc::c_uint
            | t2_144 >> 19 as libc::c_uint)
            ^ ((t2_144 << 3 as libc::c_uint | t2_144 >> 61 as libc::c_uint)
                ^ t2_144 >> 6 as libc::c_uint);
        let mut s0_64: uint64_t = (t15_64 << 63 as libc::c_uint
            | t15_64 >> 1 as libc::c_uint)
            ^ ((t15_64 << 56 as libc::c_uint | t15_64 >> 8 as libc::c_uint)
                ^ t15_64 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_64
            .wrapping_add(t7_64)
            .wrapping_add(s0_64)
            .wrapping_add(t16_64);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_65: uint64_t = ws[i_8 as usize];
        let mut t15_65: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_65: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_145: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_65: uint64_t = (t2_145 << 45 as libc::c_uint
            | t2_145 >> 19 as libc::c_uint)
            ^ ((t2_145 << 3 as libc::c_uint | t2_145 >> 61 as libc::c_uint)
                ^ t2_145 >> 6 as libc::c_uint);
        let mut s0_65: uint64_t = (t15_65 << 63 as libc::c_uint
            | t15_65 >> 1 as libc::c_uint)
            ^ ((t15_65 << 56 as libc::c_uint | t15_65 >> 8 as libc::c_uint)
                ^ t15_65 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_65
            .wrapping_add(t7_65)
            .wrapping_add(s0_65)
            .wrapping_add(t16_65);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_66: uint64_t = ws[i_8 as usize];
        let mut t15_66: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_66: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_146: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_66: uint64_t = (t2_146 << 45 as libc::c_uint
            | t2_146 >> 19 as libc::c_uint)
            ^ ((t2_146 << 3 as libc::c_uint | t2_146 >> 61 as libc::c_uint)
                ^ t2_146 >> 6 as libc::c_uint);
        let mut s0_66: uint64_t = (t15_66 << 63 as libc::c_uint
            | t15_66 >> 1 as libc::c_uint)
            ^ ((t15_66 << 56 as libc::c_uint | t15_66 >> 8 as libc::c_uint)
                ^ t15_66 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_66
            .wrapping_add(t7_66)
            .wrapping_add(s0_66)
            .wrapping_add(t16_66);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_67: uint64_t = ws[i_8 as usize];
        let mut t15_67: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_67: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_147: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_67: uint64_t = (t2_147 << 45 as libc::c_uint
            | t2_147 >> 19 as libc::c_uint)
            ^ ((t2_147 << 3 as libc::c_uint | t2_147 >> 61 as libc::c_uint)
                ^ t2_147 >> 6 as libc::c_uint);
        let mut s0_67: uint64_t = (t15_67 << 63 as libc::c_uint
            | t15_67 >> 1 as libc::c_uint)
            ^ ((t15_67 << 56 as libc::c_uint | t15_67 >> 8 as libc::c_uint)
                ^ t15_67 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_67
            .wrapping_add(t7_67)
            .wrapping_add(s0_67)
            .wrapping_add(t16_67);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_68: uint64_t = ws[i_8 as usize];
        let mut t15_68: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_68: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_148: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_68: uint64_t = (t2_148 << 45 as libc::c_uint
            | t2_148 >> 19 as libc::c_uint)
            ^ ((t2_148 << 3 as libc::c_uint | t2_148 >> 61 as libc::c_uint)
                ^ t2_148 >> 6 as libc::c_uint);
        let mut s0_68: uint64_t = (t15_68 << 63 as libc::c_uint
            | t15_68 >> 1 as libc::c_uint)
            ^ ((t15_68 << 56 as libc::c_uint | t15_68 >> 8 as libc::c_uint)
                ^ t15_68 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_68
            .wrapping_add(t7_68)
            .wrapping_add(s0_68)
            .wrapping_add(t16_68);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_69: uint64_t = ws[i_8 as usize];
        let mut t15_69: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_69: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_149: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_69: uint64_t = (t2_149 << 45 as libc::c_uint
            | t2_149 >> 19 as libc::c_uint)
            ^ ((t2_149 << 3 as libc::c_uint | t2_149 >> 61 as libc::c_uint)
                ^ t2_149 >> 6 as libc::c_uint);
        let mut s0_69: uint64_t = (t15_69 << 63 as libc::c_uint
            | t15_69 >> 1 as libc::c_uint)
            ^ ((t15_69 << 56 as libc::c_uint | t15_69 >> 8 as libc::c_uint)
                ^ t15_69 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_69
            .wrapping_add(t7_69)
            .wrapping_add(s0_69)
            .wrapping_add(t16_69);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_70: uint64_t = ws[i_8 as usize];
        let mut t15_70: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_70: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_150: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_70: uint64_t = (t2_150 << 45 as libc::c_uint
            | t2_150 >> 19 as libc::c_uint)
            ^ ((t2_150 << 3 as libc::c_uint | t2_150 >> 61 as libc::c_uint)
                ^ t2_150 >> 6 as libc::c_uint);
        let mut s0_70: uint64_t = (t15_70 << 63 as libc::c_uint
            | t15_70 >> 1 as libc::c_uint)
            ^ ((t15_70 << 56 as libc::c_uint | t15_70 >> 8 as libc::c_uint)
                ^ t15_70 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_70
            .wrapping_add(t7_70)
            .wrapping_add(s0_70)
            .wrapping_add(t16_70);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_71: uint64_t = ws[i_8 as usize];
        let mut t15_71: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_71: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_151: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_71: uint64_t = (t2_151 << 45 as libc::c_uint
            | t2_151 >> 19 as libc::c_uint)
            ^ ((t2_151 << 3 as libc::c_uint | t2_151 >> 61 as libc::c_uint)
                ^ t2_151 >> 6 as libc::c_uint);
        let mut s0_71: uint64_t = (t15_71 << 63 as libc::c_uint
            | t15_71 >> 1 as libc::c_uint)
            ^ ((t15_71 << 56 as libc::c_uint | t15_71 >> 8 as libc::c_uint)
                ^ t15_71 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_71
            .wrapping_add(t7_71)
            .wrapping_add(s0_71)
            .wrapping_add(t16_71);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_72: uint64_t = ws[i_8 as usize];
        let mut t15_72: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_72: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_152: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_72: uint64_t = (t2_152 << 45 as libc::c_uint
            | t2_152 >> 19 as libc::c_uint)
            ^ ((t2_152 << 3 as libc::c_uint | t2_152 >> 61 as libc::c_uint)
                ^ t2_152 >> 6 as libc::c_uint);
        let mut s0_72: uint64_t = (t15_72 << 63 as libc::c_uint
            | t15_72 >> 1 as libc::c_uint)
            ^ ((t15_72 << 56 as libc::c_uint | t15_72 >> 8 as libc::c_uint)
                ^ t15_72 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_72
            .wrapping_add(t7_72)
            .wrapping_add(s0_72)
            .wrapping_add(t16_72);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_73: uint64_t = ws[i_8 as usize];
        let mut t15_73: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_73: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_153: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_73: uint64_t = (t2_153 << 45 as libc::c_uint
            | t2_153 >> 19 as libc::c_uint)
            ^ ((t2_153 << 3 as libc::c_uint | t2_153 >> 61 as libc::c_uint)
                ^ t2_153 >> 6 as libc::c_uint);
        let mut s0_73: uint64_t = (t15_73 << 63 as libc::c_uint
            | t15_73 >> 1 as libc::c_uint)
            ^ ((t15_73 << 56 as libc::c_uint | t15_73 >> 8 as libc::c_uint)
                ^ t15_73 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_73
            .wrapping_add(t7_73)
            .wrapping_add(s0_73)
            .wrapping_add(t16_73);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_74: uint64_t = ws[i_8 as usize];
        let mut t15_74: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_74: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_154: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_74: uint64_t = (t2_154 << 45 as libc::c_uint
            | t2_154 >> 19 as libc::c_uint)
            ^ ((t2_154 << 3 as libc::c_uint | t2_154 >> 61 as libc::c_uint)
                ^ t2_154 >> 6 as libc::c_uint);
        let mut s0_74: uint64_t = (t15_74 << 63 as libc::c_uint
            | t15_74 >> 1 as libc::c_uint)
            ^ ((t15_74 << 56 as libc::c_uint | t15_74 >> 8 as libc::c_uint)
                ^ t15_74 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_74
            .wrapping_add(t7_74)
            .wrapping_add(s0_74)
            .wrapping_add(t16_74);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_75: uint64_t = ws[i_8 as usize];
        let mut t15_75: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_75: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_155: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_75: uint64_t = (t2_155 << 45 as libc::c_uint
            | t2_155 >> 19 as libc::c_uint)
            ^ ((t2_155 << 3 as libc::c_uint | t2_155 >> 61 as libc::c_uint)
                ^ t2_155 >> 6 as libc::c_uint);
        let mut s0_75: uint64_t = (t15_75 << 63 as libc::c_uint
            | t15_75 >> 1 as libc::c_uint)
            ^ ((t15_75 << 56 as libc::c_uint | t15_75 >> 8 as libc::c_uint)
                ^ t15_75 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_75
            .wrapping_add(t7_75)
            .wrapping_add(s0_75)
            .wrapping_add(t16_75);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_76: uint64_t = ws[i_8 as usize];
        let mut t15_76: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_76: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_156: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_76: uint64_t = (t2_156 << 45 as libc::c_uint
            | t2_156 >> 19 as libc::c_uint)
            ^ ((t2_156 << 3 as libc::c_uint | t2_156 >> 61 as libc::c_uint)
                ^ t2_156 >> 6 as libc::c_uint);
        let mut s0_76: uint64_t = (t15_76 << 63 as libc::c_uint
            | t15_76 >> 1 as libc::c_uint)
            ^ ((t15_76 << 56 as libc::c_uint | t15_76 >> 8 as libc::c_uint)
                ^ t15_76 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_76
            .wrapping_add(t7_76)
            .wrapping_add(s0_76)
            .wrapping_add(t16_76);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_77: uint64_t = ws[i_8 as usize];
        let mut t15_77: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_77: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_157: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_77: uint64_t = (t2_157 << 45 as libc::c_uint
            | t2_157 >> 19 as libc::c_uint)
            ^ ((t2_157 << 3 as libc::c_uint | t2_157 >> 61 as libc::c_uint)
                ^ t2_157 >> 6 as libc::c_uint);
        let mut s0_77: uint64_t = (t15_77 << 63 as libc::c_uint
            | t15_77 >> 1 as libc::c_uint)
            ^ ((t15_77 << 56 as libc::c_uint | t15_77 >> 8 as libc::c_uint)
                ^ t15_77 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_77
            .wrapping_add(t7_77)
            .wrapping_add(s0_77)
            .wrapping_add(t16_77);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
        let mut t16_78: uint64_t = ws[i_8 as usize];
        let mut t15_78: uint64_t = ws[i_8
            .wrapping_add(1 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t7_78: uint64_t = ws[i_8
            .wrapping_add(9 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut t2_158: uint64_t = ws[i_8
            .wrapping_add(14 as libc::c_uint)
            .wrapping_rem(16 as libc::c_uint) as usize];
        let mut s1_78: uint64_t = (t2_158 << 45 as libc::c_uint
            | t2_158 >> 19 as libc::c_uint)
            ^ ((t2_158 << 3 as libc::c_uint | t2_158 >> 61 as libc::c_uint)
                ^ t2_158 >> 6 as libc::c_uint);
        let mut s0_78: uint64_t = (t15_78 << 63 as libc::c_uint
            | t15_78 >> 1 as libc::c_uint)
            ^ ((t15_78 << 56 as libc::c_uint | t15_78 >> 8 as libc::c_uint)
                ^ t15_78 >> 7 as libc::c_uint);
        ws[i_8
            as usize] = s1_78
            .wrapping_add(t7_78)
            .wrapping_add(s0_78)
            .wrapping_add(t16_78);
        i_8 = (i_8 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t
            as uint32_t;
    }
    i0 = (i0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut i_9: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os: *mut uint64_t = hash;
    *os.offset(i_9 as isize) = x;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_0: *mut uint64_t = hash;
    *os_0.offset(i_9 as isize) = x_0;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_1: *mut uint64_t = hash;
    *os_1.offset(i_9 as isize) = x_1;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_2: *mut uint64_t = hash;
    *os_2.offset(i_9 as isize) = x_2;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_3: *mut uint64_t = hash;
    *os_3.offset(i_9 as isize) = x_3;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_4: *mut uint64_t = hash;
    *os_4.offset(i_9 as isize) = x_4;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_5: *mut uint64_t = hash;
    *os_5.offset(i_9 as isize) = x_5;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint64_t = (*hash.offset(i_9 as isize))
        .wrapping_add(hash_old[i_9 as usize]);
    let mut os_6: *mut uint64_t = hash;
    *os_6.offset(i_9 as isize) = x_6;
    i_9 = (i_9 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha512_update_nblocks(
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut st: *mut uint64_t,
) {
    let mut blocks: uint32_t = len.wrapping_div(128 as libc::c_uint);
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < blocks {
        let mut b0: *mut uint8_t = b;
        let mut mb: *mut uint8_t = b0
            .offset(i.wrapping_mul(128 as libc::c_uint) as isize);
        sha512_update(mb, st);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha512_update_last(
    mut totlen: FStar_UInt128_uint128,
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut hash: *mut uint64_t,
) {
    let mut blocks: uint32_t = 0;
    if len.wrapping_add(16 as libc::c_uint).wrapping_add(1 as libc::c_uint)
        <= 128 as libc::c_uint
    {
        blocks = 1 as libc::c_uint;
    } else {
        blocks = 2 as libc::c_uint;
    }
    let mut fin: uint32_t = blocks.wrapping_mul(128 as libc::c_uint);
    let mut last: [uint8_t; 256] = [
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
    let mut totlen_buf: [uint8_t; 16] = [
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
    ];
    let mut total_len_bits: FStar_UInt128_uint128 = FStar_UInt128_shift_left(
        totlen,
        3 as libc::c_uint,
    );
    store128_be(totlen_buf.as_mut_ptr(), total_len_bits);
    let mut b0: *mut uint8_t = b;
    memcpy(
        last.as_mut_ptr() as *mut libc::c_void,
        b0 as *const libc::c_void,
        (len as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    last[len as usize] = 0x80 as libc::c_uint as uint8_t;
    memcpy(
        last.as_mut_ptr().offset(fin as isize).offset(-(16 as libc::c_uint as isize))
            as *mut libc::c_void,
        totlen_buf.as_mut_ptr() as *const libc::c_void,
        (16 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut last00: *mut uint8_t = last.as_mut_ptr();
    let mut last10: *mut uint8_t = last
        .as_mut_ptr()
        .offset(128 as libc::c_uint as isize);
    let mut l0: *mut uint8_t = last00;
    let mut l1: *mut uint8_t = last10;
    let mut lb0: *mut uint8_t = l0;
    let mut lb1: *mut uint8_t = l1;
    let mut last0: *mut uint8_t = lb0;
    let mut last1: *mut uint8_t = lb1;
    sha512_update(last0, hash);
    if blocks > 1 as libc::c_uint {
        sha512_update(last1, hash);
        return;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha512_finish(
    mut st: *mut uint64_t,
    mut h: *mut uint8_t,
) {
    let mut hbuf: [uint8_t; 64] = [
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
    let mut i: uint32_t = 0 as libc::c_uint;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        h as *mut libc::c_void,
        hbuf.as_mut_ptr() as *const libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha384_init(mut hash: *mut uint64_t) {
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut x: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os: *mut uint64_t = hash;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_0: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_0: *mut uint64_t = hash;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_1: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_1: *mut uint64_t = hash;
    *os_1.offset(i as isize) = x_1;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_2: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_2: *mut uint64_t = hash;
    *os_2.offset(i as isize) = x_2;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_3: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_3: *mut uint64_t = hash;
    *os_3.offset(i as isize) = x_3;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_4: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_4: *mut uint64_t = hash;
    *os_4.offset(i as isize) = x_4;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_5: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_5: *mut uint64_t = hash;
    *os_5.offset(i as isize) = x_5;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut x_6: uint64_t = Hacl_Hash_SHA2_h384[i as usize];
    let mut os_6: *mut uint64_t = hash;
    *os_6.offset(i as isize) = x_6;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha384_update_nblocks(
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut st: *mut uint64_t,
) {
    Hacl_Hash_SHA2_sha512_update_nblocks(len, b, st);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha384_update_last(
    mut totlen: FStar_UInt128_uint128,
    mut len: uint32_t,
    mut b: *mut uint8_t,
    mut st: *mut uint64_t,
) {
    Hacl_Hash_SHA2_sha512_update_last(totlen, len, b, st);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_sha384_finish(
    mut st: *mut uint64_t,
    mut h: *mut uint8_t,
) {
    let mut hbuf: [uint8_t; 64] = [
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
    let mut i: uint32_t = 0 as libc::c_uint;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    store64(
        hbuf.as_mut_ptr().offset(i.wrapping_mul(8 as libc::c_uint) as isize),
        if 0 != 0 {
            (*st.offset(i as isize) & 0xff00000000000000 as libc::c_ulonglong)
                >> 56 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000000000 as libc::c_ulonglong)
                    >> 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000000000 as libc::c_ulonglong)
                    >> 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00000000 as libc::c_ulonglong)
                    >> 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff000000 as libc::c_ulonglong)
                    << 8 as libc::c_int
                | (*st.offset(i as isize) & 0xff0000 as libc::c_ulonglong)
                    << 24 as libc::c_int
                | (*st.offset(i as isize) & 0xff00 as libc::c_ulonglong)
                    << 40 as libc::c_int
                | (*st.offset(i as isize) & 0xff as libc::c_ulonglong)
                    << 56 as libc::c_int
        } else {
            _OSSwapInt64(*st.offset(i as isize))
        },
    );
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    memcpy(
        h as *mut libc::c_void,
        hbuf.as_mut_ptr() as *const libc::c_void,
        (48 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_malloc_256() -> *mut Hacl_Streaming_MD_state_32 {
    let mut buf: *mut uint8_t = calloc(
        64 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut block_state: *mut uint32_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    Hacl_Hash_SHA2_sha256_init(block_state);
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
pub unsafe extern "C" fn Hacl_Hash_SHA2_copy_256(
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
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    memcpy(
        block_state as *mut libc::c_void,
        block_state0 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
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
pub unsafe extern "C" fn Hacl_Hash_SHA2_reset_256(
    mut state: *mut Hacl_Streaming_MD_state_32,
) {
    let mut block_state: *mut uint32_t = (*state).block_state;
    Hacl_Hash_SHA2_sha256_init(block_state);
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[inline]
unsafe extern "C" fn update_224_256(
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
            Hacl_Hash_SHA2_sha256_update_nblocks(64 as libc::c_uint, buf_0, block_state);
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
        Hacl_Hash_SHA2_sha256_update_nblocks(
            data1_len.wrapping_div(64 as libc::c_uint).wrapping_mul(64 as libc::c_uint),
            data1,
            block_state,
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
            Hacl_Hash_SHA2_sha256_update_nblocks(64 as libc::c_uint, buf0, block_state);
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
        Hacl_Hash_SHA2_sha256_update_nblocks(
            data1_len_0
                .wrapping_div(64 as libc::c_uint)
                .wrapping_mul(64 as libc::c_uint),
            data1_0,
            block_state,
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
pub unsafe extern "C" fn Hacl_Hash_SHA2_update_256(
    mut state: *mut Hacl_Streaming_MD_state_32,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    return update_224_256(state, input, input_len);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_digest_256(
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
    let mut tmp_block_state: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        tmp_block_state.as_mut_ptr() as *mut libc::c_void,
        block_state as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
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
    Hacl_Hash_SHA2_sha256_update_nblocks(
        0 as libc::c_uint,
        buf_multi,
        tmp_block_state.as_mut_ptr(),
    );
    let mut prev_len_last: uint64_t = total_len.wrapping_sub(r as uint64_t);
    Hacl_Hash_SHA2_sha256_update_last(
        prev_len_last.wrapping_add(r as uint64_t),
        r,
        buf_last,
        tmp_block_state.as_mut_ptr(),
    );
    Hacl_Hash_SHA2_sha256_finish(tmp_block_state.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_free_256(
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
pub unsafe extern "C" fn Hacl_Hash_SHA2_hash_256(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut st: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Hash_SHA2_sha256_init(st.as_mut_ptr());
    let mut rem: uint32_t = input_len.wrapping_rem(64 as libc::c_uint);
    let mut len_: uint64_t = input_len as uint64_t;
    Hacl_Hash_SHA2_sha256_update_nblocks(input_len, ib, st.as_mut_ptr());
    let mut rem1: uint32_t = input_len.wrapping_rem(64 as libc::c_uint);
    let mut b0: *mut uint8_t = ib;
    let mut lb: *mut uint8_t = b0.offset(input_len as isize).offset(-(rem1 as isize));
    Hacl_Hash_SHA2_sha256_update_last(len_, rem, lb, st.as_mut_ptr());
    Hacl_Hash_SHA2_sha256_finish(st.as_mut_ptr(), rb);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_malloc_224() -> *mut Hacl_Streaming_MD_state_32 {
    let mut buf: *mut uint8_t = calloc(
        64 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut block_state: *mut uint32_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint32_t>() as libc::c_ulong,
    ) as *mut uint32_t;
    Hacl_Hash_SHA2_sha224_init(block_state);
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
pub unsafe extern "C" fn Hacl_Hash_SHA2_reset_224(
    mut state: *mut Hacl_Streaming_MD_state_32,
) {
    let mut block_state: *mut uint32_t = (*state).block_state;
    Hacl_Hash_SHA2_sha224_init(block_state);
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_update_224(
    mut state: *mut Hacl_Streaming_MD_state_32,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    return update_224_256(state, input, input_len);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_digest_224(
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
    let mut tmp_block_state: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    memcpy(
        tmp_block_state.as_mut_ptr() as *mut libc::c_void,
        block_state as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
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
    Hacl_Hash_SHA2_sha224_update_nblocks(
        0 as libc::c_uint,
        buf_multi,
        tmp_block_state.as_mut_ptr(),
    );
    let mut prev_len_last: uint64_t = total_len.wrapping_sub(r as uint64_t);
    Hacl_Hash_SHA2_sha224_update_last(
        prev_len_last.wrapping_add(r as uint64_t),
        r,
        buf_last,
        tmp_block_state.as_mut_ptr(),
    );
    Hacl_Hash_SHA2_sha224_finish(tmp_block_state.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_free_224(
    mut state: *mut Hacl_Streaming_MD_state_32,
) {
    Hacl_Hash_SHA2_free_256(state);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_hash_224(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut st: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Hash_SHA2_sha224_init(st.as_mut_ptr());
    let mut rem: uint32_t = input_len.wrapping_rem(64 as libc::c_uint);
    let mut len_: uint64_t = input_len as uint64_t;
    Hacl_Hash_SHA2_sha224_update_nblocks(input_len, ib, st.as_mut_ptr());
    let mut rem1: uint32_t = input_len.wrapping_rem(64 as libc::c_uint);
    let mut b0: *mut uint8_t = ib;
    let mut lb: *mut uint8_t = b0.offset(input_len as isize).offset(-(rem1 as isize));
    Hacl_Hash_SHA2_sha224_update_last(len_, rem, lb, st.as_mut_ptr());
    Hacl_Hash_SHA2_sha224_finish(st.as_mut_ptr(), rb);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_malloc_512() -> *mut Hacl_Streaming_MD_state_64 {
    let mut buf: *mut uint8_t = calloc(
        128 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut block_state: *mut uint64_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    Hacl_Hash_SHA2_sha512_init(block_state);
    let mut s: Hacl_Streaming_MD_state_64 = {
        let mut init = Hacl_Streaming_MD_state_64_s {
            block_state: block_state,
            buf: buf,
            total_len: 0 as libc::c_uint as uint64_t,
        };
        init
    };
    let mut p: *mut Hacl_Streaming_MD_state_64 = malloc(
        ::core::mem::size_of::<Hacl_Streaming_MD_state_64>() as libc::c_ulong,
    ) as *mut Hacl_Streaming_MD_state_64;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_copy_512(
    mut state: *mut Hacl_Streaming_MD_state_64,
) -> *mut Hacl_Streaming_MD_state_64 {
    let mut block_state0: *mut uint64_t = (*state).block_state;
    let mut buf0: *mut uint8_t = (*state).buf;
    let mut total_len0: uint64_t = (*state).total_len;
    let mut buf: *mut uint8_t = calloc(
        128 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    memcpy(
        buf as *mut libc::c_void,
        buf0 as *const libc::c_void,
        (128 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut block_state: *mut uint64_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    memcpy(
        block_state as *mut libc::c_void,
        block_state0 as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut s: Hacl_Streaming_MD_state_64 = {
        let mut init = Hacl_Streaming_MD_state_64_s {
            block_state: block_state,
            buf: buf,
            total_len: total_len0,
        };
        init
    };
    let mut p: *mut Hacl_Streaming_MD_state_64 = malloc(
        ::core::mem::size_of::<Hacl_Streaming_MD_state_64>() as libc::c_ulong,
    ) as *mut Hacl_Streaming_MD_state_64;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_reset_512(
    mut state: *mut Hacl_Streaming_MD_state_64,
) {
    let mut block_state: *mut uint64_t = (*state).block_state;
    Hacl_Hash_SHA2_sha512_init(block_state);
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[inline]
unsafe extern "C" fn update_384_512(
    mut state: *mut Hacl_Streaming_MD_state_64,
    mut chunk: *mut uint8_t,
    mut chunk_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut block_state: *mut uint64_t = (*state).block_state;
    let mut total_len: uint64_t = (*state).total_len;
    if chunk_len as uint64_t
        > (18446744073709551615 as libc::c_ulonglong).wrapping_sub(total_len)
    {
        return 3 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    let mut sz: uint32_t = 0;
    if total_len % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        sz = 128 as libc::c_uint;
    } else {
        sz = (total_len % 128 as libc::c_uint as uint64_t) as uint32_t;
    }
    if chunk_len <= (128 as libc::c_uint).wrapping_sub(sz) {
        let mut buf: *mut uint8_t = (*state).buf;
        let mut total_len1: uint64_t = (*state).total_len;
        let mut sz1: uint32_t = 0;
        if total_len1 % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1 > 0 as libc::c_ulonglong
        {
            sz1 = 128 as libc::c_uint;
        } else {
            sz1 = (total_len1 % 128 as libc::c_uint as uint64_t) as uint32_t;
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
        if total_len1_0 % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_0 > 0 as libc::c_ulonglong
        {
            sz1_0 = 128 as libc::c_uint;
        } else {
            sz1_0 = (total_len1_0 % 128 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_0 == 0 as libc::c_uint) {
            Hacl_Hash_SHA2_sha512_update_nblocks(
                128 as libc::c_uint,
                buf_0,
                block_state,
            );
        }
        let mut ite: uint32_t = 0;
        if chunk_len as uint64_t % 128 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong && chunk_len as uint64_t > 0 as libc::c_ulonglong
        {
            ite = 128 as libc::c_uint;
        } else {
            ite = (chunk_len as uint64_t % 128 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks: uint32_t = chunk_len
            .wrapping_sub(ite)
            .wrapping_div(128 as libc::c_uint);
        let mut data1_len: uint32_t = n_blocks.wrapping_mul(128 as libc::c_uint);
        let mut data2_len: uint32_t = chunk_len.wrapping_sub(data1_len);
        let mut data1: *mut uint8_t = chunk;
        let mut data2: *mut uint8_t = chunk.offset(data1_len as isize);
        Hacl_Hash_SHA2_sha512_update_nblocks(
            data1_len
                .wrapping_div(128 as libc::c_uint)
                .wrapping_mul(128 as libc::c_uint),
            data1,
            block_state,
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
        let mut diff: uint32_t = (128 as libc::c_uint).wrapping_sub(sz);
        let mut chunk1: *mut uint8_t = chunk;
        let mut chunk2: *mut uint8_t = chunk.offset(diff as isize);
        let mut buf_1: *mut uint8_t = (*state).buf;
        let mut total_len10: uint64_t = (*state).total_len;
        let mut sz10: uint32_t = 0;
        if total_len10 % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len10 > 0 as libc::c_ulonglong
        {
            sz10 = 128 as libc::c_uint;
        } else {
            sz10 = (total_len10 % 128 as libc::c_uint as uint64_t) as uint32_t;
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
        if total_len1_1 % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_1 > 0 as libc::c_ulonglong
        {
            sz1_1 = 128 as libc::c_uint;
        } else {
            sz1_1 = (total_len1_1 % 128 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_1 == 0 as libc::c_uint) {
            Hacl_Hash_SHA2_sha512_update_nblocks(128 as libc::c_uint, buf0, block_state);
        }
        let mut ite_0: uint32_t = 0;
        if chunk_len.wrapping_sub(diff) as uint64_t % 128 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong
            && chunk_len.wrapping_sub(diff) as uint64_t > 0 as libc::c_ulonglong
        {
            ite_0 = 128 as libc::c_uint;
        } else {
            ite_0 = (chunk_len.wrapping_sub(diff) as uint64_t
                % 128 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(ite_0)
            .wrapping_div(128 as libc::c_uint);
        let mut data1_len_0: uint32_t = n_blocks_0.wrapping_mul(128 as libc::c_uint);
        let mut data2_len_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(data1_len_0);
        let mut data1_0: *mut uint8_t = chunk2;
        let mut data2_0: *mut uint8_t = chunk2.offset(data1_len_0 as isize);
        Hacl_Hash_SHA2_sha512_update_nblocks(
            data1_len_0
                .wrapping_div(128 as libc::c_uint)
                .wrapping_mul(128 as libc::c_uint),
            data1_0,
            block_state,
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
pub unsafe extern "C" fn Hacl_Hash_SHA2_update_512(
    mut state: *mut Hacl_Streaming_MD_state_64,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    return update_384_512(state, input, input_len);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_digest_512(
    mut state: *mut Hacl_Streaming_MD_state_64,
    mut output: *mut uint8_t,
) {
    let mut block_state: *mut uint64_t = (*state).block_state;
    let mut buf_: *mut uint8_t = (*state).buf;
    let mut total_len: uint64_t = (*state).total_len;
    let mut r: uint32_t = 0;
    if total_len % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        r = 128 as libc::c_uint;
    } else {
        r = (total_len % 128 as libc::c_uint as uint64_t) as uint32_t;
    }
    let mut buf_1: *mut uint8_t = buf_;
    let mut tmp_block_state: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        tmp_block_state.as_mut_ptr() as *mut libc::c_void,
        block_state as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut buf_multi: *mut uint8_t = buf_1;
    let mut ite: uint32_t = 0;
    if r.wrapping_rem(128 as libc::c_uint) == 0 as libc::c_uint && r > 0 as libc::c_uint
    {
        ite = 128 as libc::c_uint;
    } else {
        ite = r.wrapping_rem(128 as libc::c_uint);
    }
    let mut buf_last: *mut uint8_t = buf_1.offset(r as isize).offset(-(ite as isize));
    Hacl_Hash_SHA2_sha512_update_nblocks(
        0 as libc::c_uint,
        buf_multi,
        tmp_block_state.as_mut_ptr(),
    );
    let mut prev_len_last: uint64_t = total_len.wrapping_sub(r as uint64_t);
    Hacl_Hash_SHA2_sha512_update_last(
        FStar_UInt128_add(
            FStar_UInt128_uint64_to_uint128(prev_len_last),
            FStar_UInt128_uint64_to_uint128(r as uint64_t),
        ),
        r,
        buf_last,
        tmp_block_state.as_mut_ptr(),
    );
    Hacl_Hash_SHA2_sha512_finish(tmp_block_state.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_free_512(
    mut state: *mut Hacl_Streaming_MD_state_64,
) {
    let mut scrut: Hacl_Streaming_MD_state_64 = *state;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: *mut uint64_t = scrut.block_state;
    free(block_state as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_hash_512(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut st: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Hash_SHA2_sha512_init(st.as_mut_ptr());
    let mut rem: uint32_t = input_len.wrapping_rem(128 as libc::c_uint);
    let mut len_: FStar_UInt128_uint128 = FStar_UInt128_uint64_to_uint128(
        input_len as uint64_t,
    );
    Hacl_Hash_SHA2_sha512_update_nblocks(input_len, ib, st.as_mut_ptr());
    let mut rem1: uint32_t = input_len.wrapping_rem(128 as libc::c_uint);
    let mut b0: *mut uint8_t = ib;
    let mut lb: *mut uint8_t = b0.offset(input_len as isize).offset(-(rem1 as isize));
    Hacl_Hash_SHA2_sha512_update_last(len_, rem, lb, st.as_mut_ptr());
    Hacl_Hash_SHA2_sha512_finish(st.as_mut_ptr(), rb);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_malloc_384() -> *mut Hacl_Streaming_MD_state_64 {
    let mut buf: *mut uint8_t = calloc(
        128 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut block_state: *mut uint64_t = calloc(
        8 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint64_t>() as libc::c_ulong,
    ) as *mut uint64_t;
    Hacl_Hash_SHA2_sha384_init(block_state);
    let mut s: Hacl_Streaming_MD_state_64 = {
        let mut init = Hacl_Streaming_MD_state_64_s {
            block_state: block_state,
            buf: buf,
            total_len: 0 as libc::c_uint as uint64_t,
        };
        init
    };
    let mut p: *mut Hacl_Streaming_MD_state_64 = malloc(
        ::core::mem::size_of::<Hacl_Streaming_MD_state_64>() as libc::c_ulong,
    ) as *mut Hacl_Streaming_MD_state_64;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_reset_384(
    mut state: *mut Hacl_Streaming_MD_state_64,
) {
    let mut block_state: *mut uint64_t = (*state).block_state;
    Hacl_Hash_SHA2_sha384_init(block_state);
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_update_384(
    mut state: *mut Hacl_Streaming_MD_state_64,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    return update_384_512(state, input, input_len);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_digest_384(
    mut state: *mut Hacl_Streaming_MD_state_64,
    mut output: *mut uint8_t,
) {
    let mut block_state: *mut uint64_t = (*state).block_state;
    let mut buf_: *mut uint8_t = (*state).buf;
    let mut total_len: uint64_t = (*state).total_len;
    let mut r: uint32_t = 0;
    if total_len % 128 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        r = 128 as libc::c_uint;
    } else {
        r = (total_len % 128 as libc::c_uint as uint64_t) as uint32_t;
    }
    let mut buf_1: *mut uint8_t = buf_;
    let mut tmp_block_state: [uint64_t; 8] = [
        0 as libc::c_uint as uint64_t,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
    memcpy(
        tmp_block_state.as_mut_ptr() as *mut libc::c_void,
        block_state as *const libc::c_void,
        (8 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint64_t>() as libc::c_ulong),
    );
    let mut buf_multi: *mut uint8_t = buf_1;
    let mut ite: uint32_t = 0;
    if r.wrapping_rem(128 as libc::c_uint) == 0 as libc::c_uint && r > 0 as libc::c_uint
    {
        ite = 128 as libc::c_uint;
    } else {
        ite = r.wrapping_rem(128 as libc::c_uint);
    }
    let mut buf_last: *mut uint8_t = buf_1.offset(r as isize).offset(-(ite as isize));
    Hacl_Hash_SHA2_sha384_update_nblocks(
        0 as libc::c_uint,
        buf_multi,
        tmp_block_state.as_mut_ptr(),
    );
    let mut prev_len_last: uint64_t = total_len.wrapping_sub(r as uint64_t);
    Hacl_Hash_SHA2_sha384_update_last(
        FStar_UInt128_add(
            FStar_UInt128_uint64_to_uint128(prev_len_last),
            FStar_UInt128_uint64_to_uint128(r as uint64_t),
        ),
        r,
        buf_last,
        tmp_block_state.as_mut_ptr(),
    );
    Hacl_Hash_SHA2_sha384_finish(tmp_block_state.as_mut_ptr(), output);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_free_384(
    mut state: *mut Hacl_Streaming_MD_state_64,
) {
    Hacl_Hash_SHA2_free_512(state);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_SHA2_hash_384(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
) {
    let mut ib: *mut uint8_t = input;
    let mut rb: *mut uint8_t = output;
    let mut st: [uint64_t; 8] = [0 as libc::c_uint as uint64_t, 0, 0, 0, 0, 0, 0, 0];
    Hacl_Hash_SHA2_sha384_init(st.as_mut_ptr());
    let mut rem: uint32_t = input_len.wrapping_rem(128 as libc::c_uint);
    let mut len_: FStar_UInt128_uint128 = FStar_UInt128_uint64_to_uint128(
        input_len as uint64_t,
    );
    Hacl_Hash_SHA2_sha384_update_nblocks(input_len, ib, st.as_mut_ptr());
    let mut rem1: uint32_t = input_len.wrapping_rem(128 as libc::c_uint);
    let mut b0: *mut uint8_t = ib;
    let mut lb: *mut uint8_t = b0.offset(input_len as isize).offset(-(rem1 as isize));
    Hacl_Hash_SHA2_sha384_update_last(len_, rem, lb, st.as_mut_ptr());
    Hacl_Hash_SHA2_sha384_finish(st.as_mut_ptr(), rb);
}
