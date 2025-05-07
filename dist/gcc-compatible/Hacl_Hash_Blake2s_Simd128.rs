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
    fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn free(_: *mut libc::c_void);
    fn aligned_alloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;
    fn Lib_Memzero0_memzero0(dst: *mut libc::c_void, len: uint64_t);
}
pub type int8_t = libc::c_schar;
pub type uint8_t = libc::c_uchar;
pub type uint16_t = libc::c_ushort;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type Hacl_Streaming_Types_error_code = uint8_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_Blake2b_blake2_params_s {
    pub digest_length: uint8_t,
    pub key_length: uint8_t,
    pub fanout: uint8_t,
    pub depth: uint8_t,
    pub leaf_length: uint32_t,
    pub node_offset: uint64_t,
    pub node_depth: uint8_t,
    pub inner_length: uint8_t,
    pub salt: *mut uint8_t,
    pub personal: *mut uint8_t,
}
pub type Hacl_Hash_Blake2b_blake2_params = Hacl_Hash_Blake2b_blake2_params_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_Blake2b_index_s {
    pub key_length: uint8_t,
    pub digest_length: uint8_t,
    pub last_node: bool,
}
pub type Hacl_Hash_Blake2b_index = Hacl_Hash_Blake2b_index_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_Blake2b_params_and_key_s {
    pub fst: *mut Hacl_Hash_Blake2b_blake2_params,
    pub snd: *mut uint8_t,
}
pub type Hacl_Hash_Blake2b_params_and_key = Hacl_Hash_Blake2b_params_and_key_s;
pub type Lib_IntVector_Intrinsics_vec128 = uint32x4_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_Blake2s_Simd128_block_state_t_s {
    pub fst: uint8_t,
    pub snd: uint8_t,
    pub thd: bool,
    pub f3: *mut Lib_IntVector_Intrinsics_vec128,
    pub f4: *mut Lib_IntVector_Intrinsics_vec128,
}
pub type Hacl_Hash_Blake2s_Simd128_block_state_t = Hacl_Hash_Blake2s_Simd128_block_state_t_s;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_Hash_Blake2s_Simd128_state_t_s {
    pub block_state: Hacl_Hash_Blake2s_Simd128_block_state_t,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
}
pub type Hacl_Hash_Blake2s_Simd128_state_t = Hacl_Hash_Blake2s_Simd128_state_t_s;
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
static mut Hacl_Hash_Blake2b_sigmaTable: [uint32_t; 160] = [
    0 as libc::c_uint,
    1 as libc::c_uint,
    2 as libc::c_uint,
    3 as libc::c_uint,
    4 as libc::c_uint,
    5 as libc::c_uint,
    6 as libc::c_uint,
    7 as libc::c_uint,
    8 as libc::c_uint,
    9 as libc::c_uint,
    10 as libc::c_uint,
    11 as libc::c_uint,
    12 as libc::c_uint,
    13 as libc::c_uint,
    14 as libc::c_uint,
    15 as libc::c_uint,
    14 as libc::c_uint,
    10 as libc::c_uint,
    4 as libc::c_uint,
    8 as libc::c_uint,
    9 as libc::c_uint,
    15 as libc::c_uint,
    13 as libc::c_uint,
    6 as libc::c_uint,
    1 as libc::c_uint,
    12 as libc::c_uint,
    0 as libc::c_uint,
    2 as libc::c_uint,
    11 as libc::c_uint,
    7 as libc::c_uint,
    5 as libc::c_uint,
    3 as libc::c_uint,
    11 as libc::c_uint,
    8 as libc::c_uint,
    12 as libc::c_uint,
    0 as libc::c_uint,
    5 as libc::c_uint,
    2 as libc::c_uint,
    15 as libc::c_uint,
    13 as libc::c_uint,
    10 as libc::c_uint,
    14 as libc::c_uint,
    3 as libc::c_uint,
    6 as libc::c_uint,
    7 as libc::c_uint,
    1 as libc::c_uint,
    9 as libc::c_uint,
    4 as libc::c_uint,
    7 as libc::c_uint,
    9 as libc::c_uint,
    3 as libc::c_uint,
    1 as libc::c_uint,
    13 as libc::c_uint,
    12 as libc::c_uint,
    11 as libc::c_uint,
    14 as libc::c_uint,
    2 as libc::c_uint,
    6 as libc::c_uint,
    5 as libc::c_uint,
    10 as libc::c_uint,
    4 as libc::c_uint,
    0 as libc::c_uint,
    15 as libc::c_uint,
    8 as libc::c_uint,
    9 as libc::c_uint,
    0 as libc::c_uint,
    5 as libc::c_uint,
    7 as libc::c_uint,
    2 as libc::c_uint,
    4 as libc::c_uint,
    10 as libc::c_uint,
    15 as libc::c_uint,
    14 as libc::c_uint,
    1 as libc::c_uint,
    11 as libc::c_uint,
    12 as libc::c_uint,
    6 as libc::c_uint,
    8 as libc::c_uint,
    3 as libc::c_uint,
    13 as libc::c_uint,
    2 as libc::c_uint,
    12 as libc::c_uint,
    6 as libc::c_uint,
    10 as libc::c_uint,
    0 as libc::c_uint,
    11 as libc::c_uint,
    8 as libc::c_uint,
    3 as libc::c_uint,
    4 as libc::c_uint,
    13 as libc::c_uint,
    7 as libc::c_uint,
    5 as libc::c_uint,
    15 as libc::c_uint,
    14 as libc::c_uint,
    1 as libc::c_uint,
    9 as libc::c_uint,
    12 as libc::c_uint,
    5 as libc::c_uint,
    1 as libc::c_uint,
    15 as libc::c_uint,
    14 as libc::c_uint,
    13 as libc::c_uint,
    4 as libc::c_uint,
    10 as libc::c_uint,
    0 as libc::c_uint,
    7 as libc::c_uint,
    6 as libc::c_uint,
    3 as libc::c_uint,
    9 as libc::c_uint,
    2 as libc::c_uint,
    8 as libc::c_uint,
    11 as libc::c_uint,
    13 as libc::c_uint,
    11 as libc::c_uint,
    7 as libc::c_uint,
    14 as libc::c_uint,
    12 as libc::c_uint,
    1 as libc::c_uint,
    3 as libc::c_uint,
    9 as libc::c_uint,
    5 as libc::c_uint,
    0 as libc::c_uint,
    15 as libc::c_uint,
    4 as libc::c_uint,
    8 as libc::c_uint,
    6 as libc::c_uint,
    2 as libc::c_uint,
    10 as libc::c_uint,
    6 as libc::c_uint,
    15 as libc::c_uint,
    14 as libc::c_uint,
    9 as libc::c_uint,
    11 as libc::c_uint,
    3 as libc::c_uint,
    0 as libc::c_uint,
    8 as libc::c_uint,
    12 as libc::c_uint,
    2 as libc::c_uint,
    13 as libc::c_uint,
    7 as libc::c_uint,
    1 as libc::c_uint,
    4 as libc::c_uint,
    10 as libc::c_uint,
    5 as libc::c_uint,
    10 as libc::c_uint,
    2 as libc::c_uint,
    8 as libc::c_uint,
    4 as libc::c_uint,
    7 as libc::c_uint,
    6 as libc::c_uint,
    1 as libc::c_uint,
    5 as libc::c_uint,
    15 as libc::c_uint,
    11 as libc::c_uint,
    9 as libc::c_uint,
    14 as libc::c_uint,
    3 as libc::c_uint,
    12 as libc::c_uint,
    13 as libc::c_uint,
    0,
];
static mut Hacl_Hash_Blake2b_ivTable_S: [uint32_t; 8] = [
    0x6a09e667 as libc::c_uint,
    0xbb67ae85 as libc::c_uint,
    0x3c6ef372 as libc::c_uint,
    0xa54ff53a as libc::c_uint,
    0x510e527f as libc::c_uint,
    0x9b05688c as libc::c_uint,
    0x1f83d9ab as libc::c_uint,
    0x5be0cd19 as libc::c_uint,
];
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_init(
    mut hash: *mut Lib_IntVector_Intrinsics_vec128,
    mut kk: uint32_t,
    mut nn: uint32_t,
) {
    let mut salt: [uint8_t; 8] = [0 as libc::c_uint as uint8_t, 0, 0, 0, 0, 0, 0, 0];
    let mut personal: [uint8_t; 8] = [0 as libc::c_uint as uint8_t, 0, 0, 0, 0, 0, 0, 0];
    let mut p: Hacl_Hash_Blake2b_blake2_params = {
        let mut init = Hacl_Hash_Blake2b_blake2_params_s {
            digest_length: 32 as libc::c_uint as uint8_t,
            key_length: 0 as libc::c_uint as uint8_t,
            fanout: 1 as libc::c_uint as uint8_t,
            depth: 1 as libc::c_uint as uint8_t,
            leaf_length: 0 as libc::c_uint,
            node_offset: 0 as libc::c_ulonglong,
            node_depth: 0 as libc::c_uint as uint8_t,
            inner_length: 0 as libc::c_uint as uint8_t,
            salt: salt.as_mut_ptr(),
            personal: personal.as_mut_ptr(),
        };
        init
    };
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut r0: *mut Lib_IntVector_Intrinsics_vec128 = hash;
    let mut r1: *mut Lib_IntVector_Intrinsics_vec128 = hash
        .offset(1 as libc::c_uint as isize);
    let mut r2: *mut Lib_IntVector_Intrinsics_vec128 = hash
        .offset(2 as libc::c_uint as isize);
    let mut r3: *mut Lib_IntVector_Intrinsics_vec128 = hash
        .offset(3 as libc::c_uint as isize);
    let mut iv0: uint32_t = Hacl_Hash_Blake2b_ivTable_S[0 as libc::c_uint as usize];
    let mut iv1: uint32_t = Hacl_Hash_Blake2b_ivTable_S[1 as libc::c_uint as usize];
    let mut iv2: uint32_t = Hacl_Hash_Blake2b_ivTable_S[2 as libc::c_uint as usize];
    let mut iv3: uint32_t = Hacl_Hash_Blake2b_ivTable_S[3 as libc::c_uint as usize];
    let mut iv4: uint32_t = Hacl_Hash_Blake2b_ivTable_S[4 as libc::c_uint as usize];
    let mut iv5: uint32_t = Hacl_Hash_Blake2b_ivTable_S[5 as libc::c_uint as usize];
    let mut iv6: uint32_t = Hacl_Hash_Blake2b_ivTable_S[6 as libc::c_uint as usize];
    let mut iv7: uint32_t = Hacl_Hash_Blake2b_ivTable_S[7 as libc::c_uint as usize];
    *r2
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
    *r3
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
    let mut uu____0: *mut uint32_t = tmp.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = (p.salt)
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = uu____0;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = (p.salt)
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = uu____0;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____1: *mut uint32_t = tmp.as_mut_ptr().offset(6 as libc::c_uint as isize);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_1: *mut uint8_t = (p.personal)
        .offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = uu____1;
    *os_1.offset(i_0 as isize) = x_1;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = (p.personal)
        .offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = uu____1;
    *os_2.offset(i_0 as isize) = x_2;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    tmp[0 as libc::c_uint
        as usize] = nn as uint8_t as uint32_t
        ^ ((kk as uint8_t as uint32_t) << 8 as libc::c_uint
            ^ ((p.fanout as uint32_t) << 16 as libc::c_uint
                ^ (p.depth as uint32_t) << 24 as libc::c_uint));
    tmp[1 as libc::c_uint as usize] = p.leaf_length;
    tmp[2 as libc::c_uint as usize] = p.node_offset as uint32_t;
    tmp[3 as libc::c_uint
        as usize] = (p.node_offset >> 32 as libc::c_uint) as uint32_t
        ^ ((p.node_depth as uint32_t) << 16 as libc::c_uint
            ^ (p.inner_length as uint32_t) << 24 as libc::c_uint);
    let mut tmp0: uint32_t = tmp[0 as libc::c_uint as usize];
    let mut tmp1: uint32_t = tmp[1 as libc::c_uint as usize];
    let mut tmp2: uint32_t = tmp[2 as libc::c_uint as usize];
    let mut tmp3: uint32_t = tmp[3 as libc::c_uint as usize];
    let mut tmp4: uint32_t = tmp[4 as libc::c_uint as usize];
    let mut tmp5: uint32_t = tmp[5 as libc::c_uint as usize];
    let mut tmp6: uint32_t = tmp[6 as libc::c_uint as usize];
    let mut tmp7: uint32_t = tmp[7 as libc::c_uint as usize];
    let mut iv0_: uint32_t = iv0 ^ tmp0;
    let mut iv1_: uint32_t = iv1 ^ tmp1;
    let mut iv2_: uint32_t = iv2 ^ tmp2;
    let mut iv3_: uint32_t = iv3 ^ tmp3;
    let mut iv4_: uint32_t = iv4 ^ tmp4;
    let mut iv5_: uint32_t = iv5 ^ tmp5;
    let mut iv6_: uint32_t = iv6 ^ tmp6;
    let mut iv7_: uint32_t = iv7 ^ tmp7;
    *r0
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1_, iv2_, iv3_);
    *r1
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv4_, iv5_, iv6_, iv7_);
}
unsafe extern "C" fn update_key(
    mut wv: *mut Lib_IntVector_Intrinsics_vec128,
    mut hash: *mut Lib_IntVector_Intrinsics_vec128,
    mut kk: uint32_t,
    mut k: *mut uint8_t,
    mut ll: uint32_t,
) {
    let mut lb: uint64_t = 64 as libc::c_uint as uint64_t;
    let mut b: [uint8_t; 64] = [
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
    memcpy(
        b.as_mut_ptr() as *mut libc::c_void,
        k as *const libc::c_void,
        (kk as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    if ll == 0 as libc::c_uint {
        update_block(
            wv,
            hash,
            1 as libc::c_int != 0,
            0 as libc::c_int != 0,
            lb,
            b.as_mut_ptr(),
        );
    } else {
        update_block(
            wv,
            hash,
            0 as libc::c_int != 0,
            0 as libc::c_int != 0,
            lb,
            b.as_mut_ptr(),
        );
    }
    Lib_Memzero0_memzero0(
        b.as_mut_ptr() as *mut libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_update_multi(
    mut len: uint32_t,
    mut wv: *mut Lib_IntVector_Intrinsics_vec128,
    mut hash: *mut Lib_IntVector_Intrinsics_vec128,
    mut prev: uint64_t,
    mut blocks: *mut uint8_t,
    mut nb: uint32_t,
) {
    let mut i: uint32_t = 0 as libc::c_uint;
    while i < nb {
        let mut totlen: uint64_t = prev
            .wrapping_add(
                i.wrapping_add(1 as libc::c_uint).wrapping_mul(64 as libc::c_uint)
                    as uint64_t,
            );
        let mut b: *mut uint8_t = blocks
            .offset(i.wrapping_mul(64 as libc::c_uint) as isize);
        update_block(wv, hash, 0 as libc::c_int != 0, 0 as libc::c_int != 0, totlen, b);
        i = i.wrapping_add(1);
        i;
    }
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_update_last(
    mut len: uint32_t,
    mut wv: *mut Lib_IntVector_Intrinsics_vec128,
    mut hash: *mut Lib_IntVector_Intrinsics_vec128,
    mut last_node: bool,
    mut prev: uint64_t,
    mut rem: uint32_t,
    mut d: *mut uint8_t,
) {
    let mut b: [uint8_t; 64] = [
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
    let mut last: *mut uint8_t = d.offset(len as isize).offset(-(rem as isize));
    memcpy(
        b.as_mut_ptr() as *mut libc::c_void,
        last as *const libc::c_void,
        (rem as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut totlen: uint64_t = prev.wrapping_add(len as uint64_t);
    update_block(wv, hash, 1 as libc::c_int != 0, last_node, totlen, b.as_mut_ptr());
    Lib_Memzero0_memzero0(
        b.as_mut_ptr() as *mut libc::c_void,
        (64 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong) as uint64_t,
    );
}
#[inline]
unsafe extern "C" fn update_blocks(
    mut len: uint32_t,
    mut wv: *mut Lib_IntVector_Intrinsics_vec128,
    mut hash: *mut Lib_IntVector_Intrinsics_vec128,
    mut prev: uint64_t,
    mut blocks: *mut uint8_t,
) {
    let mut nb0: uint32_t = len.wrapping_div(64 as libc::c_uint);
    let mut rem0: uint32_t = len.wrapping_rem(64 as libc::c_uint);
    let mut nb: uint32_t = 0;
    if rem0 == 0 as libc::c_uint && nb0 > 0 as libc::c_uint {
        nb = nb0.wrapping_sub(1 as libc::c_uint);
    } else {
        nb = nb0;
    }
    let mut rem: uint32_t = 0;
    if rem0 == 0 as libc::c_uint && nb0 > 0 as libc::c_uint {
        rem = 64 as libc::c_uint;
    } else {
        rem = rem0;
    }
    Hacl_Hash_Blake2s_Simd128_update_multi(len, wv, hash, prev, blocks, nb);
    Hacl_Hash_Blake2s_Simd128_update_last(
        len,
        wv,
        hash,
        0 as libc::c_int != 0,
        prev,
        rem,
        blocks,
    );
}
#[inline]
unsafe extern "C" fn update(
    mut wv: *mut Lib_IntVector_Intrinsics_vec128,
    mut hash: *mut Lib_IntVector_Intrinsics_vec128,
    mut kk: uint32_t,
    mut k: *mut uint8_t,
    mut ll: uint32_t,
    mut d: *mut uint8_t,
) {
    let mut lb: uint64_t = 64 as libc::c_uint as uint64_t;
    if kk > 0 as libc::c_uint {
        update_key(wv, hash, kk, k, ll);
        if !(ll == 0 as libc::c_uint) {
            update_blocks(ll, wv, hash, lb, d);
            return;
        }
        return;
    }
    update_blocks(ll, wv, hash, 0 as libc::c_uint as uint64_t, d);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_load_state128s_from_state32(
    mut st: *mut Lib_IntVector_Intrinsics_vec128,
    mut st32: *mut uint32_t,
) {
    let mut r0: *mut Lib_IntVector_Intrinsics_vec128 = st;
    let mut r1: *mut Lib_IntVector_Intrinsics_vec128 = st
        .offset(1 as libc::c_uint as isize);
    let mut r2: *mut Lib_IntVector_Intrinsics_vec128 = st
        .offset(2 as libc::c_uint as isize);
    let mut r3: *mut Lib_IntVector_Intrinsics_vec128 = st
        .offset(3 as libc::c_uint as isize);
    let mut b0: *mut uint32_t = st32;
    let mut b1: *mut uint32_t = st32.offset(4 as libc::c_uint as isize);
    let mut b2: *mut uint32_t = st32.offset(8 as libc::c_uint as isize);
    let mut b3: *mut uint32_t = st32.offset(12 as libc::c_uint as isize);
    *r0
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(
        *b0.offset(0 as libc::c_uint as isize),
        *b0.offset(1 as libc::c_uint as isize),
        *b0.offset(2 as libc::c_uint as isize),
        *b0.offset(3 as libc::c_uint as isize),
    );
    *r1
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(
        *b1.offset(0 as libc::c_uint as isize),
        *b1.offset(1 as libc::c_uint as isize),
        *b1.offset(2 as libc::c_uint as isize),
        *b1.offset(3 as libc::c_uint as isize),
    );
    *r2
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(
        *b2.offset(0 as libc::c_uint as isize),
        *b2.offset(1 as libc::c_uint as isize),
        *b2.offset(2 as libc::c_uint as isize),
        *b2.offset(3 as libc::c_uint as isize),
    );
    *r3
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(
        *b3.offset(0 as libc::c_uint as isize),
        *b3.offset(1 as libc::c_uint as isize),
        *b3.offset(2 as libc::c_uint as isize),
        *b3.offset(3 as libc::c_uint as isize),
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_malloc_with_key() -> *mut Lib_IntVector_Intrinsics_vec128 {
    let mut buf: *mut Lib_IntVector_Intrinsics_vec128 = aligned_alloc(
        16 as libc::c_int as libc::c_ulong,
        (::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>() as libc::c_ulong)
            .wrapping_mul(4 as libc::c_uint as libc::c_ulong),
    ) as *mut Lib_IntVector_Intrinsics_vec128;
    memset(
        buf as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    return buf;
}
unsafe extern "C" fn malloc_raw(
    mut kk: Hacl_Hash_Blake2b_index,
    mut key: Hacl_Hash_Blake2b_params_and_key,
) -> *mut Hacl_Hash_Blake2s_Simd128_state_t {
    let mut buf: *mut uint8_t = calloc(
        64 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut wv: *mut Lib_IntVector_Intrinsics_vec128 = aligned_alloc(
        16 as libc::c_int as libc::c_ulong,
        (::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>() as libc::c_ulong)
            .wrapping_mul(4 as libc::c_uint as libc::c_ulong),
    ) as *mut Lib_IntVector_Intrinsics_vec128;
    memset(
        wv as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    let mut b: *mut Lib_IntVector_Intrinsics_vec128 = aligned_alloc(
        16 as libc::c_int as libc::c_ulong,
        (::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>() as libc::c_ulong)
            .wrapping_mul(4 as libc::c_uint as libc::c_ulong),
    ) as *mut Lib_IntVector_Intrinsics_vec128;
    memset(
        b as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = {
        let mut init = Hacl_Hash_Blake2s_Simd128_block_state_t_s {
            fst: kk.key_length,
            snd: kk.digest_length,
            thd: kk.last_node,
            f3: wv,
            f4: b,
        };
        init
    };
    let mut p: *mut Hacl_Hash_Blake2b_blake2_params = key.fst;
    let mut kk1: uint8_t = (*p).key_length;
    let mut nn: uint8_t = (*p).digest_length;
    let mut last_node: bool = block_state.thd;
    let mut i0: Hacl_Hash_Blake2b_index = {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk1,
            digest_length: nn,
            last_node: last_node,
        };
        init
    };
    let mut h: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
    let mut kk2: uint32_t = i0.key_length as uint32_t;
    let mut k_: *mut uint8_t = key.snd;
    if !(kk2 == 0 as libc::c_uint) {
        let mut sub_b: *mut uint8_t = buf.offset(kk2 as isize);
        memset(
            sub_b as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            ((64 as libc::c_uint).wrapping_sub(kk2) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            buf as *mut libc::c_void,
            k_ as *const libc::c_void,
            (kk2 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut pv: Hacl_Hash_Blake2b_blake2_params = *p.offset(0 as libc::c_uint as isize);
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut r0: *mut Lib_IntVector_Intrinsics_vec128 = h;
    let mut r1: *mut Lib_IntVector_Intrinsics_vec128 = h
        .offset(1 as libc::c_uint as isize);
    let mut r2: *mut Lib_IntVector_Intrinsics_vec128 = h
        .offset(2 as libc::c_uint as isize);
    let mut r3: *mut Lib_IntVector_Intrinsics_vec128 = h
        .offset(3 as libc::c_uint as isize);
    let mut iv0: uint32_t = Hacl_Hash_Blake2b_ivTable_S[0 as libc::c_uint as usize];
    let mut iv1: uint32_t = Hacl_Hash_Blake2b_ivTable_S[1 as libc::c_uint as usize];
    let mut iv2: uint32_t = Hacl_Hash_Blake2b_ivTable_S[2 as libc::c_uint as usize];
    let mut iv3: uint32_t = Hacl_Hash_Blake2b_ivTable_S[3 as libc::c_uint as usize];
    let mut iv4: uint32_t = Hacl_Hash_Blake2b_ivTable_S[4 as libc::c_uint as usize];
    let mut iv5: uint32_t = Hacl_Hash_Blake2b_ivTable_S[5 as libc::c_uint as usize];
    let mut iv6: uint32_t = Hacl_Hash_Blake2b_ivTable_S[6 as libc::c_uint as usize];
    let mut iv7: uint32_t = Hacl_Hash_Blake2b_ivTable_S[7 as libc::c_uint as usize];
    *r2
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
    *r3
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
    let mut uu____0: *mut uint32_t = tmp.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = (pv.salt)
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r4: uint32_t = u;
    let mut x: uint32_t = r4;
    let mut os: *mut uint32_t = uu____0;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = (pv.salt)
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r4_0: uint32_t = u_0;
    let mut x_0: uint32_t = r4_0;
    let mut os_0: *mut uint32_t = uu____0;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____1: *mut uint32_t = tmp.as_mut_ptr().offset(6 as libc::c_uint as isize);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_1: *mut uint8_t = (pv.personal)
        .offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r4_1: uint32_t = u_1;
    let mut x_1: uint32_t = r4_1;
    let mut os_1: *mut uint32_t = uu____1;
    *os_1.offset(i_0 as isize) = x_1;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = (pv.personal)
        .offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r4_2: uint32_t = u_2;
    let mut x_2: uint32_t = r4_2;
    let mut os_2: *mut uint32_t = uu____1;
    *os_2.offset(i_0 as isize) = x_2;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    tmp[0 as libc::c_uint
        as usize] = pv.digest_length as uint32_t
        ^ ((pv.key_length as uint32_t) << 8 as libc::c_uint
            ^ ((pv.fanout as uint32_t) << 16 as libc::c_uint
                ^ (pv.depth as uint32_t) << 24 as libc::c_uint));
    tmp[1 as libc::c_uint as usize] = pv.leaf_length;
    tmp[2 as libc::c_uint as usize] = pv.node_offset as uint32_t;
    tmp[3 as libc::c_uint
        as usize] = (pv.node_offset >> 32 as libc::c_uint) as uint32_t
        ^ ((pv.node_depth as uint32_t) << 16 as libc::c_uint
            ^ (pv.inner_length as uint32_t) << 24 as libc::c_uint);
    let mut tmp0: uint32_t = tmp[0 as libc::c_uint as usize];
    let mut tmp1: uint32_t = tmp[1 as libc::c_uint as usize];
    let mut tmp2: uint32_t = tmp[2 as libc::c_uint as usize];
    let mut tmp3: uint32_t = tmp[3 as libc::c_uint as usize];
    let mut tmp4: uint32_t = tmp[4 as libc::c_uint as usize];
    let mut tmp5: uint32_t = tmp[5 as libc::c_uint as usize];
    let mut tmp6: uint32_t = tmp[6 as libc::c_uint as usize];
    let mut tmp7: uint32_t = tmp[7 as libc::c_uint as usize];
    let mut iv0_: uint32_t = iv0 ^ tmp0;
    let mut iv1_: uint32_t = iv1 ^ tmp1;
    let mut iv2_: uint32_t = iv2 ^ tmp2;
    let mut iv3_: uint32_t = iv3 ^ tmp3;
    let mut iv4_: uint32_t = iv4 ^ tmp4;
    let mut iv5_: uint32_t = iv5 ^ tmp5;
    let mut iv6_: uint32_t = iv6 ^ tmp6;
    let mut iv7_: uint32_t = iv7 ^ tmp7;
    *r0
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1_, iv2_, iv3_);
    *r1
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv4_, iv5_, iv6_, iv7_);
    let mut kk10: uint8_t = kk.key_length;
    let mut ite: uint32_t = 0;
    if kk10 as libc::c_uint != 0 as libc::c_uint {
        ite = 64 as libc::c_uint;
    } else {
        ite = 0 as libc::c_uint;
    }
    let mut s: Hacl_Hash_Blake2s_Simd128_state_t = {
        let mut init = Hacl_Hash_Blake2s_Simd128_state_t_s {
            block_state: block_state,
            buf: buf,
            total_len: ite as uint64_t,
        };
        init
    };
    let mut p0: *mut Hacl_Hash_Blake2s_Simd128_state_t = malloc(
        ::core::mem::size_of::<Hacl_Hash_Blake2s_Simd128_state_t>() as libc::c_ulong,
    ) as *mut Hacl_Hash_Blake2s_Simd128_state_t;
    *p0.offset(0 as libc::c_uint as isize) = s;
    return p0;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_malloc_with_params_and_key(
    mut p: *mut Hacl_Hash_Blake2b_blake2_params,
    mut last_node: bool,
    mut k: *mut uint8_t,
) -> *mut Hacl_Hash_Blake2s_Simd128_state_t {
    let mut pv: Hacl_Hash_Blake2b_blake2_params = *p.offset(0 as libc::c_uint as isize);
    let mut i1: Hacl_Hash_Blake2b_index = {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: pv.key_length,
            digest_length: pv.digest_length,
            last_node: last_node,
        };
        init
    };
    return malloc_raw(
        i1,
        {
            let mut init = Hacl_Hash_Blake2b_params_and_key_s {
                fst: p,
                snd: k,
            };
            init
        },
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_malloc_with_key0(
    mut k: *mut uint8_t,
    mut kk: uint8_t,
) -> *mut Hacl_Hash_Blake2s_Simd128_state_t {
    let mut nn: uint8_t = 32 as libc::c_uint as uint8_t;
    let mut i: Hacl_Hash_Blake2b_index = {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk,
            digest_length: nn,
            last_node: 0 as libc::c_int != 0,
        };
        init
    };
    let mut salt: [uint8_t; 8] = [0 as libc::c_uint as uint8_t, 0, 0, 0, 0, 0, 0, 0];
    let mut personal: [uint8_t; 8] = [0 as libc::c_uint as uint8_t, 0, 0, 0, 0, 0, 0, 0];
    let mut p: Hacl_Hash_Blake2b_blake2_params = {
        let mut init = Hacl_Hash_Blake2b_blake2_params_s {
            digest_length: i.digest_length,
            key_length: i.key_length,
            fanout: 1 as libc::c_uint as uint8_t,
            depth: 1 as libc::c_uint as uint8_t,
            leaf_length: 0 as libc::c_uint,
            node_offset: 0 as libc::c_ulonglong,
            node_depth: 0 as libc::c_uint as uint8_t,
            inner_length: 0 as libc::c_uint as uint8_t,
            salt: salt.as_mut_ptr(),
            personal: personal.as_mut_ptr(),
        };
        init
    };
    let mut p0: Hacl_Hash_Blake2b_blake2_params = p;
    let mut s: *mut Hacl_Hash_Blake2s_Simd128_state_t = Hacl_Hash_Blake2s_Simd128_malloc_with_params_and_key(
        &mut p0,
        0 as libc::c_int != 0,
        k,
    );
    return s;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_malloc() -> *mut Hacl_Hash_Blake2s_Simd128_state_t {
    return Hacl_Hash_Blake2s_Simd128_malloc_with_key0(
        0 as *mut uint8_t,
        0 as libc::c_uint as uint8_t,
    );
}
unsafe extern "C" fn index_of_state(
    mut s: *mut Hacl_Hash_Blake2s_Simd128_state_t,
) -> Hacl_Hash_Blake2b_index {
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = (*s).block_state;
    let mut last_node: bool = block_state.thd;
    let mut nn: uint8_t = block_state.snd;
    let mut kk1: uint8_t = block_state.fst;
    return {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk1,
            digest_length: nn,
            last_node: last_node,
        };
        init
    };
}
unsafe extern "C" fn reset_raw(
    mut state: *mut Hacl_Hash_Blake2s_Simd128_state_t,
    mut key: Hacl_Hash_Blake2b_params_and_key,
) {
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = (*state).block_state;
    let mut buf: *mut uint8_t = (*state).buf;
    let mut last_node0: bool = block_state.thd;
    let mut nn0: uint8_t = block_state.snd;
    let mut kk10: uint8_t = block_state.fst;
    let mut i0: Hacl_Hash_Blake2b_index = {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk10,
            digest_length: nn0,
            last_node: last_node0,
        };
        init
    };
    let mut p: *mut Hacl_Hash_Blake2b_blake2_params = key.fst;
    let mut kk1: uint8_t = (*p).key_length;
    let mut nn: uint8_t = (*p).digest_length;
    let mut last_node: bool = block_state.thd;
    let mut i1: Hacl_Hash_Blake2b_index = {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk1,
            digest_length: nn,
            last_node: last_node,
        };
        init
    };
    let mut h: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
    let mut kk2: uint32_t = i1.key_length as uint32_t;
    let mut k_1: *mut uint8_t = key.snd;
    if !(kk2 == 0 as libc::c_uint) {
        let mut sub_b: *mut uint8_t = buf.offset(kk2 as isize);
        memset(
            sub_b as *mut libc::c_void,
            0 as libc::c_uint as libc::c_int,
            ((64 as libc::c_uint).wrapping_sub(kk2) as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        memcpy(
            buf as *mut libc::c_void,
            k_1 as *const libc::c_void,
            (kk2 as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
    }
    let mut pv: Hacl_Hash_Blake2b_blake2_params = *p.offset(0 as libc::c_uint as isize);
    let mut tmp: [uint32_t; 8] = [0 as libc::c_uint, 0, 0, 0, 0, 0, 0, 0];
    let mut r0: *mut Lib_IntVector_Intrinsics_vec128 = h;
    let mut r1: *mut Lib_IntVector_Intrinsics_vec128 = h
        .offset(1 as libc::c_uint as isize);
    let mut r2: *mut Lib_IntVector_Intrinsics_vec128 = h
        .offset(2 as libc::c_uint as isize);
    let mut r3: *mut Lib_IntVector_Intrinsics_vec128 = h
        .offset(3 as libc::c_uint as isize);
    let mut iv0: uint32_t = Hacl_Hash_Blake2b_ivTable_S[0 as libc::c_uint as usize];
    let mut iv1: uint32_t = Hacl_Hash_Blake2b_ivTable_S[1 as libc::c_uint as usize];
    let mut iv2: uint32_t = Hacl_Hash_Blake2b_ivTable_S[2 as libc::c_uint as usize];
    let mut iv3: uint32_t = Hacl_Hash_Blake2b_ivTable_S[3 as libc::c_uint as usize];
    let mut iv4: uint32_t = Hacl_Hash_Blake2b_ivTable_S[4 as libc::c_uint as usize];
    let mut iv5: uint32_t = Hacl_Hash_Blake2b_ivTable_S[5 as libc::c_uint as usize];
    let mut iv6: uint32_t = Hacl_Hash_Blake2b_ivTable_S[6 as libc::c_uint as usize];
    let mut iv7: uint32_t = Hacl_Hash_Blake2b_ivTable_S[7 as libc::c_uint as usize];
    *r2
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv0, iv1, iv2, iv3);
    *r3
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv4, iv5, iv6, iv7);
    let mut uu____0: *mut uint32_t = tmp.as_mut_ptr().offset(4 as libc::c_uint as isize);
    let mut i: uint32_t = 0 as libc::c_uint;
    let mut bj: *mut uint8_t = (pv.salt)
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u: uint32_t = load32(bj);
    let mut r: uint32_t = u;
    let mut x: uint32_t = r;
    let mut os: *mut uint32_t = uu____0;
    *os.offset(i as isize) = x;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_0: *mut uint8_t = (pv.salt)
        .offset(i.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_0: uint32_t = load32(bj_0);
    let mut r_0: uint32_t = u_0;
    let mut x_0: uint32_t = r_0;
    let mut os_0: *mut uint32_t = uu____0;
    *os_0.offset(i as isize) = x_0;
    i = (i as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut uu____1: *mut uint32_t = tmp.as_mut_ptr().offset(6 as libc::c_uint as isize);
    let mut i_0: uint32_t = 0 as libc::c_uint;
    let mut bj_1: *mut uint8_t = (pv.personal)
        .offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_1: uint32_t = load32(bj_1);
    let mut r_1: uint32_t = u_1;
    let mut x_1: uint32_t = r_1;
    let mut os_1: *mut uint32_t = uu____1;
    *os_1.offset(i_0 as isize) = x_1;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    let mut bj_2: *mut uint8_t = (pv.personal)
        .offset(i_0.wrapping_mul(4 as libc::c_uint) as isize);
    let mut u_2: uint32_t = load32(bj_2);
    let mut r_2: uint32_t = u_2;
    let mut x_2: uint32_t = r_2;
    let mut os_2: *mut uint32_t = uu____1;
    *os_2.offset(i_0 as isize) = x_2;
    i_0 = (i_0 as libc::c_uint).wrapping_add(1 as libc::c_uint) as uint32_t as uint32_t;
    tmp[0 as libc::c_uint
        as usize] = pv.digest_length as uint32_t
        ^ ((pv.key_length as uint32_t) << 8 as libc::c_uint
            ^ ((pv.fanout as uint32_t) << 16 as libc::c_uint
                ^ (pv.depth as uint32_t) << 24 as libc::c_uint));
    tmp[1 as libc::c_uint as usize] = pv.leaf_length;
    tmp[2 as libc::c_uint as usize] = pv.node_offset as uint32_t;
    tmp[3 as libc::c_uint
        as usize] = (pv.node_offset >> 32 as libc::c_uint) as uint32_t
        ^ ((pv.node_depth as uint32_t) << 16 as libc::c_uint
            ^ (pv.inner_length as uint32_t) << 24 as libc::c_uint);
    let mut tmp0: uint32_t = tmp[0 as libc::c_uint as usize];
    let mut tmp1: uint32_t = tmp[1 as libc::c_uint as usize];
    let mut tmp2: uint32_t = tmp[2 as libc::c_uint as usize];
    let mut tmp3: uint32_t = tmp[3 as libc::c_uint as usize];
    let mut tmp4: uint32_t = tmp[4 as libc::c_uint as usize];
    let mut tmp5: uint32_t = tmp[5 as libc::c_uint as usize];
    let mut tmp6: uint32_t = tmp[6 as libc::c_uint as usize];
    let mut tmp7: uint32_t = tmp[7 as libc::c_uint as usize];
    let mut iv0_: uint32_t = iv0 ^ tmp0;
    let mut iv1_: uint32_t = iv1 ^ tmp1;
    let mut iv2_: uint32_t = iv2 ^ tmp2;
    let mut iv3_: uint32_t = iv3 ^ tmp3;
    let mut iv4_: uint32_t = iv4 ^ tmp4;
    let mut iv5_: uint32_t = iv5 ^ tmp5;
    let mut iv6_: uint32_t = iv6 ^ tmp6;
    let mut iv7_: uint32_t = iv7 ^ tmp7;
    *r0
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv0_, iv1_, iv2_, iv3_);
    *r1
        .offset(
            0 as libc::c_uint as isize,
        ) = Lib_IntVector_Intrinsics_vec128_load32s(iv4_, iv5_, iv6_, iv7_);
    let mut kk11: uint8_t = i0.key_length;
    let mut ite: uint32_t = 0;
    if kk11 as libc::c_uint != 0 as libc::c_uint {
        ite = 64 as libc::c_uint;
    } else {
        ite = 0 as libc::c_uint;
    }
    let mut total_len: uint64_t = ite as uint64_t;
    (*state).total_len = total_len;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_reset_with_key_and_params(
    mut s: *mut Hacl_Hash_Blake2s_Simd128_state_t,
    mut p: *mut Hacl_Hash_Blake2b_blake2_params,
    mut k: *mut uint8_t,
) {
    let mut i1: Hacl_Hash_Blake2b_index = index_of_state(s);
    reset_raw(
        s,
        {
            let mut init = Hacl_Hash_Blake2b_params_and_key_s {
                fst: p,
                snd: k,
            };
            init
        },
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_reset_with_key(
    mut s: *mut Hacl_Hash_Blake2s_Simd128_state_t,
    mut k: *mut uint8_t,
) {
    let mut idx: Hacl_Hash_Blake2b_index = index_of_state(s);
    let mut salt: [uint8_t; 8] = [0 as libc::c_uint as uint8_t, 0, 0, 0, 0, 0, 0, 0];
    let mut personal: [uint8_t; 8] = [0 as libc::c_uint as uint8_t, 0, 0, 0, 0, 0, 0, 0];
    let mut p: Hacl_Hash_Blake2b_blake2_params = {
        let mut init = Hacl_Hash_Blake2b_blake2_params_s {
            digest_length: idx.digest_length,
            key_length: idx.key_length,
            fanout: 1 as libc::c_uint as uint8_t,
            depth: 1 as libc::c_uint as uint8_t,
            leaf_length: 0 as libc::c_uint,
            node_offset: 0 as libc::c_ulonglong,
            node_depth: 0 as libc::c_uint as uint8_t,
            inner_length: 0 as libc::c_uint as uint8_t,
            salt: salt.as_mut_ptr(),
            personal: personal.as_mut_ptr(),
        };
        init
    };
    let mut p0: Hacl_Hash_Blake2b_blake2_params = p;
    reset_raw(
        s,
        {
            let mut init = Hacl_Hash_Blake2b_params_and_key_s {
                fst: &mut p0,
                snd: k,
            };
            init
        },
    );
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_reset(
    mut s: *mut Hacl_Hash_Blake2s_Simd128_state_t,
) {
    Hacl_Hash_Blake2s_Simd128_reset_with_key(s, 0 as *mut uint8_t);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_update(
    mut state: *mut Hacl_Hash_Blake2s_Simd128_state_t,
    mut chunk: *mut uint8_t,
    mut chunk_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = (*state).block_state;
    let mut total_len: uint64_t = (*state).total_len;
    if chunk_len as uint64_t
        > (0xffffffffffffffff as libc::c_ulonglong).wrapping_sub(total_len)
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
            let mut prevlen: uint64_t = total_len1_0.wrapping_sub(sz1_0 as uint64_t);
            let mut hash: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
            let mut wv: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f3;
            let mut nb: uint32_t = 1 as libc::c_uint;
            Hacl_Hash_Blake2s_Simd128_update_multi(
                64 as libc::c_uint,
                wv,
                hash,
                prevlen,
                buf_0,
                nb,
            );
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
        let mut hash_0: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
        let mut wv_0: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f3;
        let mut nb_0: uint32_t = data1_len.wrapping_div(64 as libc::c_uint);
        Hacl_Hash_Blake2s_Simd128_update_multi(
            data1_len,
            wv_0,
            hash_0,
            total_len1_0,
            data1,
            nb_0,
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
            let mut prevlen_0: uint64_t = total_len1_1.wrapping_sub(sz1_1 as uint64_t);
            let mut hash_1: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
            let mut wv_1: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f3;
            let mut nb_1: uint32_t = 1 as libc::c_uint;
            Hacl_Hash_Blake2s_Simd128_update_multi(
                64 as libc::c_uint,
                wv_1,
                hash_1,
                prevlen_0,
                buf0,
                nb_1,
            );
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
        let mut hash_2: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
        let mut wv_2: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f3;
        let mut nb_2: uint32_t = data1_len_0.wrapping_div(64 as libc::c_uint);
        Hacl_Hash_Blake2s_Simd128_update_multi(
            data1_len_0,
            wv_2,
            hash_2,
            total_len1_1,
            data1_0,
            nb_2,
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
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_info(
    mut s: *mut Hacl_Hash_Blake2s_Simd128_state_t,
) -> Hacl_Hash_Blake2b_index {
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = (*s).block_state;
    let mut last_node: bool = block_state.thd;
    let mut nn: uint8_t = block_state.snd;
    let mut kk: uint8_t = block_state.fst;
    return {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk,
            digest_length: nn,
            last_node: last_node,
        };
        init
    };
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_free(
    mut state: *mut Hacl_Hash_Blake2s_Simd128_state_t,
) {
    let mut scrut: Hacl_Hash_Blake2s_Simd128_state_t = *state;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = scrut.block_state;
    let mut b: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
    let mut wv: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f3;
    free(wv as *mut libc::c_void);
    free(b as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_Hash_Blake2s_Simd128_copy(
    mut state: *mut Hacl_Hash_Blake2s_Simd128_state_t,
) -> *mut Hacl_Hash_Blake2s_Simd128_state_t {
    let mut block_state0: Hacl_Hash_Blake2s_Simd128_block_state_t = (*state).block_state;
    let mut buf0: *mut uint8_t = (*state).buf;
    let mut total_len0: uint64_t = (*state).total_len;
    let mut last_node: bool = block_state0.thd;
    let mut nn: uint8_t = block_state0.snd;
    let mut kk1: uint8_t = block_state0.fst;
    let mut i: Hacl_Hash_Blake2b_index = {
        let mut init = Hacl_Hash_Blake2b_index_s {
            key_length: kk1,
            digest_length: nn,
            last_node: last_node,
        };
        init
    };
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
    let mut wv: *mut Lib_IntVector_Intrinsics_vec128 = aligned_alloc(
        16 as libc::c_int as libc::c_ulong,
        (::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>() as libc::c_ulong)
            .wrapping_mul(4 as libc::c_uint as libc::c_ulong),
    ) as *mut Lib_IntVector_Intrinsics_vec128;
    memset(
        wv as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    let mut b: *mut Lib_IntVector_Intrinsics_vec128 = aligned_alloc(
        16 as libc::c_int as libc::c_ulong,
        (::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>() as libc::c_ulong)
            .wrapping_mul(4 as libc::c_uint as libc::c_ulong),
    ) as *mut Lib_IntVector_Intrinsics_vec128;
    memset(
        b as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    let mut block_state: Hacl_Hash_Blake2s_Simd128_block_state_t = {
        let mut init = Hacl_Hash_Blake2s_Simd128_block_state_t_s {
            fst: i.key_length,
            snd: i.digest_length,
            thd: i.last_node,
            f3: wv,
            f4: b,
        };
        init
    };
    let mut src_b: *mut Lib_IntVector_Intrinsics_vec128 = block_state0.f4;
    let mut dst_b: *mut Lib_IntVector_Intrinsics_vec128 = block_state.f4;
    memcpy(
        dst_b as *mut libc::c_void,
        src_b as *const libc::c_void,
        (4 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    let mut s: Hacl_Hash_Blake2s_Simd128_state_t = {
        let mut init = Hacl_Hash_Blake2s_Simd128_state_t_s {
            block_state: block_state,
            buf: buf,
            total_len: total_len0,
        };
        init
    };
    let mut p: *mut Hacl_Hash_Blake2s_Simd128_state_t = malloc(
        ::core::mem::size_of::<Hacl_Hash_Blake2s_Simd128_state_t>() as libc::c_ulong,
    ) as *mut Hacl_Hash_Blake2s_Simd128_state_t;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
