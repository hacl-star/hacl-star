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
}
pub type int8_t = libc::c_schar;
pub type int64_t = libc::c_longlong;
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
pub type uint64_t = libc::c_ulonglong;
pub type Hacl_Streaming_Types_error_code = uint8_t;
pub type Lib_IntVector_Intrinsics_vec128 = uint32x4_t;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Hacl_MAC_Poly1305_Simd128_state_t_s {
    pub block_state: *mut Lib_IntVector_Intrinsics_vec128,
    pub buf: *mut uint8_t,
    pub total_len: uint64_t,
    pub p_key: *mut uint8_t,
}
pub type Hacl_MAC_Poly1305_Simd128_state_t = Hacl_MAC_Poly1305_Simd128_state_t_s;
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
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_Simd128_malloc(
    mut key: *mut uint8_t,
) -> *mut Hacl_MAC_Poly1305_Simd128_state_t {
    let mut buf: *mut uint8_t = calloc(
        32 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    let mut r1: *mut Lib_IntVector_Intrinsics_vec128 = aligned_alloc(
        16 as libc::c_int as libc::c_ulong,
        (::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>() as libc::c_ulong)
            .wrapping_mul(25 as libc::c_uint as libc::c_ulong),
    ) as *mut Lib_IntVector_Intrinsics_vec128;
    memset(
        r1 as *mut libc::c_void,
        0 as libc::c_uint as libc::c_int,
        (25 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(
                ::core::mem::size_of::<Lib_IntVector_Intrinsics_vec128>()
                    as libc::c_ulong,
            ),
    );
    let mut block_state: *mut Lib_IntVector_Intrinsics_vec128 = r1;
    Hacl_MAC_Poly1305_Simd128_poly1305_init(block_state, key);
    let mut k_: *mut uint8_t = calloc(
        32 as libc::c_uint as libc::c_ulong,
        ::core::mem::size_of::<uint8_t>() as libc::c_ulong,
    ) as *mut uint8_t;
    memcpy(
        k_ as *mut libc::c_void,
        key as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_0: *mut uint8_t = k_;
    let mut s: Hacl_MAC_Poly1305_Simd128_state_t = {
        let mut init = Hacl_MAC_Poly1305_Simd128_state_t_s {
            block_state: block_state,
            buf: buf,
            total_len: 0 as libc::c_uint as uint64_t,
            p_key: k_0,
        };
        init
    };
    let mut p: *mut Hacl_MAC_Poly1305_Simd128_state_t = malloc(
        ::core::mem::size_of::<Hacl_MAC_Poly1305_Simd128_state_t>() as libc::c_ulong,
    ) as *mut Hacl_MAC_Poly1305_Simd128_state_t;
    *p.offset(0 as libc::c_uint as isize) = s;
    return p;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_Simd128_reset(
    mut state: *mut Hacl_MAC_Poly1305_Simd128_state_t,
    mut key: *mut uint8_t,
) {
    let mut block_state: *mut Lib_IntVector_Intrinsics_vec128 = (*state).block_state;
    let mut k_: *mut uint8_t = (*state).p_key;
    Hacl_MAC_Poly1305_Simd128_poly1305_init(block_state, key);
    memcpy(
        k_ as *mut libc::c_void,
        key as *const libc::c_void,
        (32 as libc::c_uint as libc::c_ulong)
            .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
    );
    let mut k_1: *mut uint8_t = k_;
    let mut total_len: uint64_t = 0 as libc::c_uint as uint64_t;
    (*state).total_len = total_len;
    (*state).p_key = k_1;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_Simd128_update(
    mut state: *mut Hacl_MAC_Poly1305_Simd128_state_t,
    mut chunk: *mut uint8_t,
    mut chunk_len: uint32_t,
) -> Hacl_Streaming_Types_error_code {
    let mut block_state: *mut Lib_IntVector_Intrinsics_vec128 = (*state).block_state;
    let mut total_len: uint64_t = (*state).total_len;
    if chunk_len as uint64_t > (0xffffffff as libc::c_ulonglong).wrapping_sub(total_len)
    {
        return 3 as libc::c_int as Hacl_Streaming_Types_error_code;
    }
    let mut sz: uint32_t = 0;
    if total_len % 32 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
        && total_len > 0 as libc::c_ulonglong
    {
        sz = 32 as libc::c_uint;
    } else {
        sz = (total_len % 32 as libc::c_uint as uint64_t) as uint32_t;
    }
    if chunk_len <= (32 as libc::c_uint).wrapping_sub(sz) {
        let mut buf: *mut uint8_t = (*state).buf;
        let mut total_len1: uint64_t = (*state).total_len;
        let mut k_1: *mut uint8_t = (*state).p_key;
        let mut sz1: uint32_t = 0;
        if total_len1 % 32 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1 > 0 as libc::c_ulonglong
        {
            sz1 = 32 as libc::c_uint;
        } else {
            sz1 = (total_len1 % 32 as libc::c_uint as uint64_t) as uint32_t;
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
        (*state).p_key = k_1;
    } else if sz == 0 as libc::c_uint {
        let mut buf_0: *mut uint8_t = (*state).buf;
        let mut total_len1_0: uint64_t = (*state).total_len;
        let mut k_1_0: *mut uint8_t = (*state).p_key;
        let mut sz1_0: uint32_t = 0;
        if total_len1_0 % 32 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_0 > 0 as libc::c_ulonglong
        {
            sz1_0 = 32 as libc::c_uint;
        } else {
            sz1_0 = (total_len1_0 % 32 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_0 == 0 as libc::c_uint) {
            poly1305_update(block_state, 32 as libc::c_uint, buf_0);
        }
        let mut ite: uint32_t = 0;
        if chunk_len as uint64_t % 32 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong && chunk_len as uint64_t > 0 as libc::c_ulonglong
        {
            ite = 32 as libc::c_uint;
        } else {
            ite = (chunk_len as uint64_t % 32 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks: uint32_t = chunk_len
            .wrapping_sub(ite)
            .wrapping_div(32 as libc::c_uint);
        let mut data1_len: uint32_t = n_blocks.wrapping_mul(32 as libc::c_uint);
        let mut data2_len: uint32_t = chunk_len.wrapping_sub(data1_len);
        let mut data1: *mut uint8_t = chunk;
        let mut data2: *mut uint8_t = chunk.offset(data1_len as isize);
        poly1305_update(block_state, data1_len, data1);
        let mut dst: *mut uint8_t = buf_0;
        memcpy(
            dst as *mut libc::c_void,
            data2 as *const libc::c_void,
            (data2_len as libc::c_ulong)
                .wrapping_mul(::core::mem::size_of::<uint8_t>() as libc::c_ulong),
        );
        (*state).total_len = total_len1_0.wrapping_add(chunk_len as uint64_t);
        (*state).p_key = k_1_0;
    } else {
        let mut diff: uint32_t = (32 as libc::c_uint).wrapping_sub(sz);
        let mut chunk1: *mut uint8_t = chunk;
        let mut chunk2: *mut uint8_t = chunk.offset(diff as isize);
        let mut buf_1: *mut uint8_t = (*state).buf;
        let mut total_len10: uint64_t = (*state).total_len;
        let mut k_1_1: *mut uint8_t = (*state).p_key;
        let mut sz10: uint32_t = 0;
        if total_len10 % 32 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len10 > 0 as libc::c_ulonglong
        {
            sz10 = 32 as libc::c_uint;
        } else {
            sz10 = (total_len10 % 32 as libc::c_uint as uint64_t) as uint32_t;
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
        (*state).p_key = k_1_1;
        let mut buf0: *mut uint8_t = (*state).buf;
        let mut total_len1_1: uint64_t = (*state).total_len;
        let mut k_10: *mut uint8_t = (*state).p_key;
        let mut sz1_1: uint32_t = 0;
        if total_len1_1 % 32 as libc::c_uint as uint64_t == 0 as libc::c_ulonglong
            && total_len1_1 > 0 as libc::c_ulonglong
        {
            sz1_1 = 32 as libc::c_uint;
        } else {
            sz1_1 = (total_len1_1 % 32 as libc::c_uint as uint64_t) as uint32_t;
        }
        if !(sz1_1 == 0 as libc::c_uint) {
            poly1305_update(block_state, 32 as libc::c_uint, buf0);
        }
        let mut ite_0: uint32_t = 0;
        if chunk_len.wrapping_sub(diff) as uint64_t % 32 as libc::c_uint as uint64_t
            == 0 as libc::c_ulonglong
            && chunk_len.wrapping_sub(diff) as uint64_t > 0 as libc::c_ulonglong
        {
            ite_0 = 32 as libc::c_uint;
        } else {
            ite_0 = (chunk_len.wrapping_sub(diff) as uint64_t
                % 32 as libc::c_uint as uint64_t) as uint32_t;
        }
        let mut n_blocks_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(ite_0)
            .wrapping_div(32 as libc::c_uint);
        let mut data1_len_0: uint32_t = n_blocks_0.wrapping_mul(32 as libc::c_uint);
        let mut data2_len_0: uint32_t = chunk_len
            .wrapping_sub(diff)
            .wrapping_sub(data1_len_0);
        let mut data1_0: *mut uint8_t = chunk2;
        let mut data2_0: *mut uint8_t = chunk2.offset(data1_len_0 as isize);
        poly1305_update(block_state, data1_len_0, data1_0);
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
        (*state).p_key = k_10;
    }
    return 0 as libc::c_int as Hacl_Streaming_Types_error_code;
}
#[no_mangle]
pub unsafe extern "C" fn Hacl_MAC_Poly1305_Simd128_free(
    mut state: *mut Hacl_MAC_Poly1305_Simd128_state_t,
) {
    let mut scrut: Hacl_MAC_Poly1305_Simd128_state_t = *state;
    let mut k_: *mut uint8_t = scrut.p_key;
    let mut buf: *mut uint8_t = scrut.buf;
    let mut block_state: *mut Lib_IntVector_Intrinsics_vec128 = scrut.block_state;
    free(k_ as *mut libc::c_void);
    free(block_state as *mut libc::c_void);
    free(buf as *mut libc::c_void);
    free(state as *mut libc::c_void);
}
