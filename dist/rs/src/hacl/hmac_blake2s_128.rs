#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn compute_blake2s_128(
    dst: &mut [u8],
    key: &mut [u8],
    key_len: u32,
    data: &mut [u8],
    data_len: u32
) ->
    ()
{
    let l: u32 = 64u32;
    let mut key_block: Vec<u8> = vec![0x00u8; l as usize];
    let nkey: (&mut [u8], &mut [u8]) = (&mut key_block).split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 32u32 };
    let zeroes: (&mut [u8], &mut [u8]) = nkey.1.split_at_mut(ite as usize);
    crate::lowstar::ignore::ignore::<&mut [u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    {
        crate::hacl::hash_blake2s_simd128::hash_with_key(
            zeroes.0,
            32u32,
            key,
            key_len,
            &mut [],
            0u32
        )
    };
    let mut ipad: Vec<u8> = vec![0x36u8; l as usize];
    for i in 0u32..l
    {
        let xi: u8 = (&mut ipad)[i as usize];
        let yi: u8 = (&mut key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: Vec<u8> = vec![0x5cu8; l as usize];
    for i in 0u32..l
    {
        let xi: u8 = (&mut opad)[i as usize];
        let yi: u8 = (&mut key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [crate::lib::intvector_intrinsics::vec128; 4] =
        [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hacl::hash_blake2s_simd128::init(&mut s, 0u32, 32u32);
    let s0: &mut [crate::lib::intvector_intrinsics::vec128] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [crate::lib::intvector_intrinsics::vec128; 4] =
            [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hacl::hash_blake2s_simd128::update_last(64u32, &mut wv, s0, 0u64, 64u32, &mut ipad)
    }
    else
    {
        let block_len: u32 = 64u32;
        let n_blocks: u32 = data_len.wrapping_div(block_len);
        let rem: u32 = data_len.wrapping_rem(block_len);
        let scrut: crate::hacl::hmac::__uint32_t_uint32_t =
            if n_blocks > 0u32 && rem == 0u32
            {
                let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
                crate::hacl::hmac::__uint32_t_uint32_t
                { fst: n_blocks·, snd: data_len.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
            }
            else
            { crate::hacl::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
        let n_blocks0: u32 = scrut.fst;
        let rem_len: u32 = scrut.snd;
        let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
        let full_blocks: (&mut [u8], &mut [u8]) = data.split_at_mut(0usize);
        let rem0: (&mut [u8], &mut [u8]) = full_blocks.1.split_at_mut(full_blocks_len as usize);
        let mut wv: [crate::lib::intvector_intrinsics::vec128; 4] =
            [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hacl::hash_blake2s_simd128::update_multi(64u32, &mut wv, s0, 0u64, &mut ipad, 1u32);
        let mut wv0: [crate::lib::intvector_intrinsics::vec128; 4] =
            [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hacl::hash_blake2s_simd128::update_multi(
            n_blocks0.wrapping_mul(64u32),
            &mut wv0,
            s0,
            block_len as u64,
            rem0.0,
            n_blocks0
        );
        let mut wv1: [crate::lib::intvector_intrinsics::vec128; 4] =
            [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hacl::hash_blake2s_simd128::update_last(
            rem_len,
            &mut wv1,
            s0,
            (64u32 as u64).wrapping_add(full_blocks_len as u64),
            rem_len,
            rem0.1
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_blake2s_simd128::finish(32u32, dst1.1, s0);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_blake2s_simd128::init(s0, 0u32, 32u32);
    let block_len: u32 = 64u32;
    let n_blocks: u32 = 32u32.wrapping_div(block_len);
    let rem: u32 = 32u32.wrapping_rem(block_len);
    let scrut: crate::hacl::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hacl::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 32u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hacl::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&mut [u8], &mut [u8]) = hash1.1.split_at_mut(0usize);
    let rem0: (&mut [u8], &mut [u8]) = full_blocks.1.split_at_mut(full_blocks_len as usize);
    let mut wv: [crate::lib::intvector_intrinsics::vec128; 4] =
        [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hacl::hash_blake2s_simd128::update_multi(64u32, &mut wv, s0, 0u64, &mut opad, 1u32);
    let mut wv0: [crate::lib::intvector_intrinsics::vec128; 4] =
        [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hacl::hash_blake2s_simd128::update_multi(
        n_blocks0.wrapping_mul(64u32),
        &mut wv0,
        s0,
        block_len as u64,
        rem0.0,
        n_blocks0
    );
    let mut wv1: [crate::lib::intvector_intrinsics::vec128; 4] =
        [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hacl::hash_blake2s_simd128::update_last(
        rem_len,
        &mut wv1,
        s0,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem_len,
        rem0.1
    );
    crate::hacl::hash_blake2s_simd128::finish(32u32, dst, s0)
}
