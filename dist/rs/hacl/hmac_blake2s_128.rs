#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

/**
Write the HMAC-BLAKE2s MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory.
*/
pub fn
compute_blake2s_128(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let l: u32 = 64u32;
    let mut key_block: Box<[u8]> = vec![0x00u8; l as usize].into_boxed_slice();
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 32u32 };
    let zeroes: (&mut [u8], &mut [u8]) = nkey.1.split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_blake2s_simd128::hash_with_key(zeroes.0, 32u32, key, key_len, &[], 0u32) };
    let mut ipad: Box<[u8]> = vec![0x36u8; l as usize].into_boxed_slice();
    for i in 0u32..l
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: Box<[u8]> = vec![0x5cu8; l as usize].into_boxed_slice();
    for i in 0u32..l
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [lib::intvector_intrinsics::vec128; 4] =
        [lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hash_blake2s_simd128::init(&mut s, 0u32, 32u32);
    let s0: &mut [lib::intvector_intrinsics::vec128] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [lib::intvector_intrinsics::vec128; 4] =
            [lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hash_blake2s_simd128::update_last(64u32, &mut wv, s0, false, 0u64, 64u32, &ipad)
    }
    else
    {
        let block_len: u32 = 64u32;
        let n_blocks: u32 = data_len.wrapping_div(block_len);
        let rem: u32 = data_len.wrapping_rem(block_len);
        let scrut: crate::hmac::__uint32_t_uint32_t =
            if n_blocks > 0u32 && rem == 0u32
            {
                let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
                crate::hmac::__uint32_t_uint32_t
                { fst: n_blocks·, snd: data_len.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
            }
            else
            { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
        let n_blocks0: u32 = scrut.fst;
        let rem_len: u32 = scrut.snd;
        let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
        let full_blocks: (&[u8], &[u8]) = data.split_at(0usize);
        let rem0: (&[u8], &[u8]) = full_blocks.1.split_at(full_blocks_len as usize);
        let mut wv: [lib::intvector_intrinsics::vec128; 4] =
            [lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hash_blake2s_simd128::update_multi(64u32, &mut wv, s0, 0u64, &ipad, 1u32);
        let mut wv0: [lib::intvector_intrinsics::vec128; 4] =
            [lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hash_blake2s_simd128::update_multi(
            n_blocks0.wrapping_mul(64u32),
            &mut wv0,
            s0,
            block_len as u64,
            rem0.0,
            n_blocks0
        );
        let mut wv1: [lib::intvector_intrinsics::vec128; 4] =
            [lib::intvector_intrinsics::vec128_zero; 4usize];
        crate::hash_blake2s_simd128::update_last(
            rem_len,
            &mut wv1,
            s0,
            false,
            (64u32 as u64).wrapping_add(full_blocks_len as u64),
            rem_len,
            rem0.1
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_blake2s_simd128::finish(32u32, dst1.1, s0);
    let hash1: (&[u8], &[u8]) = dst1.1.split_at(0usize);
    crate::hash_blake2s_simd128::init(s0, 0u32, 32u32);
    let block_len: u32 = 64u32;
    let n_blocks: u32 = 32u32.wrapping_div(block_len);
    let rem: u32 = 32u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 32u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = hash1.1.split_at(0usize);
    let rem0: (&[u8], &[u8]) = full_blocks.1.split_at(full_blocks_len as usize);
    let mut wv: [lib::intvector_intrinsics::vec128; 4] =
        [lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hash_blake2s_simd128::update_multi(64u32, &mut wv, s0, 0u64, &opad, 1u32);
    let mut wv0: [lib::intvector_intrinsics::vec128; 4] =
        [lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hash_blake2s_simd128::update_multi(
        n_blocks0.wrapping_mul(64u32),
        &mut wv0,
        s0,
        block_len as u64,
        rem0.0,
        n_blocks0
    );
    let mut wv1: [lib::intvector_intrinsics::vec128; 4] =
        [lib::intvector_intrinsics::vec128_zero; 4usize];
    crate::hash_blake2s_simd128::update_last(
        rem_len,
        &mut wv1,
        s0,
        false,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem_len,
        rem0.1
    );
    crate::hash_blake2s_simd128::finish(32u32, dst, s0)
}
