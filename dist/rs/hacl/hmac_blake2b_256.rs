#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

/**
Write the HMAC-BLAKE2b MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
pub fn
compute_blake2b_256(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 128] = [0x00u8; 128usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 64u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_blake2b_simd256::hash_with_key(zeroes.0, 64u32, key, key_len, &[], 0u32) };
    let mut ipad: [u8; 128] = [0x36u8; 128usize];
    for i in 0u32..128u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 128] = [0x5cu8; 128usize];
    for i in 0u32..128u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [lib::intvector_intrinsics::vec256; 4] =
        [lib::intvector_intrinsics::vec256_zero; 4usize];
    crate::hash_blake2b_simd256::init(&mut s, 0u32, 64u32);
    let s0: &mut [lib::intvector_intrinsics::vec256] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [lib::intvector_intrinsics::vec256; 4] =
            [lib::intvector_intrinsics::vec256_zero; 4usize];
        crate::hash_blake2b_simd256::update_last(
            128u32,
            &mut wv,
            s0,
            false,
            fstar::uint128::uint64_to_uint128(0u64),
            128u32,
            &ipad
        )
    }
    else
    {
        let block_len: u32 = 128u32;
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
        let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
        let mut wv: [lib::intvector_intrinsics::vec256; 4] =
            [lib::intvector_intrinsics::vec256_zero; 4usize];
        crate::hash_blake2b_simd256::update_multi(
            128u32,
            &mut wv,
            s0,
            fstar::uint128::uint64_to_uint128(0u64),
            &ipad,
            1u32
        );
        let mut wv0: [lib::intvector_intrinsics::vec256; 4] =
            [lib::intvector_intrinsics::vec256_zero; 4usize];
        crate::hash_blake2b_simd256::update_multi(
            n_blocks0.wrapping_mul(128u32),
            &mut wv0,
            s0,
            fstar::uint128::uint64_to_uint128(block_len as u64),
            rem0.0,
            n_blocks0
        );
        let mut wv1: [lib::intvector_intrinsics::vec256; 4] =
            [lib::intvector_intrinsics::vec256_zero; 4usize];
        crate::hash_blake2b_simd256::update_last(
            rem_len,
            &mut wv1,
            s0,
            false,
            fstar::uint128::add(
                fstar::uint128::uint64_to_uint128(128u32 as u64),
                fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
            ),
            rem_len,
            rem0.1
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_blake2b_simd256::finish(64u32, dst1.1, s0);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_blake2b_simd256::init(s0, 0u32, 64u32);
    let block_len: u32 = 128u32;
    let n_blocks: u32 = 64u32.wrapping_div(block_len);
    let rem: u32 = 64u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 64u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    let mut wv: [lib::intvector_intrinsics::vec256; 4] =
        [lib::intvector_intrinsics::vec256_zero; 4usize];
    crate::hash_blake2b_simd256::update_multi(
        128u32,
        &mut wv,
        s0,
        fstar::uint128::uint64_to_uint128(0u64),
        &opad,
        1u32
    );
    let mut wv0: [lib::intvector_intrinsics::vec256; 4] =
        [lib::intvector_intrinsics::vec256_zero; 4usize];
    crate::hash_blake2b_simd256::update_multi(
        n_blocks0.wrapping_mul(128u32),
        &mut wv0,
        s0,
        fstar::uint128::uint64_to_uint128(block_len as u64),
        rem0.0,
        n_blocks0
    );
    let mut wv1: [lib::intvector_intrinsics::vec256; 4] =
        [lib::intvector_intrinsics::vec256_zero; 4usize];
    crate::hash_blake2b_simd256::update_last(
        rem_len,
        &mut wv1,
        s0,
        false,
        fstar::uint128::add(
            fstar::uint128::uint64_to_uint128(128u32 as u64),
            fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
        ),
        rem_len,
        rem0.1
    );
    crate::hash_blake2b_simd256::finish(64u32, dst, s0)
}
