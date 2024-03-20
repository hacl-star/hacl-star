#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn is_supported_alg(uu___: crate::hacl::streaming_types::hash_alg) -> bool
{
    match uu___
    {
        crate::hacl::streaming_types::hash_alg::SHA1 => true,
        crate::hacl::streaming_types::hash_alg::SHA2_256 => true,
        crate::hacl::streaming_types::hash_alg::SHA2_384 => true,
        crate::hacl::streaming_types::hash_alg::SHA2_512 => true,
        crate::hacl::streaming_types::hash_alg::Blake2S => true,
        crate::hacl::streaming_types::hash_alg::Blake2B => true,
        _ => false
    }
}

pub type supported_alg = crate::hacl::streaming_types::hash_alg;

pub const hash_256: (&mut [u8], &mut [u8], u32) () = crate::evercrypt::hash::hash_256;

pub fn compute_sha1(
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
    let ite: u32 = if key_len <= 64u32 { key_len } else { 20u32 };
    let zeroes: (&mut [u8], &mut [u8]) = nkey.1.split_at_mut(ite as usize);
    crate::lowstar::ignore::ignore::<&mut [u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hacl::hash_sha1::hash_oneshot(zeroes.0, key, key_len) };
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
    let mut s: [u32; 5] =
        [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32, 0xc3d2e1f0u32];
    if data_len == 0u32
    { crate::hacl::hash_sha1::update_last(&mut s, 0u64, &mut ipad, 64u32) }
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
        crate::hacl::hash_sha1::update_multi(&mut s, &mut ipad, 1u32);
        crate::hacl::hash_sha1::update_multi(&mut s, rem0.0, n_blocks0);
        crate::hacl::hash_sha1::update_last(
            &mut s,
            (64u32 as u64).wrapping_add(full_blocks_len as u64),
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_sha1::finish(&mut s, dst1.1);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_sha1::init(&mut s);
    let block_len: u32 = 64u32;
    let n_blocks: u32 = 20u32.wrapping_div(block_len);
    let rem: u32 = 20u32.wrapping_rem(block_len);
    let scrut: crate::hacl::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hacl::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 20u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hacl::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&mut [u8], &mut [u8]) = hash1.1.split_at_mut(0usize);
    let rem0: (&mut [u8], &mut [u8]) = full_blocks.1.split_at_mut(full_blocks_len as usize);
    crate::hacl::hash_sha1::update_multi(&mut s, &mut opad, 1u32);
    crate::hacl::hash_sha1::update_multi(&mut s, rem0.0, n_blocks0);
    crate::hacl::hash_sha1::update_last(
        &mut s,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem0.1,
        rem_len
    );
    crate::hacl::hash_sha1::finish(&mut s, dst)
}

pub fn compute_sha2_256(
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
    { hash_256(zeroes.0, key, key_len) };
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
    let mut st: [u32; 8] = [0u32; 8usize];
    for i in 0u32..8u32
    {
        let x: u32 = (&crate::hacl::hash_sha2::h256)[i as usize];
        let os: (&mut [u32], &mut [u32]) = (&mut st).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let s: &mut [u32] = &mut st;
    if data_len == 0u32
    {
        crate::hacl::hash_sha2::sha256_update_last(
            0u64.wrapping_add(64u32 as u64),
            64u32,
            &mut ipad,
            s
        )
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
        crate::evercrypt::hash::update_multi_256(s, &mut ipad, 1u32);
        crate::evercrypt::hash::update_multi_256(s, rem0.0, n_blocks0);
        crate::hacl::hash_sha2::sha256_update_last(
            (64u32 as u64).wrapping_add(full_blocks_len as u64).wrapping_add(rem_len as u64),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_sha2::sha256_finish(s, dst1.1);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_sha2::sha256_init(s);
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
    crate::evercrypt::hash::update_multi_256(s, &mut opad, 1u32);
    crate::evercrypt::hash::update_multi_256(s, rem0.0, n_blocks0);
    crate::hacl::hash_sha2::sha256_update_last(
        (64u32 as u64).wrapping_add(full_blocks_len as u64).wrapping_add(rem_len as u64),
        rem_len,
        rem0.1,
        s
    );
    crate::hacl::hash_sha2::sha256_finish(s, dst)
}

pub fn compute_sha2_384(
    dst: &mut [u8],
    key: &mut [u8],
    key_len: u32,
    data: &mut [u8],
    data_len: u32
) ->
    ()
{
    let l: u32 = 128u32;
    let mut key_block: Vec<u8> = vec![0x00u8; l as usize];
    let nkey: (&mut [u8], &mut [u8]) = (&mut key_block).split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 48u32 };
    let zeroes: (&mut [u8], &mut [u8]) = nkey.1.split_at_mut(ite as usize);
    crate::lowstar::ignore::ignore::<&mut [u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hacl::hash_sha2::hash_384(zeroes.0, key, key_len) };
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
    let mut st: [u64; 8] = [0u64; 8usize];
    for i in 0u32..8u32
    {
        let x: u64 = (&crate::hacl::hash_sha2::h384)[i as usize];
        let os: (&mut [u64], &mut [u64]) = (&mut st).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let s: &mut [u64] = &mut st;
    if data_len == 0u32
    {
        crate::hacl::hash_sha2::sha384_update_last(
            crate::fstar::uint128::add(
                crate::fstar::uint128::uint64_to_uint128(0u64),
                crate::fstar::uint128::uint64_to_uint128(128u32 as u64)
            ),
            128u32,
            &mut ipad,
            s
        )
    }
    else
    {
        let block_len: u32 = 128u32;
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
        crate::hacl::hash_sha2::sha384_update_nblocks(128u32, &mut ipad, s);
        crate::hacl::hash_sha2::sha384_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
        crate::hacl::hash_sha2::sha384_update_last(
            crate::fstar::uint128::add(
                crate::fstar::uint128::add(
                    crate::fstar::uint128::uint64_to_uint128(128u32 as u64),
                    crate::fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
                ),
                crate::fstar::uint128::uint64_to_uint128(rem_len as u64)
            ),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_sha2::sha384_finish(s, dst1.1);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_sha2::sha384_init(s);
    let block_len: u32 = 128u32;
    let n_blocks: u32 = 48u32.wrapping_div(block_len);
    let rem: u32 = 48u32.wrapping_rem(block_len);
    let scrut: crate::hacl::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hacl::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 48u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hacl::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&mut [u8], &mut [u8]) = hash1.1.split_at_mut(0usize);
    let rem0: (&mut [u8], &mut [u8]) = full_blocks.1.split_at_mut(full_blocks_len as usize);
    crate::hacl::hash_sha2::sha384_update_nblocks(128u32, &mut opad, s);
    crate::hacl::hash_sha2::sha384_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
    crate::hacl::hash_sha2::sha384_update_last(
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::uint64_to_uint128(128u32 as u64),
                crate::fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
            ),
            crate::fstar::uint128::uint64_to_uint128(rem_len as u64)
        ),
        rem_len,
        rem0.1,
        s
    );
    crate::hacl::hash_sha2::sha384_finish(s, dst)
}

pub fn compute_sha2_512(
    dst: &mut [u8],
    key: &mut [u8],
    key_len: u32,
    data: &mut [u8],
    data_len: u32
) ->
    ()
{
    let l: u32 = 128u32;
    let mut key_block: Vec<u8> = vec![0x00u8; l as usize];
    let nkey: (&mut [u8], &mut [u8]) = (&mut key_block).split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 64u32 };
    let zeroes: (&mut [u8], &mut [u8]) = nkey.1.split_at_mut(ite as usize);
    crate::lowstar::ignore::ignore::<&mut [u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hacl::hash_sha2::hash_512(zeroes.0, key, key_len) };
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
    let mut st: [u64; 8] = [0u64; 8usize];
    for i in 0u32..8u32
    {
        let x: u64 = (&crate::hacl::hash_sha2::h512)[i as usize];
        let os: (&mut [u64], &mut [u64]) = (&mut st).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let s: &mut [u64] = &mut st;
    if data_len == 0u32
    {
        crate::hacl::hash_sha2::sha512_update_last(
            crate::fstar::uint128::add(
                crate::fstar::uint128::uint64_to_uint128(0u64),
                crate::fstar::uint128::uint64_to_uint128(128u32 as u64)
            ),
            128u32,
            &mut ipad,
            s
        )
    }
    else
    {
        let block_len: u32 = 128u32;
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
        crate::hacl::hash_sha2::sha512_update_nblocks(128u32, &mut ipad, s);
        crate::hacl::hash_sha2::sha512_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
        crate::hacl::hash_sha2::sha512_update_last(
            crate::fstar::uint128::add(
                crate::fstar::uint128::add(
                    crate::fstar::uint128::uint64_to_uint128(128u32 as u64),
                    crate::fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
                ),
                crate::fstar::uint128::uint64_to_uint128(rem_len as u64)
            ),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_sha2::sha512_finish(s, dst1.1);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_sha2::sha512_init(s);
    let block_len: u32 = 128u32;
    let n_blocks: u32 = 64u32.wrapping_div(block_len);
    let rem: u32 = 64u32.wrapping_rem(block_len);
    let scrut: crate::hacl::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hacl::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 64u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hacl::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&mut [u8], &mut [u8]) = hash1.1.split_at_mut(0usize);
    let rem0: (&mut [u8], &mut [u8]) = full_blocks.1.split_at_mut(full_blocks_len as usize);
    crate::hacl::hash_sha2::sha512_update_nblocks(128u32, &mut opad, s);
    crate::hacl::hash_sha2::sha512_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
    crate::hacl::hash_sha2::sha512_update_last(
        crate::fstar::uint128::add(
            crate::fstar::uint128::add(
                crate::fstar::uint128::uint64_to_uint128(128u32 as u64),
                crate::fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
            ),
            crate::fstar::uint128::uint64_to_uint128(rem_len as u64)
        ),
        rem_len,
        rem0.1,
        s
    );
    crate::hacl::hash_sha2::sha512_finish(s, dst)
}

pub fn compute_blake2s(
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
    { crate::hacl::hash_blake2s::hash_with_key(zeroes.0, 32u32, key, key_len, &mut [], 0u32) };
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
    let mut s: [u32; 16] = [0u32; 16usize];
    crate::hacl::hash_blake2s::init(&mut s, 0u32, 32u32);
    let s0: &mut [u32] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [u32; 16] = [0u32; 16usize];
        crate::hacl::hash_blake2s::update_last(64u32, &mut wv, s0, 0u64, 64u32, &mut ipad)
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
        let mut wv: [u32; 16] = [0u32; 16usize];
        crate::hacl::hash_blake2s::update_multi(64u32, &mut wv, s0, 0u64, &mut ipad, 1u32);
        let mut wv0: [u32; 16] = [0u32; 16usize];
        crate::hacl::hash_blake2s::update_multi(
            n_blocks0.wrapping_mul(64u32),
            &mut wv0,
            s0,
            block_len as u64,
            rem0.0,
            n_blocks0
        );
        let mut wv1: [u32; 16] = [0u32; 16usize];
        crate::hacl::hash_blake2s::update_last(
            rem_len,
            &mut wv1,
            s0,
            (64u32 as u64).wrapping_add(full_blocks_len as u64),
            rem_len,
            rem0.1
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_blake2s::finish(32u32, dst1.1, s0);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_blake2s::init(s0, 0u32, 32u32);
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
    let mut wv: [u32; 16] = [0u32; 16usize];
    crate::hacl::hash_blake2s::update_multi(64u32, &mut wv, s0, 0u64, &mut opad, 1u32);
    let mut wv0: [u32; 16] = [0u32; 16usize];
    crate::hacl::hash_blake2s::update_multi(
        n_blocks0.wrapping_mul(64u32),
        &mut wv0,
        s0,
        block_len as u64,
        rem0.0,
        n_blocks0
    );
    let mut wv1: [u32; 16] = [0u32; 16usize];
    crate::hacl::hash_blake2s::update_last(
        rem_len,
        &mut wv1,
        s0,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem_len,
        rem0.1
    );
    crate::hacl::hash_blake2s::finish(32u32, dst, s0)
}

pub fn compute_blake2b(
    dst: &mut [u8],
    key: &mut [u8],
    key_len: u32,
    data: &mut [u8],
    data_len: u32
) ->
    ()
{
    let l: u32 = 128u32;
    let mut key_block: Vec<u8> = vec![0x00u8; l as usize];
    let nkey: (&mut [u8], &mut [u8]) = (&mut key_block).split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 64u32 };
    let zeroes: (&mut [u8], &mut [u8]) = nkey.1.split_at_mut(ite as usize);
    crate::lowstar::ignore::ignore::<&mut [u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hacl::hash_blake2b::hash_with_key(zeroes.0, 64u32, key, key_len, &mut [], 0u32) };
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
    let mut s: [u64; 16] = [0u64; 16usize];
    crate::hacl::hash_blake2b::init(&mut s, 0u32, 64u32);
    let s0: &mut [u64] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [u64; 16] = [0u64; 16usize];
        crate::hacl::hash_blake2b::update_last(
            128u32,
            &mut wv,
            s0,
            crate::fstar::uint128::uint64_to_uint128(0u64),
            128u32,
            &mut ipad
        )
    }
    else
    {
        let block_len: u32 = 128u32;
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
        let mut wv: [u64; 16] = [0u64; 16usize];
        crate::hacl::hash_blake2b::update_multi(
            128u32,
            &mut wv,
            s0,
            crate::fstar::uint128::uint64_to_uint128(0u64),
            &mut ipad,
            1u32
        );
        let mut wv0: [u64; 16] = [0u64; 16usize];
        crate::hacl::hash_blake2b::update_multi(
            n_blocks0.wrapping_mul(128u32),
            &mut wv0,
            s0,
            crate::fstar::uint128::uint64_to_uint128(block_len as u64),
            rem0.0,
            n_blocks0
        );
        let mut wv1: [u64; 16] = [0u64; 16usize];
        crate::hacl::hash_blake2b::update_last(
            rem_len,
            &mut wv1,
            s0,
            crate::fstar::uint128::add(
                crate::fstar::uint128::uint64_to_uint128(128u32 as u64),
                crate::fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
            ),
            rem_len,
            rem0.1
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = (&mut ipad).split_at_mut(0usize);
    crate::hacl::hash_blake2b::finish(64u32, dst1.1, s0);
    let hash1: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(0usize);
    crate::hacl::hash_blake2b::init(s0, 0u32, 64u32);
    let block_len: u32 = 128u32;
    let n_blocks: u32 = 64u32.wrapping_div(block_len);
    let rem: u32 = 64u32.wrapping_rem(block_len);
    let scrut: crate::hacl::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hacl::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 64u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hacl::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&mut [u8], &mut [u8]) = hash1.1.split_at_mut(0usize);
    let rem0: (&mut [u8], &mut [u8]) = full_blocks.1.split_at_mut(full_blocks_len as usize);
    let mut wv: [u64; 16] = [0u64; 16usize];
    crate::hacl::hash_blake2b::update_multi(
        128u32,
        &mut wv,
        s0,
        crate::fstar::uint128::uint64_to_uint128(0u64),
        &mut opad,
        1u32
    );
    let mut wv0: [u64; 16] = [0u64; 16usize];
    crate::hacl::hash_blake2b::update_multi(
        n_blocks0.wrapping_mul(128u32),
        &mut wv0,
        s0,
        crate::fstar::uint128::uint64_to_uint128(block_len as u64),
        rem0.0,
        n_blocks0
    );
    let mut wv1: [u64; 16] = [0u64; 16usize];
    crate::hacl::hash_blake2b::update_last(
        rem_len,
        &mut wv1,
        s0,
        crate::fstar::uint128::add(
            crate::fstar::uint128::uint64_to_uint128(128u32 as u64),
            crate::fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
        ),
        rem_len,
        rem0.1
    );
    crate::hacl::hash_blake2b::finish(64u32, dst, s0)
}

pub fn compute(
    a: crate::hacl::streaming_types::hash_alg,
    mac: &mut [u8],
    key: &mut [u8],
    keylen: u32,
    data: &mut [u8],
    datalen: u32
) ->
    ()
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::SHA1 =>
          compute_sha1(mac, key, keylen, data, datalen),
        crate::hacl::streaming_types::hash_alg::SHA2_256 =>
          compute_sha2_256(mac, key, keylen, data, datalen),
        crate::hacl::streaming_types::hash_alg::SHA2_384 =>
          compute_sha2_384(mac, key, keylen, data, datalen),
        crate::hacl::streaming_types::hash_alg::SHA2_512 =>
          compute_sha2_512(mac, key, keylen, data, datalen),
        crate::hacl::streaming_types::hash_alg::Blake2S =>
          compute_blake2s(mac, key, keylen, data, datalen),
        crate::hacl::streaming_types::hash_alg::Blake2B =>
          compute_blake2b(mac, key, keylen, data, datalen),
        _ => panic!("Precondition of the function most likely violated")
    }
}
