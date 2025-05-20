#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[derive(PartialEq, Clone, Copy)]
pub(crate) struct __uint32_t_uint32_t
{ pub fst: u32, pub snd: u32 }

/**
Write the HMAC-MD5 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 byte.
`dst` must point to 16 bytes of memory.
*/
pub fn
compute_md5(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 64] = [0x00u8; 64usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 16u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_md5::hash_oneshot(zeroes.0, key, key_len) };
    let mut ipad: [u8; 64] = [0x36u8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 64] = [0x5cu8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u32; 4] = [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32];
    if data_len == 0u32
    { crate::hash_md5::update_last(&mut s, 0u64, &ipad, 64u32) }
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
        let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
        crate::hash_md5::update_multi(&mut s, &ipad, 1u32);
        crate::hash_md5::update_multi(&mut s, rem0.0, n_blocks0);
        crate::hash_md5::update_last(
            &mut s,
            (64u32 as u64).wrapping_add(full_blocks_len as u64),
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_md5::finish(&s, dst1.1);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_md5::init(&mut s);
    let block_len: u32 = 64u32;
    let n_blocks: u32 = 16u32.wrapping_div(block_len);
    let rem: u32 = 16u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 16u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_md5::update_multi(&mut s, &opad, 1u32);
    crate::hash_md5::update_multi(&mut s, rem0.0, n_blocks0);
    crate::hash_md5::update_last(
        &mut s,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem0.1,
        rem_len
    );
    crate::hash_md5::finish(&s, dst)
}

/**
Write the HMAC-SHA-1 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 byte.
`dst` must point to 20 bytes of memory.
*/
pub fn
compute_sha1(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 64] = [0x00u8; 64usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 20u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha1::hash_oneshot(zeroes.0, key, key_len) };
    let mut ipad: [u8; 64] = [0x36u8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 64] = [0x5cu8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u32; 5] =
        [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32, 0xc3d2e1f0u32];
    if data_len == 0u32
    { crate::hash_sha1::update_last(&mut s, 0u64, &ipad, 64u32) }
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
        let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
        crate::hash_sha1::update_multi(&mut s, &ipad, 1u32);
        crate::hash_sha1::update_multi(&mut s, rem0.0, n_blocks0);
        crate::hash_sha1::update_last(
            &mut s,
            (64u32 as u64).wrapping_add(full_blocks_len as u64),
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_sha1::finish(&s, dst1.1);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha1::init(&mut s);
    let block_len: u32 = 64u32;
    let n_blocks: u32 = 20u32.wrapping_div(block_len);
    let rem: u32 = 20u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 20u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha1::update_multi(&mut s, &opad, 1u32);
    crate::hash_sha1::update_multi(&mut s, rem0.0, n_blocks0);
    crate::hash_sha1::update_last(
        &mut s,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem0.1,
        rem_len
    );
    crate::hash_sha1::finish(&s, dst)
}

/**
Write the HMAC-SHA-2-224 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 28 bytes of memory.
*/
pub fn
compute_sha2_224(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 64] = [0x00u8; 64usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 28u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha2::hash_224(zeroes.0, key, key_len) };
    let mut ipad: [u8; 64] = [0x36u8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 64] = [0x5cu8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut st: [u32; 8] = [0u32; 8usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = (&crate::hash_sha2::h224)[i as usize];
            let os: (&mut [u32], &mut [u32]) = st.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let s: &mut [u32] = &mut st;
    if data_len == 0u32
    { crate::hash_sha2::sha224_update_last(0u64.wrapping_add(64u32 as u64), 64u32, &ipad, s) }
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
        let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
        crate::hash_sha2::sha224_update_nblocks(64u32, &ipad, s);
        crate::hash_sha2::sha224_update_nblocks(n_blocks0.wrapping_mul(64u32), rem0.0, s);
        crate::hash_sha2::sha224_update_last(
            (64u32 as u64).wrapping_add(full_blocks_len as u64).wrapping_add(rem_len as u64),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_sha2::sha224_finish(s, dst1.1);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha2::sha224_init(s);
    let block_len: u32 = 64u32;
    let n_blocks: u32 = 28u32.wrapping_div(block_len);
    let rem: u32 = 28u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 28u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha2::sha224_update_nblocks(64u32, &opad, s);
    crate::hash_sha2::sha224_update_nblocks(n_blocks0.wrapping_mul(64u32), rem0.0, s);
    crate::hash_sha2::sha224_update_last(
        (64u32 as u64).wrapping_add(full_blocks_len as u64).wrapping_add(rem_len as u64),
        rem_len,
        rem0.1,
        s
    );
    crate::hash_sha2::sha224_finish(s, dst)
}

/**
Write the HMAC-SHA-2-256 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory.
*/
pub fn
compute_sha2_256(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 64] = [0x00u8; 64usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 32u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha2::hash_256(zeroes.0, key, key_len) };
    let mut ipad: [u8; 64] = [0x36u8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 64] = [0x5cu8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut st: [u32; 8] = [0u32; 8usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = (&crate::hash_sha2::h256)[i as usize];
            let os: (&mut [u32], &mut [u32]) = st.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let s: &mut [u32] = &mut st;
    if data_len == 0u32
    { crate::hash_sha2::sha256_update_last(0u64.wrapping_add(64u32 as u64), 64u32, &ipad, s) }
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
        let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
        crate::hash_sha2::sha256_update_nblocks(64u32, &ipad, s);
        crate::hash_sha2::sha256_update_nblocks(n_blocks0.wrapping_mul(64u32), rem0.0, s);
        crate::hash_sha2::sha256_update_last(
            (64u32 as u64).wrapping_add(full_blocks_len as u64).wrapping_add(rem_len as u64),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_sha2::sha256_finish(s, dst1.1);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha2::sha256_init(s);
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
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha2::sha256_update_nblocks(64u32, &opad, s);
    crate::hash_sha2::sha256_update_nblocks(n_blocks0.wrapping_mul(64u32), rem0.0, s);
    crate::hash_sha2::sha256_update_last(
        (64u32 as u64).wrapping_add(full_blocks_len as u64).wrapping_add(rem_len as u64),
        rem_len,
        rem0.1,
        s
    );
    crate::hash_sha2::sha256_finish(s, dst)
}

/**
Write the HMAC-SHA-2-384 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 48 bytes of memory.
*/
pub fn
compute_sha2_384(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 128] = [0x00u8; 128usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 48u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha2::hash_384(zeroes.0, key, key_len) };
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
    let mut st: [u64; 8] = [0u64; 8usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = (&crate::hash_sha2::h384)[i as usize];
            let os: (&mut [u64], &mut [u64]) = st.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let s: &mut [u64] = &mut st;
    if data_len == 0u32
    {
        crate::hash_sha2::sha384_update_last(
            fstar::uint128::add(
                fstar::uint128::uint64_to_uint128(0u64),
                fstar::uint128::uint64_to_uint128(128u32 as u64)
            ),
            128u32,
            &ipad,
            s
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
        crate::hash_sha2::sha384_update_nblocks(128u32, &ipad, s);
        crate::hash_sha2::sha384_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
        crate::hash_sha2::sha384_update_last(
            fstar::uint128::add(
                fstar::uint128::add(
                    fstar::uint128::uint64_to_uint128(128u32 as u64),
                    fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
                ),
                fstar::uint128::uint64_to_uint128(rem_len as u64)
            ),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_sha2::sha384_finish(s, dst1.1);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha2::sha384_init(s);
    let block_len: u32 = 128u32;
    let n_blocks: u32 = 48u32.wrapping_div(block_len);
    let rem: u32 = 48u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 48u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha2::sha384_update_nblocks(128u32, &opad, s);
    crate::hash_sha2::sha384_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
    crate::hash_sha2::sha384_update_last(
        fstar::uint128::add(
            fstar::uint128::add(
                fstar::uint128::uint64_to_uint128(128u32 as u64),
                fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
            ),
            fstar::uint128::uint64_to_uint128(rem_len as u64)
        ),
        rem_len,
        rem0.1,
        s
    );
    crate::hash_sha2::sha384_finish(s, dst)
}

/**
Write the HMAC-SHA-2-512 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
pub fn
compute_sha2_512(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 128] = [0x00u8; 128usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 64u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha2::hash_512(zeroes.0, key, key_len) };
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
    let mut st: [u64; 8] = [0u64; 8usize];
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: u64 = (&crate::hash_sha2::h512)[i as usize];
            let os: (&mut [u64], &mut [u64]) = st.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let s: &mut [u64] = &mut st;
    if data_len == 0u32
    {
        crate::hash_sha2::sha512_update_last(
            fstar::uint128::add(
                fstar::uint128::uint64_to_uint128(0u64),
                fstar::uint128::uint64_to_uint128(128u32 as u64)
            ),
            128u32,
            &ipad,
            s
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
        crate::hash_sha2::sha512_update_nblocks(128u32, &ipad, s);
        crate::hash_sha2::sha512_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
        crate::hash_sha2::sha512_update_last(
            fstar::uint128::add(
                fstar::uint128::add(
                    fstar::uint128::uint64_to_uint128(128u32 as u64),
                    fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
                ),
                fstar::uint128::uint64_to_uint128(rem_len as u64)
            ),
            rem_len,
            rem0.1,
            s
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    crate::hash_sha2::sha512_finish(s, dst1.1);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha2::sha512_init(s);
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
    crate::hash_sha2::sha512_update_nblocks(128u32, &opad, s);
    crate::hash_sha2::sha512_update_nblocks(n_blocks0.wrapping_mul(128u32), rem0.0, s);
    crate::hash_sha2::sha512_update_last(
        fstar::uint128::add(
            fstar::uint128::add(
                fstar::uint128::uint64_to_uint128(128u32 as u64),
                fstar::uint128::uint64_to_uint128(full_blocks_len as u64)
            ),
            fstar::uint128::uint64_to_uint128(rem_len as u64)
        ),
        rem_len,
        rem0.1,
        s
    );
    crate::hash_sha2::sha512_finish(s, dst)
}

/**
Write the HMAC-SHA-3-224 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 144 bytes.
`dst` must point to 28 bytes of memory.
*/
pub fn
compute_sha3_224(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 144] = [0x00u8; 144usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 144u32 { key_len } else { 28u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 144u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha3::sha3_224(zeroes.0, key, key_len) };
    let mut ipad: [u8; 144] = [0x36u8; 144usize];
    for i in 0u32..144u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 144] = [0x5cu8; 144usize];
    for i in 0u32..144u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u64; 25] = [0u64; 25usize];
    if data_len == 0u32
    {
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_224,
            &mut s,
            &ipad,
            144u32
        )
    }
    else
    {
        let block_len: u32 = 144u32;
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
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_224,
            &mut s,
            &ipad,
            1u32
        );
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_224,
            &mut s,
            rem0.0,
            n_blocks0
        );
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_224,
            &mut s,
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    let remOut: u32 = 28u32;
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws: [u64; 32] = [0u64; 32usize];
    ((&mut ws)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&ws)[i as usize]
        )
    );
    (dst1.1[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_224, &mut s);
    let block_len: u32 = 144u32;
    let n_blocks: u32 = 28u32.wrapping_div(block_len);
    let rem: u32 = 28u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 28u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_224,
        &mut s,
        &opad,
        1u32
    );
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_224,
        &mut s,
        rem0.0,
        n_blocks0
    );
    crate::hash_sha3::update_last_sha3(
        crate::streaming_types::hash_alg::SHA3_224,
        &mut s,
        rem0.1,
        rem_len
    );
    let remOut0: u32 = 28u32;
    let mut hbuf0: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf0)[i.wrapping_mul(8u32) as usize..],
            (&ws0)[i as usize]
        )
    );
    (dst[28u32.wrapping_sub(remOut0) as usize..28u32.wrapping_sub(remOut0) as usize
    +
    remOut0 as usize]).copy_from_slice(&(&(&hbuf0)[0usize..])[0usize..remOut0 as usize])
}

/**
Write the HMAC-SHA-3-256 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 136 bytes.
`dst` must point to 32 bytes of memory.
*/
pub fn
compute_sha3_256(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 136] = [0x00u8; 136usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 136u32 { key_len } else { 32u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 136u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha3::sha3_256(zeroes.0, key, key_len) };
    let mut ipad: [u8; 136] = [0x36u8; 136usize];
    for i in 0u32..136u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 136] = [0x5cu8; 136usize];
    for i in 0u32..136u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u64; 25] = [0u64; 25usize];
    if data_len == 0u32
    {
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_256,
            &mut s,
            &ipad,
            136u32
        )
    }
    else
    {
        let block_len: u32 = 136u32;
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
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_256,
            &mut s,
            &ipad,
            1u32
        );
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_256,
            &mut s,
            rem0.0,
            n_blocks0
        );
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_256,
            &mut s,
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    let remOut: u32 = 32u32;
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws: [u64; 32] = [0u64; 32usize];
    ((&mut ws)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&ws)[i as usize]
        )
    );
    (dst1.1[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_256, &mut s);
    let block_len: u32 = 136u32;
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
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_256,
        &mut s,
        &opad,
        1u32
    );
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_256,
        &mut s,
        rem0.0,
        n_blocks0
    );
    crate::hash_sha3::update_last_sha3(
        crate::streaming_types::hash_alg::SHA3_256,
        &mut s,
        rem0.1,
        rem_len
    );
    let remOut0: u32 = 32u32;
    let mut hbuf0: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf0)[i.wrapping_mul(8u32) as usize..],
            (&ws0)[i as usize]
        )
    );
    (dst[32u32.wrapping_sub(remOut0) as usize..32u32.wrapping_sub(remOut0) as usize
    +
    remOut0 as usize]).copy_from_slice(&(&(&hbuf0)[0usize..])[0usize..remOut0 as usize])
}

/**
Write the HMAC-SHA-3-384 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 104 bytes.
`dst` must point to 48 bytes of memory.
*/
pub fn
compute_sha3_384(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 104] = [0x00u8; 104usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 104u32 { key_len } else { 48u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 104u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha3::sha3_384(zeroes.0, key, key_len) };
    let mut ipad: [u8; 104] = [0x36u8; 104usize];
    for i in 0u32..104u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 104] = [0x5cu8; 104usize];
    for i in 0u32..104u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u64; 25] = [0u64; 25usize];
    if data_len == 0u32
    {
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_384,
            &mut s,
            &ipad,
            104u32
        )
    }
    else
    {
        let block_len: u32 = 104u32;
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
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_384,
            &mut s,
            &ipad,
            1u32
        );
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_384,
            &mut s,
            rem0.0,
            n_blocks0
        );
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_384,
            &mut s,
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    let remOut: u32 = 48u32;
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws: [u64; 32] = [0u64; 32usize];
    ((&mut ws)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&ws)[i as usize]
        )
    );
    (dst1.1[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_384, &mut s);
    let block_len: u32 = 104u32;
    let n_blocks: u32 = 48u32.wrapping_div(block_len);
    let rem: u32 = 48u32.wrapping_rem(block_len);
    let scrut: crate::hmac::__uint32_t_uint32_t =
        if n_blocks > 0u32 && rem == 0u32
        {
            let n_blocks·: u32 = n_blocks.wrapping_sub(1u32);
            crate::hmac::__uint32_t_uint32_t
            { fst: n_blocks·, snd: 48u32.wrapping_sub(n_blocks·.wrapping_mul(block_len)) }
        }
        else
        { crate::hmac::__uint32_t_uint32_t { fst: n_blocks, snd: rem } };
    let n_blocks0: u32 = scrut.fst;
    let rem_len: u32 = scrut.snd;
    let full_blocks_len: u32 = n_blocks0.wrapping_mul(block_len);
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_384,
        &mut s,
        &opad,
        1u32
    );
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_384,
        &mut s,
        rem0.0,
        n_blocks0
    );
    crate::hash_sha3::update_last_sha3(
        crate::streaming_types::hash_alg::SHA3_384,
        &mut s,
        rem0.1,
        rem_len
    );
    let remOut0: u32 = 48u32;
    let mut hbuf0: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf0)[i.wrapping_mul(8u32) as usize..],
            (&ws0)[i as usize]
        )
    );
    (dst[48u32.wrapping_sub(remOut0) as usize..48u32.wrapping_sub(remOut0) as usize
    +
    remOut0 as usize]).copy_from_slice(&(&(&hbuf0)[0usize..])[0usize..remOut0 as usize])
}

/**
Write the HMAC-SHA-3-512 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 72 bytes.
`dst` must point to 64 bytes of memory.
*/
pub fn
compute_sha3_512(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 72] = [0x00u8; 72usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 72u32 { key_len } else { 64u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 72u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_sha3::sha3_512(zeroes.0, key, key_len) };
    let mut ipad: [u8; 72] = [0x36u8; 72usize];
    for i in 0u32..72u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 72] = [0x5cu8; 72usize];
    for i in 0u32..72u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u64; 25] = [0u64; 25usize];
    if data_len == 0u32
    {
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_512,
            &mut s,
            &ipad,
            72u32
        )
    }
    else
    {
        let block_len: u32 = 72u32;
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
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_512,
            &mut s,
            &ipad,
            1u32
        );
        crate::hash_sha3::update_multi_sha3(
            crate::streaming_types::hash_alg::SHA3_512,
            &mut s,
            rem0.0,
            n_blocks0
        );
        crate::hash_sha3::update_last_sha3(
            crate::streaming_types::hash_alg::SHA3_512,
            &mut s,
            rem0.1,
            rem_len
        )
    };
    let dst1: (&mut [u8], &mut [u8]) = ipad.split_at_mut(0usize);
    let remOut: u32 = 64u32;
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let mut ws: [u64; 32] = [0u64; 32usize];
    ((&mut ws)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
            (&ws)[i as usize]
        )
    );
    (dst1.1[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize
    +
    remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize]);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_512, &mut s);
    let block_len: u32 = 72u32;
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
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_512,
        &mut s,
        &opad,
        1u32
    );
    crate::hash_sha3::update_multi_sha3(
        crate::streaming_types::hash_alg::SHA3_512,
        &mut s,
        rem0.0,
        n_blocks0
    );
    crate::hash_sha3::update_last_sha3(
        crate::streaming_types::hash_alg::SHA3_512,
        &mut s,
        rem0.1,
        rem_len
    );
    let remOut0: u32 = 64u32;
    let mut hbuf0: [u8; 256] = [0u8; 256usize];
    let mut ws0: [u64; 32] = [0u64; 32usize];
    ((&mut ws0)[0usize..25usize]).copy_from_slice(&(&s)[0usize..25usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store64_le(
            &mut (&mut hbuf0)[i.wrapping_mul(8u32) as usize..],
            (&ws0)[i as usize]
        )
    );
    (dst[64u32.wrapping_sub(remOut0) as usize..64u32.wrapping_sub(remOut0) as usize
    +
    remOut0 as usize]).copy_from_slice(&(&(&hbuf0)[0usize..])[0usize..remOut0 as usize])
}

/**
Write the HMAC-BLAKE2s MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory.
*/
pub fn
compute_blake2s_32(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 64] = [0x00u8; 64usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 64u32 { key_len } else { 32u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 64u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_blake2s::hash_with_key(zeroes.0, 32u32, key, key_len, &[], 0u32) };
    let mut ipad: [u8; 64] = [0x36u8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&ipad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut ipad)[i as usize] = xi ^ yi
    };
    let mut opad: [u8; 64] = [0x5cu8; 64usize];
    for i in 0u32..64u32
    {
        let xi: u8 = (&opad)[i as usize];
        let yi: u8 = (&key_block)[i as usize];
        (&mut opad)[i as usize] = xi ^ yi
    };
    let mut s: [u32; 16] = [0u32; 16usize];
    crate::hash_blake2s::init(&mut s, 0u32, 32u32);
    let s0: &mut [u32] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [u32; 16] = [0u32; 16usize];
        crate::hash_blake2s::update_last(64u32, &mut wv, s0, false, 0u64, 64u32, &ipad)
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
        let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
        let mut wv: [u32; 16] = [0u32; 16usize];
        crate::hash_blake2s::update_multi(64u32, &mut wv, s0, 0u64, &ipad, 1u32);
        let mut wv0: [u32; 16] = [0u32; 16usize];
        crate::hash_blake2s::update_multi(
            n_blocks0.wrapping_mul(64u32),
            &mut wv0,
            s0,
            block_len as u64,
            rem0.0,
            n_blocks0
        );
        let mut wv1: [u32; 16] = [0u32; 16usize];
        crate::hash_blake2s::update_last(
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
    crate::hash_blake2s::finish(32u32, dst1.1, s0);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_blake2s::init(s0, 0u32, 32u32);
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
    let full_blocks: (&[u8], &[u8]) = (hash1.1).split_at(0usize);
    let rem0: (&[u8], &[u8]) = (full_blocks.1).split_at(full_blocks_len as usize);
    let mut wv: [u32; 16] = [0u32; 16usize];
    crate::hash_blake2s::update_multi(64u32, &mut wv, s0, 0u64, &opad, 1u32);
    let mut wv0: [u32; 16] = [0u32; 16usize];
    crate::hash_blake2s::update_multi(
        n_blocks0.wrapping_mul(64u32),
        &mut wv0,
        s0,
        block_len as u64,
        rem0.0,
        n_blocks0
    );
    let mut wv1: [u32; 16] = [0u32; 16usize];
    crate::hash_blake2s::update_last(
        rem_len,
        &mut wv1,
        s0,
        false,
        (64u32 as u64).wrapping_add(full_blocks_len as u64),
        rem_len,
        rem0.1
    );
    crate::hash_blake2s::finish(32u32, dst, s0)
}

/**
Write the HMAC-BLAKE2b MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory.
*/
pub fn
compute_blake2b_32(dst: &mut [u8], key: &[u8], key_len: u32, data: &[u8], data_len: u32)
{
    let mut key_block: [u8; 128] = [0x00u8; 128usize];
    let nkey: (&mut [u8], &mut [u8]) = key_block.split_at_mut(0usize);
    let ite: u32 = if key_len <= 128u32 { key_len } else { 64u32 };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if key_len <= 128u32
    { (zeroes.0[0usize..key_len as usize]).copy_from_slice(&key[0usize..key_len as usize]) }
    else
    { crate::hash_blake2b::hash_with_key(zeroes.0, 64u32, key, key_len, &[], 0u32) };
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
    let mut s: [u64; 16] = [0u64; 16usize];
    crate::hash_blake2b::init(&mut s, 0u32, 64u32);
    let s0: &mut [u64] = &mut s;
    if data_len == 0u32
    {
        let mut wv: [u64; 16] = [0u64; 16usize];
        crate::hash_blake2b::update_last(
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
        let mut wv: [u64; 16] = [0u64; 16usize];
        crate::hash_blake2b::update_multi(
            128u32,
            &mut wv,
            s0,
            fstar::uint128::uint64_to_uint128(0u64),
            &ipad,
            1u32
        );
        let mut wv0: [u64; 16] = [0u64; 16usize];
        crate::hash_blake2b::update_multi(
            n_blocks0.wrapping_mul(128u32),
            &mut wv0,
            s0,
            fstar::uint128::uint64_to_uint128(block_len as u64),
            rem0.0,
            n_blocks0
        );
        let mut wv1: [u64; 16] = [0u64; 16usize];
        crate::hash_blake2b::update_last(
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
    crate::hash_blake2b::finish(64u32, dst1.1, s0);
    let hash1: (&[u8], &[u8]) = (dst1.1).split_at(0usize);
    crate::hash_blake2b::init(s0, 0u32, 64u32);
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
    let mut wv: [u64; 16] = [0u64; 16usize];
    crate::hash_blake2b::update_multi(
        128u32,
        &mut wv,
        s0,
        fstar::uint128::uint64_to_uint128(0u64),
        &opad,
        1u32
    );
    let mut wv0: [u64; 16] = [0u64; 16usize];
    crate::hash_blake2b::update_multi(
        n_blocks0.wrapping_mul(128u32),
        &mut wv0,
        s0,
        fstar::uint128::uint64_to_uint128(block_len as u64),
        rem0.0,
        n_blocks0
    );
    let mut wv1: [u64; 16] = [0u64; 16usize];
    crate::hash_blake2b::update_last(
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
    crate::hash_blake2b::finish(64u32, dst, s0)
}
