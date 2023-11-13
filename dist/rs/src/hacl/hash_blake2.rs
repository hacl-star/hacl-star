pub fn blake2b_init(hash: &mut [u64], kk: u32, nn: u32) -> ()
{
    let r0: (&mut [u64], &mut [u64]) = hash.split_at_mut(0usize);
    let r1: (&mut [u64], &mut [u64]) = r0.1.split_at_mut(4usize);
    let r2: (&mut [u64], &mut [u64]) = r1.1.split_at_mut(4usize);
    let r3: (&mut [u64], &mut [u64]) = r2.1.split_at_mut(4usize);
    let iv0: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[0usize];
    let iv1: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[1usize];
    let iv2: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[2usize];
    let iv3: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[3usize];
    let iv4: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[4usize];
    let iv5: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[5usize];
    let iv6: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[6usize];
    let iv7: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[7usize];
    r3.0[0usize] = iv0;
    r3.0[1usize] = iv1;
    r3.0[2usize] = iv2;
    r3.0[3usize] = iv3;
    r3.1[0usize] = iv4;
    r3.1[1usize] = iv5;
    r3.1[2usize] = iv6;
    r3.1[3usize] = iv7;
    let kk_shift_8: u64 = (kk as u64).wrapping_shl(8u32);
    let iv0_: u64 = iv0 ^ (0x01010000u64 ^ (kk_shift_8 ^ nn as u64));
    r1.0[0usize] = iv0_;
    r1.0[1usize] = iv1;
    r1.0[2usize] = iv2;
    r1.0[3usize] = iv3;
    r2.0[0usize] = iv4;
    r2.0[1usize] = iv5;
    r2.0[2usize] = iv6;
    r2.0[3usize] = iv7
}

pub fn blake2b_update_key(wv: &mut [u64], hash: &mut [u64], kk: u32, k: &mut [u8], ll: u32) ->
    ()
{
    let lb: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::uint64_to_uint128(128u32 as u64);
    let mut b: [u8; 128] = [0u8; 128usize];
    ((&mut b)[0usize..0usize + kk as usize]).copy_from_slice(&k[0usize..0usize + kk as usize]);
    if ll == 0u32
    { crate::hacl::blake2b_32::blake2b_update_block(wv, hash, truebool, lb, &mut b) }
    else
    { crate::hacl::blake2b_32::blake2b_update_block(wv, hash, falsebool, lb, &mut b) };
    crate::lib::memzero0::memzero::<u8>(&mut b, 128u32)
}

pub fn blake2b_update_multi(
    len: u32,
    wv: &mut [u64],
    hash: &mut [u64],
    prev: crate::fstar::uint128::uint128,
    blocks: &mut [u8],
    nb: u32
) ->
    ()
{
    crate::lowstar::ignore::ignore::<u32>(len);
    for i in 0u32..nb
    {
        let totlen: crate::fstar::uint128::uint128 =
            crate::fstar::uint128::add_mod(
                prev,
                crate::fstar::uint128::uint64_to_uint128(
                    i.wrapping_add(1u32).wrapping_mul(128u32) as u64
                )
            );
        let b: (&mut [u8], &mut [u8]) = blocks.split_at_mut(i.wrapping_mul(128u32) as usize);
        crate::hacl::blake2b_32::blake2b_update_block(wv, hash, falsebool, totlen, b.1)
    }
}

pub fn blake2b_update_last(
    len: u32,
    wv: &mut [u64],
    hash: &mut [u64],
    prev: crate::fstar::uint128::uint128,
    rem: u32,
    d: &mut [u8]
) ->
    ()
{
    let mut b: [u8; 128] = [0u8; 128usize];
    let last: (&mut [u8], &mut [u8]) = d.split_at_mut(len.wrapping_sub(rem) as usize);
    ((&mut b)[0usize..0usize + rem as usize]).copy_from_slice(
        &last.1[0usize..0usize + rem as usize]
    );
    let totlen: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::add_mod(prev, crate::fstar::uint128::uint64_to_uint128(len as u64));
    crate::hacl::blake2b_32::blake2b_update_block(wv, hash, truebool, totlen, &mut b);
    crate::lib::memzero0::memzero::<u8>(&mut b, 128u32)
}

#[inline] fn blake2b_update(
    wv: &mut [u64],
    hash: &mut [u64],
    kk: u32,
    k: &mut [u8],
    ll: u32,
    d: &mut [u8]
) ->
    ()
{
    let lb: crate::fstar::uint128::uint128 =
        crate::fstar::uint128::uint64_to_uint128(128u32 as u64);
    if kk > 0u32
    {
        blake2b_update_key(wv, hash, kk, k, ll);
        if ! ll == 0u32 { crate::hacl::blake2b_32::blake2b_update_blocks(ll, wv, hash, lb, d) }
    }
    else
    {
        crate::hacl::blake2b_32::blake2b_update_blocks(
            ll,
            wv,
            hash,
            crate::fstar::uint128::uint64_to_uint128(0u32 as u64),
            d
        )
    }
}

pub fn blake2b_finish(nn: u32, output: &mut [u8], hash: &mut [u64]) -> ()
{
    let mut b: [u8; 64] = [0u8; 64usize];
    let first: (&mut [u8], &mut [u8]) = (&mut b).split_at_mut(0usize);
    let second: (&mut [u8], &mut [u8]) = first.1.split_at_mut(32usize);
    let row0: (&mut [u64], &mut [u64]) = hash.split_at_mut(0usize);
    let row1: (&mut [u64], &mut [u64]) = row0.1.split_at_mut(4usize);
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store64_le(
            &mut second.0[i.wrapping_mul(8u32) as usize..],
            row1.0[i as usize]
        )
    };
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store64_le(
            &mut second.1[i.wrapping_mul(8u32) as usize..],
            row1.1[i as usize]
        )
    };
    let r#final: (&mut [u8], &mut [u8]) = second.0.split_at_mut(0usize);
    (output[0usize..0usize + nn as usize]).copy_from_slice(
        &r#final.1[0usize..0usize + nn as usize]
    );
    crate::lib::memzero0::memzero::<u8>(r#final.0, 64u32)
}

pub fn blake2b(nn: u32, output: &mut [u8], ll: u32, d: &mut [u8], kk: u32, k: &mut [u8]) -> ()
{
    let mut b: [u64; 16] = [0u64; 16usize];
    let mut b1: [u64; 16] = [0u64; 16usize];
    blake2b_init(&mut b, kk, nn);
    blake2b_update(&mut b1, &mut b, kk, k, ll, d);
    blake2b_finish(nn, output, &mut b);
    crate::lib::memzero0::memzero::<u64>(&mut b1, 16u32);
    crate::lib::memzero0::memzero::<u64>(&mut b, 16u32)
}

pub fn blake2b_malloc(r: ()) -> &mut [u64]
{
    let mut buf: Vec<u64> = vec![0u64; 16usize];
    &mut buf
}

pub fn blake2s_init(hash: &mut [u32], kk: u32, nn: u32) -> ()
{
    let r0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let r1: (&mut [u32], &mut [u32]) = r0.1.split_at_mut(4usize);
    let r2: (&mut [u32], &mut [u32]) = r1.1.split_at_mut(4usize);
    let r3: (&mut [u32], &mut [u32]) = r2.1.split_at_mut(4usize);
    let iv0: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[0usize];
    let iv1: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[1usize];
    let iv2: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[2usize];
    let iv3: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[3usize];
    let iv4: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[4usize];
    let iv5: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[5usize];
    let iv6: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[6usize];
    let iv7: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[7usize];
    r3.0[0usize] = iv0;
    r3.0[1usize] = iv1;
    r3.0[2usize] = iv2;
    r3.0[3usize] = iv3;
    r3.1[0usize] = iv4;
    r3.1[1usize] = iv5;
    r3.1[2usize] = iv6;
    r3.1[3usize] = iv7;
    let kk_shift_8: u32 = kk.wrapping_shl(8u32);
    let iv0_: u32 = iv0 ^ (0x01010000u32 ^ (kk_shift_8 ^ nn));
    r1.0[0usize] = iv0_;
    r1.0[1usize] = iv1;
    r1.0[2usize] = iv2;
    r1.0[3usize] = iv3;
    r2.0[0usize] = iv4;
    r2.0[1usize] = iv5;
    r2.0[2usize] = iv6;
    r2.0[3usize] = iv7
}

pub fn blake2s_update_key(wv: &mut [u32], hash: &mut [u32], kk: u32, k: &mut [u8], ll: u32) ->
    ()
{
    let lb: u64 = 64u32 as u64;
    let mut b: [u8; 64] = [0u8; 64usize];
    ((&mut b)[0usize..0usize + kk as usize]).copy_from_slice(&k[0usize..0usize + kk as usize]);
    if ll == 0u32
    { crate::hacl::blake2s_32::blake2s_update_block(wv, hash, truebool, lb, &mut b) }
    else
    { crate::hacl::blake2s_32::blake2s_update_block(wv, hash, falsebool, lb, &mut b) };
    crate::lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

pub fn blake2s_update_multi(
    len: u32,
    wv: &mut [u32],
    hash: &mut [u32],
    prev: u64,
    blocks: &mut [u8],
    nb: u32
) ->
    ()
{
    crate::lowstar::ignore::ignore::<u32>(len);
    for i in 0u32..nb
    {
        let totlen: u64 = prev.wrapping_add(i.wrapping_add(1u32).wrapping_mul(64u32) as u64);
        let b: (&mut [u8], &mut [u8]) = blocks.split_at_mut(i.wrapping_mul(64u32) as usize);
        crate::hacl::blake2s_32::blake2s_update_block(wv, hash, falsebool, totlen, b.1)
    }
}

pub fn blake2s_update_last(
    len: u32,
    wv: &mut [u32],
    hash: &mut [u32],
    prev: u64,
    rem: u32,
    d: &mut [u8]
) ->
    ()
{
    let mut b: [u8; 64] = [0u8; 64usize];
    let last: (&mut [u8], &mut [u8]) = d.split_at_mut(len.wrapping_sub(rem) as usize);
    ((&mut b)[0usize..0usize + rem as usize]).copy_from_slice(
        &last.1[0usize..0usize + rem as usize]
    );
    let totlen: u64 = prev.wrapping_add(len as u64);
    crate::hacl::blake2s_32::blake2s_update_block(wv, hash, truebool, totlen, &mut b);
    crate::lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

#[inline] fn blake2s_update(
    wv: &mut [u32],
    hash: &mut [u32],
    kk: u32,
    k: &mut [u8],
    ll: u32,
    d: &mut [u8]
) ->
    ()
{
    let lb: u64 = 64u32 as u64;
    if kk > 0u32
    {
        blake2s_update_key(wv, hash, kk, k, ll);
        if ! ll == 0u32 { crate::hacl::blake2s_32::blake2s_update_blocks(ll, wv, hash, lb, d) }
    }
    else
    { crate::hacl::blake2s_32::blake2s_update_blocks(ll, wv, hash, 0u32 as u64, d) }
}

pub fn blake2s_finish(nn: u32, output: &mut [u8], hash: &mut [u32]) -> ()
{
    let mut b: [u8; 32] = [0u8; 32usize];
    let first: (&mut [u8], &mut [u8]) = (&mut b).split_at_mut(0usize);
    let second: (&mut [u8], &mut [u8]) = first.1.split_at_mut(16usize);
    let row0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let row1: (&mut [u32], &mut [u32]) = row0.1.split_at_mut(4usize);
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store32_le(
            &mut second.0[i.wrapping_mul(4u32) as usize..],
            row1.0[i as usize]
        )
    };
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store32_le(
            &mut second.1[i.wrapping_mul(4u32) as usize..],
            row1.1[i as usize]
        )
    };
    let r#final: (&mut [u8], &mut [u8]) = second.0.split_at_mut(0usize);
    (output[0usize..0usize + nn as usize]).copy_from_slice(
        &r#final.1[0usize..0usize + nn as usize]
    );
    crate::lib::memzero0::memzero::<u8>(r#final.0, 32u32)
}

pub fn blake2s(nn: u32, output: &mut [u8], ll: u32, d: &mut [u8], kk: u32, k: &mut [u8]) -> ()
{
    let mut b: [u32; 16] = [0u32; 16usize];
    let mut b1: [u32; 16] = [0u32; 16usize];
    blake2s_init(&mut b, kk, nn);
    blake2s_update(&mut b1, &mut b, kk, k, ll, d);
    blake2s_finish(nn, output, &mut b);
    crate::lib::memzero0::memzero::<u32>(&mut b1, 16u32);
    crate::lib::memzero0::memzero::<u32>(&mut b, 16u32)
}

pub fn blake2s_malloc(r: ()) -> &mut [u32]
{
    let mut buf: Vec<u32> = vec![0u32; 16usize];
    &mut buf
}
