pub fn blake2b_init(hash: &mut [u64], kk: u32, nn: u32) -> ()
{
  let r0: (&mut [u64], &mut [u64]) = hash.split_at_mut(0usize);
  let r1: (&mut [u64], &mut [u64]) = r0.1.split_at_mut(4usize);
  let r2: (&mut [u64], &mut [u64]) = r1.1.split_at_mut(4usize);
  let r3: (&mut [u64], &mut [u64]) = r2.1.split_at_mut(4usize);
  let iv0: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[0u32 as usize];
  let iv1: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[1u32 as usize];
  let iv2: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[2u32 as usize];
  let iv3: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[3u32 as usize];
  let iv4: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[4u32 as usize];
  let iv5: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[5u32 as usize];
  let iv6: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[6u32 as usize];
  let iv7: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[7u32 as usize];
  r3.0[0u32 as usize] = iv0;
  r3.0[1u32 as usize] = iv1;
  r3.0[2u32 as usize] = iv2;
  r3.0[3u32 as usize] = iv3;
  r3.1[0u32 as usize] = iv4;
  r3.1[1u32 as usize] = iv5;
  r3.1[2u32 as usize] = iv6;
  r3.1[3u32 as usize] = iv7;
  let kk_shift_8: u64 = (kk as u64).wrapping_shl(8u32);
  let iv0': u64 = iv0 ^ (0x01010000u64 ^ (kk_shift_8 ^ nn as u64));
  r1.0[0u32 as usize] = iv0';
  r1.0[1u32 as usize] = iv1;
  r1.0[2u32 as usize] = iv2;
  r1.0[3u32 as usize] = iv3;
  r2.0[0u32 as usize] = iv4;
  r2.0[1u32 as usize] = iv5;
  r2.0[2u32 as usize] = iv6;
  r2.0[3u32 as usize] = iv7
}

fn blake2b_update(
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
    crate::hacl::blake2b_32::blake2b_update_key(wv, hash, kk, k, ll);
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

pub fn blake2b_malloc(r: ()) -> &mut [u64]
{
  let mut buf: Vec<u64> = vec![0u64; 16u32 as usize];
  &mut buf
}

pub fn blake2s_init(hash: &mut [u32], kk: u32, nn: u32) -> ()
{
  let r0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
  let r1: (&mut [u32], &mut [u32]) = r0.1.split_at_mut(4usize);
  let r2: (&mut [u32], &mut [u32]) = r1.1.split_at_mut(4usize);
  let r3: (&mut [u32], &mut [u32]) = r2.1.split_at_mut(4usize);
  let iv0: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[0u32 as usize];
  let iv1: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[1u32 as usize];
  let iv2: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[2u32 as usize];
  let iv3: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[3u32 as usize];
  let iv4: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[4u32 as usize];
  let iv5: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[5u32 as usize];
  let iv6: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[6u32 as usize];
  let iv7: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[7u32 as usize];
  r3.0[0u32 as usize] = iv0;
  r3.0[1u32 as usize] = iv1;
  r3.0[2u32 as usize] = iv2;
  r3.0[3u32 as usize] = iv3;
  r3.1[0u32 as usize] = iv4;
  r3.1[1u32 as usize] = iv5;
  r3.1[2u32 as usize] = iv6;
  r3.1[3u32 as usize] = iv7;
  let kk_shift_8: u32 = kk.wrapping_shl(8u32);
  let iv0': u32 = iv0 ^ (0x01010000u32 ^ (kk_shift_8 ^ nn));
  r1.0[0u32 as usize] = iv0';
  r1.0[1u32 as usize] = iv1;
  r1.0[2u32 as usize] = iv2;
  r1.0[3u32 as usize] = iv3;
  r2.0[0u32 as usize] = iv4;
  r2.0[1u32 as usize] = iv5;
  r2.0[2u32 as usize] = iv6;
  r2.0[3u32 as usize] = iv7
}

fn blake2s_update(
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
    crate::hacl::blake2s_32::blake2s_update_key(wv, hash, kk, k, ll);
    if ! ll == 0u32 { crate::hacl::blake2s_32::blake2s_update_blocks(ll, wv, hash, lb, d) }
  }
  else
  { crate::hacl::blake2s_32::blake2s_update_blocks(ll, wv, hash, 0u32 as u64, d) }
}

pub fn blake2s_malloc(r: ()) -> &mut [u32]
{
  let mut buf: Vec<u32> = vec![0u32; 16u32 as usize];
  &mut buf
}