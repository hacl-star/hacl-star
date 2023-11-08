pub fn blake2b_init(hash: &mut [crate::lib::intvector::intrinsics::vec256], kk: u32, nn: u32) ->
  ()
{
  let
  r0:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    hash.split_at_mut(0usize);
  let
  r1:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r0.1.split_at_mut(1usize);
  let
  r2:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r1.1.split_at_mut(1usize);
  let
  r3:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r2.1.split_at_mut(1usize);
  let iv0: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[0u32 as usize];
  let iv1: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[1u32 as usize];
  let iv2: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[2u32 as usize];
  let iv3: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[3u32 as usize];
  let iv4: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[4u32 as usize];
  let iv5: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[5u32 as usize];
  let iv6: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[6u32 as usize];
  let iv7: u64 = (&crate::hacl::impl_blake2_constants::ivTable_B)[7u32 as usize];
  r3.0[0u32 as usize] = crate::lib::intvector::intrinsics::vec256_load64s(iv0, iv1, iv2, iv3);
  r3.1[0u32 as usize] = crate::lib::intvector::intrinsics::vec256_load64s(iv4, iv5, iv6, iv7);
  let kk_shift_8: u64 = (kk as u64).wrapping_shl(8u32);
  let iv0': u64 = iv0 ^ (0x01010000u64 ^ (kk_shift_8 ^ nn as u64));
  r1.0[0u32 as usize] = crate::lib::intvector::intrinsics::vec256_load64s(iv0', iv1, iv2, iv3);
  r2.0[0u32 as usize] = crate::lib::intvector::intrinsics::vec256_load64s(iv4, iv5, iv6, iv7)
}

fn blake2b_update(
  wv: &mut [crate::lib::intvector::intrinsics::vec256],
  hash: &mut [crate::lib::intvector::intrinsics::vec256],
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
    crate::hacl::blake2b_256::blake2b_update_key(wv, hash, kk, k, ll);
    if ! ll == 0u32 { crate::hacl::blake2b_256::blake2b_update_blocks(ll, wv, hash, lb, d) }
  }
  else
  {
    crate::hacl::blake2b_256::blake2b_update_blocks(
      ll,
      wv,
      hash,
      crate::fstar::uint128::uint64_to_uint128(0u32 as u64),
      d
    )
  }
}

pub fn load_state256b_from_state32(
  st: &mut [crate::lib::intvector::intrinsics::vec256],
  st32: &mut [u64]
) ->
  ()
{
  let
  r0:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    st.split_at_mut(0usize);
  let
  r1:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r0.1.split_at_mut(1usize);
  let
  r2:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r1.1.split_at_mut(1usize);
  let
  r3:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r2.1.split_at_mut(1usize);
  let b0: (&mut [u64], &mut [u64]) = st32.split_at_mut(0usize);
  let b1: (&mut [u64], &mut [u64]) = b0.1.split_at_mut(4usize);
  let b2: (&mut [u64], &mut [u64]) = b1.1.split_at_mut(4usize);
  let b3: (&mut [u64], &mut [u64]) = b2.1.split_at_mut(4usize);
  r1.0[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_load64s(
      b1.0[0u32 as usize],
      b1.0[1u32 as usize],
      b1.0[2u32 as usize],
      b1.0[3u32 as usize]
    );
  r2.0[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_load64s(
      b2.0[0u32 as usize],
      b2.0[1u32 as usize],
      b2.0[2u32 as usize],
      b2.0[3u32 as usize]
    );
  r3.0[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_load64s(
      b3.0[0u32 as usize],
      b3.0[1u32 as usize],
      b3.0[2u32 as usize],
      b3.0[3u32 as usize]
    );
  r3.1[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_load64s(
      b3.1[0u32 as usize],
      b3.1[1u32 as usize],
      b3.1[2u32 as usize],
      b3.1[3u32 as usize]
    )
}

pub fn store_state256b_to_state32(
  st32: &mut [u64],
  st: &mut [crate::lib::intvector::intrinsics::vec256]
) ->
  ()
{
  let
  r0:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    st.split_at_mut(0usize);
  let
  r1:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r0.1.split_at_mut(1usize);
  let
  r2:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r1.1.split_at_mut(1usize);
  let
  r3:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r2.1.split_at_mut(1usize);
  let b0: (&mut [u64], &mut [u64]) = st32.split_at_mut(0usize);
  let b1: (&mut [u64], &mut [u64]) = b0.1.split_at_mut(4usize);
  let b2: (&mut [u64], &mut [u64]) = b1.1.split_at_mut(4usize);
  let b3: (&mut [u64], &mut [u64]) = b2.1.split_at_mut(4usize);
  let mut b8: [u8; 32] = [0u8; 32u32 as usize];
  crate::lib::intvector::intrinsics::vec256_store64_le(&mut b8, r1.0[0u32 as usize]);
  for i in 0u32..4u32
  {
    let os: (&mut [u64], &mut [u64]) = b1.0.split_at_mut(0usize);
    let bj: (&mut [u8], &mut [u8]) =
      (&mut b8).split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
    let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
    let r: u64 = u;
    let x: u64 = r;
    os.1[i as usize] = x
  };
  let mut b8: [u8; 32] = [0u8; 32u32 as usize];
  crate::lib::intvector::intrinsics::vec256_store64_le(&mut b8, r2.0[0u32 as usize]);
  for i in 0u32..4u32
  {
    let os: (&mut [u64], &mut [u64]) = b2.0.split_at_mut(0usize);
    let bj: (&mut [u8], &mut [u8]) =
      (&mut b8).split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
    let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
    let r: u64 = u;
    let x: u64 = r;
    os.1[i as usize] = x
  };
  let mut b8: [u8; 32] = [0u8; 32u32 as usize];
  crate::lib::intvector::intrinsics::vec256_store64_le(&mut b8, r3.0[0u32 as usize]);
  for i in 0u32..4u32
  {
    let os: (&mut [u64], &mut [u64]) = b3.0.split_at_mut(0usize);
    let bj: (&mut [u8], &mut [u8]) =
      (&mut b8).split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
    let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
    let r: u64 = u;
    let x: u64 = r;
    os.1[i as usize] = x
  };
  let mut b8: [u8; 32] = [0u8; 32u32 as usize];
  crate::lib::intvector::intrinsics::vec256_store64_le(&mut b8, r3.1[0u32 as usize]);
  for i in 0u32..4u32
  {
    let os: (&mut [u64], &mut [u64]) = b3.1.split_at_mut(0usize);
    let bj: (&mut [u8], &mut [u8]) =
      (&mut b8).split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
    let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
    let r: u64 = u;
    let x: u64 = r;
    os.1[i as usize] = x
  }
}

pub fn blake2b_malloc(r: ()) -> &mut [crate::lib::intvector::intrinsics::vec256]
{
  let mut buf: Vec<crate::lib::intvector::intrinsics::vec256> =
    vec![crate::lib::intvector::intrinsics::vec256_zero; 4u32 as usize];
  &mut buf
}