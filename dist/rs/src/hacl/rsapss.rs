fn load_skey(
  modBits: u32,
  eBits: u32,
  dBits: u32,
  nb: &mut [u8],
  eb: &mut [u8],
  db: &mut [u8],
  skey: &mut [u64]
) ->
  bool
{
  let dbLen: u32 = dBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
  let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
  let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
  let pkeyLen: u32 = nLen.wrapping_add(nLen).wrapping_add(eLen);
  let pkey: (&mut [u64], &mut [u64]) = skey.split_at_mut(0usize);
  let d: (&mut [u64], &mut [u64]) = pkey.1.split_at_mut((pkeyLen as usize).wrapping_add(0usize));
  let b: bool = load_pkey(modBits, eBits, nb, eb, d.0);
  crate::hacl::bignum::convert::bn_from_bytes_be_uint64(dbLen, db, d.1);
  let m1: u64 = crate::hacl::impl::rsapss::keys::check_exponent_u64(dBits, d.1);
  b && m1 == 0xFFFFFFFFFFFFFFFFu64
}

pub fn mgf_hash(
  a: crate::spec::hash::definitions::hash_alg,
  len: u32,
  mgfseed: &mut [u8],
  maskLen: u32,
  res: &mut [u8]
) ->
  ()
{ crate::hacl::impl::rsapss::mgf::mgf_hash(a, len, mgfseed, maskLen, res) }