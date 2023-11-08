fn double_round_256(st: &mut [crate::lib::intvector::intrinsics::vec256]) -> ()
{
  st[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[0u32 as usize], st[4u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[12u32 as usize], st[0u32 as usize]);
  st[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[8u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[8u32 as usize], st[12u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[4u32 as usize], st[8u32 as usize]);
  st[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[0u32 as usize], st[4u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[12u32 as usize], st[0u32 as usize]);
  st[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[8u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[8u32 as usize], st[12u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[4u32 as usize], st[8u32 as usize]);
  st[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[1u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[1u32 as usize], st[5u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[13u32 as usize], st[1u32 as usize]);
  st[13u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[9u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[9u32 as usize], st[13u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[5u32 as usize], st[9u32 as usize]);
  st[5u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[1u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[1u32 as usize], st[5u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[13u32 as usize], st[1u32 as usize]);
  st[13u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[9u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[9u32 as usize], st[13u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[5u32 as usize], st[9u32 as usize]);
  st[5u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[2u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[2u32 as usize], st[6u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[14u32 as usize], st[2u32 as usize]);
  st[14u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[10u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[10u32 as usize], st[14u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[6u32 as usize], st[10u32 as usize]);
  st[6u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[2u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[2u32 as usize], st[6u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[14u32 as usize], st[2u32 as usize]);
  st[14u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[10u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[10u32 as usize], st[14u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[6u32 as usize], st[10u32 as usize]);
  st[6u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[3u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[3u32 as usize], st[7u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[15u32 as usize], st[3u32 as usize]);
  st[15u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[11u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[11u32 as usize], st[15u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[7u32 as usize], st[11u32 as usize]);
  st[7u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[3u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[3u32 as usize], st[7u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[15u32 as usize], st[3u32 as usize]);
  st[15u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[11u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[11u32 as usize], st[15u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[7u32 as usize], st[11u32 as usize]);
  st[7u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[0u32 as usize], st[5u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[15u32 as usize], st[0u32 as usize]);
  st[15u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[10u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[10u32 as usize], st[15u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[5u32 as usize], st[10u32 as usize]);
  st[5u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[0u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[0u32 as usize], st[5u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[15u32 as usize], st[0u32 as usize]);
  st[15u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[10u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[10u32 as usize], st[15u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[5u32 as usize], st[10u32 as usize]);
  st[5u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[1u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[1u32 as usize], st[6u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[12u32 as usize], st[1u32 as usize]);
  st[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[11u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[11u32 as usize], st[12u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[6u32 as usize], st[11u32 as usize]);
  st[6u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[1u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[1u32 as usize], st[6u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[12u32 as usize], st[1u32 as usize]);
  st[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[11u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[11u32 as usize], st[12u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[6u32 as usize], st[11u32 as usize]);
  st[6u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[2u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[2u32 as usize], st[7u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[13u32 as usize], st[2u32 as usize]);
  st[13u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[8u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[8u32 as usize], st[13u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[7u32 as usize], st[8u32 as usize]);
  st[7u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[2u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[2u32 as usize], st[7u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[13u32 as usize], st[2u32 as usize]);
  st[13u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[8u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[8u32 as usize], st[13u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[7u32 as usize], st[8u32 as usize]);
  st[7u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32);
  st[3u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[3u32 as usize], st[4u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[14u32 as usize], st[3u32 as usize]);
  st[14u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 16u32);
  st[9u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[9u32 as usize], st[14u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[4u32 as usize], st[9u32 as usize]);
  st[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 12u32);
  st[3u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[3u32 as usize], st[4u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[14u32 as usize], st[3u32 as usize]);
  st[14u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 8u32);
  st[9u32 as usize] =
    crate::lib::intvector::intrinsics::vec256_add32(st[9u32 as usize], st[14u32 as usize]);
  let std: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_xor(st[4u32 as usize], st[9u32 as usize]);
  st[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_rotate_left32(std, 7u32)
}

fn chacha20_core_256(
  k: &mut [crate::lib::intvector::intrinsics::vec256],
  ctx: &mut [crate::lib::intvector::intrinsics::vec256],
  ctr: u32
) ->
  ()
{
  (k[0u32 as usize..0u32 as usize + 16u32 as usize]).copy_from_slice(
    &ctx[0u32 as usize..0u32 as usize + 16u32 as usize]
  );
  let ctr_u32: u32 = 8u32.wrapping_mul(ctr);
  let cv: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_load32(ctr_u32);
  k[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_add32(k[12u32 as usize], cv);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  double_round_256(k);
  for i in 0u32..16u32
  {
    let
    os:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      k.split_at_mut(0usize);
    let x: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add32(os.1[i as usize], ctx[i as usize]);
    os.1[i as usize] = x
  };
  k[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_add32(k[12u32 as usize], cv)
}

fn chacha20_init_256(
  ctx: &mut [crate::lib::intvector::intrinsics::vec256],
  k: &mut [u8],
  n: &mut [u8],
  ctr: u32
) ->
  ()
{
  let mut ctx1: [u32; 16] = [0u32; 16u32 as usize];
  for i in 0u32..4u32
  {
    let os: &mut [u32] = &mut (&mut (&mut ctx1)[0u32 as usize..])[0u32 as usize..];
    let x: u32 = (&crate::hacl::chacha20::chacha20_constants)[i as usize];
    os[i as usize] = x
  };
  for i in 0u32..8u32
  {
    let os: &mut [u32] = &mut (&mut (&mut ctx1)[4u32 as usize..])[0u32 as usize..];
    let bj: (&mut [u8], &mut [u8]) =
      k.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
    let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
    let r: u32 = u;
    let x: u32 = r;
    os[i as usize] = x
  };
  (&mut ctx1)[12u32 as usize] = ctr;
  for i in 0u32..3u32
  {
    let os: &mut [u32] = &mut (&mut (&mut ctx1)[13u32 as usize..])[0u32 as usize..];
    let bj: (&mut [u8], &mut [u8]) =
      n.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
    let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
    let r: u32 = u;
    let x: u32 = r;
    os[i as usize] = x
  };
  for i in 0u32..16u32
  {
    let
    os:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      ctx.split_at_mut(0usize);
    let x: u32 = (&mut ctx1)[i as usize];
    let x: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load32(x);
    os.1[i as usize] = x
  };
  let ctr1: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_load32s(
      0u32,
      1u32,
      2u32,
      3u32,
      4u32,
      5u32,
      6u32,
      7u32
    );
  let c12: crate::lib::intvector::intrinsics::vec256 = ctx[12u32 as usize];
  ctx[12u32 as usize] = crate::lib::intvector::intrinsics::vec256_add32(c12, ctr1)
}

pub fn chacha20_encrypt_256(
  len: u32,
  out: &mut [u8],
  text: &mut [u8],
  key: &mut [u8],
  n: &mut [u8],
  ctr: u32
) ->
  ()
{
  let mut ctx: [crate::lib::intvector::intrinsics::vec256; 16] =
    [crate::lib::intvector::intrinsics::vec256_zero; 16u32 as usize];
  chacha20_init_256(&mut ctx, key, n, ctr);
  let rem: u32 = len.wrapping_rem(512u32);
  let nb: u32 = len.wrapping_div(512u32);
  let rem1: u32 = len.wrapping_rem(512u32);
  for i in 0u32..rem1
  {
    let uu____0: (&mut [u8], &mut [u8]) =
      out.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
    let uu____1: (&mut [u8], &mut [u8]) =
      text.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
    let mut k: [crate::lib::intvector::intrinsics::vec256; 16] =
      [crate::lib::intvector::intrinsics::vec256_zero; 16u32 as usize];
    chacha20_core_256(&mut k, &mut ctx, i);
    let st0: crate::lib::intvector::intrinsics::vec256 = (&mut k)[0u32 as usize];
    let st1: crate::lib::intvector::intrinsics::vec256 = (&mut k)[1u32 as usize];
    let st2: crate::lib::intvector::intrinsics::vec256 = (&mut k)[2u32 as usize];
    let st3: crate::lib::intvector::intrinsics::vec256 = (&mut k)[3u32 as usize];
    let st4: crate::lib::intvector::intrinsics::vec256 = (&mut k)[4u32 as usize];
    let st5: crate::lib::intvector::intrinsics::vec256 = (&mut k)[5u32 as usize];
    let st6: crate::lib::intvector::intrinsics::vec256 = (&mut k)[6u32 as usize];
    let st7: crate::lib::intvector::intrinsics::vec256 = (&mut k)[7u32 as usize];
    let st8: crate::lib::intvector::intrinsics::vec256 = (&mut k)[8u32 as usize];
    let st9: crate::lib::intvector::intrinsics::vec256 = (&mut k)[9u32 as usize];
    let st10: crate::lib::intvector::intrinsics::vec256 = (&mut k)[10u32 as usize];
    let st11: crate::lib::intvector::intrinsics::vec256 = (&mut k)[11u32 as usize];
    let st12: crate::lib::intvector::intrinsics::vec256 = (&mut k)[12u32 as usize];
    let st13: crate::lib::intvector::intrinsics::vec256 = (&mut k)[13u32 as usize];
    let st14: crate::lib::intvector::intrinsics::vec256 = (&mut k)[14u32 as usize];
    let st15: crate::lib::intvector::intrinsics::vec256 = (&mut k)[15u32 as usize];
    let v0: crate::lib::intvector::intrinsics::vec256 = st0;
    let v1: crate::lib::intvector::intrinsics::vec256 = st1;
    let v2: crate::lib::intvector::intrinsics::vec256 = st2;
    let v3: crate::lib::intvector::intrinsics::vec256 = st3;
    let v4: crate::lib::intvector::intrinsics::vec256 = st4;
    let v5: crate::lib::intvector::intrinsics::vec256 = st5;
    let v6: crate::lib::intvector::intrinsics::vec256 = st6;
    let v7: crate::lib::intvector::intrinsics::vec256 = st7;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v0, v1);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v0, v1);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v2, v3);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v2, v3);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v4, v5);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v4, v5);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v6, v7);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v6, v7);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0: crate::lib::intvector::intrinsics::vec256 = v0';
    let v1: crate::lib::intvector::intrinsics::vec256 = v2';
    let v2: crate::lib::intvector::intrinsics::vec256 = v1';
    let v3: crate::lib::intvector::intrinsics::vec256 = v3';
    let v4: crate::lib::intvector::intrinsics::vec256 = v4';
    let v5: crate::lib::intvector::intrinsics::vec256 = v6';
    let v6: crate::lib::intvector::intrinsics::vec256 = v5';
    let v7: crate::lib::intvector::intrinsics::vec256 = v7';
    let v01: crate::lib::intvector::intrinsics::vec256 = st8;
    let v11: crate::lib::intvector::intrinsics::vec256 = st9;
    let v21: crate::lib::intvector::intrinsics::vec256 = st10;
    let v31: crate::lib::intvector::intrinsics::vec256 = st11;
    let v41: crate::lib::intvector::intrinsics::vec256 = st12;
    let v51: crate::lib::intvector::intrinsics::vec256 = st13;
    let v61: crate::lib::intvector::intrinsics::vec256 = st14;
    let v71: crate::lib::intvector::intrinsics::vec256 = st15;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v01, v11);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v01, v11);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v21, v31);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v21, v31);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v41, v51);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v41, v51);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v61, v71);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v61, v71);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v8: crate::lib::intvector::intrinsics::vec256 = v0';
    let v9: crate::lib::intvector::intrinsics::vec256 = v2';
    let v10: crate::lib::intvector::intrinsics::vec256 = v1';
    let v11: crate::lib::intvector::intrinsics::vec256 = v3';
    let v12: crate::lib::intvector::intrinsics::vec256 = v4';
    let v13: crate::lib::intvector::intrinsics::vec256 = v6';
    let v14: crate::lib::intvector::intrinsics::vec256 = v5';
    let v15: crate::lib::intvector::intrinsics::vec256 = v7';
    (&mut k)[0u32 as usize] = v0;
    (&mut k)[1u32 as usize] = v8;
    (&mut k)[2u32 as usize] = v1;
    (&mut k)[3u32 as usize] = v9;
    (&mut k)[4u32 as usize] = v2;
    (&mut k)[5u32 as usize] = v10;
    (&mut k)[6u32 as usize] = v3;
    (&mut k)[7u32 as usize] = v11;
    (&mut k)[8u32 as usize] = v4;
    (&mut k)[9u32 as usize] = v12;
    (&mut k)[10u32 as usize] = v5;
    (&mut k)[11u32 as usize] = v13;
    (&mut k)[12u32 as usize] = v6;
    (&mut k)[13u32 as usize] = v14;
    (&mut k)[14u32 as usize] = v7;
    (&mut k)[15u32 as usize] = v15;
    for i in 0u32..16u32
    {
      let x: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load32_le(
          &mut uu____1.1[i.wrapping_mul(32u32) as usize..]
        );
      let y: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_xor(x, (&mut k)[i as usize]);
      crate::lib::intvector::intrinsics::vec256_store32_le(
        &mut uu____0.1[i.wrapping_mul(32u32) as usize..],
        y
      )
    }
  };
  if rem1 > 0u32
  {
    let uu____2: (&mut [u8], &mut [u8]) =
      out.split_at_mut((nb.wrapping_mul(512u32) as usize).wrapping_add(0usize));
    let mut plain: [u8; 512] = [0u8; 512u32 as usize];
    ((&mut plain)[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut text[nb.wrapping_mul(512u32) as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    );
    let mut k: [crate::lib::intvector::intrinsics::vec256; 16] =
      [crate::lib::intvector::intrinsics::vec256_zero; 16u32 as usize];
    chacha20_core_256(&mut k, &mut ctx, nb);
    let st0: crate::lib::intvector::intrinsics::vec256 = (&mut k)[0u32 as usize];
    let st1: crate::lib::intvector::intrinsics::vec256 = (&mut k)[1u32 as usize];
    let st2: crate::lib::intvector::intrinsics::vec256 = (&mut k)[2u32 as usize];
    let st3: crate::lib::intvector::intrinsics::vec256 = (&mut k)[3u32 as usize];
    let st4: crate::lib::intvector::intrinsics::vec256 = (&mut k)[4u32 as usize];
    let st5: crate::lib::intvector::intrinsics::vec256 = (&mut k)[5u32 as usize];
    let st6: crate::lib::intvector::intrinsics::vec256 = (&mut k)[6u32 as usize];
    let st7: crate::lib::intvector::intrinsics::vec256 = (&mut k)[7u32 as usize];
    let st8: crate::lib::intvector::intrinsics::vec256 = (&mut k)[8u32 as usize];
    let st9: crate::lib::intvector::intrinsics::vec256 = (&mut k)[9u32 as usize];
    let st10: crate::lib::intvector::intrinsics::vec256 = (&mut k)[10u32 as usize];
    let st11: crate::lib::intvector::intrinsics::vec256 = (&mut k)[11u32 as usize];
    let st12: crate::lib::intvector::intrinsics::vec256 = (&mut k)[12u32 as usize];
    let st13: crate::lib::intvector::intrinsics::vec256 = (&mut k)[13u32 as usize];
    let st14: crate::lib::intvector::intrinsics::vec256 = (&mut k)[14u32 as usize];
    let st15: crate::lib::intvector::intrinsics::vec256 = (&mut k)[15u32 as usize];
    let v0: crate::lib::intvector::intrinsics::vec256 = st0;
    let v1: crate::lib::intvector::intrinsics::vec256 = st1;
    let v2: crate::lib::intvector::intrinsics::vec256 = st2;
    let v3: crate::lib::intvector::intrinsics::vec256 = st3;
    let v4: crate::lib::intvector::intrinsics::vec256 = st4;
    let v5: crate::lib::intvector::intrinsics::vec256 = st5;
    let v6: crate::lib::intvector::intrinsics::vec256 = st6;
    let v7: crate::lib::intvector::intrinsics::vec256 = st7;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v0, v1);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v0, v1);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v2, v3);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v2, v3);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v4, v5);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v4, v5);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v6, v7);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v6, v7);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0: crate::lib::intvector::intrinsics::vec256 = v0';
    let v1: crate::lib::intvector::intrinsics::vec256 = v2';
    let v2: crate::lib::intvector::intrinsics::vec256 = v1';
    let v3: crate::lib::intvector::intrinsics::vec256 = v3';
    let v4: crate::lib::intvector::intrinsics::vec256 = v4';
    let v5: crate::lib::intvector::intrinsics::vec256 = v6';
    let v6: crate::lib::intvector::intrinsics::vec256 = v5';
    let v7: crate::lib::intvector::intrinsics::vec256 = v7';
    let v01: crate::lib::intvector::intrinsics::vec256 = st8;
    let v11: crate::lib::intvector::intrinsics::vec256 = st9;
    let v21: crate::lib::intvector::intrinsics::vec256 = st10;
    let v31: crate::lib::intvector::intrinsics::vec256 = st11;
    let v41: crate::lib::intvector::intrinsics::vec256 = st12;
    let v51: crate::lib::intvector::intrinsics::vec256 = st13;
    let v61: crate::lib::intvector::intrinsics::vec256 = st14;
    let v71: crate::lib::intvector::intrinsics::vec256 = st15;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v01, v11);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v01, v11);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v21, v31);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v21, v31);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v41, v51);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v41, v51);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v61, v71);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v61, v71);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v8: crate::lib::intvector::intrinsics::vec256 = v0';
    let v9: crate::lib::intvector::intrinsics::vec256 = v2';
    let v10: crate::lib::intvector::intrinsics::vec256 = v1';
    let v11: crate::lib::intvector::intrinsics::vec256 = v3';
    let v12: crate::lib::intvector::intrinsics::vec256 = v4';
    let v13: crate::lib::intvector::intrinsics::vec256 = v6';
    let v14: crate::lib::intvector::intrinsics::vec256 = v5';
    let v15: crate::lib::intvector::intrinsics::vec256 = v7';
    (&mut k)[0u32 as usize] = v0;
    (&mut k)[1u32 as usize] = v8;
    (&mut k)[2u32 as usize] = v1;
    (&mut k)[3u32 as usize] = v9;
    (&mut k)[4u32 as usize] = v2;
    (&mut k)[5u32 as usize] = v10;
    (&mut k)[6u32 as usize] = v3;
    (&mut k)[7u32 as usize] = v11;
    (&mut k)[8u32 as usize] = v4;
    (&mut k)[9u32 as usize] = v12;
    (&mut k)[10u32 as usize] = v5;
    (&mut k)[11u32 as usize] = v13;
    (&mut k)[12u32 as usize] = v6;
    (&mut k)[13u32 as usize] = v14;
    (&mut k)[14u32 as usize] = v7;
    (&mut k)[15u32 as usize] = v15;
    for i in 0u32..16u32
    {
      let x: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load32_le(
          &mut (&mut plain)[i.wrapping_mul(32u32) as usize..]
        );
      let y: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_xor(x, (&mut k)[i as usize]);
      crate::lib::intvector::intrinsics::vec256_store32_le(
        &mut (&mut plain)[i.wrapping_mul(32u32) as usize..],
        y
      )
    };
    (uu____2.1[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    )
  }
}

pub fn chacha20_decrypt_256(
  len: u32,
  out: &mut [u8],
  cipher: &mut [u8],
  key: &mut [u8],
  n: &mut [u8],
  ctr: u32
) ->
  ()
{
  let mut ctx: [crate::lib::intvector::intrinsics::vec256; 16] =
    [crate::lib::intvector::intrinsics::vec256_zero; 16u32 as usize];
  chacha20_init_256(&mut ctx, key, n, ctr);
  let rem: u32 = len.wrapping_rem(512u32);
  let nb: u32 = len.wrapping_div(512u32);
  let rem1: u32 = len.wrapping_rem(512u32);
  for i in 0u32..rem1
  {
    let uu____0: (&mut [u8], &mut [u8]) =
      out.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
    let uu____1: (&mut [u8], &mut [u8]) =
      cipher.split_at_mut((i.wrapping_mul(512u32) as usize).wrapping_add(0usize));
    let mut k: [crate::lib::intvector::intrinsics::vec256; 16] =
      [crate::lib::intvector::intrinsics::vec256_zero; 16u32 as usize];
    chacha20_core_256(&mut k, &mut ctx, i);
    let st0: crate::lib::intvector::intrinsics::vec256 = (&mut k)[0u32 as usize];
    let st1: crate::lib::intvector::intrinsics::vec256 = (&mut k)[1u32 as usize];
    let st2: crate::lib::intvector::intrinsics::vec256 = (&mut k)[2u32 as usize];
    let st3: crate::lib::intvector::intrinsics::vec256 = (&mut k)[3u32 as usize];
    let st4: crate::lib::intvector::intrinsics::vec256 = (&mut k)[4u32 as usize];
    let st5: crate::lib::intvector::intrinsics::vec256 = (&mut k)[5u32 as usize];
    let st6: crate::lib::intvector::intrinsics::vec256 = (&mut k)[6u32 as usize];
    let st7: crate::lib::intvector::intrinsics::vec256 = (&mut k)[7u32 as usize];
    let st8: crate::lib::intvector::intrinsics::vec256 = (&mut k)[8u32 as usize];
    let st9: crate::lib::intvector::intrinsics::vec256 = (&mut k)[9u32 as usize];
    let st10: crate::lib::intvector::intrinsics::vec256 = (&mut k)[10u32 as usize];
    let st11: crate::lib::intvector::intrinsics::vec256 = (&mut k)[11u32 as usize];
    let st12: crate::lib::intvector::intrinsics::vec256 = (&mut k)[12u32 as usize];
    let st13: crate::lib::intvector::intrinsics::vec256 = (&mut k)[13u32 as usize];
    let st14: crate::lib::intvector::intrinsics::vec256 = (&mut k)[14u32 as usize];
    let st15: crate::lib::intvector::intrinsics::vec256 = (&mut k)[15u32 as usize];
    let v0: crate::lib::intvector::intrinsics::vec256 = st0;
    let v1: crate::lib::intvector::intrinsics::vec256 = st1;
    let v2: crate::lib::intvector::intrinsics::vec256 = st2;
    let v3: crate::lib::intvector::intrinsics::vec256 = st3;
    let v4: crate::lib::intvector::intrinsics::vec256 = st4;
    let v5: crate::lib::intvector::intrinsics::vec256 = st5;
    let v6: crate::lib::intvector::intrinsics::vec256 = st6;
    let v7: crate::lib::intvector::intrinsics::vec256 = st7;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v0, v1);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v0, v1);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v2, v3);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v2, v3);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v4, v5);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v4, v5);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v6, v7);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v6, v7);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0: crate::lib::intvector::intrinsics::vec256 = v0';
    let v1: crate::lib::intvector::intrinsics::vec256 = v2';
    let v2: crate::lib::intvector::intrinsics::vec256 = v1';
    let v3: crate::lib::intvector::intrinsics::vec256 = v3';
    let v4: crate::lib::intvector::intrinsics::vec256 = v4';
    let v5: crate::lib::intvector::intrinsics::vec256 = v6';
    let v6: crate::lib::intvector::intrinsics::vec256 = v5';
    let v7: crate::lib::intvector::intrinsics::vec256 = v7';
    let v01: crate::lib::intvector::intrinsics::vec256 = st8;
    let v11: crate::lib::intvector::intrinsics::vec256 = st9;
    let v21: crate::lib::intvector::intrinsics::vec256 = st10;
    let v31: crate::lib::intvector::intrinsics::vec256 = st11;
    let v41: crate::lib::intvector::intrinsics::vec256 = st12;
    let v51: crate::lib::intvector::intrinsics::vec256 = st13;
    let v61: crate::lib::intvector::intrinsics::vec256 = st14;
    let v71: crate::lib::intvector::intrinsics::vec256 = st15;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v01, v11);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v01, v11);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v21, v31);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v21, v31);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v41, v51);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v41, v51);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v61, v71);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v61, v71);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v8: crate::lib::intvector::intrinsics::vec256 = v0';
    let v9: crate::lib::intvector::intrinsics::vec256 = v2';
    let v10: crate::lib::intvector::intrinsics::vec256 = v1';
    let v11: crate::lib::intvector::intrinsics::vec256 = v3';
    let v12: crate::lib::intvector::intrinsics::vec256 = v4';
    let v13: crate::lib::intvector::intrinsics::vec256 = v6';
    let v14: crate::lib::intvector::intrinsics::vec256 = v5';
    let v15: crate::lib::intvector::intrinsics::vec256 = v7';
    (&mut k)[0u32 as usize] = v0;
    (&mut k)[1u32 as usize] = v8;
    (&mut k)[2u32 as usize] = v1;
    (&mut k)[3u32 as usize] = v9;
    (&mut k)[4u32 as usize] = v2;
    (&mut k)[5u32 as usize] = v10;
    (&mut k)[6u32 as usize] = v3;
    (&mut k)[7u32 as usize] = v11;
    (&mut k)[8u32 as usize] = v4;
    (&mut k)[9u32 as usize] = v12;
    (&mut k)[10u32 as usize] = v5;
    (&mut k)[11u32 as usize] = v13;
    (&mut k)[12u32 as usize] = v6;
    (&mut k)[13u32 as usize] = v14;
    (&mut k)[14u32 as usize] = v7;
    (&mut k)[15u32 as usize] = v15;
    for i in 0u32..16u32
    {
      let x: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load32_le(
          &mut uu____1.1[i.wrapping_mul(32u32) as usize..]
        );
      let y: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_xor(x, (&mut k)[i as usize]);
      crate::lib::intvector::intrinsics::vec256_store32_le(
        &mut uu____0.1[i.wrapping_mul(32u32) as usize..],
        y
      )
    }
  };
  if rem1 > 0u32
  {
    let uu____2: (&mut [u8], &mut [u8]) =
      out.split_at_mut((nb.wrapping_mul(512u32) as usize).wrapping_add(0usize));
    let mut plain: [u8; 512] = [0u8; 512u32 as usize];
    ((&mut plain)[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut cipher[nb.wrapping_mul(512u32) as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    );
    let mut k: [crate::lib::intvector::intrinsics::vec256; 16] =
      [crate::lib::intvector::intrinsics::vec256_zero; 16u32 as usize];
    chacha20_core_256(&mut k, &mut ctx, nb);
    let st0: crate::lib::intvector::intrinsics::vec256 = (&mut k)[0u32 as usize];
    let st1: crate::lib::intvector::intrinsics::vec256 = (&mut k)[1u32 as usize];
    let st2: crate::lib::intvector::intrinsics::vec256 = (&mut k)[2u32 as usize];
    let st3: crate::lib::intvector::intrinsics::vec256 = (&mut k)[3u32 as usize];
    let st4: crate::lib::intvector::intrinsics::vec256 = (&mut k)[4u32 as usize];
    let st5: crate::lib::intvector::intrinsics::vec256 = (&mut k)[5u32 as usize];
    let st6: crate::lib::intvector::intrinsics::vec256 = (&mut k)[6u32 as usize];
    let st7: crate::lib::intvector::intrinsics::vec256 = (&mut k)[7u32 as usize];
    let st8: crate::lib::intvector::intrinsics::vec256 = (&mut k)[8u32 as usize];
    let st9: crate::lib::intvector::intrinsics::vec256 = (&mut k)[9u32 as usize];
    let st10: crate::lib::intvector::intrinsics::vec256 = (&mut k)[10u32 as usize];
    let st11: crate::lib::intvector::intrinsics::vec256 = (&mut k)[11u32 as usize];
    let st12: crate::lib::intvector::intrinsics::vec256 = (&mut k)[12u32 as usize];
    let st13: crate::lib::intvector::intrinsics::vec256 = (&mut k)[13u32 as usize];
    let st14: crate::lib::intvector::intrinsics::vec256 = (&mut k)[14u32 as usize];
    let st15: crate::lib::intvector::intrinsics::vec256 = (&mut k)[15u32 as usize];
    let v0: crate::lib::intvector::intrinsics::vec256 = st0;
    let v1: crate::lib::intvector::intrinsics::vec256 = st1;
    let v2: crate::lib::intvector::intrinsics::vec256 = st2;
    let v3: crate::lib::intvector::intrinsics::vec256 = st3;
    let v4: crate::lib::intvector::intrinsics::vec256 = st4;
    let v5: crate::lib::intvector::intrinsics::vec256 = st5;
    let v6: crate::lib::intvector::intrinsics::vec256 = st6;
    let v7: crate::lib::intvector::intrinsics::vec256 = st7;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v0, v1);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v0, v1);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v2, v3);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v2, v3);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v4, v5);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v4, v5);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v6, v7);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v6, v7);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0: crate::lib::intvector::intrinsics::vec256 = v0';
    let v1: crate::lib::intvector::intrinsics::vec256 = v2';
    let v2: crate::lib::intvector::intrinsics::vec256 = v1';
    let v3: crate::lib::intvector::intrinsics::vec256 = v3';
    let v4: crate::lib::intvector::intrinsics::vec256 = v4';
    let v5: crate::lib::intvector::intrinsics::vec256 = v6';
    let v6: crate::lib::intvector::intrinsics::vec256 = v5';
    let v7: crate::lib::intvector::intrinsics::vec256 = v7';
    let v01: crate::lib::intvector::intrinsics::vec256 = st8;
    let v11: crate::lib::intvector::intrinsics::vec256 = st9;
    let v21: crate::lib::intvector::intrinsics::vec256 = st10;
    let v31: crate::lib::intvector::intrinsics::vec256 = st11;
    let v41: crate::lib::intvector::intrinsics::vec256 = st12;
    let v51: crate::lib::intvector::intrinsics::vec256 = st13;
    let v61: crate::lib::intvector::intrinsics::vec256 = st14;
    let v71: crate::lib::intvector::intrinsics::vec256 = st15;
    let v0': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v01, v11);
    let v1': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v01, v11);
    let v2': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v21, v31);
    let v3': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v21, v31);
    let v4': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v41, v51);
    let v5': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v41, v51);
    let v6': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low32(v61, v71);
    let v7': crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high32(v61, v71);
    let v0': crate::lib::intvector::intrinsics::vec256 = v0';
    let v1': crate::lib::intvector::intrinsics::vec256 = v1';
    let v2': crate::lib::intvector::intrinsics::vec256 = v2';
    let v3': crate::lib::intvector::intrinsics::vec256 = v3';
    let v4': crate::lib::intvector::intrinsics::vec256 = v4';
    let v5': crate::lib::intvector::intrinsics::vec256 = v5';
    let v6': crate::lib::intvector::intrinsics::vec256 = v6';
    let v7': crate::lib::intvector::intrinsics::vec256 = v7';
    let v0'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v0', v2');
    let v2'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v0', v2');
    let v1'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v1', v3');
    let v3'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v1', v3');
    let v4'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v4', v6');
    let v6'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v4', v6');
    let v5'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low64(v5', v7');
    let v7'1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high64(v5', v7');
    let v0'1: crate::lib::intvector::intrinsics::vec256 = v0'1;
    let v1'1: crate::lib::intvector::intrinsics::vec256 = v1'1;
    let v2'1: crate::lib::intvector::intrinsics::vec256 = v2'1;
    let v3'1: crate::lib::intvector::intrinsics::vec256 = v3'1;
    let v4'1: crate::lib::intvector::intrinsics::vec256 = v4'1;
    let v5'1: crate::lib::intvector::intrinsics::vec256 = v5'1;
    let v6'1: crate::lib::intvector::intrinsics::vec256 = v6'1;
    let v7'1: crate::lib::intvector::intrinsics::vec256 = v7'1;
    let v0'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v0'1, v4'1);
    let v4'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v0'1, v4'1);
    let v1'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v1'1, v5'1);
    let v5'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v1'1, v5'1);
    let v2'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v2'1, v6'1);
    let v6'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v2'1, v6'1);
    let v3'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_low128(v3'1, v7'1);
    let v7'2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_interleave_high128(v3'1, v7'1);
    let v0'2: crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1'2: crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2'2: crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3'2: crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4'2: crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5'2: crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6'2: crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7'2: crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v0': crate::lib::intvector::intrinsics::vec256 = v0'2;
    let v1': crate::lib::intvector::intrinsics::vec256 = v1'2;
    let v2': crate::lib::intvector::intrinsics::vec256 = v2'2;
    let v3': crate::lib::intvector::intrinsics::vec256 = v3'2;
    let v4': crate::lib::intvector::intrinsics::vec256 = v4'2;
    let v5': crate::lib::intvector::intrinsics::vec256 = v5'2;
    let v6': crate::lib::intvector::intrinsics::vec256 = v6'2;
    let v7': crate::lib::intvector::intrinsics::vec256 = v7'2;
    let v8: crate::lib::intvector::intrinsics::vec256 = v0';
    let v9: crate::lib::intvector::intrinsics::vec256 = v2';
    let v10: crate::lib::intvector::intrinsics::vec256 = v1';
    let v11: crate::lib::intvector::intrinsics::vec256 = v3';
    let v12: crate::lib::intvector::intrinsics::vec256 = v4';
    let v13: crate::lib::intvector::intrinsics::vec256 = v6';
    let v14: crate::lib::intvector::intrinsics::vec256 = v5';
    let v15: crate::lib::intvector::intrinsics::vec256 = v7';
    (&mut k)[0u32 as usize] = v0;
    (&mut k)[1u32 as usize] = v8;
    (&mut k)[2u32 as usize] = v1;
    (&mut k)[3u32 as usize] = v9;
    (&mut k)[4u32 as usize] = v2;
    (&mut k)[5u32 as usize] = v10;
    (&mut k)[6u32 as usize] = v3;
    (&mut k)[7u32 as usize] = v11;
    (&mut k)[8u32 as usize] = v4;
    (&mut k)[9u32 as usize] = v12;
    (&mut k)[10u32 as usize] = v5;
    (&mut k)[11u32 as usize] = v13;
    (&mut k)[12u32 as usize] = v6;
    (&mut k)[13u32 as usize] = v14;
    (&mut k)[14u32 as usize] = v7;
    (&mut k)[15u32 as usize] = v15;
    for i in 0u32..16u32
    {
      let x: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load32_le(
          &mut (&mut plain)[i.wrapping_mul(32u32) as usize..]
        );
      let y: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_xor(x, (&mut k)[i as usize]);
      crate::lib::intvector::intrinsics::vec256_store32_le(
        &mut (&mut plain)[i.wrapping_mul(32u32) as usize..],
        y
      )
    };
    (uu____2.1[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    )
  }
}