fn double_round_32(st: &mut [u32]) -> ()
{
  st[0u32 as usize] = (st[0u32 as usize]).wrapping_add(st[4u32 as usize]);
  let std: u32 = st[12u32 as usize] ^ st[0u32 as usize];
  st[12u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[8u32 as usize] = (st[8u32 as usize]).wrapping_add(st[12u32 as usize]);
  let std: u32 = st[4u32 as usize] ^ st[8u32 as usize];
  st[4u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[0u32 as usize] = (st[0u32 as usize]).wrapping_add(st[4u32 as usize]);
  let std: u32 = st[12u32 as usize] ^ st[0u32 as usize];
  st[12u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[8u32 as usize] = (st[8u32 as usize]).wrapping_add(st[12u32 as usize]);
  let std: u32 = st[4u32 as usize] ^ st[8u32 as usize];
  st[4u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[1u32 as usize] = (st[1u32 as usize]).wrapping_add(st[5u32 as usize]);
  let std: u32 = st[13u32 as usize] ^ st[1u32 as usize];
  st[13u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[9u32 as usize] = (st[9u32 as usize]).wrapping_add(st[13u32 as usize]);
  let std: u32 = st[5u32 as usize] ^ st[9u32 as usize];
  st[5u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[1u32 as usize] = (st[1u32 as usize]).wrapping_add(st[5u32 as usize]);
  let std: u32 = st[13u32 as usize] ^ st[1u32 as usize];
  st[13u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[9u32 as usize] = (st[9u32 as usize]).wrapping_add(st[13u32 as usize]);
  let std: u32 = st[5u32 as usize] ^ st[9u32 as usize];
  st[5u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[2u32 as usize] = (st[2u32 as usize]).wrapping_add(st[6u32 as usize]);
  let std: u32 = st[14u32 as usize] ^ st[2u32 as usize];
  st[14u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[10u32 as usize] = (st[10u32 as usize]).wrapping_add(st[14u32 as usize]);
  let std: u32 = st[6u32 as usize] ^ st[10u32 as usize];
  st[6u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[2u32 as usize] = (st[2u32 as usize]).wrapping_add(st[6u32 as usize]);
  let std: u32 = st[14u32 as usize] ^ st[2u32 as usize];
  st[14u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[10u32 as usize] = (st[10u32 as usize]).wrapping_add(st[14u32 as usize]);
  let std: u32 = st[6u32 as usize] ^ st[10u32 as usize];
  st[6u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[3u32 as usize] = (st[3u32 as usize]).wrapping_add(st[7u32 as usize]);
  let std: u32 = st[15u32 as usize] ^ st[3u32 as usize];
  st[15u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[11u32 as usize] = (st[11u32 as usize]).wrapping_add(st[15u32 as usize]);
  let std: u32 = st[7u32 as usize] ^ st[11u32 as usize];
  st[7u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[3u32 as usize] = (st[3u32 as usize]).wrapping_add(st[7u32 as usize]);
  let std: u32 = st[15u32 as usize] ^ st[3u32 as usize];
  st[15u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[11u32 as usize] = (st[11u32 as usize]).wrapping_add(st[15u32 as usize]);
  let std: u32 = st[7u32 as usize] ^ st[11u32 as usize];
  st[7u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[0u32 as usize] = (st[0u32 as usize]).wrapping_add(st[5u32 as usize]);
  let std: u32 = st[15u32 as usize] ^ st[0u32 as usize];
  st[15u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[10u32 as usize] = (st[10u32 as usize]).wrapping_add(st[15u32 as usize]);
  let std: u32 = st[5u32 as usize] ^ st[10u32 as usize];
  st[5u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[0u32 as usize] = (st[0u32 as usize]).wrapping_add(st[5u32 as usize]);
  let std: u32 = st[15u32 as usize] ^ st[0u32 as usize];
  st[15u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[10u32 as usize] = (st[10u32 as usize]).wrapping_add(st[15u32 as usize]);
  let std: u32 = st[5u32 as usize] ^ st[10u32 as usize];
  st[5u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[1u32 as usize] = (st[1u32 as usize]).wrapping_add(st[6u32 as usize]);
  let std: u32 = st[12u32 as usize] ^ st[1u32 as usize];
  st[12u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[11u32 as usize] = (st[11u32 as usize]).wrapping_add(st[12u32 as usize]);
  let std: u32 = st[6u32 as usize] ^ st[11u32 as usize];
  st[6u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[1u32 as usize] = (st[1u32 as usize]).wrapping_add(st[6u32 as usize]);
  let std: u32 = st[12u32 as usize] ^ st[1u32 as usize];
  st[12u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[11u32 as usize] = (st[11u32 as usize]).wrapping_add(st[12u32 as usize]);
  let std: u32 = st[6u32 as usize] ^ st[11u32 as usize];
  st[6u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[2u32 as usize] = (st[2u32 as usize]).wrapping_add(st[7u32 as usize]);
  let std: u32 = st[13u32 as usize] ^ st[2u32 as usize];
  st[13u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[8u32 as usize] = (st[8u32 as usize]).wrapping_add(st[13u32 as usize]);
  let std: u32 = st[7u32 as usize] ^ st[8u32 as usize];
  st[7u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[2u32 as usize] = (st[2u32 as usize]).wrapping_add(st[7u32 as usize]);
  let std: u32 = st[13u32 as usize] ^ st[2u32 as usize];
  st[13u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[8u32 as usize] = (st[8u32 as usize]).wrapping_add(st[13u32 as usize]);
  let std: u32 = st[7u32 as usize] ^ st[8u32 as usize];
  st[7u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32);
  st[3u32 as usize] = (st[3u32 as usize]).wrapping_add(st[4u32 as usize]);
  let std: u32 = st[14u32 as usize] ^ st[3u32 as usize];
  st[14u32 as usize] = std.wrapping_shl(16u32) | std.wrapping_shr(16u32);
  st[9u32 as usize] = (st[9u32 as usize]).wrapping_add(st[14u32 as usize]);
  let std: u32 = st[4u32 as usize] ^ st[9u32 as usize];
  st[4u32 as usize] = std.wrapping_shl(12u32) | std.wrapping_shr(20u32);
  st[3u32 as usize] = (st[3u32 as usize]).wrapping_add(st[4u32 as usize]);
  let std: u32 = st[14u32 as usize] ^ st[3u32 as usize];
  st[14u32 as usize] = std.wrapping_shl(8u32) | std.wrapping_shr(24u32);
  st[9u32 as usize] = (st[9u32 as usize]).wrapping_add(st[14u32 as usize]);
  let std: u32 = st[4u32 as usize] ^ st[9u32 as usize];
  st[4u32 as usize] = std.wrapping_shl(7u32) | std.wrapping_shr(25u32)
}

fn chacha20_core_32(k: &mut [u32], ctx: &mut [u32], ctr: u32) -> ()
{
  (k[0u32 as usize..0u32 as usize + 16u32 as usize]).copy_from_slice(
    &ctx[0u32 as usize..0u32 as usize + 16u32 as usize]
  );
  let ctr_u32: u32 = 1u32.wrapping_mul(ctr);
  let cv: u32 = ctr_u32;
  k[12u32 as usize] = (k[12u32 as usize]).wrapping_add(cv);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  double_round_32(k);
  for i in 0u32..16u32
  {
    let os: (&mut [u32], &mut [u32]) = k.split_at_mut(0usize);
    let x: u32 = (os.1[i as usize]).wrapping_add(ctx[i as usize]);
    os.1[i as usize] = x
  };
  k[12u32 as usize] = (k[12u32 as usize]).wrapping_add(cv)
}

fn chacha20_init_32(ctx: &mut [u32], k: &mut [u8], n: &mut [u8], ctr: u32) -> ()
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
    let os: (&mut [u32], &mut [u32]) = ctx.split_at_mut(0usize);
    let x: u32 = (&mut ctx1)[i as usize];
    os.1[i as usize] = x
  };
  let ctr1: u32 = 0u32;
  let c12: u32 = ctx[12u32 as usize];
  ctx[12u32 as usize] = c12.wrapping_add(ctr1)
}

pub fn chacha20_encrypt_32(
  len: u32,
  out: &mut [u8],
  text: &mut [u8],
  key: &mut [u8],
  n: &mut [u8],
  ctr: u32
) ->
  ()
{
  let mut ctx: [u32; 16] = [0u32; 16u32 as usize];
  chacha20_init_32(&mut ctx, key, n, ctr);
  let rem: u32 = len.wrapping_rem(64u32);
  let nb: u32 = len.wrapping_div(64u32);
  let rem1: u32 = len.wrapping_rem(64u32);
  for i in 0u32..rem1
  {
    let uu____0: (&mut [u8], &mut [u8]) =
      out.split_at_mut((i.wrapping_mul(64u32) as usize).wrapping_add(0usize));
    let uu____1: (&mut [u8], &mut [u8]) =
      text.split_at_mut((i.wrapping_mul(64u32) as usize).wrapping_add(0usize));
    let mut k: [u32; 16] = [0u32; 16u32 as usize];
    chacha20_core_32(&mut k, &mut ctx, i);
    for i in 0u32..16u32
    {
      let u: u32 =
        crate::lowstar::endianness::load32_le(&mut uu____1.1[i.wrapping_mul(4u32) as usize..]);
      let x: u32 = u;
      let y: u32 = x ^ (&mut k)[i as usize];
      crate::lowstar::endianness::store32_le(&mut uu____0.1[i.wrapping_mul(4u32) as usize..], y)
    }
  };
  if rem1 > 0u32
  {
    let uu____2: (&mut [u8], &mut [u8]) =
      out.split_at_mut((nb.wrapping_mul(64u32) as usize).wrapping_add(0usize));
    let mut plain: [u8; 64] = [0u8; 64u32 as usize];
    ((&mut plain)[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut text[nb.wrapping_mul(64u32) as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    );
    let mut k: [u32; 16] = [0u32; 16u32 as usize];
    chacha20_core_32(&mut k, &mut ctx, nb);
    for i in 0u32..16u32
    {
      let u: u32 =
        crate::lowstar::endianness::load32_le(&mut (&mut plain)[i.wrapping_mul(4u32) as usize..]);
      let x: u32 = u;
      let y: u32 = x ^ (&mut k)[i as usize];
      crate::lowstar::endianness::store32_le(&mut (&mut plain)[i.wrapping_mul(4u32) as usize..], y)
    };
    (uu____2.1[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    )
  }
}

pub fn chacha20_decrypt_32(
  len: u32,
  out: &mut [u8],
  cipher: &mut [u8],
  key: &mut [u8],
  n: &mut [u8],
  ctr: u32
) ->
  ()
{
  let mut ctx: [u32; 16] = [0u32; 16u32 as usize];
  chacha20_init_32(&mut ctx, key, n, ctr);
  let rem: u32 = len.wrapping_rem(64u32);
  let nb: u32 = len.wrapping_div(64u32);
  let rem1: u32 = len.wrapping_rem(64u32);
  for i in 0u32..rem1
  {
    let uu____0: (&mut [u8], &mut [u8]) =
      out.split_at_mut((i.wrapping_mul(64u32) as usize).wrapping_add(0usize));
    let uu____1: (&mut [u8], &mut [u8]) =
      cipher.split_at_mut((i.wrapping_mul(64u32) as usize).wrapping_add(0usize));
    let mut k: [u32; 16] = [0u32; 16u32 as usize];
    chacha20_core_32(&mut k, &mut ctx, i);
    for i in 0u32..16u32
    {
      let u: u32 =
        crate::lowstar::endianness::load32_le(&mut uu____1.1[i.wrapping_mul(4u32) as usize..]);
      let x: u32 = u;
      let y: u32 = x ^ (&mut k)[i as usize];
      crate::lowstar::endianness::store32_le(&mut uu____0.1[i.wrapping_mul(4u32) as usize..], y)
    }
  };
  if rem1 > 0u32
  {
    let uu____2: (&mut [u8], &mut [u8]) =
      out.split_at_mut((nb.wrapping_mul(64u32) as usize).wrapping_add(0usize));
    let mut plain: [u8; 64] = [0u8; 64u32 as usize];
    ((&mut plain)[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut cipher[nb.wrapping_mul(64u32) as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    );
    let mut k: [u32; 16] = [0u32; 16u32 as usize];
    chacha20_core_32(&mut k, &mut ctx, nb);
    for i in 0u32..16u32
    {
      let u: u32 =
        crate::lowstar::endianness::load32_le(&mut (&mut plain)[i.wrapping_mul(4u32) as usize..]);
      let x: u32 = u;
      let y: u32 = x ^ (&mut k)[i as usize];
      crate::lowstar::endianness::store32_le(&mut (&mut plain)[i.wrapping_mul(4u32) as usize..], y)
    };
    (uu____2.1[0u32 as usize..0u32 as usize + rem as usize]).copy_from_slice(
      &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + rem as usize]
    )
  }
}