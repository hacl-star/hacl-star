pub const chacha20_constants: [u32; 4] =
  [0x61707865u32, 0x3320646eu32, 0x79622d32u32, 0x6b206574u32];

fn quarter_round(st: &mut [u32], a: u32, b: u32, c: u32, d: u32) -> ()
{
  let sta: u32 = st[a as usize];
  let stb: u32 = st[b as usize];
  let std: u32 = st[d as usize];
  let sta1: u32 = sta.wrapping_add(stb);
  let std1: u32 = std ^ sta1;
  let std2: u32 = std1.wrapping_shl(16u32) | std1.wrapping_shr(16u32);
  st[a as usize] = sta1;
  st[d as usize] = std2;
  let sta: u32 = st[c as usize];
  let stb: u32 = st[d as usize];
  let std: u32 = st[b as usize];
  let sta1: u32 = sta.wrapping_add(stb);
  let std1: u32 = std ^ sta1;
  let std2: u32 = std1.wrapping_shl(12u32) | std1.wrapping_shr(20u32);
  st[c as usize] = sta1;
  st[b as usize] = std2;
  let sta: u32 = st[a as usize];
  let stb: u32 = st[b as usize];
  let std: u32 = st[d as usize];
  let sta1: u32 = sta.wrapping_add(stb);
  let std1: u32 = std ^ sta1;
  let std2: u32 = std1.wrapping_shl(8u32) | std1.wrapping_shr(24u32);
  st[a as usize] = sta1;
  st[d as usize] = std2;
  let sta: u32 = st[c as usize];
  let stb: u32 = st[d as usize];
  let std: u32 = st[b as usize];
  let sta1: u32 = sta.wrapping_add(stb);
  let std1: u32 = std ^ sta1;
  let std2: u32 = std1.wrapping_shl(7u32) | std1.wrapping_shr(25u32);
  st[c as usize] = sta1;
  st[b as usize] = std2
}

fn double_round(st: &mut [u32]) -> ()
{
  quarter_round(st, 0u32, 4u32, 8u32, 12u32);
  quarter_round(st, 1u32, 5u32, 9u32, 13u32);
  quarter_round(st, 2u32, 6u32, 10u32, 14u32);
  quarter_round(st, 3u32, 7u32, 11u32, 15u32);
  quarter_round(st, 0u32, 5u32, 10u32, 15u32);
  quarter_round(st, 1u32, 6u32, 11u32, 12u32);
  quarter_round(st, 2u32, 7u32, 8u32, 13u32);
  quarter_round(st, 3u32, 4u32, 9u32, 14u32)
}

fn rounds(st: &mut [u32]) -> ()
{
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st);
  double_round(st)
}

fn chacha20_core(k: &mut [u32], ctx: &mut [u32], ctr: u32) -> ()
{
  (k[0u32 as usize..0u32 as usize + 16u32 as usize]).copy_from_slice(
    &ctx[0u32 as usize..0u32 as usize + 16u32 as usize]
  );
  let ctr_u32: u32 = ctr;
  k[12u32 as usize] = (k[12u32 as usize]).wrapping_add(ctr_u32);
  rounds(k);
  for i in 0u32..16u32
  {
    let os: (&mut [u32], &mut [u32]) = k.split_at_mut(0usize);
    let x: u32 = (os.1[i as usize]).wrapping_add(ctx[i as usize]);
    os.1[i as usize] = x
  };
  k[12u32 as usize] = (k[12u32 as usize]).wrapping_add(ctr_u32)
}

pub fn chacha20_init(ctx: &mut [u32], k: &mut [u8], n: &mut [u8], ctr: u32) -> ()
{
  for i in 0u32..4u32
  {
    let os: &mut [u32] = &mut (&mut ctx[0u32 as usize..])[0u32 as usize..];
    let x: u32 = (&chacha20_constants)[i as usize];
    os[i as usize] = x
  };
  for i in 0u32..8u32
  {
    let os: &mut [u32] = &mut (&mut ctx[4u32 as usize..])[0u32 as usize..];
    let bj: (&mut [u8], &mut [u8]) =
      k.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
    let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
    let r: u32 = u;
    let x: u32 = r;
    os[i as usize] = x
  };
  ctx[12u32 as usize] = ctr;
  for i in 0u32..3u32
  {
    let os: &mut [u32] = &mut (&mut ctx[13u32 as usize..])[0u32 as usize..];
    let bj: (&mut [u8], &mut [u8]) =
      n.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
    let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
    let r: u32 = u;
    let x: u32 = r;
    os[i as usize] = x
  }
}

fn chacha20_encrypt_block(ctx: &mut [u32], out: &mut [u8], incr: u32, text: &mut [u8]) -> ()
{
  let mut k: [u32; 16] = [0u32; 16u32 as usize];
  chacha20_core(&mut k, ctx, incr);
  let mut bl: [u32; 16] = [0u32; 16u32 as usize];
  for i in 0u32..16u32
  {
    let os: (&mut [u32], &mut [u32]) = (&mut bl).split_at_mut(0usize);
    let bj: (&mut [u8], &mut [u8]) =
      text.split_at_mut((i.wrapping_mul(4u32) as usize).wrapping_add(0usize));
    let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
    let r: u32 = u;
    let x: u32 = r;
    os.1[i as usize] = x
  };
  for i in 0u32..16u32
  {
    let os: (&mut [u32], &mut [u32]) = (&mut bl).split_at_mut(0usize);
    let x: u32 = os.1[i as usize] ^ (&mut k)[i as usize];
    os.1[i as usize] = x
  };
  for i in 0u32..16u32
  {
    crate::lowstar::endianness::store32_le(
      &mut out[i.wrapping_mul(4u32) as usize..],
      (&mut bl)[i as usize]
    )
  }
}

fn chacha20_encrypt_last(ctx: &mut [u32], len: u32, out: &mut [u8], incr: u32, text: &mut [u8]) ->
  ()
{
  let mut plain: [u8; 64] = [0u8; 64u32 as usize];
  ((&mut plain)[0u32 as usize..0u32 as usize + len as usize]).copy_from_slice(
    &text[0u32 as usize..0u32 as usize + len as usize]
  );
  let mut plain_copy: [u8; 64] = [0u8; 64u32 as usize];
  ((&mut plain_copy)[0u32 as usize..0u32 as usize + 64u32 as usize]).copy_from_slice(
    &(&mut plain)[0u32 as usize..0u32 as usize + 64u32 as usize]
  );
  chacha20_encrypt_block(ctx, &mut plain, incr, &mut plain_copy);
  (out[0u32 as usize..0u32 as usize + len as usize]).copy_from_slice(
    &(&mut (&mut plain)[0u32 as usize..])[0u32 as usize..0u32 as usize + len as usize]
  )
}

pub fn chacha20_update(ctx: &mut [u32], len: u32, out: &mut [u8], text: &mut [u8]) -> ()
{
  let rem: u32 = len.wrapping_rem(64u32);
  let nb: u32 = len.wrapping_div(64u32);
  let rem1: u32 = len.wrapping_rem(64u32);
  for i in 0u32..rem1
  {
    chacha20_encrypt_block(
      ctx,
      &mut out[i.wrapping_mul(64u32) as usize..],
      i,
      &mut text[i.wrapping_mul(64u32) as usize..]
    )
  };
  if rem1 > 0u32
  {
    chacha20_encrypt_last(
      ctx,
      rem,
      &mut out[nb.wrapping_mul(64u32) as usize..],
      nb,
      &mut text[nb.wrapping_mul(64u32) as usize..]
    )
  }
}

pub fn chacha20_encrypt(
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
  chacha20_init(&mut ctx, key, n, ctr);
  chacha20_update(&mut ctx, len, out, text)
}

pub fn chacha20_decrypt(
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
  chacha20_init(&mut ctx, key, n, ctr);
  chacha20_update(&mut ctx, len, out, cipher)
}