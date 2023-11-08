fn fsum(out: &mut [u64], a: &mut [u64], b: &mut [u64]) -> ()
{ crate::hacl::bignum25519_51::fadd(out, a, b) }

fn fdifference(out: &mut [u64], a: &mut [u64], b: &mut [u64]) -> ()
{ crate::hacl::bignum25519_51::fsub(out, a, b) }

pub fn reduce_513(a: &mut [u64]) -> ()
{
  let f0: u64 = a[0u32 as usize];
  let f1: u64 = a[1u32 as usize];
  let f2: u64 = a[2u32 as usize];
  let f3: u64 = a[3u32 as usize];
  let f4: u64 = a[4u32 as usize];
  let l': u64 = f0.wrapping_add(0u64);
  let tmp0: u64 = l' & 0x7ffffffffffffu64;
  let c0: u64 = l'.wrapping_shr(51u32);
  let l': u64 = f1.wrapping_add(c0);
  let tmp1: u64 = l' & 0x7ffffffffffffu64;
  let c1: u64 = l'.wrapping_shr(51u32);
  let l': u64 = f2.wrapping_add(c1);
  let tmp2: u64 = l' & 0x7ffffffffffffu64;
  let c2: u64 = l'.wrapping_shr(51u32);
  let l': u64 = f3.wrapping_add(c2);
  let tmp3: u64 = l' & 0x7ffffffffffffu64;
  let c3: u64 = l'.wrapping_shr(51u32);
  let l': u64 = f4.wrapping_add(c3);
  let tmp4: u64 = l' & 0x7ffffffffffffu64;
  let c4: u64 = l'.wrapping_shr(51u32);
  let l': u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
  let tmp0': u64 = l' & 0x7ffffffffffffu64;
  let c5: u64 = l'.wrapping_shr(51u32);
  a[0u32 as usize] = tmp0';
  a[1u32 as usize] = tmp1.wrapping_add(c5);
  a[2u32 as usize] = tmp2;
  a[3u32 as usize] = tmp3;
  a[4u32 as usize] = tmp4
}

fn fmul(output: &mut [u64], input: &mut [u64], input2: &mut [u64]) -> ()
{
  let mut tmp: [crate::fstar::uint128::uint128; 10] =
    [crate::fstar::uint128::uint64_to_uint128(0u64); 10u32 as usize];
  crate::hacl::impl::curve25519::field51::fmul(output, input, input2, &mut tmp)
}

fn times_2(out: &mut [u64], a: &mut [u64]) -> ()
{
  let a0: u64 = a[0u32 as usize];
  let a1: u64 = a[1u32 as usize];
  let a2: u64 = a[2u32 as usize];
  let a3: u64 = a[3u32 as usize];
  let a4: u64 = a[4u32 as usize];
  let o0: u64 = 2u64.wrapping_mul(a0);
  let o1: u64 = 2u64.wrapping_mul(a1);
  let o2: u64 = 2u64.wrapping_mul(a2);
  let o3: u64 = 2u64.wrapping_mul(a3);
  let o4: u64 = 2u64.wrapping_mul(a4);
  out[0u32 as usize] = o0;
  out[1u32 as usize] = o1;
  out[2u32 as usize] = o2;
  out[3u32 as usize] = o3;
  out[4u32 as usize] = o4
}

fn times_d(out: &mut [u64], a: &mut [u64]) -> ()
{
  let mut d: [u64; 5] = [0u64; 5u32 as usize];
  (&mut d)[0u32 as usize] = 0x00034dca135978a3u64;
  (&mut d)[1u32 as usize] = 0x0001a8283b156ebdu64;
  (&mut d)[2u32 as usize] = 0x0005e7a26001c029u64;
  (&mut d)[3u32 as usize] = 0x000739c663a03cbbu64;
  (&mut d)[4u32 as usize] = 0x00052036cee2b6ffu64;
  fmul(out, &mut d, a)
}

fn times_2d(out: &mut [u64], a: &mut [u64]) -> ()
{
  let mut d2: [u64; 5] = [0u64; 5u32 as usize];
  (&mut d2)[0u32 as usize] = 0x00069b9426b2f159u64;
  (&mut d2)[1u32 as usize] = 0x00035050762add7au64;
  (&mut d2)[2u32 as usize] = 0x0003cf44c0038052u64;
  (&mut d2)[3u32 as usize] = 0x0006738cc7407977u64;
  (&mut d2)[4u32 as usize] = 0x0002406d9dc56dffu64;
  fmul(out, &mut d2, a)
}

fn fsquare(out: &mut [u64], a: &mut [u64]) -> ()
{
  let mut tmp: [crate::fstar::uint128::uint128; 5] =
    [crate::fstar::uint128::uint64_to_uint128(0u64); 5u32 as usize];
  crate::hacl::impl::curve25519::field51::fsqr(out, a, &mut tmp)
}

fn fsquare_times(output: &mut [u64], input: &mut [u64], count: u32) -> ()
{
  let mut tmp: [crate::fstar::uint128::uint128; 5] =
    [crate::fstar::uint128::uint64_to_uint128(0u64); 5u32 as usize];
  crate::hacl::curve25519_51::fsquare_times(output, input, &mut tmp, count)
}

fn fsquare_times_inplace(output: &mut [u64], count: u32) -> ()
{
  let mut tmp: [crate::fstar::uint128::uint128; 5] =
    [crate::fstar::uint128::uint64_to_uint128(0u64); 5u32 as usize];
  crate::hacl::curve25519_51::fsquare_times(output, output, &mut tmp, count)
}

pub fn inverse(out: &mut [u64], a: &mut [u64]) -> ()
{
  let mut tmp: [crate::fstar::uint128::uint128; 10] =
    [crate::fstar::uint128::uint64_to_uint128(0u64); 10u32 as usize];
  crate::hacl::curve25519_51::finv(out, a, &mut tmp)
}

fn reduce(out: &mut [u64]) -> ()
{
  let o0: u64 = out[0u32 as usize];
  let o1: u64 = out[1u32 as usize];
  let o2: u64 = out[2u32 as usize];
  let o3: u64 = out[3u32 as usize];
  let o4: u64 = out[4u32 as usize];
  let l': u64 = o0.wrapping_add(0u64);
  let tmp0: u64 = l' & 0x7ffffffffffffu64;
  let c0: u64 = l'.wrapping_shr(51u32);
  let l': u64 = o1.wrapping_add(c0);
  let tmp1: u64 = l' & 0x7ffffffffffffu64;
  let c1: u64 = l'.wrapping_shr(51u32);
  let l': u64 = o2.wrapping_add(c1);
  let tmp2: u64 = l' & 0x7ffffffffffffu64;
  let c2: u64 = l'.wrapping_shr(51u32);
  let l': u64 = o3.wrapping_add(c2);
  let tmp3: u64 = l' & 0x7ffffffffffffu64;
  let c3: u64 = l'.wrapping_shr(51u32);
  let l': u64 = o4.wrapping_add(c3);
  let tmp4: u64 = l' & 0x7ffffffffffffu64;
  let c4: u64 = l'.wrapping_shr(51u32);
  let l': u64 = tmp0.wrapping_add(c4.wrapping_mul(19u64));
  let tmp0': u64 = l' & 0x7ffffffffffffu64;
  let c5: u64 = l'.wrapping_shr(51u32);
  let f0: u64 = tmp0';
  let f1: u64 = tmp1.wrapping_add(c5);
  let f2: u64 = tmp2;
  let f3: u64 = tmp3;
  let f4: u64 = tmp4;
  let m0: u64 = crate::fstar::uint64::gte_mask(f0, 0x7ffffffffffedu64);
  let m1: u64 = crate::fstar::uint64::eq_mask(f1, 0x7ffffffffffffu64);
  let m2: u64 = crate::fstar::uint64::eq_mask(f2, 0x7ffffffffffffu64);
  let m3: u64 = crate::fstar::uint64::eq_mask(f3, 0x7ffffffffffffu64);
  let m4: u64 = crate::fstar::uint64::eq_mask(f4, 0x7ffffffffffffu64);
  let mask: u64 = m0 & m1 & m2 & m3 & m4;
  let f0': u64 = f0.wrapping_sub(mask & 0x7ffffffffffedu64);
  let f1': u64 = f1.wrapping_sub(mask & 0x7ffffffffffffu64);
  let f2': u64 = f2.wrapping_sub(mask & 0x7ffffffffffffu64);
  let f3': u64 = f3.wrapping_sub(mask & 0x7ffffffffffffu64);
  let f4': u64 = f4.wrapping_sub(mask & 0x7ffffffffffffu64);
  let f01: u64 = f0';
  let f11: u64 = f1';
  let f21: u64 = f2';
  let f31: u64 = f3';
  let f41: u64 = f4';
  out[0u32 as usize] = f01;
  out[1u32 as usize] = f11;
  out[2u32 as usize] = f21;
  out[3u32 as usize] = f31;
  out[4u32 as usize] = f41
}

pub fn load_51(output: &mut [u64], input: &mut [u8]) -> ()
{
  let mut u64s: [u64; 4] = [0u64; 4u32 as usize];
  for i in 0u32..4u32
  {
    let os: (&mut [u64], &mut [u64]) = (&mut u64s).split_at_mut(0usize);
    let bj: (&mut [u8], &mut [u8]) =
      input.split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
    let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
    let r: u64 = u;
    let x: u64 = r;
    os.1[i as usize] = x
  };
  let u64s3: u64 = (&mut u64s)[3u32 as usize];
  (&mut u64s)[3u32 as usize] = u64s3 & 0x7fffffffffffffffu64;
  output[0u32 as usize] = (&mut u64s)[0u32 as usize] & 0x7ffffffffffffu64;
  output[1u32 as usize] =
    ((&mut u64s)[0u32 as usize]).wrapping_shr(51u32)
    |
    ((&mut u64s)[1u32 as usize] & 0x3fffffffffu64).wrapping_shl(13u32);
  output[2u32 as usize] =
    ((&mut u64s)[1u32 as usize]).wrapping_shr(38u32)
    |
    ((&mut u64s)[2u32 as usize] & 0x1ffffffu64).wrapping_shl(26u32);
  output[3u32 as usize] =
    ((&mut u64s)[2u32 as usize]).wrapping_shr(25u32)
    |
    ((&mut u64s)[3u32 as usize] & 0xfffu64).wrapping_shl(39u32);
  output[4u32 as usize] = ((&mut u64s)[3u32 as usize]).wrapping_shr(12u32)
}

pub fn store_51(output: &mut [u8], input: &mut [u64]) -> ()
{
  let mut u64s: [u64; 4] = [0u64; 4u32 as usize];
  crate::hacl::bignum25519_51::store_felem(&mut u64s, input);
  for i in 0u32..4u32
  {
    crate::lowstar::endianness::store64_le(
      &mut output[i.wrapping_mul(8u32) as usize..],
      (&mut u64s)[i as usize]
    )
  }
}

pub fn point_double(out: &mut [u64], p: &mut [u64]) -> ()
{
  let mut tmp: [u64; 20] = [0u64; 20u32 as usize];
  let tmp1: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
  let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(5usize);
  let tmp3: (&mut [u64], &mut [u64]) = tmp2.1.split_at_mut(5usize);
  let tmp4: (&mut [u64], &mut [u64]) = tmp3.1.split_at_mut(5usize);
  let x1: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
  let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
  let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
  fsquare(tmp2.0, y1.0);
  fsquare(tmp3.0, z1.0);
  fsum(tmp4.0, tmp2.0, tmp3.0);
  fdifference(tmp4.1, tmp2.0, tmp3.0);
  fsquare(tmp2.0, z1.1);
  times_2(tmp2.0, tmp2.0);
  let tmp1: (&mut [u64], &mut [u64]) = tmp2.0.split_at_mut(0usize);
  let tmp2: (&mut [u64], &mut [u64]) = tmp3.0.split_at_mut(0usize);
  let tmp3: (&mut [u64], &mut [u64]) = tmp4.0.split_at_mut(0usize);
  let tmp4: (&mut [u64], &mut [u64]) = tmp4.1.split_at_mut(0usize);
  let x1: (&mut [u64], &mut [u64]) = y1.0.split_at_mut(0usize);
  let y1: (&mut [u64], &mut [u64]) = z1.0.split_at_mut(0usize);
  fsum(tmp2.1, x1.1, y1.1);
  fsquare(tmp2.1, tmp2.1);
  reduce_513(tmp3.1);
  fdifference(tmp2.1, tmp3.1, tmp2.1);
  reduce_513(tmp1.1);
  reduce_513(tmp4.1);
  fsum(tmp1.1, tmp1.1, tmp4.1);
  let tmp_f: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(0usize);
  let tmp_e: (&mut [u64], &mut [u64]) = tmp2.1.split_at_mut(0usize);
  let tmp_h: (&mut [u64], &mut [u64]) = tmp3.1.split_at_mut(0usize);
  let tmp_g: (&mut [u64], &mut [u64]) = tmp4.1.split_at_mut(0usize);
  let x3: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
  let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(5usize);
  let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(5usize);
  let t3: (&mut [u64], &mut [u64]) = z3.1.split_at_mut(5usize);
  fmul(y3.0, tmp_e.1, tmp_f.1);
  fmul(z3.0, tmp_g.1, tmp_h.1);
  fmul(t3.1, tmp_e.1, tmp_h.1);
  fmul(t3.0, tmp_f.1, tmp_g.1)
}

pub fn point_add(out: &mut [u64], p: &mut [u64], q: &mut [u64]) -> ()
{
  let mut tmp: [u64; 30] = [0u64; 30u32 as usize];
  let tmp1: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
  let tmp2: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(5usize);
  let tmp3: (&mut [u64], &mut [u64]) = tmp2.1.split_at_mut(5usize);
  let tmp4: (&mut [u64], &mut [u64]) = tmp3.1.split_at_mut(5usize);
  let x1: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
  let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
  let x2: (&mut [u64], &mut [u64]) = q.split_at_mut(0usize);
  let y2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(5usize);
  fdifference(tmp2.0, y1.1, y1.0);
  fdifference(tmp3.0, y2.1, y2.0);
  fmul(tmp4.0, tmp2.0, tmp3.0);
  fsum(tmp2.0, y1.1, y1.0);
  fsum(tmp3.0, y2.1, y2.0);
  fmul(tmp4.1, tmp2.0, tmp3.0);
  let tmp1: (&mut [u64], &mut [u64]) = tmp2.0.split_at_mut(0usize);
  let tmp2: (&mut [u64], &mut [u64]) = tmp3.0.split_at_mut(0usize);
  let tmp3: (&mut [u64], &mut [u64]) = tmp4.0.split_at_mut(0usize);
  let tmp4: (&mut [u64], &mut [u64]) = tmp4.1.split_at_mut(0usize);
  let tmp5: (&mut [u64], &mut [u64]) = tmp4.1.split_at_mut(5usize);
  let tmp6: (&mut [u64], &mut [u64]) = tmp5.1.split_at_mut(5usize);
  let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
  let t1: (&mut [u64], &mut [u64]) = z1.1.split_at_mut(5usize);
  let z2: (&mut [u64], &mut [u64]) = y2.1.split_at_mut(5usize);
  let t2: (&mut [u64], &mut [u64]) = z2.1.split_at_mut(5usize);
  times_2d(tmp1.1, t1.1);
  fmul(tmp1.1, tmp1.1, t2.1);
  times_2(tmp2.1, t1.0);
  fmul(tmp2.1, tmp2.1, t2.0);
  fdifference(tmp6.0, tmp5.0, tmp3.1);
  fdifference(tmp6.1, tmp2.1, tmp1.1);
  fsum(tmp1.1, tmp2.1, tmp1.1);
  fsum(tmp2.1, tmp5.0, tmp3.1);
  let tmp_g: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(0usize);
  let tmp_h: (&mut [u64], &mut [u64]) = tmp2.1.split_at_mut(0usize);
  let tmp_e: (&mut [u64], &mut [u64]) = tmp6.0.split_at_mut(0usize);
  let tmp_f: (&mut [u64], &mut [u64]) = tmp6.1.split_at_mut(0usize);
  let x3: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
  let y3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(5usize);
  let z3: (&mut [u64], &mut [u64]) = y3.1.split_at_mut(5usize);
  let t3: (&mut [u64], &mut [u64]) = z3.1.split_at_mut(5usize);
  fmul(y3.0, tmp_e.1, tmp_f.1);
  fmul(z3.0, tmp_g.1, tmp_h.1);
  fmul(t3.1, tmp_e.1, tmp_h.1);
  fmul(t3.0, tmp_f.1, tmp_g.1)
}

pub fn make_point_inf(b: &mut [u64]) -> ()
{
  let x: (&mut [u64], &mut [u64]) = b.split_at_mut(0usize);
  let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
  let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(5usize);
  let t: (&mut [u64], &mut [u64]) = z.1.split_at_mut(5usize);
  y.0[0u32 as usize] = 0u64;
  y.0[1u32 as usize] = 0u64;
  y.0[2u32 as usize] = 0u64;
  y.0[3u32 as usize] = 0u64;
  y.0[4u32 as usize] = 0u64;
  z.0[0u32 as usize] = 1u64;
  z.0[1u32 as usize] = 0u64;
  z.0[2u32 as usize] = 0u64;
  z.0[3u32 as usize] = 0u64;
  z.0[4u32 as usize] = 0u64;
  t.0[0u32 as usize] = 1u64;
  t.0[1u32 as usize] = 0u64;
  t.0[2u32 as usize] = 0u64;
  t.0[3u32 as usize] = 0u64;
  t.0[4u32 as usize] = 0u64;
  t.1[0u32 as usize] = 0u64;
  t.1[1u32 as usize] = 0u64;
  t.1[2u32 as usize] = 0u64;
  t.1[3u32 as usize] = 0u64;
  t.1[4u32 as usize] = 0u64
}

fn pow2_252m2(out: &mut [u64], z: &mut [u64]) -> ()
{
  let mut buf: [u64; 20] = [0u64; 20u32 as usize];
  let a: (&mut [u64], &mut [u64]) = (&mut buf).split_at_mut(0usize);
  let t0: (&mut [u64], &mut [u64]) = a.1.split_at_mut(5usize);
  let b: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(5usize);
  let c: (&mut [u64], &mut [u64]) = b.1.split_at_mut(5usize);
  fsquare_times(t0.0, z, 1u32);
  fsquare_times(b.0, t0.0, 2u32);
  fmul(c.0, b.0, z);
  fmul(t0.0, c.0, t0.0);
  fsquare_times(b.0, t0.0, 1u32);
  fmul(c.0, b.0, c.0);
  fsquare_times(b.0, c.0, 5u32);
  fmul(c.0, b.0, c.0);
  fsquare_times(b.0, c.0, 10u32);
  fmul(c.1, b.0, c.0);
  fsquare_times(b.0, c.1, 20u32);
  fmul(b.0, b.0, c.1);
  fsquare_times_inplace(b.0, 10u32);
  fmul(c.0, b.0, c.0);
  fsquare_times(b.0, c.0, 50u32);
  let a: (&mut [u64], &mut [u64]) = t0.0.split_at_mut(0usize);
  let t0: (&mut [u64], &mut [u64]) = b.0.split_at_mut(0usize);
  let b: (&mut [u64], &mut [u64]) = c.0.split_at_mut(0usize);
  let c: (&mut [u64], &mut [u64]) = c.1.split_at_mut(0usize);
  fsquare_times(a.1, z, 1u32);
  fmul(c.1, t0.1, b.1);
  fsquare_times(t0.1, c.1, 100u32);
  fmul(t0.1, t0.1, c.1);
  fsquare_times_inplace(t0.1, 50u32);
  fmul(t0.1, t0.1, b.1);
  fsquare_times_inplace(t0.1, 2u32);
  fmul(out, t0.1, a.1)
}

fn is_0(x: &mut [u64]) -> bool
{
  let x0: u64 = x[0u32 as usize];
  let x1: u64 = x[1u32 as usize];
  let x2: u64 = x[2u32 as usize];
  let x3: u64 = x[3u32 as usize];
  let x4: u64 = x[4u32 as usize];
  x0 == 0u64 && x1 == 0u64 && x2 == 0u64 && x3 == 0u64 && x4 == 0u64
}

fn mul_modp_sqrt_m1(x: &mut [u64]) -> ()
{
  let mut sqrt_m1: [u64; 5] = [0u64; 5u32 as usize];
  (&mut sqrt_m1)[0u32 as usize] = 0x00061b274a0ea0b0u64;
  (&mut sqrt_m1)[1u32 as usize] = 0x0000d5a5fc8f189du64;
  (&mut sqrt_m1)[2u32 as usize] = 0x0007ef5e9cbd0c60u64;
  (&mut sqrt_m1)[3u32 as usize] = 0x00078595a6804c9eu64;
  (&mut sqrt_m1)[4u32 as usize] = 0x0002b8324804fc1du64;
  fmul(x, x, &mut sqrt_m1)
}

fn recover_x(x: &mut [u64], y: &mut [u64], sign: u64) -> bool
{
  let mut tmp: [u64; 15] = [0u64; 15u32 as usize];
  let x2: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
  let x0: u64 = y[0u32 as usize];
  let x1: u64 = y[1u32 as usize];
  let x21: u64 = y[2u32 as usize];
  let x3: u64 = y[3u32 as usize];
  let x4: u64 = y[4u32 as usize];
  let b: bool =
    x0 >= 0x7ffffffffffedu64 && x1 == 0x7ffffffffffffu64 && x21 == 0x7ffffffffffffu64
    &&
    x3 == 0x7ffffffffffffu64
    &&
    x4 == 0x7ffffffffffffu64;
  let res: bool =
    if b
    { falsebool }
    else
    {
      let mut tmp1: [u64; 20] = [0u64; 20u32 as usize];
      let one: (&mut [u64], &mut [u64]) = (&mut tmp1).split_at_mut(0usize);
      let y2: (&mut [u64], &mut [u64]) = one.1.split_at_mut(5usize);
      let dyyi: (&mut [u64], &mut [u64]) = y2.1.split_at_mut(5usize);
      let dyy: (&mut [u64], &mut [u64]) = dyyi.1.split_at_mut(5usize);
      y2.0[0u32 as usize] = 1u64;
      ();
      y2.0[1u32 as usize] = 0u64;
      ();
      y2.0[2u32 as usize] = 0u64;
      ();
      y2.0[3u32 as usize] = 0u64;
      ();
      y2.0[4u32 as usize] = 0u64;
      ();
      fsquare(dyyi.0, y);
      times_d(dyy.1, dyyi.0);
      fsum(dyy.1, dyy.1, y2.0);
      reduce_513(dyy.1);
      inverse(dyy.0, dyy.1);
      fdifference(x2.1, dyyi.0, y2.0);
      fmul(x2.1, x2.1, dyy.0);
      reduce(x2.1);
      ();
      let x2_is_0: bool = is_0(x2.1);
      let z: u8 =
        if x2_is_0
        if sign == 0u64
        {
          x[0u32 as usize] = 0u64;
          ();
          x[1u32 as usize] = 0u64;
          ();
          x[2u32 as usize] = 0u64;
          ();
          x[3u32 as usize] = 0u64;
          ();
          x[4u32 as usize] = 0u64;
          ();
          1u8
        }
        else
        { 0u8 }
        else
        { 2u8 };
      if z == 0u8
      { falsebool }
      else
      if z == 1u8
      { truebool }
      else
      {
        let x21: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(0usize);
        let x3: (&mut [u64], &mut [u64]) = x21.1.split_at_mut(5usize);
        let t0: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(5usize);
        pow2_252m2(t0.0, x3.0);
        fsquare(t0.1, t0.0);
        fdifference(t0.1, t0.1, x3.0);
        reduce_513(t0.1);
        reduce(t0.1);
        let t0_is_0: bool = is_0(t0.1);
        if ! t0_is_0 { mul_modp_sqrt_m1(t0.0) };
        let x21: (&mut [u64], &mut [u64]) = x3.0.split_at_mut(0usize);
        let x3: (&mut [u64], &mut [u64]) = t0.0.split_at_mut(0usize);
        let t0: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(0usize);
        fsquare(t0.1, x3.1);
        fdifference(t0.1, t0.1, x21.1);
        reduce_513(t0.1);
        reduce(t0.1);
        let z1: bool = is_0(t0.1);
        if z1 == falsebool
        { falsebool }
        else
        {
          let x3: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(0usize);
          let t0: (&mut [u64], &mut [u64]) = t0.1.split_at_mut(0usize);
          reduce(x3.1);
          let x0: u64 = x3.1[0u32 as usize];
          let x0: u64 = x0 & 1u64;
          if ! x0 == sign
          {
            t0.1[0u32 as usize] = 0u64;
            ();
            t0.1[1u32 as usize] = 0u64;
            ();
            t0.1[2u32 as usize] = 0u64;
            ();
            t0.1[3u32 as usize] = 0u64;
            ();
            t0.1[4u32 as usize] = 0u64;
            ();
            fdifference(x3.1, t0.1, x3.1);
            reduce_513(x3.1);
            reduce(x3.1)
          };
          (x[0u32 as usize..0u32 as usize + 5u32 as usize]).copy_from_slice(
            &x3.1[0u32 as usize..0u32 as usize + 5u32 as usize]
          );
          ();
          truebool
        }
      }
    };
  let res: bool = res;
  res
}

pub fn point_decompress(out: &mut [u64], s: &mut [u8]) -> bool
{
  let mut tmp: [u64; 10] = [0u64; 10u32 as usize];
  let y: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
  let x: (&mut [u64], &mut [u64]) = y.1.split_at_mut(5usize);
  let s31: u8 = s[31u32 as usize];
  let z: u8 = s31.wrapping_shr(7u32);
  let sign: u64 = z as u64;
  load_51(x.0, s);
  let z: bool = recover_x(x.1, x.0, sign);
  let res: bool =
    if z == falsebool
    { falsebool }
    else
    {
      let outx: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
      let outy: (&mut [u64], &mut [u64]) = outx.1.split_at_mut(5usize);
      let outz: (&mut [u64], &mut [u64]) = outy.1.split_at_mut(5usize);
      let outt: (&mut [u64], &mut [u64]) = outz.1.split_at_mut(5usize);
      (outy.0[0u32 as usize..0u32 as usize + 5u32 as usize]).copy_from_slice(
        &x.1[0u32 as usize..0u32 as usize + 5u32 as usize]
      );
      ();
      (outz.0[0u32 as usize..0u32 as usize + 5u32 as usize]).copy_from_slice(
        &x.0[0u32 as usize..0u32 as usize + 5u32 as usize]
      );
      ();
      outt.0[0u32 as usize] = 1u64;
      ();
      outt.0[1u32 as usize] = 0u64;
      ();
      outt.0[2u32 as usize] = 0u64;
      ();
      outt.0[3u32 as usize] = 0u64;
      ();
      outt.0[4u32 as usize] = 0u64;
      ();
      fmul(outt.1, x.1, x.0);
      truebool
    };
  let res: bool = res;
  res
}

pub fn point_compress(z: &mut [u8], p: &mut [u64]) -> ()
{
  let mut tmp: [u64; 15] = [0u64; 15u32 as usize];
  let x: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(5usize);
  let out: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
  let zinv1: (&mut [u64], &mut [u64]) = x.0.split_at_mut(0usize);
  let x1: (&mut [u64], &mut [u64]) = out.0.split_at_mut(0usize);
  let out1: (&mut [u64], &mut [u64]) = out.1.split_at_mut(0usize);
  let px: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
  let py: (&mut [u64], &mut [u64]) = px.1.split_at_mut(5usize);
  let pz: (&mut [u64], &mut [u64]) = py.1.split_at_mut(5usize);
  inverse(zinv1.1, pz.1);
  fmul(x1.1, py.0, zinv1.1);
  reduce(x1.1);
  fmul(out1.1, pz.0, zinv1.1);
  reduce_513(out1.1);
  let x0: u64 = x1.0[0u32 as usize];
  let b: u64 = x0 & 1u64;
  store_51(z, out1.0);
  let xbyte: u8 = b as u8;
  let o31: u8 = z[31u32 as usize];
  z[31u32 as usize] = o31.wrapping_add(xbyte.wrapping_shl(7u32))
}

fn barrett_reduction(z: &mut [u64], t: &mut [u64]) -> ()
{
  let t0: u64 = t[0u32 as usize];
  let t1: u64 = t[1u32 as usize];
  let t2: u64 = t[2u32 as usize];
  let t3: u64 = t[3u32 as usize];
  let t4: u64 = t[4u32 as usize];
  let t5: u64 = t[5u32 as usize];
  let t6: u64 = t[6u32 as usize];
  let t7: u64 = t[7u32 as usize];
  let t8: u64 = t[8u32 as usize];
  let t9: u64 = t[9u32 as usize];
  let m0: u64 = 0x12631a5cf5d3edu64;
  let m1: u64 = 0xf9dea2f79cd658u64;
  let m2: u64 = 0x000000000014deu64;
  let m3: u64 = 0x00000000000000u64;
  let m4: u64 = 0x00000010000000u64;
  let m0: u64 = m0;
  let m1: u64 = m1;
  let m2: u64 = m2;
  let m3: u64 = m3;
  let m4: u64 = m4;
  let m01: u64 = 0x9ce5a30a2c131bu64;
  let m11: u64 = 0x215d086329a7edu64;
  let m21: u64 = 0xffffffffeb2106u64;
  let m31: u64 = 0xffffffffffffffu64;
  let m41: u64 = 0x00000fffffffffu64;
  let mu0: u64 = m01;
  let mu1: u64 = m11;
  let mu2: u64 = m21;
  let mu3: u64 = m31;
  let mu4: u64 = m41;
  let y': u64 = (t5 & 0xffffffu64).wrapping_shl(32u32);
  let x': u64 = t4.wrapping_shr(24u32);
  let z0: u64 = x' | y';
  let y': u64 = (t6 & 0xffffffu64).wrapping_shl(32u32);
  let x': u64 = t5.wrapping_shr(24u32);
  let z1: u64 = x' | y';
  let y': u64 = (t7 & 0xffffffu64).wrapping_shl(32u32);
  let x': u64 = t6.wrapping_shr(24u32);
  let z2: u64 = x' | y';
  let y': u64 = (t8 & 0xffffffu64).wrapping_shl(32u32);
  let x': u64 = t7.wrapping_shr(24u32);
  let z3: u64 = x' | y';
  let y': u64 = (t9 & 0xffffffu64).wrapping_shl(32u32);
  let x': u64 = t8.wrapping_shr(24u32);
  let z4: u64 = x' | y';
  let q0: u64 = z0;
  let q1: u64 = z1;
  let q2: u64 = z2;
  let q3: u64 = z3;
  let q4: u64 = z4;
  let xy00: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu0);
  let xy01: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu1);
  let xy02: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu2);
  let xy03: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu3);
  let xy04: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q0, mu4);
  let xy10: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu0);
  let xy11: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu1);
  let xy12: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu2);
  let xy13: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu3);
  let xy14: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q1, mu4);
  let xy20: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu0);
  let xy21: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu1);
  let xy22: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu2);
  let xy23: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu3);
  let xy24: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q2, mu4);
  let xy30: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu0);
  let xy31: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu1);
  let xy32: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu2);
  let xy33: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu3);
  let xy34: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q3, mu4);
  let xy40: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu0);
  let xy41: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu1);
  let xy42: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu2);
  let xy43: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu3);
  let xy44: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(q4, mu4);
  let z0: crate::fstar::uint128::uint128 = xy00;
  let z1: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy01, xy10);
  let z2: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy02, xy11), xy20);
  let z3: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(
      crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy03, xy12), xy21),
      xy30
    );
  let z4: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy04, xy13), xy22),
        xy31
      ),
      xy40
    );
  let z5: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(
      crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy14, xy23), xy32),
      xy41
    );
  let z6: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy24, xy33), xy42);
  let z7: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy34, xy43);
  let z8: crate::fstar::uint128::uint128 = xy44;
  let carry: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(z0, 56u32);
  let c0: crate::fstar::uint128::uint128 = carry;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z1, c0), 56u32);
  let c1: crate::fstar::uint128::uint128 = carry;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z2, c1), 56u32);
  let c2: crate::fstar::uint128::uint128 = carry;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z3, c2), 56u32);
  let c3: crate::fstar::uint128::uint128 = carry;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z4, c3), 56u32);
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z4, c3))
    &
    0xffffffffffffffu64;
  let c4: crate::fstar::uint128::uint128 = carry;
  let t41: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z5, c4), 56u32);
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z5, c4))
    &
    0xffffffffffffffu64;
  let c5: crate::fstar::uint128::uint128 = carry;
  let t51: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z6, c5), 56u32);
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z6, c5))
    &
    0xffffffffffffffu64;
  let c6: crate::fstar::uint128::uint128 = carry;
  let t61: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z7, c6), 56u32);
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z7, c6))
    &
    0xffffffffffffffu64;
  let c7: crate::fstar::uint128::uint128 = carry;
  let t71: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z8, c7), 56u32);
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z8, c7))
    &
    0xffffffffffffffu64;
  let c8: crate::fstar::uint128::uint128 = carry;
  let t81: u64 = t10;
  let t91: u64 = crate::fstar::uint128::uint128_to_uint64(c8);
  let qmu4': u64 = t41;
  let qmu5': u64 = t51;
  let qmu6': u64 = t61;
  let qmu7': u64 = t71;
  let qmu8': u64 = t81;
  let qmu9': u64 = t91;
  let y': u64 = (qmu5' & 0xffffffffffu64).wrapping_shl(16u32);
  let x': u64 = qmu4'.wrapping_shr(40u32);
  let z0: u64 = x' | y';
  let y': u64 = (qmu6' & 0xffffffffffu64).wrapping_shl(16u32);
  let x': u64 = qmu5'.wrapping_shr(40u32);
  let z1: u64 = x' | y';
  let y': u64 = (qmu7' & 0xffffffffffu64).wrapping_shl(16u32);
  let x': u64 = qmu6'.wrapping_shr(40u32);
  let z2: u64 = x' | y';
  let y': u64 = (qmu8' & 0xffffffffffu64).wrapping_shl(16u32);
  let x': u64 = qmu7'.wrapping_shr(40u32);
  let z3: u64 = x' | y';
  let y': u64 = (qmu9' & 0xffffffffffu64).wrapping_shl(16u32);
  let x': u64 = qmu8'.wrapping_shr(40u32);
  let z4: u64 = x' | y';
  let qdiv0: u64 = z0;
  let qdiv1: u64 = z1;
  let qdiv2: u64 = z2;
  let qdiv3: u64 = z3;
  let qdiv4: u64 = z4;
  let r0: u64 = t0;
  let r1: u64 = t1;
  let r2: u64 = t2;
  let r3: u64 = t3;
  let r4: u64 = t4 & 0xffffffffffu64;
  let xy00: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m0);
  let xy01: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m1);
  let xy02: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m2);
  let xy03: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m3);
  let xy04: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv0, m4);
  let xy10: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m0);
  let xy11: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m1);
  let xy12: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m2);
  let xy13: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv1, m3);
  let xy20: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv2, m0);
  let xy21: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv2, m1);
  let xy22: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv2, m2);
  let xy30: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv3, m0);
  let xy31: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv3, m1);
  let xy40: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(qdiv4, m0);
  let carry: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(xy00, 56u32);
  let t10: u64 = crate::fstar::uint128::uint128_to_uint64(xy00) & 0xffffffffffffffu64;
  let c0: crate::fstar::uint128::uint128 = carry;
  let t01: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(
      crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy01, xy10), c0),
      56u32
    );
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(
      crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy01, xy10), c0)
    )
    &
    0xffffffffffffffu64;
  let c1: crate::fstar::uint128::uint128 = carry;
  let t11: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy02, xy11), xy20),
        c1
      ),
      56u32
    );
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy02, xy11), xy20),
        c1
      )
    )
    &
    0xffffffffffffffu64;
  let c2: crate::fstar::uint128::uint128 = carry;
  let t21: u64 = t10;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(
          crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy03, xy12), xy21),
          xy30
        ),
        c2
      ),
      56u32
    );
  let t10: u64 =
    crate::fstar::uint128::uint128_to_uint64(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(
          crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy03, xy12), xy21),
          xy30
        ),
        c2
      )
    )
    &
    0xffffffffffffffu64;
  let c3: crate::fstar::uint128::uint128 = carry;
  let t31: u64 = t10;
  let t41: u64 =
    crate::fstar::uint128::uint128_to_uint64(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(
          crate::fstar::uint128::add_mod(
            crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy04, xy13), xy22),
            xy31
          ),
          xy40
        ),
        c3
      )
    )
    &
    0xffffffffffu64;
  let qmul0: u64 = t01;
  let qmul1: u64 = t11;
  let qmul2: u64 = t21;
  let qmul3: u64 = t31;
  let qmul4: u64 = t41;
  let b: u64 = r0.wrapping_sub(qmul0).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(r0).wrapping_sub(qmul0);
  let c1: u64 = b;
  let t01: u64 = t10;
  let b: u64 = r1.wrapping_sub(qmul1.wrapping_add(c1)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(r1).wrapping_sub(qmul1.wrapping_add(c1));
  let c2: u64 = b;
  let t11: u64 = t10;
  let b: u64 = r2.wrapping_sub(qmul2.wrapping_add(c2)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(r2).wrapping_sub(qmul2.wrapping_add(c2));
  let c3: u64 = b;
  let t21: u64 = t10;
  let b: u64 = r3.wrapping_sub(qmul3.wrapping_add(c3)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(r3).wrapping_sub(qmul3.wrapping_add(c3));
  let c4: u64 = b;
  let t31: u64 = t10;
  let b: u64 = r4.wrapping_sub(qmul4.wrapping_add(c4)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(40u32).wrapping_add(r4).wrapping_sub(qmul4.wrapping_add(c4));
  let t41: u64 = t10;
  let s0: u64 = t01;
  let s1: u64 = t11;
  let s2: u64 = t21;
  let s3: u64 = t31;
  let s4: u64 = t41;
  let m01: u64 = 0x12631a5cf5d3edu64;
  let m11: u64 = 0xf9dea2f79cd658u64;
  let m21: u64 = 0x000000000014deu64;
  let m31: u64 = 0x00000000000000u64;
  let m41: u64 = 0x00000010000000u64;
  let y0: u64 = m01;
  let y1: u64 = m11;
  let y2: u64 = m21;
  let y3: u64 = m31;
  let y4: u64 = m41;
  let b: u64 = s0.wrapping_sub(y0).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(s0).wrapping_sub(y0);
  let b0: u64 = b;
  let t01: u64 = t10;
  let b: u64 = s1.wrapping_sub(y1.wrapping_add(b0)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(s1).wrapping_sub(y1.wrapping_add(b0));
  let b1: u64 = b;
  let t11: u64 = t10;
  let b: u64 = s2.wrapping_sub(y2.wrapping_add(b1)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(s2).wrapping_sub(y2.wrapping_add(b1));
  let b2: u64 = b;
  let t21: u64 = t10;
  let b: u64 = s3.wrapping_sub(y3.wrapping_add(b2)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(s3).wrapping_sub(y3.wrapping_add(b2));
  let b3: u64 = b;
  let t31: u64 = t10;
  let b: u64 = s4.wrapping_sub(y4.wrapping_add(b3)).wrapping_shr(63u32);
  let t10: u64 = b.wrapping_shl(56u32).wrapping_add(s4).wrapping_sub(y4.wrapping_add(b3));
  let b4: u64 = b;
  let t41: u64 = t10;
  let mask: u64 = b4.wrapping_sub(1u64);
  let z0: u64 = s0 ^ mask & (s0 ^ t01);
  let z1: u64 = s1 ^ mask & (s1 ^ t11);
  let z2: u64 = s2 ^ mask & (s2 ^ t21);
  let z3: u64 = s3 ^ mask & (s3 ^ t31);
  let z4: u64 = s4 ^ mask & (s4 ^ t41);
  let z0: u64 = z0;
  let z1: u64 = z1;
  let z2: u64 = z2;
  let z3: u64 = z3;
  let z4: u64 = z4;
  let o0: u64 = z0;
  let o1: u64 = z1;
  let o2: u64 = z2;
  let o3: u64 = z3;
  let o4: u64 = z4;
  let z0: u64 = o0;
  let z1: u64 = o1;
  let z2: u64 = o2;
  let z3: u64 = o3;
  let z4: u64 = o4;
  z[0u32 as usize] = z0;
  z[1u32 as usize] = z1;
  z[2u32 as usize] = z2;
  z[3u32 as usize] = z3;
  z[4u32 as usize] = z4
}

fn mul_modq(out: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
  let mut tmp: [u64; 10] = [0u64; 10u32 as usize];
  let x0: u64 = x[0u32 as usize];
  let x1: u64 = x[1u32 as usize];
  let x2: u64 = x[2u32 as usize];
  let x3: u64 = x[3u32 as usize];
  let x4: u64 = x[4u32 as usize];
  let y0: u64 = y[0u32 as usize];
  let y1: u64 = y[1u32 as usize];
  let y2: u64 = y[2u32 as usize];
  let y3: u64 = y[3u32 as usize];
  let y4: u64 = y[4u32 as usize];
  let xy00: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y0);
  let xy01: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y1);
  let xy02: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y2);
  let xy03: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y3);
  let xy04: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x0, y4);
  let xy10: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y0);
  let xy11: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y1);
  let xy12: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y2);
  let xy13: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y3);
  let xy14: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x1, y4);
  let xy20: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y0);
  let xy21: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y1);
  let xy22: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y2);
  let xy23: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y3);
  let xy24: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x2, y4);
  let xy30: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y0);
  let xy31: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y1);
  let xy32: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y2);
  let xy33: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y3);
  let xy34: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x3, y4);
  let xy40: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y0);
  let xy41: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y1);
  let xy42: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y2);
  let xy43: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y3);
  let xy44: crate::fstar::uint128::uint128 = crate::fstar::uint128::mul_wide(x4, y4);
  let z0: crate::fstar::uint128::uint128 = xy00;
  let z1: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy01, xy10);
  let z2: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy02, xy11), xy20);
  let z3: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(
      crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy03, xy12), xy21),
      xy30
    );
  let z4: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(
      crate::fstar::uint128::add_mod(
        crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy04, xy13), xy22),
        xy31
      ),
      xy40
    );
  let z5: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(
      crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy14, xy23), xy32),
      xy41
    );
  let z6: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::add_mod(crate::fstar::uint128::add_mod(xy24, xy33), xy42);
  let z7: crate::fstar::uint128::uint128 = crate::fstar::uint128::add_mod(xy34, xy43);
  let z8: crate::fstar::uint128::uint128 = xy44;
  let carry: crate::fstar::uint128::uint128 = crate::fstar::uint128::shift_right(z0, 56u32);
  let t: u64 = crate::fstar::uint128::uint128_to_uint64(z0) & 0xffffffffffffffu64;
  let c0: crate::fstar::uint128::uint128 = carry;
  let t0: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z1, c0), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z1, c0))
    &
    0xffffffffffffffu64;
  let c1: crate::fstar::uint128::uint128 = carry;
  let t1: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z2, c1), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z2, c1))
    &
    0xffffffffffffffu64;
  let c2: crate::fstar::uint128::uint128 = carry;
  let t2: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z3, c2), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z3, c2))
    &
    0xffffffffffffffu64;
  let c3: crate::fstar::uint128::uint128 = carry;
  let t3: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z4, c3), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z4, c3))
    &
    0xffffffffffffffu64;
  let c4: crate::fstar::uint128::uint128 = carry;
  let t4: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z5, c4), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z5, c4))
    &
    0xffffffffffffffu64;
  let c5: crate::fstar::uint128::uint128 = carry;
  let t5: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z6, c5), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z6, c5))
    &
    0xffffffffffffffu64;
  let c6: crate::fstar::uint128::uint128 = carry;
  let t6: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z7, c6), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z7, c6))
    &
    0xffffffffffffffu64;
  let c7: crate::fstar::uint128::uint128 = carry;
  let t7: u64 = t;
  let carry: crate::fstar::uint128::uint128 =
    crate::fstar::uint128::shift_right(crate::fstar::uint128::add_mod(z8, c7), 56u32);
  let t: u64 =
    crate::fstar::uint128::uint128_to_uint64(crate::fstar::uint128::add_mod(z8, c7))
    &
    0xffffffffffffffu64;
  let c8: crate::fstar::uint128::uint128 = carry;
  let t8: u64 = t;
  let t9: u64 = crate::fstar::uint128::uint128_to_uint64(c8);
  let z0: u64 = t0;
  let z1: u64 = t1;
  let z2: u64 = t2;
  let z3: u64 = t3;
  let z4: u64 = t4;
  let z5: u64 = t5;
  let z6: u64 = t6;
  let z7: u64 = t7;
  let z8: u64 = t8;
  let z9: u64 = t9;
  (&mut tmp)[0u32 as usize] = z0;
  (&mut tmp)[1u32 as usize] = z1;
  (&mut tmp)[2u32 as usize] = z2;
  (&mut tmp)[3u32 as usize] = z3;
  (&mut tmp)[4u32 as usize] = z4;
  (&mut tmp)[5u32 as usize] = z5;
  (&mut tmp)[6u32 as usize] = z6;
  (&mut tmp)[7u32 as usize] = z7;
  (&mut tmp)[8u32 as usize] = z8;
  (&mut tmp)[9u32 as usize] = z9;
  barrett_reduction(out, &mut tmp)
}

fn add_modq(out: &mut [u64], x: &mut [u64], y: &mut [u64]) -> ()
{
  let x0: u64 = x[0u32 as usize];
  let x1: u64 = x[1u32 as usize];
  let x2: u64 = x[2u32 as usize];
  let x3: u64 = x[3u32 as usize];
  let x4: u64 = x[4u32 as usize];
  let y0: u64 = y[0u32 as usize];
  let y1: u64 = y[1u32 as usize];
  let y2: u64 = y[2u32 as usize];
  let y3: u64 = y[3u32 as usize];
  let y4: u64 = y[4u32 as usize];
  let carry: u64 = x0.wrapping_add(y0).wrapping_shr(56u32);
  let t: u64 = x0.wrapping_add(y0) & 0xffffffffffffffu64;
  let t0: u64 = t;
  let c0: u64 = carry;
  let carry: u64 = x1.wrapping_add(y1).wrapping_add(c0).wrapping_shr(56u32);
  let t: u64 = x1.wrapping_add(y1).wrapping_add(c0) & 0xffffffffffffffu64;
  let t1: u64 = t;
  let c1: u64 = carry;
  let carry: u64 = x2.wrapping_add(y2).wrapping_add(c1).wrapping_shr(56u32);
  let t: u64 = x2.wrapping_add(y2).wrapping_add(c1) & 0xffffffffffffffu64;
  let t2: u64 = t;
  let c2: u64 = carry;
  let carry: u64 = x3.wrapping_add(y3).wrapping_add(c2).wrapping_shr(56u32);
  let t: u64 = x3.wrapping_add(y3).wrapping_add(c2) & 0xffffffffffffffu64;
  let t3: u64 = t;
  let c3: u64 = carry;
  let t4: u64 = x4.wrapping_add(y4).wrapping_add(c3);
  let m0: u64 = 0x12631a5cf5d3edu64;
  let m1: u64 = 0xf9dea2f79cd658u64;
  let m2: u64 = 0x000000000014deu64;
  let m3: u64 = 0x00000000000000u64;
  let m4: u64 = 0x00000010000000u64;
  let y01: u64 = m0;
  let y11: u64 = m1;
  let y21: u64 = m2;
  let y31: u64 = m3;
  let y41: u64 = m4;
  let b: u64 = t0.wrapping_sub(y01).wrapping_shr(63u32);
  let t: u64 = b.wrapping_shl(56u32).wrapping_add(t0).wrapping_sub(y01);
  let b0: u64 = b;
  let t01: u64 = t;
  let b: u64 = t1.wrapping_sub(y11.wrapping_add(b0)).wrapping_shr(63u32);
  let t: u64 = b.wrapping_shl(56u32).wrapping_add(t1).wrapping_sub(y11.wrapping_add(b0));
  let b1: u64 = b;
  let t11: u64 = t;
  let b: u64 = t2.wrapping_sub(y21.wrapping_add(b1)).wrapping_shr(63u32);
  let t: u64 = b.wrapping_shl(56u32).wrapping_add(t2).wrapping_sub(y21.wrapping_add(b1));
  let b2: u64 = b;
  let t21: u64 = t;
  let b: u64 = t3.wrapping_sub(y31.wrapping_add(b2)).wrapping_shr(63u32);
  let t: u64 = b.wrapping_shl(56u32).wrapping_add(t3).wrapping_sub(y31.wrapping_add(b2));
  let b3: u64 = b;
  let t31: u64 = t;
  let b: u64 = t4.wrapping_sub(y41.wrapping_add(b3)).wrapping_shr(63u32);
  let t: u64 = b.wrapping_shl(56u32).wrapping_add(t4).wrapping_sub(y41.wrapping_add(b3));
  let b4: u64 = b;
  let t41: u64 = t;
  let mask: u64 = b4.wrapping_sub(1u64);
  let z0: u64 = t0 ^ mask & (t0 ^ t01);
  let z1: u64 = t1 ^ mask & (t1 ^ t11);
  let z2: u64 = t2 ^ mask & (t2 ^ t21);
  let z3: u64 = t3 ^ mask & (t3 ^ t31);
  let z4: u64 = t4 ^ mask & (t4 ^ t41);
  let z0: u64 = z0;
  let z1: u64 = z1;
  let z2: u64 = z2;
  let z3: u64 = z3;
  let z4: u64 = z4;
  let o0: u64 = z0;
  let o1: u64 = z1;
  let o2: u64 = z2;
  let o3: u64 = z3;
  let o4: u64 = z4;
  let z0: u64 = o0;
  let z1: u64 = o1;
  let z2: u64 = o2;
  let z3: u64 = o3;
  let z4: u64 = o4;
  out[0u32 as usize] = z0;
  out[1u32 as usize] = z1;
  out[2u32 as usize] = z2;
  out[3u32 as usize] = z3;
  out[4u32 as usize] = z4
}

fn gte_q(s: &mut [u64]) -> bool
{
  let s0: u64 = s[0u32 as usize];
  let s1: u64 = s[1u32 as usize];
  let s2: u64 = s[2u32 as usize];
  let s3: u64 = s[3u32 as usize];
  let s4: u64 = s[4u32 as usize];
  if s4 > 0x00000010000000u64
  { truebool }
  else
  if s4 < 0x00000010000000u64
  { falsebool }
  else
  if s3 > 0x00000000000000u64
  { truebool }
  else
  if s2 > 0x000000000014deu64
  { truebool }
  else
  if s2 < 0x000000000014deu64
  { falsebool }
  else
  if s1 > 0xf9dea2f79cd658u64
  { truebool }
  else
  if s1 < 0xf9dea2f79cd658u64
  { falsebool }
  else
  if s0 >= 0x12631a5cf5d3edu64 { truebool } else { falsebool }
}

fn eq(a: &mut [u64], b: &mut [u64]) -> bool
{
  let a0: u64 = a[0u32 as usize];
  let a1: u64 = a[1u32 as usize];
  let a2: u64 = a[2u32 as usize];
  let a3: u64 = a[3u32 as usize];
  let a4: u64 = a[4u32 as usize];
  let b0: u64 = b[0u32 as usize];
  let b1: u64 = b[1u32 as usize];
  let b2: u64 = b[2u32 as usize];
  let b3: u64 = b[3u32 as usize];
  let b4: u64 = b[4u32 as usize];
  a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4
}

pub fn point_equal(p: &mut [u64], q: &mut [u64]) -> bool
{
  let mut tmp: [u64; 20] = [0u64; 20u32 as usize];
  let pxqz: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
  let qxpz: (&mut [u64], &mut [u64]) = pxqz.1.split_at_mut(5usize);
  fmul(qxpz.0, &mut p[0u32 as usize..], &mut q[10u32 as usize..]);
  reduce(qxpz.0);
  fmul(qxpz.1, &mut q[0u32 as usize..], &mut p[10u32 as usize..]);
  reduce(qxpz.1);
  let b: bool = eq(qxpz.0, qxpz.1);
  if b
  {
    let pyqz: (&mut [u64], &mut [u64]) = qxpz.1.split_at_mut(5usize);
    let qypz: (&mut [u64], &mut [u64]) = pyqz.1.split_at_mut(5usize);
    fmul(qypz.0, &mut p[5u32 as usize..], &mut q[10u32 as usize..]);
    reduce(qypz.0);
    fmul(qypz.1, &mut q[5u32 as usize..], &mut p[10u32 as usize..]);
    reduce(qypz.1);
    eq(qypz.0, qypz.1)
  }
  else
  { falsebool }
}

pub fn point_negate(p: &mut [u64], out: &mut [u64]) -> ()
{
  let mut zero: [u64; 5] = [0u64; 5u32 as usize];
  (&mut zero)[0u32 as usize] = 0u64;
  (&mut zero)[1u32 as usize] = 0u64;
  (&mut zero)[2u32 as usize] = 0u64;
  (&mut zero)[3u32 as usize] = 0u64;
  (&mut zero)[4u32 as usize] = 0u64;
  let x: (&mut [u64], &mut [u64]) = p.split_at_mut(0usize);
  let y: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
  let z: (&mut [u64], &mut [u64]) = y.1.split_at_mut(5usize);
  let t: (&mut [u64], &mut [u64]) = z.1.split_at_mut(5usize);
  let x1: (&mut [u64], &mut [u64]) = out.split_at_mut(0usize);
  let y1: (&mut [u64], &mut [u64]) = x1.1.split_at_mut(5usize);
  let z1: (&mut [u64], &mut [u64]) = y1.1.split_at_mut(5usize);
  let t1: (&mut [u64], &mut [u64]) = z1.1.split_at_mut(5usize);
  fdifference(y1.0, &mut zero, y.0);
  reduce_513(y1.0);
  (z1.0[0u32 as usize..0u32 as usize + 5u32 as usize]).copy_from_slice(
    &z.0[0u32 as usize..0u32 as usize + 5u32 as usize]
  );
  (t1.0[0u32 as usize..0u32 as usize + 5u32 as usize]).copy_from_slice(
    &t.0[0u32 as usize..0u32 as usize + 5u32 as usize]
  );
  fdifference(t1.1, &mut zero, t.1);
  reduce_513(t1.1)
}

fn precomp_get_consttime(table: &[u64], bits_l: u64, tmp: &mut [u64]) -> ()
{
  (tmp[0u32 as usize..0u32 as usize + 20u32 as usize]).copy_from_slice(
    &(&mut table[0u32 as usize..] as &mut [u64])[0u32 as usize..0u32 as usize + 20u32 as usize]
  );
  for i in 0u32..15u32
  {
    let c: u64 = crate::fstar::uint64::eq_mask(bits_l, i.wrapping_add(1u32) as u64);
    let res_j: (&[u64], &[u64]) =
      table.split_at_mut((i.wrapping_add(1u32).wrapping_mul(20u32) as usize).wrapping_add(0usize));
    for i in 0u32..20u32
    {
      let os: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
      let x: u64 = c & res_j.1[i as usize] | ! c & os.1[i as usize];
      os.1[i as usize] = x
    }
  }
}

fn point_negate_mul_double_g_vartime(
  out: &mut [u64],
  scalar1: &mut [u8],
  scalar2: &mut [u8],
  q2: &mut [u64]
) ->
  ()
{
  let mut q2_neg: [u64; 20] = [0u64; 20u32 as usize];
  point_negate(q2, &mut q2_neg);
  crate::hacl::impl::ed25519::ladder::point_mul_g_double_vartime(
    out,
    scalar1,
    scalar2,
    &mut q2_neg
  )
}

fn store_56(out: &mut [u8], b: &mut [u64]) -> ()
{
  let b0: u64 = b[0u32 as usize];
  let b1: u64 = b[1u32 as usize];
  let b2: u64 = b[2u32 as usize];
  let b3: u64 = b[3u32 as usize];
  let b4: u64 = b[4u32 as usize];
  let b4': u32 = b4 as u32;
  let b8: (&mut [u8], &mut [u8]) = out.split_at_mut(0usize);
  crate::lowstar::endianness::store64_le(b8.1, b0);
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  crate::lowstar::endianness::store64_le(b8.1, b1);
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  crate::lowstar::endianness::store64_le(b8.1, b2);
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  crate::lowstar::endianness::store64_le(b8.1, b3);
  crate::lowstar::endianness::store32_le(&mut b8.0[28u32 as usize..], b4')
}

fn load_64_bytes(out: &mut [u64], b: &mut [u8]) -> ()
{
  let b8: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b0: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b1: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b2: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b3: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b4: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b5: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b6: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b7: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b8: u64 = z & 0xffffffffffffffu64;
  let b63: u8 = b8.0[63u32 as usize];
  let b9: u64 = b63 as u64;
  out[0u32 as usize] = b0;
  out[1u32 as usize] = b1;
  out[2u32 as usize] = b2;
  out[3u32 as usize] = b3;
  out[4u32 as usize] = b4;
  out[5u32 as usize] = b5;
  out[6u32 as usize] = b6;
  out[7u32 as usize] = b7;
  out[8u32 as usize] = b8;
  out[9u32 as usize] = b9
}

fn load_32_bytes(out: &mut [u64], b: &mut [u8]) -> ()
{
  let b8: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b0: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b1: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b2: u64 = z & 0xffffffffffffffu64;
  let b8: (&mut [u8], &mut [u8]) = b8.1.split_at_mut(7usize);
  let u: u64 = crate::lowstar::endianness::load64_le(b8.1);
  let z: u64 = u;
  let b3: u64 = z & 0xffffffffffffffu64;
  let u: u32 = crate::lowstar::endianness::load32_le(&mut b8.0[28u32 as usize..]);
  let b4: u32 = u;
  let b41: u64 = b4 as u64;
  out[0u32 as usize] = b0;
  out[1u32 as usize] = b1;
  out[2u32 as usize] = b2;
  out[3u32 as usize] = b3;
  out[4u32 as usize] = b41
}

fn sha512_modq_pre(out: &mut [u64], prefix: &mut [u8], len: u32, input: &mut [u8]) -> ()
{
  let mut tmp: [u64; 10] = [0u64; 10u32 as usize];
  let mut hash: [u8; 64] = [0u8; 64u32 as usize];
  crate::hacl::impl::sha512::modq::sha512_pre_msg(&mut hash, prefix, len, input);
  load_64_bytes(&mut tmp, &mut hash);
  barrett_reduction(out, &mut tmp)
}

fn sha512_modq_pre_pre2(
  out: &mut [u64],
  prefix: &mut [u8],
  prefix2: &mut [u8],
  len: u32,
  input: &mut [u8]
) ->
  ()
{
  let mut tmp: [u64; 10] = [0u64; 10u32 as usize];
  let mut hash: [u8; 64] = [0u8; 64u32 as usize];
  crate::hacl::impl::sha512::modq::sha512_pre_pre2_msg(&mut hash, prefix, prefix2, len, input);
  load_64_bytes(&mut tmp, &mut hash);
  barrett_reduction(out, &mut tmp)
}

fn point_mul_g_compress(out: &mut [u8], s: &mut [u8]) -> ()
{
  let mut tmp: [u64; 20] = [0u64; 20u32 as usize];
  crate::hacl::impl::ed25519::ladder::point_mul_g(&mut tmp, s);
  point_compress(out, &mut tmp)
}

fn secret_expand(expanded: &mut [u8], secret: &mut [u8]) -> ()
{
  crate::hacl::hash_sha2::hash_512(secret, 32u32, expanded);
  let h_low: (&mut [u8], &mut [u8]) = expanded.split_at_mut(0usize);
  let h_low0: u8 = h_low.1[0u32 as usize];
  let h_low31: u8 = h_low.1[31u32 as usize];
  h_low.1[0u32 as usize] = h_low0 & 0xf8u8;
  h_low.1[31u32 as usize] = h_low31 & 127u8 | 64u8
}

pub fn secret_to_public(public_key: &mut [u8], private_key: &mut [u8]) -> ()
{
  let mut expanded_secret: [u8; 64] = [0u8; 64u32 as usize];
  secret_expand(&mut expanded_secret, private_key);
  let a: (&mut [u8], &mut [u8]) = (&mut expanded_secret).split_at_mut(0usize);
  point_mul_g_compress(public_key, a.1)
}

pub fn expand_keys(expanded_keys: &mut [u8], private_key: &mut [u8]) -> ()
{
  let public_key: (&mut [u8], &mut [u8]) = expanded_keys.split_at_mut(0usize);
  let s_prefix: (&mut [u8], &mut [u8]) = public_key.1.split_at_mut(32usize);
  let s: (&mut [u8], &mut [u8]) = s_prefix.1.split_at_mut(0usize);
  secret_expand(s.0, private_key);
  point_mul_g_compress(s_prefix.0, s.1)
}

pub fn sign_expanded(
  signature: &mut [u8],
  expanded_keys: &mut [u8],
  msg_len: u32,
  msg: &mut [u8]
) ->
  ()
{
  let rs: (&mut [u8], &mut [u8]) = signature.split_at_mut(0usize);
  let ss: (&mut [u8], &mut [u8]) = rs.1.split_at_mut(32usize);
  let mut rq: [u64; 5] = [0u64; 5u32 as usize];
  let mut hq: [u64; 5] = [0u64; 5u32 as usize];
  let mut rb: [u8; 32] = [0u8; 32u32 as usize];
  let public_key: (&mut [u8], &mut [u8]) = expanded_keys.split_at_mut(0usize);
  let s: (&mut [u8], &mut [u8]) = public_key.1.split_at_mut(32usize);
  let prefix: (&mut [u8], &mut [u8]) = s.1.split_at_mut(32usize);
  sha512_modq_pre(&mut rq, prefix.1, msg_len, msg);
  store_56(&mut rb, &mut rq);
  point_mul_g_compress(ss.0, &mut rb);
  sha512_modq_pre_pre2(&mut hq, ss.0, s.0, msg_len, msg);
  let mut aq: [u64; 5] = [0u64; 5u32 as usize];
  load_32_bytes(&mut aq, prefix.0);
  mul_modq(&mut aq, &mut hq, &mut aq);
  add_modq(&mut aq, &mut rq, &mut aq);
  store_56(ss.1, &mut aq)
}

pub fn sign(signature: &mut [u8], private_key: &mut [u8], msg_len: u32, msg: &mut [u8]) -> ()
{
  let mut expanded_keys: [u8; 96] = [0u8; 96u32 as usize];
  expand_keys(&mut expanded_keys, private_key);
  sign_expanded(signature, &mut expanded_keys, msg_len, msg)
}

pub fn verify(public_key: &mut [u8], msg_len: u32, msg: &mut [u8], signature: &mut [u8]) ->
  bool
{
  let mut a': [u64; 20] = [0u64; 20u32 as usize];
  let b: bool = point_decompress(&mut a', public_key);
  if b
  {
    let mut r': [u64; 20] = [0u64; 20u32 as usize];
    let rs: (&mut [u8], &mut [u8]) = signature.split_at_mut(0usize);
    let b': bool = point_decompress(&mut r', rs.1);
    if b'
    {
      let mut hb: [u8; 32] = [0u8; 32u32 as usize];
      let rs1: (&mut [u8], &mut [u8]) = rs.1.split_at_mut(0usize);
      let sb: (&mut [u8], &mut [u8]) = rs1.1.split_at_mut(32usize);
      let mut tmp: [u64; 5] = [0u64; 5u32 as usize];
      load_32_bytes(&mut tmp, sb.1);
      let b1: bool = gte_q(&mut tmp);
      let b1: bool = b1;
      if b1
      { falsebool }
      else
      {
        let mut tmp: [u64; 5] = [0u64; 5u32 as usize];
        sha512_modq_pre_pre2(&mut tmp, sb.0, public_key, msg_len, msg);
        store_56(&mut hb, &mut tmp);
        let mut exp_d: [u64; 20] = [0u64; 20u32 as usize];
        point_negate_mul_double_g_vartime(&mut exp_d, sb.1, &mut hb, &mut a');
        let b2: bool = point_equal(&mut exp_d, &mut r');
        b2
      }
    }
    else
    { falsebool }
  }
  else
  { falsebool }
}