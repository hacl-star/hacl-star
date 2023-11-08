pub fn add(a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{
  let mut c: u32 = 0u32;
  for i in 0u32..32u32
  {
    let t1: u32 = a[4u32.wrapping_mul(i) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i) as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1)
  };
  for i in 128u32..128u32
  {
    let t1: u32 = a[i as usize];
    let t2: u32 = b[i as usize];
    let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut((i as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1)
  };
  c
}

pub fn sub(a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{
  let mut c: u32 = 0u32;
  for i in 0u32..32u32
  {
    let t1: u32 = a[4u32.wrapping_mul(i) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i) as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1)
  };
  for i in 128u32..128u32
  {
    let t1: u32 = a[i as usize];
    let t2: u32 = b[i as usize];
    let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut((i as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1)
  };
  c
}

pub fn add_mod(n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{
  let mut c: u32 = 0u32;
  for i in 0u32..32u32
  {
    let t1: u32 = a[4u32.wrapping_mul(i) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i) as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      res.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1);
    let t1: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let t2: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1)
  };
  for i in 128u32..128u32
  {
    let t1: u32 = a[i as usize];
    let t2: u32 = b[i as usize];
    let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut((i as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::add_carry_u32(c, t1, t2, res_i.1)
  };
  let c0: u32 = c;
  let mut tmp: [u32; 128] = [0u32; 128u32 as usize];
  let mut c: u32 = 0u32;
  for i in 0u32..32u32
  {
    let t1: u32 = res[4u32.wrapping_mul(i) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i) as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      (&mut tmp).split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
    let t1: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
    let t1: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
    let t1: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1)
  };
  for i in 128u32..128u32
  {
    let t1: u32 = res[i as usize];
    let t2: u32 = n[i as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      (&mut tmp).split_at_mut((i as usize).wrapping_add(0usize));
    c = crate::lib::inttypes::intrinsics::sub_borrow_u32(c, t1, t2, res_i.1)
  };
  let c1: u32 = c;
  let c: u32 = c0.wrapping_sub(c1);
  for i in 0u32..128u32
  {
    let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
    let x: u32 = c & os.1[i as usize] | ! c & (&mut tmp)[i as usize];
    os.1[i as usize] = x
  }
}

pub fn mul(a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{
  let mut tmp: [u32; 512] = [0u32; 512u32 as usize];
  crate::hacl::bignum::karatsuba::bn_karatsuba_mul_uint32(128u32, a, b, &mut tmp, res)
}

pub fn sqr(a: &mut [u32], res: &mut [u32]) -> ()
{
  let mut tmp: [u32; 512] = [0u32; 512u32 as usize];
  crate::hacl::bignum::karatsuba::bn_karatsuba_sqr_uint32(128u32, a, &mut tmp, res)
}

fn reduction(n: &mut [u32], nInv: u32, c: &mut [u32], res: &mut [u32]) -> ()
{
  let mut c0: u32 = 0u32;
  for i in 0u32..128u32
  {
    let qj: u32 = nInv.wrapping_mul(c[i as usize]);
    let res_j: (&mut [u32], &mut [u32]) = c.split_at_mut((i as usize).wrapping_add(0usize));
    let mut c1: u32 = 0u32;
    for i in 0u32..32u32
    {
      let a_i: u32 = n[4u32.wrapping_mul(i) as usize];
      let res_i: (&mut [u32], &mut [u32]) =
        res_j.1.split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
      c1 = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c1, res_i.1);
      let a_i: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
      let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
      c1 = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c1, res_i.1);
      let a_i: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
      let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
      c1 = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c1, res_i.1);
      let a_i: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
      let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
      c1 = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c1, res_i.1)
    };
    for i in 128u32..128u32
    {
      let a_i: u32 = n[i as usize];
      let res_i: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut((i as usize).wrapping_add(0usize));
      c1 = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c1, res_i.1)
    };
    let r: u32 = c1;
    let c1: u32 = r;
    let resb: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut(128usize);
    let res_j: u32 = resb.0[128u32.wrapping_add(i) as usize];
    c0 = crate::lib::inttypes::intrinsics::add_carry_u32(c0, c1, res_j, resb.1)
  };
  (res[0u32 as usize..0u32 as usize + 128u32 as usize]).copy_from_slice(
    &(&mut c[128u32 as usize..])[0u32 as usize..0u32 as usize + 128u32 as usize]
  );
  let c0: u32 = c0;
  let mut tmp: [u32; 128] = [0u32; 128u32 as usize];
  let mut c1: u32 = 0u32;
  for i in 0u32..32u32
  {
    let t1: u32 = res[4u32.wrapping_mul(i) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i) as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      (&mut tmp).split_at_mut((4u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    c1 = crate::lib::inttypes::intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1);
    let t1: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c1 = crate::lib::inttypes::intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1);
    let t1: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c1 = crate::lib::inttypes::intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1);
    let t1: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let t2: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
    let res_i: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
    c1 = crate::lib::inttypes::intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1)
  };
  for i in 128u32..128u32
  {
    let t1: u32 = res[i as usize];
    let t2: u32 = n[i as usize];
    let res_i: (&mut [u32], &mut [u32]) =
      (&mut tmp).split_at_mut((i as usize).wrapping_add(0usize));
    c1 = crate::lib::inttypes::intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1)
  };
  let c1: u32 = c1;
  let c2: u32 = c0.wrapping_sub(c1);
  for i in 0u32..128u32
  {
    let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
    let x: u32 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
    os.1[i as usize] = x
  }
}

fn from(n: &mut [u32], nInv_u64: u32, aM: &mut [u32], a: &mut [u32]) -> ()
{
  let mut tmp: [u32; 256] = [0u32; 256u32 as usize];
  ((&mut tmp)[0u32 as usize..0u32 as usize + 128u32 as usize]).copy_from_slice(
    &aM[0u32 as usize..0u32 as usize + 128u32 as usize]
  );
  reduction(n, nInv_u64, &mut tmp, a)
}

fn amont_mul(n: &mut [u32], nInv_u64: u32, aM: &mut [u32], bM: &mut [u32], resM: &mut [u32]) ->
  ()
{
  let mut c: [u32; 256] = [0u32; 256u32 as usize];
  let mut tmp: [u32; 512] = [0u32; 512u32 as usize];
  crate::hacl::bignum::karatsuba::bn_karatsuba_mul_uint32(128u32, aM, bM, &mut tmp, &mut c);
  areduction(n, nInv_u64, &mut c, resM)
}

fn amont_sqr(n: &mut [u32], nInv_u64: u32, aM: &mut [u32], resM: &mut [u32]) -> ()
{
  let mut c: [u32; 256] = [0u32; 256u32 as usize];
  let mut tmp: [u32; 512] = [0u32; 512u32 as usize];
  crate::hacl::bignum::karatsuba::bn_karatsuba_sqr_uint32(128u32, aM, &mut tmp, &mut c);
  areduction(n, nInv_u64, &mut c, resM)
}

fn exp_vartime(
  nBits: u32,
  n: &mut [u32],
  a: &mut [u32],
  bBits: u32,
  b: &mut [u32],
  res: &mut [u32]
) ->
  ()
{
  let mut r2: [u32; 128] = [0u32; 128u32 as usize];
  precompr2(nBits, n, &mut r2);
  let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0u32 as usize]);
  exp_vartime_precomp(n, mu, &mut r2, a, bBits, b, res)
}

fn exp_consttime(
  nBits: u32,
  n: &mut [u32],
  a: &mut [u32],
  bBits: u32,
  b: &mut [u32],
  res: &mut [u32]
) ->
  ()
{
  let mut r2: [u32; 128] = [0u32; 128u32 as usize];
  precompr2(nBits, n, &mut r2);
  let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0u32 as usize]);
  exp_consttime_precomp(n, mu, &mut r2, a, bBits, b, res)
}

pub fn lt_mask(a: &mut [u32], b: &mut [u32]) -> u32
{
  let mut acc: u32 = 0u32;
  for i in 0u32..128u32
  {
    let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
    let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], b[i as usize]);
    acc = beq & acc | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
  };
  acc
}

pub fn eq_mask(a: &mut [u32], b: &mut [u32]) -> u32
{
  let mut mask: u32 = 0xFFFFFFFFu32;
  for i in 0u32..128u32
  {
    let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
    mask = uu____0 & mask
  };
  let mask1: u32 = mask;
  mask1
}