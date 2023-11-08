fn poly1305_padded_256(
  ctx: &mut [crate::lib::intvector::intrinsics::vec256],
  len: u32,
  text: &mut [u8]
) ->
  ()
{
  let n: u32 = len.wrapping_div(16u32);
  let r: u32 = len.wrapping_rem(16u32);
  let blocks: (&mut [u8], &mut [u8]) = text.split_at_mut(0usize);
  let rem: (&mut [u8], &mut [u8]) =
    blocks.1.split_at_mut((n.wrapping_mul(16u32) as usize).wrapping_add(0usize));
  let
  pre:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    ctx.split_at_mut(5usize);
  let
  acc:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    pre.0.split_at_mut(0usize);
  let sz_block: u32 = 64u32;
  let len0: u32 = n.wrapping_mul(16u32).wrapping_div(sz_block).wrapping_mul(sz_block);
  let t0: (&mut [u8], &mut [u8]) = rem.0.split_at_mut(0usize);
  if len0 > 0u32
  {
    let bs: u32 = 64u32;
    let text0: (&mut [u8], &mut [u8]) = t0.1.split_at_mut(0usize);
    crate::hacl::poly1305_256::load_acc4(acc.1, text0.1);
    let len1: u32 = len0.wrapping_sub(bs);
    let text1: (&mut [u8], &mut [u8]) = text0.1.split_at_mut((bs as usize).wrapping_add(0usize));
    let nb: u32 = len1.wrapping_div(bs);
    for i in 0u32..i
    {
      let block: (&mut [u8], &mut [u8]) =
        text1.1.split_at_mut((i.wrapping_mul(bs) as usize).wrapping_add(0usize));
      let mut e: [crate::lib::intvector::intrinsics::vec256; 5] =
        [crate::lib::intvector::intrinsics::vec256_zero; 5u32 as usize];
      let lo: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load64_le(&mut block.1[0u32 as usize..]);
      let hi: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load64_le(&mut block.1[32u32 as usize..]);
      let mask26: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64);
      let m0: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_interleave_low128(lo, hi);
      let m1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_interleave_high128(lo, hi);
      let m2: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right(m0, 48u32);
      let m3: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right(m1, 48u32);
      let m4: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_interleave_high64(m0, m1);
      let t01: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_interleave_low64(m0, m1);
      let t3: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_interleave_low64(m2, m3);
      let t2: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 4u32);
      let o2: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(t2, mask26);
      let t1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(t01, 26u32);
      let o1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(t1, mask26);
      let o5: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(t01, mask26);
      let t31: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 30u32);
      let o3: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(t31, mask26);
      let o4: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(m4, 40u32);
      let o0: crate::lib::intvector::intrinsics::vec256 = o5;
      let o1: crate::lib::intvector::intrinsics::vec256 = o1;
      let o2: crate::lib::intvector::intrinsics::vec256 = o2;
      let o3: crate::lib::intvector::intrinsics::vec256 = o3;
      let o4: crate::lib::intvector::intrinsics::vec256 = o4;
      (&mut e)[0u32 as usize] = o0;
      (&mut e)[1u32 as usize] = o1;
      (&mut e)[2u32 as usize] = o2;
      (&mut e)[3u32 as usize] = o3;
      (&mut e)[4u32 as usize] = o4;
      let b: u64 = 0x1000000u64;
      let mask: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load64(b);
      let f4: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
      (&mut e)[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_or(f4, mask);
      let
      rn:
      (&mut [crate::lib::intvector::intrinsics::vec256],
      &mut [crate::lib::intvector::intrinsics::vec256])
      =
        pre.1.split_at_mut(10usize);
      let
      rn5:
      (&mut [crate::lib::intvector::intrinsics::vec256],
      &mut [crate::lib::intvector::intrinsics::vec256])
      =
        rn.1.split_at_mut(5usize);
      let r0: crate::lib::intvector::intrinsics::vec256 = rn5.0[0u32 as usize];
      let r1: crate::lib::intvector::intrinsics::vec256 = rn5.0[1u32 as usize];
      let r2: crate::lib::intvector::intrinsics::vec256 = rn5.0[2u32 as usize];
      let r3: crate::lib::intvector::intrinsics::vec256 = rn5.0[3u32 as usize];
      let r4: crate::lib::intvector::intrinsics::vec256 = rn5.0[4u32 as usize];
      let r51: crate::lib::intvector::intrinsics::vec256 = rn5.1[1u32 as usize];
      let r52: crate::lib::intvector::intrinsics::vec256 = rn5.1[2u32 as usize];
      let r53: crate::lib::intvector::intrinsics::vec256 = rn5.1[3u32 as usize];
      let r54: crate::lib::intvector::intrinsics::vec256 = rn5.1[4u32 as usize];
      let f10: crate::lib::intvector::intrinsics::vec256 = acc.1[0u32 as usize];
      let f11: crate::lib::intvector::intrinsics::vec256 = acc.1[1u32 as usize];
      let f12: crate::lib::intvector::intrinsics::vec256 = acc.1[2u32 as usize];
      let f13: crate::lib::intvector::intrinsics::vec256 = acc.1[3u32 as usize];
      let f14: crate::lib::intvector::intrinsics::vec256 = acc.1[4u32 as usize];
      let a0: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_mul64(r0, f10);
      let a1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_mul64(r1, f10);
      let a2: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_mul64(r2, f10);
      let a3: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_mul64(r3, f10);
      let a4: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_mul64(r4, f10);
      let a01: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a0,
          crate::lib::intvector::intrinsics::vec256_mul64(r54, f11)
        );
      let a11: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a1,
          crate::lib::intvector::intrinsics::vec256_mul64(r0, f11)
        );
      let a21: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a2,
          crate::lib::intvector::intrinsics::vec256_mul64(r1, f11)
        );
      let a31: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a3,
          crate::lib::intvector::intrinsics::vec256_mul64(r2, f11)
        );
      let a41: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a4,
          crate::lib::intvector::intrinsics::vec256_mul64(r3, f11)
        );
      let a02: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a01,
          crate::lib::intvector::intrinsics::vec256_mul64(r53, f12)
        );
      let a12: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a11,
          crate::lib::intvector::intrinsics::vec256_mul64(r54, f12)
        );
      let a22: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a21,
          crate::lib::intvector::intrinsics::vec256_mul64(r0, f12)
        );
      let a32: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a31,
          crate::lib::intvector::intrinsics::vec256_mul64(r1, f12)
        );
      let a42: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a41,
          crate::lib::intvector::intrinsics::vec256_mul64(r2, f12)
        );
      let a03: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a02,
          crate::lib::intvector::intrinsics::vec256_mul64(r52, f13)
        );
      let a13: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a12,
          crate::lib::intvector::intrinsics::vec256_mul64(r53, f13)
        );
      let a23: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a22,
          crate::lib::intvector::intrinsics::vec256_mul64(r54, f13)
        );
      let a33: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a32,
          crate::lib::intvector::intrinsics::vec256_mul64(r0, f13)
        );
      let a43: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a42,
          crate::lib::intvector::intrinsics::vec256_mul64(r1, f13)
        );
      let a04: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a03,
          crate::lib::intvector::intrinsics::vec256_mul64(r51, f14)
        );
      let a14: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a13,
          crate::lib::intvector::intrinsics::vec256_mul64(r52, f14)
        );
      let a24: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a23,
          crate::lib::intvector::intrinsics::vec256_mul64(r53, f14)
        );
      let a34: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a33,
          crate::lib::intvector::intrinsics::vec256_mul64(r54, f14)
        );
      let a44: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(
          a43,
          crate::lib::intvector::intrinsics::vec256_mul64(r0, f14)
        );
      let t01: crate::lib::intvector::intrinsics::vec256 = a04;
      let t1: crate::lib::intvector::intrinsics::vec256 = a14;
      let t2: crate::lib::intvector::intrinsics::vec256 = a24;
      let t3: crate::lib::intvector::intrinsics::vec256 = a34;
      let t4: crate::lib::intvector::intrinsics::vec256 = a44;
      let mask26: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64);
      let z0: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(t01, 26u32);
      let z1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 26u32);
      let x0: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(t01, mask26);
      let x3: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(t3, mask26);
      let x1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(t1, z0);
      let x4: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(t4, z1);
      let z01: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(x1, 26u32);
      let z11: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(x4, 26u32);
      let t: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_left64(z11, 2u32);
      let z12: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(z11, t);
      let x11: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(x1, mask26);
      let x41: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(x4, mask26);
      let x2: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(t2, z01);
      let x01: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(x0, z12);
      let z02: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(x2, 26u32);
      let z13: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(x01, 26u32);
      let x21: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(x2, mask26);
      let x02: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(x01, mask26);
      let x31: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(x3, z02);
      let x12: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(x11, z13);
      let z03: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_shift_right64(x31, 26u32);
      let x32: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_and(x31, mask26);
      let x42: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(x41, z03);
      let o0: crate::lib::intvector::intrinsics::vec256 = x02;
      let o1: crate::lib::intvector::intrinsics::vec256 = x12;
      let o2: crate::lib::intvector::intrinsics::vec256 = x21;
      let o3: crate::lib::intvector::intrinsics::vec256 = x32;
      let o4: crate::lib::intvector::intrinsics::vec256 = x42;
      acc.1[0u32 as usize] = o0;
      acc.1[1u32 as usize] = o1;
      acc.1[2u32 as usize] = o2;
      acc.1[3u32 as usize] = o3;
      acc.1[4u32 as usize] = o4;
      let f10: crate::lib::intvector::intrinsics::vec256 = acc.1[0u32 as usize];
      let f11: crate::lib::intvector::intrinsics::vec256 = acc.1[1u32 as usize];
      let f12: crate::lib::intvector::intrinsics::vec256 = acc.1[2u32 as usize];
      let f13: crate::lib::intvector::intrinsics::vec256 = acc.1[3u32 as usize];
      let f14: crate::lib::intvector::intrinsics::vec256 = acc.1[4u32 as usize];
      let f20: crate::lib::intvector::intrinsics::vec256 = (&mut e)[0u32 as usize];
      let f21: crate::lib::intvector::intrinsics::vec256 = (&mut e)[1u32 as usize];
      let f22: crate::lib::intvector::intrinsics::vec256 = (&mut e)[2u32 as usize];
      let f23: crate::lib::intvector::intrinsics::vec256 = (&mut e)[3u32 as usize];
      let f24: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
      let o0: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(f10, f20);
      let o1: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(f11, f21);
      let o2: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(f12, f22);
      let o3: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(f13, f23);
      let o4: crate::lib::intvector::intrinsics::vec256 =
        crate::lib::intvector::intrinsics::vec256_add64(f14, f24);
      acc.1[0u32 as usize] = o0;
      acc.1[1u32 as usize] = o1;
      acc.1[2u32 as usize] = o2;
      acc.1[3u32 as usize] = o3;
      acc.1[4u32 as usize] = o4
    };
    crate::hacl::poly1305_256::fmul_r4_normalize(acc.1, pre.1)
  };
  let len1: u32 = n.wrapping_mul(16u32).wrapping_sub(len0);
  let t1: (&mut [u8], &mut [u8]) = t0.1.split_at_mut((len0 as usize).wrapping_add(0usize));
  let nb: u32 = len1.wrapping_div(16u32);
  let rem1: u32 = len1.wrapping_rem(16u32);
  for i in 0u32..rem1
  {
    let block: (&mut [u8], &mut [u8]) =
      t1.1.split_at_mut((i.wrapping_mul(16u32) as usize).wrapping_add(0usize));
    let mut e: [crate::lib::intvector::intrinsics::vec256; 5] =
      [crate::lib::intvector::intrinsics::vec256_zero; 5u32 as usize];
    let u: u64 = crate::lowstar::endianness::load64_le(&mut block.1[0u32 as usize..]);
    let lo: u64 = u;
    let u: u64 = crate::lowstar::endianness::load64_le(&mut block.1[8u32 as usize..]);
    let hi: u64 = u;
    let f0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(lo);
    let f1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(hi);
    let f01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        f0,
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 26u32),
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_or(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 52u32),
        crate::lib::intvector::intrinsics::vec256_shift_left64(
          crate::lib::intvector::intrinsics::vec256_and(
            f1,
            crate::lib::intvector::intrinsics::vec256_load64(0x3fffu64)
          ),
          12u32
        )
      );
    let f3: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 14u32),
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f4: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 40u32);
    let f01: crate::lib::intvector::intrinsics::vec256 = f01;
    let f11: crate::lib::intvector::intrinsics::vec256 = f11;
    let f2: crate::lib::intvector::intrinsics::vec256 = f2;
    let f3: crate::lib::intvector::intrinsics::vec256 = f3;
    let f4: crate::lib::intvector::intrinsics::vec256 = f4;
    (&mut e)[0u32 as usize] = f01;
    (&mut e)[1u32 as usize] = f11;
    (&mut e)[2u32 as usize] = f2;
    (&mut e)[3u32 as usize] = f3;
    (&mut e)[4u32 as usize] = f4;
    let b: u64 = 0x1000000u64;
    let mask: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(b);
    let f4: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
    (&mut e)[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_or(f4, mask);
    let
    r1:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      pre.1.split_at_mut(0usize);
    let
    r5:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      r1.1.split_at_mut(5usize);
    let r0: crate::lib::intvector::intrinsics::vec256 = r5.0[0u32 as usize];
    let r11: crate::lib::intvector::intrinsics::vec256 = r5.0[1u32 as usize];
    let r2: crate::lib::intvector::intrinsics::vec256 = r5.0[2u32 as usize];
    let r3: crate::lib::intvector::intrinsics::vec256 = r5.0[3u32 as usize];
    let r4: crate::lib::intvector::intrinsics::vec256 = r5.0[4u32 as usize];
    let r51: crate::lib::intvector::intrinsics::vec256 = r5.1[1u32 as usize];
    let r52: crate::lib::intvector::intrinsics::vec256 = r5.1[2u32 as usize];
    let r53: crate::lib::intvector::intrinsics::vec256 = r5.1[3u32 as usize];
    let r54: crate::lib::intvector::intrinsics::vec256 = r5.1[4u32 as usize];
    let f10: crate::lib::intvector::intrinsics::vec256 = (&mut e)[0u32 as usize];
    let f11: crate::lib::intvector::intrinsics::vec256 = (&mut e)[1u32 as usize];
    let f12: crate::lib::intvector::intrinsics::vec256 = (&mut e)[2u32 as usize];
    let f13: crate::lib::intvector::intrinsics::vec256 = (&mut e)[3u32 as usize];
    let f14: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
    let a0: crate::lib::intvector::intrinsics::vec256 = acc.1[0u32 as usize];
    let a1: crate::lib::intvector::intrinsics::vec256 = acc.1[1u32 as usize];
    let a2: crate::lib::intvector::intrinsics::vec256 = acc.1[2u32 as usize];
    let a3: crate::lib::intvector::intrinsics::vec256 = acc.1[3u32 as usize];
    let a4: crate::lib::intvector::intrinsics::vec256 = acc.1[4u32 as usize];
    let a01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a0, f10);
    let a11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a1, f11);
    let a21: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a2, f12);
    let a31: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a3, f13);
    let a41: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a4, f14);
    let a02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a01);
    let a12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r11, a01);
    let a22: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r2, a01);
    let a32: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r3, a01);
    let a42: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r4, a01);
    let a03: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a02,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a11)
      );
    let a13: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a12,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a11)
      );
    let a23: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a22,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a11)
      );
    let a33: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a32,
        crate::lib::intvector::intrinsics::vec256_mul64(r2, a11)
      );
    let a43: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a42,
        crate::lib::intvector::intrinsics::vec256_mul64(r3, a11)
      );
    let a04: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a03,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a21)
      );
    let a14: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a13,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a21)
      );
    let a24: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a23,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a21)
      );
    let a34: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a33,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a21)
      );
    let a44: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a43,
        crate::lib::intvector::intrinsics::vec256_mul64(r2, a21)
      );
    let a05: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a04,
        crate::lib::intvector::intrinsics::vec256_mul64(r52, a31)
      );
    let a15: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a14,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a31)
      );
    let a25: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a24,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a31)
      );
    let a35: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a34,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a31)
      );
    let a45: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a44,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a31)
      );
    let a06: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a05,
        crate::lib::intvector::intrinsics::vec256_mul64(r51, a41)
      );
    let a16: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a15,
        crate::lib::intvector::intrinsics::vec256_mul64(r52, a41)
      );
    let a26: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a25,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a41)
      );
    let a36: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a35,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a41)
      );
    let a46: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a45,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a41)
      );
    let t01: crate::lib::intvector::intrinsics::vec256 = a06;
    let t11: crate::lib::intvector::intrinsics::vec256 = a16;
    let t2: crate::lib::intvector::intrinsics::vec256 = a26;
    let t3: crate::lib::intvector::intrinsics::vec256 = a36;
    let t4: crate::lib::intvector::intrinsics::vec256 = a46;
    let mask26: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64);
    let z0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(t01, 26u32);
    let z1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(t01, mask26);
    let x3: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(t3, mask26);
    let x1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t11, z0);
    let x4: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t4, z1);
    let z01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x4, 26u32);
    let t: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(z11, t);
    let x11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x1, mask26);
    let x41: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x4, mask26);
    let x2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t2, z01);
    let x01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x0, z12);
    let z02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x2, mask26);
    let x02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x01, mask26);
    let x31: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x3, z02);
    let x12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x11, z13);
    let z03: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x31, mask26);
    let x42: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x41, z03);
    let o0: crate::lib::intvector::intrinsics::vec256 = x02;
    let o1: crate::lib::intvector::intrinsics::vec256 = x12;
    let o2: crate::lib::intvector::intrinsics::vec256 = x21;
    let o3: crate::lib::intvector::intrinsics::vec256 = x32;
    let o4: crate::lib::intvector::intrinsics::vec256 = x42;
    acc.1[0u32 as usize] = o0;
    acc.1[1u32 as usize] = o1;
    acc.1[2u32 as usize] = o2;
    acc.1[3u32 as usize] = o3;
    acc.1[4u32 as usize] = o4
  };
  if rem1 > 0u32
  {
    let last: (&mut [u8], &mut [u8]) =
      t1.1.split_at_mut((nb.wrapping_mul(16u32) as usize).wrapping_add(0usize));
    let mut e: [crate::lib::intvector::intrinsics::vec256; 5] =
      [crate::lib::intvector::intrinsics::vec256_zero; 5u32 as usize];
    let mut tmp: [u8; 16] = [0u8; 16u32 as usize];
    ((&mut tmp)[0u32 as usize..0u32 as usize + rem1 as usize]).copy_from_slice(
      &last.1[0u32 as usize..0u32 as usize + rem1 as usize]
    );
    let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[0u32 as usize..]);
    let lo: u64 = u;
    let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[8u32 as usize..]);
    let hi: u64 = u;
    let f0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(lo);
    let f1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(hi);
    let f01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        f0,
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 26u32),
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_or(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 52u32),
        crate::lib::intvector::intrinsics::vec256_shift_left64(
          crate::lib::intvector::intrinsics::vec256_and(
            f1,
            crate::lib::intvector::intrinsics::vec256_load64(0x3fffu64)
          ),
          12u32
        )
      );
    let f3: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 14u32),
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f4: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 40u32);
    let f01: crate::lib::intvector::intrinsics::vec256 = f01;
    let f11: crate::lib::intvector::intrinsics::vec256 = f11;
    let f2: crate::lib::intvector::intrinsics::vec256 = f2;
    let f3: crate::lib::intvector::intrinsics::vec256 = f3;
    let f4: crate::lib::intvector::intrinsics::vec256 = f4;
    (&mut e)[0u32 as usize] = f01;
    (&mut e)[1u32 as usize] = f11;
    (&mut e)[2u32 as usize] = f2;
    (&mut e)[3u32 as usize] = f3;
    (&mut e)[4u32 as usize] = f4;
    let b: u64 = 1u64.wrapping_shl(rem1.wrapping_mul(8u32).wrapping_rem(26u32));
    let mask: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(b);
    let fi: crate::lib::intvector::intrinsics::vec256 =
      (&mut e)[rem1.wrapping_mul(8u32).wrapping_div(26u32) as usize];
    (&mut e)[rem1.wrapping_mul(8u32).wrapping_div(26u32) as usize] =
      crate::lib::intvector::intrinsics::vec256_or(fi, mask);
    let
    r1:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      pre.1.split_at_mut(0usize);
    let
    r5:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      r1.1.split_at_mut(5usize);
    let r0: crate::lib::intvector::intrinsics::vec256 = r5.0[0u32 as usize];
    let r11: crate::lib::intvector::intrinsics::vec256 = r5.0[1u32 as usize];
    let r2: crate::lib::intvector::intrinsics::vec256 = r5.0[2u32 as usize];
    let r3: crate::lib::intvector::intrinsics::vec256 = r5.0[3u32 as usize];
    let r4: crate::lib::intvector::intrinsics::vec256 = r5.0[4u32 as usize];
    let r51: crate::lib::intvector::intrinsics::vec256 = r5.1[1u32 as usize];
    let r52: crate::lib::intvector::intrinsics::vec256 = r5.1[2u32 as usize];
    let r53: crate::lib::intvector::intrinsics::vec256 = r5.1[3u32 as usize];
    let r54: crate::lib::intvector::intrinsics::vec256 = r5.1[4u32 as usize];
    let f10: crate::lib::intvector::intrinsics::vec256 = (&mut e)[0u32 as usize];
    let f11: crate::lib::intvector::intrinsics::vec256 = (&mut e)[1u32 as usize];
    let f12: crate::lib::intvector::intrinsics::vec256 = (&mut e)[2u32 as usize];
    let f13: crate::lib::intvector::intrinsics::vec256 = (&mut e)[3u32 as usize];
    let f14: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
    let a0: crate::lib::intvector::intrinsics::vec256 = acc.1[0u32 as usize];
    let a1: crate::lib::intvector::intrinsics::vec256 = acc.1[1u32 as usize];
    let a2: crate::lib::intvector::intrinsics::vec256 = acc.1[2u32 as usize];
    let a3: crate::lib::intvector::intrinsics::vec256 = acc.1[3u32 as usize];
    let a4: crate::lib::intvector::intrinsics::vec256 = acc.1[4u32 as usize];
    let a01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a0, f10);
    let a11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a1, f11);
    let a21: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a2, f12);
    let a31: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a3, f13);
    let a41: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a4, f14);
    let a02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a01);
    let a12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r11, a01);
    let a22: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r2, a01);
    let a32: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r3, a01);
    let a42: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r4, a01);
    let a03: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a02,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a11)
      );
    let a13: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a12,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a11)
      );
    let a23: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a22,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a11)
      );
    let a33: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a32,
        crate::lib::intvector::intrinsics::vec256_mul64(r2, a11)
      );
    let a43: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a42,
        crate::lib::intvector::intrinsics::vec256_mul64(r3, a11)
      );
    let a04: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a03,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a21)
      );
    let a14: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a13,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a21)
      );
    let a24: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a23,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a21)
      );
    let a34: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a33,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a21)
      );
    let a44: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a43,
        crate::lib::intvector::intrinsics::vec256_mul64(r2, a21)
      );
    let a05: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a04,
        crate::lib::intvector::intrinsics::vec256_mul64(r52, a31)
      );
    let a15: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a14,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a31)
      );
    let a25: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a24,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a31)
      );
    let a35: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a34,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a31)
      );
    let a45: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a44,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a31)
      );
    let a06: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a05,
        crate::lib::intvector::intrinsics::vec256_mul64(r51, a41)
      );
    let a16: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a15,
        crate::lib::intvector::intrinsics::vec256_mul64(r52, a41)
      );
    let a26: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a25,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a41)
      );
    let a36: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a35,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a41)
      );
    let a46: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a45,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a41)
      );
    let t01: crate::lib::intvector::intrinsics::vec256 = a06;
    let t11: crate::lib::intvector::intrinsics::vec256 = a16;
    let t2: crate::lib::intvector::intrinsics::vec256 = a26;
    let t3: crate::lib::intvector::intrinsics::vec256 = a36;
    let t4: crate::lib::intvector::intrinsics::vec256 = a46;
    let mask26: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64);
    let z0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(t01, 26u32);
    let z1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(t01, mask26);
    let x3: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(t3, mask26);
    let x1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t11, z0);
    let x4: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t4, z1);
    let z01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x4, 26u32);
    let t: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(z11, t);
    let x11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x1, mask26);
    let x41: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x4, mask26);
    let x2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t2, z01);
    let x01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x0, z12);
    let z02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x2, mask26);
    let x02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x01, mask26);
    let x31: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x3, z02);
    let x12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x11, z13);
    let z03: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x31, mask26);
    let x42: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x41, z03);
    let o0: crate::lib::intvector::intrinsics::vec256 = x02;
    let o1: crate::lib::intvector::intrinsics::vec256 = x12;
    let o2: crate::lib::intvector::intrinsics::vec256 = x21;
    let o3: crate::lib::intvector::intrinsics::vec256 = x32;
    let o4: crate::lib::intvector::intrinsics::vec256 = x42;
    acc.1[0u32 as usize] = o0;
    acc.1[1u32 as usize] = o1;
    acc.1[2u32 as usize] = o2;
    acc.1[3u32 as usize] = o3;
    acc.1[4u32 as usize] = o4
  };
  let mut tmp: [u8; 16] = [0u8; 16u32 as usize];
  ((&mut tmp)[0u32 as usize..0u32 as usize + r as usize]).copy_from_slice(
    &rem.1[0u32 as usize..0u32 as usize + r as usize]
  );
  if r > 0u32
  {
    let
    pre:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      pre.1.split_at_mut(0usize);
    let
    acc:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      acc.1.split_at_mut(0usize);
    let mut e: [crate::lib::intvector::intrinsics::vec256; 5] =
      [crate::lib::intvector::intrinsics::vec256_zero; 5u32 as usize];
    let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[0u32 as usize..]);
    let lo: u64 = u;
    let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut tmp)[8u32 as usize..]);
    let hi: u64 = u;
    let f0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(lo);
    let f1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(hi);
    let f01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        f0,
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 26u32),
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_or(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 52u32),
        crate::lib::intvector::intrinsics::vec256_shift_left64(
          crate::lib::intvector::intrinsics::vec256_and(
            f1,
            crate::lib::intvector::intrinsics::vec256_load64(0x3fffu64)
          ),
          12u32
        )
      );
    let f3: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(
        crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 14u32),
        crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
      );
    let f4: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 40u32);
    let f01: crate::lib::intvector::intrinsics::vec256 = f01;
    let f11: crate::lib::intvector::intrinsics::vec256 = f11;
    let f2: crate::lib::intvector::intrinsics::vec256 = f2;
    let f3: crate::lib::intvector::intrinsics::vec256 = f3;
    let f4: crate::lib::intvector::intrinsics::vec256 = f4;
    (&mut e)[0u32 as usize] = f01;
    (&mut e)[1u32 as usize] = f11;
    (&mut e)[2u32 as usize] = f2;
    (&mut e)[3u32 as usize] = f3;
    (&mut e)[4u32 as usize] = f4;
    let b: u64 = 0x1000000u64;
    let mask: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(b);
    let f4: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
    (&mut e)[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_or(f4, mask);
    let
    r1:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      pre.1.split_at_mut(0usize);
    let
    r5:
    (&mut [crate::lib::intvector::intrinsics::vec256],
    &mut [crate::lib::intvector::intrinsics::vec256])
    =
      r1.1.split_at_mut(5usize);
    let r0: crate::lib::intvector::intrinsics::vec256 = r5.0[0u32 as usize];
    let r11: crate::lib::intvector::intrinsics::vec256 = r5.0[1u32 as usize];
    let r2: crate::lib::intvector::intrinsics::vec256 = r5.0[2u32 as usize];
    let r3: crate::lib::intvector::intrinsics::vec256 = r5.0[3u32 as usize];
    let r4: crate::lib::intvector::intrinsics::vec256 = r5.0[4u32 as usize];
    let r51: crate::lib::intvector::intrinsics::vec256 = r5.1[1u32 as usize];
    let r52: crate::lib::intvector::intrinsics::vec256 = r5.1[2u32 as usize];
    let r53: crate::lib::intvector::intrinsics::vec256 = r5.1[3u32 as usize];
    let r54: crate::lib::intvector::intrinsics::vec256 = r5.1[4u32 as usize];
    let f10: crate::lib::intvector::intrinsics::vec256 = (&mut e)[0u32 as usize];
    let f11: crate::lib::intvector::intrinsics::vec256 = (&mut e)[1u32 as usize];
    let f12: crate::lib::intvector::intrinsics::vec256 = (&mut e)[2u32 as usize];
    let f13: crate::lib::intvector::intrinsics::vec256 = (&mut e)[3u32 as usize];
    let f14: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
    let a0: crate::lib::intvector::intrinsics::vec256 = acc.1[0u32 as usize];
    let a1: crate::lib::intvector::intrinsics::vec256 = acc.1[1u32 as usize];
    let a2: crate::lib::intvector::intrinsics::vec256 = acc.1[2u32 as usize];
    let a3: crate::lib::intvector::intrinsics::vec256 = acc.1[3u32 as usize];
    let a4: crate::lib::intvector::intrinsics::vec256 = acc.1[4u32 as usize];
    let a01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a0, f10);
    let a11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a1, f11);
    let a21: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a2, f12);
    let a31: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a3, f13);
    let a41: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(a4, f14);
    let a02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a01);
    let a12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r11, a01);
    let a22: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r2, a01);
    let a32: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r3, a01);
    let a42: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_mul64(r4, a01);
    let a03: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a02,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a11)
      );
    let a13: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a12,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a11)
      );
    let a23: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a22,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a11)
      );
    let a33: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a32,
        crate::lib::intvector::intrinsics::vec256_mul64(r2, a11)
      );
    let a43: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a42,
        crate::lib::intvector::intrinsics::vec256_mul64(r3, a11)
      );
    let a04: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a03,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a21)
      );
    let a14: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a13,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a21)
      );
    let a24: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a23,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a21)
      );
    let a34: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a33,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a21)
      );
    let a44: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a43,
        crate::lib::intvector::intrinsics::vec256_mul64(r2, a21)
      );
    let a05: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a04,
        crate::lib::intvector::intrinsics::vec256_mul64(r52, a31)
      );
    let a15: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a14,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a31)
      );
    let a25: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a24,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a31)
      );
    let a35: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a34,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a31)
      );
    let a45: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a44,
        crate::lib::intvector::intrinsics::vec256_mul64(r11, a31)
      );
    let a06: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a05,
        crate::lib::intvector::intrinsics::vec256_mul64(r51, a41)
      );
    let a16: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a15,
        crate::lib::intvector::intrinsics::vec256_mul64(r52, a41)
      );
    let a26: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a25,
        crate::lib::intvector::intrinsics::vec256_mul64(r53, a41)
      );
    let a36: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a35,
        crate::lib::intvector::intrinsics::vec256_mul64(r54, a41)
      );
    let a46: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(
        a45,
        crate::lib::intvector::intrinsics::vec256_mul64(r0, a41)
      );
    let t0: crate::lib::intvector::intrinsics::vec256 = a06;
    let t1: crate::lib::intvector::intrinsics::vec256 = a16;
    let t2: crate::lib::intvector::intrinsics::vec256 = a26;
    let t3: crate::lib::intvector::intrinsics::vec256 = a36;
    let t4: crate::lib::intvector::intrinsics::vec256 = a46;
    let mask26: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64);
    let z0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(t0, 26u32);
    let z1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 26u32);
    let x0: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(t0, mask26);
    let x3: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(t3, mask26);
    let x1: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t1, z0);
    let x4: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t4, z1);
    let z01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x1, 26u32);
    let z11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x4, 26u32);
    let t: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_left64(z11, 2u32);
    let z12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(z11, t);
    let x11: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x1, mask26);
    let x41: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x4, mask26);
    let x2: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(t2, z01);
    let x01: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x0, z12);
    let z02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x2, 26u32);
    let z13: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x01, 26u32);
    let x21: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x2, mask26);
    let x02: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x01, mask26);
    let x31: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x3, z02);
    let x12: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x11, z13);
    let z03: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_shift_right64(x31, 26u32);
    let x32: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_and(x31, mask26);
    let x42: crate::lib::intvector::intrinsics::vec256 =
      crate::lib::intvector::intrinsics::vec256_add64(x41, z03);
    let o0: crate::lib::intvector::intrinsics::vec256 = x02;
    let o1: crate::lib::intvector::intrinsics::vec256 = x12;
    let o2: crate::lib::intvector::intrinsics::vec256 = x21;
    let o3: crate::lib::intvector::intrinsics::vec256 = x32;
    let o4: crate::lib::intvector::intrinsics::vec256 = x42;
    acc.1[0u32 as usize] = o0;
    acc.1[1u32 as usize] = o1;
    acc.1[2u32 as usize] = o2;
    acc.1[3u32 as usize] = o3;
    acc.1[4u32 as usize] = o4
  }
}

fn poly1305_do_256(
  k: &mut [u8],
  aadlen: u32,
  aad: &mut [u8],
  mlen: u32,
  m: &mut [u8],
  out: &mut [u8]
) ->
  ()
{
  let mut ctx: [crate::lib::intvector::intrinsics::vec256; 25] =
    [crate::lib::intvector::intrinsics::vec256_zero; 25u32 as usize];
  let mut block: [u8; 16] = [0u8; 16u32 as usize];
  crate::hacl::poly1305_256::poly1305_init(&mut ctx, k);
  if aadlen != 0u32 { poly1305_padded_256(&mut ctx, aadlen, aad) };
  if mlen != 0u32 { poly1305_padded_256(&mut ctx, mlen, m) };
  crate::lowstar::endianness::store64_le(&mut (&mut block)[0u32 as usize..], aadlen as u64);
  crate::lowstar::endianness::store64_le(&mut (&mut block)[8u32 as usize..], mlen as u64);
  let
  pre:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    (&mut ctx).split_at_mut(5usize);
  let
  acc:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    pre.0.split_at_mut(0usize);
  let mut e: [crate::lib::intvector::intrinsics::vec256; 5] =
    [crate::lib::intvector::intrinsics::vec256_zero; 5u32 as usize];
  let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut block)[0u32 as usize..]);
  let lo: u64 = u;
  let u: u64 = crate::lowstar::endianness::load64_le(&mut (&mut block)[8u32 as usize..]);
  let hi: u64 = u;
  let f0: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_load64(lo);
  let f1: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_load64(hi);
  let f01: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(
      f0,
      crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
    );
  let f11: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(
      crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 26u32),
      crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
    );
  let f2: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_or(
      crate::lib::intvector::intrinsics::vec256_shift_right64(f0, 52u32),
      crate::lib::intvector::intrinsics::vec256_shift_left64(
        crate::lib::intvector::intrinsics::vec256_and(
          f1,
          crate::lib::intvector::intrinsics::vec256_load64(0x3fffu64)
        ),
        12u32
      )
    );
  let f3: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(
      crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 14u32),
      crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64)
    );
  let f4: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(f1, 40u32);
  let f01: crate::lib::intvector::intrinsics::vec256 = f01;
  let f11: crate::lib::intvector::intrinsics::vec256 = f11;
  let f2: crate::lib::intvector::intrinsics::vec256 = f2;
  let f3: crate::lib::intvector::intrinsics::vec256 = f3;
  let f4: crate::lib::intvector::intrinsics::vec256 = f4;
  (&mut e)[0u32 as usize] = f01;
  (&mut e)[1u32 as usize] = f11;
  (&mut e)[2u32 as usize] = f2;
  (&mut e)[3u32 as usize] = f3;
  (&mut e)[4u32 as usize] = f4;
  let b: u64 = 0x1000000u64;
  let mask: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_load64(b);
  let f4: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
  (&mut e)[4u32 as usize] = crate::lib::intvector::intrinsics::vec256_or(f4, mask);
  let
  r:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    pre.1.split_at_mut(0usize);
  let
  r5:
  (&mut [crate::lib::intvector::intrinsics::vec256],
  &mut [crate::lib::intvector::intrinsics::vec256])
  =
    r.1.split_at_mut(5usize);
  let r0: crate::lib::intvector::intrinsics::vec256 = r5.0[0u32 as usize];
  let r1: crate::lib::intvector::intrinsics::vec256 = r5.0[1u32 as usize];
  let r2: crate::lib::intvector::intrinsics::vec256 = r5.0[2u32 as usize];
  let r3: crate::lib::intvector::intrinsics::vec256 = r5.0[3u32 as usize];
  let r4: crate::lib::intvector::intrinsics::vec256 = r5.0[4u32 as usize];
  let r51: crate::lib::intvector::intrinsics::vec256 = r5.1[1u32 as usize];
  let r52: crate::lib::intvector::intrinsics::vec256 = r5.1[2u32 as usize];
  let r53: crate::lib::intvector::intrinsics::vec256 = r5.1[3u32 as usize];
  let r54: crate::lib::intvector::intrinsics::vec256 = r5.1[4u32 as usize];
  let f10: crate::lib::intvector::intrinsics::vec256 = (&mut e)[0u32 as usize];
  let f11: crate::lib::intvector::intrinsics::vec256 = (&mut e)[1u32 as usize];
  let f12: crate::lib::intvector::intrinsics::vec256 = (&mut e)[2u32 as usize];
  let f13: crate::lib::intvector::intrinsics::vec256 = (&mut e)[3u32 as usize];
  let f14: crate::lib::intvector::intrinsics::vec256 = (&mut e)[4u32 as usize];
  let a0: crate::lib::intvector::intrinsics::vec256 = acc.1[0u32 as usize];
  let a1: crate::lib::intvector::intrinsics::vec256 = acc.1[1u32 as usize];
  let a2: crate::lib::intvector::intrinsics::vec256 = acc.1[2u32 as usize];
  let a3: crate::lib::intvector::intrinsics::vec256 = acc.1[3u32 as usize];
  let a4: crate::lib::intvector::intrinsics::vec256 = acc.1[4u32 as usize];
  let a01: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(a0, f10);
  let a11: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(a1, f11);
  let a21: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(a2, f12);
  let a31: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(a3, f13);
  let a41: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(a4, f14);
  let a02: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_mul64(r0, a01);
  let a12: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_mul64(r1, a01);
  let a22: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_mul64(r2, a01);
  let a32: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_mul64(r3, a01);
  let a42: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_mul64(r4, a01);
  let a03: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a02,
      crate::lib::intvector::intrinsics::vec256_mul64(r54, a11)
    );
  let a13: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a12,
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a11)
    );
  let a23: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a22,
      crate::lib::intvector::intrinsics::vec256_mul64(r1, a11)
    );
  let a33: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a32,
      crate::lib::intvector::intrinsics::vec256_mul64(r2, a11)
    );
  let a43: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a42,
      crate::lib::intvector::intrinsics::vec256_mul64(r3, a11)
    );
  let a04: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a03,
      crate::lib::intvector::intrinsics::vec256_mul64(r53, a21)
    );
  let a14: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a13,
      crate::lib::intvector::intrinsics::vec256_mul64(r54, a21)
    );
  let a24: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a23,
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a21)
    );
  let a34: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a33,
      crate::lib::intvector::intrinsics::vec256_mul64(r1, a21)
    );
  let a44: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a43,
      crate::lib::intvector::intrinsics::vec256_mul64(r2, a21)
    );
  let a05: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a04,
      crate::lib::intvector::intrinsics::vec256_mul64(r52, a31)
    );
  let a15: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a14,
      crate::lib::intvector::intrinsics::vec256_mul64(r53, a31)
    );
  let a25: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a24,
      crate::lib::intvector::intrinsics::vec256_mul64(r54, a31)
    );
  let a35: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a34,
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a31)
    );
  let a45: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a44,
      crate::lib::intvector::intrinsics::vec256_mul64(r1, a31)
    );
  let a06: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a05,
      crate::lib::intvector::intrinsics::vec256_mul64(r51, a41)
    );
  let a16: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a15,
      crate::lib::intvector::intrinsics::vec256_mul64(r52, a41)
    );
  let a26: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a25,
      crate::lib::intvector::intrinsics::vec256_mul64(r53, a41)
    );
  let a36: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a35,
      crate::lib::intvector::intrinsics::vec256_mul64(r54, a41)
    );
  let a46: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(
      a45,
      crate::lib::intvector::intrinsics::vec256_mul64(r0, a41)
    );
  let t0: crate::lib::intvector::intrinsics::vec256 = a06;
  let t1: crate::lib::intvector::intrinsics::vec256 = a16;
  let t2: crate::lib::intvector::intrinsics::vec256 = a26;
  let t3: crate::lib::intvector::intrinsics::vec256 = a36;
  let t4: crate::lib::intvector::intrinsics::vec256 = a46;
  let mask26: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_load64(0x3ffffffu64);
  let z0: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(t0, 26u32);
  let z1: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(t3, 26u32);
  let x0: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(t0, mask26);
  let x3: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(t3, mask26);
  let x1: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(t1, z0);
  let x4: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(t4, z1);
  let z01: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(x1, 26u32);
  let z11: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(x4, 26u32);
  let t: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_left64(z11, 2u32);
  let z12: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(z11, t);
  let x11: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(x1, mask26);
  let x41: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(x4, mask26);
  let x2: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(t2, z01);
  let x01: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(x0, z12);
  let z02: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(x2, 26u32);
  let z13: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(x01, 26u32);
  let x21: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(x2, mask26);
  let x02: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(x01, mask26);
  let x31: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(x3, z02);
  let x12: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(x11, z13);
  let z03: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_shift_right64(x31, 26u32);
  let x32: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_and(x31, mask26);
  let x42: crate::lib::intvector::intrinsics::vec256 =
    crate::lib::intvector::intrinsics::vec256_add64(x41, z03);
  let o0: crate::lib::intvector::intrinsics::vec256 = x02;
  let o1: crate::lib::intvector::intrinsics::vec256 = x12;
  let o2: crate::lib::intvector::intrinsics::vec256 = x21;
  let o3: crate::lib::intvector::intrinsics::vec256 = x32;
  let o4: crate::lib::intvector::intrinsics::vec256 = x42;
  acc.1[0u32 as usize] = o0;
  acc.1[1u32 as usize] = o1;
  acc.1[2u32 as usize] = o2;
  acc.1[3u32 as usize] = o3;
  acc.1[4u32 as usize] = o4;
  crate::hacl::poly1305_256::poly1305_finish(out, k, pre.1)
}

pub fn aead_encrypt(
  k: &mut [u8],
  n: &mut [u8],
  aadlen: u32,
  aad: &mut [u8],
  mlen: u32,
  m: &mut [u8],
  cipher: &mut [u8],
  mac: &mut [u8]
) ->
  ()
{
  crate::hacl::chacha20_vec256::chacha20_encrypt_256(mlen, cipher, m, k, n, 1u32);
  let mut tmp: [u8; 64] = [0u8; 64u32 as usize];
  let mut tmp_copy: [u8; 64] = [0u8; 64u32 as usize];
  crate::hacl::chacha20_vec256::chacha20_encrypt_256(64u32, &mut tmp, &mut tmp_copy, k, n, 0u32);
  let key: (&mut [u8], &mut [u8]) = (&mut tmp).split_at_mut(0usize);
  poly1305_do_256(key.1, aadlen, aad, mlen, cipher, mac)
}

pub fn aead_decrypt(
  k: &mut [u8],
  n: &mut [u8],
  aadlen: u32,
  aad: &mut [u8],
  mlen: u32,
  m: &mut [u8],
  cipher: &mut [u8],
  mac: &mut [u8]
) ->
  u32
{
  let mut computed_mac: [u8; 16] = [0u8; 16u32 as usize];
  let mut tmp: [u8; 64] = [0u8; 64u32 as usize];
  let mut tmp_copy: [u8; 64] = [0u8; 64u32 as usize];
  crate::hacl::chacha20_vec256::chacha20_encrypt_256(64u32, &mut tmp, &mut tmp_copy, k, n, 0u32);
  let key: (&mut [u8], &mut [u8]) = (&mut tmp).split_at_mut(0usize);
  poly1305_do_256(key.1, aadlen, aad, mlen, cipher, &mut computed_mac);
  let mut res: u8 = 255u8;
  for i in 0u32..16u32
  {
    let uu____0: u8 =
      crate::fstar::uint8::eq_mask((&mut computed_mac)[i as usize], mac[i as usize]);
    res = uu____0 & res
  };
  let z: u8 = res;
  if z == 255u8
  {
    crate::hacl::chacha20_vec256::chacha20_encrypt_256(mlen, m, cipher, k, n, 1u32);
    0u32
  }
  else
  { 1u32 }
}