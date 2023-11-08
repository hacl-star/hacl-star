const _h0: [u32; 4] = [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32];

const _t: [u32; 64] =
  [0xd76aa478u32,
    0xe8c7b756u32,
    0x242070dbu32,
    0xc1bdceeeu32,
    0xf57c0fafu32,
    0x4787c62au32,
    0xa8304613u32,
    0xfd469501u32,
    0x698098d8u32,
    0x8b44f7afu32,
    0xffff5bb1u32,
    0x895cd7beu32,
    0x6b901122u32,
    0xfd987193u32,
    0xa679438eu32,
    0x49b40821u32,
    0xf61e2562u32,
    0xc040b340u32,
    0x265e5a51u32,
    0xe9b6c7aau32,
    0xd62f105du32,
    0x02441453u32,
    0xd8a1e681u32,
    0xe7d3fbc8u32,
    0x21e1cde6u32,
    0xc33707d6u32,
    0xf4d50d87u32,
    0x455a14edu32,
    0xa9e3e905u32,
    0xfcefa3f8u32,
    0x676f02d9u32,
    0x8d2a4c8au32,
    0xfffa3942u32,
    0x8771f681u32,
    0x6d9d6122u32,
    0xfde5380cu32,
    0xa4beea44u32,
    0x4bdecfa9u32,
    0xf6bb4b60u32,
    0xbebfbc70u32,
    0x289b7ec6u32,
    0xeaa127fau32,
    0xd4ef3085u32,
    0x4881d05u32,
    0xd9d4d039u32,
    0xe6db99e5u32,
    0x1fa27cf8u32,
    0xc4ac5665u32,
    0xf4292244u32,
    0x432aff97u32,
    0xab9423a7u32,
    0xfc93a039u32,
    0x655b59c3u32,
    0x8f0ccc92u32,
    0xffeff47du32,
    0x85845dd1u32,
    0x6fa87e4fu32,
    0xfe2ce6e0u32,
    0xa3014314u32,
    0x4e0811a1u32,
    0xf7537e82u32,
    0xbd3af235u32,
    0x2ad7d2bbu32,
    0xeb86d391u32];

pub fn legacy_init(s: &mut [u32]) -> ()
for i in 0u32..4u32 { s[i as usize] = (&mut _h0)[i as usize] }

fn legacy_update(abcd: &mut [u32], x: &mut [u8]) -> ()
{
  let aa: u32 = abcd[0u32 as usize];
  let bb: u32 = abcd[1u32 as usize];
  let cc: u32 = abcd[2u32 as usize];
  let dd: u32 = abcd[3u32 as usize];
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = x.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[0u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(7u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(25u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[1u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(12u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(20u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[2u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(17u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(15u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[3u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(22u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(10u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[4u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(7u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(25u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[5u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(12u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(20u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[6u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(17u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(15u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[7u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(22u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(10u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[8u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(7u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(25u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[9u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(12u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(20u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[10u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(17u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(15u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[11u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(22u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(10u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[12u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(7u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(25u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[13u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(12u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(20u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[14u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(17u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(15u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(4usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[15u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(22u32)
      |
      va.wrapping_add(vb & vc | ! vb & vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(10u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[16u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(5u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(27u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[17u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(9u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(23u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[18u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(14u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(18u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[19u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(20u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(12u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[20u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(5u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(27u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[21u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(9u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(23u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[22u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(14u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(18u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[23u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(20u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(12u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[24u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(5u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(27u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[25u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(9u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(23u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[26u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(14u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(18u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[27u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(20u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(12u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[28u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(5u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(27u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[29u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(9u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(23u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[30u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(14u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(18u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.0.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[31u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shl(20u32)
      |
      va.wrapping_add(vb & vd | vc & ! vd).wrapping_add(xk).wrapping_add(ti).wrapping_shr(12u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[32u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(4u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(28u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[33u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(11u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(21u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[34u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(16u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(16u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[35u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(23u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(9u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[36u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(4u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(28u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[37u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(11u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(21u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[38u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(16u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(16u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[39u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(23u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(9u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[40u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(4u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(28u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[41u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(11u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(21u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[42u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(16u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(16u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[43u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(23u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(9u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[44u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(4u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(28u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[45u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(11u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(21u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[46u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(16u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(16u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[47u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(23u32)
      |
      va.wrapping_add(vb ^ (vc ^ vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(9u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[48u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(6u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(26u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[49u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(10u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(22u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[50u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(15u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(17u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[51u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(21u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(11u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[52u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(6u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(26u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[53u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(10u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(22u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[54u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(15u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(17u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[55u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(21u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(11u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[56u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(6u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(26u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[57u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(10u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(22u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[58u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(15u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(17u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[59u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(21u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(11u32)
    );
  abcd[1u32 as usize] = v;
  let va: u32 = abcd[0u32 as usize];
  let vb: u32 = abcd[1u32 as usize];
  let vc: u32 = abcd[2u32 as usize];
  let vd: u32 = abcd[3u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[60u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(6u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(26u32)
    );
  abcd[0u32 as usize] = v;
  let va: u32 = abcd[3u32 as usize];
  let vb: u32 = abcd[0u32 as usize];
  let vc: u32 = abcd[1u32 as usize];
  let vd: u32 = abcd[2u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[61u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(10u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(22u32)
    );
  abcd[3u32 as usize] = v;
  let va: u32 = abcd[2u32 as usize];
  let vb: u32 = abcd[3u32 as usize];
  let vc: u32 = abcd[0u32 as usize];
  let vd: u32 = abcd[1u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[62u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(15u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(17u32)
    );
  abcd[2u32 as usize] = v;
  let va: u32 = abcd[1u32 as usize];
  let vb: u32 = abcd[2u32 as usize];
  let vc: u32 = abcd[3u32 as usize];
  let vd: u32 = abcd[0u32 as usize];
  let b: (&mut [u8], &mut [u8]) = b.1.split_at_mut(0usize);
  let u: u32 = crate::lowstar::endianness::load32_le(b.1);
  let xk: u32 = u;
  let ti: u32 = (&mut _t)[63u32 as usize];
  let v: u32 =
    vb.wrapping_add(
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shl(21u32)
      |
      va.wrapping_add(vc ^ (vb | ! vd)).wrapping_add(xk).wrapping_add(ti).wrapping_shr(11u32)
    );
  abcd[1u32 as usize] = v;
  let a: u32 = abcd[0u32 as usize];
  let b: u32 = abcd[1u32 as usize];
  let c: u32 = abcd[2u32 as usize];
  let d: u32 = abcd[3u32 as usize];
  abcd[0u32 as usize] = a.wrapping_add(aa);
  abcd[1u32 as usize] = b.wrapping_add(bb);
  abcd[2u32 as usize] = c.wrapping_add(cc);
  abcd[3u32 as usize] = d.wrapping_add(dd)
}

fn legacy_pad(len: u64, dst: &mut [u8]) -> ()
{
  let dst1: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
  dst1.1[0u32 as usize] = 0x80u8;
  let dst2: (&mut [u8], &mut [u8]) = dst1.1.split_at_mut(1usize);
  for
  i
  in
  0u32..128u32.wrapping_sub(9u32.wrapping_add(dst.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
    64u32
  )
  { dst2.1[i as usize] = 0u8 };
  let dst3: (&mut [u8], &mut [u8]) =
    dst2.1.split_at_mut(
      (128u32.wrapping_sub(9u32.wrapping_add(len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
        64u32
      )
      as
      usize).wrapping_add(0usize)
    );
  crate::lowstar::endianness::store64_le(dst3.1, len.wrapping_shl(3u32))
}

pub fn legacy_finish(s: &mut [u32], dst: &mut [u8]) -> ()
for i in 0u32..4u32
{
  crate::lowstar::endianness::store32_le(
    &mut dst[i.wrapping_mul(4u32) as usize..],
    (&mut s[0u32 as usize..])[i as usize]
  )
}

pub fn legacy_update_multi(s: &mut [u32], blocks: &mut [u8], n_blocks: u32) -> ()
for i in 0u32..i
{
  let sz: u32 = 64u32;
  let block: (&mut [u8], &mut [u8]) =
    blocks.split_at_mut((sz.wrapping_mul(i) as usize).wrapping_add(0usize));
  legacy_update(s, block.1)
}

pub fn legacy_update_last(s: &mut [u32], prev_len: u64, input: &mut [u8], input_len: u32) -> ()
{
  let blocks_n: u32 = input_len.wrapping_div(64u32);
  let blocks_len: u32 = blocks_n.wrapping_mul(64u32);
  let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
  let rest_len: u32 = input_len.wrapping_sub(blocks_len);
  let rest: (&mut [u8], &mut [u8]) =
    blocks.1.split_at_mut((blocks_len as usize).wrapping_add(0usize));
  legacy_update_multi(s, rest.0, blocks_n);
  let total_input_len: u64 = prev_len.wrapping_add(input_len as u64);
  let pad_len: u32 =
    1u32.wrapping_add(
      128u32.wrapping_sub(9u32.wrapping_add(total_input_len.wrapping_rem(64u32 as u64) as u32)).wrapping_rem(
        64u32
      )
    ).wrapping_add(8u32);
  let tmp_len: u32 = rest_len.wrapping_add(pad_len);
  let mut tmp_twoblocks: [u8; 128] = [0u8; 128u32 as usize];
  let tmp: (&mut [u8], &mut [u8]) = (&mut tmp_twoblocks).split_at_mut(0usize);
  let tmp_rest: (&mut [u8], &mut [u8]) = tmp.1.split_at_mut(0usize);
  let tmp_pad: (&mut [u8], &mut [u8]) =
    tmp_rest.1.split_at_mut((rest_len as usize).wrapping_add(0usize));
  (tmp_pad.0[0u32 as usize..0u32 as usize + rest_len as usize]).copy_from_slice(
    &rest.1[0u32 as usize..0u32 as usize + rest_len as usize]
  );
  legacy_pad(total_input_len, tmp_pad.1);
  legacy_update_multi(s, tmp_pad.0, tmp_len.wrapping_div(64u32))
}

pub fn legacy_hash(input: &mut [u8], input_len: u32, dst: &mut [u8]) -> ()
{
  let mut s: [u32; 4] = [0x67452301u32, 0xefcdab89u32, 0x98badcfeu32, 0x10325476u32];
  let blocks_n: u32 = input_len.wrapping_div(64u32);
  let blocks_n1: u32 =
    if input_len.wrapping_rem(64u32) == 0u32 && blocks_n > 0u32
    { blocks_n.wrapping_sub(1u32) }
    else
    { blocks_n };
  let blocks_len: u32 = blocks_n1.wrapping_mul(64u32);
  let blocks: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
  let rest_len: u32 = input_len.wrapping_sub(blocks_len);
  let rest: (&mut [u8], &mut [u8]) =
    blocks.1.split_at_mut((blocks_len as usize).wrapping_add(0usize));
  let blocks_n: u32 = blocks_n1;
  let blocks_len: u32 = blocks_len;
  let blocks: &mut [u8] = rest.0;
  let rest_len: u32 = rest_len;
  let rest: &mut [u8] = rest.1;
  legacy_update_multi(&mut s, blocks, blocks_n);
  legacy_update_last(&mut s, blocks_len as u64, rest, rest_len);
  legacy_finish(&mut s, dst)
}

pub fn op_Bang_Star__Hacl_Streaming_Functor_state_s  uint32_t* ()(
  p: &mut [crate::hacl::streaming::md::state_32]
) ->
  crate::hacl::streaming::md::state_32
{ p[0u32 as usize] }

pub fn op_Star_Equals__Hacl_Streaming_Functor_state_s  uint32_t* ()(
  p: &mut [crate::hacl::streaming::md::state_32],
  v: crate::hacl::streaming::md::state_32
) ->
  ()
{ p[0u32 as usize] = v }

pub fn legacy_hash(input: &mut [u8], input_len: u32, dst: &mut [u8]) -> ()
{ legacy_hash(input, input_len, dst) }