pub fn shake128_4x(
  input_len: u32,
  input0: &mut [u8],
  input1: &mut [u8],
  input2: &mut [u8],
  input3: &mut [u8],
  output_len: u32,
  output0: &mut [u8],
  output1: &mut [u8],
  output2: &mut [u8],
  output3: &mut [u8]
) ->
  ()
{
  crate::hacl::hash_sha3::shake128_hacl(input_len, input0, output_len, output0);
  crate::hacl::hash_sha3::shake128_hacl(input_len, input1, output_len, output1);
  crate::hacl::hash_sha3::shake128_hacl(input_len, input2, output_len, output2);
  crate::hacl::hash_sha3::shake128_hacl(input_len, input3, output_len, output3)
}

pub fn mod_pow2(n1: u32, n2: u32, logq: u32, a: &mut [u16]) -> ()
if logq < 16u32
for i in 0u32..n2
for i in 0u32..logq
{
  a[i.wrapping_mul(n2).wrapping_add(i) as usize] =
    a[i.wrapping_mul(n2).wrapping_add(i) as usize] & 1u16.wrapping_shl(logq).wrapping_sub(1u16)
}

pub fn matrix_add(n1: u32, n2: u32, a: &mut [u16], b: &mut [u16]) -> ()
for i in 0u32..n2
for i in 0u32..a
{
  a[i.wrapping_mul(n2).wrapping_add(i) as usize] =
    (a[i.wrapping_mul(n2).wrapping_add(i) as usize]).wrapping_add(
      b[i.wrapping_mul(n2).wrapping_add(i) as usize]
    )
}

pub fn matrix_sub(n1: u32, n2: u32, a: &mut [u16], b: &mut [u16]) -> ()
for i in 0u32..n2
for i in 0u32..a
{
  b[i.wrapping_mul(n2).wrapping_add(i) as usize] =
    (a[i.wrapping_mul(n2).wrapping_add(i) as usize]).wrapping_sub(
      b[i.wrapping_mul(n2).wrapping_add(i) as usize]
    )
}

pub fn matrix_mul(n1: u32, n2: u32, n3: u32, a: &mut [u16], b: &mut [u16], c: &mut [u16]) -> ()
for i in 0u32..n2
for i in 0u32..a
{
  let mut res: u16 = 0u16;
  for i in 0u32..n3
  {
    let aij: u16 = a[i.wrapping_mul(n2).wrapping_add(i) as usize];
    let bjk: u16 = b[i.wrapping_mul(n3).wrapping_add(i) as usize];
    let res0: u16 = res;
    res = res0.wrapping_add(aij.wrapping_mul(bjk))
  };
  c[i.wrapping_mul(n3).wrapping_add(i) as usize] = res
}

pub fn matrix_mul_s(n1: u32, n2: u32, n3: u32, a: &mut [u16], b: &mut [u16], c: &mut [u16]) ->
  ()
for i in 0u32..n2
for i in 0u32..a
{
  let mut res: u16 = 0u16;
  for i in 0u32..n3
  {
    let aij: u16 = a[i.wrapping_mul(n2).wrapping_add(i) as usize];
    let bjk: u16 = b[i.wrapping_mul(n2).wrapping_add(i) as usize];
    let res0: u16 = res;
    res = res0.wrapping_add(aij.wrapping_mul(bjk))
  };
  c[i.wrapping_mul(n3).wrapping_add(i) as usize] = res
}

pub fn matrix_eq(n1: u32, n2: u32, a: &mut [u16], b: &mut [u16]) -> u16
{
  let mut res: u16 = 0xFFFFu16;
  for i in 0u32..n2.wrapping_mul(a)
  {
    let uu____0: u16 = crate::fstar::uint16::eq_mask(a[i as usize], b[i as usize]);
    res = uu____0 & res
  };
  let r: u16 = res;
  r
}

pub fn matrix_to_lbytes(n1: u32, n2: u32, m: &mut [u16], res: &mut [u8]) -> ()
for i in 0u32..n2.wrapping_mul(m)
{
  crate::lowstar::endianness::store16_le(
    &mut res[2u32.wrapping_mul(i) as usize..],
    m[i as usize]
  )
}

pub fn matrix_from_lbytes(n1: u32, n2: u32, b: &mut [u8], res: &mut [u16]) -> ()
for i in 0u32..n2.wrapping_mul(b)
{
  let os: (&mut [u16], &mut [u16]) = res.split_at_mut(0usize);
  let u: u16 = crate::lowstar::endianness::load16_le(&mut b[2u32.wrapping_mul(i) as usize..]);
  let x: u16 = u;
  os.1[i as usize] = x
}

pub const cdf_table640: [u16; 13] =
  [4643u16,
    13363u16,
    20579u16,
    25843u16,
    29227u16,
    31145u16,
    32103u16,
    32525u16,
    32689u16,
    32745u16,
    32762u16,
    32766u16,
    32767u16];

pub const cdf_table976: [u16; 11] =
  [5638u16,
    15915u16,
    23689u16,
    28571u16,
    31116u16,
    32217u16,
    32613u16,
    32731u16,
    32760u16,
    32766u16,
    32767u16];

pub const cdf_table1344: [u16; 7] =
  [9142u16, 23462u16, 30338u16, 32361u16, 32725u16, 32765u16, 32767u16];

pub fn frodo_pack(n1: u32, n2: u32, d: u32, a: &mut [u16], res: &mut [u8]) -> ()
{
  let n: u32 = n1.wrapping_mul(n2).wrapping_div(8u32);
  for i in 0u32..i
  {
    let a1: (&mut [u16], &mut [u16]) =
      a.split_at_mut((8u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    let r: (&mut [u8], &mut [u8]) =
      res.split_at_mut((d.wrapping_mul(i) as usize).wrapping_add(0usize));
    let maskd: u16 = (1u32.wrapping_shl(d) as u16).wrapping_sub(1u16);
    let mut v16: [u8; 16] = [0u8; 16u32 as usize];
    let a0: u16 = a1.1[0u32 as usize] & maskd;
    let a11: u16 = a1.1[1u32 as usize] & maskd;
    let a2: u16 = a1.1[2u32 as usize] & maskd;
    let a3: u16 = a1.1[3u32 as usize] & maskd;
    let a4: u16 = a1.1[4u32 as usize] & maskd;
    let a5: u16 = a1.1[5u32 as usize] & maskd;
    let a6: u16 = a1.1[6u32 as usize] & maskd;
    let a7: u16 = a1.1[7u32 as usize] & maskd;
    let templong: crate::fstar::uint128::uint128 =
      crate::fstar::uint128::logor(
        crate::fstar::uint128::logor(
          crate::fstar::uint128::logor(
            crate::fstar::uint128::logor(
              crate::fstar::uint128::logor(
                crate::fstar::uint128::logor(
                  crate::fstar::uint128::logor(
                    crate::fstar::uint128::shift_left(
                      crate::fstar::uint128::uint64_to_uint128(a0 as u64),
                      7u32.wrapping_mul(d)
                    ),
                    crate::fstar::uint128::shift_left(
                      crate::fstar::uint128::uint64_to_uint128(a11 as u64),
                      6u32.wrapping_mul(d)
                    )
                  ),
                  crate::fstar::uint128::shift_left(
                    crate::fstar::uint128::uint64_to_uint128(a2 as u64),
                    5u32.wrapping_mul(d)
                  )
                ),
                crate::fstar::uint128::shift_left(
                  crate::fstar::uint128::uint64_to_uint128(a3 as u64),
                  4u32.wrapping_mul(d)
                )
              ),
              crate::fstar::uint128::shift_left(
                crate::fstar::uint128::uint64_to_uint128(a4 as u64),
                3u32.wrapping_mul(d)
              )
            ),
            crate::fstar::uint128::shift_left(
              crate::fstar::uint128::uint64_to_uint128(a5 as u64),
              2u32.wrapping_mul(d)
            )
          ),
          crate::fstar::uint128::shift_left(
            crate::fstar::uint128::uint64_to_uint128(a6 as u64),
            1u32.wrapping_mul(d)
          )
        ),
        crate::fstar::uint128::shift_left(
          crate::fstar::uint128::uint64_to_uint128(a7 as u64),
          0u32.wrapping_mul(d)
        )
      );
    crate::lowstar::endianness::store128_be(&mut v16, templong);
    let src: (&mut [u8], &mut [u8]) =
      (&mut v16).split_at_mut((16u32.wrapping_sub(d) as usize).wrapping_add(0usize));
    (r.1[0u32 as usize..0u32 as usize + d as usize]).copy_from_slice(
      &src.1[0u32 as usize..0u32 as usize + d as usize]
    )
  }
}

pub fn frodo_unpack(n1: u32, n2: u32, d: u32, b: &mut [u8], res: &mut [u16]) -> ()
{
  let n: u32 = n1.wrapping_mul(n2).wrapping_div(8u32);
  for i in 0u32..i
  {
    let b1: (&mut [u8], &mut [u8]) =
      b.split_at_mut((d.wrapping_mul(i) as usize).wrapping_add(0usize));
    let r: (&mut [u16], &mut [u16]) =
      res.split_at_mut((8u32.wrapping_mul(i) as usize).wrapping_add(0usize));
    let maskd: u16 = (1u32.wrapping_shl(d) as u16).wrapping_sub(1u16);
    let mut src: [u8; 16] = [0u8; 16u32 as usize];
    ((&mut src)[16u32.wrapping_sub(d) as usize..16u32.wrapping_sub(d) as usize + d as usize]).copy_from_slice(
      &b1.1[0u32 as usize..0u32 as usize + d as usize]
    );
    let u: crate::fstar::uint128::uint128 = crate::lowstar::endianness::load128_be(&mut src);
    let templong: crate::fstar::uint128::uint128 = u;
    r.1[0u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 7u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[1u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 6u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[2u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 5u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[3u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 4u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[4u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 3u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[5u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 2u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[6u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 1u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd;
    r.1[7u32 as usize] =
      crate::fstar::uint128::uint128_to_uint64(
        crate::fstar::uint128::shift_right(templong, 0u32.wrapping_mul(d))
      )
      as
      u16
      &
      maskd
  }
}

pub fn frodo_key_encode(logq: u32, b: u32, n: u32, a: &mut [u8], res: &mut [u16]) -> ()
for i in 0u32..a
{
  let mut v8: [u8; 8] = [0u8; 8u32 as usize];
  let chunk: (&mut [u8], &mut [u8]) =
    a.split_at_mut((i.wrapping_mul(b) as usize).wrapping_add(0usize));
  ((&mut v8)[0u32 as usize..0u32 as usize + b as usize]).copy_from_slice(
    &chunk.1[0u32 as usize..0u32 as usize + b as usize]
  );
  let u: u64 = crate::lowstar::endianness::load64_le(&mut v8);
  let x: u64 = u;
  let x: u64 = x;
  for i in 0u32..8u32
  {
    let rk: u64 = x.wrapping_shr(b.wrapping_mul(i)) & 1u64.wrapping_shl(b).wrapping_sub(1u64);
    res[i.wrapping_mul(n).wrapping_add(i) as usize] =
      (rk as u16).wrapping_shl(logq.wrapping_sub(b))
  }
}

pub fn frodo_key_decode(logq: u32, b: u32, n: u32, a: &mut [u16], res: &mut [u8]) -> ()
for i in 0u32..a
{
  let mut templong: u64 = 0u64;
  for i in 0u32..8u32
  {
    let aik: u16 = a[i.wrapping_mul(n).wrapping_add(i) as usize];
    let res1: u16 =
      aik.wrapping_add(1u16.wrapping_shl(logq.wrapping_sub(b).wrapping_sub(1u32))).wrapping_shr(
        logq.wrapping_sub(b)
      );
    templong =
      templong
      |
      ((res1 & 1u16.wrapping_shl(b).wrapping_sub(1u16)) as u64).wrapping_shl(b.wrapping_mul(i))
  };
  let templong: u64 = templong;
  let mut v8: [u8; 8] = [0u8; 8u32 as usize];
  crate::lowstar::endianness::store64_le(&mut v8, templong);
  let tmp: (&mut [u8], &mut [u8]) = (&mut v8).split_at_mut(0usize);
  (res[i.wrapping_mul(b) as usize..i.wrapping_mul(b) as usize + b as usize]).copy_from_slice(
    &tmp.1[0u32 as usize..0u32 as usize + b as usize]
  )
}