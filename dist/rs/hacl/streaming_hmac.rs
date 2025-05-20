#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[derive(PartialEq, Clone, Copy)]
pub enum r#impl
{
    MD5,
    SHA1,
    SHA2_224,
    SHA2_256,
    SHA2_384,
    SHA2_512,
    SHA3_224,
    SHA3_256,
    SHA3_384,
    SHA3_512,
    Blake2S_32,
    Blake2S_128,
    Blake2B_32,
    Blake2B_256
}

fn alg_of_impl(i: crate::streaming_hmac::r#impl) -> crate::streaming_types::hash_alg
{
    match i
    {
        crate::streaming_hmac::r#impl::MD5 => crate::streaming_types::hash_alg::MD5,
        crate::streaming_hmac::r#impl::SHA1 => crate::streaming_types::hash_alg::SHA1,
        crate::streaming_hmac::r#impl::SHA2_224 => crate::streaming_types::hash_alg::SHA2_224,
        crate::streaming_hmac::r#impl::SHA2_256 => crate::streaming_types::hash_alg::SHA2_256,
        crate::streaming_hmac::r#impl::SHA2_384 => crate::streaming_types::hash_alg::SHA2_384,
        crate::streaming_hmac::r#impl::SHA2_512 => crate::streaming_types::hash_alg::SHA2_512,
        crate::streaming_hmac::r#impl::SHA3_224 => crate::streaming_types::hash_alg::SHA3_224,
        crate::streaming_hmac::r#impl::SHA3_256 => crate::streaming_types::hash_alg::SHA3_256,
        crate::streaming_hmac::r#impl::SHA3_384 => crate::streaming_types::hash_alg::SHA3_384,
        crate::streaming_hmac::r#impl::SHA3_512 => crate::streaming_types::hash_alg::SHA3_512,
        crate::streaming_hmac::r#impl::Blake2S_32 => crate::streaming_types::hash_alg::Blake2S,
        crate::streaming_hmac::r#impl::Blake2S_128 => crate::streaming_types::hash_alg::Blake2S,
        crate::streaming_hmac::r#impl::Blake2B_32 => crate::streaming_types::hash_alg::Blake2B,
        crate::streaming_hmac::r#impl::Blake2B_256 => crate::streaming_types::hash_alg::Blake2B,
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[derive(PartialEq, Clone, Copy)]
enum state_s_tags
{
    MD5_a,
    SHA1_a,
    SHA2_224_a,
    SHA2_256_a,
    SHA2_384_a,
    SHA2_512_a,
    SHA3_224_a,
    SHA3_256_a,
    SHA3_384_a,
    SHA3_512_a,
    Blake2S_a,
    Blake2S_128_a,
    Blake2B_a,
    Blake2B_256_a
}

#[derive(PartialEq, Clone)]
pub enum state_s
{
    MD5_a { p: Box<[u32]> },
    SHA1_a { p: Box<[u32]> },
    SHA2_224_a { p: Box<[u32]> },
    SHA2_256_a { p: Box<[u32]> },
    SHA2_384_a { p: Box<[u64]> },
    SHA2_512_a { p: Box<[u64]> },
    SHA3_224_a { p: Box<[u64]> },
    SHA3_256_a { p: Box<[u64]> },
    SHA3_384_a { p: Box<[u64]> },
    SHA3_512_a { p: Box<[u64]> },
    Blake2S_a { p: Box<[u32]> },
    Blake2S_128_a { p: Box<[lib::intvector_intrinsics::vec128]> },
    Blake2B_a { p: Box<[u64]> },
    Blake2B_256_a { p: Box<[lib::intvector_intrinsics::vec256]> }
}

fn impl_of_state_s(s: crate::streaming_hmac::state_s) -> crate::streaming_hmac::r#impl
{
    match s
    {
        crate::streaming_hmac::state_s::MD5_a { .. } => crate::streaming_hmac::r#impl::MD5,
        crate::streaming_hmac::state_s::SHA1_a { .. } => crate::streaming_hmac::r#impl::SHA1,
        crate::streaming_hmac::state_s::SHA2_224_a { .. } => crate::streaming_hmac::r#impl::SHA2_224,
        crate::streaming_hmac::state_s::SHA2_256_a { .. } => crate::streaming_hmac::r#impl::SHA2_256,
        crate::streaming_hmac::state_s::SHA2_384_a { .. } => crate::streaming_hmac::r#impl::SHA2_384,
        crate::streaming_hmac::state_s::SHA2_512_a { .. } => crate::streaming_hmac::r#impl::SHA2_512,
        crate::streaming_hmac::state_s::SHA3_224_a { .. } => crate::streaming_hmac::r#impl::SHA3_224,
        crate::streaming_hmac::state_s::SHA3_256_a { .. } => crate::streaming_hmac::r#impl::SHA3_256,
        crate::streaming_hmac::state_s::SHA3_384_a { .. } => crate::streaming_hmac::r#impl::SHA3_384,
        crate::streaming_hmac::state_s::SHA3_512_a { .. } => crate::streaming_hmac::r#impl::SHA3_512,
        crate::streaming_hmac::state_s::Blake2S_a { .. } =>
          crate::streaming_hmac::r#impl::Blake2S_32,
        crate::streaming_hmac::state_s::Blake2S_128_a { .. } =>
          crate::streaming_hmac::r#impl::Blake2S_128,
        crate::streaming_hmac::state_s::Blake2B_a { .. } =>
          crate::streaming_hmac::r#impl::Blake2B_32,
        crate::streaming_hmac::state_s::Blake2B_256_a { .. } =>
          crate::streaming_hmac::r#impl::Blake2B_256,
        _ => panic!("Incomplete pattern matching")
    }
}

fn impl_of_state(s: &[crate::streaming_hmac::state_s]) -> crate::streaming_hmac::r#impl
{ crate::streaming_hmac::impl_of_state_s(s[0usize]) }

fn init(s: &[crate::streaming_hmac::state_s])
{
    match s[0usize]
    {
        crate::streaming_hmac::state_s::MD5_a { p: ref mut p1 } => crate::hash_md5::init(p1),
        crate::streaming_hmac::state_s::SHA1_a { p: ref mut p1 } => crate::hash_sha1::init(p1),
        crate::streaming_hmac::state_s::SHA2_224_a { p: ref mut p1 } =>
          crate::hash_sha2::sha224_init(p1),
        crate::streaming_hmac::state_s::SHA2_256_a { p: ref mut p1 } =>
          crate::hash_sha2::sha256_init(p1),
        crate::streaming_hmac::state_s::SHA2_384_a { p: ref mut p1 } =>
          crate::hash_sha2::sha384_init(p1),
        crate::streaming_hmac::state_s::SHA2_512_a { p: ref mut p1 } =>
          crate::hash_sha2::sha512_init(p1),
        crate::streaming_hmac::state_s::SHA3_224_a { p: ref mut p1 } =>
          crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_224, p1),
        crate::streaming_hmac::state_s::SHA3_256_a { p: ref mut p1 } =>
          crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_256, p1),
        crate::streaming_hmac::state_s::SHA3_384_a { p: ref mut p1 } =>
          crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_384, p1),
        crate::streaming_hmac::state_s::SHA3_512_a { p: ref mut p1 } =>
          crate::hash_sha3::init_(crate::streaming_types::hash_alg::SHA3_512, p1),
        crate::streaming_hmac::state_s::Blake2S_a { p: ref mut p1 } =>
          crate::hash_blake2s::init(p1, 0u32, 32u32),
        crate::streaming_hmac::state_s::Blake2S_128_a { p: ref mut p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec128
          { crate::hash_blake2s_simd128::init(p1, 0u32, 32u32) }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec128]>(p1) },
        crate::streaming_hmac::state_s::Blake2B_a { p: ref mut p1 } =>
          crate::hash_blake2b::init(p1, 0u32, 64u32),
        crate::streaming_hmac::state_s::Blake2B_256_a { p: ref mut p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec256
          { crate::hash_blake2b_simd256::init(p1, 0u32, 64u32) }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec256]>(p1) },
        _ => panic!("Incomplete pattern matching")
    }
}

fn update_multi(s: &[crate::streaming_hmac::state_s], prevlen: u64, blocks: &[u8], len: u32)
{
    match s[0usize]
    {
        crate::streaming_hmac::state_s::MD5_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(64u32);
              crate::hash_md5::update_multi(p1, blocks, n)
          },
        crate::streaming_hmac::state_s::SHA1_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(64u32);
              crate::hash_sha1::update_multi(p1, blocks, n)
          },
        crate::streaming_hmac::state_s::SHA2_224_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(64u32);
              crate::hash_sha2::sha224_update_nblocks(n.wrapping_mul(64u32), blocks, p1)
          },
        crate::streaming_hmac::state_s::SHA2_256_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(64u32);
              crate::hash_sha2::sha256_update_nblocks(n.wrapping_mul(64u32), blocks, p1)
          },
        crate::streaming_hmac::state_s::SHA2_384_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(128u32);
              crate::hash_sha2::sha384_update_nblocks(n.wrapping_mul(128u32), blocks, p1)
          },
        crate::streaming_hmac::state_s::SHA2_512_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(128u32);
              crate::hash_sha2::sha512_update_nblocks(n.wrapping_mul(128u32), blocks, p1)
          },
        crate::streaming_hmac::state_s::SHA3_224_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(144u32);
              crate::hash_sha3::update_multi_sha3(
                  crate::streaming_types::hash_alg::SHA3_224,
                  p1,
                  blocks,
                  n
              )
          },
        crate::streaming_hmac::state_s::SHA3_256_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(136u32);
              crate::hash_sha3::update_multi_sha3(
                  crate::streaming_types::hash_alg::SHA3_256,
                  p1,
                  blocks,
                  n
              )
          },
        crate::streaming_hmac::state_s::SHA3_384_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(104u32);
              crate::hash_sha3::update_multi_sha3(
                  crate::streaming_types::hash_alg::SHA3_384,
                  p1,
                  blocks,
                  n
              )
          },
        crate::streaming_hmac::state_s::SHA3_512_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(72u32);
              crate::hash_sha3::update_multi_sha3(
                  crate::streaming_types::hash_alg::SHA3_512,
                  p1,
                  blocks,
                  n
              )
          },
        crate::streaming_hmac::state_s::Blake2S_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(64u32);
              let mut wv: [u32; 16] = [0u32; 16usize];
              crate::hash_blake2s::update_multi(
                  n.wrapping_mul(64u32),
                  &mut wv,
                  p1,
                  prevlen,
                  blocks,
                  n
              )
          },
        crate::streaming_hmac::state_s::Blake2S_128_a { p: ref mut p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec128
          {
              let n: u32 = len.wrapping_div(64u32);
              crate::hash_blake2s_simd128::update_multi_no_inline(p1, prevlen, blocks, n)
          }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec128]>(p1) },
        crate::streaming_hmac::state_s::Blake2B_a { p: ref mut p1 } =>
          {
              let n: u32 = len.wrapping_div(128u32);
              let mut wv: [u64; 16] = [0u64; 16usize];
              crate::hash_blake2b::update_multi(
                  n.wrapping_mul(128u32),
                  &mut wv,
                  p1,
                  fstar::uint128::uint64_to_uint128(prevlen),
                  blocks,
                  n
              )
          },
        crate::streaming_hmac::state_s::Blake2B_256_a { p: ref mut p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec256
          {
              let n: u32 = len.wrapping_div(128u32);
              crate::hash_blake2b_simd256::update_multi_no_inline(
                  p1,
                  fstar::uint128::uint64_to_uint128(prevlen),
                  blocks,
                  n
              )
          }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec256]>(p1) },
        _ => panic!("Incomplete pattern matching")
    }
}

fn update_last(s: &[crate::streaming_hmac::state_s], prev_len: u64, last: &[u8], last_len: u32)
{
    match s[0usize]
    {
        crate::streaming_hmac::state_s::MD5_a { p: ref mut p1 } =>
          crate::hash_md5::update_last(p1, prev_len, last, last_len),
        crate::streaming_hmac::state_s::SHA1_a { p: ref mut p1 } =>
          crate::hash_sha1::update_last(p1, prev_len, last, last_len),
        crate::streaming_hmac::state_s::SHA2_224_a { p: ref mut p1 } =>
          crate::hash_sha2::sha224_update_last(
              prev_len.wrapping_add(last_len as u64),
              last_len,
              last,
              p1
          ),
        crate::streaming_hmac::state_s::SHA2_256_a { p: ref mut p1 } =>
          crate::hash_sha2::sha256_update_last(
              prev_len.wrapping_add(last_len as u64),
              last_len,
              last,
              p1
          ),
        crate::streaming_hmac::state_s::SHA2_384_a { p: ref mut p1 } =>
          crate::hash_sha2::sha384_update_last(
              fstar::uint128::add(
                  fstar::uint128::uint64_to_uint128(prev_len),
                  fstar::uint128::uint64_to_uint128(last_len as u64)
              ),
              last_len,
              last,
              p1
          ),
        crate::streaming_hmac::state_s::SHA2_512_a { p: ref mut p1 } =>
          crate::hash_sha2::sha512_update_last(
              fstar::uint128::add(
                  fstar::uint128::uint64_to_uint128(prev_len),
                  fstar::uint128::uint64_to_uint128(last_len as u64)
              ),
              last_len,
              last,
              p1
          ),
        crate::streaming_hmac::state_s::SHA3_224_a { p: ref mut p1 } =>
          crate::hash_sha3::update_last_sha3(
              crate::streaming_types::hash_alg::SHA3_224,
              p1,
              last,
              last_len
          ),
        crate::streaming_hmac::state_s::SHA3_256_a { p: ref mut p1 } =>
          crate::hash_sha3::update_last_sha3(
              crate::streaming_types::hash_alg::SHA3_256,
              p1,
              last,
              last_len
          ),
        crate::streaming_hmac::state_s::SHA3_384_a { p: ref mut p1 } =>
          crate::hash_sha3::update_last_sha3(
              crate::streaming_types::hash_alg::SHA3_384,
              p1,
              last,
              last_len
          ),
        crate::streaming_hmac::state_s::SHA3_512_a { p: ref mut p1 } =>
          crate::hash_sha3::update_last_sha3(
              crate::streaming_types::hash_alg::SHA3_512,
              p1,
              last,
              last_len
          ),
        crate::streaming_hmac::state_s::Blake2S_a { p: ref mut p1 } =>
          {
              let mut wv: [u32; 16] = [0u32; 16usize];
              crate::hash_blake2s::update_last(
                  last_len,
                  &mut wv,
                  p1,
                  false,
                  prev_len,
                  last_len,
                  last
              )
          },
        crate::streaming_hmac::state_s::Blake2S_128_a { p: ref mut p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec128
          { crate::hash_blake2s_simd128::update_last_no_inline(p1, prev_len, last, last_len) }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec128]>(p1) },
        crate::streaming_hmac::state_s::Blake2B_a { p: ref mut p1 } =>
          {
              let mut wv: [u64; 16] = [0u64; 16usize];
              crate::hash_blake2b::update_last(
                  last_len,
                  &mut wv,
                  p1,
                  false,
                  fstar::uint128::uint64_to_uint128(prev_len),
                  last_len,
                  last
              )
          },
        crate::streaming_hmac::state_s::Blake2B_256_a { p: ref mut p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec256
          {
              crate::hash_blake2b_simd256::update_last_no_inline(
                  p1,
                  fstar::uint128::uint64_to_uint128(prev_len),
                  last,
                  last_len
              )
          }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec256]>(p1) },
        _ => panic!("Incomplete pattern matching")
    }
}

fn finish(s: &[crate::streaming_hmac::state_s], dst: &mut [u8])
{
    match s[0usize]
    {
        crate::streaming_hmac::state_s::MD5_a { p: ref p1 } => crate::hash_md5::finish(p1, dst),
        crate::streaming_hmac::state_s::SHA1_a { p: ref p1 } => crate::hash_sha1::finish(p1, dst),
        crate::streaming_hmac::state_s::SHA2_224_a { p: ref p1 } =>
          crate::hash_sha2::sha224_finish(p1, dst),
        crate::streaming_hmac::state_s::SHA2_256_a { p: ref p1 } =>
          crate::hash_sha2::sha256_finish(p1, dst),
        crate::streaming_hmac::state_s::SHA2_384_a { p: ref p1 } =>
          crate::hash_sha2::sha384_finish(p1, dst),
        crate::streaming_hmac::state_s::SHA2_512_a { p: ref p1 } =>
          crate::hash_sha2::sha512_finish(p1, dst),
        crate::streaming_hmac::state_s::SHA3_224_a { p: ref mut p1 } =>
          {
              let remOut: u32 = 28u32;
              let mut hbuf: [u8; 256] = [0u8; 256usize];
              let mut ws: [u64; 32] = [0u64; 32usize];
              ((&mut ws)[0usize..25usize]).copy_from_slice(&p1[0usize..25usize]);
              krml::unroll_for!(
                  32,
                  "i",
                  0u32,
                  1u32,
                  lowstar::endianness::store64_le(
                      &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
                      (&ws)[i as usize]
                  )
              );
              (dst[28u32.wrapping_sub(remOut) as usize..28u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize])
          },
        crate::streaming_hmac::state_s::SHA3_256_a { p: ref mut p1 } =>
          {
              let remOut: u32 = 32u32;
              let mut hbuf: [u8; 256] = [0u8; 256usize];
              let mut ws: [u64; 32] = [0u64; 32usize];
              ((&mut ws)[0usize..25usize]).copy_from_slice(&p1[0usize..25usize]);
              krml::unroll_for!(
                  32,
                  "i",
                  0u32,
                  1u32,
                  lowstar::endianness::store64_le(
                      &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
                      (&ws)[i as usize]
                  )
              );
              (dst[32u32.wrapping_sub(remOut) as usize..32u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize])
          },
        crate::streaming_hmac::state_s::SHA3_384_a { p: ref mut p1 } =>
          {
              let remOut: u32 = 48u32;
              let mut hbuf: [u8; 256] = [0u8; 256usize];
              let mut ws: [u64; 32] = [0u64; 32usize];
              ((&mut ws)[0usize..25usize]).copy_from_slice(&p1[0usize..25usize]);
              krml::unroll_for!(
                  32,
                  "i",
                  0u32,
                  1u32,
                  lowstar::endianness::store64_le(
                      &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
                      (&ws)[i as usize]
                  )
              );
              (dst[48u32.wrapping_sub(remOut) as usize..48u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize])
          },
        crate::streaming_hmac::state_s::SHA3_512_a { p: ref mut p1 } =>
          {
              let remOut: u32 = 64u32;
              let mut hbuf: [u8; 256] = [0u8; 256usize];
              let mut ws: [u64; 32] = [0u64; 32usize];
              ((&mut ws)[0usize..25usize]).copy_from_slice(&p1[0usize..25usize]);
              krml::unroll_for!(
                  32,
                  "i",
                  0u32,
                  1u32,
                  lowstar::endianness::store64_le(
                      &mut (&mut hbuf)[i.wrapping_mul(8u32) as usize..],
                      (&ws)[i as usize]
                  )
              );
              (dst[64u32.wrapping_sub(remOut) as usize..64u32.wrapping_sub(remOut) as usize
              +
              remOut as usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..remOut as usize])
          },
        crate::streaming_hmac::state_s::Blake2S_a { p: ref p1 } =>
          crate::hash_blake2s::finish(32u32, dst, p1),
        crate::streaming_hmac::state_s::Blake2S_128_a { p: ref p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec128
          { crate::hash_blake2s_simd128::finish(32u32, dst, p1) }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec128]>(p1) },
        crate::streaming_hmac::state_s::Blake2B_a { p: ref p1 } =>
          crate::hash_blake2b::finish(64u32, dst, p1),
        crate::streaming_hmac::state_s::Blake2B_256_a { p: ref p1 } =>
          if evercrypt::targetconfig::hacl_can_compile_vec256
          { crate::hash_blake2b_simd256::finish(64u32, dst, p1) }
          else
          { lowstar::ignore::ignore::<&[lib::intvector_intrinsics::vec256]>(p1) },
        _ => panic!("Incomplete pattern matching")
    }
}

fn free_(s: &[crate::streaming_hmac::state_s])
{
    match s[0usize]
    {
        crate::streaming_hmac::state_s::MD5_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA1_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA2_224_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA2_256_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA2_384_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA2_512_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA3_224_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA3_256_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA3_384_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::SHA3_512_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::Blake2S_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::Blake2S_128_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::Blake2B_a { p: ref p1 } => (),
        crate::streaming_hmac::state_s::Blake2B_256_a { p: ref p1 } => (),
        _ => panic!("Incomplete pattern matching")
    }
}

fn copy(s_src: &[crate::streaming_hmac::state_s], mut s_dst: &[crate::streaming_hmac::state_s])
{
    match s_src[0usize]
    {
        crate::streaming_hmac::state_s::MD5_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u32] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::MD5_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..4usize]).copy_from_slice(&p_src[0usize..4usize])
          },
        crate::streaming_hmac::state_s::SHA1_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u32] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA1_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..5usize]).copy_from_slice(&p_src[0usize..5usize])
          },
        crate::streaming_hmac::state_s::SHA2_224_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u32] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA2_224_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..8usize]).copy_from_slice(&p_src[0usize..8usize])
          },
        crate::streaming_hmac::state_s::SHA2_256_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u32] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA2_256_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..8usize]).copy_from_slice(&p_src[0usize..8usize])
          },
        crate::streaming_hmac::state_s::SHA2_384_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA2_384_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..8usize]).copy_from_slice(&p_src[0usize..8usize])
          },
        crate::streaming_hmac::state_s::SHA2_512_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA2_512_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..8usize]).copy_from_slice(&p_src[0usize..8usize])
          },
        crate::streaming_hmac::state_s::SHA3_224_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA3_224_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..25usize]).copy_from_slice(&p_src[0usize..25usize])
          },
        crate::streaming_hmac::state_s::SHA3_256_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA3_256_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..25usize]).copy_from_slice(&p_src[0usize..25usize])
          },
        crate::streaming_hmac::state_s::SHA3_384_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA3_384_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..25usize]).copy_from_slice(&p_src[0usize..25usize])
          },
        crate::streaming_hmac::state_s::SHA3_512_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::SHA3_512_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..25usize]).copy_from_slice(&p_src[0usize..25usize])
          },
        crate::streaming_hmac::state_s::Blake2S_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u32] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::Blake2S_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..16usize]).copy_from_slice(&p_src[0usize..16usize])
          },
        crate::streaming_hmac::state_s::Blake2S_128_a { p: ref p_src } =>
          if evercrypt::targetconfig::hacl_can_compile_vec128
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [lib::intvector_intrinsics::vec128] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::Blake2S_128_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              crate::hash_blake2s_simd128::copy_internal_state(p_src, p_dst)
          },
        crate::streaming_hmac::state_s::Blake2B_a { p: ref p_src } =>
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [u64] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::Blake2B_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              (p_dst[0usize..16usize]).copy_from_slice(&p_src[0usize..16usize])
          },
        crate::streaming_hmac::state_s::Blake2B_256_a { p: ref p_src } =>
          if evercrypt::targetconfig::hacl_can_compile_vec256
          {
              let x1: &mut crate::streaming_hmac::state_s = &mut s_dst[0usize];
              let p_dst: &mut [lib::intvector_intrinsics::vec256] =
                  match *x1
                  {
                      crate::streaming_hmac::state_s::Blake2B_256_a { ref mut p } => p,
                      _ => panic!("Incomplete pattern matching")
                  };
              crate::hash_blake2b_simd256::copy_internal_state(p_src, p_dst)
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn hash(i: crate::streaming_hmac::r#impl, dst: &mut [u8], input: &[u8], input_len: u32)
{
    match i
    {
        crate::streaming_hmac::r#impl::MD5 => crate::hash_md5::hash_oneshot(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA1 => crate::hash_sha1::hash_oneshot(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA2_224 => crate::hash_sha2::hash_224(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA2_256 => crate::hash_sha2::hash_256(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA2_384 => crate::hash_sha2::hash_384(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA2_512 => crate::hash_sha2::hash_512(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA3_224 => crate::hash_sha3::sha3_224(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA3_256 => crate::hash_sha3::sha3_256(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA3_384 => crate::hash_sha3::sha3_384(dst, input, input_len),
        crate::streaming_hmac::r#impl::SHA3_512 => crate::hash_sha3::sha3_512(dst, input, input_len),
        crate::streaming_hmac::r#impl::Blake2S_32 =>
          crate::hash_blake2s::hash_with_key(dst, 32u32, input, input_len, &[], 0u32),
        crate::streaming_hmac::r#impl::Blake2S_128 =>
          if evercrypt::targetconfig::hacl_can_compile_vec128
          { crate::hash_blake2s_simd128::hash_with_key(dst, 32u32, input, input_len, &[], 0u32) },
        crate::streaming_hmac::r#impl::Blake2B_32 =>
          crate::hash_blake2b::hash_with_key(dst, 64u32, input, input_len, &[], 0u32),
        crate::streaming_hmac::r#impl::Blake2B_256 =>
          if evercrypt::targetconfig::hacl_can_compile_vec256
          { crate::hash_blake2b_simd256::hash_with_key(dst, 64u32, input, input_len, &[], 0u32) },
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub struct index
{ pub fst: crate::streaming_hmac::r#impl, pub snd: u32 }

fn hash_len(a: crate::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::streaming_types::hash_alg::MD5 => 16u32,
        crate::streaming_types::hash_alg::SHA1 => 20u32,
        crate::streaming_types::hash_alg::SHA2_224 => 28u32,
        crate::streaming_types::hash_alg::SHA2_256 => 32u32,
        crate::streaming_types::hash_alg::SHA2_384 => 48u32,
        crate::streaming_types::hash_alg::SHA2_512 => 64u32,
        crate::streaming_types::hash_alg::Blake2S => 32u32,
        crate::streaming_types::hash_alg::Blake2B => 64u32,
        crate::streaming_types::hash_alg::SHA3_224 => 28u32,
        crate::streaming_types::hash_alg::SHA3_256 => 32u32,
        crate::streaming_types::hash_alg::SHA3_384 => 48u32,
        crate::streaming_types::hash_alg::SHA3_512 => 64u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

fn block_len(a: crate::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::streaming_types::hash_alg::MD5 => 64u32,
        crate::streaming_types::hash_alg::SHA1 => 64u32,
        crate::streaming_types::hash_alg::SHA2_224 => 64u32,
        crate::streaming_types::hash_alg::SHA2_256 => 64u32,
        crate::streaming_types::hash_alg::SHA2_384 => 128u32,
        crate::streaming_types::hash_alg::SHA2_512 => 128u32,
        crate::streaming_types::hash_alg::SHA3_224 => 144u32,
        crate::streaming_types::hash_alg::SHA3_256 => 136u32,
        crate::streaming_types::hash_alg::SHA3_384 => 104u32,
        crate::streaming_types::hash_alg::SHA3_512 => 72u32,
        crate::streaming_types::hash_alg::Shake128 => 168u32,
        crate::streaming_types::hash_alg::Shake256 => 136u32,
        crate::streaming_types::hash_alg::Blake2S => 64u32,
        crate::streaming_types::hash_alg::Blake2B => 128u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

fn max_input_len64(a: crate::streaming_types::hash_alg) -> u64
{
    match a
    {
        crate::streaming_types::hash_alg::MD5 => 2305843009213693951u64,
        crate::streaming_types::hash_alg::SHA1 => 2305843009213693951u64,
        crate::streaming_types::hash_alg::SHA2_224 => 2305843009213693951u64,
        crate::streaming_types::hash_alg::SHA2_256 => 2305843009213693951u64,
        crate::streaming_types::hash_alg::SHA2_384 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::SHA2_512 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::Blake2S => 18446744073709551615u64,
        crate::streaming_types::hash_alg::Blake2B => 18446744073709551615u64,
        crate::streaming_types::hash_alg::SHA3_224 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::SHA3_256 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::SHA3_384 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::SHA3_512 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::Shake128 => 18446744073709551615u64,
        crate::streaming_types::hash_alg::Shake256 => 18446744073709551615u64,
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[derive(PartialEq, Clone)]
pub struct two_state
{
    pub fst: u32,
    pub snd: Box<[crate::streaming_hmac::state_s]>,
    pub thd: Box<[crate::streaming_hmac::state_s]>
}

fn wrap_key(r#impl: crate::streaming_hmac::r#impl, output: &mut [u8], key: &[u8], len: u32)
{
    let nkey: (&mut [u8], &mut [u8]) = output.split_at_mut(0usize);
    let ite: u32 =
        if len <= crate::streaming_hmac::block_len(crate::streaming_hmac::alg_of_impl(r#impl))
        { len }
        else
        { crate::streaming_hmac::hash_len(crate::streaming_hmac::alg_of_impl(r#impl)) };
    let zeroes: (&mut [u8], &mut [u8]) = (nkey.1).split_at_mut(ite as usize);
    lowstar::ignore::ignore::<&[u8]>(zeroes.1);
    if len <= crate::streaming_hmac::block_len(crate::streaming_hmac::alg_of_impl(r#impl))
    {
        if len > 0u32
        { (zeroes.0[0usize..len as usize]).copy_from_slice(&key[0usize..len as usize]) }
    }
    else
    { crate::streaming_hmac::hash(r#impl, zeroes.0, key, len) }
}

fn init0(k: &[u8], buf: &mut [u8], s: crate::streaming_hmac::two_state)
{
    let k_len: u32 = s.fst;
    let s1: &[crate::streaming_hmac::state_s] = &s.snd;
    let s2: &[crate::streaming_hmac::state_s] = &s.thd;
    crate::streaming_hmac::init(s1);
    crate::streaming_hmac::init(s2);
    let i1: crate::streaming_hmac::r#impl = crate::streaming_hmac::impl_of_state(s1);
    let a: crate::streaming_types::hash_alg = crate::streaming_hmac::alg_of_impl(i1);
    let mut b: [u8; 168] = [0u8; 168usize];
    let block: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    crate::streaming_hmac::wrap_key(i1, block.1, k, k_len);
    let b0: [u8; 168] = [0x36u8; 168usize];
    let ipad: (&[u8], &[u8]) = b0.split_at(0usize);
    let mut b1: [u8; 168] = [0x5cu8; 168usize];
    let opad: (&mut [u8], &mut [u8]) = b1.split_at_mut(0usize);
    for i in 0u32..crate::streaming_hmac::block_len(a)
    {
        let xi: u8 = ipad.1[i as usize];
        let yi: u8 = block.1[i as usize];
        buf[i as usize] = xi ^ yi
    };
    for i in 0u32..crate::streaming_hmac::block_len(a)
    {
        let xi: u8 = opad.1[i as usize];
        let yi: u8 = block.1[i as usize];
        opad.1[i as usize] = xi ^ yi
    };
    crate::streaming_hmac::update_multi(s2, 0u64, opad.1, crate::streaming_hmac::block_len(a))
}

fn finish0(s: crate::streaming_hmac::two_state, dst: &mut [u8])
{
    match s
    {
        crate::streaming_hmac::two_state { snd: ref s1, thd: ref s2, .. } =>
          {
              let i1: crate::streaming_hmac::r#impl = crate::streaming_hmac::impl_of_state(s1);
              let a: crate::streaming_types::hash_alg = crate::streaming_hmac::alg_of_impl(i1);
              crate::streaming_hmac::finish(s1, dst);
              crate::streaming_hmac::update_last(
                  s2,
                  crate::streaming_hmac::block_len(a) as u64,
                  dst,
                  crate::streaming_hmac::hash_len(a)
              );
              crate::streaming_hmac::finish(s2, dst)
          }
    }
}

pub fn s1 <'a>(i: crate::streaming_hmac::index, s: crate::streaming_hmac::two_state) ->
    Box<[crate::streaming_hmac::state_s]>
{
    lowstar::ignore::ignore::<crate::streaming_hmac::index>(i);
    s.snd
}

pub fn s2 <'a>(i: crate::streaming_hmac::index, s: crate::streaming_hmac::two_state) ->
    Box<[crate::streaming_hmac::state_s]>
{
    lowstar::ignore::ignore::<crate::streaming_hmac::index>(i);
    s.thd
}

pub fn index_of_state(s: crate::streaming_hmac::two_state) -> crate::streaming_hmac::index
{
    match s
    {
        crate::streaming_hmac::two_state { fst: kl, snd: ref s11, .. } =>
          {
              let i1: crate::streaming_hmac::r#impl = crate::streaming_hmac::impl_of_state(s11);
              crate::streaming_hmac::index { fst: i1, snd: kl }
          }
    }
}

#[derive(PartialEq, Clone)]
pub struct agile_state
{ pub block_state: crate::streaming_hmac::two_state, pub buf: Box<[u8]>, pub total_len: u64 }

fn __proj__Mkdtuple2__item___1__Hacl_Agile_Hash_impl_uint32_t(
    pair: crate::streaming_hmac::index
) ->
    crate::streaming_hmac::r#impl
{ pair.fst }

fn dfst__Hacl_Agile_Hash_impl_uint32_t(t: crate::streaming_hmac::index) ->
    crate::streaming_hmac::r#impl
{ crate::streaming_hmac::__proj__Mkdtuple2__item___1__Hacl_Agile_Hash_impl_uint32_t(t) }

fn __proj__Mkdtuple2__item___2__Hacl_Agile_Hash_impl_uint32_t(
    pair: crate::streaming_hmac::index
) ->
    u32
{ pair.snd }

fn dsnd__Hacl_Agile_Hash_impl_uint32_t(t: crate::streaming_hmac::index) -> u32
{ crate::streaming_hmac::__proj__Mkdtuple2__item___2__Hacl_Agile_Hash_impl_uint32_t(t) }

#[derive(PartialEq, Clone)]
enum option__·uint32_t····Hacl_Agile_Hash_state_s·····Hacl_Agile_Hash_state_s··
{
    None,
    Some { v: crate::streaming_hmac::two_state }
}

fn is_blake2b_256(uu___: crate::streaming_hmac::r#impl) -> bool
{ match uu___ { crate::streaming_hmac::r#impl::Blake2B_256 => true, _ => false } }

fn is_blake2s_128(uu___: crate::streaming_hmac::r#impl) -> bool
{ match uu___ { crate::streaming_hmac::r#impl::Blake2S_128 => true, _ => false } }

pub fn get_impl(s: &[crate::streaming_hmac::agile_state]) -> crate::streaming_hmac::index
{
    let block_state: &crate::streaming_hmac::two_state = &(s[0usize]).block_state;
    crate::streaming_hmac::index_of_state(*block_state)
}

fn reset_internal(state: &mut [crate::streaming_hmac::agile_state], key: &[u8])
{
    let block_state: &crate::streaming_hmac::two_state = &(state[0usize]).block_state;
    let buf: &mut [u8] = &mut (state[0usize]).buf;
    let i1: crate::streaming_hmac::index = crate::streaming_hmac::index_of_state(*block_state);
    crate::streaming_hmac::init0(key, buf, *block_state);
    let total_len: u64 =
        crate::streaming_hmac::block_len(
            crate::streaming_hmac::alg_of_impl(
                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
            )
        )
        as
        u64;
    (state[0usize]).total_len = total_len
}

pub fn reset(state: &mut [crate::streaming_hmac::agile_state], key: &[u8], key_length: u32) ->
    crate::streaming_types::error_code
{
    let k_len: u32 = (crate::streaming_hmac::get_impl(state)).snd;
    if key_length != k_len
    { crate::streaming_types::error_code::InvalidLength }
    else
    {
        crate::streaming_hmac::reset_internal(state, key);
        crate::streaming_types::error_code::Success
    }
}

pub fn update(state: &mut [crate::streaming_hmac::agile_state], chunk: &[u8], chunk_len: u32) ->
    crate::streaming_types::error_code
{
    let block_state: &crate::streaming_hmac::two_state = &(state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    let i1: crate::streaming_hmac::index = crate::streaming_hmac::index_of_state(*block_state);
    if
    chunk_len as u64
    >
    (crate::streaming_hmac::max_input_len64(
        crate::streaming_hmac::alg_of_impl(
            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
        )
    )).wrapping_sub(total_len)
    { crate::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if
            total_len.wrapping_rem(
                crate::streaming_hmac::block_len(
                    crate::streaming_hmac::alg_of_impl(
                        crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                    )
                )
                as
                u64
            )
            ==
            0u64
            &&
            total_len > 0u64
            {
                crate::streaming_hmac::block_len(
                    crate::streaming_hmac::alg_of_impl(
                        crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                    )
                )
            }
            else
            {
                total_len.wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                as
                u32
            };
        if
        chunk_len
        <=
        (crate::streaming_hmac::block_len(
            crate::streaming_hmac::alg_of_impl(
                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
            )
        )).wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if
                total_len1.wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                ==
                0u64
                &&
                total_len1 > 0u64
                {
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                }
                else
                {
                    total_len1.wrapping_rem(
                        crate::streaming_hmac::block_len(
                            crate::streaming_hmac::alg_of_impl(
                                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                            )
                        )
                        as
                        u64
                    )
                    as
                    u32
                };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2
        }
        else if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if
                total_len1.wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                ==
                0u64
                &&
                total_len1 > 0u64
                {
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                }
                else
                {
                    total_len1.wrapping_rem(
                        crate::streaming_hmac::block_len(
                            crate::streaming_hmac::alg_of_impl(
                                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                            )
                        )
                        as
                        u64
                    )
                    as
                    u32
                };
            if sz1 != 0u32
            {
                let prevlen: u64 = total_len1.wrapping_sub(sz1 as u64);
                match *block_state
                {
                    crate::streaming_hmac::two_state { snd: ref s11, .. } =>
                      crate::streaming_hmac::update_multi(
                          s11,
                          prevlen,
                          buf,
                          crate::streaming_hmac::block_len(
                              crate::streaming_hmac::alg_of_impl(
                                  crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                              )
                          )
                      )
                }
            };
            let ite: u32 =
                if
                (chunk_len as u64).wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                ==
                0u64
                &&
                chunk_len as u64 > 0u64
                {
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                }
                else
                {
                    (chunk_len as u64).wrapping_rem(
                        crate::streaming_hmac::block_len(
                            crate::streaming_hmac::alg_of_impl(
                                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                            )
                        )
                        as
                        u64
                    )
                    as
                    u32
                };
            let n_blocks: u32 =
                chunk_len.wrapping_sub(ite).wrapping_div(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                );
            let data1_len: u32 =
                n_blocks.wrapping_mul(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                );
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&[u8], &[u8]) = chunk.split_at(0usize);
            let data2: (&[u8], &[u8]) = (data1.1).split_at(data1_len as usize);
            match *block_state
            {
                crate::streaming_hmac::two_state { snd: ref s11, .. } =>
                  crate::streaming_hmac::update_multi(s11, total_len1, data2.0, data1_len)
            };
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 =
                (crate::streaming_hmac::block_len(
                    crate::streaming_hmac::alg_of_impl(
                        crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                    )
                )).wrapping_sub(sz);
            let chunk1: (&[u8], &[u8]) = chunk.split_at(0usize);
            let chunk2: (&[u8], &[u8]) = (chunk1.1).split_at(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if
                total_len1.wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                ==
                0u64
                &&
                total_len1 > 0u64
                {
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                }
                else
                {
                    total_len1.wrapping_rem(
                        crate::streaming_hmac::block_len(
                            crate::streaming_hmac::alg_of_impl(
                                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                            )
                        )
                        as
                        u64
                    )
                    as
                    u32
                };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            (state[0usize]).total_len = total_len2;
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let sz10: u32 =
                if
                total_len10.wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                ==
                0u64
                &&
                total_len10 > 0u64
                {
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                }
                else
                {
                    total_len10.wrapping_rem(
                        crate::streaming_hmac::block_len(
                            crate::streaming_hmac::alg_of_impl(
                                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                            )
                        )
                        as
                        u64
                    )
                    as
                    u32
                };
            if sz10 != 0u32
            {
                let prevlen: u64 = total_len10.wrapping_sub(sz10 as u64);
                match *block_state
                {
                    crate::streaming_hmac::two_state { snd: ref s11, .. } =>
                      crate::streaming_hmac::update_multi(
                          s11,
                          prevlen,
                          buf0,
                          crate::streaming_hmac::block_len(
                              crate::streaming_hmac::alg_of_impl(
                                  crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                              )
                          )
                      )
                }
            };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                    as
                    u64
                )
                ==
                0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                {
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                }
                else
                {
                    (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(
                        crate::streaming_hmac::block_len(
                            crate::streaming_hmac::alg_of_impl(
                                crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                            )
                        )
                        as
                        u64
                    )
                    as
                    u32
                };
            let n_blocks: u32 =
                chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                );
            let data1_len: u32 =
                n_blocks.wrapping_mul(
                    crate::streaming_hmac::block_len(
                        crate::streaming_hmac::alg_of_impl(
                            crate::streaming_hmac::dfst__Hacl_Agile_Hash_impl_uint32_t(i1)
                        )
                    )
                );
            let data2_len: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(data1_len);
            let data1: (&[u8], &[u8]) = (chunk2.1).split_at(0usize);
            let data2: (&[u8], &[u8]) = (data1.1).split_at(data1_len as usize);
            match *block_state
            {
                crate::streaming_hmac::two_state { snd: ref s11, .. } =>
                  crate::streaming_hmac::update_multi(s11, total_len10, data2.0, data1_len)
            };
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::streaming_types::error_code::Success
    }
}

#[derive(PartialEq, Clone)]
struct
__·uint32_t····Hacl_Agile_Hash_state_s·····Hacl_Agile_Hash_state_s··_·uint32_t····Hacl_Agile_Hash_state_s·····Hacl_Agile_Hash_state_s··
{ pub fst: crate::streaming_hmac::two_state, pub snd: crate::streaming_hmac::two_state }

pub fn free(state: &[crate::streaming_hmac::agile_state])
{
    let block_state: &crate::streaming_hmac::two_state = &(state[0usize]).block_state;
    let i1: crate::streaming_hmac::index = crate::streaming_hmac::index_of_state(*block_state);
    lowstar::ignore::ignore::<crate::streaming_hmac::index>(i1);
    match state[0usize]
    {
        crate::streaming_hmac::agile_state { block_state: block_state0, ref buf, .. } =>
          match block_state0
          {
              crate::streaming_hmac::two_state { snd: ref s11, thd: ref s21, .. } =>
                {
                    crate::streaming_hmac::free_(s11);
                    crate::streaming_hmac::free_(s21)
                }
          }
    }
}
