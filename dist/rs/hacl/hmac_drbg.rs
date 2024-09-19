#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub type supported_alg = crate::streaming_types::hash_alg;

pub const reseed_interval: u32 = 1024u32;

pub const max_output_length: u32 = 65536u32;

pub const max_length: u32 = 65536u32;

pub const max_personalization_string_length: u32 = 65536u32;

pub const max_additional_input_length: u32 = 65536u32;

/**
Return the minimal entropy input length of the desired hash function.

@param a Hash algorithm to use.
*/
pub fn
min_length(a: crate::streaming_types::hash_alg) ->
    u32
{
    match a
    {
        crate::streaming_types::hash_alg::SHA1 => 16u32,
        crate::streaming_types::hash_alg::SHA2_256 => 32u32,
        crate::streaming_types::hash_alg::SHA2_384 => 32u32,
        crate::streaming_types::hash_alg::SHA2_512 => 32u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub struct state { pub k: Box<[u8]>, pub v: Box<[u8]>, pub reseed_counter: Box<[u32]> }

pub fn uu___is_State(a: crate::streaming_types::hash_alg, projectee: state) -> bool
{
    lowstar::ignore::ignore::<crate::streaming_types::hash_alg>(a);
    lowstar::ignore::ignore::<state>(projectee);
    true
}

/**
Create a DRBG state.

@param a Hash algorithm to use. The possible instantiations are ...
  * `Spec_Hash_Definitions_SHA2_256`,
  * `Spec_Hash_Definitions_SHA2_384`,
  * `Spec_Hash_Definitions_SHA2_512`, and
  * `Spec_Hash_Definitions_SHA1`.
*/
pub fn
create_in(a: crate::streaming_types::hash_alg) ->
    state
{
    let k: &[u8] =
        match a
        {
            crate::streaming_types::hash_alg::SHA1 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 20usize].into_boxed_slice();
                  &buf
              },
            crate::streaming_types::hash_alg::SHA2_256 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 32usize].into_boxed_slice();
                  &buf
              },
            crate::streaming_types::hash_alg::SHA2_384 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 48usize].into_boxed_slice();
                  &buf
              },
            crate::streaming_types::hash_alg::SHA2_512 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 64usize].into_boxed_slice();
                  &buf
              },
            _ => panic!("Precondition of the function most likely violated")
        };
    let v: &[u8] =
        match a
        {
            crate::streaming_types::hash_alg::SHA1 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 20usize].into_boxed_slice();
                  &buf
              },
            crate::streaming_types::hash_alg::SHA2_256 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 32usize].into_boxed_slice();
                  &buf
              },
            crate::streaming_types::hash_alg::SHA2_384 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 48usize].into_boxed_slice();
                  &buf
              },
            crate::streaming_types::hash_alg::SHA2_512 =>
              {
                  let buf: Box<[u8]> = vec![0u8; 64usize].into_boxed_slice();
                  &buf
              },
            _ => panic!("Precondition of the function most likely violated")
        };
    let ctr: Box<[u32]> = vec![1u32].into_boxed_slice();
    state { k: (*k).into(), v: (*v).into(), reseed_counter: ctr }
}

/**
Instantiate the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param nonce_len Length of nonce.
@param nonce Pointer to `nonce_len` bytes of memory where nonce is read from.
@param personalization_string_len length of personalization string.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from.
*/
pub fn
instantiate(
    a: crate::streaming_types::hash_alg,
    mut st: state,
    entropy_input_len: u32,
    entropy_input: &[u8],
    nonce_len: u32,
    nonce: &[u8],
    personalization_string_len: u32,
    personalization_string: &[u8]
)
{
    match a
    {
        crate::streaming_types::hash_alg::SHA1 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8;
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize].into_boxed_slice();
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..nonce_len as usize]).copy_from_slice(
                  &nonce[0usize..nonce_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len.wrapping_add(nonce_len) as usize..])[0usize..personalization_string_len
              as
              usize]).copy_from_slice(
                  &personalization_string[0usize..personalization_string_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              (k[0usize..20usize]).copy_from_slice(&[0u8; 20usize]);
              (v[0usize..20usize]).copy_from_slice(&[1u8; 20usize]);
              ctr[0usize] = 1u32;
              let input_len: u32 =
                  21u32.wrapping_add(
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                  );
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  ((&mut (&mut input)[21usize..])[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                      personalization_string_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[20usize] = 0u8;
              crate::hmac::compute_sha1(k·.1, k, 20u32, &input, input_len);
              crate::hmac::compute_sha1(v, k·.1, 20u32, v, 20u32);
              (k[0usize..20usize]).copy_from_slice(&k·.1[0usize..20usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  let input_len0: u32 =
                      21u32.wrapping_add(
                          entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                      );
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
                  if
                  entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
                  !=
                  0u32
                  {
                      ((&mut (&mut input0)[21usize..])[0usize..entropy_input_len.wrapping_add(
                          nonce_len
                      ).wrapping_add(personalization_string_len)
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[20usize] = 1u8;
                  crate::hmac::compute_sha1(k·0.1, k, 20u32, &input0, input_len0);
                  crate::hmac::compute_sha1(v, k·0.1, 20u32, v, 20u32);
                  (k[0usize..20usize]).copy_from_slice(&k·0.1[0usize..20usize])
              }
          },
        crate::streaming_types::hash_alg::SHA2_256 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8;
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize].into_boxed_slice();
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..nonce_len as usize]).copy_from_slice(
                  &nonce[0usize..nonce_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len.wrapping_add(nonce_len) as usize..])[0usize..personalization_string_len
              as
              usize]).copy_from_slice(
                  &personalization_string[0usize..personalization_string_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              (k[0usize..32usize]).copy_from_slice(&[0u8; 32usize]);
              (v[0usize..32usize]).copy_from_slice(&[1u8; 32usize]);
              ctr[0usize] = 1u32;
              let input_len: u32 =
                  33u32.wrapping_add(
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                  );
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  ((&mut (&mut input)[33usize..])[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                      personalization_string_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[32usize] = 0u8;
              crate::hmac::compute_sha2_256(k·.1, k, 32u32, &input, input_len);
              crate::hmac::compute_sha2_256(v, k·.1, 32u32, v, 32u32);
              (k[0usize..32usize]).copy_from_slice(&k·.1[0usize..32usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  let input_len0: u32 =
                      33u32.wrapping_add(
                          entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                      );
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
                  if
                  entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
                  !=
                  0u32
                  {
                      ((&mut (&mut input0)[33usize..])[0usize..entropy_input_len.wrapping_add(
                          nonce_len
                      ).wrapping_add(personalization_string_len)
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[32usize] = 1u8;
                  crate::hmac::compute_sha2_256(k·0.1, k, 32u32, &input0, input_len0);
                  crate::hmac::compute_sha2_256(v, k·0.1, 32u32, v, 32u32);
                  (k[0usize..32usize]).copy_from_slice(&k·0.1[0usize..32usize])
              }
          },
        crate::streaming_types::hash_alg::SHA2_384 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8;
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize].into_boxed_slice();
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..nonce_len as usize]).copy_from_slice(
                  &nonce[0usize..nonce_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len.wrapping_add(nonce_len) as usize..])[0usize..personalization_string_len
              as
              usize]).copy_from_slice(
                  &personalization_string[0usize..personalization_string_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              (k[0usize..48usize]).copy_from_slice(&[0u8; 48usize]);
              (v[0usize..48usize]).copy_from_slice(&[1u8; 48usize]);
              ctr[0usize] = 1u32;
              let input_len: u32 =
                  49u32.wrapping_add(
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                  );
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  ((&mut (&mut input)[49usize..])[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                      personalization_string_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[48usize] = 0u8;
              crate::hmac::compute_sha2_384(k·.1, k, 48u32, &input, input_len);
              crate::hmac::compute_sha2_384(v, k·.1, 48u32, v, 48u32);
              (k[0usize..48usize]).copy_from_slice(&k·.1[0usize..48usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  let input_len0: u32 =
                      49u32.wrapping_add(
                          entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                      );
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
                  if
                  entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
                  !=
                  0u32
                  {
                      ((&mut (&mut input0)[49usize..])[0usize..entropy_input_len.wrapping_add(
                          nonce_len
                      ).wrapping_add(personalization_string_len)
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[48usize] = 1u8;
                  crate::hmac::compute_sha2_384(k·0.1, k, 48u32, &input0, input_len0);
                  crate::hmac::compute_sha2_384(v, k·0.1, 48u32, v, 48u32);
                  (k[0usize..48usize]).copy_from_slice(&k·0.1[0usize..48usize])
              }
          },
        crate::streaming_types::hash_alg::SHA2_512 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8;
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize].into_boxed_slice();
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..nonce_len as usize]).copy_from_slice(
                  &nonce[0usize..nonce_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len.wrapping_add(nonce_len) as usize..])[0usize..personalization_string_len
              as
              usize]).copy_from_slice(
                  &personalization_string[0usize..personalization_string_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              (k[0usize..64usize]).copy_from_slice(&[0u8; 64usize]);
              (v[0usize..64usize]).copy_from_slice(&[1u8; 64usize]);
              ctr[0usize] = 1u32;
              let input_len: u32 =
                  65u32.wrapping_add(
                      entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                  );
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  ((&mut (&mut input)[65usize..])[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                      personalization_string_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                          personalization_string_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[64usize] = 0u8;
              crate::hmac::compute_sha2_512(k·.1, k, 64u32, &input, input_len);
              crate::hmac::compute_sha2_512(v, k·.1, 64u32, v, 64u32);
              (k[0usize..64usize]).copy_from_slice(&k·.1[0usize..64usize]);
              if
              entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
              !=
              0u32
              {
                  let input_len0: u32 =
                      65u32.wrapping_add(
                          entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                      );
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
                  if
                  entropy_input_len.wrapping_add(nonce_len).wrapping_add(personalization_string_len)
                  !=
                  0u32
                  {
                      ((&mut (&mut input0)[65usize..])[0usize..entropy_input_len.wrapping_add(
                          nonce_len
                      ).wrapping_add(personalization_string_len)
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(nonce_len).wrapping_add(
                              personalization_string_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[64usize] = 1u8;
                  crate::hmac::compute_sha2_512(k·0.1, k, 64u32, &input0, input_len0);
                  crate::hmac::compute_sha2_512(v, k·0.1, 64u32, v, 64u32);
                  (k[0usize..64usize]).copy_from_slice(&k·0.1[0usize..64usize])
              }
          },
        _ => panic!("Precondition of the function most likely violated")
    }
}

/**
Reseed the DRBG.

@param a Hash algorithm to use. (Value must match the value used in `Hacl_HMAC_DRBG_create_in`.)
@param st Pointer to DRBG state.
@param entropy_input_len Length of entropy input.
@param entropy_input Pointer to `entropy_input_len` bytes of memory where entropy input is read from.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
*/
pub fn
reseed(
    a: crate::streaming_types::hash_alg,
    mut st: state,
    entropy_input_len: u32,
    entropy_input: &[u8],
    additional_input_input_len: u32,
    additional_input_input: &[u8]
)
{
    match a
    {
        crate::streaming_types::hash_alg::SHA1 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8; entropy_input_len.wrapping_add(additional_input_input_len) as usize].into_boxed_slice(

                  );
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..additional_input_input_len
              as
              usize]).copy_from_slice(
                  &additional_input_input[0usize..additional_input_input_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              let input_len: u32 =
                  21u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  ((&mut (&mut input)[21usize..])[0usize..entropy_input_len.wrapping_add(
                      additional_input_input_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[20usize] = 0u8;
              crate::hmac::compute_sha1(k·.1, k, 20u32, &input, input_len);
              crate::hmac::compute_sha1(v, k·.1, 20u32, v, 20u32);
              (k[0usize..20usize]).copy_from_slice(&k·.1[0usize..20usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  let input_len0: u32 =
                      21u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
                  if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
                  {
                      ((&mut (&mut input0)[21usize..])[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                              additional_input_input_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[20usize] = 1u8;
                  crate::hmac::compute_sha1(k·0.1, k, 20u32, &input0, input_len0);
                  crate::hmac::compute_sha1(v, k·0.1, 20u32, v, 20u32);
                  (k[0usize..20usize]).copy_from_slice(&k·0.1[0usize..20usize])
              };
              ctr[0usize] = 1u32
          },
        crate::streaming_types::hash_alg::SHA2_256 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8; entropy_input_len.wrapping_add(additional_input_input_len) as usize].into_boxed_slice(

                  );
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..additional_input_input_len
              as
              usize]).copy_from_slice(
                  &additional_input_input[0usize..additional_input_input_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              let input_len: u32 =
                  33u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  ((&mut (&mut input)[33usize..])[0usize..entropy_input_len.wrapping_add(
                      additional_input_input_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[32usize] = 0u8;
              crate::hmac::compute_sha2_256(k·.1, k, 32u32, &input, input_len);
              crate::hmac::compute_sha2_256(v, k·.1, 32u32, v, 32u32);
              (k[0usize..32usize]).copy_from_slice(&k·.1[0usize..32usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  let input_len0: u32 =
                      33u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
                  if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
                  {
                      ((&mut (&mut input0)[33usize..])[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                              additional_input_input_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[32usize] = 1u8;
                  crate::hmac::compute_sha2_256(k·0.1, k, 32u32, &input0, input_len0);
                  crate::hmac::compute_sha2_256(v, k·0.1, 32u32, v, 32u32);
                  (k[0usize..32usize]).copy_from_slice(&k·0.1[0usize..32usize])
              };
              ctr[0usize] = 1u32
          },
        crate::streaming_types::hash_alg::SHA2_384 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8; entropy_input_len.wrapping_add(additional_input_input_len) as usize].into_boxed_slice(

                  );
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..additional_input_input_len
              as
              usize]).copy_from_slice(
                  &additional_input_input[0usize..additional_input_input_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              let input_len: u32 =
                  49u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  ((&mut (&mut input)[49usize..])[0usize..entropy_input_len.wrapping_add(
                      additional_input_input_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[48usize] = 0u8;
              crate::hmac::compute_sha2_384(k·.1, k, 48u32, &input, input_len);
              crate::hmac::compute_sha2_384(v, k·.1, 48u32, v, 48u32);
              (k[0usize..48usize]).copy_from_slice(&k·.1[0usize..48usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  let input_len0: u32 =
                      49u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
                  if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
                  {
                      ((&mut (&mut input0)[49usize..])[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                              additional_input_input_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[48usize] = 1u8;
                  crate::hmac::compute_sha2_384(k·0.1, k, 48u32, &input0, input_len0);
                  crate::hmac::compute_sha2_384(v, k·0.1, 48u32, v, 48u32);
                  (k[0usize..48usize]).copy_from_slice(&k·0.1[0usize..48usize])
              };
              ctr[0usize] = 1u32
          },
        crate::streaming_types::hash_alg::SHA2_512 =>
          {
              let mut seed_material: Box<[u8]> =
                  vec![0u8; entropy_input_len.wrapping_add(additional_input_input_len) as usize].into_boxed_slice(

                  );
              ((&mut (&mut seed_material)[0usize..])[0usize..entropy_input_len as usize]).copy_from_slice(
                  &entropy_input[0usize..entropy_input_len as usize]
              );
              ((&mut (&mut seed_material)[entropy_input_len as usize..])[0usize..additional_input_input_len
              as
              usize]).copy_from_slice(
                  &additional_input_input[0usize..additional_input_input_len as usize]
              );
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              let input_len: u32 =
                  65u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  ((&mut (&mut input)[65usize..])[0usize..entropy_input_len.wrapping_add(
                      additional_input_input_len
                  )
                  as
                  usize]).copy_from_slice(
                      &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]
                  )
              };
              (&mut input)[64usize] = 0u8;
              crate::hmac::compute_sha2_512(k·.1, k, 64u32, &input, input_len);
              crate::hmac::compute_sha2_512(v, k·.1, 64u32, v, 64u32);
              (k[0usize..64usize]).copy_from_slice(&k·.1[0usize..64usize]);
              if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
              {
                  let input_len0: u32 =
                      65u32.wrapping_add(entropy_input_len.wrapping_add(additional_input_input_len));
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
                  if entropy_input_len.wrapping_add(additional_input_input_len) != 0u32
                  {
                      ((&mut (&mut input0)[65usize..])[0usize..entropy_input_len.wrapping_add(
                          additional_input_input_len
                      )
                      as
                      usize]).copy_from_slice(
                          &(&seed_material)[0usize..entropy_input_len.wrapping_add(
                              additional_input_input_len
                          )
                          as
                          usize]
                      )
                  };
                  (&mut input0)[64usize] = 1u8;
                  crate::hmac::compute_sha2_512(k·0.1, k, 64u32, &input0, input_len0);
                  crate::hmac::compute_sha2_512(v, k·0.1, 64u32, v, 64u32);
                  (k[0usize..64usize]).copy_from_slice(&k·0.1[0usize..64usize])
              };
              ctr[0usize] = 1u32
          },
        _ => panic!("Precondition of the function most likely violated")
    }
}

/**
Generate output.

@param a Hash algorithm to use. (Value must match the value used in `create_in`.)
@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input_len Length of additional input.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
*/
pub fn
generate(
    a: crate::streaming_types::hash_alg,
    output: &mut [u8],
    mut st: state,
    n: u32,
    additional_input_len: u32,
    additional_input: &[u8]
) ->
    bool
{
    match a
    {
        crate::streaming_types::hash_alg::SHA1 =>
          if (&st.reseed_counter)[0usize] > reseed_interval
          { false }
          else
          {
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              if additional_input_len > 0u32
              {
                  let input_len: u32 = 21u32.wrapping_add(additional_input_len);
                  let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
                  let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
                  (k·.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input)[21usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input)[20usize] = 0u8;
                  crate::hmac::compute_sha1(k·.1, k, 20u32, &input, input_len);
                  crate::hmac::compute_sha1(v, k·.1, 20u32, v, 20u32);
                  (k[0usize..20usize]).copy_from_slice(&k·.1[0usize..20usize]);
                  if additional_input_len != 0u32
                  {
                      let input_len0: u32 = 21u32.wrapping_add(additional_input_len);
                      let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                      let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                      (k·0.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
                      if additional_input_len != 0u32
                      {
                          ((&mut (&mut input0)[21usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                              &additional_input[0usize..additional_input_len as usize]
                          )
                      };
                      (&mut input0)[20usize] = 1u8;
                      crate::hmac::compute_sha1(k·0.1, k, 20u32, &input0, input_len0);
                      crate::hmac::compute_sha1(v, k·0.1, 20u32, v, 20u32);
                      (k[0usize..20usize]).copy_from_slice(&k·0.1[0usize..20usize])
                  }
              };
              let output1: &mut [u8] = output;
              let max: u32 = n.wrapping_div(20u32);
              let out: (&mut [u8], &mut [u8]) = output1.split_at_mut(0usize);
              for i in 0u32..max
              {
                  crate::hmac::compute_sha1(v, k, 20u32, v, 20u32);
                  ((&mut out.1[i.wrapping_mul(20u32) as usize..])[0usize..20usize]).copy_from_slice(
                      &v[0usize..20usize]
                  )
              };
              if max.wrapping_mul(20u32) < n
              {
                  let block: (&mut [u8], &mut [u8]) =
                      out.1.split_at_mut(max.wrapping_mul(20u32) as usize);
                  crate::hmac::compute_sha1(v, k, 20u32, v, 20u32);
                  (block.1[0usize..n.wrapping_sub(max.wrapping_mul(20u32)) as usize]).copy_from_slice(
                      &(&v[0usize..])[0usize..n.wrapping_sub(max.wrapping_mul(20u32)) as usize]
                  )
              };
              let input_len: u32 = 21u32.wrapping_add(additional_input_len);
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
              if additional_input_len != 0u32
              {
                  ((&mut (&mut input)[21usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                      &additional_input[0usize..additional_input_len as usize]
                  )
              };
              (&mut input)[20usize] = 0u8;
              crate::hmac::compute_sha1(k·.1, k, 20u32, &input, input_len);
              crate::hmac::compute_sha1(v, k·.1, 20u32, v, 20u32);
              (k[0usize..20usize]).copy_from_slice(&k·.1[0usize..20usize]);
              if additional_input_len != 0u32
              {
                  let input_len0: u32 = 21u32.wrapping_add(additional_input_len);
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..20usize]).copy_from_slice(&v[0usize..20usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input0)[21usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input0)[20usize] = 1u8;
                  crate::hmac::compute_sha1(k·0.1, k, 20u32, &input0, input_len0);
                  crate::hmac::compute_sha1(v, k·0.1, 20u32, v, 20u32);
                  (k[0usize..20usize]).copy_from_slice(&k·0.1[0usize..20usize])
              };
              let old_ctr: u32 = ctr[0usize];
              ctr[0usize] = old_ctr.wrapping_add(1u32);
              true
          },
        crate::streaming_types::hash_alg::SHA2_256 =>
          if (&st.reseed_counter)[0usize] > reseed_interval
          { false }
          else
          {
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              if additional_input_len > 0u32
              {
                  let input_len: u32 = 33u32.wrapping_add(additional_input_len);
                  let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
                  let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
                  (k·.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input)[33usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input)[32usize] = 0u8;
                  crate::hmac::compute_sha2_256(k·.1, k, 32u32, &input, input_len);
                  crate::hmac::compute_sha2_256(v, k·.1, 32u32, v, 32u32);
                  (k[0usize..32usize]).copy_from_slice(&k·.1[0usize..32usize]);
                  if additional_input_len != 0u32
                  {
                      let input_len0: u32 = 33u32.wrapping_add(additional_input_len);
                      let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                      let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                      (k·0.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
                      if additional_input_len != 0u32
                      {
                          ((&mut (&mut input0)[33usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                              &additional_input[0usize..additional_input_len as usize]
                          )
                      };
                      (&mut input0)[32usize] = 1u8;
                      crate::hmac::compute_sha2_256(k·0.1, k, 32u32, &input0, input_len0);
                      crate::hmac::compute_sha2_256(v, k·0.1, 32u32, v, 32u32);
                      (k[0usize..32usize]).copy_from_slice(&k·0.1[0usize..32usize])
                  }
              };
              let output1: &mut [u8] = output;
              let max: u32 = n.wrapping_div(32u32);
              let out: (&mut [u8], &mut [u8]) = output1.split_at_mut(0usize);
              for i in 0u32..max
              {
                  crate::hmac::compute_sha2_256(v, k, 32u32, v, 32u32);
                  ((&mut out.1[i.wrapping_mul(32u32) as usize..])[0usize..32usize]).copy_from_slice(
                      &v[0usize..32usize]
                  )
              };
              if max.wrapping_mul(32u32) < n
              {
                  let block: (&mut [u8], &mut [u8]) =
                      out.1.split_at_mut(max.wrapping_mul(32u32) as usize);
                  crate::hmac::compute_sha2_256(v, k, 32u32, v, 32u32);
                  (block.1[0usize..n.wrapping_sub(max.wrapping_mul(32u32)) as usize]).copy_from_slice(
                      &(&v[0usize..])[0usize..n.wrapping_sub(max.wrapping_mul(32u32)) as usize]
                  )
              };
              let input_len: u32 = 33u32.wrapping_add(additional_input_len);
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
              if additional_input_len != 0u32
              {
                  ((&mut (&mut input)[33usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                      &additional_input[0usize..additional_input_len as usize]
                  )
              };
              (&mut input)[32usize] = 0u8;
              crate::hmac::compute_sha2_256(k·.1, k, 32u32, &input, input_len);
              crate::hmac::compute_sha2_256(v, k·.1, 32u32, v, 32u32);
              (k[0usize..32usize]).copy_from_slice(&k·.1[0usize..32usize]);
              if additional_input_len != 0u32
              {
                  let input_len0: u32 = 33u32.wrapping_add(additional_input_len);
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..32usize]).copy_from_slice(&v[0usize..32usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input0)[33usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input0)[32usize] = 1u8;
                  crate::hmac::compute_sha2_256(k·0.1, k, 32u32, &input0, input_len0);
                  crate::hmac::compute_sha2_256(v, k·0.1, 32u32, v, 32u32);
                  (k[0usize..32usize]).copy_from_slice(&k·0.1[0usize..32usize])
              };
              let old_ctr: u32 = ctr[0usize];
              ctr[0usize] = old_ctr.wrapping_add(1u32);
              true
          },
        crate::streaming_types::hash_alg::SHA2_384 =>
          if (&st.reseed_counter)[0usize] > reseed_interval
          { false }
          else
          {
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              if additional_input_len > 0u32
              {
                  let input_len: u32 = 49u32.wrapping_add(additional_input_len);
                  let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
                  let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
                  (k·.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input)[49usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input)[48usize] = 0u8;
                  crate::hmac::compute_sha2_384(k·.1, k, 48u32, &input, input_len);
                  crate::hmac::compute_sha2_384(v, k·.1, 48u32, v, 48u32);
                  (k[0usize..48usize]).copy_from_slice(&k·.1[0usize..48usize]);
                  if additional_input_len != 0u32
                  {
                      let input_len0: u32 = 49u32.wrapping_add(additional_input_len);
                      let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                      let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                      (k·0.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
                      if additional_input_len != 0u32
                      {
                          ((&mut (&mut input0)[49usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                              &additional_input[0usize..additional_input_len as usize]
                          )
                      };
                      (&mut input0)[48usize] = 1u8;
                      crate::hmac::compute_sha2_384(k·0.1, k, 48u32, &input0, input_len0);
                      crate::hmac::compute_sha2_384(v, k·0.1, 48u32, v, 48u32);
                      (k[0usize..48usize]).copy_from_slice(&k·0.1[0usize..48usize])
                  }
              };
              let output1: &mut [u8] = output;
              let max: u32 = n.wrapping_div(48u32);
              let out: (&mut [u8], &mut [u8]) = output1.split_at_mut(0usize);
              for i in 0u32..max
              {
                  crate::hmac::compute_sha2_384(v, k, 48u32, v, 48u32);
                  ((&mut out.1[i.wrapping_mul(48u32) as usize..])[0usize..48usize]).copy_from_slice(
                      &v[0usize..48usize]
                  )
              };
              if max.wrapping_mul(48u32) < n
              {
                  let block: (&mut [u8], &mut [u8]) =
                      out.1.split_at_mut(max.wrapping_mul(48u32) as usize);
                  crate::hmac::compute_sha2_384(v, k, 48u32, v, 48u32);
                  (block.1[0usize..n.wrapping_sub(max.wrapping_mul(48u32)) as usize]).copy_from_slice(
                      &(&v[0usize..])[0usize..n.wrapping_sub(max.wrapping_mul(48u32)) as usize]
                  )
              };
              let input_len: u32 = 49u32.wrapping_add(additional_input_len);
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
              if additional_input_len != 0u32
              {
                  ((&mut (&mut input)[49usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                      &additional_input[0usize..additional_input_len as usize]
                  )
              };
              (&mut input)[48usize] = 0u8;
              crate::hmac::compute_sha2_384(k·.1, k, 48u32, &input, input_len);
              crate::hmac::compute_sha2_384(v, k·.1, 48u32, v, 48u32);
              (k[0usize..48usize]).copy_from_slice(&k·.1[0usize..48usize]);
              if additional_input_len != 0u32
              {
                  let input_len0: u32 = 49u32.wrapping_add(additional_input_len);
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..48usize]).copy_from_slice(&v[0usize..48usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input0)[49usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input0)[48usize] = 1u8;
                  crate::hmac::compute_sha2_384(k·0.1, k, 48u32, &input0, input_len0);
                  crate::hmac::compute_sha2_384(v, k·0.1, 48u32, v, 48u32);
                  (k[0usize..48usize]).copy_from_slice(&k·0.1[0usize..48usize])
              };
              let old_ctr: u32 = ctr[0usize];
              ctr[0usize] = old_ctr.wrapping_add(1u32);
              true
          },
        crate::streaming_types::hash_alg::SHA2_512 =>
          if (&st.reseed_counter)[0usize] > reseed_interval
          { false }
          else
          {
              let k: &mut [u8] = &mut st.k;
              let v: &mut [u8] = &mut st.v;
              let ctr: &mut [u32] = &mut st.reseed_counter;
              if additional_input_len > 0u32
              {
                  let input_len: u32 = 65u32.wrapping_add(additional_input_len);
                  let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
                  let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
                  (k·.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input)[65usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input)[64usize] = 0u8;
                  crate::hmac::compute_sha2_512(k·.1, k, 64u32, &input, input_len);
                  crate::hmac::compute_sha2_512(v, k·.1, 64u32, v, 64u32);
                  (k[0usize..64usize]).copy_from_slice(&k·.1[0usize..64usize]);
                  if additional_input_len != 0u32
                  {
                      let input_len0: u32 = 65u32.wrapping_add(additional_input_len);
                      let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                      let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                      (k·0.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
                      if additional_input_len != 0u32
                      {
                          ((&mut (&mut input0)[65usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                              &additional_input[0usize..additional_input_len as usize]
                          )
                      };
                      (&mut input0)[64usize] = 1u8;
                      crate::hmac::compute_sha2_512(k·0.1, k, 64u32, &input0, input_len0);
                      crate::hmac::compute_sha2_512(v, k·0.1, 64u32, v, 64u32);
                      (k[0usize..64usize]).copy_from_slice(&k·0.1[0usize..64usize])
                  }
              };
              let output1: &mut [u8] = output;
              let max: u32 = n.wrapping_div(64u32);
              let out: (&mut [u8], &mut [u8]) = output1.split_at_mut(0usize);
              for i in 0u32..max
              {
                  crate::hmac::compute_sha2_512(v, k, 64u32, v, 64u32);
                  ((&mut out.1[i.wrapping_mul(64u32) as usize..])[0usize..64usize]).copy_from_slice(
                      &v[0usize..64usize]
                  )
              };
              if max.wrapping_mul(64u32) < n
              {
                  let block: (&mut [u8], &mut [u8]) =
                      out.1.split_at_mut(max.wrapping_mul(64u32) as usize);
                  crate::hmac::compute_sha2_512(v, k, 64u32, v, 64u32);
                  (block.1[0usize..n.wrapping_sub(max.wrapping_mul(64u32)) as usize]).copy_from_slice(
                      &(&v[0usize..])[0usize..n.wrapping_sub(max.wrapping_mul(64u32)) as usize]
                  )
              };
              let input_len: u32 = 65u32.wrapping_add(additional_input_len);
              let mut input: Box<[u8]> = vec![0u8; input_len as usize].into_boxed_slice();
              let k·: (&mut [u8], &mut [u8]) = input.split_at_mut(0usize);
              (k·.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
              if additional_input_len != 0u32
              {
                  ((&mut (&mut input)[65usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                      &additional_input[0usize..additional_input_len as usize]
                  )
              };
              (&mut input)[64usize] = 0u8;
              crate::hmac::compute_sha2_512(k·.1, k, 64u32, &input, input_len);
              crate::hmac::compute_sha2_512(v, k·.1, 64u32, v, 64u32);
              (k[0usize..64usize]).copy_from_slice(&k·.1[0usize..64usize]);
              if additional_input_len != 0u32
              {
                  let input_len0: u32 = 65u32.wrapping_add(additional_input_len);
                  let mut input0: Box<[u8]> = vec![0u8; input_len0 as usize].into_boxed_slice();
                  let k·0: (&mut [u8], &mut [u8]) = input0.split_at_mut(0usize);
                  (k·0.1[0usize..64usize]).copy_from_slice(&v[0usize..64usize]);
                  if additional_input_len != 0u32
                  {
                      ((&mut (&mut input0)[65usize..])[0usize..additional_input_len as usize]).copy_from_slice(
                          &additional_input[0usize..additional_input_len as usize]
                      )
                  };
                  (&mut input0)[64usize] = 1u8;
                  crate::hmac::compute_sha2_512(k·0.1, k, 64u32, &input0, input_len0);
                  crate::hmac::compute_sha2_512(v, k·0.1, 64u32, v, 64u32);
                  (k[0usize..64usize]).copy_from_slice(&k·0.1[0usize..64usize])
              };
              let old_ctr: u32 = ctr[0usize];
              ctr[0usize] = old_ctr.wrapping_add(1u32);
              true
          },
        _ => panic!("Precondition of the function most likely violated")
    }
}
