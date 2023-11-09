pub fn extract_blake2s_128(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac_blake2s_128::compute_blake2s_128(prk, salt, saltlen, ikm, ikmlen) }
