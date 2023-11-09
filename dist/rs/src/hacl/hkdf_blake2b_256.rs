pub fn extract_blake2b_256(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac::blake2b_256::compute_blake2b_256(prk, salt, saltlen, ikm, ikmlen) }