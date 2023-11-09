pub fn extract_sha2_256(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac::compute_sha2_256(prk, salt, saltlen, ikm, ikmlen) }

pub fn extract_sha2_384(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac::compute_sha2_384(prk, salt, saltlen, ikm, ikmlen) }

pub fn extract_sha2_512(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac::compute_sha2_512(prk, salt, saltlen, ikm, ikmlen) }

pub fn extract_blake2s_32(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac::compute_blake2s_32(prk, salt, saltlen, ikm, ikmlen) }

pub fn extract_blake2b_32(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac::compute_blake2b_32(prk, salt, saltlen, ikm, ikmlen) }
