fn extract_sha1(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha1(prk, salt, saltlen, ikm, ikmlen) }

fn extract_sha2_256(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha2_256(prk, salt, saltlen, ikm, ikmlen) }

fn extract_sha2_384(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha2_384(prk, salt, saltlen, ikm, ikmlen) }

fn extract_sha2_512(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha2_512(prk, salt, saltlen, ikm, ikmlen) }

fn extract_blake2s(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_blake2s(prk, salt, saltlen, ikm, ikmlen) }

fn extract_blake2b(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_blake2b(prk, salt, saltlen, ikm, ikmlen) }