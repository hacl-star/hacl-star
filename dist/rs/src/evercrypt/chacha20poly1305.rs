pub fn aead_encrypt(
    k: &mut [u8],
    n: &mut [u8],
    aadlen: u32,
    aad: &mut [u8],
    mlen: u32,
    m: &mut [u8],
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    ()
{
    let vec256: bool = crate::evercrypt::autoconfig2::has_vec256(());
    let vec128: bool = crate::evercrypt::autoconfig2::has_vec128(());
    if crate::evercrypt::targetconfig::hacl_can_compile_vec256 && vec256
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::hacl::chacha20poly1305_256::aead_encrypt(k, n, aadlen, aad, mlen, m, cipher, tag)
    }
    else
    if crate::evercrypt::targetconfig::hacl_can_compile_vec128 && vec128
    {
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::chacha20poly1305_128::aead_encrypt(k, n, aadlen, aad, mlen, m, cipher, tag)
    }
    else
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::chacha20poly1305_32::aead_encrypt(k, n, aadlen, aad, mlen, m, cipher, tag)
    }
}

pub fn aead_decrypt(
    k: &mut [u8],
    n: &mut [u8],
    aadlen: u32,
    aad: &mut [u8],
    mlen: u32,
    m: &mut [u8],
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    u32
{
    let vec256: bool = crate::evercrypt::autoconfig2::has_vec256(());
    let vec128: bool = crate::evercrypt::autoconfig2::has_vec128(());
    if crate::evercrypt::targetconfig::hacl_can_compile_vec256 && vec256
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::hacl::chacha20poly1305_256::aead_decrypt(k, n, aadlen, aad, mlen, m, cipher, tag)
    }
    else
    if crate::evercrypt::targetconfig::hacl_can_compile_vec128 && vec128
    {
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::chacha20poly1305_128::aead_decrypt(k, n, aadlen, aad, mlen, m, cipher, tag)
    }
    else
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::chacha20poly1305_32::aead_decrypt(k, n, aadlen, aad, mlen, m, cipher, tag)
    }
}
