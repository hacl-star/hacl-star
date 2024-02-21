#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

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
    let vec256: bool = crate::evercrypt::autoconfig2::has_vec256();
    let vec128: bool = crate::evercrypt::autoconfig2::has_vec128();
    if crate::evercrypt::targetconfig::hacl_can_compile_vec256 && vec256
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::hacl::aead_chacha20poly1305_simd256::encrypt(cipher, tag, m, mlen, aad, aadlen, k, n)
    }
    else
    if crate::evercrypt::targetconfig::hacl_can_compile_vec128 && vec128
    {
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::aead_chacha20poly1305_simd128::encrypt(cipher, tag, m, mlen, aad, aadlen, k, n)
    }
    else
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::aead_chacha20poly1305::encrypt(cipher, tag, m, mlen, aad, aadlen, k, n)
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
    let vec256: bool = crate::evercrypt::autoconfig2::has_vec256();
    let vec128: bool = crate::evercrypt::autoconfig2::has_vec128();
    if crate::evercrypt::targetconfig::hacl_can_compile_vec256 && vec256
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::hacl::aead_chacha20poly1305_simd256::decrypt(m, cipher, mlen, aad, aadlen, k, n, tag)
    }
    else
    if crate::evercrypt::targetconfig::hacl_can_compile_vec128 && vec128
    {
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::aead_chacha20poly1305_simd128::decrypt(m, cipher, mlen, aad, aadlen, k, n, tag)
    }
    else
    {
        crate::lowstar::ignore::ignore::<bool>(vec128);
        crate::lowstar::ignore::ignore::<bool>(vec256);
        crate::hacl::aead_chacha20poly1305::decrypt(m, cipher, mlen, aad, aadlen, k, n, tag)
    }
}
