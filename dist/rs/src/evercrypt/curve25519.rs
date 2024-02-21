#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn secret_to_public(r#pub: &mut [u8], r#priv: &mut [u8]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_bmi2: bool = crate::evercrypt::autoconfig2::has_bmi2();
        let has_adx: bool = crate::evercrypt::autoconfig2::has_adx();
        if has_bmi2 && has_adx
        { crate::hacl::curve25519_64::secret_to_public(r#pub, r#priv) }
        else
        { crate::hacl::curve25519_51::secret_to_public(r#pub, r#priv) }
    }
    else
    { crate::hacl::curve25519_51::secret_to_public(r#pub, r#priv) }
}

pub fn scalarmult(shared: &mut [u8], my_priv: &mut [u8], their_pub: &mut [u8]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_bmi2: bool = crate::evercrypt::autoconfig2::has_bmi2();
        let has_adx: bool = crate::evercrypt::autoconfig2::has_adx();
        if has_bmi2 && has_adx
        { crate::hacl::curve25519_64::scalarmult(shared, my_priv, their_pub) }
        else
        { crate::hacl::curve25519_51::scalarmult(shared, my_priv, their_pub) }
    }
    else
    { crate::hacl::curve25519_51::scalarmult(shared, my_priv, their_pub) }
}

pub fn ecdh(shared: &mut [u8], my_priv: &mut [u8], their_pub: &mut [u8]) -> bool
{
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_bmi2: bool = crate::evercrypt::autoconfig2::has_bmi2();
        let has_adx: bool = crate::evercrypt::autoconfig2::has_adx();
        if has_bmi2 && has_adx
        { crate::hacl::curve25519_64::ecdh(shared, my_priv, their_pub) }
        else
        { crate::hacl::curve25519_51::ecdh(shared, my_priv, their_pub) }
    }
    else
    { crate::hacl::curve25519_51::ecdh(shared, my_priv, their_pub) }
}
