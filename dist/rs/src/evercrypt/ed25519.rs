#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn secret_to_public(public_key: &mut [u8], private_key: &mut [u8]) -> ()
{ crate::hacl::ed25519::secret_to_public(public_key, private_key) }

pub fn expand_keys(expanded_keys: &mut [u8], private_key: &mut [u8]) -> ()
{ crate::hacl::ed25519::expand_keys(expanded_keys, private_key) }

pub fn sign_expanded(
    signature: &mut [u8],
    expanded_keys: &mut [u8],
    msg_len: u32,
    msg: &mut [u8]
) ->
    ()
{ crate::hacl::ed25519::sign_expanded(signature, expanded_keys, msg_len, msg) }

pub fn sign(signature: &mut [u8], private_key: &mut [u8], msg_len: u32, msg: &mut [u8]) -> ()
{ crate::hacl::ed25519::sign(signature, private_key, msg_len, msg) }

pub fn verify(public_key: &mut [u8], msg_len: u32, msg: &mut [u8], signature: &mut [u8]) ->
    bool
{ crate::hacl::ed25519::verify(public_key, msg_len, msg, signature) }
