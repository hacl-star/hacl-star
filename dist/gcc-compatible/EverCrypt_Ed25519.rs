#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]
extern "C" {
    fn Hacl_Ed25519_secret_to_public(
        public_key: *mut uint8_t,
        private_key: *mut uint8_t,
    );
    fn Hacl_Ed25519_expand_keys(expanded_keys: *mut uint8_t, private_key: *mut uint8_t);
    fn Hacl_Ed25519_sign_expanded(
        signature: *mut uint8_t,
        expanded_keys: *mut uint8_t,
        msg_len: uint32_t,
        msg: *mut uint8_t,
    );
    fn Hacl_Ed25519_sign(
        signature: *mut uint8_t,
        private_key: *mut uint8_t,
        msg_len: uint32_t,
        msg: *mut uint8_t,
    );
    fn Hacl_Ed25519_verify(
        public_key: *mut uint8_t,
        msg_len: uint32_t,
        msg: *mut uint8_t,
        signature: *mut uint8_t,
    ) -> bool;
}
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Ed25519_secret_to_public(
    mut public_key: *mut uint8_t,
    mut private_key: *mut uint8_t,
) {
    Hacl_Ed25519_secret_to_public(public_key, private_key);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Ed25519_expand_keys(
    mut expanded_keys: *mut uint8_t,
    mut private_key: *mut uint8_t,
) {
    Hacl_Ed25519_expand_keys(expanded_keys, private_key);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Ed25519_sign_expanded(
    mut signature: *mut uint8_t,
    mut expanded_keys: *mut uint8_t,
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
) {
    Hacl_Ed25519_sign_expanded(signature, expanded_keys, msg_len, msg);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Ed25519_sign(
    mut signature: *mut uint8_t,
    mut private_key: *mut uint8_t,
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
) {
    Hacl_Ed25519_sign(signature, private_key, msg_len, msg);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Ed25519_verify(
    mut public_key: *mut uint8_t,
    mut msg_len: uint32_t,
    mut msg: *mut uint8_t,
    mut signature: *mut uint8_t,
) -> bool {
    return Hacl_Ed25519_verify(public_key, msg_len, msg, signature);
}
