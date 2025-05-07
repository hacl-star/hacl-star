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
    fn Hacl_Curve25519_51_scalarmult(
        out: *mut uint8_t,
        priv_0: *mut uint8_t,
        pub_0: *mut uint8_t,
    );
    fn Hacl_Curve25519_51_secret_to_public(pub_0: *mut uint8_t, priv_0: *mut uint8_t);
    fn Hacl_Curve25519_51_ecdh(
        out: *mut uint8_t,
        priv_0: *mut uint8_t,
        pub_0: *mut uint8_t,
    ) -> bool;
}
pub type uint8_t = libc::c_uchar;
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Curve25519_secret_to_public(
    mut pub_0: *mut uint8_t,
    mut priv_0: *mut uint8_t,
) {
    Hacl_Curve25519_51_secret_to_public(pub_0, priv_0);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Curve25519_scalarmult(
    mut shared: *mut uint8_t,
    mut my_priv: *mut uint8_t,
    mut their_pub: *mut uint8_t,
) {
    Hacl_Curve25519_51_scalarmult(shared, my_priv, their_pub);
}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Curve25519_ecdh(
    mut shared: *mut uint8_t,
    mut my_priv: *mut uint8_t,
    mut their_pub: *mut uint8_t,
) -> bool {
    return Hacl_Curve25519_51_ecdh(shared, my_priv, their_pub);
}
