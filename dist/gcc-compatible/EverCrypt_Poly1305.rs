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
    fn Hacl_MAC_Poly1305_Simd128_mac(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
        key: *mut uint8_t,
    );
    fn Hacl_MAC_Poly1305_mac(
        output: *mut uint8_t,
        input: *mut uint8_t,
        input_len: uint32_t,
        key: *mut uint8_t,
    );
    fn EverCrypt_AutoConfig2_has_vec128() -> bool;
    fn EverCrypt_AutoConfig2_has_vec256() -> bool;
}
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
unsafe extern "C" fn poly1305_vale(
    mut dst: *mut uint8_t,
    mut src: *mut uint8_t,
    mut len: uint32_t,
    mut key: *mut uint8_t,
) {}
#[no_mangle]
pub unsafe extern "C" fn EverCrypt_Poly1305_mac(
    mut output: *mut uint8_t,
    mut input: *mut uint8_t,
    mut input_len: uint32_t,
    mut key: *mut uint8_t,
) {
    let mut vec256: bool = EverCrypt_AutoConfig2_has_vec256();
    let mut vec128: bool = EverCrypt_AutoConfig2_has_vec128();
    if vec128 {
        Hacl_MAC_Poly1305_Simd128_mac(output, input, input_len, key);
        return;
    }
    Hacl_MAC_Poly1305_mac(output, input, input_len, key);
}
