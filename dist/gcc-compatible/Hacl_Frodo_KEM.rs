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
    fn Lib_RandomBuffer_System_randombytes(buf: *mut uint8_t, len: uint32_t) -> bool;
}
pub type uint8_t = libc::c_uchar;
pub type uint32_t = libc::c_uint;
#[no_mangle]
pub unsafe extern "C" fn randombytes_(mut len: uint32_t, mut res: *mut uint8_t) {
    let mut b: bool = Lib_RandomBuffer_System_randombytes(res, len);
}
