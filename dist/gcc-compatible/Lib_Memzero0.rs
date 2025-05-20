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
    fn memset_s(
        __s: *mut libc::c_void,
        __smax: rsize_t,
        __c: libc::c_int,
        __n: rsize_t,
    ) -> errno_t;
}
pub type __darwin_size_t = libc::c_ulong;
pub type size_t = __darwin_size_t;
pub type rsize_t = __darwin_size_t;
pub type errno_t = libc::c_int;
pub type uint64_t = libc::c_ulonglong;
#[no_mangle]
pub unsafe extern "C" fn Lib_Memzero0_memzero0(
    mut dst: *mut libc::c_void,
    mut len: uint64_t,
) {
    let mut len_: size_t = len as size_t;
    memset_s(dst, len_, 0 as libc::c_int, len_);
}
