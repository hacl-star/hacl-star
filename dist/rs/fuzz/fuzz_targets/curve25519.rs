#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // fuzzed code goes here
    if data.len() != 32 {
        return;
    }
    let mut priv_ = [ 0; 32 ];
    let mut pub_ = [ 0; 32 ];
    priv_.copy_from_slice(data);
    hacl_rs::hacl::curve25519_51::secret_to_public(&mut pub_, &mut priv_);
});
