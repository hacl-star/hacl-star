#![no_main]

use libfuzzer_sys::fuzz_target;
use hacl_rs::hacl::p256;

fuzz_target!(|data: &[u8]| {
    // fuzzed code goes here
    if data.len() != 32 {
        return;
    }
    let mut priv_ = [ 0; 32 ];
    priv_.copy_from_slice(data);
    if ! p256::validate_private_key(&mut priv_) {
        return;
    }
    let mut pub_ = [ 0; 64 ];
    p256::dh_initiator(&mut pub_, &mut priv_);
});
