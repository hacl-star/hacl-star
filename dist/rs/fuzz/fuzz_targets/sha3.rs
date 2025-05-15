#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut data = data.to_vec();
    let data_len = data.len() as u32;
    let mut digest = [0u8; 28];
    hacl_rs::hacl::hash_sha3::sha3_224(&mut digest, &mut data, data_len);
});
