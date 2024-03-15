#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub const crypto_bytes: u32 = 24u32;

pub const crypto_publickeybytes: u32 = 15632u32;

pub const crypto_secretkeybytes: u32 = 31296u32;

pub const crypto_ciphertextbytes: u32 = 15744u32;

pub fn crypto_kem_keypair(pk: &mut [u8], sk: &mut [u8]) -> u32
{
    let mut coins: [u8; 64] = [0u8; 64usize];
    crate::hacl::frodo_kem::randombytes_(64u32, &mut coins);
    let s: (&mut [u8], &mut [u8]) = (&mut coins).split_at_mut(0usize);
    let seed_se: (&mut [u8], &mut [u8]) = s.1.split_at_mut(24usize);
    let z: (&mut [u8], &mut [u8]) = seed_se.1.split_at_mut(24usize);
    let seed_a: (&mut [u8], &mut [u8]) = pk.split_at_mut(0usize);
    crate::hacl::hash_sha3::shake256_hacl(16u32, z.1, 16u32, seed_a.1);
    let b_bytes: (&mut [u8], &mut [u8]) = seed_a.1.split_at_mut(16usize);
    let s_bytes: (&mut [u8], &mut [u8]) = sk.split_at_mut(15656usize);
    let mut s_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut e_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut r: [u8; 31232] = [0u8; 31232usize];
    let mut shake_input_seed_se: [u8; 25] = [0u8; 25usize];
    (&mut shake_input_seed_se)[0usize] = 0x5fu8;
    ((&mut shake_input_seed_se)[1usize..1usize + 24usize]).copy_from_slice(&z.0[0usize..24usize]);
    crate::hacl::hash_sha3::shake256_hacl(25u32, &mut shake_input_seed_se, 31232u32, &mut r);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 25u32);
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        976u32,
        8u32,
        &mut (&mut r)[0usize..],
        &mut s_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        976u32,
        8u32,
        &mut (&mut r)[15616usize..],
        &mut e_matrix
    );
    let mut b_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut a_matrix: [u16; 952576] = [0u16; 952576usize];
    crate::hacl::frodo_kem::frodo_gen_matrix(
        crate::hacl::spec::frodo_gen_a::SHAKE128,
        976u32,
        b_bytes.0,
        &mut a_matrix
    );
    crate::hacl::frodo_kem::matrix_mul_s(
        976u32,
        976u32,
        8u32,
        &mut a_matrix,
        &mut s_matrix,
        &mut b_matrix
    );
    crate::hacl::frodo_kem::matrix_add(976u32, 8u32, &mut b_matrix, &mut e_matrix);
    crate::hacl::frodo_kem::frodo_pack(976u32, 8u32, 16u32, &mut b_matrix, b_bytes.1);
    crate::hacl::frodo_kem::matrix_to_lbytes(976u32, 8u32, &mut s_matrix, s_bytes.1);
    crate::lib::memzero0::memzero::<u16>(&mut s_matrix, 7808u32);
    crate::lib::memzero0::memzero::<u16>(&mut e_matrix, 7808u32);
    let slen1: u32 = 31272u32;
    let sk_p: (&mut [u8], &mut [u8]) = s_bytes.0.split_at_mut(0usize);
    (sk_p.1[0usize..24usize]).copy_from_slice(&seed_se.0[0usize..24usize]);
    (sk_p.1[24usize..24usize + 15632usize]).copy_from_slice(&pk[0usize..15632usize]);
    crate::hacl::hash_sha3::shake256_hacl(15632u32, pk, 24u32, &mut sk[slen1 as usize..]);
    crate::lib::memzero0::memzero::<u8>(&mut coins, 64u32);
    0u32
}

pub fn crypto_kem_enc(ct: &mut [u8], ss: &mut [u8], pk: &mut [u8]) -> u32
{
    let mut coins: [u8; 24] = [0u8; 24usize];
    crate::hacl::frodo_kem::randombytes_(24u32, &mut coins);
    let mut seed_se_k: [u8; 48] = [0u8; 48usize];
    let mut pkh_mu: [u8; 48] = [0u8; 48usize];
    crate::hacl::hash_sha3::shake256_hacl(15632u32, pk, 24u32, &mut (&mut pkh_mu)[0usize..]);
    ((&mut pkh_mu)[24usize..24usize + 24usize]).copy_from_slice(&(&mut coins)[0usize..24usize]);
    crate::hacl::hash_sha3::shake256_hacl(48u32, &mut pkh_mu, 48u32, &mut seed_se_k);
    let seed_se: (&mut [u8], &mut [u8]) = (&mut seed_se_k).split_at_mut(0usize);
    let k: (&mut [u8], &mut [u8]) = seed_se.1.split_at_mut(24usize);
    let seed_a: (&mut [u8], &mut [u8]) = pk.split_at_mut(0usize);
    let b: (&mut [u8], &mut [u8]) = seed_a.1.split_at_mut(16usize);
    let mut sp_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut ep_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut epp_matrix: [u16; 64] = [0u16; 64usize];
    let mut r: [u8; 31360] = [0u8; 31360usize];
    let mut shake_input_seed_se: [u8; 25] = [0u8; 25usize];
    (&mut shake_input_seed_se)[0usize] = 0x96u8;
    ((&mut shake_input_seed_se)[1usize..1usize + 24usize]).copy_from_slice(&k.0[0usize..24usize]);
    crate::hacl::hash_sha3::shake256_hacl(25u32, &mut shake_input_seed_se, 31360u32, &mut r);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 25u32);
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        8u32,
        976u32,
        &mut (&mut r)[0usize..],
        &mut sp_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        8u32,
        976u32,
        &mut (&mut r)[15616usize..],
        &mut ep_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        8u32,
        8u32,
        &mut (&mut r)[31232usize..],
        &mut epp_matrix
    );
    let c1: (&mut [u8], &mut [u8]) = ct.split_at_mut(0usize);
    let c2: (&mut [u8], &mut [u8]) = c1.1.split_at_mut(15616usize);
    let mut bp_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut a_matrix: [u16; 952576] = [0u16; 952576usize];
    crate::hacl::frodo_kem::frodo_gen_matrix(
        crate::hacl::spec::frodo_gen_a::SHAKE128,
        976u32,
        b.0,
        &mut a_matrix
    );
    crate::hacl::frodo_kem::matrix_mul(
        8u32,
        976u32,
        976u32,
        &mut sp_matrix,
        &mut a_matrix,
        &mut bp_matrix
    );
    crate::hacl::frodo_kem::matrix_add(8u32, 976u32, &mut bp_matrix, &mut ep_matrix);
    crate::hacl::frodo_kem::frodo_pack(8u32, 976u32, 16u32, &mut bp_matrix, c2.0);
    let mut v_matrix: [u16; 64] = [0u16; 64usize];
    let mut b_matrix: [u16; 7808] = [0u16; 7808usize];
    crate::hacl::frodo_kem::frodo_unpack(976u32, 8u32, 16u32, b.1, &mut b_matrix);
    crate::hacl::frodo_kem::matrix_mul(
        8u32,
        976u32,
        8u32,
        &mut sp_matrix,
        &mut b_matrix,
        &mut v_matrix
    );
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut v_matrix, &mut epp_matrix);
    let mut mu_encode: [u16; 64] = [0u16; 64usize];
    crate::hacl::frodo_kem::frodo_key_encode(16u32, 3u32, 8u32, &mut coins, &mut mu_encode);
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut v_matrix, &mut mu_encode);
    crate::lib::memzero0::memzero::<u16>(&mut mu_encode, 64u32);
    crate::hacl::frodo_kem::frodo_pack(8u32, 8u32, 16u32, &mut v_matrix, c2.1);
    crate::lib::memzero0::memzero::<u16>(&mut v_matrix, 64u32);
    crate::lib::memzero0::memzero::<u16>(&mut sp_matrix, 7808u32);
    crate::lib::memzero0::memzero::<u16>(&mut ep_matrix, 7808u32);
    crate::lib::memzero0::memzero::<u16>(&mut epp_matrix, 64u32);
    let ss_init_len: u32 = 15768u32;
    let mut shake_input_ss: Vec<u8> = vec![0u8; ss_init_len as usize];
    ((&mut shake_input_ss)[0usize..15744usize]).copy_from_slice(&ct[0usize..15744usize]);
    ((&mut shake_input_ss)[15744usize..15744usize + 24usize]).copy_from_slice(
        &k.1[0usize..24usize]
    );
    crate::hacl::hash_sha3::shake256_hacl(ss_init_len, &mut shake_input_ss, 24u32, ss);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_ss, ss_init_len);
    crate::lib::memzero0::memzero::<u8>(&mut seed_se_k, 48u32);
    crate::lib::memzero0::memzero::<u8>(&mut coins, 24u32);
    0u32
}

pub fn crypto_kem_dec(ss: &mut [u8], ct: &mut [u8], sk: &mut [u8]) -> u32
{
    let mut bp_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut c_matrix: [u16; 64] = [0u16; 64usize];
    let c1: (&mut [u8], &mut [u8]) = ct.split_at_mut(0usize);
    let c2: (&mut [u8], &mut [u8]) = c1.1.split_at_mut(15616usize);
    crate::hacl::frodo_kem::frodo_unpack(8u32, 976u32, 16u32, c2.0, &mut bp_matrix);
    crate::hacl::frodo_kem::frodo_unpack(8u32, 8u32, 16u32, c2.1, &mut c_matrix);
    let mut mu_decode: [u8; 24] = [0u8; 24usize];
    let s_bytes: (&mut [u8], &mut [u8]) = sk.split_at_mut(15656usize);
    let mut s_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut m_matrix: [u16; 64] = [0u16; 64usize];
    crate::hacl::frodo_kem::matrix_from_lbytes(976u32, 8u32, s_bytes.1, &mut s_matrix);
    crate::hacl::frodo_kem::matrix_mul_s(
        8u32,
        976u32,
        8u32,
        &mut bp_matrix,
        &mut s_matrix,
        &mut m_matrix
    );
    crate::hacl::frodo_kem::matrix_sub(8u32, 8u32, &mut c_matrix, &mut m_matrix);
    crate::hacl::frodo_kem::frodo_key_decode(16u32, 3u32, 8u32, &mut m_matrix, &mut mu_decode);
    crate::lib::memzero0::memzero::<u16>(&mut s_matrix, 7808u32);
    crate::lib::memzero0::memzero::<u16>(&mut m_matrix, 64u32);
    let mut seed_se_k: [u8; 48] = [0u8; 48usize];
    let pkh_mu_decode_len: u32 = 48u32;
    let mut pkh_mu_decode: Vec<u8> = vec![0u8; pkh_mu_decode_len as usize];
    let pkh: (&mut [u8], &mut [u8]) = s_bytes.1.split_at_mut(15616usize);
    ((&mut pkh_mu_decode)[0usize..24usize]).copy_from_slice(&pkh.1[0usize..24usize]);
    ((&mut pkh_mu_decode)[24usize..24usize + 24usize]).copy_from_slice(
        &(&mut mu_decode)[0usize..24usize]
    );
    crate::hacl::hash_sha3::shake256_hacl(
        pkh_mu_decode_len,
        &mut pkh_mu_decode,
        48u32,
        &mut seed_se_k
    );
    let seed_se: (&mut [u8], &mut [u8]) = (&mut seed_se_k).split_at_mut(0usize);
    let kp: (&mut [u8], &mut [u8]) = seed_se.1.split_at_mut(24usize);
    let s: (&mut [u8], &mut [u8]) = s_bytes.0.split_at_mut(0usize);
    let mut bpp_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut cp_matrix: [u16; 64] = [0u16; 64usize];
    let mut sp_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut ep_matrix: [u16; 7808] = [0u16; 7808usize];
    let mut epp_matrix: [u16; 64] = [0u16; 64usize];
    let mut r: [u8; 31360] = [0u8; 31360usize];
    let mut shake_input_seed_se: [u8; 25] = [0u8; 25usize];
    (&mut shake_input_seed_se)[0usize] = 0x96u8;
    ((&mut shake_input_seed_se)[1usize..1usize + 24usize]).copy_from_slice(&kp.0[0usize..24usize]);
    crate::hacl::hash_sha3::shake256_hacl(25u32, &mut shake_input_seed_se, 31360u32, &mut r);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 25u32);
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        8u32,
        976u32,
        &mut (&mut r)[0usize..],
        &mut sp_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        8u32,
        976u32,
        &mut (&mut r)[15616usize..],
        &mut ep_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix976(
        8u32,
        8u32,
        &mut (&mut r)[31232usize..],
        &mut epp_matrix
    );
    let pk: (&mut [u8], &mut [u8]) = s.1.split_at_mut(24usize);
    let seed_a: (&mut [u8], &mut [u8]) = pk.1.split_at_mut(0usize);
    let b: (&mut [u8], &mut [u8]) = seed_a.1.split_at_mut(16usize);
    let mut a_matrix: [u16; 952576] = [0u16; 952576usize];
    crate::hacl::frodo_kem::frodo_gen_matrix(
        crate::hacl::spec::frodo_gen_a::SHAKE128,
        976u32,
        b.0,
        &mut a_matrix
    );
    crate::hacl::frodo_kem::matrix_mul(
        8u32,
        976u32,
        976u32,
        &mut sp_matrix,
        &mut a_matrix,
        &mut bpp_matrix
    );
    crate::hacl::frodo_kem::matrix_add(8u32, 976u32, &mut bpp_matrix, &mut ep_matrix);
    let mut b_matrix: [u16; 7808] = [0u16; 7808usize];
    crate::hacl::frodo_kem::frodo_unpack(976u32, 8u32, 16u32, b.1, &mut b_matrix);
    crate::hacl::frodo_kem::matrix_mul(
        8u32,
        976u32,
        8u32,
        &mut sp_matrix,
        &mut b_matrix,
        &mut cp_matrix
    );
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut cp_matrix, &mut epp_matrix);
    let mut mu_encode: [u16; 64] = [0u16; 64usize];
    crate::hacl::frodo_kem::frodo_key_encode(16u32, 3u32, 8u32, &mut mu_decode, &mut mu_encode);
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut cp_matrix, &mut mu_encode);
    crate::lib::memzero0::memzero::<u16>(&mut mu_encode, 64u32);
    crate::hacl::frodo_kem::mod_pow2(8u32, 976u32, 16u32, &mut bpp_matrix);
    crate::hacl::frodo_kem::mod_pow2(8u32, 8u32, 16u32, &mut cp_matrix);
    crate::lib::memzero0::memzero::<u16>(&mut sp_matrix, 7808u32);
    crate::lib::memzero0::memzero::<u16>(&mut ep_matrix, 7808u32);
    crate::lib::memzero0::memzero::<u16>(&mut epp_matrix, 64u32);
    let b1: u16 = crate::hacl::frodo_kem::matrix_eq(8u32, 976u32, &mut bp_matrix, &mut bpp_matrix);
    let b2: u16 = crate::hacl::frodo_kem::matrix_eq(8u32, 8u32, &mut c_matrix, &mut cp_matrix);
    let mask: u16 = b1 & b2;
    let mask0: u16 = mask;
    let mut kp_s: [u8; 24] = [0u8; 24usize];
    for i in 0u32..24u32
    {
        let uu____0: u8 = pk.0[i as usize];
        let x: u8 = uu____0 ^ mask0 as u8 & (kp.1[i as usize] ^ uu____0);
        let os: (&mut [u8], &mut [u8]) = (&mut kp_s).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let ss_init_len: u32 = 15768u32;
    let mut ss_init: Vec<u8> = vec![0u8; ss_init_len as usize];
    ((&mut ss_init)[0usize..15744usize]).copy_from_slice(&ct[0usize..15744usize]);
    ((&mut ss_init)[15744usize..15744usize + 24usize]).copy_from_slice(
        &(&mut kp_s)[0usize..24usize]
    );
    crate::hacl::hash_sha3::shake256_hacl(ss_init_len, &mut ss_init, 24u32, ss);
    crate::lib::memzero0::memzero::<u8>(&mut ss_init, ss_init_len);
    crate::lib::memzero0::memzero::<u8>(&mut kp_s, 24u32);
    crate::lib::memzero0::memzero::<u8>(&mut seed_se_k, 48u32);
    crate::lib::memzero0::memzero::<u8>(&mut mu_decode, 24u32);
    0u32
}
