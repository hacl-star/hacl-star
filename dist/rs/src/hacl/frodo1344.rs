#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub const crypto_bytes: u32 = 32u32;

pub const crypto_publickeybytes: u32 = 21520u32;

pub const crypto_secretkeybytes: u32 = 43088u32;

pub const crypto_ciphertextbytes: u32 = 21632u32;

pub fn crypto_kem_keypair(pk: &mut [u8], sk: &mut [u8]) -> u32
{
    let mut coins: [u8; 80] = [0u8; 80usize];
    crate::hacl::frodo_kem::randombytes_(80u32, &mut coins);
    let s: (&[u8], &[u8]) = coins.split_at(0usize);
    let seed_se: (&[u8], &[u8]) = s.1.split_at(32usize);
    let z: (&[u8], &[u8]) = seed_se.1.split_at(32usize);
    let seed_a: (&mut [u8], &mut [u8]) = pk.split_at_mut(0usize);
    crate::hacl::hash_sha3::shake256(seed_a.1, 16u32, z.1, 16u32);
    let b_bytes: (&mut [u8], &mut [u8]) = seed_a.1.split_at_mut(16usize);
    let s_bytes: (&mut [u8], &mut [u8]) = sk.split_at_mut(21552usize);
    let mut s_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut e_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut r: [u8; 43008] = [0u8; 43008usize];
    let mut shake_input_seed_se: [u8; 33] = [0u8; 33usize];
    (&mut shake_input_seed_se)[0usize] = 0x5fu8;
    ((&mut shake_input_seed_se)[1usize..1usize + 32usize]).copy_from_slice(&z.0[0usize..32usize]);
    crate::hacl::hash_sha3::shake256(&mut r, 43008u32, &shake_input_seed_se, 33u32);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 33u32);
    crate::hacl::frodo_kem::frodo_sample_matrix1344(1344u32, 8u32, &(&r)[0usize..], &mut s_matrix);
    crate::hacl::frodo_kem::frodo_sample_matrix1344(
        1344u32,
        8u32,
        &(&r)[21504usize..],
        &mut e_matrix
    );
    let mut b_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut a_matrix: [u16; 1806336] = [0u16; 1806336usize];
    crate::hacl::frodo_kem::frodo_gen_matrix(
        crate::hacl::spec::frodo_gen_a::SHAKE128,
        1344u32,
        b_bytes.0,
        &mut a_matrix
    );
    crate::hacl::frodo_kem::matrix_mul_s(
        1344u32,
        1344u32,
        8u32,
        &a_matrix,
        &s_matrix,
        &mut b_matrix
    );
    crate::hacl::frodo_kem::matrix_add(1344u32, 8u32, &mut b_matrix, &e_matrix);
    crate::hacl::frodo_kem::frodo_pack(1344u32, 8u32, 16u32, &b_matrix, b_bytes.1);
    crate::hacl::frodo_kem::matrix_to_lbytes(1344u32, 8u32, &s_matrix, s_bytes.1);
    crate::lib::memzero0::memzero::<u16>(&mut s_matrix, 10752u32);
    crate::lib::memzero0::memzero::<u16>(&mut e_matrix, 10752u32);
    let slen1: u32 = 43056u32;
    let sk_p: (&mut [u8], &mut [u8]) = s_bytes.0.split_at_mut(0usize);
    (sk_p.1[0usize..32usize]).copy_from_slice(&seed_se.0[0usize..32usize]);
    (sk_p.1[32usize..32usize + 21520usize]).copy_from_slice(&pk[0usize..21520usize]);
    crate::hacl::hash_sha3::shake256(&mut sk[slen1 as usize..], 32u32, pk, 21520u32);
    crate::lib::memzero0::memzero::<u8>(&mut coins, 80u32);
    0u32
}

pub fn crypto_kem_enc(ct: &mut [u8], ss: &mut [u8], pk: &[u8]) -> u32
{
    let mut coins: [u8; 32] = [0u8; 32usize];
    crate::hacl::frodo_kem::randombytes_(32u32, &mut coins);
    let mut seed_se_k: [u8; 64] = [0u8; 64usize];
    let mut pkh_mu: [u8; 64] = [0u8; 64usize];
    crate::hacl::hash_sha3::shake256(&mut (&mut pkh_mu)[0usize..], 32u32, pk, 21520u32);
    ((&mut pkh_mu)[32usize..32usize + 32usize]).copy_from_slice(&(&coins)[0usize..32usize]);
    crate::hacl::hash_sha3::shake256(&mut seed_se_k, 64u32, &pkh_mu, 64u32);
    let seed_se: (&[u8], &[u8]) = seed_se_k.split_at(0usize);
    let k: (&[u8], &[u8]) = seed_se.1.split_at(32usize);
    let seed_a: (&[u8], &[u8]) = pk.split_at(0usize);
    let b: (&[u8], &[u8]) = seed_a.1.split_at(16usize);
    let mut sp_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut ep_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut epp_matrix: [u16; 64] = [0u16; 64usize];
    let mut r: [u8; 43136] = [0u8; 43136usize];
    let mut shake_input_seed_se: [u8; 33] = [0u8; 33usize];
    (&mut shake_input_seed_se)[0usize] = 0x96u8;
    ((&mut shake_input_seed_se)[1usize..1usize + 32usize]).copy_from_slice(&k.0[0usize..32usize]);
    crate::hacl::hash_sha3::shake256(&mut r, 43136u32, &shake_input_seed_se, 33u32);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 33u32);
    crate::hacl::frodo_kem::frodo_sample_matrix1344(8u32, 1344u32, &(&r)[0usize..], &mut sp_matrix);
    crate::hacl::frodo_kem::frodo_sample_matrix1344(
        8u32,
        1344u32,
        &(&r)[21504usize..],
        &mut ep_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix1344(
        8u32,
        8u32,
        &(&r)[43008usize..],
        &mut epp_matrix
    );
    let c1: (&mut [u8], &mut [u8]) = ct.split_at_mut(0usize);
    let c2: (&mut [u8], &mut [u8]) = c1.1.split_at_mut(21504usize);
    let mut bp_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut a_matrix: [u16; 1806336] = [0u16; 1806336usize];
    crate::hacl::frodo_kem::frodo_gen_matrix(
        crate::hacl::spec::frodo_gen_a::SHAKE128,
        1344u32,
        b.0,
        &mut a_matrix
    );
    crate::hacl::frodo_kem::matrix_mul(
        8u32,
        1344u32,
        1344u32,
        &sp_matrix,
        &a_matrix,
        &mut bp_matrix
    );
    crate::hacl::frodo_kem::matrix_add(8u32, 1344u32, &mut bp_matrix, &ep_matrix);
    crate::hacl::frodo_kem::frodo_pack(8u32, 1344u32, 16u32, &bp_matrix, c2.0);
    let mut v_matrix: [u16; 64] = [0u16; 64usize];
    let mut b_matrix: [u16; 10752] = [0u16; 10752usize];
    crate::hacl::frodo_kem::frodo_unpack(1344u32, 8u32, 16u32, b.1, &mut b_matrix);
    crate::hacl::frodo_kem::matrix_mul(8u32, 1344u32, 8u32, &sp_matrix, &b_matrix, &mut v_matrix);
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut v_matrix, &epp_matrix);
    let mut mu_encode: [u16; 64] = [0u16; 64usize];
    crate::hacl::frodo_kem::frodo_key_encode(16u32, 4u32, 8u32, &coins, &mut mu_encode);
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut v_matrix, &mu_encode);
    crate::lib::memzero0::memzero::<u16>(&mut mu_encode, 64u32);
    crate::hacl::frodo_kem::frodo_pack(8u32, 8u32, 16u32, &v_matrix, c2.1);
    crate::lib::memzero0::memzero::<u16>(&mut v_matrix, 64u32);
    crate::lib::memzero0::memzero::<u16>(&mut sp_matrix, 10752u32);
    crate::lib::memzero0::memzero::<u16>(&mut ep_matrix, 10752u32);
    crate::lib::memzero0::memzero::<u16>(&mut epp_matrix, 64u32);
    let ss_init_len: u32 = 21664u32;
    let mut shake_input_ss: Vec<u8> = vec![0u8; ss_init_len as usize];
    ((&mut shake_input_ss)[0usize..21632usize]).copy_from_slice(&ct[0usize..21632usize]);
    ((&mut shake_input_ss)[21632usize..21632usize + 32usize]).copy_from_slice(
        &k.1[0usize..32usize]
    );
    crate::hacl::hash_sha3::shake256(ss, 32u32, &shake_input_ss, ss_init_len);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_ss, ss_init_len);
    crate::lib::memzero0::memzero::<u8>(&mut seed_se_k, 64u32);
    crate::lib::memzero0::memzero::<u8>(&mut coins, 32u32);
    0u32
}

pub fn crypto_kem_dec(ss: &mut [u8], ct: &[u8], sk: &[u8]) -> u32
{
    let mut bp_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut c_matrix: [u16; 64] = [0u16; 64usize];
    let c1: (&[u8], &[u8]) = ct.split_at(0usize);
    let c2: (&[u8], &[u8]) = c1.1.split_at(21504usize);
    crate::hacl::frodo_kem::frodo_unpack(8u32, 1344u32, 16u32, c2.0, &mut bp_matrix);
    crate::hacl::frodo_kem::frodo_unpack(8u32, 8u32, 16u32, c2.1, &mut c_matrix);
    let mut mu_decode: [u8; 32] = [0u8; 32usize];
    let s_bytes: (&[u8], &[u8]) = sk.split_at(21552usize);
    let mut s_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut m_matrix: [u16; 64] = [0u16; 64usize];
    crate::hacl::frodo_kem::matrix_from_lbytes(1344u32, 8u32, s_bytes.1, &mut s_matrix);
    crate::hacl::frodo_kem::matrix_mul_s(8u32, 1344u32, 8u32, &bp_matrix, &s_matrix, &mut m_matrix);
    crate::hacl::frodo_kem::matrix_sub(8u32, 8u32, &c_matrix, &mut m_matrix);
    crate::hacl::frodo_kem::frodo_key_decode(16u32, 4u32, 8u32, &m_matrix, &mut mu_decode);
    crate::lib::memzero0::memzero::<u16>(&mut s_matrix, 10752u32);
    crate::lib::memzero0::memzero::<u16>(&mut m_matrix, 64u32);
    let mut seed_se_k: [u8; 64] = [0u8; 64usize];
    let pkh_mu_decode_len: u32 = 64u32;
    let mut pkh_mu_decode: Vec<u8> = vec![0u8; pkh_mu_decode_len as usize];
    let pkh: (&[u8], &[u8]) = s_bytes.1.split_at(21504usize);
    ((&mut pkh_mu_decode)[0usize..32usize]).copy_from_slice(&pkh.1[0usize..32usize]);
    ((&mut pkh_mu_decode)[32usize..32usize + 32usize]).copy_from_slice(
        &(&mu_decode)[0usize..32usize]
    );
    crate::hacl::hash_sha3::shake256(&mut seed_se_k, 64u32, &pkh_mu_decode, pkh_mu_decode_len);
    let seed_se: (&[u8], &[u8]) = seed_se_k.split_at(0usize);
    let kp: (&[u8], &[u8]) = seed_se.1.split_at(32usize);
    let s: (&[u8], &[u8]) = s_bytes.0.split_at(0usize);
    let mut bpp_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut cp_matrix: [u16; 64] = [0u16; 64usize];
    let mut sp_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut ep_matrix: [u16; 10752] = [0u16; 10752usize];
    let mut epp_matrix: [u16; 64] = [0u16; 64usize];
    let mut r: [u8; 43136] = [0u8; 43136usize];
    let mut shake_input_seed_se: [u8; 33] = [0u8; 33usize];
    (&mut shake_input_seed_se)[0usize] = 0x96u8;
    ((&mut shake_input_seed_se)[1usize..1usize + 32usize]).copy_from_slice(&kp.0[0usize..32usize]);
    crate::hacl::hash_sha3::shake256(&mut r, 43136u32, &shake_input_seed_se, 33u32);
    crate::lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 33u32);
    crate::hacl::frodo_kem::frodo_sample_matrix1344(8u32, 1344u32, &(&r)[0usize..], &mut sp_matrix);
    crate::hacl::frodo_kem::frodo_sample_matrix1344(
        8u32,
        1344u32,
        &(&r)[21504usize..],
        &mut ep_matrix
    );
    crate::hacl::frodo_kem::frodo_sample_matrix1344(
        8u32,
        8u32,
        &(&r)[43008usize..],
        &mut epp_matrix
    );
    let pk: (&[u8], &[u8]) = s.1.split_at(32usize);
    let seed_a: (&[u8], &[u8]) = pk.1.split_at(0usize);
    let b: (&[u8], &[u8]) = seed_a.1.split_at(16usize);
    let mut a_matrix: [u16; 1806336] = [0u16; 1806336usize];
    crate::hacl::frodo_kem::frodo_gen_matrix(
        crate::hacl::spec::frodo_gen_a::SHAKE128,
        1344u32,
        b.0,
        &mut a_matrix
    );
    crate::hacl::frodo_kem::matrix_mul(
        8u32,
        1344u32,
        1344u32,
        &sp_matrix,
        &a_matrix,
        &mut bpp_matrix
    );
    crate::hacl::frodo_kem::matrix_add(8u32, 1344u32, &mut bpp_matrix, &ep_matrix);
    let mut b_matrix: [u16; 10752] = [0u16; 10752usize];
    crate::hacl::frodo_kem::frodo_unpack(1344u32, 8u32, 16u32, b.1, &mut b_matrix);
    crate::hacl::frodo_kem::matrix_mul(8u32, 1344u32, 8u32, &sp_matrix, &b_matrix, &mut cp_matrix);
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut cp_matrix, &epp_matrix);
    let mut mu_encode: [u16; 64] = [0u16; 64usize];
    crate::hacl::frodo_kem::frodo_key_encode(16u32, 4u32, 8u32, &mu_decode, &mut mu_encode);
    crate::hacl::frodo_kem::matrix_add(8u32, 8u32, &mut cp_matrix, &mu_encode);
    crate::lib::memzero0::memzero::<u16>(&mut mu_encode, 64u32);
    crate::hacl::frodo_kem::mod_pow2(8u32, 1344u32, 16u32, &mut bpp_matrix);
    crate::hacl::frodo_kem::mod_pow2(8u32, 8u32, 16u32, &mut cp_matrix);
    crate::lib::memzero0::memzero::<u16>(&mut sp_matrix, 10752u32);
    crate::lib::memzero0::memzero::<u16>(&mut ep_matrix, 10752u32);
    crate::lib::memzero0::memzero::<u16>(&mut epp_matrix, 64u32);
    let b1: u16 = crate::hacl::frodo_kem::matrix_eq(8u32, 1344u32, &bp_matrix, &bpp_matrix);
    let b2: u16 = crate::hacl::frodo_kem::matrix_eq(8u32, 8u32, &c_matrix, &cp_matrix);
    let mask: u16 = b1 & b2;
    let mask0: u16 = mask;
    let mut kp_s: [u8; 32] = [0u8; 32usize];
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u8 = pk.0[i as usize];
            let x: u8 = uu____0 ^ mask0 as u8 & (kp.1[i as usize] ^ uu____0);
            let os: (&mut [u8], &mut [u8]) = kp_s.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let ss_init_len: u32 = 21664u32;
    let mut ss_init: Vec<u8> = vec![0u8; ss_init_len as usize];
    ((&mut ss_init)[0usize..21632usize]).copy_from_slice(&ct[0usize..21632usize]);
    ((&mut ss_init)[21632usize..21632usize + 32usize]).copy_from_slice(&(&kp_s)[0usize..32usize]);
    crate::hacl::hash_sha3::shake256(ss, 32u32, &ss_init, ss_init_len);
    crate::lib::memzero0::memzero::<u8>(&mut ss_init, ss_init_len);
    crate::lib::memzero0::memzero::<u8>(&mut kp_s, 32u32);
    crate::lib::memzero0::memzero::<u8>(&mut seed_se_k, 64u32);
    crate::lib::memzero0::memzero::<u8>(&mut mu_decode, 32u32);
    0u32
}
