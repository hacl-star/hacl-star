#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub const crypto_bytes: u32 = 16u32;

pub const crypto_publickeybytes: u32 = 976u32;

pub const crypto_secretkeybytes: u32 = 2032u32;

pub const crypto_ciphertextbytes: u32 = 1080u32;

pub fn crypto_kem_keypair(pk: &mut [u8], sk: &mut [u8]) -> u32
{
    let mut coins: [u8; 48] = [0u8; 48usize];
    crate::frodo_kem::randombytes_(48u32, &mut coins);
    let s: (&[u8], &[u8]) = coins.split_at(0usize);
    let seed_se: (&[u8], &[u8]) = (s.1).split_at(16usize);
    let z: (&[u8], &[u8]) = (seed_se.1).split_at(16usize);
    let seed_a: (&mut [u8], &mut [u8]) = pk.split_at_mut(0usize);
    crate::hash_sha3::shake128(seed_a.1, 16u32, z.1, 16u32);
    let b_bytes: (&mut [u8], &mut [u8]) = (seed_a.1).split_at_mut(16usize);
    let s_bytes: (&mut [u8], &mut [u8]) = sk.split_at_mut(992usize);
    let mut s_matrix: [u16; 512] = [0u16; 512usize];
    let mut e_matrix: [u16; 512] = [0u16; 512usize];
    let mut r: [u8; 2048] = [0u8; 2048usize];
    let mut shake_input_seed_se: [u8; 17] = [0u8; 17usize];
    (&mut shake_input_seed_se)[0usize] = 0x5fu8;
    ((&mut shake_input_seed_se)[1usize..1usize + 16usize]).copy_from_slice(&z.0[0usize..16usize]);
    crate::hash_sha3::shake128(&mut r, 2048u32, &shake_input_seed_se, 17u32);
    lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 17u32);
    crate::frodo_kem::frodo_sample_matrix64(64u32, 8u32, &(&r)[0usize..], &mut s_matrix);
    crate::frodo_kem::frodo_sample_matrix64(64u32, 8u32, &(&r)[1024usize..], &mut e_matrix);
    let mut b_matrix: [u16; 512] = [0u16; 512usize];
    let mut a_matrix: [u16; 4096] = [0u16; 4096usize];
    crate::frodo_kem::frodo_gen_matrix(
        crate::spec::frodo_gen_a::SHAKE128,
        64u32,
        b_bytes.0,
        &mut a_matrix
    );
    crate::frodo_kem::matrix_mul_s(64u32, 64u32, 8u32, &a_matrix, &s_matrix, &mut b_matrix);
    crate::frodo_kem::matrix_add(64u32, 8u32, &mut b_matrix, &e_matrix);
    crate::frodo_kem::frodo_pack(64u32, 8u32, 15u32, &b_matrix, b_bytes.1);
    crate::frodo_kem::matrix_to_lbytes(64u32, 8u32, &s_matrix, s_bytes.1);
    lib::memzero0::memzero::<u16>(&mut s_matrix, 512u32);
    lib::memzero0::memzero::<u16>(&mut e_matrix, 512u32);
    let slen1: u32 = 2016u32;
    let sk_p: (&mut [u8], &mut [u8]) = (s_bytes.0).split_at_mut(0usize);
    (sk_p.1[0usize..16usize]).copy_from_slice(&seed_se.0[0usize..16usize]);
    (sk_p.1[16usize..16usize + 976usize]).copy_from_slice(&pk[0usize..976usize]);
    crate::hash_sha3::shake128(&mut sk[slen1 as usize..], 16u32, pk, 976u32);
    lib::memzero0::memzero::<u8>(&mut coins, 48u32);
    0u32
}

pub fn crypto_kem_enc(ct: &mut [u8], ss: &mut [u8], pk: &[u8]) -> u32
{
    let mut coins: [u8; 16] = [0u8; 16usize];
    crate::frodo_kem::randombytes_(16u32, &mut coins);
    let mut seed_se_k: [u8; 32] = [0u8; 32usize];
    let mut pkh_mu: [u8; 32] = [0u8; 32usize];
    crate::hash_sha3::shake128(&mut (&mut pkh_mu)[0usize..], 16u32, pk, 976u32);
    ((&mut pkh_mu)[16usize..16usize + 16usize]).copy_from_slice(&(&coins)[0usize..16usize]);
    crate::hash_sha3::shake128(&mut seed_se_k, 32u32, &pkh_mu, 32u32);
    let seed_se: (&[u8], &[u8]) = seed_se_k.split_at(0usize);
    let k: (&[u8], &[u8]) = (seed_se.1).split_at(16usize);
    let seed_a: (&[u8], &[u8]) = pk.split_at(0usize);
    let b: (&[u8], &[u8]) = (seed_a.1).split_at(16usize);
    let mut sp_matrix: [u16; 512] = [0u16; 512usize];
    let mut ep_matrix: [u16; 512] = [0u16; 512usize];
    let mut epp_matrix: [u16; 64] = [0u16; 64usize];
    let mut r: [u8; 2176] = [0u8; 2176usize];
    let mut shake_input_seed_se: [u8; 17] = [0u8; 17usize];
    (&mut shake_input_seed_se)[0usize] = 0x96u8;
    ((&mut shake_input_seed_se)[1usize..1usize + 16usize]).copy_from_slice(&k.0[0usize..16usize]);
    crate::hash_sha3::shake128(&mut r, 2176u32, &shake_input_seed_se, 17u32);
    lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 17u32);
    crate::frodo_kem::frodo_sample_matrix64(8u32, 64u32, &(&r)[0usize..], &mut sp_matrix);
    crate::frodo_kem::frodo_sample_matrix64(8u32, 64u32, &(&r)[1024usize..], &mut ep_matrix);
    crate::frodo_kem::frodo_sample_matrix64(8u32, 8u32, &(&r)[2048usize..], &mut epp_matrix);
    let c1: (&mut [u8], &mut [u8]) = ct.split_at_mut(0usize);
    let c2: (&mut [u8], &mut [u8]) = (c1.1).split_at_mut(960usize);
    let mut bp_matrix: [u16; 512] = [0u16; 512usize];
    let mut a_matrix: [u16; 4096] = [0u16; 4096usize];
    crate::frodo_kem::frodo_gen_matrix(
        crate::spec::frodo_gen_a::SHAKE128,
        64u32,
        b.0,
        &mut a_matrix
    );
    crate::frodo_kem::matrix_mul(8u32, 64u32, 64u32, &sp_matrix, &a_matrix, &mut bp_matrix);
    crate::frodo_kem::matrix_add(8u32, 64u32, &mut bp_matrix, &ep_matrix);
    crate::frodo_kem::frodo_pack(8u32, 64u32, 15u32, &bp_matrix, c2.0);
    let mut v_matrix: [u16; 64] = [0u16; 64usize];
    let mut b_matrix: [u16; 512] = [0u16; 512usize];
    crate::frodo_kem::frodo_unpack(64u32, 8u32, 15u32, b.1, &mut b_matrix);
    crate::frodo_kem::matrix_mul(8u32, 64u32, 8u32, &sp_matrix, &b_matrix, &mut v_matrix);
    crate::frodo_kem::matrix_add(8u32, 8u32, &mut v_matrix, &epp_matrix);
    let mut mu_encode: [u16; 64] = [0u16; 64usize];
    crate::frodo_kem::frodo_key_encode(15u32, 2u32, 8u32, &coins, &mut mu_encode);
    crate::frodo_kem::matrix_add(8u32, 8u32, &mut v_matrix, &mu_encode);
    lib::memzero0::memzero::<u16>(&mut mu_encode, 64u32);
    crate::frodo_kem::frodo_pack(8u32, 8u32, 15u32, &v_matrix, c2.1);
    lib::memzero0::memzero::<u16>(&mut v_matrix, 64u32);
    lib::memzero0::memzero::<u16>(&mut sp_matrix, 512u32);
    lib::memzero0::memzero::<u16>(&mut ep_matrix, 512u32);
    lib::memzero0::memzero::<u16>(&mut epp_matrix, 64u32);
    let ss_init_len: u32 = 1096u32;
    let mut shake_input_ss: Box<[u8]> = vec![0u8; ss_init_len as usize].into_boxed_slice();
    ((&mut shake_input_ss)[0usize..1080usize]).copy_from_slice(&ct[0usize..1080usize]);
    ((&mut shake_input_ss)[1080usize..1080usize + 16usize]).copy_from_slice(&k.1[0usize..16usize]);
    crate::hash_sha3::shake128(ss, 16u32, &shake_input_ss, ss_init_len);
    lib::memzero0::memzero::<u8>(&mut shake_input_ss, ss_init_len);
    lib::memzero0::memzero::<u8>(&mut seed_se_k, 32u32);
    lib::memzero0::memzero::<u8>(&mut coins, 16u32);
    0u32
}

pub fn crypto_kem_dec(ss: &mut [u8], ct: &[u8], sk: &[u8]) -> u32
{
    let mut bp_matrix: [u16; 512] = [0u16; 512usize];
    let mut c_matrix: [u16; 64] = [0u16; 64usize];
    let c1: (&[u8], &[u8]) = ct.split_at(0usize);
    let c2: (&[u8], &[u8]) = (c1.1).split_at(960usize);
    crate::frodo_kem::frodo_unpack(8u32, 64u32, 15u32, c2.0, &mut bp_matrix);
    crate::frodo_kem::frodo_unpack(8u32, 8u32, 15u32, c2.1, &mut c_matrix);
    let mut mu_decode: [u8; 16] = [0u8; 16usize];
    let s_bytes: (&[u8], &[u8]) = sk.split_at(992usize);
    let mut s_matrix: [u16; 512] = [0u16; 512usize];
    let mut m_matrix: [u16; 64] = [0u16; 64usize];
    crate::frodo_kem::matrix_from_lbytes(64u32, 8u32, s_bytes.1, &mut s_matrix);
    crate::frodo_kem::matrix_mul_s(8u32, 64u32, 8u32, &bp_matrix, &s_matrix, &mut m_matrix);
    crate::frodo_kem::matrix_sub(8u32, 8u32, &c_matrix, &mut m_matrix);
    crate::frodo_kem::frodo_key_decode(15u32, 2u32, 8u32, &m_matrix, &mut mu_decode);
    lib::memzero0::memzero::<u16>(&mut s_matrix, 512u32);
    lib::memzero0::memzero::<u16>(&mut m_matrix, 64u32);
    let mut seed_se_k: [u8; 32] = [0u8; 32usize];
    let pkh_mu_decode_len: u32 = 32u32;
    let mut pkh_mu_decode: Box<[u8]> = vec![0u8; pkh_mu_decode_len as usize].into_boxed_slice();
    let pkh: (&[u8], &[u8]) = (s_bytes.1).split_at(1024usize);
    ((&mut pkh_mu_decode)[0usize..16usize]).copy_from_slice(&pkh.1[0usize..16usize]);
    ((&mut pkh_mu_decode)[16usize..16usize + 16usize]).copy_from_slice(
        &(&mu_decode)[0usize..16usize]
    );
    crate::hash_sha3::shake128(&mut seed_se_k, 32u32, &pkh_mu_decode, pkh_mu_decode_len);
    let seed_se: (&[u8], &[u8]) = seed_se_k.split_at(0usize);
    let kp: (&[u8], &[u8]) = (seed_se.1).split_at(16usize);
    let s: (&[u8], &[u8]) = (s_bytes.0).split_at(0usize);
    let mut bpp_matrix: [u16; 512] = [0u16; 512usize];
    let mut cp_matrix: [u16; 64] = [0u16; 64usize];
    let mut sp_matrix: [u16; 512] = [0u16; 512usize];
    let mut ep_matrix: [u16; 512] = [0u16; 512usize];
    let mut epp_matrix: [u16; 64] = [0u16; 64usize];
    let mut r: [u8; 2176] = [0u8; 2176usize];
    let mut shake_input_seed_se: [u8; 17] = [0u8; 17usize];
    (&mut shake_input_seed_se)[0usize] = 0x96u8;
    ((&mut shake_input_seed_se)[1usize..1usize + 16usize]).copy_from_slice(&kp.0[0usize..16usize]);
    crate::hash_sha3::shake128(&mut r, 2176u32, &shake_input_seed_se, 17u32);
    lib::memzero0::memzero::<u8>(&mut shake_input_seed_se, 17u32);
    crate::frodo_kem::frodo_sample_matrix64(8u32, 64u32, &(&r)[0usize..], &mut sp_matrix);
    crate::frodo_kem::frodo_sample_matrix64(8u32, 64u32, &(&r)[1024usize..], &mut ep_matrix);
    crate::frodo_kem::frodo_sample_matrix64(8u32, 8u32, &(&r)[2048usize..], &mut epp_matrix);
    let pk: (&[u8], &[u8]) = (s.1).split_at(16usize);
    let seed_a: (&[u8], &[u8]) = (pk.1).split_at(0usize);
    let b: (&[u8], &[u8]) = (seed_a.1).split_at(16usize);
    let mut a_matrix: [u16; 4096] = [0u16; 4096usize];
    crate::frodo_kem::frodo_gen_matrix(
        crate::spec::frodo_gen_a::SHAKE128,
        64u32,
        b.0,
        &mut a_matrix
    );
    crate::frodo_kem::matrix_mul(8u32, 64u32, 64u32, &sp_matrix, &a_matrix, &mut bpp_matrix);
    crate::frodo_kem::matrix_add(8u32, 64u32, &mut bpp_matrix, &ep_matrix);
    let mut b_matrix: [u16; 512] = [0u16; 512usize];
    crate::frodo_kem::frodo_unpack(64u32, 8u32, 15u32, b.1, &mut b_matrix);
    crate::frodo_kem::matrix_mul(8u32, 64u32, 8u32, &sp_matrix, &b_matrix, &mut cp_matrix);
    crate::frodo_kem::matrix_add(8u32, 8u32, &mut cp_matrix, &epp_matrix);
    let mut mu_encode: [u16; 64] = [0u16; 64usize];
    crate::frodo_kem::frodo_key_encode(15u32, 2u32, 8u32, &mu_decode, &mut mu_encode);
    crate::frodo_kem::matrix_add(8u32, 8u32, &mut cp_matrix, &mu_encode);
    lib::memzero0::memzero::<u16>(&mut mu_encode, 64u32);
    crate::frodo_kem::mod_pow2(8u32, 64u32, 15u32, &mut bpp_matrix);
    crate::frodo_kem::mod_pow2(8u32, 8u32, 15u32, &mut cp_matrix);
    lib::memzero0::memzero::<u16>(&mut sp_matrix, 512u32);
    lib::memzero0::memzero::<u16>(&mut ep_matrix, 512u32);
    lib::memzero0::memzero::<u16>(&mut epp_matrix, 64u32);
    let b1: u16 = crate::frodo_kem::matrix_eq(8u32, 64u32, &bp_matrix, &bpp_matrix);
    let b2: u16 = crate::frodo_kem::matrix_eq(8u32, 8u32, &c_matrix, &cp_matrix);
    let mask: u16 = b1 & b2;
    let mask0: u16 = mask;
    let mut kp_s: [u8; 16] = [0u8; 16usize];
    krml::unroll_for!(
        16,
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
    let ss_init_len: u32 = 1096u32;
    let mut ss_init: Box<[u8]> = vec![0u8; ss_init_len as usize].into_boxed_slice();
    ((&mut ss_init)[0usize..1080usize]).copy_from_slice(&ct[0usize..1080usize]);
    ((&mut ss_init)[1080usize..1080usize + 16usize]).copy_from_slice(&(&kp_s)[0usize..16usize]);
    crate::hash_sha3::shake128(ss, 16u32, &ss_init, ss_init_len);
    lib::memzero0::memzero::<u8>(&mut ss_init, ss_init_len);
    lib::memzero0::memzero::<u8>(&mut kp_s, 16u32);
    lib::memzero0::memzero::<u8>(&mut seed_se_k, 32u32);
    lib::memzero0::memzero::<u8>(&mut mu_decode, 16u32);
    0u32
}
