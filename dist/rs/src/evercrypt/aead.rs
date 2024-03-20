#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub struct state_s { pub impl: crate::hacl::spec::impl, pub ek: Vec<u8> }

pub fn uu___is_Ek(a: crate::hacl::spec::alg, projectee: state_s) -> bool
{
    crate::lowstar::ignore::ignore::<crate::hacl::spec::alg>(a);
    crate::lowstar::ignore::ignore::<state_s>(projectee);
    true
}

pub fn alg_of_state(s: &mut [state_s]) -> crate::hacl::spec::alg
{
    let r#impl: crate::hacl::spec::impl = (s[0usize]).impl;
    match r#impl
    {
        crate::hacl::spec::impl::Hacl_CHACHA20 => crate::hacl::spec::alg::CHACHA20_POLY1305,
        crate::hacl::spec::impl::Vale_AES128 => crate::hacl::spec::alg::AES128_GCM,
        crate::hacl::spec::impl::Vale_AES256 => crate::hacl::spec::alg::AES256_GCM,
        _ => panic!("Precondition of the function most likely violated")
    }
}

fn create_in_chacha20_poly1305(dst: &mut [&mut [state_s]], k: &mut [u8]) ->
    crate::evercrypt::error::error_code
{
    let mut ek: Vec<u8> = vec![0u8; 32usize];
    let mut p: Vec<state_s> =
        {
            let mut tmp: Vec<state_s> = Vec::new();
            tmp.push(state_s { impl: crate::hacl::spec::impl::Hacl_CHACHA20, ek: ek });
            tmp
        };
    ((&mut ek)[0usize..32usize]).copy_from_slice(&k[0usize..32usize]);
    dst[0usize] = &mut p;
    crate::evercrypt::error::error_code::Success
}

fn create_in_aes128_gcm(dst: &mut [&mut [state_s]], k: &mut [u8]) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [&mut [state_s]]>(dst);
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_aesni: bool = crate::evercrypt::autoconfig2::has_aesni();
        let has_pclmulqdq: bool = crate::evercrypt::autoconfig2::has_pclmulqdq();
        let has_avx: bool = crate::evercrypt::autoconfig2::has_avx();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        let has_movbe: bool = crate::evercrypt::autoconfig2::has_movbe();
        if has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
        {
            let mut ek: Vec<u8> = vec![0u8; 480usize];
            let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aes::aes128_key_expansion(k, hkeys_b.0)
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aeshash::aes128_keyhash_init(hkeys_b.0, hkeys_b.1)
            );
            let mut p: Vec<state_s> =
                {
                    let mut tmp: Vec<state_s> = Vec::new();
                    tmp.push(state_s { impl: crate::hacl::spec::impl::Vale_AES128, ek: ek });
                    tmp
                };
            dst[0usize] = &mut p;
            crate::evercrypt::error::error_code::Success
        }
        else
        { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
    }
    else
    { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
}

fn create_in_aes256_gcm(dst: &mut [&mut [state_s]], k: &mut [u8]) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [&mut [state_s]]>(dst);
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_aesni: bool = crate::evercrypt::autoconfig2::has_aesni();
        let has_pclmulqdq: bool = crate::evercrypt::autoconfig2::has_pclmulqdq();
        let has_avx: bool = crate::evercrypt::autoconfig2::has_avx();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        let has_movbe: bool = crate::evercrypt::autoconfig2::has_movbe();
        if has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
        {
            let mut ek: Vec<u8> = vec![0u8; 544usize];
            let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aes::aes256_key_expansion(k, hkeys_b.0)
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aeshash::aes256_keyhash_init(hkeys_b.0, hkeys_b.1)
            );
            let mut p: Vec<state_s> =
                {
                    let mut tmp: Vec<state_s> = Vec::new();
                    tmp.push(state_s { impl: crate::hacl::spec::impl::Vale_AES256, ek: ek });
                    tmp
                };
            dst[0usize] = &mut p;
            crate::evercrypt::error::error_code::Success
        }
        else
        { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
    }
    else
    { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
}

pub fn create_in(a: crate::hacl::spec::alg, dst: &mut [&mut [state_s]], k: &mut [u8]) ->
    crate::evercrypt::error::error_code
{
    match a
    {
        crate::hacl::spec::alg::AES128_GCM => create_in_aes128_gcm(dst, k),
        crate::hacl::spec::alg::AES256_GCM => create_in_aes256_gcm(dst, k),
        crate::hacl::spec::alg::CHACHA20_POLY1305 => create_in_chacha20_poly1305(dst, k),
        _ => crate::evercrypt::error::error_code::UnsupportedAlgorithm
    }
}

fn encrypt_aes128_gcm(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [state_s]>(s);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(plain);
    crate::lowstar::ignore::ignore::<u32>(plain_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        if false
        { crate::evercrypt::error::error_code::InvalidKey }
        else
        if iv_len == 0u32
        { crate::evercrypt::error::error_code::InvalidIVLength }
        else
        {
            let ek: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek.split_at_mut(304usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let plain_len·: u32 =
                (plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let plain_b·: (&mut [u8], &mut [u8]) = plain.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &plain[plain_len· as usize..plain_len· as usize
                +
                (plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (plain_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            if len128x6.wrapping_div(16u64) >= 18u64
            {
                let len128_num: u64 =
                    (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                        len128x6
                    );
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) =
                    in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128x6·: u64 = len128x6.wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm128_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b.0,
                        &mut tmp_iv,
                        hkeys_b.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            }
            else
            {
                let len128x61: u32 = 0u32;
                let len128_num: u64 = (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) = in128x6_b.1.split_at_mut(len128x61 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x61 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                let len128x6·: u64 = 0u64;
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm128_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b.0,
                        &mut tmp_iv,
                        hkeys_b.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            };
            (cipher[(plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(plain_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            crate::evercrypt::error::error_code::Success
        }
    }
    else
    { panic!("statically unreachable") }
}

fn encrypt_aes256_gcm(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [state_s]>(s);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(plain);
    crate::lowstar::ignore::ignore::<u32>(plain_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        if false
        { crate::evercrypt::error::error_code::InvalidKey }
        else
        if iv_len == 0u32
        { crate::evercrypt::error::error_code::InvalidIVLength }
        else
        {
            let ek: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek.split_at_mut(368usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let plain_len·: u32 =
                (plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let plain_b·: (&mut [u8], &mut [u8]) = plain.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &plain[plain_len· as usize..plain_len· as usize
                +
                (plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (plain_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            if len128x6.wrapping_div(16u64) >= 18u64
            {
                let len128_num: u64 =
                    (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                        len128x6
                    );
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) =
                    in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128x6·: u64 = len128x6.wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm256_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b.0,
                        &mut tmp_iv,
                        hkeys_b.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            }
            else
            {
                let len128x61: u32 = 0u32;
                let len128_num: u64 = (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) = in128x6_b.1.split_at_mut(len128x61 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x61 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                let len128x6·: u64 = 0u64;
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm256_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b.0,
                        &mut tmp_iv,
                        hkeys_b.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            };
            (cipher[(plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(plain_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            crate::evercrypt::error::error_code::Success
        }
    }
    else
    { panic!("statically unreachable") }
}

pub fn encrypt(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    if false
    { crate::evercrypt::error::error_code::InvalidKey }
    else
    {
        let mut scrut: &mut state_s = &mut s[0usize];
        let i: crate::hacl::spec::impl = (*scrut).impl;
        let ek: &mut [u8] = &mut (*scrut).ek;
        match i
        {
            crate::hacl::spec::impl::Vale_AES128 =>
              encrypt_aes128_gcm(s, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag),
            crate::hacl::spec::impl::Vale_AES256 =>
              encrypt_aes256_gcm(s, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag),
            crate::hacl::spec::impl::Hacl_CHACHA20 =>
              if iv_len != 12u32
              { crate::evercrypt::error::error_code::InvalidIVLength }
              else
              {
                  crate::evercrypt::chacha20poly1305::aead_encrypt(
                      ek,
                      iv,
                      ad_len,
                      ad,
                      plain_len,
                      plain,
                      cipher,
                      tag
                  );
                  crate::evercrypt::error::error_code::Success
              },
            _ => panic!("Precondition of the function most likely violated")
        }
    }
}

pub fn encrypt_expand_aes128_gcm_no_check(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(plain);
    crate::lowstar::ignore::ignore::<u32>(plain_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let mut ek: [u8; 480] = [0u8; 480usize];
        let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
        let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aes::aes128_key_expansion(k, hkeys_b.0)
        );
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aeshash::aes128_keyhash_init(hkeys_b.0, hkeys_b.1)
        );
        let mut p: [state_s; 1] =
            [state_s { impl: crate::hacl::spec::impl::Vale_AES128, ek: Vec::from(ek) }; 1usize];
        let s: &mut [state_s] = &mut p;
        if false
        {
            crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                crate::evercrypt::error::error_code::InvalidKey
            )
        }
        else
        if iv_len == 0u32
        {
            crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                crate::evercrypt::error::error_code::InvalidIVLength
            )
        }
        else
        {
            let ek0: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(304usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(176usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b0.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let plain_len·: u32 =
                (plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let plain_b·: (&mut [u8], &mut [u8]) = plain.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &plain[plain_len· as usize..plain_len· as usize
                +
                (plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (plain_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            if len128x6.wrapping_div(16u64) >= 18u64
            {
                let len128_num: u64 =
                    (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                        len128x6
                    );
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) =
                    in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128x6·: u64 = len128x6.wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm128_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b0.0,
                        &mut tmp_iv,
                        hkeys_b0.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            }
            else
            {
                let len128x61: u32 = 0u32;
                let len128_num: u64 = (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) = in128x6_b.1.split_at_mut(len128x61 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x61 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                let len128x6·: u64 = 0u64;
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm128_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b0.0,
                        &mut tmp_iv,
                        hkeys_b0.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            };
            (cipher[(plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(plain_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                crate::evercrypt::error::error_code::Success
            )
        };
        crate::evercrypt::error::error_code::Success
    }
    else
    { panic!("EverCrypt was compiled on a system which doesn't support Vale") }
}

pub fn encrypt_expand_aes256_gcm_no_check(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(plain);
    crate::lowstar::ignore::ignore::<u32>(plain_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let mut ek: [u8; 544] = [0u8; 544usize];
        let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
        let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aes::aes256_key_expansion(k, hkeys_b.0)
        );
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aeshash::aes256_keyhash_init(hkeys_b.0, hkeys_b.1)
        );
        let mut p: [state_s; 1] =
            [state_s { impl: crate::hacl::spec::impl::Vale_AES256, ek: Vec::from(ek) }; 1usize];
        let s: &mut [state_s] = &mut p;
        if false
        {
            crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                crate::evercrypt::error::error_code::InvalidKey
            )
        }
        else
        if iv_len == 0u32
        {
            crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                crate::evercrypt::error::error_code::InvalidIVLength
            )
        }
        else
        {
            let ek0: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(368usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(240usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b0.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let plain_len·: u32 =
                (plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let plain_b·: (&mut [u8], &mut [u8]) = plain.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &plain[plain_len· as usize..plain_len· as usize
                +
                (plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (plain_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            if len128x6.wrapping_div(16u64) >= 18u64
            {
                let len128_num: u64 =
                    (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                        len128x6
                    );
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) =
                    in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128x6·: u64 = len128x6.wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm256_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b0.0,
                        &mut tmp_iv,
                        hkeys_b0.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            }
            else
            {
                let len128x61: u32 = 0u32;
                let len128_num: u64 = (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                let in128_b: (&mut [u8], &mut [u8]) = in128x6_b.1.split_at_mut(len128x61 as usize);
                let out128_b: (&mut [u8], &mut [u8]) =
                    out128x6_b.1.split_at_mut(len128x61 as usize);
                let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                let len128_num·: u64 = len128_num.wrapping_div(16u64);
                let len128x6·: u64 = 0u64;
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcmencryptopt::gcm256_encrypt_opt(
                        auth_b·.1,
                        ad_len as u64,
                        auth_num,
                        hkeys_b0.0,
                        &mut tmp_iv,
                        hkeys_b0.1,
                        scratch_b1.0,
                        in128_b.0,
                        out128_b.0,
                        len128x6·,
                        in128_b.1,
                        out128_b.1,
                        len128_num·,
                        abytes_b.0,
                        plain_len as u64,
                        scratch_b1.1,
                        tag
                    )
                )
            };
            (cipher[(plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(plain_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                crate::evercrypt::error::error_code::Success
            )
        };
        crate::evercrypt::error::error_code::Success
    }
    else
    { panic!("EverCrypt was compiled on a system which doesn't support Vale") }
}

pub fn encrypt_expand_aes128_gcm(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(plain);
    crate::lowstar::ignore::ignore::<u32>(plain_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_pclmulqdq: bool = crate::evercrypt::autoconfig2::has_pclmulqdq();
        let has_avx: bool = crate::evercrypt::autoconfig2::has_avx();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        let has_movbe: bool = crate::evercrypt::autoconfig2::has_movbe();
        let has_aesni: bool = crate::evercrypt::autoconfig2::has_aesni();
        if has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
        {
            let mut ek: [u8; 480] = [0u8; 480usize];
            let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aes::aes128_key_expansion(k, hkeys_b.0)
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aeshash::aes128_keyhash_init(hkeys_b.0, hkeys_b.1)
            );
            let mut p: [state_s; 1] =
                [state_s { impl: crate::hacl::spec::impl::Vale_AES128, ek: Vec::from(ek) }; 1usize];
            let s: &mut [state_s] = &mut p;
            if false
            {
                crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                    crate::evercrypt::error::error_code::InvalidKey
                )
            }
            else
            if iv_len == 0u32
            {
                crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                    crate::evercrypt::error::error_code::InvalidIVLength
                )
            }
            else
            {
                let ek0: &mut [u8] = &mut (s[0usize]).ek;
                let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(304usize);
                let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
                let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
                let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(176usize);
                let mut tmp_iv: [u8; 16] = [0u8; 16usize];
                let len: u32 = iv_len.wrapping_div(16u32);
                let bytes_len: u32 = len.wrapping_mul(16u32);
                let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
                ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                    &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
                );
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                        iv_b.1,
                        iv_len as u64,
                        len as u64,
                        &mut tmp_iv,
                        &mut tmp_iv,
                        hkeys_b0.1
                    )
                );
                let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
                let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
                let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
                let plain_len·: u32 =
                    (plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let auth_len·: u32 =
                    (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let plain_b·: (&mut [u8], &mut [u8]) = plain.split_at_mut(0usize);
                let out_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
                let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
                (abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &plain[plain_len· as usize..plain_len· as usize
                    +
                    (plain_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &ad[auth_len· as usize..auth_len· as usize
                    +
                    (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                let len128x6: u64 = (plain_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
                if len128x6.wrapping_div(16u64) >= 18u64
                {
                    let len128_num: u64 =
                        (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                            len128x6
                        );
                    let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128x6·: u64 = len128x6.wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    crate::lowstar::ignore::ignore::<u64>(
                        crate::vale::stdcalls_x64_gcmencryptopt::gcm128_encrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            plain_len as u64,
                            scratch_b1.1,
                            tag
                        )
                    )
                }
                else
                {
                    let len128x61: u32 = 0u32;
                    let len128_num: u64 =
                        (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                    let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x61 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x61 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let len128x6·: u64 = 0u64;
                    crate::lowstar::ignore::ignore::<u64>(
                        crate::vale::stdcalls_x64_gcmencryptopt::gcm128_encrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            plain_len as u64,
                            scratch_b1.1,
                            tag
                        )
                    )
                };
                (cipher[(plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(plain_len
                as
                u64
                as
                u32).wrapping_div(16u32).wrapping_mul(16u32)
                as
                usize
                +
                (plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                    crate::evercrypt::error::error_code::Success
                )
            };
            crate::evercrypt::error::error_code::Success
        }
        else
        { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
    }
    else
    { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
}

pub fn encrypt_expand_aes256_gcm(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(plain);
    crate::lowstar::ignore::ignore::<u32>(plain_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_pclmulqdq: bool = crate::evercrypt::autoconfig2::has_pclmulqdq();
        let has_avx: bool = crate::evercrypt::autoconfig2::has_avx();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        let has_movbe: bool = crate::evercrypt::autoconfig2::has_movbe();
        let has_aesni: bool = crate::evercrypt::autoconfig2::has_aesni();
        if has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
        {
            let mut ek: [u8; 544] = [0u8; 544usize];
            let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aes::aes256_key_expansion(k, hkeys_b.0)
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aeshash::aes256_keyhash_init(hkeys_b.0, hkeys_b.1)
            );
            let mut p: [state_s; 1] =
                [state_s { impl: crate::hacl::spec::impl::Vale_AES256, ek: Vec::from(ek) }; 1usize];
            let s: &mut [state_s] = &mut p;
            if false
            {
                crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                    crate::evercrypt::error::error_code::InvalidKey
                )
            }
            else
            if iv_len == 0u32
            {
                crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                    crate::evercrypt::error::error_code::InvalidIVLength
                )
            }
            else
            {
                let ek0: &mut [u8] = &mut (s[0usize]).ek;
                let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(368usize);
                let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
                let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
                let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(240usize);
                let mut tmp_iv: [u8; 16] = [0u8; 16usize];
                let len: u32 = iv_len.wrapping_div(16u32);
                let bytes_len: u32 = len.wrapping_mul(16u32);
                let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
                ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                    &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
                );
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                        iv_b.1,
                        iv_len as u64,
                        len as u64,
                        &mut tmp_iv,
                        &mut tmp_iv,
                        hkeys_b0.1
                    )
                );
                let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
                let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
                let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
                let plain_len·: u32 =
                    (plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let auth_len·: u32 =
                    (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let plain_b·: (&mut [u8], &mut [u8]) = plain.split_at_mut(0usize);
                let out_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
                let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
                (abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &plain[plain_len· as usize..plain_len· as usize
                    +
                    (plain_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &ad[auth_len· as usize..auth_len· as usize
                    +
                    (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                let len128x6: u64 = (plain_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
                if len128x6.wrapping_div(16u64) >= 18u64
                {
                    let len128_num: u64 =
                        (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                            len128x6
                        );
                    let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128x6·: u64 = len128x6.wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    crate::lowstar::ignore::ignore::<u64>(
                        crate::vale::stdcalls_x64_gcmencryptopt::gcm256_encrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            plain_len as u64,
                            scratch_b1.1,
                            tag
                        )
                    )
                }
                else
                {
                    let len128x61: u32 = 0u32;
                    let len128_num: u64 =
                        (plain_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                    let in128x6_b: (&mut [u8], &mut [u8]) = plain_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x61 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x61 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let len128x6·: u64 = 0u64;
                    crate::lowstar::ignore::ignore::<u64>(
                        crate::vale::stdcalls_x64_gcmencryptopt::gcm256_encrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            plain_len as u64,
                            scratch_b1.1,
                            tag
                        )
                    )
                };
                (cipher[(plain_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(plain_len
                as
                u64
                as
                u32).wrapping_div(16u32).wrapping_mul(16u32)
                as
                usize
                +
                (plain_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &abytes_b.0[0usize..(plain_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                crate::lowstar::ignore::ignore::<crate::evercrypt::error::error_code>(
                    crate::evercrypt::error::error_code::Success
                )
            };
            crate::evercrypt::error::error_code::Success
        }
        else
        { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
    }
    else
    { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
}

pub fn encrypt_expand_chacha20_poly1305(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    let mut ek: [u8; 32] = [0u8; 32usize];
    let mut p: [state_s; 1] =
        [state_s { impl: crate::hacl::spec::impl::Hacl_CHACHA20, ek: Vec::from(ek) }; 1usize];
    ((&mut ek)[0usize..32usize]).copy_from_slice(&k[0usize..32usize]);
    let s: &mut [state_s] = &mut p;
    let ek0: &mut [u8] = &mut (s[0usize]).ek;
    crate::evercrypt::chacha20poly1305::aead_encrypt(
        ek0,
        iv,
        ad_len,
        ad,
        plain_len,
        plain,
        cipher,
        tag
    );
    crate::evercrypt::error::error_code::Success
}

pub fn encrypt_expand(
    a: crate::hacl::spec::alg,
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    plain: &mut [u8],
    plain_len: u32,
    cipher: &mut [u8],
    tag: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    match a
    {
        crate::hacl::spec::alg::AES128_GCM =>
          encrypt_expand_aes128_gcm(k, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag),
        crate::hacl::spec::alg::AES256_GCM =>
          encrypt_expand_aes256_gcm(k, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag),
        crate::hacl::spec::alg::CHACHA20_POLY1305 =>
          encrypt_expand_chacha20_poly1305(k, iv, iv_len, ad, ad_len, plain, plain_len, cipher, tag),
        _ => panic!("Precondition of the function most likely violated")
    }
}

fn decrypt_aes128_gcm(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [state_s]>(s);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<u32>(cipher_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        if false
        { crate::evercrypt::error::error_code::InvalidKey }
        else
        if iv_len == 0u32
        { crate::evercrypt::error::error_code::InvalidIVLength }
        else
        {
            let ek: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek.split_at_mut(304usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let cipher_len·: u32 =
                (cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let cipher_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &cipher[cipher_len· as usize..cipher_len· as usize
                +
                (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (cipher_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            let c: u64 =
                if len128x6.wrapping_div(16u64) >= 6u64
                {
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                            len128x6
                        );
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128x6·: u64 = len128x6.wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm128_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b.0,
                            &mut tmp_iv,
                            hkeys_b.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                }
                else
                {
                    let len128x61: u32 = 0u32;
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x61 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x61 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let len128x6·: u64 = 0u64;
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm128_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b.0,
                            &mut tmp_iv,
                            hkeys_b.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                };
            (dst[(cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(cipher_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let r: u64 = c;
            if r == 0u64
            { crate::evercrypt::error::error_code::Success }
            else
            { crate::evercrypt::error::error_code::AuthenticationFailure }
        }
    }
    else
    { panic!("statically unreachable") }
}

fn decrypt_aes256_gcm(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [state_s]>(s);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<u32>(cipher_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        if false
        { crate::evercrypt::error::error_code::InvalidKey }
        else
        if iv_len == 0u32
        { crate::evercrypt::error::error_code::InvalidIVLength }
        else
        {
            let ek: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek.split_at_mut(368usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let cipher_len·: u32 =
                (cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let cipher_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &cipher[cipher_len· as usize..cipher_len· as usize
                +
                (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (cipher_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            let c: u64 =
                if len128x6.wrapping_div(16u64) >= 6u64
                {
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                            len128x6
                        );
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128x6·: u64 = len128x6.wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm256_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b.0,
                            &mut tmp_iv,
                            hkeys_b.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                }
                else
                {
                    let len128x61: u32 = 0u32;
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x61 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x61 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let len128x6·: u64 = 0u64;
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm256_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b.0,
                            &mut tmp_iv,
                            hkeys_b.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                };
            (dst[(cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(cipher_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let r: u64 = c;
            if r == 0u64
            { crate::evercrypt::error::error_code::Success }
            else
            { crate::evercrypt::error::error_code::AuthenticationFailure }
        }
    }
    else
    { panic!("statically unreachable") }
}

fn decrypt_chacha20_poly1305(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    if false
    { crate::evercrypt::error::error_code::InvalidKey }
    else
    if iv_len != 12u32
    { crate::evercrypt::error::error_code::InvalidIVLength }
    else
    {
        let ek: &mut [u8] = &mut (s[0usize]).ek;
        let r: u32 =
            crate::evercrypt::chacha20poly1305::aead_decrypt(
                ek,
                iv,
                ad_len,
                ad,
                cipher_len,
                dst,
                cipher,
                tag
            );
        if r == 0u32
        { crate::evercrypt::error::error_code::Success }
        else
        { crate::evercrypt::error::error_code::AuthenticationFailure }
    }
}

pub fn decrypt(
    s: &mut [state_s],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    if false
    { crate::evercrypt::error::error_code::InvalidKey }
    else
    {
        let i: crate::hacl::spec::impl = (s[0usize]).impl;
        match i
        {
            crate::hacl::spec::impl::Vale_AES128 =>
              decrypt_aes128_gcm(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst),
            crate::hacl::spec::impl::Vale_AES256 =>
              decrypt_aes256_gcm(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst),
            crate::hacl::spec::impl::Hacl_CHACHA20 =>
              decrypt_chacha20_poly1305(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst),
            _ => panic!("Precondition of the function most likely violated")
        }
    }
}

pub fn decrypt_expand_aes128_gcm_no_check(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<u32>(cipher_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let mut ek: [u8; 480] = [0u8; 480usize];
        let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
        let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aes::aes128_key_expansion(k, hkeys_b.0)
        );
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aeshash::aes128_keyhash_init(hkeys_b.0, hkeys_b.1)
        );
        let mut p: [state_s; 1] =
            [state_s { impl: crate::hacl::spec::impl::Vale_AES128, ek: Vec::from(ek) }; 1usize];
        let s: &mut [state_s] = &mut p;
        if false
        { crate::evercrypt::error::error_code::InvalidKey }
        else
        if iv_len == 0u32
        { crate::evercrypt::error::error_code::InvalidIVLength }
        else
        {
            let ek0: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(304usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(176usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b0.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let cipher_len·: u32 =
                (cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let cipher_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &cipher[cipher_len· as usize..cipher_len· as usize
                +
                (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (cipher_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            let c: u64 =
                if len128x6.wrapping_div(16u64) >= 6u64
                {
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                            len128x6
                        );
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128x6·: u64 = len128x6.wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm128_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                }
                else
                {
                    let len128x61: u32 = 0u32;
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x61 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x61 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let len128x6·: u64 = 0u64;
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm128_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                };
            (dst[(cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(cipher_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let r: u64 = c;
            if r == 0u64
            { crate::evercrypt::error::error_code::Success }
            else
            { crate::evercrypt::error::error_code::AuthenticationFailure }
        }
    }
    else
    { panic!("EverCrypt was compiled on a system which doesn't support Vale") }
}

pub fn decrypt_expand_aes256_gcm_no_check(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<u32>(cipher_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let mut ek: [u8; 544] = [0u8; 544usize];
        let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
        let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aes::aes256_key_expansion(k, hkeys_b.0)
        );
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_aeshash::aes256_keyhash_init(hkeys_b.0, hkeys_b.1)
        );
        let mut p: [state_s; 1] =
            [state_s { impl: crate::hacl::spec::impl::Vale_AES256, ek: Vec::from(ek) }; 1usize];
        let s: &mut [state_s] = &mut p;
        if false
        { crate::evercrypt::error::error_code::InvalidKey }
        else
        if iv_len == 0u32
        { crate::evercrypt::error::error_code::InvalidIVLength }
        else
        {
            let ek0: &mut [u8] = &mut (s[0usize]).ek;
            let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(368usize);
            let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
            let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
            let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(240usize);
            let mut tmp_iv: [u8; 16] = [0u8; 16usize];
            let len: u32 = iv_len.wrapping_div(16u32);
            let bytes_len: u32 = len.wrapping_mul(16u32);
            let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
            ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                    iv_b.1,
                    iv_len as u64,
                    len as u64,
                    &mut tmp_iv,
                    &mut tmp_iv,
                    hkeys_b0.1
                )
            );
            let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
            let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
            let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
            let cipher_len·: u32 =
                (cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let auth_len·: u32 = (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
            let cipher_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
            let out_b·: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
            let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
            (abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &cipher[cipher_len· as usize..cipher_len· as usize
                +
                (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &ad[auth_len· as usize..auth_len· as usize
                +
                (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let len128x6: u64 = (cipher_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
            let c: u64 =
                if len128x6.wrapping_div(16u64) >= 6u64
                {
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                            len128x6
                        );
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128x6·: u64 = len128x6.wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm256_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                }
                else
                {
                    let len128x61: u32 = 0u32;
                    let len128_num: u64 =
                        (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                    let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                    let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                    let in128_b: (&mut [u8], &mut [u8]) =
                        in128x6_b.1.split_at_mut(len128x61 as usize);
                    let out128_b: (&mut [u8], &mut [u8]) =
                        out128x6_b.1.split_at_mut(len128x61 as usize);
                    let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                    let len128_num·: u64 = len128_num.wrapping_div(16u64);
                    let len128x6·: u64 = 0u64;
                    let c: u64 =
                        crate::vale::stdcalls_x64_gcmdecryptopt::gcm256_decrypt_opt(
                            auth_b·.1,
                            ad_len as u64,
                            auth_num,
                            hkeys_b0.0,
                            &mut tmp_iv,
                            hkeys_b0.1,
                            scratch_b1.0,
                            in128_b.0,
                            out128_b.0,
                            len128x6·,
                            in128_b.1,
                            out128_b.1,
                            len128_num·,
                            abytes_b.0,
                            cipher_len as u64,
                            scratch_b1.1,
                            tag
                        );
                    c
                };
            (dst[(cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(cipher_len
            as
            u64
            as
            u32).wrapping_div(16u32).wrapping_mul(16u32)
            as
            usize
            +
            (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                &abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
            );
            let r: u64 = c;
            if r == 0u64
            { crate::evercrypt::error::error_code::Success }
            else
            { crate::evercrypt::error::error_code::AuthenticationFailure }
        }
    }
    else
    { panic!("EverCrypt was compiled on a system which doesn't support Vale") }
}

pub fn decrypt_expand_aes128_gcm(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<u32>(cipher_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_pclmulqdq: bool = crate::evercrypt::autoconfig2::has_pclmulqdq();
        let has_avx: bool = crate::evercrypt::autoconfig2::has_avx();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        let has_movbe: bool = crate::evercrypt::autoconfig2::has_movbe();
        let has_aesni: bool = crate::evercrypt::autoconfig2::has_aesni();
        if has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
        {
            let mut ek: [u8; 480] = [0u8; 480usize];
            let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(176usize);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aes::aes128_key_expansion(k, hkeys_b.0)
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aeshash::aes128_keyhash_init(hkeys_b.0, hkeys_b.1)
            );
            let mut p: [state_s; 1] =
                [state_s { impl: crate::hacl::spec::impl::Vale_AES128, ek: Vec::from(ek) }; 1usize];
            let s: &mut [state_s] = &mut p;
            if false
            { crate::evercrypt::error::error_code::InvalidKey }
            else
            if iv_len == 0u32
            { crate::evercrypt::error::error_code::InvalidIVLength }
            else
            {
                let ek0: &mut [u8] = &mut (s[0usize]).ek;
                let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(304usize);
                let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
                let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
                let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(176usize);
                let mut tmp_iv: [u8; 16] = [0u8; 16usize];
                let len: u32 = iv_len.wrapping_div(16u32);
                let bytes_len: u32 = len.wrapping_mul(16u32);
                let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
                ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                    &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
                );
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                        iv_b.1,
                        iv_len as u64,
                        len as u64,
                        &mut tmp_iv,
                        &mut tmp_iv,
                        hkeys_b0.1
                    )
                );
                let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
                let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
                let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
                let cipher_len·: u32 =
                    (cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let auth_len·: u32 =
                    (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let cipher_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
                let out_b·: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
                let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
                (abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &cipher[cipher_len· as usize..cipher_len· as usize
                    +
                    (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &ad[auth_len· as usize..auth_len· as usize
                    +
                    (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                let len128x6: u64 = (cipher_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
                let c: u64 =
                    if len128x6.wrapping_div(16u64) >= 6u64
                    {
                        let len128_num: u64 =
                            (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                                len128x6
                            );
                        let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                        let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                        let in128_b: (&mut [u8], &mut [u8]) =
                            in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                        let out128_b: (&mut [u8], &mut [u8]) =
                            out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                        let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                        let len128x6·: u64 = len128x6.wrapping_div(16u64);
                        let len128_num·: u64 = len128_num.wrapping_div(16u64);
                        let c: u64 =
                            crate::vale::stdcalls_x64_gcmdecryptopt::gcm128_decrypt_opt(
                                auth_b·.1,
                                ad_len as u64,
                                auth_num,
                                hkeys_b0.0,
                                &mut tmp_iv,
                                hkeys_b0.1,
                                scratch_b1.0,
                                in128_b.0,
                                out128_b.0,
                                len128x6·,
                                in128_b.1,
                                out128_b.1,
                                len128_num·,
                                abytes_b.0,
                                cipher_len as u64,
                                scratch_b1.1,
                                tag
                            );
                        c
                    }
                    else
                    {
                        let len128x61: u32 = 0u32;
                        let len128_num: u64 =
                            (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                        let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                        let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                        let in128_b: (&mut [u8], &mut [u8]) =
                            in128x6_b.1.split_at_mut(len128x61 as usize);
                        let out128_b: (&mut [u8], &mut [u8]) =
                            out128x6_b.1.split_at_mut(len128x61 as usize);
                        let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                        let len128_num·: u64 = len128_num.wrapping_div(16u64);
                        let len128x6·: u64 = 0u64;
                        let c: u64 =
                            crate::vale::stdcalls_x64_gcmdecryptopt::gcm128_decrypt_opt(
                                auth_b·.1,
                                ad_len as u64,
                                auth_num,
                                hkeys_b0.0,
                                &mut tmp_iv,
                                hkeys_b0.1,
                                scratch_b1.0,
                                in128_b.0,
                                out128_b.0,
                                len128x6·,
                                in128_b.1,
                                out128_b.1,
                                len128_num·,
                                abytes_b.0,
                                cipher_len as u64,
                                scratch_b1.1,
                                tag
                            );
                        c
                    };
                (dst[(cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(cipher_len
                as
                u64
                as
                u32).wrapping_div(16u32).wrapping_mul(16u32)
                as
                usize
                +
                (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                let r: u64 = c;
                if r == 0u64
                { crate::evercrypt::error::error_code::Success }
                else
                { crate::evercrypt::error::error_code::AuthenticationFailure }
            }
        }
        else
        { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
    }
    else
    { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
}

pub fn decrypt_expand_aes256_gcm(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    crate::lowstar::ignore::ignore::<&mut [u8]>(k);
    crate::lowstar::ignore::ignore::<&mut [u8]>(iv);
    crate::lowstar::ignore::ignore::<u32>(iv_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(ad);
    crate::lowstar::ignore::ignore::<u32>(ad_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(cipher);
    crate::lowstar::ignore::ignore::<u32>(cipher_len);
    crate::lowstar::ignore::ignore::<&mut [u8]>(tag);
    crate::lowstar::ignore::ignore::<&mut [u8]>(dst);
    if crate::evercrypt::targetconfig::hacl_can_compile_vale
    {
        let has_pclmulqdq: bool = crate::evercrypt::autoconfig2::has_pclmulqdq();
        let has_avx: bool = crate::evercrypt::autoconfig2::has_avx();
        let has_sse: bool = crate::evercrypt::autoconfig2::has_sse();
        let has_movbe: bool = crate::evercrypt::autoconfig2::has_movbe();
        let has_aesni: bool = crate::evercrypt::autoconfig2::has_aesni();
        if has_aesni && has_pclmulqdq && has_avx && has_sse && has_movbe
        {
            let mut ek: [u8; 544] = [0u8; 544usize];
            let keys_b: (&mut [u8], &mut [u8]) = (&mut ek).split_at_mut(0usize);
            let hkeys_b: (&mut [u8], &mut [u8]) = keys_b.1.split_at_mut(240usize);
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aes::aes256_key_expansion(k, hkeys_b.0)
            );
            crate::lowstar::ignore::ignore::<u64>(
                crate::vale::stdcalls_x64_aeshash::aes256_keyhash_init(hkeys_b.0, hkeys_b.1)
            );
            let mut p: [state_s; 1] =
                [state_s { impl: crate::hacl::spec::impl::Vale_AES256, ek: Vec::from(ek) }; 1usize];
            let s: &mut [state_s] = &mut p;
            if false
            { crate::evercrypt::error::error_code::InvalidKey }
            else
            if iv_len == 0u32
            { crate::evercrypt::error::error_code::InvalidIVLength }
            else
            {
                let ek0: &mut [u8] = &mut (s[0usize]).ek;
                let scratch_b: (&mut [u8], &mut [u8]) = ek0.split_at_mut(368usize);
                let ek1: (&mut [u8], &mut [u8]) = scratch_b.0.split_at_mut(0usize);
                let keys_b0: (&mut [u8], &mut [u8]) = ek1.1.split_at_mut(0usize);
                let hkeys_b0: (&mut [u8], &mut [u8]) = keys_b0.1.split_at_mut(240usize);
                let mut tmp_iv: [u8; 16] = [0u8; 16usize];
                let len: u32 = iv_len.wrapping_div(16u32);
                let bytes_len: u32 = len.wrapping_mul(16u32);
                let iv_b: (&mut [u8], &mut [u8]) = iv.split_at_mut(0usize);
                ((&mut tmp_iv)[0usize..iv_len.wrapping_rem(16u32) as usize]).copy_from_slice(
                    &iv[bytes_len as usize..bytes_len as usize + iv_len.wrapping_rem(16u32) as usize]
                );
                crate::lowstar::ignore::ignore::<u64>(
                    crate::vale::stdcalls_x64_gcm_iv::compute_iv_stdcall(
                        iv_b.1,
                        iv_len as u64,
                        len as u64,
                        &mut tmp_iv,
                        &mut tmp_iv,
                        hkeys_b0.1
                    )
                );
                let inout_b: (&mut [u8], &mut [u8]) = scratch_b.1.split_at_mut(0usize);
                let abytes_b: (&mut [u8], &mut [u8]) = inout_b.1.split_at_mut(16usize);
                let scratch_b1: (&mut [u8], &mut [u8]) = abytes_b.1.split_at_mut(16usize);
                let cipher_len·: u32 =
                    (cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let auth_len·: u32 =
                    (ad_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32);
                let cipher_b·: (&mut [u8], &mut [u8]) = cipher.split_at_mut(0usize);
                let out_b·: (&mut [u8], &mut [u8]) = dst.split_at_mut(0usize);
                let auth_b·: (&mut [u8], &mut [u8]) = ad.split_at_mut(0usize);
                (abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &cipher[cipher_len· as usize..cipher_len· as usize
                    +
                    (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                (scratch_b1.0[0usize..(ad_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &ad[auth_len· as usize..auth_len· as usize
                    +
                    (ad_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                let len128x6: u64 = (cipher_len as u64).wrapping_div(96u64).wrapping_mul(96u64);
                let c: u64 =
                    if len128x6.wrapping_div(16u64) >= 6u64
                    {
                        let len128_num: u64 =
                            (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64).wrapping_sub(
                                len128x6
                            );
                        let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                        let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                        let in128_b: (&mut [u8], &mut [u8]) =
                            in128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                        let out128_b: (&mut [u8], &mut [u8]) =
                            out128x6_b.1.split_at_mut(len128x6 as u32 as usize);
                        let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                        let len128x6·: u64 = len128x6.wrapping_div(16u64);
                        let len128_num·: u64 = len128_num.wrapping_div(16u64);
                        let c: u64 =
                            crate::vale::stdcalls_x64_gcmdecryptopt::gcm256_decrypt_opt(
                                auth_b·.1,
                                ad_len as u64,
                                auth_num,
                                hkeys_b0.0,
                                &mut tmp_iv,
                                hkeys_b0.1,
                                scratch_b1.0,
                                in128_b.0,
                                out128_b.0,
                                len128x6·,
                                in128_b.1,
                                out128_b.1,
                                len128_num·,
                                abytes_b.0,
                                cipher_len as u64,
                                scratch_b1.1,
                                tag
                            );
                        c
                    }
                    else
                    {
                        let len128x61: u32 = 0u32;
                        let len128_num: u64 =
                            (cipher_len as u64).wrapping_div(16u64).wrapping_mul(16u64);
                        let in128x6_b: (&mut [u8], &mut [u8]) = cipher_b·.1.split_at_mut(0usize);
                        let out128x6_b: (&mut [u8], &mut [u8]) = out_b·.1.split_at_mut(0usize);
                        let in128_b: (&mut [u8], &mut [u8]) =
                            in128x6_b.1.split_at_mut(len128x61 as usize);
                        let out128_b: (&mut [u8], &mut [u8]) =
                            out128x6_b.1.split_at_mut(len128x61 as usize);
                        let auth_num: u64 = (ad_len as u64).wrapping_div(16u64);
                        let len128_num·: u64 = len128_num.wrapping_div(16u64);
                        let len128x6·: u64 = 0u64;
                        let c: u64 =
                            crate::vale::stdcalls_x64_gcmdecryptopt::gcm256_decrypt_opt(
                                auth_b·.1,
                                ad_len as u64,
                                auth_num,
                                hkeys_b0.0,
                                &mut tmp_iv,
                                hkeys_b0.1,
                                scratch_b1.0,
                                in128_b.0,
                                out128_b.0,
                                len128x6·,
                                in128_b.1,
                                out128_b.1,
                                len128_num·,
                                abytes_b.0,
                                cipher_len as u64,
                                scratch_b1.1,
                                tag
                            );
                        c
                    };
                (dst[(cipher_len as u64 as u32).wrapping_div(16u32).wrapping_mul(16u32) as usize..(cipher_len
                as
                u64
                as
                u32).wrapping_div(16u32).wrapping_mul(16u32)
                as
                usize
                +
                (cipher_len as u64 as u32).wrapping_rem(16u32) as usize]).copy_from_slice(
                    &abytes_b.0[0usize..(cipher_len as u64 as u32).wrapping_rem(16u32) as usize]
                );
                let r: u64 = c;
                if r == 0u64
                { crate::evercrypt::error::error_code::Success }
                else
                { crate::evercrypt::error::error_code::AuthenticationFailure }
            }
        }
        else
        { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
    }
    else
    { crate::evercrypt::error::error_code::UnsupportedAlgorithm }
}

pub fn decrypt_expand_chacha20_poly1305(
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    let mut ek: [u8; 32] = [0u8; 32usize];
    let mut p: [state_s; 1] =
        [state_s { impl: crate::hacl::spec::impl::Hacl_CHACHA20, ek: Vec::from(ek) }; 1usize];
    ((&mut ek)[0usize..32usize]).copy_from_slice(&k[0usize..32usize]);
    let s: &mut [state_s] = &mut p;
    let r: crate::evercrypt::error::error_code =
        decrypt_chacha20_poly1305(s, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst);
    r
}

pub fn decrypt_expand(
    a: crate::hacl::spec::alg,
    k: &mut [u8],
    iv: &mut [u8],
    iv_len: u32,
    ad: &mut [u8],
    ad_len: u32,
    cipher: &mut [u8],
    cipher_len: u32,
    tag: &mut [u8],
    dst: &mut [u8]
) ->
    crate::evercrypt::error::error_code
{
    match a
    {
        crate::hacl::spec::alg::AES128_GCM =>
          decrypt_expand_aes128_gcm(k, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst),
        crate::hacl::spec::alg::AES256_GCM =>
          decrypt_expand_aes256_gcm(k, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst),
        crate::hacl::spec::alg::CHACHA20_POLY1305 =>
          decrypt_expand_chacha20_poly1305(k, iv, iv_len, ad, ad_len, cipher, cipher_len, tag, dst),
        _ => panic!("Precondition of the function most likely violated")
    }
}
