#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

fn expand_sha1(
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    let tlen: u32 = 20u32;
    let n: u32 = len.wrapping_div(tlen);
    let output: (&mut [u8], &mut [u8]) = okm.split_at_mut(0usize);
    let mut text: Vec<u8> = vec![0u8; tlen.wrapping_add(infolen).wrapping_add(1u32) as usize];
    let text0: (&mut [u8], &mut [u8]) = (&mut text).split_at_mut(tlen as usize);
    let tag: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(0usize - tlen as usize);
    let ctr: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(tlen.wrapping_add(infolen) as usize);
    ((&mut (&mut text)[tlen as usize..])[0usize..infolen as usize]).copy_from_slice(
        &info[0usize..infolen as usize]
    );
    for i in 0u32..n
    {
        ctr.1[0usize] = i.wrapping_add(1u32) as u8;
        if i == 0u32
        {
            crate::evercrypt::hmac::compute_sha1(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha1(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        ((&mut output.1[i.wrapping_mul(tlen) as usize..])[0usize..tlen as usize]).copy_from_slice(
            &ctr.0[0usize..tlen as usize]
        )
    };
    if n.wrapping_mul(tlen) < len
    {
        ctr.1[0usize] = n.wrapping_add(1u32) as u8;
        if n == 0u32
        {
            crate::evercrypt::hmac::compute_sha1(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha1(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        let block: (&mut [u8], &mut [u8]) = output.1.split_at_mut(n.wrapping_mul(tlen) as usize);
        (block.1[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]).copy_from_slice(
            &(&mut ctr.0[0usize..])[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]
        )
    }
}

fn extract_sha1(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha1(prk, salt, saltlen, ikm, ikmlen) }

fn expand_sha2_256(
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    let tlen: u32 = 32u32;
    let n: u32 = len.wrapping_div(tlen);
    let output: (&mut [u8], &mut [u8]) = okm.split_at_mut(0usize);
    let mut text: Vec<u8> = vec![0u8; tlen.wrapping_add(infolen).wrapping_add(1u32) as usize];
    let text0: (&mut [u8], &mut [u8]) = (&mut text).split_at_mut(tlen as usize);
    let tag: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(0usize - tlen as usize);
    let ctr: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(tlen.wrapping_add(infolen) as usize);
    ((&mut (&mut text)[tlen as usize..])[0usize..infolen as usize]).copy_from_slice(
        &info[0usize..infolen as usize]
    );
    for i in 0u32..n
    {
        ctr.1[0usize] = i.wrapping_add(1u32) as u8;
        if i == 0u32
        {
            crate::evercrypt::hmac::compute_sha2_256(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha2_256(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        ((&mut output.1[i.wrapping_mul(tlen) as usize..])[0usize..tlen as usize]).copy_from_slice(
            &ctr.0[0usize..tlen as usize]
        )
    };
    if n.wrapping_mul(tlen) < len
    {
        ctr.1[0usize] = n.wrapping_add(1u32) as u8;
        if n == 0u32
        {
            crate::evercrypt::hmac::compute_sha2_256(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha2_256(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        let block: (&mut [u8], &mut [u8]) = output.1.split_at_mut(n.wrapping_mul(tlen) as usize);
        (block.1[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]).copy_from_slice(
            &(&mut ctr.0[0usize..])[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]
        )
    }
}

fn extract_sha2_256(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha2_256(prk, salt, saltlen, ikm, ikmlen) }

fn expand_sha2_384(
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    let tlen: u32 = 48u32;
    let n: u32 = len.wrapping_div(tlen);
    let output: (&mut [u8], &mut [u8]) = okm.split_at_mut(0usize);
    let mut text: Vec<u8> = vec![0u8; tlen.wrapping_add(infolen).wrapping_add(1u32) as usize];
    let text0: (&mut [u8], &mut [u8]) = (&mut text).split_at_mut(tlen as usize);
    let tag: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(0usize - tlen as usize);
    let ctr: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(tlen.wrapping_add(infolen) as usize);
    ((&mut (&mut text)[tlen as usize..])[0usize..infolen as usize]).copy_from_slice(
        &info[0usize..infolen as usize]
    );
    for i in 0u32..n
    {
        ctr.1[0usize] = i.wrapping_add(1u32) as u8;
        if i == 0u32
        {
            crate::evercrypt::hmac::compute_sha2_384(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha2_384(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        ((&mut output.1[i.wrapping_mul(tlen) as usize..])[0usize..tlen as usize]).copy_from_slice(
            &ctr.0[0usize..tlen as usize]
        )
    };
    if n.wrapping_mul(tlen) < len
    {
        ctr.1[0usize] = n.wrapping_add(1u32) as u8;
        if n == 0u32
        {
            crate::evercrypt::hmac::compute_sha2_384(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha2_384(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        let block: (&mut [u8], &mut [u8]) = output.1.split_at_mut(n.wrapping_mul(tlen) as usize);
        (block.1[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]).copy_from_slice(
            &(&mut ctr.0[0usize..])[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]
        )
    }
}

fn extract_sha2_384(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha2_384(prk, salt, saltlen, ikm, ikmlen) }

fn expand_sha2_512(
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    let tlen: u32 = 64u32;
    let n: u32 = len.wrapping_div(tlen);
    let output: (&mut [u8], &mut [u8]) = okm.split_at_mut(0usize);
    let mut text: Vec<u8> = vec![0u8; tlen.wrapping_add(infolen).wrapping_add(1u32) as usize];
    let text0: (&mut [u8], &mut [u8]) = (&mut text).split_at_mut(tlen as usize);
    let tag: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(0usize - tlen as usize);
    let ctr: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(tlen.wrapping_add(infolen) as usize);
    ((&mut (&mut text)[tlen as usize..])[0usize..infolen as usize]).copy_from_slice(
        &info[0usize..infolen as usize]
    );
    for i in 0u32..n
    {
        ctr.1[0usize] = i.wrapping_add(1u32) as u8;
        if i == 0u32
        {
            crate::evercrypt::hmac::compute_sha2_512(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha2_512(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        ((&mut output.1[i.wrapping_mul(tlen) as usize..])[0usize..tlen as usize]).copy_from_slice(
            &ctr.0[0usize..tlen as usize]
        )
    };
    if n.wrapping_mul(tlen) < len
    {
        ctr.1[0usize] = n.wrapping_add(1u32) as u8;
        if n == 0u32
        {
            crate::evercrypt::hmac::compute_sha2_512(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_sha2_512(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        let block: (&mut [u8], &mut [u8]) = output.1.split_at_mut(n.wrapping_mul(tlen) as usize);
        (block.1[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]).copy_from_slice(
            &(&mut ctr.0[0usize..])[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]
        )
    }
}

fn extract_sha2_512(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_sha2_512(prk, salt, saltlen, ikm, ikmlen) }

fn expand_blake2s(
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    let tlen: u32 = 32u32;
    let n: u32 = len.wrapping_div(tlen);
    let output: (&mut [u8], &mut [u8]) = okm.split_at_mut(0usize);
    let mut text: Vec<u8> = vec![0u8; tlen.wrapping_add(infolen).wrapping_add(1u32) as usize];
    let text0: (&mut [u8], &mut [u8]) = (&mut text).split_at_mut(tlen as usize);
    let tag: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(0usize - tlen as usize);
    let ctr: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(tlen.wrapping_add(infolen) as usize);
    ((&mut (&mut text)[tlen as usize..])[0usize..infolen as usize]).copy_from_slice(
        &info[0usize..infolen as usize]
    );
    for i in 0u32..n
    {
        ctr.1[0usize] = i.wrapping_add(1u32) as u8;
        if i == 0u32
        {
            crate::evercrypt::hmac::compute_blake2s(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_blake2s(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        ((&mut output.1[i.wrapping_mul(tlen) as usize..])[0usize..tlen as usize]).copy_from_slice(
            &ctr.0[0usize..tlen as usize]
        )
    };
    if n.wrapping_mul(tlen) < len
    {
        ctr.1[0usize] = n.wrapping_add(1u32) as u8;
        if n == 0u32
        {
            crate::evercrypt::hmac::compute_blake2s(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_blake2s(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        let block: (&mut [u8], &mut [u8]) = output.1.split_at_mut(n.wrapping_mul(tlen) as usize);
        (block.1[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]).copy_from_slice(
            &(&mut ctr.0[0usize..])[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]
        )
    }
}

fn extract_blake2s(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_blake2s(prk, salt, saltlen, ikm, ikmlen) }

fn expand_blake2b(
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    let tlen: u32 = 64u32;
    let n: u32 = len.wrapping_div(tlen);
    let output: (&mut [u8], &mut [u8]) = okm.split_at_mut(0usize);
    let mut text: Vec<u8> = vec![0u8; tlen.wrapping_add(infolen).wrapping_add(1u32) as usize];
    let text0: (&mut [u8], &mut [u8]) = (&mut text).split_at_mut(tlen as usize);
    let tag: (&mut [u8], &mut [u8]) = text0.1.split_at_mut(0usize - tlen as usize);
    let ctr: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(tlen.wrapping_add(infolen) as usize);
    ((&mut (&mut text)[tlen as usize..])[0usize..infolen as usize]).copy_from_slice(
        &info[0usize..infolen as usize]
    );
    for i in 0u32..n
    {
        ctr.1[0usize] = i.wrapping_add(1u32) as u8;
        if i == 0u32
        {
            crate::evercrypt::hmac::compute_blake2b(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_blake2b(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        ((&mut output.1[i.wrapping_mul(tlen) as usize..])[0usize..tlen as usize]).copy_from_slice(
            &ctr.0[0usize..tlen as usize]
        )
    };
    if n.wrapping_mul(tlen) < len
    {
        ctr.1[0usize] = n.wrapping_add(1u32) as u8;
        if n == 0u32
        {
            crate::evercrypt::hmac::compute_blake2b(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::evercrypt::hmac::compute_blake2b(
                ctr.0,
                prk,
                prklen,
                &mut text,
                tlen.wrapping_add(infolen).wrapping_add(1u32)
            )
        };
        let block: (&mut [u8], &mut [u8]) = output.1.split_at_mut(n.wrapping_mul(tlen) as usize);
        (block.1[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]).copy_from_slice(
            &(&mut ctr.0[0usize..])[0usize..len.wrapping_sub(n.wrapping_mul(tlen)) as usize]
        )
    }
}

fn extract_blake2b(prk: &mut [u8], salt: &mut [u8], saltlen: u32, ikm: &mut [u8], ikmlen: u32) ->
    ()
{ crate::evercrypt::hmac::compute_blake2b(prk, salt, saltlen, ikm, ikmlen) }

pub fn expand(
    a: crate::hacl::streaming_types::hash_alg,
    okm: &mut [u8],
    prk: &mut [u8],
    prklen: u32,
    info: &mut [u8],
    infolen: u32,
    len: u32
) ->
    ()
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::SHA1 =>
          expand_sha1(okm, prk, prklen, info, infolen, len),
        crate::hacl::streaming_types::hash_alg::SHA2_256 =>
          expand_sha2_256(okm, prk, prklen, info, infolen, len),
        crate::hacl::streaming_types::hash_alg::SHA2_384 =>
          expand_sha2_384(okm, prk, prklen, info, infolen, len),
        crate::hacl::streaming_types::hash_alg::SHA2_512 =>
          expand_sha2_512(okm, prk, prklen, info, infolen, len),
        crate::hacl::streaming_types::hash_alg::Blake2S =>
          expand_blake2s(okm, prk, prklen, info, infolen, len),
        crate::hacl::streaming_types::hash_alg::Blake2B =>
          expand_blake2b(okm, prk, prklen, info, infolen, len),
        _ => panic!("Precondition of the function most likely violated")
    }
}

pub fn extract(
    a: crate::hacl::streaming_types::hash_alg,
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{
    match a
    {
        crate::hacl::streaming_types::hash_alg::SHA1 =>
          extract_sha1(prk, salt, saltlen, ikm, ikmlen),
        crate::hacl::streaming_types::hash_alg::SHA2_256 =>
          extract_sha2_256(prk, salt, saltlen, ikm, ikmlen),
        crate::hacl::streaming_types::hash_alg::SHA2_384 =>
          extract_sha2_384(prk, salt, saltlen, ikm, ikmlen),
        crate::hacl::streaming_types::hash_alg::SHA2_512 =>
          extract_sha2_512(prk, salt, saltlen, ikm, ikmlen),
        crate::hacl::streaming_types::hash_alg::Blake2S =>
          extract_blake2s(prk, salt, saltlen, ikm, ikmlen),
        crate::hacl::streaming_types::hash_alg::Blake2B =>
          extract_blake2b(prk, salt, saltlen, ikm, ikmlen),
        _ => panic!("Precondition of the function most likely violated")
    }
}
