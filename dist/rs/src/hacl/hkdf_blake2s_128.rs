#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub fn expand_blake2s_128(
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
            crate::hacl::hmac_blake2s_128::compute_blake2s_128(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::hacl::hmac_blake2s_128::compute_blake2s_128(
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
            crate::hacl::hmac_blake2s_128::compute_blake2s_128(
                ctr.0,
                prk,
                prklen,
                tag.0,
                infolen.wrapping_add(1u32)
            )
        }
        else
        {
            crate::hacl::hmac_blake2s_128::compute_blake2s_128(
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

pub fn extract_blake2s_128(
    prk: &mut [u8],
    salt: &mut [u8],
    saltlen: u32,
    ikm: &mut [u8],
    ikmlen: u32
) ->
    ()
{ crate::hacl::hmac_blake2s_128::compute_blake2s_128(prk, salt, saltlen, ikm, ikmlen) }
