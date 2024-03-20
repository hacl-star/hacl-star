#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

fn secretbox_init(xkeys: &mut [u8], k: &mut [u8], n: &mut [u8]) -> ()
{
    let subkey: (&mut [u8], &mut [u8]) = xkeys.split_at_mut(0usize);
    let aekey: (&mut [u8], &mut [u8]) = subkey.1.split_at_mut(32usize);
    let n0: (&mut [u8], &mut [u8]) = n.split_at_mut(0usize);
    let n1: (&mut [u8], &mut [u8]) = n0.1.split_at_mut(16usize);
    crate::hacl::salsa20::hsalsa200(aekey.0, k, n1.0);
    crate::hacl::salsa20::salsa20_key_block00(aekey.1, aekey.0, n1.1)
}

fn secretbox_detached(
    mlen: u32,
    c: &mut [u8],
    tag: &mut [u8],
    k: &mut [u8],
    n: &mut [u8],
    m: &mut [u8]
) ->
    ()
{
    let mut xkeys: [u8; 96] = [0u8; 96usize];
    secretbox_init(&mut xkeys, k, n);
    let mkey: (&mut [u8], &mut [u8]) = (&mut xkeys).split_at_mut(32usize);
    let n1: (&mut [u8], &mut [u8]) = n.split_at_mut(16usize);
    let subkey: (&mut [u8], &mut [u8]) = mkey.0.split_at_mut(0usize);
    let ekey0: (&mut [u8], &mut [u8]) = mkey.1.split_at_mut(32usize);
    let mlen0: u32 = if mlen <= 32u32 { mlen } else { 32u32 };
    let mlen1: u32 = mlen.wrapping_sub(mlen0);
    let m0: (&mut [u8], &mut [u8]) = m.split_at_mut(0usize);
    let m1: (&mut [u8], &mut [u8]) = m0.1.split_at_mut(mlen0 as usize);
    let mut block0: [u8; 32] = [0u8; 32usize];
    ((&mut block0)[0usize..mlen0 as usize]).copy_from_slice(&m1.0[0usize..mlen0 as usize]);
    for i in 0u32..32u32
    {
        let x: u8 = (&mut block0)[i as usize] ^ ekey0.1[i as usize];
        let os: (&mut [u8], &mut [u8]) = (&mut block0).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let c0: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let c1: (&mut [u8], &mut [u8]) = c0.1.split_at_mut(mlen0 as usize);
    (c1.0[0usize..mlen0 as usize]).copy_from_slice(
        &(&mut (&mut block0)[0usize..])[0usize..mlen0 as usize]
    );
    crate::hacl::salsa20::salsa20_encrypt0(mlen1, c1.1, m1.1, subkey.1, n1.1, 1u32);
    crate::hacl::mac_poly1305::mac(tag, c, mlen, ekey0.0)
}

fn secretbox_open_detached(
    mlen: u32,
    m: &mut [u8],
    k: &mut [u8],
    n: &mut [u8],
    c: &mut [u8],
    tag: &mut [u8]
) ->
    u32
{
    let mut xkeys: [u8; 96] = [0u8; 96usize];
    secretbox_init(&mut xkeys, k, n);
    let mkey: (&mut [u8], &mut [u8]) = (&mut xkeys).split_at_mut(32usize);
    let mut tag·: [u8; 16] = [0u8; 16usize];
    crate::hacl::mac_poly1305::mac(&mut tag·, c, mlen, mkey.1);
    let mut res: [u8; 1] = [255u8; 1usize];
    for i in 0u32..16u32
    {
        let uu____0: u8 = crate::fstar::uint8::eq_mask(tag[i as usize], (&mut tag·)[i as usize]);
        (&mut res)[0usize] = uu____0 & (&mut res)[0usize]
    };
    let z: u8 = (&mut res)[0usize];
    if z == 255u8
    {
        let subkey: (&mut [u8], &mut [u8]) = mkey.0.split_at_mut(0usize);
        let ekey0: (&mut [u8], &mut [u8]) = mkey.1.split_at_mut(32usize);
        let n1: (&mut [u8], &mut [u8]) = n.split_at_mut(16usize);
        let mlen0: u32 = if mlen <= 32u32 { mlen } else { 32u32 };
        let mlen1: u32 = mlen.wrapping_sub(mlen0);
        let c0: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
        let c1: (&mut [u8], &mut [u8]) = c0.1.split_at_mut(mlen0 as usize);
        let mut block0: [u8; 32] = [0u8; 32usize];
        ((&mut block0)[0usize..mlen0 as usize]).copy_from_slice(&c1.0[0usize..mlen0 as usize]);
        for i in 0u32..32u32
        {
            let x: u8 = (&mut block0)[i as usize] ^ ekey0.1[i as usize];
            let os: (&mut [u8], &mut [u8]) = (&mut block0).split_at_mut(0usize);
            os.1[i as usize] = x
        };
        let m0: (&mut [u8], &mut [u8]) = m.split_at_mut(0usize);
        let m1: (&mut [u8], &mut [u8]) = m0.1.split_at_mut(mlen0 as usize);
        (m1.0[0usize..mlen0 as usize]).copy_from_slice(
            &(&mut (&mut block0)[0usize..])[0usize..mlen0 as usize]
        );
        crate::hacl::salsa20::salsa20_decrypt0(mlen1, m1.1, c1.1, subkey.1, n1.1, 1u32);
        0u32
    }
    else
    { 0xffffffffu32 }
}

fn secretbox_easy(mlen: u32, c: &mut [u8], k: &mut [u8], n: &mut [u8], m: &mut [u8]) -> ()
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    secretbox_detached(mlen, cip.1, cip.0, k, n, m)
}

fn secretbox_open_easy(mlen: u32, m: &mut [u8], k: &mut [u8], n: &mut [u8], c: &mut [u8]) ->
    u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    secretbox_open_detached(mlen, m, k, n, cip.1, cip.0)
}

#[inline] fn box_beforenm(k: &mut [u8], pk: &mut [u8], sk: &mut [u8]) -> u32
{
    let mut n0: [u8; 16] = [0u8; 16usize];
    let r: bool = crate::hacl::curve25519_51::ecdh(k, sk, pk);
    if r
    {
        crate::hacl::salsa20::hsalsa200(k, k, &mut n0);
        0u32
    }
    else
    { 0xffffffffu32 }
}

#[inline] fn box_detached_afternm(
    mlen: u32,
    c: &mut [u8],
    tag: &mut [u8],
    k: &mut [u8],
    n: &mut [u8],
    m: &mut [u8]
) ->
    u32
{
    secretbox_detached(mlen, c, tag, k, n, m);
    0u32
}

#[inline] fn box_detached(
    mlen: u32,
    c: &mut [u8],
    tag: &mut [u8],
    sk: &mut [u8],
    pk: &mut [u8],
    n: &mut [u8],
    m: &mut [u8]
) ->
    u32
{
    let mut k: [u8; 32] = [0u8; 32usize];
    let r: u32 = box_beforenm(&mut k, pk, sk);
    if r == 0u32 { box_detached_afternm(mlen, c, tag, &mut k, n, m) } else { 0xffffffffu32 }
}

#[inline] fn box_open_detached_afternm(
    mlen: u32,
    m: &mut [u8],
    k: &mut [u8],
    n: &mut [u8],
    c: &mut [u8],
    tag: &mut [u8]
) ->
    u32
{ secretbox_open_detached(mlen, m, k, n, c, tag) }

#[inline] fn box_open_detached(
    mlen: u32,
    m: &mut [u8],
    pk: &mut [u8],
    sk: &mut [u8],
    n: &mut [u8],
    c: &mut [u8],
    tag: &mut [u8]
) ->
    u32
{
    let mut k: [u8; 32] = [0u8; 32usize];
    let r: u32 = box_beforenm(&mut k, pk, sk);
    if r == 0u32 { box_open_detached_afternm(mlen, m, &mut k, n, c, tag) } else { 0xffffffffu32 }
}

#[inline] fn box_easy_afternm(
    mlen: u32,
    c: &mut [u8],
    k: &mut [u8],
    n: &mut [u8],
    m: &mut [u8]
) ->
    u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    let res: u32 = box_detached_afternm(mlen, cip.1, cip.0, k, n, m);
    res
}

#[inline] fn box_easy(
    mlen: u32,
    c: &mut [u8],
    sk: &mut [u8],
    pk: &mut [u8],
    n: &mut [u8],
    m: &mut [u8]
) ->
    u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    let res: u32 = box_detached(mlen, cip.1, cip.0, sk, pk, n, m);
    res
}

#[inline] fn box_open_easy_afternm(
    mlen: u32,
    m: &mut [u8],
    k: &mut [u8],
    n: &mut [u8],
    c: &mut [u8]
) ->
    u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    box_open_detached_afternm(mlen, m, k, n, cip.1, cip.0)
}

#[inline] fn box_open_easy(
    mlen: u32,
    m: &mut [u8],
    pk: &mut [u8],
    sk: &mut [u8],
    n: &mut [u8],
    c: &mut [u8]
) ->
    u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    box_open_detached(mlen, m, pk, sk, n, cip.1, cip.0)
}

pub fn crypto_secretbox_detached(
    c: &mut [u8],
    tag: &mut [u8],
    m: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{
    secretbox_detached(mlen, c, tag, k, n, m);
    0u32
}

pub fn crypto_secretbox_open_detached(
    m: &mut [u8],
    c: &mut [u8],
    tag: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{ secretbox_open_detached(mlen, m, k, n, c, tag) }

pub fn crypto_secretbox_easy(c: &mut [u8], m: &mut [u8], mlen: u32, n: &mut [u8], k: &mut [u8]) ->
    u32
{
    secretbox_easy(mlen, c, k, n, m);
    0u32
}

pub fn crypto_secretbox_open_easy(
    m: &mut [u8],
    c: &mut [u8],
    clen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{ secretbox_open_easy(clen.wrapping_sub(16u32), m, k, n, c) }

pub fn crypto_box_beforenm(k: &mut [u8], pk: &mut [u8], sk: &mut [u8]) -> u32
{ box_beforenm(k, pk, sk) }

pub fn crypto_box_detached_afternm(
    c: &mut [u8],
    tag: &mut [u8],
    m: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{ box_detached_afternm(mlen, c, tag, k, n, m) }

pub fn crypto_box_detached(
    c: &mut [u8],
    tag: &mut [u8],
    m: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    pk: &mut [u8],
    sk: &mut [u8]
) ->
    u32
{ box_detached(mlen, c, tag, sk, pk, n, m) }

pub fn crypto_box_open_detached_afternm(
    m: &mut [u8],
    c: &mut [u8],
    tag: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{ box_open_detached_afternm(mlen, m, k, n, c, tag) }

pub fn crypto_box_open_detached(
    m: &mut [u8],
    c: &mut [u8],
    tag: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    pk: &mut [u8],
    sk: &mut [u8]
) ->
    u32
{ box_open_detached(mlen, m, pk, sk, n, c, tag) }

pub fn crypto_box_easy_afternm(
    c: &mut [u8],
    m: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{ box_easy_afternm(mlen, c, k, n, m) }

pub fn crypto_box_easy(
    c: &mut [u8],
    m: &mut [u8],
    mlen: u32,
    n: &mut [u8],
    pk: &mut [u8],
    sk: &mut [u8]
) ->
    u32
{ box_easy(mlen, c, sk, pk, n, m) }

pub fn crypto_box_open_easy_afternm(
    m: &mut [u8],
    c: &mut [u8],
    clen: u32,
    n: &mut [u8],
    k: &mut [u8]
) ->
    u32
{ box_open_easy_afternm(clen.wrapping_sub(16u32), m, k, n, c) }

pub fn crypto_box_open_easy(
    m: &mut [u8],
    c: &mut [u8],
    clen: u32,
    n: &mut [u8],
    pk: &mut [u8],
    sk: &mut [u8]
) ->
    u32
{ box_open_easy(clen.wrapping_sub(16u32), m, pk, sk, n, c) }
