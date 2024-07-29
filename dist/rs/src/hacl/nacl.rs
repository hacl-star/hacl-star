#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

fn secretbox_init(xkeys: &mut [u8], k: &[u8], n: &[u8])
{
    let subkey: (&mut [u8], &mut [u8]) = xkeys.split_at_mut(0usize);
    let aekey: (&mut [u8], &mut [u8]) = subkey.1.split_at_mut(32usize);
    let n0: (&[u8], &[u8]) = n.split_at(0usize);
    let n1: (&[u8], &[u8]) = n0.1.split_at(16usize);
    crate::hacl::salsa20::hsalsa200(aekey.0, k, n1.0);
    crate::hacl::salsa20::salsa20_key_block00(aekey.1, aekey.0, n1.1)
}

fn secretbox_detached(mlen: u32, c: &mut [u8], tag: &mut [u8], k: &[u8], n: &[u8], m: &[u8])
{
    let mut xkeys: [u8; 96] = [0u8; 96usize];
    secretbox_init(&mut xkeys, k, n);
    let mkey: (&[u8], &[u8]) = (&xkeys).split_at(32usize);
    let n1: (&[u8], &[u8]) = n.split_at(16usize);
    let subkey: (&[u8], &[u8]) = mkey.0.split_at(0usize);
    let ekey0: (&[u8], &[u8]) = mkey.1.split_at(32usize);
    let mlen0: u32 = if mlen <= 32u32 { mlen } else { 32u32 };
    let mlen1: u32 = mlen.wrapping_sub(mlen0);
    let m0: (&[u8], &[u8]) = m.split_at(0usize);
    let m1: (&[u8], &[u8]) = m0.1.split_at(mlen0 as usize);
    let mut block0: [u8; 32] = [0u8; 32usize];
    ((&mut block0)[0usize..mlen0 as usize]).copy_from_slice(&m1.0[0usize..mlen0 as usize]);
    krml::unroll_for!(
        32,
        "i",
        0u32,
        1u32,
        {
            let x: u8 = (&block0)[i as usize] ^ ekey0.1[i as usize];
            let os: (&mut [u8], &mut [u8]) = (&mut block0).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let c0: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let c1: (&mut [u8], &mut [u8]) = c0.1.split_at_mut(mlen0 as usize);
    (c1.0[0usize..mlen0 as usize]).copy_from_slice(&(&(&block0)[0usize..])[0usize..mlen0 as usize]);
    crate::hacl::salsa20::salsa20_encrypt0(mlen1, c1.1, m1.1, subkey.1, n1.1, 1u32);
    crate::hacl::mac_poly1305::mac(tag, c, mlen, ekey0.0)
}

fn secretbox_open_detached(mlen: u32, m: &mut [u8], k: &[u8], n: &[u8], c: &[u8], tag: &[u8]) ->
    u32
{
    let mut xkeys: [u8; 96] = [0u8; 96usize];
    secretbox_init(&mut xkeys, k, n);
    let mkey: (&[u8], &[u8]) = (&xkeys).split_at(32usize);
    let mut tag·: [u8; 16] = [0u8; 16usize];
    crate::hacl::mac_poly1305::mac(&mut tag·, c, mlen, mkey.1);
    let mut res: [u8; 1] = [255u8; 1usize];
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            let uu____0: u8 = crate::fstar::uint8::eq_mask(tag[i as usize], (&tag·)[i as usize]);
            (&mut res)[0usize] = uu____0 & (&res)[0usize]
        }
    );
    let z: u8 = (&res)[0usize];
    if z == 255u8
    {
        let subkey: (&[u8], &[u8]) = mkey.0.split_at(0usize);
        let ekey0: (&[u8], &[u8]) = mkey.1.split_at(32usize);
        let n1: (&[u8], &[u8]) = n.split_at(16usize);
        let mlen0: u32 = if mlen <= 32u32 { mlen } else { 32u32 };
        let mlen1: u32 = mlen.wrapping_sub(mlen0);
        let c0: (&[u8], &[u8]) = c.split_at(0usize);
        let c1: (&[u8], &[u8]) = c0.1.split_at(mlen0 as usize);
        let mut block0: [u8; 32] = [0u8; 32usize];
        ((&mut block0)[0usize..mlen0 as usize]).copy_from_slice(&c1.0[0usize..mlen0 as usize]);
        krml::unroll_for!(
            32,
            "i",
            0u32,
            1u32,
            {
                let x: u8 = (&block0)[i as usize] ^ ekey0.1[i as usize];
                let os: (&mut [u8], &mut [u8]) = (&mut block0).split_at_mut(0usize);
                os.1[i as usize] = x
            }
        );
        let m0: (&mut [u8], &mut [u8]) = m.split_at_mut(0usize);
        let m1: (&mut [u8], &mut [u8]) = m0.1.split_at_mut(mlen0 as usize);
        (m1.0[0usize..mlen0 as usize]).copy_from_slice(
            &(&(&block0)[0usize..])[0usize..mlen0 as usize]
        );
        crate::hacl::salsa20::salsa20_decrypt0(mlen1, m1.1, c1.1, subkey.1, n1.1, 1u32);
        0u32
    }
    else
    { 0xffffffffu32 }
}

fn secretbox_easy(mlen: u32, c: &mut [u8], k: &[u8], n: &[u8], m: &[u8])
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    secretbox_detached(mlen, cip.1, cip.0, k, n, m)
}

fn secretbox_open_easy(mlen: u32, m: &mut [u8], k: &[u8], n: &[u8], c: &[u8]) -> u32
{
    let tag: (&[u8], &[u8]) = c.split_at(0usize);
    let cip: (&[u8], &[u8]) = tag.1.split_at(16usize);
    secretbox_open_detached(mlen, m, k, n, cip.1, cip.0)
}

#[inline] fn box_beforenm(k: &mut [u8], pk: &[u8], sk: &[u8]) -> u32
{
    let n0: [u8; 16] = [0u8; 16usize];
    let r: bool = crate::hacl::curve25519_51::ecdh(k, sk, pk);
    if r
    {
        crate::hacl::salsa20::hsalsa200(k, k, &n0);
        0u32
    }
    else
    { 0xffffffffu32 }
}

#[inline] fn box_detached_afternm(
    mlen: u32,
    c: &mut [u8],
    tag: &mut [u8],
    k: &[u8],
    n: &[u8],
    m: &[u8]
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
    sk: &[u8],
    pk: &[u8],
    n: &[u8],
    m: &[u8]
) ->
    u32
{
    let mut k: [u8; 32] = [0u8; 32usize];
    let r: u32 = box_beforenm(&mut k, pk, sk);
    if r == 0u32 { box_detached_afternm(mlen, c, tag, &k, n, m) } else { 0xffffffffu32 }
}

#[inline] fn box_open_detached_afternm(
    mlen: u32,
    m: &mut [u8],
    k: &[u8],
    n: &[u8],
    c: &[u8],
    tag: &[u8]
) ->
    u32
{ secretbox_open_detached(mlen, m, k, n, c, tag) }

#[inline] fn box_open_detached(
    mlen: u32,
    m: &mut [u8],
    pk: &[u8],
    sk: &[u8],
    n: &[u8],
    c: &[u8],
    tag: &[u8]
) ->
    u32
{
    let mut k: [u8; 32] = [0u8; 32usize];
    let r: u32 = box_beforenm(&mut k, pk, sk);
    if r == 0u32 { box_open_detached_afternm(mlen, m, &k, n, c, tag) } else { 0xffffffffu32 }
}

#[inline] fn box_easy_afternm(mlen: u32, c: &mut [u8], k: &[u8], n: &[u8], m: &[u8]) -> u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    let res: u32 = box_detached_afternm(mlen, cip.1, cip.0, k, n, m);
    res
}

#[inline] fn box_easy(mlen: u32, c: &mut [u8], sk: &[u8], pk: &[u8], n: &[u8], m: &[u8]) -> u32
{
    let tag: (&mut [u8], &mut [u8]) = c.split_at_mut(0usize);
    let cip: (&mut [u8], &mut [u8]) = tag.1.split_at_mut(16usize);
    let res: u32 = box_detached(mlen, cip.1, cip.0, sk, pk, n, m);
    res
}

#[inline] fn box_open_easy_afternm(mlen: u32, m: &mut [u8], k: &[u8], n: &[u8], c: &[u8]) ->
    u32
{
    let tag: (&[u8], &[u8]) = c.split_at(0usize);
    let cip: (&[u8], &[u8]) = tag.1.split_at(16usize);
    box_open_detached_afternm(mlen, m, k, n, cip.1, cip.0)
}

#[inline] fn box_open_easy(mlen: u32, m: &mut [u8], pk: &[u8], sk: &[u8], n: &[u8], c: &[u8]) ->
    u32
{
    let tag: (&[u8], &[u8]) = c.split_at(0usize);
    let cip: (&[u8], &[u8]) = tag.1.split_at(16usize);
    box_open_detached(mlen, m, pk, sk, n, cip.1, cip.0)
}

/**
Encrypt a message with a key and nonce.

Note: `c` and `m` can point to the same memory for in-place encryption.

@param c Pointer to `mlen` bytes where the ciphertext is written to.
@param tag Pointer to 16 (tag length) bytes where the authentication tag is written to.
@param m Pointer to `mlen` bytes where the message is read from.
@param mlen Length of message.
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
pub fn
crypto_secretbox_detached(
    c: &mut [u8],
    tag: &mut [u8],
    m: &[u8],
    mlen: u32,
    n: &[u8],
    k: &[u8]
) ->
    u32
{
    secretbox_detached(mlen, c, tag, k, n, m);
    0u32
}

/**
Verify and decrypt a ciphertext produced with `Hacl_NaCl_crypto_secretbox_detached`.

Note: `m` and `c` can point to the same memory for in-place decryption.

@param m Pointer to `mlen` bytes where the message is written to.
@param c Pointer to `mlen` bytes where the ciphertext is read from.
@param tag Pointer to 16 (tag length) bytes where the authentication tag is read from.
@param mlen Length of message (and ciphertext).
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
pub fn
crypto_secretbox_open_detached(
    m: &mut [u8],
    c: &[u8],
    tag: &[u8],
    mlen: u32,
    n: &[u8],
    k: &[u8]
) ->
    u32
{ secretbox_open_detached(mlen, m, k, n, c, tag) }

/**
Encrypt a message with a key and nonce.

@param c Pointer to 16 (tag length) + `mlen` bytes where the ciphertext is written to.
@param m Pointer to `mlen` bytes where the message is read from.
@param mlen Length of message.
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
pub fn
crypto_secretbox_easy(c: &mut [u8], m: &[u8], mlen: u32, n: &[u8], k: &[u8]) ->
    u32
{
    secretbox_easy(mlen, c, k, n, m);
    0u32
}

/**
Verify and decrypt a ciphertext produced with `crypto_secretbox_easy`.

@param m Pointer to `mlen` bytes where the message is written to.
@param c Pointer to `clen` bytes where the ciphertext is read from. The authentication tag must be included.
@param clen Length of ciphertext.
@param n Pointer to 24 (`crypto_secretbox_NONCEBYTES`) bytes where the nonce is read from.
@param k Pointer to 32 (`crypto_secretbox_KEYBYTES`) bytes where the key is read from.
*/
pub fn
crypto_secretbox_open_easy(m: &mut [u8], c: &[u8], clen: u32, n: &[u8], k: &[u8]) ->
    u32
{ secretbox_open_easy(clen.wrapping_sub(16u32), m, k, n, c) }

/**
Compute a shared secret key given a public key and secret key.

@param k Pointer to 32 (`crypto_box_BEFORENMBYTES`) bytes of memory where the shared secret is written to.
@param pk Pointer to 32 bytes of memory where **their** public key is read from.
@param sk Pointer to 32 bytes of memory where **my** secret key is read from.
*/
pub fn
crypto_box_beforenm(k: &mut [u8], pk: &[u8], sk: &[u8]) ->
    u32
{ box_beforenm(k, pk, sk) }

/**
See `crypto_box_detached`.
*/
pub fn
crypto_box_detached_afternm(
    c: &mut [u8],
    tag: &mut [u8],
    m: &[u8],
    mlen: u32,
    n: &[u8],
    k: &[u8]
) ->
    u32
{ box_detached_afternm(mlen, c, tag, k, n, m) }

/**
Encrypt a message using the recipient's public key, the sender's secret key, and a nonce.

@param c Pointer to `mlen` bytes of memory where the ciphertext is written to.
@param tag Pointer to 16 (tag length) bytes of memory where the authentication tag is written to.
@param m Pointer to `mlen` bytes of memory where the message is read from.
@param mlen Length of the message.
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where **their** public key is read from.
@param sk Pointer to 32 bytes of memory where **my** secret key is read from.
*/
pub fn
crypto_box_detached(
    c: &mut [u8],
    tag: &mut [u8],
    m: &[u8],
    mlen: u32,
    n: &[u8],
    pk: &[u8],
    sk: &[u8]
) ->
    u32
{ box_detached(mlen, c, tag, sk, pk, n, m) }

/**
See `crypto_box_open_detached`.
*/
pub fn
crypto_box_open_detached_afternm(
    m: &mut [u8],
    c: &[u8],
    tag: &[u8],
    mlen: u32,
    n: &[u8],
    k: &[u8]
) ->
    u32
{ box_open_detached_afternm(mlen, m, k, n, c, tag) }

/**
Verify and decrypt a ciphertext produced by `crypto_box_detached`.

@param m Pointer to `mlen` bytes of memory where the decrypted message is written to.
@param c Pointer to `mlen` bytes of memory where the ciphertext is read from. Note: the ciphertext must include the tag.
@param tag Pointer to 16 (tag length) bytes of memory where the authentication tag is read from.
@param mlen Length of the message (and ciphertext).
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where the public key of the sender is read from.
@param sk Pointer to 32 bytes of memory where the secret key of the recipient is read from.
*/
pub fn
crypto_box_open_detached(
    m: &mut [u8],
    c: &[u8],
    tag: &[u8],
    mlen: u32,
    n: &[u8],
    pk: &[u8],
    sk: &[u8]
) ->
    u32
{ box_open_detached(mlen, m, pk, sk, n, c, tag) }

/**
See `crypto_box_easy`.
*/
pub fn
crypto_box_easy_afternm(c: &mut [u8], m: &[u8], mlen: u32, n: &[u8], k: &[u8]) ->
    u32
{ box_easy_afternm(mlen, c, k, n, m) }

/**
Encrypt a message using the recipient's public key, the sender's secret key, and a nonce.

@param c Pointer to 16 (tag length) + `mlen` bytes of memory where the authentication tag and ciphertext is written to.
@param m Pointer to `mlen` bytes of memory where the message is read from.
@param mlen Length of the message.
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where the public key of the recipient is read from.
@param sk Pointer to 32 bytes of memory where the secret key of the sender is read from.
*/
pub fn
crypto_box_easy(c: &mut [u8], m: &[u8], mlen: u32, n: &[u8], pk: &[u8], sk: &[u8]) ->
    u32
{ box_easy(mlen, c, sk, pk, n, m) }

/**
See `crypto_box_open_easy`.
*/
pub fn
crypto_box_open_easy_afternm(m: &mut [u8], c: &[u8], clen: u32, n: &[u8], k: &[u8]) ->
    u32
{ box_open_easy_afternm(clen.wrapping_sub(16u32), m, k, n, c) }

/**
Verify and decrypt a ciphertext produced by `crypto_box_easy`.

@param m Pointer to `clen` - 16 (tag length) bytes of memory where the decrypted message is written to.
@param c Pointer to `clen` bytes of memory where the ciphertext is read from. Note: the ciphertext must include the tag.
@param clen Length of the ciphertext.
@param n Pointer to 24 (`crypto_box_NONCEBYTES`) bytes of memory where the nonce is read from.
@param pk Pointer to 32 bytes of memory where the public key of the sender is read from.
@param sk Pointer to 32 bytes of memory where the secret key of the recipient is read from.
*/
pub fn
crypto_box_open_easy(m: &mut [u8], c: &[u8], clen: u32, n: &[u8], pk: &[u8], sk: &[u8]) ->
    u32
{ box_open_easy(clen.wrapping_sub(16u32), m, pk, sk, n, c) }
