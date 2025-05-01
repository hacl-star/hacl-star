#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn hash_len(a: crate::streaming_types::hash_alg) -> u32
{
    match a
    {
        crate::streaming_types::hash_alg::MD5 => 16u32,
        crate::streaming_types::hash_alg::SHA1 => 20u32,
        crate::streaming_types::hash_alg::SHA2_224 => 28u32,
        crate::streaming_types::hash_alg::SHA2_256 => 32u32,
        crate::streaming_types::hash_alg::SHA2_384 => 48u32,
        crate::streaming_types::hash_alg::SHA2_512 => 64u32,
        crate::streaming_types::hash_alg::Blake2S => 32u32,
        crate::streaming_types::hash_alg::Blake2B => 64u32,
        crate::streaming_types::hash_alg::SHA3_224 => 28u32,
        crate::streaming_types::hash_alg::SHA3_256 => 32u32,
        crate::streaming_types::hash_alg::SHA3_384 => 48u32,
        crate::streaming_types::hash_alg::SHA3_512 => 64u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[inline] fn hash(
    a: crate::streaming_types::hash_alg,
    mHash: &mut [u8],
    msgLen: u32,
    msg: &[u8]
)
{
    match a
    {
        crate::streaming_types::hash_alg::SHA2_256 => crate::hash_sha2::hash_256(mHash, msg, msgLen),
        crate::streaming_types::hash_alg::SHA2_384 => crate::hash_sha2::hash_384(mHash, msg, msgLen),
        crate::streaming_types::hash_alg::SHA2_512 => crate::hash_sha2::hash_512(mHash, msg, msgLen),
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[inline] fn mgf_hash(
    a: crate::streaming_types::hash_alg,
    len: u32,
    mgfseed: &[u8],
    maskLen: u32,
    res: &mut [u8]
)
{
    let mut mgfseed_counter: Box<[u8]> =
        vec![0u8; len.wrapping_add(4u32) as usize].into_boxed_slice();
    ((&mut mgfseed_counter)[0usize..len as usize]).copy_from_slice(&mgfseed[0usize..len as usize]);
    let hLen: u32 = crate::rsapss::hash_len(a);
    let n: u32 = maskLen.wrapping_sub(1u32).wrapping_div(hLen).wrapping_add(1u32);
    let accLen: u32 = n.wrapping_mul(hLen);
    let mut acc: Box<[u8]> = vec![0u8; accLen as usize].into_boxed_slice();
    for i in 0u32..n
    {
        let acc_i: (&mut [u8], &mut [u8]) = acc.split_at_mut(i.wrapping_mul(hLen) as usize);
        let c: (&mut [u8], &mut [u8]) = mgfseed_counter.split_at_mut(len as usize);
        c.1[0usize] = i.wrapping_shr(24u32) as u8;
        c.1[1usize] = i.wrapping_shr(16u32) as u8;
        c.1[2usize] = i.wrapping_shr(8u32) as u8;
        c.1[3usize] = i as u8;
        crate::rsapss::hash(a, acc_i.1, len.wrapping_add(4u32), &mgfseed_counter)
    };
    (res[0usize..maskLen as usize]).copy_from_slice(&(&(&acc)[0usize..])[0usize..maskLen as usize])
}

#[inline] fn check_num_bits_u64(bs: u32, b: &[u64]) -> u64
{
    let bLen: u32 = bs.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    if bs == 64u32.wrapping_mul(bLen)
    { 0xFFFFFFFFFFFFFFFFu64 }
    else
    {
        let mut b2: Box<[u64]> = vec![0u64; bLen as usize].into_boxed_slice();
        let i: u32 = bs.wrapping_div(64u32);
        let j: u32 = bs.wrapping_rem(64u32);
        (&mut b2)[i as usize] = (&b2)[i as usize] | 1u64.wrapping_shl(j);
        let mut acc: [u64; 1] = [0u64; 1usize];
        for i0 in 0u32..bLen
        {
            let beq: u64 = fstar::uint64::eq_mask(b[i0 as usize], (&b2)[i0 as usize]);
            let blt: u64 = ! fstar::uint64::gte_mask(b[i0 as usize], (&b2)[i0 as usize]);
            (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & blt
        };
        let res: u64 = (&acc)[0usize];
        res
    }
}

#[inline] fn check_modulus_u64(modBits: u32, n: &[u64]) -> u64
{
    let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let bits0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bits0);
    let mut b2: Box<[u64]> = vec![0u64; nLen as usize].into_boxed_slice();
    let i: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32);
    let j: u32 = modBits.wrapping_sub(1u32).wrapping_rem(64u32);
    (&mut b2)[i as usize] = (&b2)[i as usize] | 1u64.wrapping_shl(j);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i0 in 0u32..nLen
    {
        let beq: u64 = fstar::uint64::eq_mask((&b2)[i0 as usize], n[i0 as usize]);
        let blt: u64 = ! fstar::uint64::gte_mask((&b2)[i0 as usize], n[i0 as usize]);
        (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & blt
    };
    let res: u64 = (&acc)[0usize];
    let m1: u64 = res;
    let m2: u64 = crate::rsapss::check_num_bits_u64(modBits, n);
    m0 & (m1 & m2)
}

#[inline] fn check_exponent_u64(eBits: u32, e: &[u64]) -> u64
{
    let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let bn_zero: Box<[u64]> = vec![0u64; eLen as usize].into_boxed_slice();
    let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
    for i in 0u32..eLen
    {
        let uu____0: u64 = fstar::uint64::eq_mask(e[i as usize], (&bn_zero)[i as usize]);
        (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
    };
    let mask1: u64 = (&mask)[0usize];
    let res: u64 = mask1;
    let m0: u64 = res;
    let m1: u64 = crate::rsapss::check_num_bits_u64(eBits, e);
    ! m0 & m1
}

#[inline] fn pss_encode(
    a: crate::streaming_types::hash_alg,
    saltLen: u32,
    salt: &[u8],
    msgLen: u32,
    msg: &[u8],
    emBits: u32,
    em: &mut [u8]
)
{
    let hLen: u32 = crate::rsapss::hash_len(a);
    let mut m1Hash: Box<[u8]> = vec![0u8; hLen as usize].into_boxed_slice();
    let m1Len: u32 = 8u32.wrapping_add(hLen).wrapping_add(saltLen);
    let mut m1: Box<[u8]> = vec![0u8; m1Len as usize].into_boxed_slice();
    crate::rsapss::hash(a, &mut (&mut m1)[8usize..], msgLen, msg);
    ((&mut m1)[8u32.wrapping_add(hLen) as usize..8u32.wrapping_add(hLen) as usize
    +
    saltLen as usize]).copy_from_slice(&salt[0usize..saltLen as usize]);
    crate::rsapss::hash(a, &mut m1Hash, m1Len, &m1);
    let emLen: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let dbLen: u32 = emLen.wrapping_sub(hLen).wrapping_sub(1u32);
    let mut db: Box<[u8]> = vec![0u8; dbLen as usize].into_boxed_slice();
    let last_before_salt: u32 = dbLen.wrapping_sub(saltLen).wrapping_sub(1u32);
    (&mut db)[last_before_salt as usize] = 1u8;
    ((&mut db)[last_before_salt.wrapping_add(1u32) as usize..last_before_salt.wrapping_add(1u32)
    as
    usize
    +
    saltLen as usize]).copy_from_slice(&salt[0usize..saltLen as usize]);
    let mut dbMask: Box<[u8]> = vec![0u8; dbLen as usize].into_boxed_slice();
    crate::rsapss::mgf_hash(a, hLen, &m1Hash, dbLen, &mut dbMask);
    for i in 0u32..dbLen
    {
        let x: u8 = (&db)[i as usize] ^ (&dbMask)[i as usize];
        let os: (&mut [u8], &mut [u8]) = db.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let msBits: u32 = emBits.wrapping_rem(8u32);
    if msBits > 0u32
    { (&mut db)[0usize] = (&db)[0usize] & 0xffu8.wrapping_shr(8u32.wrapping_sub(msBits)) };
    (em[0usize..dbLen as usize]).copy_from_slice(&(&db)[0usize..dbLen as usize]);
    (em[dbLen as usize..dbLen as usize + hLen as usize]).copy_from_slice(
        &(&m1Hash)[0usize..hLen as usize]
    );
    em[emLen.wrapping_sub(1u32) as usize] = 0xbcu8
}

#[inline] fn pss_verify(
    a: crate::streaming_types::hash_alg,
    saltLen: u32,
    msgLen: u32,
    msg: &[u8],
    emBits: u32,
    em: &[u8]
) ->
    bool
{
    let emLen: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let msBits: u32 = emBits.wrapping_rem(8u32);
    let em_0: u8 = if msBits > 0u32 { em[0usize] & 0xffu8.wrapping_shl(msBits) } else { 0u8 };
    let em_last: u8 = em[emLen.wrapping_sub(1u32) as usize];
    if
    emLen < saltLen.wrapping_add(crate::rsapss::hash_len(a)).wrapping_add(2u32)
    ||
    ! (em_last == 0xbcu8 && em_0 == 0u8)
    { false }
    else
    {
        let emLen1: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let hLen: u32 = crate::rsapss::hash_len(a);
        let mut m1Hash0: Box<[u8]> = vec![0u8; hLen as usize].into_boxed_slice();
        let dbLen: u32 = emLen1.wrapping_sub(hLen).wrapping_sub(1u32);
        let maskedDB: (&[u8], &[u8]) = em.split_at(0usize);
        let m1Hash: (&[u8], &[u8]) = (maskedDB.1).split_at(dbLen as usize);
        let mut dbMask: Box<[u8]> = vec![0u8; dbLen as usize].into_boxed_slice();
        crate::rsapss::mgf_hash(a, hLen, m1Hash.1, dbLen, &mut dbMask);
        for i in 0u32..dbLen
        {
            let x: u8 = (&dbMask)[i as usize] ^ m1Hash.0[i as usize];
            let os: (&mut [u8], &mut [u8]) = dbMask.split_at_mut(0usize);
            os.1[i as usize] = x
        };
        let msBits1: u32 = emBits.wrapping_rem(8u32);
        if msBits1 > 0u32
        {
            (&mut dbMask)[0usize] =
                (&dbMask)[0usize] & 0xffu8.wrapping_shr(8u32.wrapping_sub(msBits1))
        };
        let padLen: u32 = emLen1.wrapping_sub(saltLen).wrapping_sub(hLen).wrapping_sub(1u32);
        let mut pad2: Box<[u8]> = vec![0u8; padLen as usize].into_boxed_slice();
        (&mut pad2)[padLen.wrapping_sub(1u32) as usize] = 0x01u8;
        let pad: (&[u8], &[u8]) = dbMask.split_at(0usize);
        let salt: (&[u8], &[u8]) = (pad.1).split_at(padLen as usize);
        let mut res: [u8; 1] = [255u8; 1usize];
        for i in 0u32..padLen
        {
            let uu____0: u8 = fstar::uint8::eq_mask(salt.0[i as usize], (&pad2)[i as usize]);
            (&mut res)[0usize] = uu____0 & (&res)[0usize]
        };
        let z: u8 = (&res)[0usize];
        if z != 255u8
        { false }
        else
        {
            let m1Len: u32 = 8u32.wrapping_add(hLen).wrapping_add(saltLen);
            let mut m1: Box<[u8]> = vec![0u8; m1Len as usize].into_boxed_slice();
            crate::rsapss::hash(a, &mut (&mut m1)[8usize..], msgLen, msg);
            ((&mut m1)[8u32.wrapping_add(hLen) as usize..8u32.wrapping_add(hLen) as usize
            +
            saltLen as usize]).copy_from_slice(&salt.1[0usize..saltLen as usize]);
            crate::rsapss::hash(a, &mut m1Hash0, m1Len, &m1);
            let mut res0: [u8; 1] = [255u8; 1usize];
            for i in 0u32..hLen
            {
                let uu____1: u8 =
                    fstar::uint8::eq_mask((&m1Hash0)[i as usize], m1Hash.1[i as usize]);
                (&mut res0)[0usize] = uu____1 & (&res0)[0usize]
            };
            let z0: u8 = (&res0)[0usize];
            z0 == 255u8
        }
    }
}

#[inline] fn load_pkey(modBits: u32, eBits: u32, nb: &[u8], eb: &[u8], pkey: &mut [u64]) ->
    bool
{
    let nbLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let ebLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let n: (&mut [u64], &mut [u64]) = pkey.split_at_mut(0usize);
    let r2: (&mut [u64], &mut [u64]) = (n.1).split_at_mut(nLen as usize);
    let e: (&mut [u64], &mut [u64]) =
        (r2.1).split_at_mut(nLen.wrapping_add(nLen) as usize - nLen as usize);
    bignum::bignum_base::bn_from_bytes_be_uint64(nbLen, nb, r2.0);
    bignum::bignum::bn_precomp_r2_mod_n_u64(
        modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32),
        modBits.wrapping_sub(1u32),
        r2.0,
        e.0
    );
    bignum::bignum_base::bn_from_bytes_be_uint64(ebLen, eb, e.1);
    let m0: u64 = crate::rsapss::check_modulus_u64(modBits, r2.0);
    let m1: u64 = crate::rsapss::check_exponent_u64(eBits, e.1);
    let m: u64 = m0 & m1;
    m == 0xFFFFFFFFFFFFFFFFu64
}

#[inline] fn load_skey(
    modBits: u32,
    eBits: u32,
    dBits: u32,
    nb: &[u8],
    eb: &[u8],
    db: &[u8],
    skey: &mut [u64]
) ->
    bool
{
    let dbLen: u32 = dBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let pkeyLen: u32 = nLen.wrapping_add(nLen).wrapping_add(eLen);
    let pkey: (&mut [u64], &mut [u64]) = skey.split_at_mut(0usize);
    let d: (&mut [u64], &mut [u64]) = (pkey.1).split_at_mut(pkeyLen as usize);
    let b: bool = crate::rsapss::load_pkey(modBits, eBits, nb, eb, d.0);
    bignum::bignum_base::bn_from_bytes_be_uint64(dbLen, db, d.1);
    let m1: u64 = crate::rsapss::check_exponent_u64(dBits, d.1);
    b && m1 == 0xFFFFFFFFFFFFFFFFu64
}

/**
Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param skey Pointer to secret key created by `Hacl_RSAPSS_new_rsapss_load_skey`.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful.
*/
pub fn
rsapss_sign(
    a: crate::streaming_types::hash_alg,
    modBits: u32,
    eBits: u32,
    dBits: u32,
    skey: &[u64],
    saltLen: u32,
    salt: &[u8],
    msgLen: u32,
    msg: &[u8],
    sgnt: &mut [u8]
) ->
    bool
{
    let hLen: u32 = crate::rsapss::hash_len(a);
    let b: bool =
        saltLen <= 0xffffffffu32.wrapping_sub(hLen).wrapping_sub(8u32)
        &&
        saltLen.wrapping_add(hLen).wrapping_add(2u32)
        <=
        modBits.wrapping_sub(1u32).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    if b
    {
        let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let mut m: Box<[u64]> = vec![0u64; nLen as usize].into_boxed_slice();
        let emBits: u32 = modBits.wrapping_sub(1u32);
        let emLen: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let mut em: Box<[u8]> = vec![0u8; emLen as usize].into_boxed_slice();
        crate::rsapss::pss_encode(a, saltLen, salt, msgLen, msg, emBits, &mut em);
        bignum::bignum_base::bn_from_bytes_be_uint64(emLen, &em, &mut (&mut m)[0usize..]);
        let nLen1: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let k: u32 = modBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let mut s: Box<[u64]> = vec![0u64; nLen1 as usize].into_boxed_slice();
        let mut m·: Box<[u64]> = vec![0u64; nLen1 as usize].into_boxed_slice();
        let nLen2: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let n: (&[u64], &[u64]) = skey.split_at(0usize);
        let r2: (&[u64], &[u64]) = (n.1).split_at(nLen2 as usize);
        let e: (&[u64], &[u64]) =
            (r2.1).split_at(nLen2.wrapping_add(nLen2) as usize - nLen2 as usize);
        let d: (&[u64], &[u64]) =
            (e.1).split_at(
                nLen2.wrapping_add(nLen2).wrapping_add(eLen) as usize
                -
                nLen2.wrapping_add(nLen2) as usize
            );
        let mu: u64 = bignum::bignum::mod_inv_uint64(r2.0[0usize]);
        bignum::bignum::bn_mod_exp_consttime_precomp_u64(
            modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32),
            r2.0,
            mu,
            e.0,
            &m,
            dBits,
            d.1,
            &mut s
        );
        let mu0: u64 = bignum::bignum::mod_inv_uint64(r2.0[0usize]);
        bignum::bignum::bn_mod_exp_vartime_precomp_u64(
            modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32),
            r2.0,
            mu0,
            e.0,
            &s,
            eBits,
            d.0,
            &mut m·
        );
        let mut mask: [u64; 1] = [0xFFFFFFFFFFFFFFFFu64; 1usize];
        for i in 0u32..nLen2
        {
            let uu____0: u64 = fstar::uint64::eq_mask((&m)[i as usize], (&m·)[i as usize]);
            (&mut mask)[0usize] = uu____0 & (&mask)[0usize]
        };
        let mask1: u64 = (&mask)[0usize];
        let eq_m: u64 = mask1;
        for i in 0u32..nLen2
        {
            let x: u64 = (&s)[i as usize];
            let x0: u64 = eq_m & x;
            let os: (&mut [u64], &mut [u64]) = s.split_at_mut(0usize);
            os.1[i as usize] = x0
        };
        let eq_b: bool = eq_m == 0xFFFFFFFFFFFFFFFFu64;
        bignum::bignum_base::bn_to_bytes_be_uint64(k, &s, sgnt);
        let eq_b0: bool = eq_b;
        eq_b0
    }
    else
    { false }
}

/**
Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param pkey Pointer to public key created by `Hacl_RSAPSS_new_rsapss_load_pkey`.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid.
*/
pub fn
rsapss_verify(
    a: crate::streaming_types::hash_alg,
    modBits: u32,
    eBits: u32,
    pkey: &[u64],
    saltLen: u32,
    sgntLen: u32,
    sgnt: &[u8],
    msgLen: u32,
    msg: &[u8]
) ->
    bool
{
    let hLen: u32 = crate::rsapss::hash_len(a);
    let b: bool =
        saltLen <= 0xffffffffu32.wrapping_sub(hLen).wrapping_sub(8u32)
        &&
        sgntLen == modBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    if b
    {
        let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let mut m: Box<[u64]> = vec![0u64; nLen as usize].into_boxed_slice();
        let nLen1: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let k: u32 = modBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let mut s: Box<[u64]> = vec![0u64; nLen1 as usize].into_boxed_slice();
        bignum::bignum_base::bn_from_bytes_be_uint64(k, sgnt, &mut s);
        let nLen2: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let n: (&[u64], &[u64]) = pkey.split_at(0usize);
        let r2: (&[u64], &[u64]) = (n.1).split_at(nLen2 as usize);
        let e: (&[u64], &[u64]) =
            (r2.1).split_at(nLen2.wrapping_add(nLen2) as usize - nLen2 as usize);
        let mut acc: [u64; 1] = [0u64; 1usize];
        for i in 0u32..nLen2
        {
            let beq: u64 = fstar::uint64::eq_mask((&s)[i as usize], r2.0[i as usize]);
            let blt: u64 = ! fstar::uint64::gte_mask((&s)[i as usize], r2.0[i as usize]);
            (&mut acc)[0usize] = beq & (&acc)[0usize] | ! beq & blt
        };
        let mask: u64 = (&acc)[0usize];
        let res: bool =
            if mask == 0xFFFFFFFFFFFFFFFFu64
            {
                let mu: u64 = bignum::bignum::mod_inv_uint64(r2.0[0usize]);
                bignum::bignum::bn_mod_exp_vartime_precomp_u64(
                    modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32),
                    r2.0,
                    mu,
                    e.0,
                    &s,
                    eBits,
                    e.1,
                    &mut m
                );
                if modBits.wrapping_sub(1u32).wrapping_rem(8u32) != 0u32
                { true }
                else
                {
                    let i: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32);
                    let j: u32 = modBits.wrapping_sub(1u32).wrapping_rem(64u32);
                    let tmp: u64 = (&m)[i as usize];
                    let get_bit: u64 = tmp.wrapping_shr(j) & 1u64;
                    get_bit == 0u64
                }
            }
            else
            { false };
        let b1: bool = res;
        let b10: bool = b1;
        if b10
        {
            let emBits: u32 = modBits.wrapping_sub(1u32);
            let emLen: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
            let mut em: Box<[u8]> = vec![0u8; emLen as usize].into_boxed_slice();
            let m1: (&[u64], &[u64]) = m.split_at(0usize);
            bignum::bignum_base::bn_to_bytes_be_uint64(emLen, m1.1, &mut em);
            let res0: bool = crate::rsapss::pss_verify(a, saltLen, msgLen, msg, emBits, &em);
            res0
        }
        else
        { false }
    }
    else
    { false }
}

/**
Load a public key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.

@return Returns an allocated public key upon success, otherwise, `NULL` if key part arguments are invalid or memory allocation fails. Note: caller must take care to `free()` the created key.
*/
pub fn
new_rsapss_load_pkey
<'a>(modBits: u32, eBits: u32, nb: &'a [u8], eb: &'a [u8]) ->
    Box<[u64]>
{
    let ite: bool =
        if 1u32 < modBits && 0u32 < eBits
        {
            let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            nLen <= 33554431u32 && eLen <= 67108863u32
            &&
            nLen.wrapping_add(nLen) <= 0xffffffffu32.wrapping_sub(eLen)
        }
        else
        { false };
    if ! ite
    { [].into() }
    else
    {
        let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let pkeyLen: u32 = nLen.wrapping_add(nLen).wrapping_add(eLen);
        let mut pkey: Box<[u64]> = vec![0u64; pkeyLen as usize].into_boxed_slice();
        let pkey1: &mut [u64] = &mut pkey;
        let pkey2: &mut [u64] = pkey1;
        let nbLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let ebLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let nLen1: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let n: (&mut [u64], &mut [u64]) = pkey2.split_at_mut(0usize);
        let r2: (&mut [u64], &mut [u64]) = (n.1).split_at_mut(nLen1 as usize);
        let e: (&mut [u64], &mut [u64]) =
            (r2.1).split_at_mut(nLen1.wrapping_add(nLen1) as usize - nLen1 as usize);
        bignum::bignum_base::bn_from_bytes_be_uint64(nbLen, nb, r2.0);
        bignum::bignum::bn_precomp_r2_mod_n_u64(
            modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32),
            modBits.wrapping_sub(1u32),
            r2.0,
            e.0
        );
        bignum::bignum_base::bn_from_bytes_be_uint64(ebLen, eb, e.1);
        let m0: u64 = crate::rsapss::check_modulus_u64(modBits, r2.0);
        let m1: u64 = crate::rsapss::check_exponent_u64(eBits, e.1);
        let m: u64 = m0 & m1;
        let b: bool = m == 0xFFFFFFFFFFFFFFFFu64;
        if b { (*pkey2).into() } else { [].into() }
    }
}

/**
Load a secret key from key parts.

@param modBits Count of bits in modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value, in big-endian byte order, is read from.

@return Returns an allocated secret key upon success, otherwise, `NULL` if key part arguments are invalid or memory allocation fails. Note: caller must take care to `free()` the created key.
*/
pub fn
new_rsapss_load_skey
<'a>(modBits: u32, eBits: u32, dBits: u32, nb: &'a [u8], eb: &'a [u8], db: &'a [u8]) ->
    Box<[u64]>
{
    let ite: bool =
        if 1u32 < modBits && 0u32 < eBits
        {
            let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            nLen <= 33554431u32 && eLen <= 67108863u32
            &&
            nLen.wrapping_add(nLen) <= 0xffffffffu32.wrapping_sub(eLen)
        }
        else
        { false };
    let ite0: bool =
        if ite && 0u32 < dBits
        {
            let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            let dLen: u32 = dBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
            dLen <= 67108863u32
            &&
            2u32.wrapping_mul(nLen) <= 0xffffffffu32.wrapping_sub(eLen).wrapping_sub(dLen)
        }
        else
        { false };
    if ! ite0
    { [].into() }
    else
    {
        let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let dLen: u32 = dBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let skeyLen: u32 = nLen.wrapping_add(nLen).wrapping_add(eLen).wrapping_add(dLen);
        let mut skey: Box<[u64]> = vec![0u64; skeyLen as usize].into_boxed_slice();
        let skey1: &mut [u64] = &mut skey;
        let skey2: &mut [u64] = skey1;
        let dbLen: u32 = dBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let nLen1: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let eLen1: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let pkeyLen: u32 = nLen1.wrapping_add(nLen1).wrapping_add(eLen1);
        let pkey: (&mut [u64], &mut [u64]) = skey2.split_at_mut(0usize);
        let d: (&mut [u64], &mut [u64]) = (pkey.1).split_at_mut(pkeyLen as usize);
        let nbLen1: u32 = modBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let ebLen1: u32 = eBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let nLen2: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
        let n: (&mut [u64], &mut [u64]) = (d.0).split_at_mut(0usize);
        let r2: (&mut [u64], &mut [u64]) = (n.1).split_at_mut(nLen2 as usize);
        let e: (&mut [u64], &mut [u64]) =
            (r2.1).split_at_mut(nLen2.wrapping_add(nLen2) as usize - nLen2 as usize);
        bignum::bignum_base::bn_from_bytes_be_uint64(nbLen1, nb, r2.0);
        bignum::bignum::bn_precomp_r2_mod_n_u64(
            modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32),
            modBits.wrapping_sub(1u32),
            r2.0,
            e.0
        );
        bignum::bignum_base::bn_from_bytes_be_uint64(ebLen1, eb, e.1);
        let m0: u64 = crate::rsapss::check_modulus_u64(modBits, r2.0);
        let m1: u64 = crate::rsapss::check_exponent_u64(eBits, e.1);
        let m: u64 = m0 & m1;
        let b: bool = m == 0xFFFFFFFFFFFFFFFFu64;
        bignum::bignum_base::bn_from_bytes_be_uint64(dbLen, db, d.1);
        let m10: u64 = crate::rsapss::check_exponent_u64(dBits, d.1);
        let b0: bool = b && m10 == 0xFFFFFFFFFFFFFFFFu64;
        if b0 { (*skey2).into() } else { [].into() }
    }
}

/**
Sign a message `msg` and write the signature to `sgnt`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param dBits Count of bits in `d` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param db Pointer to `ceil(modBits / 8)` bytes where the `d` value, in big-endian byte order, is read from.
@param saltLen Length of salt.
@param salt Pointer to `saltLen` bytes where the salt is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.
@param sgnt Pointer to `ceil(modBits / 8)` bytes where the signature is written to.

@return Returns true if and only if signing was successful.
*/
pub fn
rsapss_skey_sign(
    a: crate::streaming_types::hash_alg,
    modBits: u32,
    eBits: u32,
    dBits: u32,
    nb: &[u8],
    eb: &[u8],
    db: &[u8],
    saltLen: u32,
    salt: &[u8],
    msgLen: u32,
    msg: &[u8],
    sgnt: &mut [u8]
) ->
    bool
{
    let mut skey: Box<[u64]> =
        vec![0u64;
            2u32.wrapping_mul(modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)).wrapping_add(
                eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)
            ).wrapping_add(dBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32))
            as
            usize].into_boxed_slice();
    let b: bool = crate::rsapss::load_skey(modBits, eBits, dBits, nb, eb, db, &mut skey);
    if b
    {
        crate::rsapss::rsapss_sign(
            a,
            modBits,
            eBits,
            dBits,
            &skey,
            saltLen,
            salt,
            msgLen,
            msg,
            sgnt
        )
    }
    else
    { false }
}

/**
Verify the signature `sgnt` of a message `msg`.

@param a Hash algorithm to use. Allowed values for `a` are ...
  - Spec_Hash_Definitions_SHA2_256,
  - Spec_Hash_Definitions_SHA2_384, and
  - Spec_Hash_Definitions_SHA2_512.
@param modBits Count of bits in the modulus (`n`).
@param eBits Count of bits in `e` value.
@param nb Pointer to `ceil(modBits / 8)` bytes where the modulus (`n`), in big-endian byte order, is read from.
@param eb Pointer to `ceil(modBits / 8)` bytes where the `e` value, in big-endian byte order, is read from.
@param saltLen Length of salt.
@param sgntLen Length of signature.
@param sgnt Pointer to `sgntLen` bytes where the signature is read from.
@param msgLen Length of message.
@param msg Pointer to `msgLen` bytes where the message is read from.

@return Returns true if and only if the signature is valid.
*/
pub fn
rsapss_pkey_verify(
    a: crate::streaming_types::hash_alg,
    modBits: u32,
    eBits: u32,
    nb: &[u8],
    eb: &[u8],
    saltLen: u32,
    sgntLen: u32,
    sgnt: &[u8],
    msgLen: u32,
    msg: &[u8]
) ->
    bool
{
    let mut pkey: Box<[u64]> =
        vec![0u64;
            2u32.wrapping_mul(modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)).wrapping_add(
                eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)
            )
            as
            usize].into_boxed_slice();
    let b: bool = crate::rsapss::load_pkey(modBits, eBits, nb, eb, &mut pkey);
    if b
    { crate::rsapss::rsapss_verify(a, modBits, eBits, &pkey, saltLen, sgntLen, sgnt, msgLen, msg) }
    else
    { false }
}

/**
The mask generation function defined in the Public Key Cryptography Standard #1
  (https://www.ietf.org/rfc/rfc2437.txt Section 10.2.1)
*/
pub fn
mgf_hash0(
    a: crate::streaming_types::hash_alg,
    len: u32,
    mgfseed: &[u8],
    maskLen: u32,
    res: &mut [u8]
)
{ crate::rsapss::mgf_hash(a, len, mgfseed, maskLen, res) }
