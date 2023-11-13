#[inline] fn mgf_hash(
    a: crate::spec::hash_definitions::hash_alg,
    len: u32,
    mgfseed: &mut [u8],
    maskLen: u32,
    res: &mut [u8]
) ->
    ()
{
    let mut mgfseed_counter: Vec<u8> = vec![0u8; len.wrapping_add(4u32) as usize];
    ((&mut mgfseed_counter)[0usize..0usize + len as usize]).copy_from_slice(
        &mgfseed[0usize..0usize + len as usize]
    );
    let hLen: u32 = crate::hacl::impl_rsapss_mgf::hash_len(a);
    let n: u32 = maskLen.wrapping_sub(1u32).wrapping_div(hLen).wrapping_add(1u32);
    let accLen: u32 = n.wrapping_mul(hLen);
    let mut acc: Vec<u8> = vec![0u8; accLen as usize];
    for i in 0u32..n
    {
        let acc_i: (&mut [u8], &mut [u8]) = (&mut acc).split_at_mut(i.wrapping_mul(hLen) as usize);
        let c: (&mut [u8], &mut [u8]) = (&mut mgfseed_counter).split_at_mut(len as usize);
        c.1[0usize] = i.wrapping_shr(24u32) as u8;
        c.1[1usize] = i.wrapping_shr(16u32) as u8;
        c.1[2usize] = i.wrapping_shr(8u32) as u8;
        c.1[3usize] = i as u8;
        crate::hacl::impl_rsapss_mgf::hash(a, acc_i.1, len.wrapping_add(4u32), c.0)
    };
    (res[0usize..0usize + maskLen as usize]).copy_from_slice(
        &(&mut (&mut acc)[0usize..])[0usize..0usize + maskLen as usize]
    )
}

#[inline] fn check_num_bits_u64(bs: u32, b: &mut [u64]) -> u64
{
    let bLen: u32 = bs.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    if bs == 64u32.wrapping_mul(bLen)
    { 0xFFFFFFFFFFFFFFFFu64 }
    else
    {
        let mut b2: Vec<u64> = vec![0u64; bLen as usize];
        let i: u32 = bs.wrapping_div(64u32);
        let j: u32 = bs.wrapping_rem(64u32);
        (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u64.wrapping_shl(j);
        let mut acc: u64 = 0u64;
        for i0 in 0u32..bLen
        {
            let beq: u64 = crate::fstar::uint64::eq_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
            let blt: u64 = ! crate::fstar::uint64::gte_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
            acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
        };
        let res: u64 = acc;
        res
    }
}

#[inline] fn check_modulus_u64(modBits: u32, n: &mut [u64]) -> u64
{
    let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let bits0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bits0);
    let mut b2: Vec<u64> = vec![0u64; nLen as usize];
    let i: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32);
    let j: u32 = modBits.wrapping_sub(1u32).wrapping_rem(64u32);
    (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u64.wrapping_shl(j);
    let mut acc: u64 = 0u64;
    for i0 in 0u32..nLen
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut b2)[i0 as usize], n[i0 as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut b2)[i0 as usize], n[i0 as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let res: u64 = acc;
    let m1: u64 = res;
    let m2: u64 = check_num_bits_u64(modBits, n);
    m0 & (m1 & m2)
}

#[inline] fn check_exponent_u64(eBits: u32, e: &mut [u64]) -> u64
{
    let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let mut bn_zero: Vec<u64> = vec![0u64; eLen as usize];
    let mut mask: u64 = 0xFFFFFFFFFFFFFFFFu64;
    for i in 0u32..eLen
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(e[i as usize], (&mut bn_zero)[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u64 = mask;
    let res: u64 = mask1;
    let m0: u64 = res;
    let m1: u64 = check_num_bits_u64(eBits, e);
    ! m0 & m1
}

#[inline] fn pss_encode(
    a: crate::spec::hash_definitions::hash_alg,
    saltLen: u32,
    salt: &mut [u8],
    msgLen: u32,
    msg: &mut [u8],
    emBits: u32,
    em: &mut [u8]
) ->
    ()
{
    let hLen: u32 = crate::hacl::impl_rsapss_mgf::hash_len(a);
    let mut m1Hash: Vec<u8> = vec![0u8; hLen as usize];
    let m1Len: u32 = 8u32.wrapping_add(hLen).wrapping_add(saltLen);
    let mut m1: Vec<u8> = vec![0u8; m1Len as usize];
    crate::hacl::impl_rsapss_mgf::hash(a, &mut (&mut m1)[8usize..], msgLen, msg);
    ((&mut m1)[8u32.wrapping_add(hLen) as usize..8u32.wrapping_add(hLen) as usize
    +
    saltLen as usize]).copy_from_slice(&salt[0usize..0usize + saltLen as usize]);
    crate::hacl::impl_rsapss_mgf::hash(a, &mut m1Hash, m1Len, &mut m1);
    let emLen: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let dbLen: u32 = emLen.wrapping_sub(hLen).wrapping_sub(1u32);
    let mut db: Vec<u8> = vec![0u8; dbLen as usize];
    let last_before_salt: u32 = dbLen.wrapping_sub(saltLen).wrapping_sub(1u32);
    (&mut db)[last_before_salt as usize] = 1u8;
    ((&mut db)[last_before_salt.wrapping_add(1u32) as usize..last_before_salt.wrapping_add(1u32)
    as
    usize
    +
    saltLen as usize]).copy_from_slice(&salt[0usize..0usize + saltLen as usize]);
    let mut dbMask: Vec<u8> = vec![0u8; dbLen as usize];
    mgf_hash(a, hLen, &mut m1Hash, dbLen, &mut dbMask);
    for i in 0u32..dbLen
    {
        let os: (&mut [u8], &mut [u8]) = (&mut db).split_at_mut(0usize);
        let x: u8 = os.1[i as usize] ^ (&mut dbMask)[i as usize];
        os.1[i as usize] = x
    };
    let msBits: u32 = emBits.wrapping_rem(8u32);
    if msBits > 0u32
    { (&mut db)[0usize] = (&mut db)[0usize] & 0xffu8.wrapping_shr(8u32.wrapping_sub(msBits)) };
    (em[0usize..0usize + dbLen as usize]).copy_from_slice(
        &(&mut db)[0usize..0usize + dbLen as usize]
    );
    (em[dbLen as usize..dbLen as usize + hLen as usize]).copy_from_slice(
        &(&mut m1Hash)[0usize..0usize + hLen as usize]
    );
    em[emLen.wrapping_sub(1u32) as usize] = 0xbcu8
}

#[inline] fn pss_verify(
    a: crate::spec::hash_definitions::hash_alg,
    saltLen: u32,
    msgLen: u32,
    msg: &mut [u8],
    emBits: u32,
    em: &mut [u8]
) ->
    bool
{
    let emLen: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let msBits: u32 = emBits.wrapping_rem(8u32);
    let em_0: u8 = if msBits > 0u32 { em[0usize] & 0xffu8.wrapping_shl(msBits) } else { 0u8 };
    let em_last: u8 = em[emLen.wrapping_sub(1u32) as usize];
    if emLen < saltLen.wrapping_add(crate::hacl::impl_rsapss_mgf::hash_len(a)).wrapping_add(2u32)
    { falsebool }
    else
    if ! (em_last == 0xbcu8 && em_0 == 0u8)
    { falsebool }
    else
    {
        let emLen1: u32 = emBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
        let hLen: u32 = crate::hacl::impl_rsapss_mgf::hash_len(a);
        let mut m1Hash0: Vec<u8> = vec![0u8; hLen as usize];
        let dbLen: u32 = emLen1.wrapping_sub(hLen).wrapping_sub(1u32);
        let maskedDB: (&mut [u8], &mut [u8]) = em.split_at_mut(0usize);
        let m1Hash: (&mut [u8], &mut [u8]) = maskedDB.1.split_at_mut(dbLen as usize);
        let mut dbMask: Vec<u8> = vec![0u8; dbLen as usize];
        mgf_hash(a, hLen, m1Hash.1, dbLen, &mut dbMask);
        for i in 0u32..dbLen
        {
            let os: (&mut [u8], &mut [u8]) = (&mut dbMask).split_at_mut(0usize);
            let x: u8 = os.1[i as usize] ^ m1Hash.0[i as usize];
            os.1[i as usize] = x
        };
        let msBits1: u32 = emBits.wrapping_rem(8u32);
        if msBits1 > 0u32
        {
            (&mut dbMask)[0usize] =
                (&mut dbMask)[0usize] & 0xffu8.wrapping_shr(8u32.wrapping_sub(msBits1))
        };
        let padLen: u32 = emLen1.wrapping_sub(saltLen).wrapping_sub(hLen).wrapping_sub(1u32);
        let mut pad2: Vec<u8> = vec![0u8; padLen as usize];
        (&mut pad2)[padLen.wrapping_sub(1u32) as usize] = 0x01u8;
        let pad: (&mut [u8], &mut [u8]) = (&mut dbMask).split_at_mut(0usize);
        let salt: (&mut [u8], &mut [u8]) = pad.1.split_at_mut(padLen as usize);
        let mut res: u8 = 255u8;
        for i in 0u32..padLen
        {
            let uu____0: u8 =
                crate::fstar::uint8::eq_mask(salt.0[i as usize], (&mut pad2)[i as usize]);
            res = uu____0 & res
        };
        let z: u8 = res;
        if ! z == 255u8
        { falsebool }
        else
        {
            let m1Len: u32 = 8u32.wrapping_add(hLen).wrapping_add(saltLen);
            let mut m1: Vec<u8> = vec![0u8; m1Len as usize];
            crate::hacl::impl_rsapss_mgf::hash(a, &mut (&mut m1)[8usize..], msgLen, msg);
            ((&mut m1)[8u32.wrapping_add(hLen) as usize..8u32.wrapping_add(hLen) as usize
            +
            saltLen as usize]).copy_from_slice(&salt.1[0usize..0usize + saltLen as usize]);
            crate::hacl::impl_rsapss_mgf::hash(a, &mut m1Hash0, m1Len, &mut m1);
            let mut res0: u8 = 255u8;
            for i in 0u32..hLen
            {
                let uu____1: u8 =
                    crate::fstar::uint8::eq_mask((&mut m1Hash0)[i as usize], m1Hash.1[i as usize]);
                res0 = uu____1 & res0
            };
            let z0: u8 = res0;
            z0 == 255u8
        }
    }
}

#[inline] fn load_skey(
    modBits: u32,
    eBits: u32,
    dBits: u32,
    nb: &mut [u8],
    eb: &mut [u8],
    db: &mut [u8],
    skey: &mut [u64]
) ->
    bool
{
    let dbLen: u32 = dBits.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let nLen: u32 = modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let eLen: u32 = eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32);
    let pkeyLen: u32 = nLen.wrapping_add(nLen).wrapping_add(eLen);
    let pkey: (&mut [u64], &mut [u64]) = skey.split_at_mut(0usize);
    let d: (&mut [u64], &mut [u64]) = pkey.1.split_at_mut(pkeyLen as usize);
    let b: bool = load_pkey(modBits, eBits, nb, eb, d.0);
    crate::hacl::bignum_base::bn_from_bytes_be_uint64(dbLen, db, d.1);
    let m1: u64 = check_exponent_u64(dBits, d.1);
    b && m1 == 0xFFFFFFFFFFFFFFFFu64
}

pub fn rsapss_skey_sign(
    a: crate::spec::hash_definitions::hash_alg,
    modBits: u32,
    eBits: u32,
    dBits: u32,
    nb: &mut [u8],
    eb: &mut [u8],
    db: &mut [u8],
    saltLen: u32,
    salt: &mut [u8],
    msgLen: u32,
    msg: &mut [u8],
    sgnt: &mut [u8]
) ->
    bool
{
    let mut skey: Vec<u64> =
        vec![0u64;
            2u32.wrapping_mul(modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)).wrapping_add(
                eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)
            ).wrapping_add(dBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32))
            as
            usize];
    let b: bool = load_skey(modBits, eBits, dBits, nb, eb, db, &mut skey);
    if b
    { rsapss_sign(a, modBits, eBits, dBits, &mut skey, saltLen, salt, msgLen, msg, sgnt) }
    else
    { falsebool }
}

pub fn rsapss_pkey_verify(
    a: crate::spec::hash_definitions::hash_alg,
    modBits: u32,
    eBits: u32,
    nb: &mut [u8],
    eb: &mut [u8],
    saltLen: u32,
    sgntLen: u32,
    sgnt: &mut [u8],
    msgLen: u32,
    msg: &mut [u8]
) ->
    bool
{
    let mut pkey: Vec<u64> =
        vec![0u64;
            2u32.wrapping_mul(modBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)).wrapping_add(
                eBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32)
            )
            as
            usize];
    let b: bool = load_pkey(modBits, eBits, nb, eb, &mut pkey);
    if b
    { rsapss_verify(a, modBits, eBits, &mut pkey, saltLen, sgntLen, sgnt, msgLen, msg) }
    else
    { falsebool }
}

pub fn mgf_hash(
    a: crate::spec::hash_definitions::hash_alg,
    len: u32,
    mgfseed: &mut [u8],
    maskLen: u32,
    res: &mut [u8]
) ->
    ()
{ mgf_hash(a, len, mgfseed, maskLen, res) }
