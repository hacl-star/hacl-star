const g25519: [u8; 32] =
    [9u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8,
        0u8];

fn point_add_and_double(
    q: &mut [u64],
    p01_tmp1: &mut [u64],
    tmp2: &mut [crate::fstar::uint128::uint128]
) ->
    ()
{
    let nq: (&mut [u64], &mut [u64]) = p01_tmp1.split_at_mut(0usize);
    let nq_p1: (&mut [u64], &mut [u64]) = nq.1.split_at_mut(10usize);
    let tmp1: (&mut [u64], &mut [u64]) = nq_p1.1.split_at_mut(10usize);
    let x1: (&mut [u64], &mut [u64]) = q.split_at_mut(0usize);
    let x2: (&mut [u64], &mut [u64]) = nq_p1.0.split_at_mut(0usize);
    let z2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(5usize);
    let z3: (&mut [u64], &mut [u64]) = tmp1.0.split_at_mut(5usize);
    let a: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(0usize);
    let b: (&mut [u64], &mut [u64]) = a.1.split_at_mut(5usize);
    let ab: (&mut [u64], &mut [u64]) = b.0.split_at_mut(0usize);
    let dc: (&mut [u64], &mut [u64]) = b.1.split_at_mut(5usize);
    crate::hacl::bignum25519_51::fadd(ab.0, z2.0, z2.1);
    crate::hacl::bignum25519_51::fsub(dc.0, z2.0, z2.1);
    let x3: (&mut [u64], &mut [u64]) = z3.0.split_at_mut(0usize);
    let z31: (&mut [u64], &mut [u64]) = z3.1.split_at_mut(0usize);
    let d: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c: (&mut [u64], &mut [u64]) = d.1.split_at_mut(5usize);
    crate::hacl::bignum25519_51::fadd(c.1, x3.1, z31.1);
    crate::hacl::bignum25519_51::fsub(c.0, x3.1, z31.1);
    crate::hacl::impl::curve25519::field51::fmul2(c.0, c.0, ab.1, tmp2);
    crate::hacl::bignum25519_51::fadd(x3.1, c.0, c.1);
    crate::hacl::bignum25519_51::fsub(z31.1, c.0, c.1);
    let a1: (&mut [u64], &mut [u64]) = ab.1.split_at_mut(0usize);
    let b1: (&mut [u64], &mut [u64]) = dc.0.split_at_mut(0usize);
    let d0: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c0: (&mut [u64], &mut [u64]) = d0.1.split_at_mut(5usize);
    let ab1: (&mut [u64], &mut [u64]) = a1.1.split_at_mut(0usize);
    let dc1: (&mut [u64], &mut [u64]) = c0.0.split_at_mut(0usize);
    crate::hacl::impl::curve25519::field51::fsqr2(dc1.1, ab1.1, tmp2);
    crate::hacl::impl::curve25519::field51::fsqr2(x3.1, x3.1, tmp2);
    ab1.0[0u32 as usize] = c0.1[0u32 as usize];
    ab1.0[1u32 as usize] = c0.1[1u32 as usize];
    ab1.0[2u32 as usize] = c0.1[2u32 as usize];
    ab1.0[3u32 as usize] = c0.1[3u32 as usize];
    ab1.0[4u32 as usize] = c0.1[4u32 as usize];
    crate::hacl::bignum25519_51::fsub(c0.1, dc1.0, c0.1);
    crate::hacl::bignum25519_51::fmul1(b1.1, c0.1, 121665u64);
    crate::hacl::bignum25519_51::fadd(b1.1, b1.1, dc1.0);
    crate::hacl::impl::curve25519::field51::fmul2(z2.0, dc1.1, ab1.1, tmp2);
    crate::hacl::impl::curve25519::field51::fmul(z31.0, z31.0, x1.1, tmp2)
}

fn point_double(nq: &mut [u64], tmp1: &mut [u64], tmp2: &mut [crate::fstar::uint128::uint128]) ->
    ()
{
    let x2: (&mut [u64], &mut [u64]) = nq.split_at_mut(0usize);
    let z2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(5usize);
    let a: (&mut [u64], &mut [u64]) = tmp1.split_at_mut(0usize);
    let b: (&mut [u64], &mut [u64]) = a.1.split_at_mut(5usize);
    let d: (&mut [u64], &mut [u64]) = b.1.split_at_mut(5usize);
    let c: (&mut [u64], &mut [u64]) = d.1.split_at_mut(5usize);
    let ab: (&mut [u64], &mut [u64]) = b.0.split_at_mut(0usize);
    let dc: (&mut [u64], &mut [u64]) = c.0.split_at_mut(0usize);
    crate::hacl::bignum25519_51::fadd(ab.0, z2.0, z2.1);
    crate::hacl::bignum25519_51::fsub(d.0, z2.0, z2.1);
    crate::hacl::impl::curve25519::field51::fsqr2(dc.1, ab.1, tmp2);
    ab.0[0u32 as usize] = c.1[0u32 as usize];
    ab.0[1u32 as usize] = c.1[1u32 as usize];
    ab.0[2u32 as usize] = c.1[2u32 as usize];
    ab.0[3u32 as usize] = c.1[3u32 as usize];
    ab.0[4u32 as usize] = c.1[4u32 as usize];
    crate::hacl::bignum25519_51::fsub(c.1, dc.0, c.1);
    crate::hacl::bignum25519_51::fmul1(d.0, c.1, 121665u64);
    crate::hacl::bignum25519_51::fadd(d.0, d.0, dc.0);
    crate::hacl::impl::curve25519::field51::fmul2(z2.0, dc.1, ab.1, tmp2)
}

fn montgomery_ladder(out: &mut [u64], key: &mut [u8], init: &mut [u64]) -> ()
{
    let mut tmp2: [crate::fstar::uint128::uint128; 10] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 10u32 as usize];
    let mut p01_tmp1_swap: [u64; 41] = [0u64; 41u32 as usize];
    let p0: (&mut [u64], &mut [u64]) = (&mut p01_tmp1_swap).split_at_mut(0usize);
    let p01: (&mut [u64], &mut [u64]) = p0.1.split_at_mut(0usize);
    let p03: (&mut [u64], &mut [u64]) = p01.1.split_at_mut(0usize);
    let p11: (&mut [u64], &mut [u64]) = p03.1.split_at_mut(10usize);
    (p11.1[0u32 as usize..0u32 as usize + 10u32 as usize]).copy_from_slice(
        &init[0u32 as usize..0u32 as usize + 10u32 as usize]
    );
    let x0: (&mut [u64], &mut [u64]) = p11.0.split_at_mut(0usize);
    let z0: (&mut [u64], &mut [u64]) = x0.1.split_at_mut(5usize);
    z0.0[0u32 as usize] = 1u64;
    z0.0[1u32 as usize] = 0u64;
    z0.0[2u32 as usize] = 0u64;
    z0.0[3u32 as usize] = 0u64;
    z0.0[4u32 as usize] = 0u64;
    z0.1[0u32 as usize] = 0u64;
    z0.1[1u32 as usize] = 0u64;
    z0.1[2u32 as usize] = 0u64;
    z0.1[3u32 as usize] = 0u64;
    z0.1[4u32 as usize] = 0u64;
    let p01_tmp1: (&mut [u64], &mut [u64]) = p01.1.split_at_mut(0usize);
    let p01_tmp11: (&mut [u64], &mut [u64]) = p01_tmp1.1.split_at_mut(0usize);
    let nq1: (&mut [u64], &mut [u64]) = p01_tmp11.1.split_at_mut(0usize);
    let nq_p11: (&mut [u64], &mut [u64]) = nq1.1.split_at_mut(10usize);
    let swap: (&mut [u64], &mut [u64]) = nq_p11.1.split_at_mut(30usize);
    crate::hacl::bignum25519_51::cswap2(1u64, nq_p11.0, swap.0);
    point_add_and_double(init, nq1.0, &mut tmp2);
    swap.1[0u32 as usize] = 1u64;
    for i in 0u32..251u32
    {
        let p01_tmp12: (&mut [u64], &mut [u64]) = nq_p11.0.split_at_mut(0usize);
        let swap1: (&mut [u64], &mut [u64]) = swap.1.split_at_mut(0usize);
        let nq2: (&mut [u64], &mut [u64]) = p01_tmp12.1.split_at_mut(0usize);
        let nq_p12: (&mut [u64], &mut [u64]) = nq2.1.split_at_mut(10usize);
        let bit: u64 =
            ((key[253u32.wrapping_sub(i).wrapping_div(8u32) as usize]).wrapping_shr(
                253u32.wrapping_sub(i).wrapping_rem(8u32)
            )
            &
            1u8)
            as
            u64;
        let sw: u64 = swap1.1[0u32 as usize] ^ bit;
        crate::hacl::bignum25519_51::cswap2(sw, nq_p12.0, nq_p12.1);
        point_add_and_double(init, nq_p12.0, &mut tmp2);
        swap1.1[0u32 as usize] = bit
    };
    let sw: u64 = swap.1[0u32 as usize];
    crate::hacl::bignum25519_51::cswap2(sw, nq_p11.0, swap.0);
    let nq10: (&mut [u64], &mut [u64]) = p01_tmp11.0.split_at_mut(0usize);
    let tmp1: (&mut [u64], &mut [u64]) = nq10.1.split_at_mut(20usize);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    (out[0u32 as usize..0u32 as usize + 10u32 as usize]).copy_from_slice(
        &p01.0[0u32 as usize..0u32 as usize + 10u32 as usize]
    )
}

pub fn fsquare_times(
    o: &mut [u64],
    inp: &mut [u64],
    tmp: &mut [crate::fstar::uint128::uint128],
    n: u32
) ->
    ()
{
    crate::hacl::impl::curve25519::field51::fsqr(o, inp, tmp);
    for i in 0u32..n.wrapping_sub(1u32) { crate::hacl::impl::curve25519::field51::fsqr(o, o, tmp) }
}

pub fn finv(o: &mut [u64], i: &mut [u64], tmp: &mut [crate::fstar::uint128::uint128]) -> ()
{
    let mut t1: [u64; 20] = [0u64; 20u32 as usize];
    let a1: (&mut [u64], &mut [u64]) = (&mut t1).split_at_mut(0usize);
    let b1: (&mut [u64], &mut [u64]) = a1.1.split_at_mut(5usize);
    let t01: (&mut [u64], &mut [u64]) = b1.1.split_at_mut(10usize);
    let tmp1: (&mut [crate::fstar::uint128::uint128], &mut [crate::fstar::uint128::uint128]) =
        tmp.split_at_mut(0usize);
    fsquare_times(b1.0, i, tmp1.1, 1u32);
    fsquare_times(t01.1, b1.0, tmp1.1, 2u32);
    crate::hacl::impl::curve25519::field51::fmul(t01.0, t01.1, i, tmp1.1);
    crate::hacl::impl::curve25519::field51::fmul(b1.0, t01.0, b1.0, tmp1.1);
    fsquare_times(t01.1, b1.0, tmp1.1, 1u32);
    crate::hacl::impl::curve25519::field51::fmul(t01.0, t01.1, t01.0, tmp1.1);
    fsquare_times(t01.1, t01.0, tmp1.1, 5u32);
    crate::hacl::impl::curve25519::field51::fmul(t01.0, t01.1, t01.0, tmp1.1);
    let b10: (&mut [u64], &mut [u64]) = t01.0.split_at_mut(0usize);
    let c1: (&mut [u64], &mut [u64]) = b10.1.split_at_mut(5usize);
    let t010: (&mut [u64], &mut [u64]) = t01.1.split_at_mut(0usize);
    let tmp10: (&mut [crate::fstar::uint128::uint128], &mut [crate::fstar::uint128::uint128]) =
        tmp1.1.split_at_mut(0usize);
    fsquare_times(t010.1, c1.0, tmp10.1, 10u32);
    crate::hacl::impl::curve25519::field51::fmul(c1.1, t010.1, c1.0, tmp10.0);
    fsquare_times(t010.1, c1.1, tmp10.1, 20u32);
    crate::hacl::impl::curve25519::field51::fmul(t010.1, t010.1, c1.1, tmp10.0);
    fsquare_times(t010.1, t010.1, tmp10.1, 10u32);
    crate::hacl::impl::curve25519::field51::fmul(c1.0, t010.1, c1.0, tmp10.0);
    fsquare_times(t010.1, c1.0, tmp10.1, 50u32);
    crate::hacl::impl::curve25519::field51::fmul(c1.1, t010.1, c1.0, tmp10.0);
    let b11: (&mut [u64], &mut [u64]) = c1.0.split_at_mut(0usize);
    let c10: (&mut [u64], &mut [u64]) = c1.1.split_at_mut(0usize);
    let t011: (&mut [u64], &mut [u64]) = t010.1.split_at_mut(0usize);
    let tmp11: (&mut [crate::fstar::uint128::uint128], &mut [crate::fstar::uint128::uint128]) =
        tmp10.1.split_at_mut(0usize);
    fsquare_times(t011.1, c10.1, tmp11.1, 100u32);
    crate::hacl::impl::curve25519::field51::fmul(t011.1, t011.1, c10.1, tmp10.0);
    fsquare_times(t011.1, t011.1, tmp11.1, 50u32);
    crate::hacl::impl::curve25519::field51::fmul(t011.1, t011.1, b11.1, tmp10.0);
    fsquare_times(t011.1, t011.1, tmp11.1, 5u32);
    let a: (&mut [u64], &mut [u64]) = b1.0.split_at_mut(0usize);
    let t0: (&mut [u64], &mut [u64]) = t011.1.split_at_mut(0usize);
    crate::hacl::impl::curve25519::field51::fmul(o, t0.1, a.1, tmp10.0)
}

fn encode_point(o: &mut [u8], i: &mut [u64]) -> ()
{
    let x: (&mut [u64], &mut [u64]) = i.split_at_mut(0usize);
    let z: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
    let mut tmp: [u64; 5] = [0u64; 5u32 as usize];
    let mut u64s: [u64; 4] = [0u64; 4u32 as usize];
    let mut tmp_w: [crate::fstar::uint128::uint128; 10] =
        [crate::fstar::uint128::uint64_to_uint128(0u64); 10u32 as usize];
    finv(&mut tmp, z.1, &mut tmp_w);
    crate::hacl::impl::curve25519::field51::fmul(&mut tmp, &mut tmp, z.0, &mut tmp_w);
    crate::hacl::bignum25519_51::store_felem(&mut u64s, &mut tmp);
    for i0 in 0u32..4u32
    {
        crate::lowstar::endianness::store64_le(
            &mut o[i0.wrapping_mul(8u32) as usize..],
            (&mut u64s)[i0 as usize]
        )
    }
}

pub fn scalarmult(out: &mut [u8], priv: &mut [u8], pub: &mut [u8]) -> ()
{
    let mut init: [u64; 10] = [0u64; 10u32 as usize];
    let mut tmp: [u64; 4] = [0u64; 4u32 as usize];
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            pub.split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        os.1[i as usize] = x
    };
    let tmp3: u64 = (&mut tmp)[3u32 as usize];
    (&mut tmp)[3u32 as usize] = tmp3 & 0x7fffffffffffffffu64;
    let x: (&mut [u64], &mut [u64]) = (&mut init).split_at_mut(0usize);
    let z: (&mut [u64], &mut [u64]) = x.1.split_at_mut(5usize);
    z.1[0u32 as usize] = 1u64;
    z.1[1u32 as usize] = 0u64;
    z.1[2u32 as usize] = 0u64;
    z.1[3u32 as usize] = 0u64;
    z.1[4u32 as usize] = 0u64;
    let f0l: u64 = (&mut tmp)[0u32 as usize] & 0x7ffffffffffffu64;
    let f0h: u64 = ((&mut tmp)[0u32 as usize]).wrapping_shr(51u32);
    let f1l: u64 = ((&mut tmp)[1u32 as usize] & 0x3fffffffffu64).wrapping_shl(13u32);
    let f1h: u64 = ((&mut tmp)[1u32 as usize]).wrapping_shr(38u32);
    let f2l: u64 = ((&mut tmp)[2u32 as usize] & 0x1ffffffu64).wrapping_shl(26u32);
    let f2h: u64 = ((&mut tmp)[2u32 as usize]).wrapping_shr(25u32);
    let f3l: u64 = ((&mut tmp)[3u32 as usize] & 0xfffu64).wrapping_shl(39u32);
    let f3h: u64 = ((&mut tmp)[3u32 as usize]).wrapping_shr(12u32);
    z.0[0u32 as usize] = f0l;
    z.0[1u32 as usize] = f0h | f1l;
    z.0[2u32 as usize] = f1h | f2l;
    z.0[3u32 as usize] = f2h | f3l;
    z.0[4u32 as usize] = f3h;
    montgomery_ladder(z.0, priv, z.0);
    encode_point(out, z.0)
}

pub fn secret_to_public(pub: &mut [u8], priv: &mut [u8]) -> ()
{
    let mut basepoint: [u8; 32] = [0u8; 32u32 as usize];
    for i in 0u32..32u32
    {
        let os: (&mut [u8], &mut [u8]) = (&mut basepoint).split_at_mut(0usize);
        let x: u8 = (&g25519)[i as usize];
        os.1[i as usize] = x
    };
    scalarmult(pub, priv, &mut basepoint)
}

pub fn ecdh(out: &mut [u8], priv: &mut [u8], pub: &mut [u8]) -> bool
{
    let mut zeros: [u8; 32] = [0u8; 32u32 as usize];
    scalarmult(out, priv, pub);
    let mut res: u8 = 255u8;
    for i in 0u32..32u32
    {
        let uu____0: u8 = crate::fstar::uint8::eq_mask(out[i as usize], (&mut zeros)[i as usize]);
        res = uu____0 & res
    };
    let z: u8 = res;
    let r: bool = z == 255u8;
    ! r
}