#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn ffdhe_len(a: crate::hacl::spec::ffdhe_alg) -> u32
{
    match a
    {
        crate::hacl::spec::ffdhe_alg::FFDHE2048 => 256u32,
        crate::hacl::spec::ffdhe_alg::FFDHE3072 => 384u32,
        crate::hacl::spec::ffdhe_alg::FFDHE4096 => 512u32,
        crate::hacl::spec::ffdhe_alg::FFDHE6144 => 768u32,
        crate::hacl::spec::ffdhe_alg::FFDHE8192 => 1024u32,
        _ => panic!("Precondition of the function most likely violated")
    }
}

#[inline] fn ffdhe_precomp_p(a: crate::hacl::spec::ffdhe_alg, p_r2_n: &mut [u64]) -> ()
{
    let nLen: u32 = (ffdhe_len(a)).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let p_n: (&mut [u64], &mut [u64]) = p_r2_n.split_at_mut(0usize);
    let r2_n: (&mut [u64], &mut [u64]) = p_n.1.split_at_mut(nLen as usize);
    let sw: u32 =
        match a
        {
            crate::hacl::spec::ffdhe_alg::FFDHE2048 => 256u32,
            crate::hacl::spec::ffdhe_alg::FFDHE3072 => 384u32,
            crate::hacl::spec::ffdhe_alg::FFDHE4096 => 512u32,
            crate::hacl::spec::ffdhe_alg::FFDHE6144 => 768u32,
            crate::hacl::spec::ffdhe_alg::FFDHE8192 => 1024u32,
            _ => panic!("Precondition of the function most likely violated")
        };
    let mut p_s: Vec<u8> = vec![0u8; sw as usize];
    let p: &[u8] =
        match a
        {
            crate::hacl::spec::ffdhe_alg::FFDHE2048 =>
              &crate::hacl::impl_ffdhe_constants::ffdhe_p2048,
            crate::hacl::spec::ffdhe_alg::FFDHE3072 =>
              &crate::hacl::impl_ffdhe_constants::ffdhe_p3072,
            crate::hacl::spec::ffdhe_alg::FFDHE4096 =>
              &crate::hacl::impl_ffdhe_constants::ffdhe_p4096,
            crate::hacl::spec::ffdhe_alg::FFDHE6144 =>
              &crate::hacl::impl_ffdhe_constants::ffdhe_p6144,
            crate::hacl::spec::ffdhe_alg::FFDHE8192 =>
              &crate::hacl::impl_ffdhe_constants::ffdhe_p8192,
            _ => panic!("Precondition of the function most likely violated")
        };
    let len: u32 = ffdhe_len(a);
    for i in 0u32..len
    {
        let x: u8 = p[i as usize];
        let os: (&mut [u8], &mut [u8]) = (&mut p_s).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    crate::hacl::bignum_base::bn_from_bytes_be_uint64(ffdhe_len(a), &mut p_s, r2_n.0);
    crate::hacl::bignum::bn_precomp_r2_mod_n_u64(
        (ffdhe_len(a)).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32),
        8u32.wrapping_mul(ffdhe_len(a)).wrapping_sub(1u32),
        r2_n.0,
        r2_n.1
    )
}

#[inline] fn ffdhe_check_pk(a: crate::hacl::spec::ffdhe_alg, pk_n: &mut [u64], p_n: &mut [u64]) ->
    u64
{
    let nLen: u32 = (ffdhe_len(a)).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let mut p_n1: Vec<u64> = vec![0u64; nLen as usize];
    let c0: u64 =
        crate::lib::inttypes_intrinsics::sub_borrow_u64(
            0u64,
            p_n[0usize],
            1u64,
            &mut (&mut p_n1)[0usize..]
        );
    if 1u32 < nLen
    {
        let a1: (&mut [u64], &mut [u64]) = p_n.split_at_mut(1usize);
        let res1: (&mut [u64], &mut [u64]) = (&mut p_n1).split_at_mut(1usize);
        let mut c: [u64; 1] = [c0; 1usize];
        for i in 0u32..nLen.wrapping_sub(1u32).wrapping_div(4u32)
        {
            let t1: u64 = a1.1[4u32.wrapping_mul(i) as usize];
            let res_i: (&mut [u64], &mut [u64]) =
                res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, 0u64, res_i.1);
            let t10: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64(
                    (&mut c)[0usize],
                    t10,
                    0u64,
                    res_i0.1
                );
            let t11: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64(
                    (&mut c)[0usize],
                    t11,
                    0u64,
                    res_i1.1
                );
            let t12: u64 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64(
                    (&mut c)[0usize],
                    t12,
                    0u64,
                    res_i2.1
                )
        };
        for
        i
        in
        nLen.wrapping_sub(1u32).wrapping_div(4u32).wrapping_mul(4u32)..nLen.wrapping_sub(1u32)
        {
            let t1: u64 = a1.1[i as usize];
            let res_i: (&mut [u64], &mut [u64]) = res1.1.split_at_mut(i as usize);
            (&mut c)[0usize] =
                crate::lib::inttypes_intrinsics::sub_borrow_u64((&mut c)[0usize], t1, 0u64, res_i.1)
        };
        let c1: u64 = (&mut c)[0usize];
        crate::lowstar::ignore::ignore::<u64>(c1)
    }
    else
    { crate::lowstar::ignore::ignore::<u64>(c0) };
    let mut b2: Vec<u64> = vec![0u64; nLen as usize];
    let i: u32 = 0u32;
    let j: u32 = 0u32;
    (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u64.wrapping_shl(j);
    let mut acc: [u64; 1] = [0u64; 1usize];
    for i0 in 0u32..nLen
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut b2)[i0 as usize], pk_n[i0 as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut b2)[i0 as usize], pk_n[i0 as usize]);
        (&mut acc)[0usize] =
            beq & (&mut acc)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let res: u64 = (&mut acc)[0usize];
    let m0: u64 = res;
    let mut acc0: [u64; 1] = [0u64; 1usize];
    for i0 in 0u32..nLen
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(pk_n[i0 as usize], (&mut p_n1)[i0 as usize]);
        let blt: u64 =
            ! crate::fstar::uint64::gte_mask(pk_n[i0 as usize], (&mut p_n1)[i0 as usize]);
        (&mut acc0)[0usize] =
            beq & (&mut acc0)[0usize] | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = (&mut acc0)[0usize];
    m0 & m1
}

#[inline] fn ffdhe_compute_exp(
    a: crate::hacl::spec::ffdhe_alg,
    p_r2_n: &mut [u64],
    sk_n: &mut [u64],
    b_n: &mut [u64],
    res: &mut [u8]
) ->
    ()
{
    let nLen: u32 = (ffdhe_len(a)).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let p_n: (&mut [u64], &mut [u64]) = p_r2_n.split_at_mut(0usize);
    let r2_n: (&mut [u64], &mut [u64]) = p_n.1.split_at_mut(nLen as usize);
    let mut res_n: Vec<u64> = vec![0u64; nLen as usize];
    let mu: u64 = crate::hacl::bignum::mod_inv_uint64(r2_n.0[0usize]);
    crate::hacl::bignum::bn_mod_exp_consttime_precomp_u64(
        (ffdhe_len(a)).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32),
        r2_n.0,
        mu,
        r2_n.1,
        b_n,
        64u32.wrapping_mul(nLen),
        sk_n,
        &mut res_n
    );
    crate::hacl::bignum_base::bn_to_bytes_be_uint64(ffdhe_len(a), &mut res_n, res)
}

pub fn ffdhe_len0(a: crate::hacl::spec::ffdhe_alg) -> u32 { ffdhe_len(a) }

pub fn new_ffdhe_precomp_p(a: crate::hacl::spec::ffdhe_alg) -> Vec<u64>
{
    let nLen: u32 = (ffdhe_len(a)).wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let mut res: Vec<u64> = vec![0u64; nLen.wrapping_add(nLen) as usize];
    if false
    { res }
    else
    {
        let res1: &mut [u64] = &mut res;
        let res2: &mut [u64] = res1;
        ffdhe_precomp_p(a, res2);
        res2.to_vec()
    }
}

pub fn ffdhe_secret_to_public_precomp(
    a: crate::hacl::spec::ffdhe_alg,
    p_r2_n: &mut [u64],
    sk: &mut [u8],
    pk: &mut [u8]
) ->
    ()
{
    let len: u32 = ffdhe_len(a);
    let nLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let mut g_n: Vec<u64> = vec![0u64; nLen as usize];
    let mut g: [u8; 1] = [0u8; 1usize];
    for i in 0u32..1u32
    {
        let x: u8 = (&crate::hacl::impl_ffdhe_constants::ffdhe_g2)[i as usize];
        let os: (&mut [u8], &mut [u8]) = (&mut g).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    crate::hacl::bignum_base::bn_from_bytes_be_uint64(1u32, &mut g, &mut (&mut g_n)[0usize..]);
    let mut sk_n: Vec<u64> = vec![0u64; nLen as usize];
    crate::hacl::bignum_base::bn_from_bytes_be_uint64(len, sk, &mut sk_n);
    ffdhe_compute_exp(a, p_r2_n, &mut sk_n, &mut g_n, pk)
}

pub fn ffdhe_secret_to_public(a: crate::hacl::spec::ffdhe_alg, sk: &mut [u8], pk: &mut [u8]) ->
    ()
{
    let len: u32 = ffdhe_len(a);
    let nLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let mut p_r2_n: Vec<u64> = vec![0u64; nLen.wrapping_add(nLen) as usize];
    ffdhe_precomp_p(a, &mut p_r2_n);
    ffdhe_secret_to_public_precomp(a, &mut p_r2_n, sk, pk)
}

pub fn ffdhe_shared_secret_precomp(
    a: crate::hacl::spec::ffdhe_alg,
    p_r2_n: &mut [u64],
    sk: &mut [u8],
    pk: &mut [u8],
    ss: &mut [u8]
) ->
    u64
{
    let len: u32 = ffdhe_len(a);
    let nLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let p_n: (&mut [u64], &mut [u64]) = p_r2_n.split_at_mut(0usize);
    let mut sk_n: Vec<u64> = vec![0u64; nLen as usize];
    let mut pk_n: Vec<u64> = vec![0u64; nLen as usize];
    crate::hacl::bignum_base::bn_from_bytes_be_uint64(len, sk, &mut sk_n);
    crate::hacl::bignum_base::bn_from_bytes_be_uint64(len, pk, &mut pk_n);
    let m: u64 = ffdhe_check_pk(a, &mut pk_n, p_n.1);
    if m == 0xFFFFFFFFFFFFFFFFu64 { ffdhe_compute_exp(a, p_r2_n, &mut sk_n, &mut pk_n, ss) };
    m
}

pub fn ffdhe_shared_secret(
    a: crate::hacl::spec::ffdhe_alg,
    sk: &mut [u8],
    pk: &mut [u8],
    ss: &mut [u8]
) ->
    u64
{
    let len: u32 = ffdhe_len(a);
    let nLen: u32 = len.wrapping_sub(1u32).wrapping_div(8u32).wrapping_add(1u32);
    let mut p_n: Vec<u64> = vec![0u64; nLen.wrapping_add(nLen) as usize];
    ffdhe_precomp_p(a, &mut p_n);
    let m: u64 = ffdhe_shared_secret_precomp(a, &mut p_n, sk, pk, ss);
    m
}
