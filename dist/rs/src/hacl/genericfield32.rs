#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

pub type pbn_mont_ctx_u32 <'a> = &'a mut [crate::hacl::bignum::bn_mont_ctx_u32];

pub fn field_modulus_check(len: u32, n: &mut [u32]) -> bool
{
    let m: u32 = crate::hacl::bignum::bn_check_modulus_u32(len, n);
    m == 0xFFFFFFFFu32
}

pub fn field_init(len: u32, n: &mut [u32]) -> Vec<crate::hacl::bignum::bn_mont_ctx_u32>
{
    let mut r2: Vec<u32> = vec![0u32; len as usize];
    let mut n1: Vec<u32> = vec![0u32; len as usize];
    let r21: &mut [u32] = &mut r2;
    let n11: &mut [u32] = &mut n1;
    (n11[0usize..len as usize]).copy_from_slice(&n[0usize..len as usize]);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    crate::hacl::bignum::bn_precomp_r2_mod_n_u32(len, nBits, n, r21);
    let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
    let mut res: crate::hacl::bignum::bn_mont_ctx_u32 =
        crate::hacl::bignum::bn_mont_ctx_u32 { len: len, n: n11.to_vec(), mu: mu, r2: r21.to_vec() };
    let mut buf: Vec<crate::hacl::bignum::bn_mont_ctx_u32> =
        {
            let mut tmp: Vec<crate::hacl::bignum::bn_mont_ctx_u32> = Vec::new();
            tmp.push(res);
            tmp
        };
    buf
}

pub fn field_get_len(k: &mut [crate::hacl::bignum::bn_mont_ctx_u32]) -> u32 { (k[0usize]).len }

pub fn to_field(k: &mut [crate::hacl::bignum::bn_mont_ctx_u32], a: &mut [u32], aM: &mut [u32]) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    crate::hacl::bignum::bn_to_mont_u32(
        len1,
        &mut (*uu____0).n,
        (*uu____0).mu,
        &mut (*uu____0).r2,
        a,
        aM
    )
}

pub fn from_field(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    a: &mut [u32]
) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    crate::hacl::bignum::bn_from_mont_u32(len1, &mut (*uu____0).n, (*uu____0).mu, aM, a)
}

pub fn add(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    bM: &mut [u32],
    cM: &mut [u32]
) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    let mut a_copy: Vec<u32> = vec![0u32; len1 as usize];
    let mut b_copy: Vec<u32> = vec![0u32; len1 as usize];
    ((&mut a_copy)[0usize..len1 as usize]).copy_from_slice(&aM[0usize..len1 as usize]);
    ((&mut b_copy)[0usize..len1 as usize]).copy_from_slice(&bM[0usize..len1 as usize]);
    crate::hacl::bignum::bn_add_mod_n_u32(len1, &mut (*uu____0).n, &mut a_copy, &mut b_copy, cM)
}

pub fn sub(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    bM: &mut [u32],
    cM: &mut [u32]
) ->
    ()
{
    let len1: u32 = field_get_len(k);
    crate::hacl::bignum::bn_sub_mod_n_u32(len1, &mut (k[0usize]).n, aM, bM, cM)
}

pub fn mul(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    bM: &mut [u32],
    cM: &mut [u32]
) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    crate::hacl::bignum::bn_mont_mul_u32(len1, &mut (*uu____0).n, (*uu____0).mu, aM, bM, cM)
}

pub fn sqr(k: &mut [crate::hacl::bignum::bn_mont_ctx_u32], aM: &mut [u32], cM: &mut [u32]) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    crate::hacl::bignum::bn_mont_sqr_u32(len1, &mut (*uu____0).n, (*uu____0).mu, aM, cM)
}

pub fn one(k: &mut [crate::hacl::bignum::bn_mont_ctx_u32], oneM: &mut [u32]) -> ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    crate::hacl::bignum::bn_from_mont_u32(
        len1,
        &mut (*uu____0).n,
        (*uu____0).mu,
        &mut (*uu____0).r2,
        oneM
    )
}

pub fn exp_consttime(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    let mut aMc: Vec<u32> = vec![0u32; (*uu____0).len as usize];
    ((&mut aMc)[0usize..(*uu____0).len as usize]).copy_from_slice(
        &aM[0usize..(*uu____0).len as usize]
    );
    if bBits < 200u32
    {
        let mut ctx: Vec<u32> = vec![0u32; len1.wrapping_add(len1) as usize];
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).n)[0usize..len1 as usize]
        );
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).r2)[0usize..len1 as usize]
        );
        let mut sw: [u32; 1] = [0u32; 1usize];
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(len1 as usize);
        crate::hacl::bignum::bn_from_mont_u32(len1, ctx_r2.0, (*uu____0).mu, ctx_r2.1, resM);
        for i in 0u32..bBits
        {
            let i1: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_div(32u32);
            let j: u32 = bBits.wrapping_sub(i).wrapping_sub(1u32).wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            let sw1: u32 = bit ^ (&mut sw)[0usize];
            for i0 in 0u32..len1
            {
                let dummy: u32 =
                    0u32.wrapping_sub(sw1) & (resM[i0 as usize] ^ (&mut aMc)[i0 as usize]);
                resM[i0 as usize] = resM[i0 as usize] ^ dummy;
                (&mut aMc)[i0 as usize] = (&mut aMc)[i0 as usize] ^ dummy
            };
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            crate::hacl::bignum::bn_mont_mul_u32(
                len1,
                ctx_n0.1,
                (*uu____0).mu,
                &mut aMc,
                resM,
                &mut aMc
            );
            let ctx_n1: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(0usize);
            crate::hacl::bignum::bn_mont_sqr_u32(len1, ctx_n1.1, (*uu____0).mu, resM, resM);
            (&mut sw)[0usize] = bit
        };
        let sw0: u32 = (&mut sw)[0usize];
        for i in 0u32..len1
        {
            let dummy: u32 = 0u32.wrapping_sub(sw0) & (resM[i as usize] ^ (&mut aMc)[i as usize]);
            resM[i as usize] = resM[i as usize] ^ dummy;
            (&mut aMc)[i as usize] = (&mut aMc)[i as usize] ^ dummy
        }
    }
    else
    {
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
        let mut ctx: Vec<u32> = vec![0u32; len1.wrapping_add(len1) as usize];
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).n)[0usize..len1 as usize]
        );
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).r2)[0usize..len1 as usize]
        );
        let mut table: Vec<u32> = vec![0u32; 16u32.wrapping_mul(len1) as usize];
        let mut tmp: Vec<u32> = vec![0u32; len1 as usize];
        let t0: (&mut [u32], &mut [u32]) = (&mut table).split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(len1 as usize);
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(len1 as usize);
        crate::hacl::bignum::bn_from_mont_u32(len1, ctx_r2.0, (*uu____0).mu, ctx_r2.1, t1.0);
        (t1.1[0usize..len1 as usize]).copy_from_slice(&(&mut aMc)[0usize..len1 as usize]);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut table);
        for i in 0u32..7u32
        {
            let t11: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(len1) as usize);
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            crate::hacl::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, (*uu____0).mu, t11.1, &mut tmp);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(len1)
            as
            usize
            +
            len1 as usize]).copy_from_slice(&(&mut tmp)[0usize..len1 as usize]);
            let t2: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize
                );
            let ctx_n1: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(0usize);
            crate::hacl::bignum::bn_mont_mul_u32(
                len1,
                ctx_n1.1,
                (*uu____0).mu,
                &mut aMc,
                t2.1,
                &mut tmp
            );
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(len1)
            as
            usize
            +
            len1 as usize]).copy_from_slice(&(&mut tmp)[0usize..len1 as usize])
        };
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            (resM[0usize..len1 as usize]).copy_from_slice(
                &(&mut (&mut table)[0u32.wrapping_mul(len1) as usize..] as &mut [u32])[0usize..len1
                as
                usize]
            );
            for i0 in 0u32..15u32
            {
                let c: u32 = crate::fstar::uint32::eq_mask(bits_c, i0.wrapping_add(1u32));
                let res_j: (&[u32], &[u32]) =
                    (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(len1) as usize);
                for i1 in 0u32..len1
                {
                    let x: u32 = c & res_j.1[i1 as usize] | ! c & resM[i1 as usize];
                    let os: (&mut [u32], &mut [u32]) = resM.split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            }
        }
        else
        {
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            let ctx_r20: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(len1 as usize);
            crate::hacl::bignum::bn_from_mont_u32(len1, ctx_r20.0, (*uu____0).mu, ctx_r20.1, resM)
        };
        let mut tmp0: Vec<u32> = vec![0u32; len1 as usize];
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            for _i in 0u32..4u32
            {
                let ctx_n0: (&mut [u32], &mut [u32]) =
                    ctx_r2.1.split_at_mut(0usize - len1 as usize);
                crate::hacl::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, (*uu____0).mu, resM, resM)
            };
            let k2: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, k2, 4u32);
            crate::lowstar::ignore::ignore::<&[u32]>(&mut table);
            ((&mut tmp0)[0usize..len1 as usize]).copy_from_slice(
                &(&mut (&mut table)[0u32.wrapping_mul(len1) as usize..] as &mut [u32])[0usize..len1
                as
                usize]
            );
            for i0 in 0u32..15u32
            {
                let c: u32 = crate::fstar::uint32::eq_mask(bits_l, i0.wrapping_add(1u32));
                let res_j: (&[u32], &[u32]) =
                    (&mut table).split_at(i0.wrapping_add(1u32).wrapping_mul(len1) as usize);
                for i1 in 0u32..len1
                {
                    let x: u32 = c & res_j.1[i1 as usize] | ! c & (&mut tmp0)[i1 as usize];
                    let os: (&mut [u32], &mut [u32]) = (&mut tmp0).split_at_mut(0usize);
                    os.1[i1 as usize] = x
                }
            };
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            crate::hacl::bignum::bn_mont_mul_u32(
                len1,
                ctx_n0.1,
                (*uu____0).mu,
                resM,
                &mut tmp0,
                resM
            )
        }
    }
}

pub fn exp_vartime(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let len1: u32 = field_get_len(k);
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    let mut aMc: Vec<u32> = vec![0u32; (*uu____0).len as usize];
    ((&mut aMc)[0usize..(*uu____0).len as usize]).copy_from_slice(
        &aM[0usize..(*uu____0).len as usize]
    );
    if bBits < 200u32
    {
        let mut ctx: Vec<u32> = vec![0u32; len1.wrapping_add(len1) as usize];
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).n)[0usize..len1 as usize]
        );
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).r2)[0usize..len1 as usize]
        );
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(len1 as usize);
        crate::hacl::bignum::bn_from_mont_u32(len1, ctx_r2.0, (*uu____0).mu, ctx_r2.1, resM);
        for i in 0u32..bBits
        {
            let i1: u32 = i.wrapping_div(32u32);
            let j: u32 = i.wrapping_rem(32u32);
            let tmp: u32 = b[i1 as usize];
            let bit: u32 = tmp.wrapping_shr(j) & 1u32;
            if ! (bit == 0u32)
            {
                let ctx_n0: (&mut [u32], &mut [u32]) =
                    ctx_r2.1.split_at_mut(0usize - len1 as usize);
                crate::hacl::bignum::bn_mont_mul_u32(
                    len1,
                    ctx_n0.1,
                    (*uu____0).mu,
                    resM,
                    &mut aMc,
                    resM
                )
            };
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            crate::hacl::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, (*uu____0).mu, &mut aMc, &mut aMc)
        }
    }
    else
    {
        let bLen: u32 =
            if bBits == 0u32
            { 1u32 }
            else
            { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
        let mut ctx: Vec<u32> = vec![0u32; len1.wrapping_add(len1) as usize];
        ((&mut ctx)[0usize..len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).n)[0usize..len1 as usize]
        );
        ((&mut ctx)[len1 as usize..len1 as usize + len1 as usize]).copy_from_slice(
            &(&mut (*uu____0).r2)[0usize..len1 as usize]
        );
        let mut table: Vec<u32> = vec![0u32; 16u32.wrapping_mul(len1) as usize];
        let mut tmp: Vec<u32> = vec![0u32; len1 as usize];
        let t0: (&mut [u32], &mut [u32]) = (&mut table).split_at_mut(0usize);
        let t1: (&mut [u32], &mut [u32]) = t0.1.split_at_mut(len1 as usize);
        let ctx_n: (&mut [u32], &mut [u32]) = (&mut ctx).split_at_mut(0usize);
        let ctx_r2: (&mut [u32], &mut [u32]) = ctx_n.1.split_at_mut(len1 as usize);
        crate::hacl::bignum::bn_from_mont_u32(len1, ctx_r2.0, (*uu____0).mu, ctx_r2.1, t1.0);
        (t1.1[0usize..len1 as usize]).copy_from_slice(&(&mut aMc)[0usize..len1 as usize]);
        crate::lowstar::ignore::ignore::<&mut [u32]>(&mut table);
        for i in 0u32..7u32
        {
            let t11: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(i.wrapping_add(1u32).wrapping_mul(len1) as usize);
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            crate::hacl::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, (*uu____0).mu, t11.1, &mut tmp);
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(2u32).wrapping_mul(len1)
            as
            usize
            +
            len1 as usize]).copy_from_slice(&(&mut tmp)[0usize..len1 as usize]);
            let t2: (&mut [u32], &mut [u32]) =
                (&mut table).split_at_mut(
                    2u32.wrapping_mul(i).wrapping_add(2u32).wrapping_mul(len1) as usize
                );
            let ctx_n1: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(0usize);
            crate::hacl::bignum::bn_mont_mul_u32(
                len1,
                ctx_n1.1,
                (*uu____0).mu,
                &mut aMc,
                t2.1,
                &mut tmp
            );
            ((&mut table)[2u32.wrapping_mul(i).wrapping_add(3u32).wrapping_mul(len1) as usize..2u32.wrapping_mul(
                i
            ).wrapping_add(3u32).wrapping_mul(len1)
            as
            usize
            +
            len1 as usize]).copy_from_slice(&(&mut tmp)[0usize..len1 as usize])
        };
        if bBits.wrapping_rem(4u32) != 0u32
        {
            let i: u32 = bBits.wrapping_div(4u32).wrapping_mul(4u32);
            let bits_c: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, i, 4u32);
            let bits_l32: u32 = bits_c;
            let a_bits_l: (&[u32], &[u32]) =
                (&mut table).split_at(bits_l32.wrapping_mul(len1) as usize);
            (resM[0usize..len1 as usize]).copy_from_slice(&a_bits_l.1[0usize..len1 as usize])
        }
        else
        {
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            let ctx_r20: (&mut [u32], &mut [u32]) = ctx_n0.1.split_at_mut(len1 as usize);
            crate::hacl::bignum::bn_from_mont_u32(len1, ctx_r20.0, (*uu____0).mu, ctx_r20.1, resM)
        };
        let mut tmp0: Vec<u32> = vec![0u32; len1 as usize];
        for i in 0u32..bBits.wrapping_div(4u32)
        {
            for _i in 0u32..4u32
            {
                let ctx_n0: (&mut [u32], &mut [u32]) =
                    ctx_r2.1.split_at_mut(0usize - len1 as usize);
                crate::hacl::bignum::bn_mont_sqr_u32(len1, ctx_n0.1, (*uu____0).mu, resM, resM)
            };
            let k2: u32 =
                bBits.wrapping_sub(bBits.wrapping_rem(4u32)).wrapping_sub(4u32.wrapping_mul(i)).wrapping_sub(
                    4u32
                );
            let bits_l: u32 = crate::hacl::bignum_base::bn_get_bits_u32(bLen, b, k2, 4u32);
            crate::lowstar::ignore::ignore::<&[u32]>(&mut table);
            let bits_l32: u32 = bits_l;
            let a_bits_l: (&[u32], &[u32]) =
                (&mut table).split_at(bits_l32.wrapping_mul(len1) as usize);
            ((&mut tmp0)[0usize..len1 as usize]).copy_from_slice(&a_bits_l.1[0usize..len1 as usize]);
            let ctx_n0: (&mut [u32], &mut [u32]) = ctx_r2.1.split_at_mut(0usize - len1 as usize);
            crate::hacl::bignum::bn_mont_mul_u32(
                len1,
                ctx_n0.1,
                (*uu____0).mu,
                resM,
                &mut tmp0,
                resM
            )
        }
    }
}

pub fn inverse(
    k: &mut [crate::hacl::bignum::bn_mont_ctx_u32],
    aM: &mut [u32],
    aInvM: &mut [u32]
) ->
    ()
{
    let mut uu____0: &mut crate::hacl::bignum::bn_mont_ctx_u32 = &mut k[0usize];
    let len1: u32 = (*uu____0).len;
    let mut n2: Vec<u32> = vec![0u32; len1 as usize];
    let c0: u32 =
        crate::lib::inttypes_intrinsics::sub_borrow_u32(
            0u32,
            (&mut (*uu____0).n)[0usize],
            2u32,
            &mut (&mut n2)[0usize..]
        );
    let c: u32 =
        if 1u32 < len1
        {
            let a1: &mut [u32] = &mut (&mut (*uu____0).n)[1usize..];
            let res1: (&mut [u32], &mut [u32]) = (&mut n2).split_at_mut(1usize);
            let mut c: [u32; 1] = [c0; 1usize];
            for i in 0u32..len1.wrapping_sub(1u32).wrapping_div(4u32)
            {
                let t1: u32 = a1[4u32.wrapping_mul(i) as usize];
                let res_i: (&mut [u32], &mut [u32]) =
                    res1.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&mut c)[0usize],
                        t1,
                        0u32,
                        res_i.1
                    );
                ();
                let t10: u32 = a1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&mut c)[0usize],
                        t10,
                        0u32,
                        res_i0.1
                    );
                ();
                let t11: u32 = a1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&mut c)[0usize],
                        t11,
                        0u32,
                        res_i1.1
                    );
                ();
                let t12: u32 = a1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&mut c)[0usize],
                        t12,
                        0u32,
                        res_i2.1
                    );
                ();
                ();
                ()
            };
            ();
            for
            i
            in
            len1.wrapping_sub(1u32).wrapping_div(4u32).wrapping_mul(4u32)..len1.wrapping_sub(1u32)
            {
                let t1: u32 = a1[i as usize];
                let res_i: (&mut [u32], &mut [u32]) = res1.1.split_at_mut(i as usize);
                (&mut c)[0usize] =
                    crate::lib::inttypes_intrinsics::sub_borrow_u32(
                        (&mut c)[0usize],
                        t1,
                        0u32,
                        res_i.1
                    );
                ();
                ()
            };
            let c1: u32 = (&mut c)[0usize];
            c1
        }
        else
        { c0 };
    crate::lowstar::ignore::ignore::<u32>(c);
    exp_vartime(k, aM, (*uu____0).len.wrapping_mul(32u32), &mut n2, aInvM)
}
