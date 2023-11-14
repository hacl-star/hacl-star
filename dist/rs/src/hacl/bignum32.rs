pub fn add(len: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{ crate::hacl::bignum_base::bn_add_eq_len_u32(len, a, b, res) }

pub fn sub(len: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> u32
{ crate::hacl::bignum_base::bn_sub_eq_len_u32(len, a, b, res) }

pub fn add_mod(len: u32, n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{ crate::hacl::bignum::bn_add_mod_n_u32(len, n, a, b, res) }

pub fn sub_mod(len: u32, n: &mut [u32], a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{ crate::hacl::bignum::bn_sub_mod_n_u32(len, n, a, b, res) }

pub fn mul(len: u32, a: &mut [u32], b: &mut [u32], res: &mut [u32]) -> ()
{
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_mul_uint32(len, a, b, &mut tmp, res)
}

pub fn sqr(len: u32, a: &mut [u32], res: &mut [u32]) -> ()
{
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_sqr_uint32(len, a, &mut tmp, res)
}

#[inline] fn bn_slow_precomp(
    len: u32,
    n: &mut [u32],
    mu: u32,
    r2: &mut [u32],
    a: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut a_mod: Vec<u32> = vec![0u32; len as usize];
    let mut a1: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    ((&mut a1)[0usize..len.wrapping_add(len) as usize]).copy_from_slice(
        &a[0usize..len.wrapping_add(len) as usize]
    );
    let mut c0: u32 = 0u32;
    for i in 0u32..len
    {
        let qj: u32 = mu.wrapping_mul((&mut a1)[i as usize]);
        let res_j: (&mut [u32], &mut [u32]) = (&mut a1).split_at_mut(i as usize);
        let mut c: u32 = 0u32;
        for i0 in 0u32..len.wrapping_div(4u32)
        {
            let a_i: u32 = n[4u32.wrapping_mul(i0) as usize];
            let res_i: (&mut [u32], &mut [u32]) =
                res_j.1.split_at_mut(4u32.wrapping_mul(i0) as usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c, res_i.1);
            let a_i0: u32 = n[4u32.wrapping_mul(i0).wrapping_add(1u32) as usize];
            let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u32(a_i0, qj, c, res_i0.1);
            let a_i1: u32 = n[4u32.wrapping_mul(i0).wrapping_add(2u32) as usize];
            let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u32(a_i1, qj, c, res_i1.1);
            let a_i2: u32 = n[4u32.wrapping_mul(i0).wrapping_add(3u32) as usize];
            let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u32(a_i2, qj, c, res_i2.1)
        };
        for i0 in len.wrapping_div(4u32).wrapping_mul(4u32)..len
        {
            let a_i: u32 = n[i0 as usize];
            let res_i: (&mut [u32], &mut [u32]) = res_j.1.split_at_mut(i0 as usize);
            c = crate::hacl::bignum_base::mul_wide_add2_u32(a_i, qj, c, res_i.1)
        };
        let r: u32 = c;
        let c1: u32 = r;
        let resb: (&mut [u32], &mut [u32]) =
            res_j.1.split_at_mut(len.wrapping_add(i) as usize - i as usize);
        let res_j0: u32 = res_j.0[len.wrapping_add(i) as usize];
        c0 = crate::lib::inttypes_intrinsics::add_carry_u32(c0, c1, res_j0, resb.1)
    };
    ((&mut a_mod)[0usize..len.wrapping_add(len).wrapping_sub(len) as usize]).copy_from_slice(
        &(&mut (&mut a1)[len as usize..])[0usize..len.wrapping_add(len).wrapping_sub(len) as usize]
    );
    let c00: u32 = c0;
    let mut tmp: Vec<u32> = vec![0u32; len as usize];
    let c1: u32 = crate::hacl::bignum_base::bn_sub_eq_len_u32(len, &mut a_mod, n, &mut tmp);
    crate::lowstar::ignore::ignore::<u32>(c1);
    let m: u32 = 0u32.wrapping_sub(c00);
    for i in 0u32..len
    {
        let os: (&mut [u32], &mut [u32]) = (&mut a_mod).split_at_mut(0usize);
        let x: u32 = m & (&mut tmp)[i as usize] | ! m & os.1[i as usize];
        os.1[i as usize] = x
    };
    let mut c: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    let mut tmp0: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum::bn_karatsuba_mul_uint32(len, &mut a_mod, r2, &mut tmp0, &mut c);
    crate::hacl::bignum::bn_mont_reduction_u32(len, n, mu, &mut c, res)
}

pub fn mod(len: u32, n: &mut [u32], a: &mut [u32], res: &mut [u32]) -> bool
{
    let mut one: Vec<u32> = vec![0u32; len as usize];
    ((&mut one)[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: u32 = 0u32;
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = acc;
    let is_valid_m: u32 = m0 & m1;
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    {
        let mut r2: Vec<u32> = vec![0u32; len as usize];
        crate::hacl::bignum::bn_precomp_r2_mod_n_u32(len, nBits, n, &mut r2);
        let mu: u32 = crate::hacl::bignum::mod_inv_uint32(n[0usize]);
        bn_slow_precomp(len, n, mu, &mut r2, a, res)
    }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn mod_exp_vartime(
    len: u32,
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    bool
{
    let is_valid_m: u32 = crate::hacl::bignum::bn_check_mod_exp_u32(len, n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    { crate::hacl::bignum::bn_mod_exp_vartime_u32(len, nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn mod_exp_consttime(
    len: u32,
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    bool
{
    let is_valid_m: u32 = crate::hacl::bignum::bn_check_mod_exp_u32(len, n, a, bBits, b);
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    { crate::hacl::bignum::bn_mod_exp_consttime_u32(len, nBits, n, a, bBits, b, res) }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn mod_inv_prime_vartime(len: u32, n: &mut [u32], a: &mut [u32], res: &mut [u32]) -> bool
{
    let mut one: Vec<u32> = vec![0u32; len as usize];
    ((&mut one)[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]);
    (&mut one)[0usize] = 1u32;
    let bit0: u32 = n[0usize] & 1u32;
    let m0: u32 = 0u32.wrapping_sub(bit0);
    let mut acc: u32 = 0u32;
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m1: u32 = acc;
    let m00: u32 = m0 & m1;
    let mut bn_zero: Vec<u32> = vec![0u32; len as usize];
    let mut mask: u32 = 0xFFFFFFFFu32;
    for i in 0u32..len
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], (&mut bn_zero)[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u32 = mask;
    let res1: u32 = mask1;
    let m10: u32 = res1;
    let mut acc0: u32 = 0u32;
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m2: u32 = acc0;
    let is_valid_m: u32 = m00 & ! m10 & m2;
    let nBits: u32 = 32u32.wrapping_mul(crate::hacl::bignum_base::bn_get_top_index_u32(len, n));
    if is_valid_m == 0xFFFFFFFFu32
    {
        let mut n2: Vec<u32> = vec![0u32; len as usize];
        let c0: u32 =
            crate::lib::inttypes_intrinsics::sub_borrow_u32(
                0u32,
                n[0usize],
                2u32,
                &mut (&mut n2)[0usize..]
            );
        let c: u32 =
            if 1u32 < len
            {
                let a1: (&mut [u32], &mut [u32]) = n.split_at_mut(1usize);
                let res10: (&mut [u32], &mut [u32]) = (&mut n2).split_at_mut(1usize);
                let mut c: u32 = c0;
                for i in 0u32..len.wrapping_sub(1u32).wrapping_div(4u32)
                {
                    let t1: u32 = a1.1[4u32.wrapping_mul(i) as usize];
                    let res_i: (&mut [u32], &mut [u32]) =
                        res10.1.split_at_mut(4u32.wrapping_mul(i) as usize);
                    c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t1, 0u32, res_i.1);
                    ();
                    let t10: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
                    let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
                    c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t10, 0u32, res_i0.1);
                    ();
                    let t11: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
                    let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
                    c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t11, 0u32, res_i1.1);
                    ();
                    let t12: u32 = a1.1[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
                    let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
                    c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t12, 0u32, res_i2.1);
                    ();
                    ();
                    ()
                };
                ();
                for
                i
                in
                len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_mul(4u32)..len.wrapping_sub(1u32)
                {
                    let t1: u32 = a1.1[i as usize];
                    let res_i: (&mut [u32], &mut [u32]) = res10.1.split_at_mut(i as usize);
                    c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t1, 0u32, res_i.1);
                    ();
                    ()
                };
                let c1: u32 = c;
                c1
            }
            else
            { c0 };
        crate::lowstar::ignore::ignore::<u32>(c);
        crate::hacl::bignum::bn_mod_exp_vartime_u32(
            len,
            nBits,
            n,
            a,
            32u32.wrapping_mul(len),
            &mut n2,
            res
        )
    }
    else
    { (res[0usize..len as usize]).copy_from_slice(&vec![0u32; len as usize]) };
    is_valid_m == 0xFFFFFFFFu32
}

pub fn bn_to_bytes_be(len: u32, b: &mut [u32], res: &mut [u8]) -> ()
{
    let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
    let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
    let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
    for i in 0u32..bnLen
    {
        crate::lowstar::endianness::store32_be(
            &mut (&mut tmp)[i.wrapping_mul(4u32) as usize..],
            b[bnLen.wrapping_sub(i).wrapping_sub(1u32) as usize]
        )
    };
    (res[0usize..len as usize]).copy_from_slice(
        &(&mut (&mut tmp)[tmpLen.wrapping_sub(len) as usize..])[0usize..len as usize]
    )
}

pub fn bn_to_bytes_le(len: u32, b: &mut [u32], res: &mut [u8]) -> ()
{
    let bnLen: u32 = len.wrapping_sub(1u32).wrapping_div(4u32).wrapping_add(1u32);
    let tmpLen: u32 = 4u32.wrapping_mul(bnLen);
    let mut tmp: Vec<u8> = vec![0u8; tmpLen as usize];
    for i in 0u32..bnLen
    {
        crate::lowstar::endianness::store32_le(
            &mut (&mut tmp)[i.wrapping_mul(4u32) as usize..],
            b[i as usize]
        )
    };
    (res[0usize..len as usize]).copy_from_slice(&(&mut (&mut tmp)[0usize..])[0usize..len as usize])
}

pub fn lt_mask(len: u32, a: &mut [u32], b: &mut [u32]) -> u32
{
    let mut acc: u32 = 0u32;
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], b[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    acc
}

pub fn eq_mask(len: u32, a: &mut [u32], b: &mut [u32]) -> u32
{
    let mut mask: u32 = 0xFFFFFFFFu32;
    for i in 0u32..len
    {
        let uu____0: u32 = crate::fstar::uint32::eq_mask(a[i as usize], b[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u32 = mask;
    mask1
}
