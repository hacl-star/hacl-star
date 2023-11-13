pub fn bn_add_mod_n_u32(
    len1: u32,
    n: &mut [u32],
    a: &mut [u32],
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut c: u32 = 0u32;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u32(c, t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u32(c, t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u32(c, t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u32(c, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u32(c, t1, t2, res_i.1)
    };
    let c0: u32 = c;
    let mut tmp: Vec<u32> = vec![0u32; len1 as usize];
    let mut c1: u32 = 0u32;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u32(c1, t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u32(c1, t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u32(c1, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u32 = res[i as usize];
        let t2: u32 = n[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u32(c1, t1, t2, res_i.1)
    };
    let c10: u32 = c1;
    let c2: u32 = c0.wrapping_sub(c10);
    for i in 0u32..len1
    {
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        let x: u32 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x
    }
}

pub fn bn_add_mod_n_u64(
    len1: u32,
    n: &mut [u64],
    a: &mut [u64],
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut c: u64 = 0u64;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::add_carry_u64(c, t1, t2, res_i.1)
    };
    let c0: u64 = c;
    let mut tmp: Vec<u64> = vec![0u64; len1 as usize];
    let mut c1: u64 = 0u64;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::sub_borrow_u64(c1, t1, t2, res_i.1)
    };
    let c10: u64 = c1;
    let c2: u64 = c0.wrapping_sub(c10);
    for i in 0u32..len1
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x: u64 = c2 & os.1[i as usize] | ! c2 & (&mut tmp)[i as usize];
        os.1[i as usize] = x
    }
}

pub fn bn_sub_mod_n_u32(
    len1: u32,
    n: &mut [u32],
    a: &mut [u32],
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut c: u32 = 0u32;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u32 = a[4u32.wrapping_mul(i) as usize];
        let t2: u32 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t1, t2, res_i.1);
        let t10: u32 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t10, t20, res_i0.1);
        let t11: u32 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t11, t21, res_i1.1);
        let t12: u32 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u32 = a[i as usize];
        let t2: u32 = b[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u32(c, t1, t2, res_i.1)
    };
    let c0: u32 = c;
    let mut tmp: Vec<u32> = vec![0u32; len1 as usize];
    let mut c1: u32 = 0u32;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u32 = res[4u32.wrapping_mul(i) as usize];
        let t2: u32 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u32], &mut [u32]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u32(c1, t1, t2, res_i.1);
        let t10: u32 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u32 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u32], &mut [u32]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u32(c1, t10, t20, res_i0.1);
        let t11: u32 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u32 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u32], &mut [u32]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u32(c1, t11, t21, res_i1.1);
        let t12: u32 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u32 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u32], &mut [u32]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u32(c1, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u32 = res[i as usize];
        let t2: u32 = n[i as usize];
        let res_i: (&mut [u32], &mut [u32]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u32(c1, t1, t2, res_i.1)
    };
    let c10: u32 = c1;
    crate::lowstar::ignore::ignore::<u32>(c10);
    let c2: u32 = 0u32.wrapping_sub(c0);
    for i in 0u32..len1
    {
        let os: (&mut [u32], &mut [u32]) = res.split_at_mut(0usize);
        let x: u32 = c2 & (&mut tmp)[i as usize] | ! c2 & os.1[i as usize];
        os.1[i as usize] = x
    }
}

pub fn bn_sub_mod_n_u64(
    len1: u32,
    n: &mut [u64],
    a: &mut [u64],
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut c: u64 = 0u64;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u64 = a[4u32.wrapping_mul(i) as usize];
        let t2: u64 = b[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(4u32.wrapping_mul(i) as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1);
        let t10: u64 = a[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = b[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t10, t20, res_i0.1);
        let t11: u64 = a[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = b[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t11, t21, res_i1.1);
        let t12: u64 = a[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = b[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u64 = a[i as usize];
        let t2: u64 = b[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = res.split_at_mut(i as usize);
        c = crate::lib::inttypes_intrinsics::sub_borrow_u64(c, t1, t2, res_i.1)
    };
    let c0: u64 = c;
    let mut tmp: Vec<u64> = vec![0u64; len1 as usize];
    let mut c1: u64 = 0u64;
    for i in 0u32..len1.wrapping_div(4u32)
    {
        let t1: u64 = res[4u32.wrapping_mul(i) as usize];
        let t2: u64 = n[4u32.wrapping_mul(i) as usize];
        let res_i: (&mut [u64], &mut [u64]) =
            (&mut tmp).split_at_mut(4u32.wrapping_mul(i) as usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t1, t2, res_i.1);
        let t10: u64 = res[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let t20: u64 = n[4u32.wrapping_mul(i).wrapping_add(1u32) as usize];
        let res_i0: (&mut [u64], &mut [u64]) = res_i.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t10, t20, res_i0.1);
        let t11: u64 = res[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let t21: u64 = n[4u32.wrapping_mul(i).wrapping_add(2u32) as usize];
        let res_i1: (&mut [u64], &mut [u64]) = res_i0.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t11, t21, res_i1.1);
        let t12: u64 = res[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let t22: u64 = n[4u32.wrapping_mul(i).wrapping_add(3u32) as usize];
        let res_i2: (&mut [u64], &mut [u64]) = res_i1.1.split_at_mut(1usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t12, t22, res_i2.1)
    };
    for i in len1.wrapping_div(4u32).wrapping_mul(4u32)..len1
    {
        let t1: u64 = res[i as usize];
        let t2: u64 = n[i as usize];
        let res_i: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(i as usize);
        c1 = crate::lib::inttypes_intrinsics::add_carry_u64(c1, t1, t2, res_i.1)
    };
    let c10: u64 = c1;
    crate::lowstar::ignore::ignore::<u64>(c10);
    let c2: u64 = 0u64.wrapping_sub(c0);
    for i in 0u32..len1
    {
        let os: (&mut [u64], &mut [u64]) = res.split_at_mut(0usize);
        let x: u64 = c2 & (&mut tmp)[i as usize] | ! c2 & os.1[i as usize];
        os.1[i as usize] = x
    }
}

pub fn mod_inv_uint32(n0: u32) -> u32
{
    let alpha: u32 = 2147483648u32;
    let beta: u32 = n0;
    let mut ub: u32 = 0u32;
    let mut vb: u32 = 0u32;
    ub = 1u32;
    vb = 0u32;
    for i in 0u32..32u32
    {
        let us: u32 = ub;
        let vs: u32 = vb;
        let u_is_odd: u32 = 0u32.wrapping_sub(us & 1u32);
        let beta_if_u_is_odd: u32 = beta & u_is_odd;
        ub = (us ^ beta_if_u_is_odd).wrapping_shr(1u32).wrapping_add(us & beta_if_u_is_odd);
        let alpha_if_u_is_odd: u32 = alpha & u_is_odd;
        vb = vs.wrapping_shr(1u32).wrapping_add(alpha_if_u_is_odd)
    };
    vb
}

pub fn mod_inv_uint64(n0: u64) -> u64
{
    let alpha: u64 = 9223372036854775808u64;
    let beta: u64 = n0;
    let mut ub: u64 = 0u64;
    let mut vb: u64 = 0u64;
    ub = 1u64;
    vb = 0u64;
    for i in 0u32..64u32
    {
        let us: u64 = ub;
        let vs: u64 = vb;
        let u_is_odd: u64 = 0u64.wrapping_sub(us & 1u64);
        let beta_if_u_is_odd: u64 = beta & u_is_odd;
        ub = (us ^ beta_if_u_is_odd).wrapping_shr(1u32).wrapping_add(us & beta_if_u_is_odd);
        let alpha_if_u_is_odd: u64 = alpha & u_is_odd;
        vb = vs.wrapping_shr(1u32).wrapping_add(alpha_if_u_is_odd)
    };
    vb
}

pub fn bn_check_modulus_u32(len: u32, n: &mut [u32]) -> u32
{
    let mut one: Vec<u32> = vec![0u32; len as usize];
    ((&mut one)[0usize..0usize + len as usize]).copy_from_slice(&vec![0u32; len as usize]);
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
    m0 & m1
}

pub fn bn_precomp_r2_mod_n_u32(len: u32, nBits: u32, n: &mut [u32], res: &mut [u32]) -> ()
{
    (res[0usize..0usize + len as usize]).copy_from_slice(&vec![0u32; len as usize]);
    let i: u32 = nBits.wrapping_div(32u32);
    let j: u32 = nBits.wrapping_rem(32u32);
    res[i as usize] = res[i as usize] | 1u32.wrapping_shl(j);
    for i0 in 0u32..64u32.wrapping_mul(len).wrapping_sub(nBits)
    { bn_add_mod_n_u32(len, n, res, res, res) }
}

pub fn bn_to_mont_u32(
    len: u32,
    n: &mut [u32],
    nInv: u32,
    r2: &mut [u32],
    a: &mut [u32],
    aM: &mut [u32]
) ->
    ()
{
    let mut c: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint32(len, a, r2, &mut tmp, &mut c);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u32(len, n, nInv, &mut c, aM)
}

pub fn bn_from_mont_u32(len: u32, n: &mut [u32], nInv_u64: u32, aM: &mut [u32], a: &mut [u32]) ->
    ()
{
    let mut tmp: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    ((&mut tmp)[0usize..0usize + len as usize]).copy_from_slice(&aM[0usize..0usize + len as usize]);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u32(len, n, nInv_u64, &mut tmp, a)
}

pub fn bn_mont_mul_u32(
    len: u32,
    n: &mut [u32],
    nInv_u64: u32,
    aM: &mut [u32],
    bM: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let mut c: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint32(len, aM, bM, &mut tmp, &mut c);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u32(len, n, nInv_u64, &mut c, resM)
}

pub fn bn_mont_sqr_u32(
    len: u32,
    n: &mut [u32],
    nInv_u64: u32,
    aM: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let mut c: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_sqr_uint32(len, aM, &mut tmp, &mut c);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u32(len, n, nInv_u64, &mut c, resM)
}

pub fn bn_check_modulus_u64(len: u32, n: &mut [u64]) -> u64
{
    let mut one: Vec<u64> = vec![0u64; len as usize];
    ((&mut one)[0usize..0usize + len as usize]).copy_from_slice(&vec![0u64; len as usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: u64 = 0u64;
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = acc;
    m0 & m1
}

pub fn bn_precomp_r2_mod_n_u64(len: u32, nBits: u32, n: &mut [u64], res: &mut [u64]) -> ()
{
    (res[0usize..0usize + len as usize]).copy_from_slice(&vec![0u64; len as usize]);
    let i: u32 = nBits.wrapping_div(64u32);
    let j: u32 = nBits.wrapping_rem(64u32);
    res[i as usize] = res[i as usize] | 1u64.wrapping_shl(j);
    for i0 in 0u32..128u32.wrapping_mul(len).wrapping_sub(nBits)
    { bn_add_mod_n_u64(len, n, res, res, res) }
}

pub fn bn_to_mont_u64(
    len: u32,
    n: &mut [u64],
    nInv: u64,
    r2: &mut [u64],
    a: &mut [u64],
    aM: &mut [u64]
) ->
    ()
{
    let mut c: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint64(len, a, r2, &mut tmp, &mut c);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u64(len, n, nInv, &mut c, aM)
}

pub fn bn_from_mont_u64(len: u32, n: &mut [u64], nInv_u64: u64, aM: &mut [u64], a: &mut [u64]) ->
    ()
{
    let mut tmp: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    ((&mut tmp)[0usize..0usize + len as usize]).copy_from_slice(&aM[0usize..0usize + len as usize]);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u64(len, n, nInv_u64, &mut tmp, a)
}

pub fn bn_mont_mul_u64(
    len: u32,
    n: &mut [u64],
    nInv_u64: u64,
    aM: &mut [u64],
    bM: &mut [u64],
    resM: &mut [u64]
) ->
    ()
{
    let mut c: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint64(len, aM, bM, &mut tmp, &mut c);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u64(len, n, nInv_u64, &mut c, resM)
}

pub fn bn_mont_sqr_u64(
    len: u32,
    n: &mut [u64],
    nInv_u64: u64,
    aM: &mut [u64],
    resM: &mut [u64]
) ->
    ()
{
    let mut c: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_sqr_uint64(len, aM, &mut tmp, &mut c);
    crate::hacl::bignum_montgomery::bn_mont_reduction_u64(len, n, nInv_u64, &mut c, resM)
}

fn bn_almost_mont_mul_u32(
    len: u32,
    n: &mut [u32],
    nInv_u64: u32,
    aM: &mut [u32],
    bM: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let mut c: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint32(len, aM, bM, &mut tmp, &mut c);
    crate::hacl::bignum_almostmontgomery::bn_almost_mont_reduction_u32(
        len,
        n,
        nInv_u64,
        &mut c,
        resM
    )
}

fn bn_almost_mont_sqr_u32(
    len: u32,
    n: &mut [u32],
    nInv_u64: u32,
    aM: &mut [u32],
    resM: &mut [u32]
) ->
    ()
{
    let mut c: Vec<u32> = vec![0u32; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u32> = vec![0u32; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_sqr_uint32(len, aM, &mut tmp, &mut c);
    crate::hacl::bignum_almostmontgomery::bn_almost_mont_reduction_u32(
        len,
        n,
        nInv_u64,
        &mut c,
        resM
    )
}

fn bn_almost_mont_mul_u64(
    len: u32,
    n: &mut [u64],
    nInv_u64: u64,
    aM: &mut [u64],
    bM: &mut [u64],
    resM: &mut [u64]
) ->
    ()
{
    let mut c: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_mul_uint64(len, aM, bM, &mut tmp, &mut c);
    crate::hacl::bignum_almostmontgomery::bn_almost_mont_reduction_u64(
        len,
        n,
        nInv_u64,
        &mut c,
        resM
    )
}

fn bn_almost_mont_sqr_u64(
    len: u32,
    n: &mut [u64],
    nInv_u64: u64,
    aM: &mut [u64],
    resM: &mut [u64]
) ->
    ()
{
    let mut c: Vec<u64> = vec![0u64; len.wrapping_add(len) as usize];
    let mut tmp: Vec<u64> = vec![0u64; 4u32.wrapping_mul(len) as usize];
    crate::hacl::bignum_karatsuba::bn_karatsuba_sqr_uint64(len, aM, &mut tmp, &mut c);
    crate::hacl::bignum_almostmontgomery::bn_almost_mont_reduction_u64(
        len,
        n,
        nInv_u64,
        &mut c,
        resM
    )
}

pub fn bn_check_mod_exp_u32(len: u32, n: &mut [u32], a: &mut [u32], bBits: u32, b: &mut [u32]) ->
    u32
{
    let mut one: Vec<u32> = vec![0u32; len as usize];
    ((&mut one)[0usize..0usize + len as usize]).copy_from_slice(&vec![0u32; len as usize]);
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
    let bLen: u32 =
        if bBits == 0u32
        { 1u32 }
        else
        { bBits.wrapping_sub(1u32).wrapping_div(32u32).wrapping_add(1u32) };
    let m10: u32 =
        if bBits < 32u32.wrapping_mul(bLen)
        {
            let mut b2: Vec<u32> = vec![0u32; bLen as usize];
            let i: u32 = bBits.wrapping_div(32u32);
            let j: u32 = bBits.wrapping_rem(32u32);
            (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u32.wrapping_shl(j);
            ();
            let mut acc0: u32 = 0u32;
            for i0 in 0u32..bLen
            {
                let beq: u32 =
                    crate::fstar::uint32::eq_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                let blt: u32 =
                    ! crate::fstar::uint32::gte_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32);
                ()
            };
            let res: u32 = acc0;
            res
        }
        else
        { 0xFFFFFFFFu32 };
    let mut acc0: u32 = 0u32;
    for i in 0u32..len
    {
        let beq: u32 = crate::fstar::uint32::eq_mask(a[i as usize], n[i as usize]);
        let blt: u32 = ! crate::fstar::uint32::gte_mask(a[i as usize], n[i as usize]);
        acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFu32 | ! blt & 0u32)
    };
    let m2: u32 = acc0;
    let m: u32 = m10 & m2;
    m00 & m
}

pub fn bn_mod_exp_vartime_u32(
    len: u32,
    nBits: u32,
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut r2: Vec<u32> = vec![0u32; len as usize];
    bn_precomp_r2_mod_n_u32(len, nBits, n, &mut r2);
    let mu: u32 = mod_inv_uint32(n[0usize]);
    crate::hacl::bignum_exponentiation::bn_mod_exp_vartime_precomp_u32(
        len,
        n,
        mu,
        &mut r2,
        a,
        bBits,
        b,
        res
    )
}

pub fn bn_mod_exp_consttime_u32(
    len: u32,
    nBits: u32,
    n: &mut [u32],
    a: &mut [u32],
    bBits: u32,
    b: &mut [u32],
    res: &mut [u32]
) ->
    ()
{
    let mut r2: Vec<u32> = vec![0u32; len as usize];
    bn_precomp_r2_mod_n_u32(len, nBits, n, &mut r2);
    let mu: u32 = mod_inv_uint32(n[0usize]);
    crate::hacl::bignum_exponentiation::bn_mod_exp_consttime_precomp_u32(
        len,
        n,
        mu,
        &mut r2,
        a,
        bBits,
        b,
        res
    )
}

pub fn bn_check_mod_exp_u64(len: u32, n: &mut [u64], a: &mut [u64], bBits: u32, b: &mut [u64]) ->
    u64
{
    let mut one: Vec<u64> = vec![0u64; len as usize];
    ((&mut one)[0usize..0usize + len as usize]).copy_from_slice(&vec![0u64; len as usize]);
    (&mut one)[0usize] = 1u64;
    let bit0: u64 = n[0usize] & 1u64;
    let m0: u64 = 0u64.wrapping_sub(bit0);
    let mut acc: u64 = 0u64;
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask((&mut one)[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask((&mut one)[i as usize], n[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m1: u64 = acc;
    let m00: u64 = m0 & m1;
    let bLen: u32 =
        if bBits == 0u32
        { 1u32 }
        else
        { bBits.wrapping_sub(1u32).wrapping_div(64u32).wrapping_add(1u32) };
    let m10: u64 =
        if bBits < 64u32.wrapping_mul(bLen)
        {
            let mut b2: Vec<u64> = vec![0u64; bLen as usize];
            let i: u32 = bBits.wrapping_div(64u32);
            let j: u32 = bBits.wrapping_rem(64u32);
            (&mut b2)[i as usize] = (&mut b2)[i as usize] | 1u64.wrapping_shl(j);
            ();
            let mut acc0: u64 = 0u64;
            for i0 in 0u32..bLen
            {
                let beq: u64 =
                    crate::fstar::uint64::eq_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                let blt: u64 =
                    ! crate::fstar::uint64::gte_mask(b[i0 as usize], (&mut b2)[i0 as usize]);
                acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64);
                ()
            };
            let res: u64 = acc0;
            res
        }
        else
        { 0xFFFFFFFFFFFFFFFFu64 };
    let mut acc0: u64 = 0u64;
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], n[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], n[i as usize]);
        acc0 = beq & acc0 | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    let m2: u64 = acc0;
    let m: u64 = m10 & m2;
    m00 & m
}

pub fn bn_mod_exp_vartime_u64(
    len: u32,
    nBits: u32,
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut r2: Vec<u64> = vec![0u64; len as usize];
    bn_precomp_r2_mod_n_u64(len, nBits, n, &mut r2);
    let mu: u64 = mod_inv_uint64(n[0usize]);
    crate::hacl::bignum_exponentiation::bn_mod_exp_vartime_precomp_u64(
        len,
        n,
        mu,
        &mut r2,
        a,
        bBits,
        b,
        res
    )
}

pub fn bn_mod_exp_consttime_u64(
    len: u32,
    nBits: u32,
    n: &mut [u64],
    a: &mut [u64],
    bBits: u32,
    b: &mut [u64],
    res: &mut [u64]
) ->
    ()
{
    let mut r2: Vec<u64> = vec![0u64; len as usize];
    bn_precomp_r2_mod_n_u64(len, nBits, n, &mut r2);
    let mu: u64 = mod_inv_uint64(n[0usize]);
    crate::hacl::bignum_exponentiation::bn_mod_exp_consttime_precomp_u64(
        len,
        n,
        mu,
        &mut r2,
        a,
        bBits,
        b,
        res
    )
}
