pub fn add(len: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{ crate::hacl::bignum_base::bn_add_eq_len_u64(len, a, b, res) }

pub fn sub(len: u32, a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> u64
{ crate::hacl::bignum_base::bn_sub_eq_len_u64(len, a, b, res) }

pub fn add_mod(len: u32, n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{ crate::hacl::bignum::bn_add_mod_n_u64(len, n, a, b, res) }

pub fn sub_mod(len: u32, n: &mut [u64], a: &mut [u64], b: &mut [u64], res: &mut [u64]) -> ()
{ crate::hacl::bignum::bn_sub_mod_n_u64(len, n, a, b, res) }

pub fn lt_mask(len: u32, a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut acc: u64 = 0u64;
    for i in 0u32..len
    {
        let beq: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        let blt: u64 = ! crate::fstar::uint64::gte_mask(a[i as usize], b[i as usize]);
        acc = beq & acc | ! beq & (blt & 0xFFFFFFFFFFFFFFFFu64 | ! blt & 0u64)
    };
    acc
}

pub fn eq_mask(len: u32, a: &mut [u64], b: &mut [u64]) -> u64
{
    let mut mask: u64 = 0xFFFFFFFFFFFFFFFFu64;
    for i in 0u32..len
    {
        let uu____0: u64 = crate::fstar::uint64::eq_mask(a[i as usize], b[i as usize]);
        mask = uu____0 & mask
    };
    let mask1: u64 = mask;
    mask1
}