#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn add_scalar(out: &mut [u64], f1: &mut [u64], f2: u64) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fadd_inline::add_scalar(out, f1, f2) }
    else
    {
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_fadd::add_scalar_e(out, f1, f2)
        )
    }
}

#[inline] fn fadd(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fadd_inline::fadd(out, f1, f2) }
    else
    { crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fadd::fadd_e(out, f1, f2)) }
}

#[inline] fn fsub(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fadd_inline::fsub(out, f1, f2) }
    else
    { crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fsub::fsub_e(out, f1, f2)) }
}

#[inline] fn fmul(out: &mut [u64], f1: &mut [u64], f2: &mut [u64], tmp: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fmul_inline::fmul(out, f1, f2, &mut tmp[0usize..]) }
    else
    {
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_fmul::fmul_e(&mut tmp[0usize..], f1, out, f2)
        )
    }
}

#[inline] fn fmul2(out: &mut [u64], f1: &mut [u64], f2: &mut [u64], tmp: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fmul_inline::fmul2(out, f1, f2, tmp) }
    else
    {
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_fmul::fmul2_e(tmp, f1, out, f2)
        )
    }
}

#[inline] fn fmul_scalar(out: &mut [u64], f1: &mut [u64], f2: u64) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fmul_inline::fmul_scalar(out, f1, f2) }
    else
    {
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_fmul::fmul_scalar_e(out, f1, f2)
        )
    }
}

#[inline] fn fsqr(out: &mut [u64], f1: &mut [u64], tmp: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fsqr_inline::fsqr(out, f1, tmp) }
    else
    { crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fsqr::fsqr_e(tmp, f1, out)) }
}

#[inline] fn fsqr2(out: &mut [u64], f: &mut [u64], tmp: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fsqr_inline::fsqr2(out, f, tmp) }
    else
    { crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fsqr::fsqr2_e(tmp, f, out)) }
}

#[inline] fn cswap2(bit: u64, p1: &mut [u64], p2: &mut [u64]) -> ()
{
    if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
    { crate::vale::inline_x64_fswap_inline::cswap2(bit, p1, p2) }
    else
    {
        crate::lowstar::ignore::ignore::<u64>(
            crate::vale::stdcalls_x64_fswap::cswap2_e(bit, p1, p2)
        )
    }
}

const g25519: [u8; 32] =
    [9u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];

fn point_add_and_double(q: &mut [u64], p01_tmp1: &mut [u64], tmp2: &mut [u64]) -> ()
{
    let nq: (&mut [u64], &mut [u64]) = p01_tmp1.split_at_mut(0usize);
    let nq_p1: (&mut [u64], &mut [u64]) = nq.1.split_at_mut(8usize);
    let tmp1: (&mut [u64], &mut [u64]) = nq_p1.1.split_at_mut(8usize);
    let x1: (&mut [u64], &mut [u64]) = q.split_at_mut(0usize);
    let x2: (&mut [u64], &mut [u64]) = nq_p1.0.split_at_mut(0usize);
    let z2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let dc: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(8usize);
    let ab: (&mut [u64], &mut [u64]) = dc.0.split_at_mut(0usize);
    let a: (&mut [u64], &mut [u64]) = ab.1.split_at_mut(0usize);
    let b: (&mut [u64], &mut [u64]) = a.1.split_at_mut(4usize);
    fadd(b.0, z2.0, z2.1);
    fsub(b.1, z2.0, z2.1);
    let ab1: (&mut [u64], &mut [u64]) = ab.1.split_at_mut(0usize);
    let x3: (&mut [u64], &mut [u64]) = tmp1.0.split_at_mut(0usize);
    let z31: (&mut [u64], &mut [u64]) = x3.1.split_at_mut(4usize);
    let d: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c: (&mut [u64], &mut [u64]) = d.1.split_at_mut(4usize);
    fadd(c.1, z31.0, z31.1);
    fsub(c.0, z31.0, z31.1);
    let mut f1_copy: [u64; 8] = [0u64; 8usize];
    ((&mut f1_copy)[0usize..8usize]).copy_from_slice(&dc.1[0usize..8usize]);
    fmul2(dc.1, &mut f1_copy, ab1.1, tmp2);
    let d1: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c1: (&mut [u64], &mut [u64]) = d1.1.split_at_mut(4usize);
    fadd(z31.0, c1.0, c1.1);
    fsub(z31.1, c1.0, c1.1);
    let ab2: (&mut [u64], &mut [u64]) = ab1.1.split_at_mut(0usize);
    let dc1: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    fsqr2(dc1.1, ab2.1, tmp2);
    let mut f1_copy0: [u64; 8] = [0u64; 8usize];
    ((&mut f1_copy0)[0usize..8usize]).copy_from_slice(&tmp1.0[0usize..8usize]);
    fsqr2(tmp1.0, &mut f1_copy0, tmp2);
    let a1: (&mut [u64], &mut [u64]) = ab2.1.split_at_mut(0usize);
    let b1: (&mut [u64], &mut [u64]) = a1.1.split_at_mut(4usize);
    let d0: (&mut [u64], &mut [u64]) = dc1.1.split_at_mut(0usize);
    let c0: (&mut [u64], &mut [u64]) = d0.1.split_at_mut(4usize);
    b1.0[0usize] = c0.1[0usize];
    b1.0[1usize] = c0.1[1usize];
    b1.0[2usize] = c0.1[2usize];
    b1.0[3usize] = c0.1[3usize];
    let mut f2_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy)[0usize..4usize]).copy_from_slice(&c0.1[0usize..4usize]);
    fsub(c0.1, c0.0, &mut f2_copy);
    fmul_scalar(b1.1, c0.1, 121665u64);
    let mut f1_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy1)[0usize..4usize]).copy_from_slice(&b1.1[0usize..4usize]);
    fadd(b1.1, &mut f1_copy1, c0.0);
    let ab3: (&mut [u64], &mut [u64]) = ab2.1.split_at_mut(0usize);
    let dc2: (&mut [u64], &mut [u64]) = dc1.1.split_at_mut(0usize);
    fmul2(nq_p1.0, dc2.1, ab3.1, tmp2);
    let z310: (&mut [u64], &mut [u64]) = tmp1.0.split_at_mut(4usize);
    let mut f1_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy2)[0usize..4usize]).copy_from_slice(&z310.1[0usize..4usize]);
    fmul(z310.1, &mut f1_copy2, x1.1, tmp2)
}

fn point_double(nq: &mut [u64], tmp1: &mut [u64], tmp2: &mut [u64]) -> ()
{
    let x2: (&mut [u64], &mut [u64]) = nq.split_at_mut(0usize);
    let z2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let ab: (&mut [u64], &mut [u64]) = tmp1.split_at_mut(0usize);
    let dc: (&mut [u64], &mut [u64]) = ab.1.split_at_mut(8usize);
    let a: (&mut [u64], &mut [u64]) = dc.0.split_at_mut(0usize);
    let b: (&mut [u64], &mut [u64]) = a.1.split_at_mut(4usize);
    fadd(b.0, z2.0, z2.1);
    fsub(b.1, z2.0, z2.1);
    fsqr2(dc.1, dc.0, tmp2);
    let d: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c: (&mut [u64], &mut [u64]) = d.1.split_at_mut(4usize);
    let a1: (&mut [u64], &mut [u64]) = dc.0.split_at_mut(0usize);
    let b1: (&mut [u64], &mut [u64]) = a1.1.split_at_mut(4usize);
    b1.0[0usize] = c.1[0usize];
    b1.0[1usize] = c.1[1usize];
    b1.0[2usize] = c.1[2usize];
    b1.0[3usize] = c.1[3usize];
    let mut f2_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy)[0usize..4usize]).copy_from_slice(&c.1[0usize..4usize]);
    fsub(c.1, c.0, &mut f2_copy);
    fmul_scalar(b1.1, c.1, 121665u64);
    let mut f1_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy)[0usize..4usize]).copy_from_slice(&b1.1[0usize..4usize]);
    fadd(b1.1, &mut f1_copy, c.0);
    let ab1: (&mut [u64], &mut [u64]) = dc.0.split_at_mut(0usize);
    let dc1: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    fmul2(nq, dc1.1, ab1.1, tmp2)
}

fn montgomery_ladder(out: &mut [u64], key: &mut [u8], init: &mut [u64]) -> ()
{
    let mut tmp2: [u64; 16] = [0u64; 16usize];
    let mut p01_tmp1_swap: [u64; 33] = [0u64; 33usize];
    let p01: (&mut [u64], &mut [u64]) = (&mut p01_tmp1_swap).split_at_mut(0usize);
    let p03: (&mut [u64], &mut [u64]) = p01.1.split_at_mut(0usize);
    let p11: (&mut [u64], &mut [u64]) = p03.1.split_at_mut(8usize);
    (p11.1[0usize..8usize]).copy_from_slice(&init[0usize..8usize]);
    let x0: (&mut [u64], &mut [u64]) = p11.0.split_at_mut(0usize);
    let z0: (&mut [u64], &mut [u64]) = x0.1.split_at_mut(4usize);
    z0.0[0usize] = 1u64;
    z0.0[1usize] = 0u64;
    z0.0[2usize] = 0u64;
    z0.0[3usize] = 0u64;
    z0.1[0usize] = 0u64;
    z0.1[1usize] = 0u64;
    z0.1[2usize] = 0u64;
    z0.1[3usize] = 0u64;
    let swap: (&mut [u64], &mut [u64]) = p01.1.split_at_mut(32usize);
    let p01_tmp1: (&mut [u64], &mut [u64]) = swap.0.split_at_mut(0usize);
    let nq: (&mut [u64], &mut [u64]) = p01_tmp1.1.split_at_mut(0usize);
    let nq_p1: (&mut [u64], &mut [u64]) = nq.1.split_at_mut(8usize);
    cswap2(1u64, nq_p1.0, nq_p1.1);
    let p01_tmp11: (&mut [u64], &mut [u64]) = p01_tmp1.1.split_at_mut(0usize);
    point_add_and_double(init, p01_tmp11.1, &mut tmp2);
    swap.1[0usize] = 1u64;
    for i in 0u32..251u32
    {
        let p01_tmp12: (&mut [u64], &mut [u64]) = p01_tmp11.1.split_at_mut(0usize);
        let swap1: (&mut [u64], &mut [u64]) = swap.1.split_at_mut(0usize);
        let nq1: (&mut [u64], &mut [u64]) = p01_tmp12.1.split_at_mut(0usize);
        let nq_p11: (&mut [u64], &mut [u64]) = nq1.1.split_at_mut(8usize);
        let bit: u64 =
            ((key[253u32.wrapping_sub(i).wrapping_div(8u32) as usize]).wrapping_shr(
                253u32.wrapping_sub(i).wrapping_rem(8u32)
            )
            &
            1u8)
            as
            u64;
        let sw: u64 = swap1.1[0usize] ^ bit;
        cswap2(sw, nq_p11.0, nq_p11.1);
        point_add_and_double(init, p01_tmp12.1, &mut tmp2);
        swap1.1[0usize] = bit
    };
    let sw: u64 = swap.1[0usize];
    let p01_tmp12: (&mut [u64], &mut [u64]) = p01_tmp11.1.split_at_mut(0usize);
    let nq1: (&mut [u64], &mut [u64]) = p01_tmp12.1.split_at_mut(0usize);
    let nq_p11: (&mut [u64], &mut [u64]) = nq1.1.split_at_mut(8usize);
    cswap2(sw, nq_p11.0, nq_p11.1);
    let p01_tmp10: (&mut [u64], &mut [u64]) = p01_tmp12.1.split_at_mut(0usize);
    let nq0: (&mut [u64], &mut [u64]) = p01_tmp10.1.split_at_mut(0usize);
    let tmp1: (&mut [u64], &mut [u64]) = nq0.1.split_at_mut(16usize);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    let p010: (&mut [u64], &mut [u64]) = p01_tmp10.1.split_at_mut(0usize);
    (out[0usize..8usize]).copy_from_slice(&p010.1[0usize..8usize])
}

fn fsquare_times(o: &mut [u64], inp: &mut [u64], tmp: &mut [u64], n: u32) -> ()
{
    fsqr(o, inp, tmp);
    for _i in 0u32..n.wrapping_sub(1u32)
    {
        let mut f1_copy: [u64; 4] = [0u64; 4usize];
        ((&mut f1_copy)[0usize..4usize]).copy_from_slice(&o[0usize..4usize]);
        fsqr(o, &mut f1_copy, tmp)
    }
}

fn finv(o: &mut [u64], i: &mut [u64], tmp: &mut [u64]) -> ()
{
    let mut t1: [u64; 16] = [0u64; 16usize];
    let a1: (&mut [u64], &mut [u64]) = (&mut t1).split_at_mut(0usize);
    let b1: (&mut [u64], &mut [u64]) = a1.1.split_at_mut(4usize);
    let t01: (&mut [u64], &mut [u64]) = b1.1.split_at_mut(8usize);
    let tmp1: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(b1.0, i, tmp1.1, 1u32);
    fsquare_times(t01.1, b1.0, tmp1.1, 2u32);
    fmul(t01.0, t01.1, i, tmp);
    let mut f2_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy)[0usize..4usize]).copy_from_slice(&b1.0[0usize..4usize]);
    fmul(b1.0, t01.0, &mut f2_copy, tmp);
    let tmp11: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(t01.1, b1.0, tmp11.1, 1u32);
    let mut f2_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy0)[0usize..4usize]).copy_from_slice(&t01.0[0usize..4usize]);
    fmul(t01.0, t01.1, &mut f2_copy0, tmp);
    let tmp12: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(t01.1, t01.0, tmp12.1, 5u32);
    let mut f2_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy1)[0usize..4usize]).copy_from_slice(&t01.0[0usize..4usize]);
    fmul(t01.0, t01.1, &mut f2_copy1, tmp);
    let b10: (&mut [u64], &mut [u64]) = t01.0.split_at_mut(0usize);
    let c1: (&mut [u64], &mut [u64]) = b10.1.split_at_mut(4usize);
    let t010: (&mut [u64], &mut [u64]) = t01.1.split_at_mut(0usize);
    let tmp10: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(t010.1, c1.0, tmp10.1, 10u32);
    fmul(c1.1, t010.1, c1.0, tmp);
    let tmp110: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(t010.1, c1.1, tmp110.1, 20u32);
    let mut f1_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy)[0usize..4usize]).copy_from_slice(&t010.1[0usize..4usize]);
    fmul(t010.1, &mut f1_copy, c1.1, tmp);
    let tmp120: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let mut i_copy: [u64; 4] = [0u64; 4usize];
    ((&mut i_copy)[0usize..4usize]).copy_from_slice(&t010.1[0usize..4usize]);
    fsquare_times(t010.1, &mut i_copy, tmp120.1, 10u32);
    let mut f2_copy2: [u64; 4] = [0u64; 4usize];
    ((&mut f2_copy2)[0usize..4usize]).copy_from_slice(&c1.0[0usize..4usize]);
    fmul(c1.0, t010.1, &mut f2_copy2, tmp);
    let tmp13: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(t010.1, c1.0, tmp13.1, 50u32);
    fmul(c1.1, t010.1, c1.0, tmp);
    let b11: (&mut [u64], &mut [u64]) = c1.0.split_at_mut(0usize);
    let c10: (&mut [u64], &mut [u64]) = c1.1.split_at_mut(0usize);
    let t011: (&mut [u64], &mut [u64]) = t010.1.split_at_mut(0usize);
    let tmp14: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    fsquare_times(t011.1, c10.1, tmp14.1, 100u32);
    let mut f1_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy0)[0usize..4usize]).copy_from_slice(&t011.1[0usize..4usize]);
    fmul(t011.1, &mut f1_copy0, c10.1, tmp);
    let tmp111: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let mut i_copy0: [u64; 4] = [0u64; 4usize];
    ((&mut i_copy0)[0usize..4usize]).copy_from_slice(&t011.1[0usize..4usize]);
    fsquare_times(t011.1, &mut i_copy0, tmp111.1, 50u32);
    let mut f1_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy1)[0usize..4usize]).copy_from_slice(&t011.1[0usize..4usize]);
    fmul(t011.1, &mut f1_copy1, b11.1, tmp);
    let tmp121: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let mut i_copy1: [u64; 4] = [0u64; 4usize];
    ((&mut i_copy1)[0usize..4usize]).copy_from_slice(&t011.1[0usize..4usize]);
    fsquare_times(t011.1, &mut i_copy1, tmp121.1, 5u32);
    let a: (&mut [u64], &mut [u64]) = b1.0.split_at_mut(0usize);
    let t0: (&mut [u64], &mut [u64]) = t011.1.split_at_mut(0usize);
    fmul(o, t0.1, a.1, tmp)
}

fn store_felem(b: &mut [u64], f: &mut [u64]) -> ()
{
    let f3: u64 = f[3usize];
    let top_bit: u64 = f3.wrapping_shr(63u32);
    f[3usize] = f3 & 0x7fffffffffffffffu64;
    add_scalar(f, f, 19u64.wrapping_mul(top_bit));
    let f30: u64 = f[3usize];
    let top_bit0: u64 = f30.wrapping_shr(63u32);
    f[3usize] = f30 & 0x7fffffffffffffffu64;
    add_scalar(f, f, 19u64.wrapping_mul(top_bit0));
    let f0: u64 = f[0usize];
    let f1: u64 = f[1usize];
    let f2: u64 = f[2usize];
    let f31: u64 = f[3usize];
    let m0: u64 = crate::fstar::uint64::gte_mask(f0, 0xffffffffffffffedu64);
    let m1: u64 = crate::fstar::uint64::eq_mask(f1, 0xffffffffffffffffu64);
    let m2: u64 = crate::fstar::uint64::eq_mask(f2, 0xffffffffffffffffu64);
    let m3: u64 = crate::fstar::uint64::eq_mask(f31, 0x7fffffffffffffffu64);
    let mask: u64 = m0 & m1 & m2 & m3;
    let f0·: u64 = f0.wrapping_sub(mask & 0xffffffffffffffedu64);
    let f1·: u64 = f1.wrapping_sub(mask & 0xffffffffffffffffu64);
    let f2·: u64 = f2.wrapping_sub(mask & 0xffffffffffffffffu64);
    let f3·: u64 = f31.wrapping_sub(mask & 0x7fffffffffffffffu64);
    let o0: u64 = f0·;
    let o1: u64 = f1·;
    let o2: u64 = f2·;
    let o3: u64 = f3·;
    b[0usize] = o0;
    b[1usize] = o1;
    b[2usize] = o2;
    b[3usize] = o3
}

fn encode_point(o: &mut [u8], i: &mut [u64]) -> ()
{
    let x: (&mut [u64], &mut [u64]) = i.split_at_mut(0usize);
    let z: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let mut u64s: [u64; 4] = [0u64; 4usize];
    let mut tmp_w: [u64; 16] = [0u64; 16usize];
    finv(&mut tmp, z.1, &mut tmp_w);
    let mut f1_copy: [u64; 4] = [0u64; 4usize];
    ((&mut f1_copy)[0usize..4usize]).copy_from_slice(&(&mut tmp)[0usize..4usize]);
    fmul(&mut tmp, &mut f1_copy, z.0, &mut tmp_w);
    store_felem(&mut u64s, &mut tmp);
    for i0 in 0u32..4u32
    {
        crate::lowstar::endianness::store64_le(
            &mut o[i0.wrapping_mul(8u32) as usize..],
            (&mut u64s)[i0 as usize]
        )
    }
}

pub fn scalarmult(out: &mut [u8], r#priv: &mut [u8], r#pub: &mut [u8]) -> ()
{
    let mut init: [u64; 8] = [0u64; 8usize];
    let mut init_copy: [u64; 8] = [0u64; 8usize];
    let mut tmp: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let bj: (&mut [u8], &mut [u8]) = r#pub.split_at_mut(i.wrapping_mul(8u32) as usize);
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
        let os: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let tmp3: u64 = (&mut tmp)[3usize];
    (&mut tmp)[3usize] = tmp3 & 0x7fffffffffffffffu64;
    let x: (&mut [u64], &mut [u64]) = (&mut init).split_at_mut(0usize);
    let z: (&mut [u64], &mut [u64]) = x.1.split_at_mut(4usize);
    z.1[0usize] = 1u64;
    z.1[1usize] = 0u64;
    z.1[2usize] = 0u64;
    z.1[3usize] = 0u64;
    z.0[0usize] = (&mut tmp)[0usize];
    z.0[1usize] = (&mut tmp)[1usize];
    z.0[2usize] = (&mut tmp)[2usize];
    z.0[3usize] = (&mut tmp)[3usize];
    ((&mut init_copy)[0usize..8usize]).copy_from_slice(&(&mut init)[0usize..8usize]);
    montgomery_ladder(&mut init, r#priv, &mut init_copy);
    encode_point(out, &mut init)
}

pub fn secret_to_public(r#pub: &mut [u8], r#priv: &mut [u8]) -> ()
{
    let mut basepoint: [u8; 32] = [0u8; 32usize];
    for i in 0u32..32u32
    {
        let x: u8 = (&g25519)[i as usize];
        let os: (&mut [u8], &mut [u8]) = (&mut basepoint).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    scalarmult(r#pub, r#priv, &mut basepoint)
}

pub fn ecdh(out: &mut [u8], r#priv: &mut [u8], r#pub: &mut [u8]) -> bool
{
    let mut zeros: [u8; 32] = [0u8; 32usize];
    scalarmult(out, r#priv, r#pub);
    let mut res: [u8; 1] = [255u8; 1usize];
    for i in 0u32..32u32
    {
        let uu____0: u8 = crate::fstar::uint8::eq_mask(out[i as usize], (&mut zeros)[i as usize]);
        (&mut res)[0usize] = uu____0 & (&mut res)[0usize]
    };
    let z: u8 = (&mut res)[0usize];
    let r: bool = z == 255u8;
    ! r
}
