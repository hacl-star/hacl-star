fn add_scalar(out: &mut [u64], f1: &mut [u64], f2: u64) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fadd_inline::add_scalar(out, f1, f2) }
else
{
    crate::lowstar::ignore::ignore::<u64>(
        crate::vale::stdcalls_x64_fadd::add_scalar_e(out, f1, f2)
    )
}

fn fadd(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fadd_inline::fadd(out, f1, f2) }
else
{ crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fadd::fadd_e(out, f1, f2)) }

fn fsub(out: &mut [u64], f1: &mut [u64], f2: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fadd_inline::fsub(out, f1, f2) }
else
{ crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fsub::fsub_e(out, f1, f2)) }

fn fmul(out: &mut [u64], f1: &mut [u64], f2: &mut [u64], tmp: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fmul_inline::fmul(out, f1, f2, &mut tmp[0usize..]) }
else
{
    crate::lowstar::ignore::ignore::<u64>(
        crate::vale::stdcalls_x64_fmul::fmul_e(&mut tmp[0usize..], f1, out, f2)
    )
}

fn fmul2(out: &mut [u64], f1: &mut [u64], f2: &mut [u64], tmp: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fmul_inline::fmul2(out, f1, f2, tmp) }
else
{
    crate::lowstar::ignore::ignore::<u64>(
        crate::vale::stdcalls_x64_fmul::fmul2_e(tmp, f1, out, f2)
    )
}

fn fmul_scalar(out: &mut [u64], f1: &mut [u64], f2: u64) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fmul_inline::fmul_scalar(out, f1, f2) }
else
{
    crate::lowstar::ignore::ignore::<u64>(
        crate::vale::stdcalls_x64_fmul::fmul_scalar_e(out, f1, f2)
    )
}

fn fsqr(out: &mut [u64], f1: &mut [u64], tmp: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fsqr_inline::fsqr(out, f1, tmp) }
else
{ crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fsqr::fsqr_e(tmp, f1, out)) }

fn fsqr2(out: &mut [u64], f: &mut [u64], tmp: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fsqr_inline::fsqr2(out, f, tmp) }
else
{ crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fsqr::fsqr2_e(tmp, f, out)) }

fn cswap2(bit: u64, p1: &mut [u64], p2: &mut [u64]) -> ()
if crate::evercrypt::targetconfig::hacl_can_compile_inline_asm
{ crate::vale::inline_x64_fswap_inline::cswap2(bit, p1, p2) }
else
{
    crate::lowstar::ignore::ignore::<u64>(crate::vale::stdcalls_x64_fswap::cswap2_e(bit, p1, p2))
}

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

fn point_add_and_double(q: &mut [u64], p01_tmp1: &mut [u64], tmp2: &mut [u64]) -> ()
{
    let nq: (&mut [u64], &mut [u64]) = p01_tmp1.split_at_mut(0usize);
    let nq_p1: (&mut [u64], &mut [u64]) = nq.1.split_at_mut(8usize);
    let tmp1: (&mut [u64], &mut [u64]) = nq_p1.1.split_at_mut(8usize);
    let x1: (&mut [u64], &mut [u64]) = q.split_at_mut(0usize);
    let x2: (&mut [u64], &mut [u64]) = nq_p1.0.split_at_mut(0usize);
    let z2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let z3: (&mut [u64], &mut [u64]) = tmp1.0.split_at_mut(4usize);
    let a: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(0usize);
    let b: (&mut [u64], &mut [u64]) = a.1.split_at_mut(4usize);
    let ab: (&mut [u64], &mut [u64]) = b.0.split_at_mut(0usize);
    let dc: (&mut [u64], &mut [u64]) = b.1.split_at_mut(4usize);
    fadd(ab.0, z2.0, z2.1);
    fsub(dc.0, z2.0, z2.1);
    let x3: (&mut [u64], &mut [u64]) = z3.0.split_at_mut(0usize);
    let z31: (&mut [u64], &mut [u64]) = z3.1.split_at_mut(0usize);
    let d: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c: (&mut [u64], &mut [u64]) = d.1.split_at_mut(4usize);
    fadd(c.1, x3.1, z31.1);
    fsub(c.0, x3.1, z31.1);
    let mut dc_copy: [u64; 8] = [0u64; 8usize];
    ((&mut dc_copy)[0usize..0usize + 8usize]).copy_from_slice(&c.0[0usize..0usize + 8usize]);
    fmul2(c.0, &mut dc_copy, ab.1, tmp2);
    fadd(x3.1, c.0, c.1);
    fsub(z31.1, c.0, c.1);
    let a1: (&mut [u64], &mut [u64]) = ab.1.split_at_mut(0usize);
    let b1: (&mut [u64], &mut [u64]) = dc.0.split_at_mut(0usize);
    let d0: (&mut [u64], &mut [u64]) = dc.1.split_at_mut(0usize);
    let c0: (&mut [u64], &mut [u64]) = d0.1.split_at_mut(4usize);
    let ab1: (&mut [u64], &mut [u64]) = a1.1.split_at_mut(0usize);
    let dc1: (&mut [u64], &mut [u64]) = c0.0.split_at_mut(0usize);
    fsqr2(dc1.1, ab1.1, tmp2);
    let mut nq_p1_copy: [u64; 8] = [0u64; 8usize];
    ((&mut nq_p1_copy)[0usize..0usize + 8usize]).copy_from_slice(&x3.1[0usize..0usize + 8usize]);
    fsqr2(x3.1, &mut nq_p1_copy, tmp2);
    ab1.0[0usize] = c0.1[0usize];
    ab1.0[1usize] = c0.1[1usize];
    ab1.0[2usize] = c0.1[2usize];
    ab1.0[3usize] = c0.1[3usize];
    fsub(c0.1, dc1.0, c0.1);
    fmul_scalar(b1.1, c0.1, 121665u64);
    fadd(b1.1, b1.1, dc1.0);
    fmul2(z2.0, dc1.1, ab1.1, tmp2);
    fmul(z31.0, z31.0, x1.1, tmp2)
}

fn point_double(nq: &mut [u64], tmp1: &mut [u64], tmp2: &mut [u64]) -> ()
{
    let x2: (&mut [u64], &mut [u64]) = nq.split_at_mut(0usize);
    let z2: (&mut [u64], &mut [u64]) = x2.1.split_at_mut(4usize);
    let a: (&mut [u64], &mut [u64]) = tmp1.split_at_mut(0usize);
    let b: (&mut [u64], &mut [u64]) = a.1.split_at_mut(4usize);
    let d: (&mut [u64], &mut [u64]) = b.1.split_at_mut(4usize);
    let c: (&mut [u64], &mut [u64]) = d.1.split_at_mut(4usize);
    let ab: (&mut [u64], &mut [u64]) = b.0.split_at_mut(0usize);
    let dc: (&mut [u64], &mut [u64]) = c.0.split_at_mut(0usize);
    fadd(ab.0, z2.0, z2.1);
    fsub(d.0, z2.0, z2.1);
    fsqr2(dc.1, ab.1, tmp2);
    ab.0[0usize] = c.1[0usize];
    ab.0[1usize] = c.1[1usize];
    ab.0[2usize] = c.1[2usize];
    ab.0[3usize] = c.1[3usize];
    fsub(c.1, dc.0, c.1);
    fmul_scalar(d.0, c.1, 121665u64);
    fadd(d.0, d.0, dc.0);
    fmul2(z2.0, dc.1, ab.1, tmp2)
}

fn montgomery_ladder(out: &mut [u64], key: &mut [u8], init: &mut [u64]) -> ()
{
    let mut tmp2: [u64; 16] = [0u64; 16usize];
    let mut p01_tmp1_swap: [u64; 33] = [0u64; 33usize];
    let p0: (&mut [u64], &mut [u64]) = (&mut p01_tmp1_swap).split_at_mut(0usize);
    let p01: (&mut [u64], &mut [u64]) = p0.1.split_at_mut(0usize);
    let p03: (&mut [u64], &mut [u64]) = p01.1.split_at_mut(0usize);
    let p11: (&mut [u64], &mut [u64]) = p03.1.split_at_mut(8usize);
    (p11.1[0usize..0usize + 8usize]).copy_from_slice(&init[0usize..0usize + 8usize]);
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
    let p01_tmp1: (&mut [u64], &mut [u64]) = p01.1.split_at_mut(0usize);
    let p01_tmp11: (&mut [u64], &mut [u64]) = p01_tmp1.1.split_at_mut(0usize);
    let nq1: (&mut [u64], &mut [u64]) = p01_tmp11.1.split_at_mut(0usize);
    let nq_p11: (&mut [u64], &mut [u64]) = nq1.1.split_at_mut(8usize);
    let swap: (&mut [u64], &mut [u64]) = nq_p11.1.split_at_mut(24usize);
    cswap2(1u64, nq_p11.0, swap.0);
    point_add_and_double(init, nq1.0, &mut tmp2);
    swap.1[0usize] = 1u64;
    for i in 0u32..251u32
    {
        let p01_tmp12: (&mut [u64], &mut [u64]) = nq_p11.0.split_at_mut(0usize);
        let swap1: (&mut [u64], &mut [u64]) = swap.1.split_at_mut(0usize);
        let nq2: (&mut [u64], &mut [u64]) = p01_tmp12.1.split_at_mut(0usize);
        let nq_p12: (&mut [u64], &mut [u64]) = nq2.1.split_at_mut(8usize);
        let bit: u64 =
            ((key[253u32.wrapping_sub(i).wrapping_div(8u32) as usize]).wrapping_shr(
                253u32.wrapping_sub(i).wrapping_rem(8u32)
            )
            &
            1u8)
            as
            u64;
        let sw: u64 = swap1.1[0usize] ^ bit;
        cswap2(sw, nq_p12.0, nq_p12.1);
        point_add_and_double(init, nq_p12.0, &mut tmp2);
        swap1.1[0usize] = bit
    };
    let sw: u64 = swap.1[0usize];
    cswap2(sw, nq_p11.0, swap.0);
    let nq10: (&mut [u64], &mut [u64]) = p01_tmp11.0.split_at_mut(0usize);
    let tmp1: (&mut [u64], &mut [u64]) = nq10.1.split_at_mut(16usize);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    point_double(tmp1.0, tmp1.1, &mut tmp2);
    (out[0usize..0usize + 8usize]).copy_from_slice(&p01.0[0usize..0usize + 8usize])
}

fn fsquare_times(o: &mut [u64], inp: &mut [u64], tmp: &mut [u64], n: u32) -> ()
{
    fsqr(o, inp, tmp);
    for i in 0u32..n.wrapping_sub(1u32) { fsqr(o, o, tmp) }
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
    fmul(t01.0, t01.1, i, tmp1.1);
    fmul(b1.0, t01.0, b1.0, tmp1.1);
    fsquare_times(t01.1, b1.0, tmp1.1, 1u32);
    fmul(t01.0, t01.1, t01.0, tmp1.1);
    fsquare_times(t01.1, t01.0, tmp1.1, 5u32);
    fmul(t01.0, t01.1, t01.0, tmp1.1);
    let b10: (&mut [u64], &mut [u64]) = t01.0.split_at_mut(0usize);
    let c1: (&mut [u64], &mut [u64]) = b10.1.split_at_mut(4usize);
    let t010: (&mut [u64], &mut [u64]) = t01.1.split_at_mut(0usize);
    let tmp10: (&mut [u64], &mut [u64]) = tmp1.1.split_at_mut(0usize);
    fsquare_times(t010.1, c1.0, tmp10.1, 10u32);
    fmul(c1.1, t010.1, c1.0, tmp10.0);
    fsquare_times(t010.1, c1.1, tmp10.1, 20u32);
    fmul(t010.1, t010.1, c1.1, tmp10.0);
    fsquare_times(t010.1, t010.1, tmp10.1, 10u32);
    fmul(c1.0, t010.1, c1.0, tmp10.0);
    fsquare_times(t010.1, c1.0, tmp10.1, 50u32);
    fmul(c1.1, t010.1, c1.0, tmp10.0);
    let b11: (&mut [u64], &mut [u64]) = c1.0.split_at_mut(0usize);
    let c10: (&mut [u64], &mut [u64]) = c1.1.split_at_mut(0usize);
    let t011: (&mut [u64], &mut [u64]) = t010.1.split_at_mut(0usize);
    let tmp11: (&mut [u64], &mut [u64]) = tmp10.1.split_at_mut(0usize);
    fsquare_times(t011.1, c10.1, tmp11.1, 100u32);
    fmul(t011.1, t011.1, c10.1, tmp10.0);
    fsquare_times(t011.1, t011.1, tmp11.1, 50u32);
    fmul(t011.1, t011.1, b11.1, tmp10.0);
    fsquare_times(t011.1, t011.1, tmp11.1, 5u32);
    let a: (&mut [u64], &mut [u64]) = b1.0.split_at_mut(0usize);
    let t0: (&mut [u64], &mut [u64]) = t011.1.split_at_mut(0usize);
    fmul(o, t0.1, a.1, tmp10.0)
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
    let f0_: u64 = f0.wrapping_sub(mask & 0xffffffffffffffedu64);
    let f1_: u64 = f1.wrapping_sub(mask & 0xffffffffffffffffu64);
    let f2_: u64 = f2.wrapping_sub(mask & 0xffffffffffffffffu64);
    let f3_: u64 = f31.wrapping_sub(mask & 0x7fffffffffffffffu64);
    let o0: u64 = f0_;
    let o1: u64 = f1_;
    let o2: u64 = f2_;
    let o3: u64 = f3_;
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
    fmul(&mut tmp, &mut tmp, z.0, &mut tmp_w);
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
    let mut tmp: [u64; 4] = [0u64; 4usize];
    for i in 0u32..4u32
    {
        let os: (&mut [u64], &mut [u64]) = (&mut tmp).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) =
            r#pub.split_at_mut((i.wrapping_mul(8u32) as usize).wrapping_add(0usize));
        let u: u64 = crate::lowstar::endianness::load64_le(bj.1);
        let r: u64 = u;
        let x: u64 = r;
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
    montgomery_ladder(z.0, r#priv, z.0);
    encode_point(out, z.0)
}

pub fn secret_to_public(r#pub: &mut [u8], r#priv: &mut [u8]) -> ()
{
    let mut basepoint: [u8; 32] = [0u8; 32usize];
    for i in 0u32..32u32
    {
        let os: (&mut [u8], &mut [u8]) = (&mut basepoint).split_at_mut(0usize);
        let x: u8 = (&g25519)[i as usize];
        os.1[i as usize] = x
    };
    scalarmult(r#pub, r#priv, &mut basepoint)
}

pub fn ecdh(out: &mut [u8], r#priv: &mut [u8], r#pub: &mut [u8]) -> bool
{
    let mut zeros: [u8; 32] = [0u8; 32usize];
    scalarmult(out, r#priv, r#pub);
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
