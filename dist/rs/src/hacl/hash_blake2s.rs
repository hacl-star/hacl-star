#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn update_block(
    wv: &mut [u32],
    hash: &mut [u32],
    flag: bool,
    totlen: u64,
    d: &mut [u8]
) ->
    ()
{
    let mut m_w: [u32; 16] = [0u32; 16usize];
    for i in 0u32..16u32
    {
        let bj: (&mut [u8], &mut [u8]) = d.split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        let os: (&mut [u32], &mut [u32]) = (&mut m_w).split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let mut mask: [u32; 4] = [0u32; 4usize];
    let wv_14: u32 = if flag { 0xFFFFFFFFu32 } else { 0u32 };
    let wv_15: u32 = 0u32;
    (&mut mask)[0usize] = totlen as u32;
    (&mut mask)[1usize] = totlen.wrapping_shr(32u32) as u32;
    (&mut mask)[2usize] = wv_14;
    (&mut mask)[3usize] = wv_15;
    (wv[0usize..16usize]).copy_from_slice(&hash[0usize..16usize]);
    let wv3: (&mut [u32], &mut [u32]) = wv.split_at_mut(12usize);
    for i in 0u32..4u32
    {
        let x: u32 = wv3.1[i as usize] ^ (&mut mask)[i as usize];
        let os: (&mut [u32], &mut [u32]) = wv3.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    for i in 0u32..10u32
    {
        let start_idx: u32 = i.wrapping_rem(10u32).wrapping_mul(16u32);
        let mut m_st: [u32; 16] = [0u32; 16usize];
        let r0: (&mut [u32], &mut [u32]) = (&mut m_st).split_at_mut(0usize);
        let r1: (&mut [u32], &mut [u32]) = r0.1.split_at_mut(4usize);
        let r2: (&mut [u32], &mut [u32]) = r1.1.split_at_mut(4usize);
        let r3: (&mut [u32], &mut [u32]) = r2.1.split_at_mut(4usize);
        let s0: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(0u32) as usize];
        let s1: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(1u32) as usize];
        let s2: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(2u32) as usize];
        let s3: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(3u32) as usize];
        let s4: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(4u32) as usize];
        let s5: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(5u32) as usize];
        let s6: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(6u32) as usize];
        let s7: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(7u32) as usize];
        let s8: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(8u32) as usize];
        let s9: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(9u32) as usize];
        let s10: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(10u32) as usize];
        let s11: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(11u32) as usize];
        let s12: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(12u32) as usize];
        let s13: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(13u32) as usize];
        let s14: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(14u32) as usize];
        let s15: u32 =
            (&crate::hacl::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(15u32) as usize];
        let uu____0: u32 = (&mut m_w)[s2 as usize];
        let uu____1: u32 = (&mut m_w)[s4 as usize];
        let uu____2: u32 = (&mut m_w)[s6 as usize];
        r1.0[0usize] = (&mut m_w)[s0 as usize];
        r1.0[1usize] = uu____0;
        r1.0[2usize] = uu____1;
        r1.0[3usize] = uu____2;
        let uu____3: u32 = (&mut m_w)[s3 as usize];
        let uu____4: u32 = (&mut m_w)[s5 as usize];
        let uu____5: u32 = (&mut m_w)[s7 as usize];
        r2.0[0usize] = (&mut m_w)[s1 as usize];
        r2.0[1usize] = uu____3;
        r2.0[2usize] = uu____4;
        r2.0[3usize] = uu____5;
        let uu____6: u32 = (&mut m_w)[s10 as usize];
        let uu____7: u32 = (&mut m_w)[s12 as usize];
        let uu____8: u32 = (&mut m_w)[s14 as usize];
        r3.0[0usize] = (&mut m_w)[s8 as usize];
        r3.0[1usize] = uu____6;
        r3.0[2usize] = uu____7;
        r3.0[3usize] = uu____8;
        let uu____9: u32 = (&mut m_w)[s11 as usize];
        let uu____10: u32 = (&mut m_w)[s13 as usize];
        let uu____11: u32 = (&mut m_w)[s15 as usize];
        r3.1[0usize] = (&mut m_w)[s9 as usize];
        r3.1[1usize] = uu____9;
        r3.1[2usize] = uu____10;
        r3.1[3usize] = uu____11;
        let x: (&mut [u32], &mut [u32]) = r1.0.split_at_mut(0usize);
        let y: (&mut [u32], &mut [u32]) = r2.0.split_at_mut(0usize);
        let z: (&mut [u32], &mut [u32]) = r3.0.split_at_mut(0usize);
        let w: (&mut [u32], &mut [u32]) = r3.1.split_at_mut(0usize);
        let wv_a: (&mut [u32], &mut [u32]) = wv3.0.split_at_mut(0usize);
        let wv_b: (&mut [u32], &mut [u32]) = wv_a.1.split_at_mut(4usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = (wv_b.0[i0 as usize]).wrapping_add(wv_b.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_b.0.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        for i0 in 0u32..4u32
        {
            let x1: u32 = (wv_b.0[i0 as usize]).wrapping_add(x.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_b.0.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let wv_a0: (&mut [u32], &mut [u32]) = wv3.1.split_at_mut(0usize);
        let wv_b0: (&mut [u32], &mut [u32]) = wv_b.0.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = wv_a0.1[i0 as usize] ^ wv_b0.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a0.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let r10: &mut [u32] = wv_a0.1;
        for i0 in 0u32..4u32
        {
            let x1: u32 = r10[i0 as usize];
            let x10: u32 = x1.wrapping_shr(16u32) | x1.wrapping_shl(16u32);
            let os: (&mut [u32], &mut [u32]) = r10.split_at_mut(0usize);
            os.1[i0 as usize] = x10
        };
        let wv_a1: (&mut [u32], &mut [u32]) = wv_b.1.split_at_mut(4usize);
        let wv_b1: (&mut [u32], &mut [u32]) = wv_a0.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = (wv_a1.1[i0 as usize]).wrapping_add(wv_b1.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a1.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let wv_a2: (&mut [u32], &mut [u32]) = wv_a1.0.split_at_mut(0usize);
        let wv_b2: (&mut [u32], &mut [u32]) = wv_a1.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = wv_a2.1[i0 as usize] ^ wv_b2.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a2.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let r11: &mut [u32] = wv_a2.1;
        for i0 in 0u32..4u32
        {
            let x1: u32 = r11[i0 as usize];
            let x10: u32 = x1.wrapping_shr(12u32) | x1.wrapping_shl(20u32);
            let os: (&mut [u32], &mut [u32]) = r11.split_at_mut(0usize);
            os.1[i0 as usize] = x10
        };
        let wv_a3: (&mut [u32], &mut [u32]) = wv_b0.1.split_at_mut(0usize);
        let wv_b3: (&mut [u32], &mut [u32]) = wv_a2.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = (wv_a3.1[i0 as usize]).wrapping_add(wv_b3.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a3.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        for i0 in 0u32..4u32
        {
            let x1: u32 = (wv_a3.1[i0 as usize]).wrapping_add(y.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a3.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let wv_a4: (&mut [u32], &mut [u32]) = wv_b1.1.split_at_mut(0usize);
        let wv_b4: (&mut [u32], &mut [u32]) = wv_a3.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = wv_a4.1[i0 as usize] ^ wv_b4.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a4.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let r12: &mut [u32] = wv_a4.1;
        for i0 in 0u32..4u32
        {
            let x1: u32 = r12[i0 as usize];
            let x10: u32 = x1.wrapping_shr(8u32) | x1.wrapping_shl(24u32);
            let os: (&mut [u32], &mut [u32]) = r12.split_at_mut(0usize);
            os.1[i0 as usize] = x10
        };
        let wv_a5: (&mut [u32], &mut [u32]) = wv_b2.1.split_at_mut(0usize);
        let wv_b5: (&mut [u32], &mut [u32]) = wv_a4.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = (wv_a5.1[i0 as usize]).wrapping_add(wv_b5.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a5.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let wv_a6: (&mut [u32], &mut [u32]) = wv_b3.1.split_at_mut(0usize);
        let wv_b6: (&mut [u32], &mut [u32]) = wv_a5.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x1: u32 = wv_a6.1[i0 as usize] ^ wv_b6.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a6.1.split_at_mut(0usize);
            os.1[i0 as usize] = x1
        };
        let r13: &mut [u32] = wv_a6.1;
        for i0 in 0u32..4u32
        {
            let x1: u32 = r13[i0 as usize];
            let x10: u32 = x1.wrapping_shr(7u32) | x1.wrapping_shl(25u32);
            let os: (&mut [u32], &mut [u32]) = r13.split_at_mut(0usize);
            os.1[i0 as usize] = x10
        };
        let r14: (&mut [u32], &mut [u32]) = wv_a6.1.split_at_mut(0usize);
        let r20: (&mut [u32], &mut [u32]) = wv_b6.1.split_at_mut(0usize);
        let r30: (&mut [u32], &mut [u32]) = wv_b5.1.split_at_mut(0usize);
        let r110: &mut [u32] = r14.1;
        let x0: u32 = r110[1usize];
        let x1: u32 = r110[2usize];
        let x2: u32 = r110[3usize];
        let x3: u32 = r110[0usize];
        r110[0usize] = x0;
        r110[1usize] = x1;
        r110[2usize] = x2;
        r110[3usize] = x3;
        let r111: &mut [u32] = r20.1;
        let x00: u32 = r111[2usize];
        let x10: u32 = r111[3usize];
        let x20: u32 = r111[0usize];
        let x30: u32 = r111[1usize];
        r111[0usize] = x00;
        r111[1usize] = x10;
        r111[2usize] = x20;
        r111[3usize] = x30;
        let r112: &mut [u32] = r30.1;
        let x01: u32 = r112[3usize];
        let x11: u32 = r112[0usize];
        let x21: u32 = r112[1usize];
        let x31: u32 = r112[2usize];
        r112[0usize] = x01;
        r112[1usize] = x11;
        r112[2usize] = x21;
        r112[3usize] = x31;
        let wv_a7: (&mut [u32], &mut [u32]) = wv_b4.1.split_at_mut(0usize);
        let wv_b7: (&mut [u32], &mut [u32]) = r14.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = (wv_a7.1[i0 as usize]).wrapping_add(wv_b7.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a7.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        for i0 in 0u32..4u32
        {
            let x12: u32 = (wv_a7.1[i0 as usize]).wrapping_add(z.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a7.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let wv_a8: (&mut [u32], &mut [u32]) = r30.1.split_at_mut(0usize);
        let wv_b8: (&mut [u32], &mut [u32]) = wv_a7.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = wv_a8.1[i0 as usize] ^ wv_b8.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a8.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let r15: &mut [u32] = wv_a8.1;
        for i0 in 0u32..4u32
        {
            let x12: u32 = r15[i0 as usize];
            let x13: u32 = x12.wrapping_shr(16u32) | x12.wrapping_shl(16u32);
            let os: (&mut [u32], &mut [u32]) = r15.split_at_mut(0usize);
            os.1[i0 as usize] = x13
        };
        let wv_a9: (&mut [u32], &mut [u32]) = r20.1.split_at_mut(0usize);
        let wv_b9: (&mut [u32], &mut [u32]) = wv_a8.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = (wv_a9.1[i0 as usize]).wrapping_add(wv_b9.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a9.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let wv_a10: (&mut [u32], &mut [u32]) = wv_b7.1.split_at_mut(0usize);
        let wv_b10: (&mut [u32], &mut [u32]) = wv_a9.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = wv_a10.1[i0 as usize] ^ wv_b10.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a10.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let r16: &mut [u32] = wv_a10.1;
        for i0 in 0u32..4u32
        {
            let x12: u32 = r16[i0 as usize];
            let x13: u32 = x12.wrapping_shr(12u32) | x12.wrapping_shl(20u32);
            let os: (&mut [u32], &mut [u32]) = r16.split_at_mut(0usize);
            os.1[i0 as usize] = x13
        };
        let wv_a11: (&mut [u32], &mut [u32]) = wv_b8.1.split_at_mut(0usize);
        let wv_b11: (&mut [u32], &mut [u32]) = wv_a10.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = (wv_a11.1[i0 as usize]).wrapping_add(wv_b11.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a11.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        for i0 in 0u32..4u32
        {
            let x12: u32 = (wv_a11.1[i0 as usize]).wrapping_add(w.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a11.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let wv_a12: (&mut [u32], &mut [u32]) = wv_b9.1.split_at_mut(0usize);
        let wv_b12: (&mut [u32], &mut [u32]) = wv_a11.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = wv_a12.1[i0 as usize] ^ wv_b12.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a12.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let r17: &mut [u32] = wv_a12.1;
        for i0 in 0u32..4u32
        {
            let x12: u32 = r17[i0 as usize];
            let x13: u32 = x12.wrapping_shr(8u32) | x12.wrapping_shl(24u32);
            let os: (&mut [u32], &mut [u32]) = r17.split_at_mut(0usize);
            os.1[i0 as usize] = x13
        };
        let wv_a13: (&mut [u32], &mut [u32]) = wv_b10.1.split_at_mut(0usize);
        let wv_b13: (&mut [u32], &mut [u32]) = wv_a12.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = (wv_a13.1[i0 as usize]).wrapping_add(wv_b13.1[i0 as usize]);
            let os: (&mut [u32], &mut [u32]) = wv_a13.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let wv_a14: (&mut [u32], &mut [u32]) = wv_b11.1.split_at_mut(0usize);
        let wv_b14: (&mut [u32], &mut [u32]) = wv_a13.1.split_at_mut(0usize);
        for i0 in 0u32..4u32
        {
            let x12: u32 = wv_a14.1[i0 as usize] ^ wv_b14.1[i0 as usize];
            let os: (&mut [u32], &mut [u32]) = wv_a14.1.split_at_mut(0usize);
            os.1[i0 as usize] = x12
        };
        let r18: &mut [u32] = wv_a14.1;
        for i0 in 0u32..4u32
        {
            let x12: u32 = r18[i0 as usize];
            let x13: u32 = x12.wrapping_shr(7u32) | x12.wrapping_shl(25u32);
            let os: (&mut [u32], &mut [u32]) = r18.split_at_mut(0usize);
            os.1[i0 as usize] = x13
        };
        let r19: (&mut [u32], &mut [u32]) = wv_a14.1.split_at_mut(0usize);
        let r21: (&mut [u32], &mut [u32]) = wv_b14.1.split_at_mut(0usize);
        let r31: (&mut [u32], &mut [u32]) = wv_b13.1.split_at_mut(0usize);
        let r113: &mut [u32] = r19.1;
        let x02: u32 = r113[3usize];
        let x12: u32 = r113[0usize];
        let x22: u32 = r113[1usize];
        let x32: u32 = r113[2usize];
        r113[0usize] = x02;
        r113[1usize] = x12;
        r113[2usize] = x22;
        r113[3usize] = x32;
        let r114: &mut [u32] = r21.1;
        let x03: u32 = r114[2usize];
        let x13: u32 = r114[3usize];
        let x23: u32 = r114[0usize];
        let x33: u32 = r114[1usize];
        r114[0usize] = x03;
        r114[1usize] = x13;
        r114[2usize] = x23;
        r114[3usize] = x33;
        let r115: &mut [u32] = r31.1;
        let x04: u32 = r115[1usize];
        let x14: u32 = r115[2usize];
        let x24: u32 = r115[3usize];
        let x34: u32 = r115[0usize];
        r115[0usize] = x04;
        r115[1usize] = x14;
        r115[2usize] = x24;
        r115[3usize] = x34
    };
    let s0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let s1: (&mut [u32], &mut [u32]) = s0.1.split_at_mut(4usize);
    let r0: (&mut [u32], &mut [u32]) = wv3.0.split_at_mut(0usize);
    let r1: (&mut [u32], &mut [u32]) = r0.1.split_at_mut(4usize);
    let r2: (&mut [u32], &mut [u32]) = r1.1.split_at_mut(4usize);
    let r3: (&mut [u32], &mut [u32]) = wv3.1.split_at_mut(0usize);
    for i in 0u32..4u32
    {
        let x: u32 = s1.0[i as usize] ^ r1.0[i as usize];
        let os: (&mut [u32], &mut [u32]) = s1.0.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    for i in 0u32..4u32
    {
        let x: u32 = s1.0[i as usize] ^ r2.1[i as usize];
        let os: (&mut [u32], &mut [u32]) = s1.0.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    for i in 0u32..4u32
    {
        let x: u32 = s1.1[i as usize] ^ r2.0[i as usize];
        let os: (&mut [u32], &mut [u32]) = s1.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    for i in 0u32..4u32
    {
        let x: u32 = s1.1[i as usize] ^ r3.1[i as usize];
        let os: (&mut [u32], &mut [u32]) = s1.1.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

pub fn init(hash: &mut [u32], kk: u32, nn: u32) -> ()
{
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let r0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let r1: (&mut [u32], &mut [u32]) = r0.1.split_at_mut(4usize);
    let r2: (&mut [u32], &mut [u32]) = r1.1.split_at_mut(4usize);
    let r3: (&mut [u32], &mut [u32]) = r2.1.split_at_mut(4usize);
    let iv0: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[0usize];
    let iv1: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[1usize];
    let iv2: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[2usize];
    let iv3: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[3usize];
    let iv4: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[4usize];
    let iv5: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[5usize];
    let iv6: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[6usize];
    let iv7: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[7usize];
    r3.0[0usize] = iv0;
    r3.0[1usize] = iv1;
    r3.0[2usize] = iv2;
    r3.0[3usize] = iv3;
    r3.1[0usize] = iv4;
    r3.1[1usize] = iv5;
    r3.1[2usize] = iv6;
    r3.1[3usize] = iv7;
    let mut salt: [u8; 8] = [0u8; 8usize];
    let mut personal: [u8; 8] = [0u8; 8usize];
    let p: crate::hacl::hash_blake2b::blake2s_params =
        crate::hacl::hash_blake2b::blake2s_params
        {
            digest_length: 32u8,
            key_length: 0u8,
            fanout: 1u8,
            depth: 1u8,
            leaf_length: 0u32,
            node_offset: 0u32,
            xof_length: 0u16,
            node_depth: 0u8,
            inner_length: 0u8,
            salt: &mut salt,
            personal: &mut personal
        };
    let uu____0: (&mut [u32], &mut [u32]) = (&mut tmp).split_at_mut(4usize);
    for i in 0u32..2u32
    {
        let bj: &mut [u8] = &mut p.salt[i.wrapping_mul(4u32) as usize..];
        let u: u32 = crate::lowstar::endianness::load32_le(bj);
        let r: u32 = u;
        let x: u32 = r;
        let os: (&mut [u32], &mut [u32]) = uu____0.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    let uu____1: (&mut [u32], &mut [u32]) = uu____0.1.split_at_mut(2usize);
    for i in 0u32..2u32
    {
        let bj: &mut [u8] = &mut p.personal[i.wrapping_mul(4u32) as usize..];
        let u: u32 = crate::lowstar::endianness::load32_le(bj);
        let r: u32 = u;
        let x: u32 = r;
        let os: (&mut [u32], &mut [u32]) = uu____1.1.split_at_mut(0usize);
        os.1[i as usize] = x
    };
    (&mut tmp)[0usize] =
        nn
        ^
        (kk.wrapping_shl(8u32)
        ^
        ((p.fanout as u32).wrapping_shl(16u32) ^ (p.depth as u32).wrapping_shl(24u32)));
    (&mut tmp)[1usize] = p.leaf_length;
    (&mut tmp)[2usize] = p.node_offset;
    (&mut tmp)[3usize] =
        p.xof_length as u32
        ^
        ((p.node_depth as u32).wrapping_shl(16u32) ^ (p.inner_length as u32).wrapping_shl(24u32));
    let tmp0: u32 = (&mut tmp)[0usize];
    let tmp1: u32 = (&mut tmp)[1usize];
    let tmp2: u32 = (&mut tmp)[2usize];
    let tmp3: u32 = (&mut tmp)[3usize];
    let tmp4: u32 = (&mut tmp)[4usize];
    let tmp5: u32 = (&mut tmp)[5usize];
    let tmp6: u32 = (&mut tmp)[6usize];
    let tmp7: u32 = (&mut tmp)[7usize];
    let iv0·: u32 = iv0 ^ tmp0;
    let iv1·: u32 = iv1 ^ tmp1;
    let iv2·: u32 = iv2 ^ tmp2;
    let iv3·: u32 = iv3 ^ tmp3;
    let iv4·: u32 = iv4 ^ tmp4;
    let iv5·: u32 = iv5 ^ tmp5;
    let iv6·: u32 = iv6 ^ tmp6;
    let iv7·: u32 = iv7 ^ tmp7;
    r1.0[0usize] = iv0·;
    r1.0[1usize] = iv1·;
    r1.0[2usize] = iv2·;
    r1.0[3usize] = iv3·;
    r2.0[0usize] = iv4·;
    r2.0[1usize] = iv5·;
    r2.0[2usize] = iv6·;
    r2.0[3usize] = iv7·
}

fn update_key(wv: &mut [u32], hash: &mut [u32], kk: u32, k: &mut [u8], ll: u32) -> ()
{
    let lb: u64 = 64u32 as u64;
    let mut b: [u8; 64] = [0u8; 64usize];
    ((&mut b)[0usize..kk as usize]).copy_from_slice(&k[0usize..kk as usize]);
    if ll == 0u32
    { update_block(wv, hash, true, lb, &mut b) }
    else
    { update_block(wv, hash, false, lb, &mut b) };
    crate::lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

pub fn update_multi(
    len: u32,
    wv: &mut [u32],
    hash: &mut [u32],
    prev: u64,
    blocks: &mut [u8],
    nb: u32
) ->
    ()
{
    crate::lowstar::ignore::ignore::<u32>(len);
    for i in 0u32..nb
    {
        let totlen: u64 = prev.wrapping_add(i.wrapping_add(1u32).wrapping_mul(64u32) as u64);
        let b: (&mut [u8], &mut [u8]) = blocks.split_at_mut(i.wrapping_mul(64u32) as usize);
        update_block(wv, hash, false, totlen, b.1)
    }
}

pub fn update_last(
    len: u32,
    wv: &mut [u32],
    hash: &mut [u32],
    prev: u64,
    rem: u32,
    d: &mut [u8]
) ->
    ()
{
    let mut b: [u8; 64] = [0u8; 64usize];
    let last: (&mut [u8], &mut [u8]) = d.split_at_mut(len.wrapping_sub(rem) as usize);
    ((&mut b)[0usize..rem as usize]).copy_from_slice(&last.1[0usize..rem as usize]);
    let totlen: u64 = prev.wrapping_add(len as u64);
    update_block(wv, hash, true, totlen, &mut b);
    crate::lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

fn update_blocks(len: u32, wv: &mut [u32], hash: &mut [u32], prev: u64, blocks: &mut [u8]) ->
    ()
{
    let nb: u32 = len.wrapping_div(64u32);
    let rem: u32 = len.wrapping_rem(64u32);
    let nb0: u32 = if rem == 0u32 && nb > 0u32 { nb.wrapping_sub(1u32) } else { nb };
    let rem0: u32 = if rem == 0u32 && nb > 0u32 { 64u32 } else { rem };
    update_multi(len, wv, hash, prev, blocks, nb0);
    update_last(len, wv, hash, prev, rem0, blocks)
}

#[inline] fn update(
    wv: &mut [u32],
    hash: &mut [u32],
    kk: u32,
    k: &mut [u8],
    ll: u32,
    d: &mut [u8]
) ->
    ()
{
    let lb: u64 = 64u32 as u64;
    if kk > 0u32
    {
        update_key(wv, hash, kk, k, ll);
        if ! (ll == 0u32) { update_blocks(ll, wv, hash, lb, d) }
    }
    else
    { update_blocks(ll, wv, hash, 0u32 as u64, d) }
}

pub fn finish(nn: u32, output: &mut [u8], hash: &mut [u32]) -> ()
{
    let mut b: [u8; 32] = [0u8; 32usize];
    let first: (&mut [u8], &mut [u8]) = (&mut b).split_at_mut(0usize);
    let second: (&mut [u8], &mut [u8]) = first.1.split_at_mut(16usize);
    let row0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let row1: (&mut [u32], &mut [u32]) = row0.1.split_at_mut(4usize);
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store32_le(
            &mut second.0[i.wrapping_mul(4u32) as usize..],
            row1.0[i as usize]
        )
    };
    for i in 0u32..4u32
    {
        crate::lowstar::endianness::store32_le(
            &mut second.1[i.wrapping_mul(4u32) as usize..],
            row1.1[i as usize]
        )
    };
    crate::lowstar::ignore::ignore::<&mut [u8]>(&mut b);
    let r#final: (&mut [u8], &mut [u8]) = (&mut b).split_at_mut(0usize);
    (output[0usize..nn as usize]).copy_from_slice(&r#final.1[0usize..nn as usize]);
    crate::lib::memzero0::memzero::<u8>(&mut b, 32u32)
}

pub struct block_state_t { pub fst: Vec<u32>, pub snd: Vec<u32> }

pub struct state_t { pub block_state: block_state_t, pub buf: Vec<u8>, pub total_len: u64 }

pub fn malloc() -> Vec<state_t>
{
    let mut buf: Vec<u8> = vec![0u8; 64usize];
    let mut wv: Vec<u32> = vec![0u32; 16usize];
    let mut b: Vec<u32> = vec![0u32; 16usize];
    let mut block_state: block_state_t = block_state_t { fst: wv, snd: b };
    init(&mut block_state.snd, 0u32, 32u32);
    let mut s: state_t = state_t { block_state: block_state, buf: buf, total_len: 0u32 as u64 };
    let mut p: Vec<state_t> =
        {
            let mut tmp: Vec<state_t> = Vec::new();
            tmp.push(s);
            tmp
        };
    p
}

pub fn reset(state: &mut [state_t]) -> ()
{
    let mut block_state: &mut block_state_t = &mut (state[0usize]).block_state;
    init(&mut (*block_state).snd, 0u32, 32u32);
    (state[0usize]).total_len = 0u32 as u64
}

pub fn update0(state: &mut [state_t], chunk: &mut [u8], chunk_len: u32) ->
    crate::hacl::streaming_types::error_code
{
    let mut block_state: &mut block_state_t = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 0xffffffffffffffffu64.wrapping_sub(total_len)
    { crate::hacl::streaming_types::error_code::MaximumLengthExceeded }
    else
    {
        let sz: u32 =
            if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
            { 64u32 }
            else
            { total_len.wrapping_rem(64u32 as u64) as u32 };
        if chunk_len <= 64u32.wrapping_sub(sz)
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..chunk_len as usize]).copy_from_slice(&chunk[0usize..chunk_len as usize]);
            let total_len2: u64 = total_len1.wrapping_add(chunk_len as u64);
            (state[0usize]).total_len = total_len2
        }
        else
        if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz1 == 0u32)
            {
                let prevlen: u64 = total_len1.wrapping_sub(sz1 as u64);
                let wv: &mut [u32] = &mut (*block_state).fst;
                let hash: &mut [u32] = &mut (*block_state).snd;
                let nb: u32 = 1u32;
                update_multi(64u32, wv, hash, prevlen, buf, nb)
            };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(64u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            let wv: &mut [u32] = &mut (*block_state).fst;
            let hash: &mut [u32] = &mut (*block_state).snd;
            let nb: u32 = data1_len.wrapping_div(64u32);
            update_multi(data1_len, wv, hash, total_len1, data2.0, nb);
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = 64u32.wrapping_sub(sz);
            let chunk1: (&mut [u8], &mut [u8]) = chunk.split_at_mut(0usize);
            let chunk2: (&mut [u8], &mut [u8]) = chunk1.1.split_at_mut(diff as usize);
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            let buf2: (&mut [u8], &mut [u8]) = buf.split_at_mut(sz1 as usize);
            (buf2.1[0usize..diff as usize]).copy_from_slice(&chunk2.0[0usize..diff as usize]);
            let total_len2: u64 = total_len1.wrapping_add(diff as u64);
            (state[0usize]).total_len = total_len2;
            let buf0: &mut [u8] = &mut (state[0usize]).buf;
            let total_len10: u64 = (state[0usize]).total_len;
            let sz10: u32 =
                if total_len10.wrapping_rem(64u32 as u64) == 0u64 && total_len10 > 0u64
                { 64u32 }
                else
                { total_len10.wrapping_rem(64u32 as u64) as u32 };
            if ! (sz10 == 0u32)
            {
                let prevlen: u64 = total_len10.wrapping_sub(sz10 as u64);
                let wv: &mut [u32] = &mut (*block_state).fst;
                let hash: &mut [u32] = &mut (*block_state).snd;
                let nb: u32 = 1u32;
                update_multi(64u32, wv, hash, prevlen, buf0, nb)
            };
            let ite: u32 =
                if
                (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(64u32 as u64) == 0u64
                &&
                chunk_len.wrapping_sub(diff) as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len.wrapping_sub(diff) as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(diff).wrapping_sub(data1_len);
            let data1: (&mut [u8], &mut [u8]) = chunk2.1.split_at_mut(0usize);
            let data2: (&mut [u8], &mut [u8]) = data1.1.split_at_mut(data1_len as usize);
            let wv: &mut [u32] = &mut (*block_state).fst;
            let hash: &mut [u32] = &mut (*block_state).snd;
            let nb: u32 = data1_len.wrapping_div(64u32);
            update_multi(data1_len, wv, hash, total_len10, data2.0, nb);
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::hacl::streaming_types::error_code::Success
    }
}

pub fn digest(state: &mut [state_t], output: &mut [u8]) -> ()
{
    let mut block_state: &mut block_state_t = &mut (state[0usize]).block_state;
    let buf_: &mut [u8] = &mut (state[0usize]).buf;
    let total_len: u64 = (state[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&mut [u8], &mut [u8]) = buf_.split_at_mut(0usize);
    let mut wv: [u32; 16] = [0u32; 16usize];
    let mut b: [u32; 16] = [0u32; 16usize];
    let mut tmp_block_state: block_state_t =
        block_state_t { fst: Vec::from(wv), snd: Vec::from(b) };
    let src_b: &mut [u32] = &mut (*block_state).snd;
    let dst_b: &mut [u32] = &mut tmp_block_state.snd;
    (dst_b[0usize..16usize]).copy_from_slice(&src_b[0usize..16usize]);
    let prev_len: u64 = total_len.wrapping_sub(r as u64);
    let buf_multi: (&mut [u8], &mut [u8]) = buf_1.1.split_at_mut(0usize);
    let ite: u32 =
        if r.wrapping_rem(64u32) == 0u32 && r > 0u32 { 64u32 } else { r.wrapping_rem(64u32) };
    let buf_last: (&mut [u8], &mut [u8]) = buf_multi.1.split_at_mut(r.wrapping_sub(ite) as usize);
    let wv0: &mut [u32] = &mut tmp_block_state.fst;
    let hash: &mut [u32] = &mut tmp_block_state.snd;
    let nb: u32 = 0u32;
    update_multi(0u32, wv0, hash, prev_len, buf_last.0, nb);
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    let wv1: &mut [u32] = &mut tmp_block_state.fst;
    let hash0: &mut [u32] = &mut tmp_block_state.snd;
    update_last(r, wv1, hash0, prev_len_last, r, buf_last.1);
    finish(32u32, output, &mut tmp_block_state.snd)
}

pub fn hash_with_key(
    output: &mut [u8],
    output_len: u32,
    input: &mut [u8],
    input_len: u32,
    key: &mut [u8],
    key_len: u32
) ->
    ()
{
    let mut b: [u32; 16] = [0u32; 16usize];
    let mut b1: [u32; 16] = [0u32; 16usize];
    init(&mut b, key_len, output_len);
    update(&mut b1, &mut b, key_len, key, input_len, input);
    finish(output_len, output, &mut b);
    crate::lib::memzero0::memzero::<u32>(&mut b1, 16u32);
    crate::lib::memzero0::memzero::<u32>(&mut b, 16u32)
}
