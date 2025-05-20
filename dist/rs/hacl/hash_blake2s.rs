#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn update_block(
    wv: &mut [u32],
    hash: &mut [u32],
    flag: bool,
    last_node: bool,
    totlen: u64,
    d: &[u8]
)
{
    let mut m_w: [u32; 16] = [0u32; 16usize];
    krml::unroll_for!(
        16,
        "i",
        0u32,
        1u32,
        {
            let bj: (&[u8], &[u8]) = d.split_at(i.wrapping_mul(4u32) as usize);
            let u: u32 = lowstar::endianness::load32_le(bj.1);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = m_w.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let mut mask: [u32; 4] = [0u32; 4usize];
    let wv_14: u32 = if flag { 0xFFFFFFFFu32 } else { 0u32 };
    let wv_15: u32 = if last_node { 0xFFFFFFFFu32 } else { 0u32 };
    (&mut mask)[0usize] = totlen as u32;
    (&mut mask)[1usize] = totlen.wrapping_shr(32u32) as u32;
    (&mut mask)[2usize] = wv_14;
    (&mut mask)[3usize] = wv_15;
    (wv[0usize..16usize]).copy_from_slice(&hash[0usize..16usize]);
    let wv3: (&mut [u32], &mut [u32]) = wv.split_at_mut(12usize);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = wv3.1[i as usize] ^ (&mask)[i as usize];
            let os: (&mut [u32], &mut [u32]) = (wv3.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        10,
        "i",
        0u32,
        1u32,
        {
            let start_idx: u32 = i.wrapping_rem(10u32).wrapping_mul(16u32);
            let mut m_st: [u32; 16] = [0u32; 16usize];
            let r0: (&mut [u32], &mut [u32]) = m_st.split_at_mut(0usize);
            let r1: (&mut [u32], &mut [u32]) = (r0.1).split_at_mut(4usize);
            let r2: (&mut [u32], &mut [u32]) = (r1.1).split_at_mut(4usize);
            let r3: (&mut [u32], &mut [u32]) = (r2.1).split_at_mut(4usize);
            let s0: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(0u32) as usize];
            let s1: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(1u32) as usize];
            let s2: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(2u32) as usize];
            let s3: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(3u32) as usize];
            let s4: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(4u32) as usize];
            let s5: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(5u32) as usize];
            let s6: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(6u32) as usize];
            let s7: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(7u32) as usize];
            let s8: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(8u32) as usize];
            let s9: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(9u32) as usize];
            let s10: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(10u32) as usize];
            let s11: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(11u32) as usize];
            let s12: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(12u32) as usize];
            let s13: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(13u32) as usize];
            let s14: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(14u32) as usize];
            let s15: u32 =
                (&crate::impl_blake2_constants::sigmaTable)[start_idx.wrapping_add(15u32) as usize];
            let uu____0: u32 = (&m_w)[s2 as usize];
            let uu____1: u32 = (&m_w)[s4 as usize];
            let uu____2: u32 = (&m_w)[s6 as usize];
            r1.0[0usize] = (&m_w)[s0 as usize];
            r1.0[1usize] = uu____0;
            r1.0[2usize] = uu____1;
            r1.0[3usize] = uu____2;
            let uu____3: u32 = (&m_w)[s3 as usize];
            let uu____4: u32 = (&m_w)[s5 as usize];
            let uu____5: u32 = (&m_w)[s7 as usize];
            r2.0[0usize] = (&m_w)[s1 as usize];
            r2.0[1usize] = uu____3;
            r2.0[2usize] = uu____4;
            r2.0[3usize] = uu____5;
            let uu____6: u32 = (&m_w)[s10 as usize];
            let uu____7: u32 = (&m_w)[s12 as usize];
            let uu____8: u32 = (&m_w)[s14 as usize];
            r3.0[0usize] = (&m_w)[s8 as usize];
            r3.0[1usize] = uu____6;
            r3.0[2usize] = uu____7;
            r3.0[3usize] = uu____8;
            let uu____9: u32 = (&m_w)[s11 as usize];
            let uu____10: u32 = (&m_w)[s13 as usize];
            let uu____11: u32 = (&m_w)[s15 as usize];
            r3.1[0usize] = (&m_w)[s9 as usize];
            r3.1[1usize] = uu____9;
            r3.1[2usize] = uu____10;
            r3.1[3usize] = uu____11;
            let x: (&[u32], &[u32]) = (r1.0).split_at(0usize);
            let y: (&[u32], &[u32]) = (r2.0).split_at(0usize);
            let z: (&[u32], &[u32]) = (r3.0).split_at(0usize);
            let w: (&[u32], &[u32]) = (r3.1).split_at(0usize);
            let wv_a: (&mut [u32], &mut [u32]) = (wv3.0).split_at_mut(0usize);
            let wv_b: (&mut [u32], &mut [u32]) = (wv_a.1).split_at_mut(4usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = (wv_b.0[i0 as usize]).wrapping_add(wv_b.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_b.0).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = (wv_b.0[i0 as usize]).wrapping_add(x.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_b.0).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let wv_a0: (&mut [u32], &mut [u32]) = (wv3.1).split_at_mut(0usize);
            let wv_b0: (&mut [u32], &mut [u32]) = (wv_b.0).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = wv_a0.1[i0 as usize] ^ wv_b0.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a0.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let r10: &mut [u32] = wv_a0.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = r10[i0 as usize];
                    let x10: u32 = x1.wrapping_shr(16u32) | x1.wrapping_shl(16u32);
                    let os: (&mut [u32], &mut [u32]) = r10.split_at_mut(0usize);
                    os.1[i0 as usize] = x10
                }
            );
            let wv_a1: (&mut [u32], &mut [u32]) = (wv_b.1).split_at_mut(4usize);
            let wv_b1: (&mut [u32], &mut [u32]) = (wv_a0.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = (wv_a1.1[i0 as usize]).wrapping_add(wv_b1.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a1.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let wv_a2: (&mut [u32], &mut [u32]) = (wv_a1.0).split_at_mut(0usize);
            let wv_b2: (&mut [u32], &mut [u32]) = (wv_a1.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = wv_a2.1[i0 as usize] ^ wv_b2.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a2.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let r11: &mut [u32] = wv_a2.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = r11[i0 as usize];
                    let x10: u32 = x1.wrapping_shr(12u32) | x1.wrapping_shl(20u32);
                    let os: (&mut [u32], &mut [u32]) = r11.split_at_mut(0usize);
                    os.1[i0 as usize] = x10
                }
            );
            let wv_a3: (&mut [u32], &mut [u32]) = (wv_b0.1).split_at_mut(0usize);
            let wv_b3: (&mut [u32], &mut [u32]) = (wv_a2.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = (wv_a3.1[i0 as usize]).wrapping_add(wv_b3.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a3.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = (wv_a3.1[i0 as usize]).wrapping_add(y.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a3.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let wv_a4: (&mut [u32], &mut [u32]) = (wv_b1.1).split_at_mut(0usize);
            let wv_b4: (&mut [u32], &mut [u32]) = (wv_a3.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = wv_a4.1[i0 as usize] ^ wv_b4.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a4.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let r12: &mut [u32] = wv_a4.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = r12[i0 as usize];
                    let x10: u32 = x1.wrapping_shr(8u32) | x1.wrapping_shl(24u32);
                    let os: (&mut [u32], &mut [u32]) = r12.split_at_mut(0usize);
                    os.1[i0 as usize] = x10
                }
            );
            let wv_a5: (&mut [u32], &mut [u32]) = (wv_b2.1).split_at_mut(0usize);
            let wv_b5: (&mut [u32], &mut [u32]) = (wv_a4.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = (wv_a5.1[i0 as usize]).wrapping_add(wv_b5.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a5.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let wv_a6: (&mut [u32], &mut [u32]) = (wv_b3.1).split_at_mut(0usize);
            let wv_b6: (&mut [u32], &mut [u32]) = (wv_a5.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = wv_a6.1[i0 as usize] ^ wv_b6.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a6.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x1
                }
            );
            let r13: &mut [u32] = wv_a6.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x1: u32 = r13[i0 as usize];
                    let x10: u32 = x1.wrapping_shr(7u32) | x1.wrapping_shl(25u32);
                    let os: (&mut [u32], &mut [u32]) = r13.split_at_mut(0usize);
                    os.1[i0 as usize] = x10
                }
            );
            let r14: (&mut [u32], &mut [u32]) = (wv_a6.1).split_at_mut(0usize);
            let r20: (&mut [u32], &mut [u32]) = (wv_b6.1).split_at_mut(0usize);
            let r30: (&mut [u32], &mut [u32]) = (wv_b5.1).split_at_mut(0usize);
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
            let wv_a7: (&mut [u32], &mut [u32]) = (wv_b4.1).split_at_mut(0usize);
            let wv_b7: (&mut [u32], &mut [u32]) = (r14.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = (wv_a7.1[i0 as usize]).wrapping_add(wv_b7.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a7.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = (wv_a7.1[i0 as usize]).wrapping_add(z.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a7.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let wv_a8: (&mut [u32], &mut [u32]) = (r30.1).split_at_mut(0usize);
            let wv_b8: (&mut [u32], &mut [u32]) = (wv_a7.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = wv_a8.1[i0 as usize] ^ wv_b8.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a8.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let r15: &mut [u32] = wv_a8.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = r15[i0 as usize];
                    let x13: u32 = x12.wrapping_shr(16u32) | x12.wrapping_shl(16u32);
                    let os: (&mut [u32], &mut [u32]) = r15.split_at_mut(0usize);
                    os.1[i0 as usize] = x13
                }
            );
            let wv_a9: (&mut [u32], &mut [u32]) = (r20.1).split_at_mut(0usize);
            let wv_b9: (&mut [u32], &mut [u32]) = (wv_a8.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = (wv_a9.1[i0 as usize]).wrapping_add(wv_b9.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a9.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let wv_a10: (&mut [u32], &mut [u32]) = (wv_b7.1).split_at_mut(0usize);
            let wv_b10: (&mut [u32], &mut [u32]) = (wv_a9.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = wv_a10.1[i0 as usize] ^ wv_b10.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a10.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let r16: &mut [u32] = wv_a10.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = r16[i0 as usize];
                    let x13: u32 = x12.wrapping_shr(12u32) | x12.wrapping_shl(20u32);
                    let os: (&mut [u32], &mut [u32]) = r16.split_at_mut(0usize);
                    os.1[i0 as usize] = x13
                }
            );
            let wv_a11: (&mut [u32], &mut [u32]) = (wv_b8.1).split_at_mut(0usize);
            let wv_b11: (&mut [u32], &mut [u32]) = (wv_a10.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = (wv_a11.1[i0 as usize]).wrapping_add(wv_b11.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a11.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = (wv_a11.1[i0 as usize]).wrapping_add(w.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a11.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let wv_a12: (&mut [u32], &mut [u32]) = (wv_b9.1).split_at_mut(0usize);
            let wv_b12: (&[u32], &[u32]) = (wv_a11.1).split_at(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = wv_a12.1[i0 as usize] ^ wv_b12.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a12.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let r17: &mut [u32] = wv_a12.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = r17[i0 as usize];
                    let x13: u32 = x12.wrapping_shr(8u32) | x12.wrapping_shl(24u32);
                    let os: (&mut [u32], &mut [u32]) = r17.split_at_mut(0usize);
                    os.1[i0 as usize] = x13
                }
            );
            let wv_a13: (&mut [u32], &mut [u32]) = (wv_b10.1).split_at_mut(0usize);
            let wv_b13: (&mut [u32], &mut [u32]) = (wv_a12.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = (wv_a13.1[i0 as usize]).wrapping_add(wv_b13.1[i0 as usize]);
                    let os: (&mut [u32], &mut [u32]) = (wv_a13.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let wv_a14: (&mut [u32], &mut [u32]) = (wv_b11.1).split_at_mut(0usize);
            let wv_b14: (&mut [u32], &mut [u32]) = (wv_a13.1).split_at_mut(0usize);
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = wv_a14.1[i0 as usize] ^ wv_b14.1[i0 as usize];
                    let os: (&mut [u32], &mut [u32]) = (wv_a14.1).split_at_mut(0usize);
                    os.1[i0 as usize] = x12
                }
            );
            let r18: &mut [u32] = wv_a14.1;
            krml::unroll_for!(
                4,
                "i0",
                0u32,
                1u32,
                {
                    let x12: u32 = r18[i0 as usize];
                    let x13: u32 = x12.wrapping_shr(7u32) | x12.wrapping_shl(25u32);
                    let os: (&mut [u32], &mut [u32]) = r18.split_at_mut(0usize);
                    os.1[i0 as usize] = x13
                }
            );
            let r19: (&mut [u32], &mut [u32]) = (wv_a14.1).split_at_mut(0usize);
            let r21: (&mut [u32], &mut [u32]) = (wv_b14.1).split_at_mut(0usize);
            let r31: (&mut [u32], &mut [u32]) = (wv_b13.1).split_at_mut(0usize);
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
        }
    );
    let s0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let s1: (&mut [u32], &mut [u32]) = (s0.1).split_at_mut(4usize);
    let r0: (&[u32], &[u32]) = (wv3.0).split_at(0usize);
    let r1: (&[u32], &[u32]) = (r0.1).split_at(4usize);
    let r2: (&[u32], &[u32]) = (r1.1).split_at(4usize);
    let r3: (&[u32], &[u32]) = (wv3.1).split_at(0usize);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = s1.0[i as usize] ^ r1.0[i as usize];
            let os: (&mut [u32], &mut [u32]) = (s1.0).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = s1.0[i as usize] ^ r2.1[i as usize];
            let os: (&mut [u32], &mut [u32]) = (s1.0).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = s1.1[i as usize] ^ r2.0[i as usize];
            let os: (&mut [u32], &mut [u32]) = (s1.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            let x: u32 = s1.1[i as usize] ^ r3.1[i as usize];
            let os: (&mut [u32], &mut [u32]) = (s1.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

pub(crate) fn init(hash: &mut [u32], kk: u32, nn: u32)
{
    let salt: [u8; 8] = [0u8; 8usize];
    let personal: [u8; 8] = [0u8; 8usize];
    let p: crate::hash_blake2b::blake2_params =
        crate::hash_blake2b::blake2_params
        {
            digest_length: 32u8,
            key_length: 0u8,
            fanout: 1u8,
            depth: 1u8,
            leaf_length: 0u32,
            node_offset: 0u64,
            node_depth: 0u8,
            inner_length: 0u8,
            salt: &salt,
            personal: &personal
        };
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let r0: (&mut [u32], &mut [u32]) = hash.split_at_mut(0usize);
    let r1: (&mut [u32], &mut [u32]) = (r0.1).split_at_mut(4usize);
    let r2: (&mut [u32], &mut [u32]) = (r1.1).split_at_mut(4usize);
    let r3: (&mut [u32], &mut [u32]) = (r2.1).split_at_mut(4usize);
    let iv0: u32 = (&crate::impl_blake2_constants::ivTable_S)[0usize];
    let iv1: u32 = (&crate::impl_blake2_constants::ivTable_S)[1usize];
    let iv2: u32 = (&crate::impl_blake2_constants::ivTable_S)[2usize];
    let iv3: u32 = (&crate::impl_blake2_constants::ivTable_S)[3usize];
    let iv4: u32 = (&crate::impl_blake2_constants::ivTable_S)[4usize];
    let iv5: u32 = (&crate::impl_blake2_constants::ivTable_S)[5usize];
    let iv6: u32 = (&crate::impl_blake2_constants::ivTable_S)[6usize];
    let iv7: u32 = (&crate::impl_blake2_constants::ivTable_S)[7usize];
    r3.0[0usize] = iv0;
    r3.0[1usize] = iv1;
    r3.0[2usize] = iv2;
    r3.0[3usize] = iv3;
    r3.1[0usize] = iv4;
    r3.1[1usize] = iv5;
    r3.1[2usize] = iv6;
    r3.1[3usize] = iv7;
    let uu____0: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4usize);
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: &[u8] = &p.salt[i.wrapping_mul(4u32) as usize..];
            let u: u32 = lowstar::endianness::load32_le(bj);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let uu____1: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(2usize);
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: &[u8] = &p.personal[i.wrapping_mul(4u32) as usize..];
            let u: u32 = lowstar::endianness::load32_le(bj);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = (uu____1.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    (&mut tmp)[0usize] =
        nn as u8 as u32
        ^
        ((kk as u8 as u32).wrapping_shl(8u32)
        ^
        ((p.fanout as u32).wrapping_shl(16u32) ^ (p.depth as u32).wrapping_shl(24u32)));
    (&mut tmp)[1usize] = p.leaf_length;
    (&mut tmp)[2usize] = p.node_offset as u32;
    (&mut tmp)[3usize] =
        (p.node_offset).wrapping_shr(32u32) as u32
        ^
        ((p.node_depth as u32).wrapping_shl(16u32) ^ (p.inner_length as u32).wrapping_shl(24u32));
    let tmp0: u32 = (&tmp)[0usize];
    let tmp1: u32 = (&tmp)[1usize];
    let tmp2: u32 = (&tmp)[2usize];
    let tmp3: u32 = (&tmp)[3usize];
    let tmp4: u32 = (&tmp)[4usize];
    let tmp5: u32 = (&tmp)[5usize];
    let tmp6: u32 = (&tmp)[6usize];
    let tmp7: u32 = (&tmp)[7usize];
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

fn update_key(wv: &mut [u32], hash: &mut [u32], kk: u32, k: &[u8], ll: u32)
{
    let lb: u64 = 64u32 as u64;
    let mut b: [u8; 64] = [0u8; 64usize];
    ((&mut b)[0usize..kk as usize]).copy_from_slice(&k[0usize..kk as usize]);
    if ll == 0u32
    { crate::hash_blake2s::update_block(wv, hash, true, false, lb, &b) }
    else
    { crate::hash_blake2s::update_block(wv, hash, false, false, lb, &b) };
    lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

pub(crate) fn update_multi(
    len: u32,
    wv: &mut [u32],
    hash: &mut [u32],
    prev: u64,
    blocks: &[u8],
    nb: u32
)
{
    lowstar::ignore::ignore::<u32>(len);
    for i in 0u32..nb
    {
        let totlen: u64 = prev.wrapping_add(i.wrapping_add(1u32).wrapping_mul(64u32) as u64);
        let b: (&[u8], &[u8]) = blocks.split_at(i.wrapping_mul(64u32) as usize);
        crate::hash_blake2s::update_block(wv, hash, false, false, totlen, b.1)
    }
}

pub(crate) fn update_last(
    len: u32,
    wv: &mut [u32],
    hash: &mut [u32],
    last_node: bool,
    prev: u64,
    rem: u32,
    d: &[u8]
)
{
    let mut b: [u8; 64] = [0u8; 64usize];
    let last: (&[u8], &[u8]) = d.split_at(len.wrapping_sub(rem) as usize);
    ((&mut b)[0usize..rem as usize]).copy_from_slice(&last.1[0usize..rem as usize]);
    let totlen: u64 = prev.wrapping_add(len as u64);
    crate::hash_blake2s::update_block(wv, hash, true, last_node, totlen, &b);
    lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

fn update_blocks(len: u32, wv: &mut [u32], hash: &mut [u32], prev: u64, blocks: &[u8])
{
    let nb: u32 = len.wrapping_div(64u32);
    let rem: u32 = len.wrapping_rem(64u32);
    let nb0: u32 = if rem == 0u32 && nb > 0u32 { nb.wrapping_sub(1u32) } else { nb };
    let rem0: u32 = if rem == 0u32 && nb > 0u32 { 64u32 } else { rem };
    crate::hash_blake2s::update_multi(len, wv, hash, prev, blocks, nb0);
    crate::hash_blake2s::update_last(len, wv, hash, false, prev, rem0, blocks)
}

#[inline] fn update(wv: &mut [u32], hash: &mut [u32], kk: u32, k: &[u8], ll: u32, d: &[u8])
{
    let lb: u64 = 64u32 as u64;
    if kk > 0u32
    {
        crate::hash_blake2s::update_key(wv, hash, kk, k, ll);
        if ll != 0u32 { crate::hash_blake2s::update_blocks(ll, wv, hash, lb, d) }
    }
    else
    { crate::hash_blake2s::update_blocks(ll, wv, hash, 0u32 as u64, d) }
}

pub(crate) fn finish(nn: u32, output: &mut [u8], hash: &[u32])
{
    let mut b: [u8; 32] = [0u8; 32usize];
    let first: (&mut [u8], &mut [u8]) = b.split_at_mut(0usize);
    let second: (&mut [u8], &mut [u8]) = (first.1).split_at_mut(16usize);
    let row0: (&[u32], &[u32]) = hash.split_at(0usize);
    let row1: (&[u32], &[u32]) = (row0.1).split_at(4usize);
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store32_le(
            &mut second.0[i.wrapping_mul(4u32) as usize..],
            row1.0[i as usize]
        )
    );
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        lowstar::endianness::store32_le(
            &mut second.1[i.wrapping_mul(4u32) as usize..],
            row1.1[i as usize]
        )
    );
    lowstar::ignore::ignore::<&[u8]>(&b);
    let r#final: (&[u8], &[u8]) = b.split_at(0usize);
    (output[0usize..nn as usize]).copy_from_slice(&r#final.1[0usize..nn as usize]);
    lib::memzero0::memzero::<u8>(&mut b, 32u32)
}

pub const block_bytes: u32 = 64u32;

pub const out_bytes: u32 = 32u32;

pub const key_bytes: u32 = 32u32;

pub const salt_bytes: u32 = 8u32;

pub const personal_bytes: u32 = 8u32;

#[derive(PartialEq, Clone)]
pub struct block_state_t
{ pub fst: u8, pub snd: u8, pub thd: bool, pub f3: Box<[u32]>, pub f4: Box<[u32]> }

#[derive(PartialEq, Clone)]
pub struct state_t
{ pub block_state: crate::hash_blake2s::block_state_t, pub buf: Box<[u8]>, pub total_len: u64 }

#[derive(PartialEq, Clone)]
enum option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··
{
    None,
    Some { v: crate::hash_blake2s::block_state_t }
}

fn malloc_raw <'a>(
    kk: crate::hash_blake2b::index,
    key: crate::hash_blake2b::params_and_key <'a>
) ->
    Box<[crate::hash_blake2s::state_t]>
{
    let mut buf: Box<[u8]> = vec![0u8; 64usize].into_boxed_slice();
    let buf1: &mut [u8] = &mut buf;
    let wv: Box<[u32]> = vec![0u32; 16usize].into_boxed_slice();
    let
    block_state:
    crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··
    =
        {
            let b: Box<[u32]> = vec![0u32; 16usize].into_boxed_slice();
            crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··::Some
            {
                v:
                crate::hash_blake2s::block_state_t
                { fst: kk.key_length, snd: kk.digest_length, thd: kk.last_node, f3: wv, f4: b }
            }
        };
    match block_state
    {
        crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··::None
        => { [].into() },
        crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··::Some
        { v: block_state1 }
        =>
          {
              let mut block_state2: crate::hash_blake2s::block_state_t = block_state1;
              let k·: crate::streaming_types::optional = crate::streaming_types::optional::Some;
              match k·
              {
                  crate::streaming_types::optional::None => [].into(),
                  crate::streaming_types::optional::Some =>
                    {
                        let p: &[crate::hash_blake2b::blake2_params] = key.fst;
                        let kk1: u8 = (p[0usize]).key_length;
                        let nn: u8 = (p[0usize]).digest_length;
                        match block_state2
                        {
                            crate::hash_blake2s::block_state_t { thd: last_node, .. } =>
                              {
                                  let i: crate::hash_blake2b::index =
                                      crate::hash_blake2b::index
                                      { key_length: kk1, digest_length: nn, last_node };
                                  let h: &mut [u32] = &mut block_state2.f4;
                                  let kk2: u32 = i.key_length as u32;
                                  let k·2: &[u8] = key.snd;
                                  if kk2 != 0u32
                                  {
                                      let sub_b: (&mut [u8], &mut [u8]) =
                                          buf1.split_at_mut(kk2 as usize);
                                      (sub_b.1[0usize..64u32.wrapping_sub(kk2) as usize]).copy_from_slice(
                                          &vec![0u8; 64u32.wrapping_sub(kk2) as usize].into_boxed_slice(

                                          )
                                      );
                                      (buf1[0usize..kk2 as usize]).copy_from_slice(
                                          &k·2[0usize..kk2 as usize]
                                      )
                                  };
                                  let pv: crate::hash_blake2b::blake2_params = p[0usize];
                                  let mut tmp: [u32; 8] = [0u32; 8usize];
                                  let r0: (&mut [u32], &mut [u32]) = h.split_at_mut(0usize);
                                  let r1: (&mut [u32], &mut [u32]) = (r0.1).split_at_mut(4usize);
                                  let r2: (&mut [u32], &mut [u32]) = (r1.1).split_at_mut(4usize);
                                  let r3: (&mut [u32], &mut [u32]) = (r2.1).split_at_mut(4usize);
                                  let iv0: u32 = (&crate::impl_blake2_constants::ivTable_S)[0usize];
                                  let iv1: u32 = (&crate::impl_blake2_constants::ivTable_S)[1usize];
                                  let iv2: u32 = (&crate::impl_blake2_constants::ivTable_S)[2usize];
                                  let iv3: u32 = (&crate::impl_blake2_constants::ivTable_S)[3usize];
                                  let iv4: u32 = (&crate::impl_blake2_constants::ivTable_S)[4usize];
                                  let iv5: u32 = (&crate::impl_blake2_constants::ivTable_S)[5usize];
                                  let iv6: u32 = (&crate::impl_blake2_constants::ivTable_S)[6usize];
                                  let iv7: u32 = (&crate::impl_blake2_constants::ivTable_S)[7usize];
                                  r3.0[0usize] = iv0;
                                  r3.0[1usize] = iv1;
                                  r3.0[2usize] = iv2;
                                  r3.0[3usize] = iv3;
                                  r3.1[0usize] = iv4;
                                  r3.1[1usize] = iv5;
                                  r3.1[2usize] = iv6;
                                  r3.1[3usize] = iv7;
                                  let uu____0: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4usize);
                                  krml::unroll_for!(
                                      2,
                                      "i0",
                                      0u32,
                                      1u32,
                                      {
                                          let bj: &[u8] =
                                              &pv.salt[i0.wrapping_mul(4u32) as usize..];
                                          let u: u32 = lowstar::endianness::load32_le(bj);
                                          let r4: u32 = u;
                                          let x: u32 = r4;
                                          let os: (&mut [u32], &mut [u32]) =
                                              (uu____0.1).split_at_mut(0usize);
                                          os.1[i0 as usize] = x
                                      }
                                  );
                                  let uu____1: (&mut [u32], &mut [u32]) =
                                      (uu____0.1).split_at_mut(2usize);
                                  krml::unroll_for!(
                                      2,
                                      "i0",
                                      0u32,
                                      1u32,
                                      {
                                          let bj: &[u8] =
                                              &pv.personal[i0.wrapping_mul(4u32) as usize..];
                                          let u: u32 = lowstar::endianness::load32_le(bj);
                                          let r4: u32 = u;
                                          let x: u32 = r4;
                                          let os: (&mut [u32], &mut [u32]) =
                                              (uu____1.1).split_at_mut(0usize);
                                          os.1[i0 as usize] = x
                                      }
                                  );
                                  (&mut tmp)[0usize] =
                                      pv.digest_length as u32
                                      ^
                                      ((pv.key_length as u32).wrapping_shl(8u32)
                                      ^
                                      ((pv.fanout as u32).wrapping_shl(16u32)
                                      ^
                                      (pv.depth as u32).wrapping_shl(24u32)));
                                  (&mut tmp)[1usize] = pv.leaf_length;
                                  (&mut tmp)[2usize] = pv.node_offset as u32;
                                  (&mut tmp)[3usize] =
                                      (pv.node_offset).wrapping_shr(32u32) as u32
                                      ^
                                      ((pv.node_depth as u32).wrapping_shl(16u32)
                                      ^
                                      (pv.inner_length as u32).wrapping_shl(24u32));
                                  let tmp0: u32 = (&tmp)[0usize];
                                  let tmp1: u32 = (&tmp)[1usize];
                                  let tmp2: u32 = (&tmp)[2usize];
                                  let tmp3: u32 = (&tmp)[3usize];
                                  let tmp4: u32 = (&tmp)[4usize];
                                  let tmp5: u32 = (&tmp)[5usize];
                                  let tmp6: u32 = (&tmp)[6usize];
                                  let tmp7: u32 = (&tmp)[7usize];
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
                        };
                        let kk10: u8 = kk.key_length;
                        let ite: u32 = if kk10 != 0u8 { 64u32 } else { 0u32 };
                        let s: crate::hash_blake2s::state_t =
                            crate::hash_blake2s::state_t
                            {
                                block_state: block_state2,
                                buf: (*buf1).into(),
                                total_len: ite as u64
                            };
                        let p0: Box<[crate::hash_blake2s::state_t]> = vec![s].into_boxed_slice();
                        p0
                    },
                  _ => panic!("Precondition of the function most likely violated")
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

fn index_of_state(s: &[crate::hash_blake2s::state_t]) -> crate::hash_blake2b::index
{
    let block_state: &crate::hash_blake2s::block_state_t = &(s[0usize]).block_state;
    match *block_state
    {
        crate::hash_blake2s::block_state_t { fst: kk1, snd: nn, thd: last_node, .. } =>
          crate::hash_blake2b::index { key_length: kk1, digest_length: nn, last_node }
    }
}

fn reset_raw(
    state: &mut [crate::hash_blake2s::state_t],
    key: crate::hash_blake2b::params_and_key
)
{
    let block_state: &mut crate::hash_blake2s::block_state_t = &mut (state[0usize]).block_state;
    let buf: &mut [u8] = &mut (state[0usize]).buf;
    let i: crate::hash_blake2b::index =
        match *block_state
        {
            crate::hash_blake2s::block_state_t { fst: kk1, snd: nn, thd: last_node, .. } =>
              crate::hash_blake2b::index { key_length: kk1, digest_length: nn, last_node }
        };
    let p: &[crate::hash_blake2b::blake2_params] = key.fst;
    let kk1: u8 = (p[0usize]).key_length;
    let nn: u8 = (p[0usize]).digest_length;
    match *block_state
    {
        crate::hash_blake2s::block_state_t { thd: last_node, .. } =>
          {
              let i1: crate::hash_blake2b::index =
                  crate::hash_blake2b::index { key_length: kk1, digest_length: nn, last_node };
              let h: &mut [u32] = &mut block_state.f4;
              let kk2: u32 = i1.key_length as u32;
              let k·1: &[u8] = key.snd;
              if kk2 != 0u32
              {
                  let sub_b: (&mut [u8], &mut [u8]) = buf.split_at_mut(kk2 as usize);
                  (sub_b.1[0usize..64u32.wrapping_sub(kk2) as usize]).copy_from_slice(
                      &vec![0u8; 64u32.wrapping_sub(kk2) as usize].into_boxed_slice()
                  );
                  (buf[0usize..kk2 as usize]).copy_from_slice(&k·1[0usize..kk2 as usize])
              };
              let pv: crate::hash_blake2b::blake2_params = p[0usize];
              let mut tmp: [u32; 8] = [0u32; 8usize];
              let r0: (&mut [u32], &mut [u32]) = h.split_at_mut(0usize);
              let r1: (&mut [u32], &mut [u32]) = (r0.1).split_at_mut(4usize);
              let r2: (&mut [u32], &mut [u32]) = (r1.1).split_at_mut(4usize);
              let r3: (&mut [u32], &mut [u32]) = (r2.1).split_at_mut(4usize);
              let iv0: u32 = (&crate::impl_blake2_constants::ivTable_S)[0usize];
              let iv1: u32 = (&crate::impl_blake2_constants::ivTable_S)[1usize];
              let iv2: u32 = (&crate::impl_blake2_constants::ivTable_S)[2usize];
              let iv3: u32 = (&crate::impl_blake2_constants::ivTable_S)[3usize];
              let iv4: u32 = (&crate::impl_blake2_constants::ivTable_S)[4usize];
              let iv5: u32 = (&crate::impl_blake2_constants::ivTable_S)[5usize];
              let iv6: u32 = (&crate::impl_blake2_constants::ivTable_S)[6usize];
              let iv7: u32 = (&crate::impl_blake2_constants::ivTable_S)[7usize];
              r3.0[0usize] = iv0;
              r3.0[1usize] = iv1;
              r3.0[2usize] = iv2;
              r3.0[3usize] = iv3;
              r3.1[0usize] = iv4;
              r3.1[1usize] = iv5;
              r3.1[2usize] = iv6;
              r3.1[3usize] = iv7;
              let uu____0: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4usize);
              krml::unroll_for!(
                  2,
                  "i0",
                  0u32,
                  1u32,
                  {
                      let bj: &[u8] = &pv.salt[i0.wrapping_mul(4u32) as usize..];
                      let u: u32 = lowstar::endianness::load32_le(bj);
                      let r: u32 = u;
                      let x: u32 = r;
                      let os: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(0usize);
                      os.1[i0 as usize] = x
                  }
              );
              let uu____1: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(2usize);
              krml::unroll_for!(
                  2,
                  "i0",
                  0u32,
                  1u32,
                  {
                      let bj: &[u8] = &pv.personal[i0.wrapping_mul(4u32) as usize..];
                      let u: u32 = lowstar::endianness::load32_le(bj);
                      let r: u32 = u;
                      let x: u32 = r;
                      let os: (&mut [u32], &mut [u32]) = (uu____1.1).split_at_mut(0usize);
                      os.1[i0 as usize] = x
                  }
              );
              (&mut tmp)[0usize] =
                  pv.digest_length as u32
                  ^
                  ((pv.key_length as u32).wrapping_shl(8u32)
                  ^
                  ((pv.fanout as u32).wrapping_shl(16u32) ^ (pv.depth as u32).wrapping_shl(24u32)));
              (&mut tmp)[1usize] = pv.leaf_length;
              (&mut tmp)[2usize] = pv.node_offset as u32;
              (&mut tmp)[3usize] =
                  (pv.node_offset).wrapping_shr(32u32) as u32
                  ^
                  ((pv.node_depth as u32).wrapping_shl(16u32)
                  ^
                  (pv.inner_length as u32).wrapping_shl(24u32));
              let tmp0: u32 = (&tmp)[0usize];
              let tmp1: u32 = (&tmp)[1usize];
              let tmp2: u32 = (&tmp)[2usize];
              let tmp3: u32 = (&tmp)[3usize];
              let tmp4: u32 = (&tmp)[4usize];
              let tmp5: u32 = (&tmp)[5usize];
              let tmp6: u32 = (&tmp)[6usize];
              let tmp7: u32 = (&tmp)[7usize];
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
    };
    let kk10: u8 = i.key_length;
    let ite: u32 = if kk10 != 0u8 { 64u32 } else { 0u32 };
    let total_len: u64 = ite as u64;
    (state[0usize]).total_len = total_len
}

/**
General-purpose re-initialization function with parameters and
key. You cannot change digest_length, key_length, or last_node, meaning those values in
the parameters object must be the same as originally decided via one of the
malloc functions. All other values of the parameter can be changed. The behavior
is unspecified if you violate this precondition.
*/
pub fn
reset_with_key_and_params(
    s: &mut [crate::hash_blake2s::state_t],
    p: &[crate::hash_blake2b::blake2_params],
    k: &[u8]
)
{
    let i1: crate::hash_blake2b::index = crate::hash_blake2s::index_of_state(s);
    lowstar::ignore::ignore::<crate::hash_blake2b::index>(i1);
    crate::hash_blake2s::reset_raw(s, crate::hash_blake2b::params_and_key { fst: p, snd: k })
}

/**
Specialized-purpose re-initialization function with no parameters,
and a key. The key length must be the same as originally decided via your choice
of malloc function. All other parameters are reset to their default values. The
original call to malloc MUST have set digest_length to the default value. The
behavior is unspecified if you violate this precondition.
*/
pub fn
reset_with_key(s: &mut [crate::hash_blake2s::state_t], k: &[u8])
{
    let idx: crate::hash_blake2b::index = crate::hash_blake2s::index_of_state(s);
    let salt: [u8; 8] = [0u8; 8usize];
    let personal: [u8; 8] = [0u8; 8usize];
    let p: crate::hash_blake2b::blake2_params =
        crate::hash_blake2b::blake2_params
        {
            digest_length: idx.digest_length,
            key_length: idx.key_length,
            fanout: 1u8,
            depth: 1u8,
            leaf_length: 0u32,
            node_offset: 0u64,
            node_depth: 0u8,
            inner_length: 0u8,
            salt: &salt,
            personal: &personal
        };
    let p0: [crate::hash_blake2b::blake2_params; 1] = [p; 1usize];
    crate::hash_blake2s::reset_raw(s, crate::hash_blake2b::params_and_key { fst: &p0, snd: k })
}

/**
Specialized-purpose re-initialization function with no parameters
and no key. This is what you want if you intend to use Blake2 as a hash
function. The key length and digest length must have been set to their
respective default values via your choice of malloc function (always true if you
used `malloc`). All other parameters are reset to their default values. The
behavior is unspecified if you violate this precondition.
*/
pub fn
reset(s: &mut [crate::hash_blake2s::state_t])
{ crate::hash_blake2s::reset_with_key(s, &[]) }

/**
Update function; 0 = success, 1 = max length exceeded
*/
pub fn
update0(state: &mut [crate::hash_blake2s::state_t], chunk: &[u8], chunk_len: u32) ->
    crate::streaming_types::error_code
{
    let block_state: &mut crate::hash_blake2s::block_state_t = &mut (state[0usize]).block_state;
    let total_len: u64 = (state[0usize]).total_len;
    if chunk_len as u64 > 0xffffffffffffffffu64.wrapping_sub(total_len)
    { crate::streaming_types::error_code::MaximumLengthExceeded }
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
        else if sz == 0u32
        {
            let buf: &mut [u8] = &mut (state[0usize]).buf;
            let total_len1: u64 = (state[0usize]).total_len;
            let sz1: u32 =
                if total_len1.wrapping_rem(64u32 as u64) == 0u64 && total_len1 > 0u64
                { 64u32 }
                else
                { total_len1.wrapping_rem(64u32 as u64) as u32 };
            if sz1 != 0u32
            {
                let prevlen: u64 = total_len1.wrapping_sub(sz1 as u64);
                match *block_state
                {
                    crate::hash_blake2s::block_state_t { f3: ref mut wv, f4: ref mut hash, .. } =>
                      {
                          let nb: u32 = 1u32;
                          crate::hash_blake2s::update_multi(64u32, wv, hash, prevlen, buf, nb)
                      }
                }
            };
            let ite: u32 =
                if (chunk_len as u64).wrapping_rem(64u32 as u64) == 0u64 && chunk_len as u64 > 0u64
                { 64u32 }
                else
                { (chunk_len as u64).wrapping_rem(64u32 as u64) as u32 };
            let n_blocks: u32 = chunk_len.wrapping_sub(ite).wrapping_div(64u32);
            let data1_len: u32 = n_blocks.wrapping_mul(64u32);
            let data2_len: u32 = chunk_len.wrapping_sub(data1_len);
            let data1: (&[u8], &[u8]) = chunk.split_at(0usize);
            let data2: (&[u8], &[u8]) = (data1.1).split_at(data1_len as usize);
            match *block_state
            {
                crate::hash_blake2s::block_state_t { f3: ref mut wv, f4: ref mut hash, .. } =>
                  {
                      let nb: u32 = data1_len.wrapping_div(64u32);
                      crate::hash_blake2s::update_multi(
                          data1_len,
                          wv,
                          hash,
                          total_len1,
                          data2.0,
                          nb
                      )
                  }
            };
            let dst: (&mut [u8], &mut [u8]) = buf.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len = total_len1.wrapping_add(chunk_len as u64)
        }
        else
        {
            let diff: u32 = 64u32.wrapping_sub(sz);
            let chunk1: (&[u8], &[u8]) = chunk.split_at(0usize);
            let chunk2: (&[u8], &[u8]) = (chunk1.1).split_at(diff as usize);
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
            if sz10 != 0u32
            {
                let prevlen: u64 = total_len10.wrapping_sub(sz10 as u64);
                match *block_state
                {
                    crate::hash_blake2s::block_state_t { f3: ref mut wv, f4: ref mut hash, .. } =>
                      {
                          let nb: u32 = 1u32;
                          crate::hash_blake2s::update_multi(64u32, wv, hash, prevlen, buf0, nb)
                      }
                }
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
            let data1: (&[u8], &[u8]) = (chunk2.1).split_at(0usize);
            let data2: (&[u8], &[u8]) = (data1.1).split_at(data1_len as usize);
            match *block_state
            {
                crate::hash_blake2s::block_state_t { f3: ref mut wv, f4: ref mut hash, .. } =>
                  {
                      let nb: u32 = data1_len.wrapping_div(64u32);
                      crate::hash_blake2s::update_multi(
                          data1_len,
                          wv,
                          hash,
                          total_len10,
                          data2.0,
                          nb
                      )
                  }
            };
            let dst: (&mut [u8], &mut [u8]) = buf0.split_at_mut(0usize);
            (dst.1[0usize..data2_len as usize]).copy_from_slice(
                &data2.1[0usize..data2_len as usize]
            );
            (state[0usize]).total_len =
                total_len10.wrapping_add(chunk_len.wrapping_sub(diff) as u64)
        };
        crate::streaming_types::error_code::Success
    }
}

/**
Digest function. This function expects the `output` array to hold
at least `digest_length` bytes, where `digest_length` was determined by your
choice of `malloc` function. Concretely, if you used `malloc` or
`malloc_with_key`, then the expected length is 32 for S, or 64 for B (default
digest length). If you used `malloc_with_params_and_key`, then the expected
length is whatever you chose for the `digest_length` field of your parameters.
For convenience, this function returns `digest_length`. When in doubt, callers
can pass an array of size HACL_BLAKE2S_32_OUT_BYTES, then use the return value
to see how many bytes were actually written.
*/
pub fn
digest(s: &[crate::hash_blake2s::state_t], dst: &mut [u8]) ->
    u8
{
    let block_state: &crate::hash_blake2s::block_state_t = &(s[0usize]).block_state;
    let i1: crate::hash_blake2b::index =
        match *block_state
        {
            crate::hash_blake2s::block_state_t { fst: kk, snd: nn, thd: last_node, .. } =>
              crate::hash_blake2b::index { key_length: kk, digest_length: nn, last_node }
        };
    let block_state0: &crate::hash_blake2s::block_state_t = &(s[0usize]).block_state;
    let buf_: &[u8] = &(s[0usize]).buf;
    let total_len: u64 = (s[0usize]).total_len;
    let r: u32 =
        if total_len.wrapping_rem(64u32 as u64) == 0u64 && total_len > 0u64
        { 64u32 }
        else
        { total_len.wrapping_rem(64u32 as u64) as u32 };
    let buf_1: (&[u8], &[u8]) = buf_.split_at(0usize);
    let wv: [u32; 16] = [0u32; 16usize];
    let b: [u32; 16] = [0u32; 16usize];
    let mut tmp_block_state: crate::hash_blake2s::block_state_t =
        crate::hash_blake2s::block_state_t
        {
            fst: i1.key_length,
            snd: i1.digest_length,
            thd: i1.last_node,
            f3: Box::new(wv),
            f4: Box::new(b)
        };
    match *block_state0
    {
        crate::hash_blake2s::block_state_t { f4: ref src_b, .. } =>
          match tmp_block_state
          {
              crate::hash_blake2s::block_state_t { f4: ref mut dst_b, .. } =>
                (dst_b[0usize..16usize]).copy_from_slice(&src_b[0usize..16usize])
          }
    };
    let prev_len: u64 = total_len.wrapping_sub(r as u64);
    let buf_multi: (&[u8], &[u8]) = (buf_1.1).split_at(0usize);
    let ite: u32 =
        if r.wrapping_rem(64u32) == 0u32 && r > 0u32 { 64u32 } else { r.wrapping_rem(64u32) };
    let buf_last: (&[u8], &[u8]) = (buf_multi.1).split_at(r.wrapping_sub(ite) as usize);
    match tmp_block_state
    {
        crate::hash_blake2s::block_state_t { f3: ref mut wv0, f4: ref mut hash, .. } =>
          {
              let nb: u32 = 0u32;
              crate::hash_blake2s::update_multi(0u32, wv0, hash, prev_len, buf_last.0, nb)
          }
    };
    let prev_len_last: u64 = total_len.wrapping_sub(r as u64);
    match tmp_block_state
    {
        crate::hash_blake2s::block_state_t
        { thd: last_node, f3: ref mut wv0, f4: ref mut hash, .. }
        => crate::hash_blake2s::update_last(r, wv0, hash, last_node, prev_len_last, r, buf_last.1)
    };
    match tmp_block_state
    {
        crate::hash_blake2s::block_state_t { snd: nn, .. } =>
          crate::hash_blake2s::finish(nn as u32, dst, &tmp_block_state.f4)
    };
    let block_state1: &crate::hash_blake2s::block_state_t = &(s[0usize]).block_state;
    match *block_state1
    {
        crate::hash_blake2s::block_state_t { fst: kk, snd: nn, thd: last_node, .. } =>
          crate::hash_blake2b::index { key_length: kk, digest_length: nn, last_node }
    }.digest_length
}

pub fn info(s: &[crate::hash_blake2s::state_t]) -> crate::hash_blake2b::index
{
    let block_state: &crate::hash_blake2s::block_state_t = &(s[0usize]).block_state;
    match *block_state
    {
        crate::hash_blake2s::block_state_t { fst: kk, snd: nn, thd: last_node, .. } =>
          crate::hash_blake2b::index { key_length: kk, digest_length: nn, last_node }
    }
}

/**
Copying. This preserves all parameters.
*/
pub fn
copy
<'a>(state: &'a [crate::hash_blake2s::state_t]) ->
    Box<[crate::hash_blake2s::state_t]>
{
    let block_state0: &crate::hash_blake2s::block_state_t = &(state[0usize]).block_state;
    let buf0: &[u8] = &(state[0usize]).buf;
    let total_len0: u64 = (state[0usize]).total_len;
    let i: crate::hash_blake2b::index =
        match *block_state0
        {
            crate::hash_blake2s::block_state_t { fst: kk1, snd: nn, thd: last_node, .. } =>
              crate::hash_blake2b::index { key_length: kk1, digest_length: nn, last_node }
        };
    let mut buf: Box<[u8]> = vec![0u8; 64usize].into_boxed_slice();
    ((&mut buf)[0usize..64usize]).copy_from_slice(&buf0[0usize..64usize]);
    let wv: Box<[u32]> = vec![0u32; 16usize].into_boxed_slice();
    let
    block_state:
    crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··
    =
        {
            let b: Box<[u32]> = vec![0u32; 16usize].into_boxed_slice();
            crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··::Some
            {
                v:
                crate::hash_blake2s::block_state_t
                { fst: i.key_length, snd: i.digest_length, thd: i.last_node, f3: wv, f4: b }
            }
        };
    match block_state
    {
        crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··::None
        => { [].into() },
        crate::hash_blake2s::option__·uint8_t···uint8_t···bool····uint32_t·····uint32_t··::Some
        { v: block_state1 }
        =>
          {
              let mut block_state2: crate::hash_blake2s::block_state_t = block_state1;
              match *block_state0
              {
                  crate::hash_blake2s::block_state_t { f4: ref src_b, .. } =>
                    match block_state2
                    {
                        crate::hash_blake2s::block_state_t { f4: ref mut dst_b, .. } =>
                          (dst_b[0usize..16usize]).copy_from_slice(&src_b[0usize..16usize])
                    }
              };
              let k·: crate::streaming_types::optional = crate::streaming_types::optional::Some;
              match k·
              {
                  crate::streaming_types::optional::None => [].into(),
                  crate::streaming_types::optional::Some =>
                    {
                        let s: crate::hash_blake2s::state_t =
                            crate::hash_blake2s::state_t
                            { block_state: block_state2, buf, total_len: total_len0 };
                        let p: Box<[crate::hash_blake2s::state_t]> = vec![s].into_boxed_slice();
                        p
                    },
                  _ => panic!("Precondition of the function most likely violated")
              }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

/**
Write the BLAKE2s digest of message `input` using key `key` into `output`.

@param output Pointer to `output_len` bytes of memory where the digest is written to.
@param output_len Length of the to-be-generated digest with 1 <= `output_len` <= 64.
@param input Pointer to `input_len` bytes of memory where the input message is read from.
@param input_len Length of the input message.
@param key Pointer to `key_len` bytes of memory where the key is read from.
@param key_len Length of the key. Can be 0.
*/
pub fn
hash_with_key(
    output: &mut [u8],
    output_len: u32,
    input: &[u8],
    input_len: u32,
    key: &[u8],
    key_len: u32
)
{
    let mut b: [u32; 16] = [0u32; 16usize];
    let mut b1: [u32; 16] = [0u32; 16usize];
    crate::hash_blake2s::init(&mut b, key_len, output_len);
    crate::hash_blake2s::update(&mut b1, &mut b, key_len, key, input_len, input);
    crate::hash_blake2s::finish(output_len, output, &b);
    lib::memzero0::memzero::<u32>(&mut b1, 16u32);
    lib::memzero0::memzero::<u32>(&mut b, 16u32)
}

/**
Write the BLAKE2s digest of message `input` using key `key` and
parameters `params` into `output`. The `key` array must be of length
`params.key_length`. The `output` array must be of length
`params.digest_length`.
*/
pub fn
hash_with_key_and_params(
    output: &mut [u8],
    input: &[u8],
    input_len: u32,
    params: crate::hash_blake2b::blake2_params,
    key: &[u8]
)
{
    let mut b: [u32; 16] = [0u32; 16usize];
    let mut b1: [u32; 16] = [0u32; 16usize];
    let mut tmp: [u32; 8] = [0u32; 8usize];
    let r0: (&mut [u32], &mut [u32]) = b.split_at_mut(0usize);
    let r1: (&mut [u32], &mut [u32]) = (r0.1).split_at_mut(4usize);
    let r2: (&mut [u32], &mut [u32]) = (r1.1).split_at_mut(4usize);
    let r3: (&mut [u32], &mut [u32]) = (r2.1).split_at_mut(4usize);
    let iv0: u32 = (&crate::impl_blake2_constants::ivTable_S)[0usize];
    let iv1: u32 = (&crate::impl_blake2_constants::ivTable_S)[1usize];
    let iv2: u32 = (&crate::impl_blake2_constants::ivTable_S)[2usize];
    let iv3: u32 = (&crate::impl_blake2_constants::ivTable_S)[3usize];
    let iv4: u32 = (&crate::impl_blake2_constants::ivTable_S)[4usize];
    let iv5: u32 = (&crate::impl_blake2_constants::ivTable_S)[5usize];
    let iv6: u32 = (&crate::impl_blake2_constants::ivTable_S)[6usize];
    let iv7: u32 = (&crate::impl_blake2_constants::ivTable_S)[7usize];
    r3.0[0usize] = iv0;
    r3.0[1usize] = iv1;
    r3.0[2usize] = iv2;
    r3.0[3usize] = iv3;
    r3.1[0usize] = iv4;
    r3.1[1usize] = iv5;
    r3.1[2usize] = iv6;
    r3.1[3usize] = iv7;
    let uu____0: (&mut [u32], &mut [u32]) = tmp.split_at_mut(4usize);
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: &[u8] = &params.salt[i.wrapping_mul(4u32) as usize..];
            let u: u32 = lowstar::endianness::load32_le(bj);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    let uu____1: (&mut [u32], &mut [u32]) = (uu____0.1).split_at_mut(2usize);
    krml::unroll_for!(
        2,
        "i",
        0u32,
        1u32,
        {
            let bj: &[u8] = &params.personal[i.wrapping_mul(4u32) as usize..];
            let u: u32 = lowstar::endianness::load32_le(bj);
            let r: u32 = u;
            let x: u32 = r;
            let os: (&mut [u32], &mut [u32]) = (uu____1.1).split_at_mut(0usize);
            os.1[i as usize] = x
        }
    );
    (&mut tmp)[0usize] =
        params.digest_length as u32
        ^
        ((params.key_length as u32).wrapping_shl(8u32)
        ^
        ((params.fanout as u32).wrapping_shl(16u32) ^ (params.depth as u32).wrapping_shl(24u32)));
    (&mut tmp)[1usize] = params.leaf_length;
    (&mut tmp)[2usize] = params.node_offset as u32;
    (&mut tmp)[3usize] =
        (params.node_offset).wrapping_shr(32u32) as u32
        ^
        ((params.node_depth as u32).wrapping_shl(16u32)
        ^
        (params.inner_length as u32).wrapping_shl(24u32));
    let tmp0: u32 = (&tmp)[0usize];
    let tmp1: u32 = (&tmp)[1usize];
    let tmp2: u32 = (&tmp)[2usize];
    let tmp3: u32 = (&tmp)[3usize];
    let tmp4: u32 = (&tmp)[4usize];
    let tmp5: u32 = (&tmp)[5usize];
    let tmp6: u32 = (&tmp)[6usize];
    let tmp7: u32 = (&tmp)[7usize];
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
    r2.0[3usize] = iv7·;
    crate::hash_blake2s::update(&mut b1, &mut b, params.key_length as u32, key, input_len, input);
    crate::hash_blake2s::finish(params.digest_length as u32, output, &b);
    lib::memzero0::memzero::<u32>(&mut b1, 16u32);
    lib::memzero0::memzero::<u32>(&mut b, 16u32)
}
