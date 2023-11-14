#[inline] fn blake2s_update_block(
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
    flag: bool,
    totlen: u64,
    d: &mut [u8]
) ->
    ()
{
    let mut m_w: [u32; 16] = [0u32; 16usize];
    for i in 0u32..16u32
    {
        let os: (&mut [u32], &mut [u32]) = (&mut m_w).split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) = d.split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut mask: crate::lib::intvector_intrinsics::vec128 =
        crate::lib::intvector_intrinsics::vec128_zero;
    let wv_14: u32 = if flag { 0xFFFFFFFFu32 } else { 0u32 };
    let wv_15: u32 = 0u32;
    mask =
        crate::lib::intvector_intrinsics::vec128_load32s(
            totlen as u32,
            totlen.wrapping_shr(32u32) as u32,
            wv_14,
            wv_15
        );
    (wv[0usize..4usize]).copy_from_slice(&hash[0usize..4usize]);
    let
    wv3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        wv.split_at_mut(3usize);
    wv3.1[0usize] = crate::lib::intvector_intrinsics::vec128_xor(wv3.1[0usize], mask);
    for i in 0u32..10u32
    {
        let start_idx: u32 = i.wrapping_rem(10u32).wrapping_mul(16u32);
        let mut m_st: [crate::lib::intvector_intrinsics::vec128; 4] =
            [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
        let
        r0:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            (&mut m_st).split_at_mut(0usize);
        let
        r1:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r0.1.split_at_mut(1usize);
        let
        r2:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r1.1.split_at_mut(1usize);
        let
        r3:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r2.1.split_at_mut(1usize);
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
        r1.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_load32s(
                (&mut m_w)[s0 as usize],
                (&mut m_w)[s2 as usize],
                (&mut m_w)[s4 as usize],
                (&mut m_w)[s6 as usize]
            );
        r2.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_load32s(
                (&mut m_w)[s1 as usize],
                (&mut m_w)[s3 as usize],
                (&mut m_w)[s5 as usize],
                (&mut m_w)[s7 as usize]
            );
        r3.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_load32s(
                (&mut m_w)[s8 as usize],
                (&mut m_w)[s10 as usize],
                (&mut m_w)[s12 as usize],
                (&mut m_w)[s14 as usize]
            );
        r3.1[0usize] =
            crate::lib::intvector_intrinsics::vec128_load32s(
                (&mut m_w)[s9 as usize],
                (&mut m_w)[s11 as usize],
                (&mut m_w)[s13 as usize],
                (&mut m_w)[s15 as usize]
            );
        let
        x:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r1.0.split_at_mut(0usize);
        let
        y:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r2.0.split_at_mut(0usize);
        let
        z:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r3.0.split_at_mut(0usize);
        let
        w:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r3.1.split_at_mut(0usize);
        let a: u32 = 0u32;
        let b: u32 = 1u32;
        let c: u32 = 2u32;
        let d1: u32 = 3u32;
        let
        wv_a:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv3.0.split_at_mut(a.wrapping_mul(1u32) as usize);
        let
        wv_b:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a.1.split_at_mut(b.wrapping_mul(1u32) as usize - a.wrapping_mul(1u32) as usize);
        wv_b.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b.0[0usize], wv_b.1[0usize]);
        wv_b.0[0usize] = crate::lib::intvector_intrinsics::vec128_add32(wv_b.0[0usize], x.1[0usize]);
        let
        wv_a0:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b.1.split_at_mut(d1.wrapping_mul(1u32) as usize - b.wrapping_mul(1u32) as usize);
        let
        wv_b0:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a0.1.split_at_mut(a.wrapping_mul(1u32) as usize - d1.wrapping_mul(1u32) as usize);
        wv_b0.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b0.0[0usize], wv_b0.1[0usize]);
        wv_b0.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b0.0[0usize], 16u32);
        let
        wv_a1:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b0.1.split_at_mut(c.wrapping_mul(1u32) as usize - a.wrapping_mul(1u32) as usize);
        let
        wv_b1:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a1.1.split_at_mut(d1.wrapping_mul(1u32) as usize - c.wrapping_mul(1u32) as usize);
        wv_b1.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b1.0[0usize], wv_b1.1[0usize]);
        let
        wv_a2:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b1.1.split_at_mut(b.wrapping_mul(1u32) as usize - d1.wrapping_mul(1u32) as usize);
        let
        wv_b2:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a2.1.split_at_mut(c.wrapping_mul(1u32) as usize - b.wrapping_mul(1u32) as usize);
        wv_b2.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b2.0[0usize], wv_b2.1[0usize]);
        wv_b2.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b2.0[0usize], 12u32);
        let
        wv_a3:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b2.1.split_at_mut(a.wrapping_mul(1u32) as usize - c.wrapping_mul(1u32) as usize);
        let
        wv_b3:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a3.1.split_at_mut(b.wrapping_mul(1u32) as usize - a.wrapping_mul(1u32) as usize);
        wv_b3.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b3.0[0usize], wv_b3.1[0usize]);
        wv_b3.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b3.0[0usize], y.1[0usize]);
        let
        wv_a4:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b3.1.split_at_mut(d1.wrapping_mul(1u32) as usize - b.wrapping_mul(1u32) as usize);
        let
        wv_b4:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a4.1.split_at_mut(a.wrapping_mul(1u32) as usize - d1.wrapping_mul(1u32) as usize);
        wv_b4.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b4.0[0usize], wv_b4.1[0usize]);
        wv_b4.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b4.0[0usize], 8u32);
        let
        wv_a5:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b4.1.split_at_mut(c.wrapping_mul(1u32) as usize - a.wrapping_mul(1u32) as usize);
        let
        wv_b5:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a5.1.split_at_mut(d1.wrapping_mul(1u32) as usize - c.wrapping_mul(1u32) as usize);
        wv_b5.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b5.0[0usize], wv_b5.1[0usize]);
        let
        wv_a6:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b5.1.split_at_mut(b.wrapping_mul(1u32) as usize - d1.wrapping_mul(1u32) as usize);
        let
        wv_b6:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a6.1.split_at_mut(c.wrapping_mul(1u32) as usize - b.wrapping_mul(1u32) as usize);
        wv_b6.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b6.0[0usize], wv_b6.1[0usize]);
        wv_b6.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b6.0[0usize], 7u32);
        let
        r10:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b6.1.split_at_mut(1usize - c.wrapping_mul(1u32) as usize);
        let
        r20:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r10.1.split_at_mut(1usize);
        let
        r30:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv3.1.split_at_mut(0usize);
        let v0: crate::lib::intvector_intrinsics::vec128 = r20.0[0usize];
        let v1: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_rotate_right_lanes32(v0, 1u32);
        r20.0[0usize] = v1;
        let v00: crate::lib::intvector_intrinsics::vec128 = r20.1[0usize];
        let v10: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_rotate_right_lanes32(v00, 2u32);
        r20.1[0usize] = v10;
        let v01: crate::lib::intvector_intrinsics::vec128 = r30.1[0usize];
        let v11: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_rotate_right_lanes32(v01, 3u32);
        r30.1[0usize] = v11;
        let a0: u32 = 0u32;
        let b0: u32 = 1u32;
        let c0: u32 = 2u32;
        let d10: u32 = 3u32;
        let
        wv_a7:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r10.0.split_at_mut(a0.wrapping_mul(1u32) as usize - c.wrapping_mul(1u32) as usize);
        let
        wv_b7:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a7.1.split_at_mut(b0.wrapping_mul(1u32) as usize - a0.wrapping_mul(1u32) as usize);
        wv_b7.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b7.0[0usize], wv_b7.1[0usize]);
        wv_b7.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b7.0[0usize], z.1[0usize]);
        let
        wv_a8:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b7.1.split_at_mut(d10.wrapping_mul(1u32) as usize - b0.wrapping_mul(1u32) as usize);
        let
        wv_b8:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a8.1.split_at_mut(a0.wrapping_mul(1u32) as usize - d10.wrapping_mul(1u32) as usize);
        wv_b8.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b8.0[0usize], wv_b8.1[0usize]);
        wv_b8.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b8.0[0usize], 16u32);
        let
        wv_a9:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b8.1.split_at_mut(c0.wrapping_mul(1u32) as usize - a0.wrapping_mul(1u32) as usize);
        let
        wv_b9:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a9.1.split_at_mut(d10.wrapping_mul(1u32) as usize - c0.wrapping_mul(1u32) as usize);
        wv_b9.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b9.0[0usize], wv_b9.1[0usize]);
        let
        wv_a10:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b9.1.split_at_mut(b0.wrapping_mul(1u32) as usize - d10.wrapping_mul(1u32) as usize);
        let
        wv_b10:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a10.1.split_at_mut(c0.wrapping_mul(1u32) as usize - b0.wrapping_mul(1u32) as usize);
        wv_b10.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b10.0[0usize], wv_b10.1[0usize]);
        wv_b10.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b10.0[0usize], 12u32);
        let
        wv_a11:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b10.1.split_at_mut(a0.wrapping_mul(1u32) as usize - c0.wrapping_mul(1u32) as usize);
        let
        wv_b11:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a11.1.split_at_mut(b0.wrapping_mul(1u32) as usize - a0.wrapping_mul(1u32) as usize);
        wv_b11.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b11.0[0usize], wv_b11.1[0usize]);
        wv_b11.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b11.0[0usize], w.1[0usize]);
        let
        wv_a12:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b11.1.split_at_mut(d10.wrapping_mul(1u32) as usize - b0.wrapping_mul(1u32) as usize);
        let
        wv_b12:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a12.1.split_at_mut(a0.wrapping_mul(1u32) as usize - d10.wrapping_mul(1u32) as usize);
        wv_b12.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b12.0[0usize], wv_b12.1[0usize]);
        wv_b12.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b12.0[0usize], 8u32);
        let
        wv_a13:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b12.1.split_at_mut(c0.wrapping_mul(1u32) as usize - a0.wrapping_mul(1u32) as usize);
        let
        wv_b13:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a13.1.split_at_mut(d10.wrapping_mul(1u32) as usize - c0.wrapping_mul(1u32) as usize);
        wv_b13.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_add32(wv_b13.0[0usize], wv_b13.1[0usize]);
        let
        wv_a14:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_b13.1.split_at_mut(b0.wrapping_mul(1u32) as usize - d10.wrapping_mul(1u32) as usize);
        let
        wv_b14:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            wv_a14.1.split_at_mut(c0.wrapping_mul(1u32) as usize - b0.wrapping_mul(1u32) as usize);
        wv_b14.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_xor(wv_b14.0[0usize], wv_b14.1[0usize]);
        wv_b14.0[0usize] =
            crate::lib::intvector_intrinsics::vec128_rotate_right32(wv_b14.0[0usize], 7u32);
        let
        r11:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r20.0.split_at_mut(0usize);
        let
        r21:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r20.1.split_at_mut(0usize);
        let
        r31:
        (&mut [crate::lib::intvector_intrinsics::vec128],
        &mut [crate::lib::intvector_intrinsics::vec128])
        =
            r30.1.split_at_mut(0usize);
        let v02: crate::lib::intvector_intrinsics::vec128 = r11.1[0usize];
        let v12: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_rotate_right_lanes32(v02, 3u32);
        r11.1[0usize] = v12;
        let v03: crate::lib::intvector_intrinsics::vec128 = r21.1[0usize];
        let v13: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_rotate_right_lanes32(v03, 2u32);
        r21.1[0usize] = v13;
        let v04: crate::lib::intvector_intrinsics::vec128 = r31.1[0usize];
        let v14: crate::lib::intvector_intrinsics::vec128 =
            crate::lib::intvector_intrinsics::vec128_rotate_right_lanes32(v04, 1u32);
        r31.1[0usize] = v14
    };
    let
    s0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        hash.split_at_mut(0usize);
    let
    s1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        s0.1.split_at_mut(1usize);
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        wv3.0.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        wv3.1.split_at_mut(0usize);
    s1.0[0usize] = crate::lib::intvector_intrinsics::vec128_xor(s1.0[0usize], r1.0[0usize]);
    s1.0[0usize] = crate::lib::intvector_intrinsics::vec128_xor(s1.0[0usize], r2.1[0usize]);
    s1.1[0usize] = crate::lib::intvector_intrinsics::vec128_xor(s1.1[0usize], r2.0[0usize]);
    s1.1[0usize] = crate::lib::intvector_intrinsics::vec128_xor(s1.1[0usize], r3.1[0usize])
}

pub fn blake2s_init(hash: &mut [crate::lib::intvector_intrinsics::vec128], kk: u32, nn: u32) ->
    ()
{
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        hash.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r2.1.split_at_mut(1usize);
    let iv0: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[0usize];
    let iv1: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[1usize];
    let iv2: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[2usize];
    let iv3: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[3usize];
    let iv4: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[4usize];
    let iv5: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[5usize];
    let iv6: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[6usize];
    let iv7: u32 = (&crate::hacl::impl_blake2_constants::ivTable_S)[7usize];
    r3.0[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv0, iv1, iv2, iv3);
    r3.1[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv4, iv5, iv6, iv7);
    let kk_shift_8: u32 = kk.wrapping_shl(8u32);
    let iv0_: u32 = iv0 ^ (0x01010000u32 ^ (kk_shift_8 ^ nn));
    r1.0[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv0_, iv1, iv2, iv3);
    r2.0[0usize] = crate::lib::intvector_intrinsics::vec128_load32s(iv4, iv5, iv6, iv7)
}

pub fn blake2s_update_key(
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
    kk: u32,
    k: &mut [u8],
    ll: u32
) ->
    ()
{
    let lb: u64 = 64u32 as u64;
    let mut b: [u8; 64] = [0u8; 64usize];
    ((&mut b)[0usize..kk as usize]).copy_from_slice(&k[0usize..kk as usize]);
    if ll == 0u32
    { blake2s_update_block(wv, hash, true, lb, &mut b) }
    else
    { blake2s_update_block(wv, hash, false, lb, &mut b) };
    crate::lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

pub fn blake2s_update_multi(
    len: u32,
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
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
        blake2s_update_block(wv, hash, false, totlen, b.1)
    }
}

pub fn blake2s_update_last(
    len: u32,
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
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
    blake2s_update_block(wv, hash, true, totlen, &mut b);
    crate::lib::memzero0::memzero::<u8>(&mut b, 64u32)
}

#[inline] fn blake2s_update(
    wv: &mut [crate::lib::intvector_intrinsics::vec128],
    hash: &mut [crate::lib::intvector_intrinsics::vec128],
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
        blake2s_update_key(wv, hash, kk, k, ll);
        if ! ll == 0u32 { crate::hacl::blake2s_128::blake2s_update_blocks(ll, wv, hash, lb, d) }
    }
    else
    { crate::hacl::blake2s_128::blake2s_update_blocks(ll, wv, hash, 0u32 as u64, d) }
}

pub fn blake2s_finish(
    nn: u32,
    output: &mut [u8],
    hash: &mut [crate::lib::intvector_intrinsics::vec128]
) ->
    ()
{
    let mut b: [u8; 32] = [0u8; 32usize];
    let first: (&mut [u8], &mut [u8]) = (&mut b).split_at_mut(0usize);
    let second: (&mut [u8], &mut [u8]) = first.1.split_at_mut(16usize);
    let
    row0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        hash.split_at_mut(0usize);
    let
    row1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        row0.1.split_at_mut(1usize);
    crate::lib::intvector_intrinsics::vec128_store32_le(second.0, row1.0[0usize]);
    crate::lib::intvector_intrinsics::vec128_store32_le(second.1, row1.1[0usize]);
    let r#final: (&mut [u8], &mut [u8]) = second.0.split_at_mut(0usize);
    (output[0usize..nn as usize]).copy_from_slice(&r#final.1[0usize..nn as usize]);
    crate::lib::memzero0::memzero::<u8>(r#final.0, 32u32)
}

pub fn blake2s(nn: u32, output: &mut [u8], ll: u32, d: &mut [u8], kk: u32, k: &mut [u8]) -> ()
{
    let mut b: [crate::lib::intvector_intrinsics::vec128; 4] =
        [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    let mut b1: [crate::lib::intvector_intrinsics::vec128; 4] =
        [crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    blake2s_init(&mut b, kk, nn);
    blake2s_update(&mut b1, &mut b, kk, k, ll, d);
    blake2s_finish(nn, output, &mut b);
    crate::lib::memzero0::memzero::<crate::lib::intvector_intrinsics::vec128>(&mut b1, 4u32);
    crate::lib::memzero0::memzero::<crate::lib::intvector_intrinsics::vec128>(&mut b, 4u32)
}

pub fn store_state128s_to_state32(
    st32: &mut [u32],
    st: &mut [crate::lib::intvector_intrinsics::vec128]
) ->
    ()
{
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        st.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r2.1.split_at_mut(1usize);
    let b0: (&mut [u32], &mut [u32]) = st32.split_at_mut(0usize);
    let b1: (&mut [u32], &mut [u32]) = b0.1.split_at_mut(4usize);
    let b2: (&mut [u32], &mut [u32]) = b1.1.split_at_mut(4usize);
    let b3: (&mut [u32], &mut [u32]) = b2.1.split_at_mut(4usize);
    let mut b8: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b8, r1.0[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b1.0.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) = (&mut b8).split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut b80: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b80, r2.0[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b2.0.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) = (&mut b80).split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut b81: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b81, r3.0[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b3.0.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) = (&mut b81).split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    };
    let mut b82: [u8; 16] = [0u8; 16usize];
    crate::lib::intvector_intrinsics::vec128_store32_le(&mut b82, r3.1[0usize]);
    for i in 0u32..4u32
    {
        let os: (&mut [u32], &mut [u32]) = b3.1.split_at_mut(0usize);
        let bj: (&mut [u8], &mut [u8]) = (&mut b82).split_at_mut(i.wrapping_mul(4u32) as usize);
        let u: u32 = crate::lowstar::endianness::load32_le(bj.1);
        let r: u32 = u;
        let x: u32 = r;
        os.1[i as usize] = x
    }
}

pub fn load_state128s_from_state32(
    st: &mut [crate::lib::intvector_intrinsics::vec128],
    st32: &mut [u32]
) ->
    ()
{
    let
    r0:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        st.split_at_mut(0usize);
    let
    r1:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r0.1.split_at_mut(1usize);
    let
    r2:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r1.1.split_at_mut(1usize);
    let
    r3:
    (&mut [crate::lib::intvector_intrinsics::vec128],
    &mut [crate::lib::intvector_intrinsics::vec128])
    =
        r2.1.split_at_mut(1usize);
    let b0: (&mut [u32], &mut [u32]) = st32.split_at_mut(0usize);
    let b1: (&mut [u32], &mut [u32]) = b0.1.split_at_mut(4usize);
    let b2: (&mut [u32], &mut [u32]) = b1.1.split_at_mut(4usize);
    let b3: (&mut [u32], &mut [u32]) = b2.1.split_at_mut(4usize);
    r1.0[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b1.0[0usize],
            b1.0[1usize],
            b1.0[2usize],
            b1.0[3usize]
        );
    r2.0[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b2.0[0usize],
            b2.0[1usize],
            b2.0[2usize],
            b2.0[3usize]
        );
    r3.0[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b3.0[0usize],
            b3.0[1usize],
            b3.0[2usize],
            b3.0[3usize]
        );
    r3.1[0usize] =
        crate::lib::intvector_intrinsics::vec128_load32s(
            b3.1[0usize],
            b3.1[1usize],
            b3.1[2usize],
            b3.1[3usize]
        )
}

pub fn blake2s_malloc() -> &mut [crate::lib::intvector_intrinsics::vec128]
{
    let mut buf: Vec<crate::lib::intvector_intrinsics::vec128> =
        vec![crate::lib::intvector_intrinsics::vec128_zero; 4usize];
    &mut buf
}
