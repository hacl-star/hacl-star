#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]

#[inline] fn sha224_init8(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
{
    for i in 0u32..8u32
    {
        let hi: u32 = (&crate::hacl::hash_sha2::h224)[i as usize];
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load32(hi);
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha224_update8(
    b: crate::hacl::sha2_types::uint8_8p,
    hash: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    let mut hash_old: [crate::lib::intvector_intrinsics::vec256; 8] =
        [crate::lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 16] =
        [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    let b7: &mut [u8] = b.snd.snd.snd.snd.snd.snd.snd;
    let b6: &mut [u8] = b.snd.snd.snd.snd.snd.snd.fst;
    let b5: &mut [u8] = b.snd.snd.snd.snd.snd.fst;
    let b4: &mut [u8] = b.snd.snd.snd.snd.fst;
    let b3: &mut [u8] = b.snd.snd.snd.fst;
    let b2: &mut [u8] = b.snd.snd.fst;
    let b1: &mut [u8] = b.snd.fst;
    let b0: &mut [u8] = b.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b0[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b1[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b2[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b3[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b4[0usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b5[0usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b6[0usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b7[0usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b0[32usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b1[32usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b2[32usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b3[32usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b4[32usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b5[32usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b6[32usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b7[32usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v4: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v5: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v6: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v7: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: crate::lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: crate::lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: crate::lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: crate::lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: crate::lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: crate::lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: crate::lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: crate::lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: crate::lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: crate::lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: crate::lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: crate::lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: crate::lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: crate::lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: crate::lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: crate::lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: crate::lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: crate::lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: crate::lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: crate::lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: crate::lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: crate::lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: crate::lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: crate::lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: crate::lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: crate::lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: crate::lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: crate::lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: crate::lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: crate::lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: crate::lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: crate::lib::intvector_intrinsics::vec256 = v7·20;
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0·3;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2·3;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1·3;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3·3;
    let ws4: crate::lib::intvector_intrinsics::vec256 = v4·3;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v6·3;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v5·3;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v7·3;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v40: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v50: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v60: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v70: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v00, v10);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v00, v10);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v20, v30);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v20, v30);
    let v4·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v40, v50);
    let v5·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v40, v50);
    let v6·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v60, v70);
    let v7·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v60, v70);
    let v0·5: crate::lib::intvector_intrinsics::vec256 = v0·4;
    let v1·5: crate::lib::intvector_intrinsics::vec256 = v1·4;
    let v2·5: crate::lib::intvector_intrinsics::vec256 = v2·4;
    let v3·5: crate::lib::intvector_intrinsics::vec256 = v3·4;
    let v4·5: crate::lib::intvector_intrinsics::vec256 = v4·4;
    let v5·5: crate::lib::intvector_intrinsics::vec256 = v5·4;
    let v6·5: crate::lib::intvector_intrinsics::vec256 = v6·4;
    let v7·5: crate::lib::intvector_intrinsics::vec256 = v7·4;
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0·5, v2·5);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0·5, v2·5);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v1·5, v3·5);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v1·5, v3·5);
    let v4·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v4·5, v6·5);
    let v6·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v4·5, v6·5);
    let v5·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v5·5, v7·5);
    let v7·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v5·5, v7·5);
    let v0·12: crate::lib::intvector_intrinsics::vec256 = v0·11;
    let v1·12: crate::lib::intvector_intrinsics::vec256 = v1·11;
    let v2·12: crate::lib::intvector_intrinsics::vec256 = v2·11;
    let v3·12: crate::lib::intvector_intrinsics::vec256 = v3·11;
    let v4·12: crate::lib::intvector_intrinsics::vec256 = v4·11;
    let v5·12: crate::lib::intvector_intrinsics::vec256 = v5·11;
    let v6·12: crate::lib::intvector_intrinsics::vec256 = v6·11;
    let v7·12: crate::lib::intvector_intrinsics::vec256 = v7·11;
    let v0·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v4·12);
    let v4·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v4·12);
    let v1·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v5·12);
    let v5·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v5·12);
    let v2·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v2·12, v6·12);
    let v6·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v2·12, v6·12);
    let v3·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v3·12, v7·12);
    let v7·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v3·12, v7·12);
    let v0·22: crate::lib::intvector_intrinsics::vec256 = v0·21;
    let v1·22: crate::lib::intvector_intrinsics::vec256 = v1·21;
    let v2·22: crate::lib::intvector_intrinsics::vec256 = v2·21;
    let v3·22: crate::lib::intvector_intrinsics::vec256 = v3·21;
    let v4·22: crate::lib::intvector_intrinsics::vec256 = v4·21;
    let v5·22: crate::lib::intvector_intrinsics::vec256 = v5·21;
    let v6·22: crate::lib::intvector_intrinsics::vec256 = v6·21;
    let v7·22: crate::lib::intvector_intrinsics::vec256 = v7·21;
    let v0·6: crate::lib::intvector_intrinsics::vec256 = v0·22;
    let v1·6: crate::lib::intvector_intrinsics::vec256 = v1·22;
    let v2·6: crate::lib::intvector_intrinsics::vec256 = v2·22;
    let v3·6: crate::lib::intvector_intrinsics::vec256 = v3·22;
    let v4·6: crate::lib::intvector_intrinsics::vec256 = v4·22;
    let v5·6: crate::lib::intvector_intrinsics::vec256 = v5·22;
    let v6·6: crate::lib::intvector_intrinsics::vec256 = v6·22;
    let v7·6: crate::lib::intvector_intrinsics::vec256 = v7·22;
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0·6;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2·6;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1·6;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3·6;
    let ws12: crate::lib::intvector_intrinsics::vec256 = v4·6;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v6·6;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v5·6;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v7·6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    for i in 0u32..4u32
    {
        for i0 in 0u32..16u32
        {
            let k_t: u32 =
                (&crate::hacl::hash_sha2::k224_256)[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
            let ws_t: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
            let a0: crate::lib::intvector_intrinsics::vec256 = hash[0usize];
            let b00: crate::lib::intvector_intrinsics::vec256 = hash[1usize];
            let c0: crate::lib::intvector_intrinsics::vec256 = hash[2usize];
            let d0: crate::lib::intvector_intrinsics::vec256 = hash[3usize];
            let e0: crate::lib::intvector_intrinsics::vec256 = hash[4usize];
            let f0: crate::lib::intvector_intrinsics::vec256 = hash[5usize];
            let g0: crate::lib::intvector_intrinsics::vec256 = hash[6usize];
            let h02: crate::lib::intvector_intrinsics::vec256 = hash[7usize];
            let k_e_t: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load32(k_t);
            let t1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(
                    crate::lib::intvector_intrinsics::vec256_add32(
                        crate::lib::intvector_intrinsics::vec256_add32(
                            crate::lib::intvector_intrinsics::vec256_add32(
                                h02,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    crate::lib::intvector_intrinsics::vec256_rotate_right32(
                                        e0,
                                        6u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        crate::lib::intvector_intrinsics::vec256_rotate_right32(
                                            e0,
                                            11u32
                                        ),
                                        crate::lib::intvector_intrinsics::vec256_rotate_right32(
                                            e0,
                                            25u32
                                        )
                                    )
                                )
                            ),
                            crate::lib::intvector_intrinsics::vec256_xor(
                                crate::lib::intvector_intrinsics::vec256_and(e0, f0),
                                crate::lib::intvector_intrinsics::vec256_and(
                                    crate::lib::intvector_intrinsics::vec256_lognot(e0),
                                    g0
                                )
                            )
                        ),
                        k_e_t
                    ),
                    ws_t
                );
            let t2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right32(a0, 2u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(a0, 13u32),
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(a0, 22u32)
                        )
                    ),
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_and(a0, b00),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_and(a0, c0),
                            crate::lib::intvector_intrinsics::vec256_and(b00, c0)
                        )
                    )
                );
            let a1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(t1, t2);
            let b10: crate::lib::intvector_intrinsics::vec256 = a0;
            let c1: crate::lib::intvector_intrinsics::vec256 = b00;
            let d1: crate::lib::intvector_intrinsics::vec256 = c0;
            let e1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(d0, t1);
            let f1: crate::lib::intvector_intrinsics::vec256 = e0;
            let g1: crate::lib::intvector_intrinsics::vec256 = f0;
            let h12: crate::lib::intvector_intrinsics::vec256 = g0;
            hash[0usize] = a1;
            hash[1usize] = b10;
            hash[2usize] = c1;
            hash[3usize] = d1;
            hash[4usize] = e1;
            hash[5usize] = f1;
            hash[6usize] = g1;
            hash[7usize] = h12
        };
        if i < 3u32
        {
            for i0 in 0u32..16u32
            {
                let t16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
                let t15: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                let t7: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                let t2: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                let s1: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right32(t2, 17u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(t2, 19u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right32(t2, 10u32)
                        )
                    );
                let s0: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right32(t15, 7u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(t15, 18u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right32(t15, 3u32)
                        )
                    );
                (&mut ws)[i0 as usize] =
                    crate::lib::intvector_intrinsics::vec256_add32(
                        crate::lib::intvector_intrinsics::vec256_add32(
                            crate::lib::intvector_intrinsics::vec256_add32(s1, t7),
                            s0
                        ),
                        t16
                    )
            }
        }
    };
    for i in 0u32..8u32
    {
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add32(
                hash[i as usize],
                (&mut hash_old)[i as usize]
            );
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha224_finish8(
    st: &mut [crate::lib::intvector_intrinsics::vec256],
    h: crate::hacl::sha2_types::uint8_8p
) ->
    ()
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: crate::lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = st[3usize];
    let v4: crate::lib::intvector_intrinsics::vec256 = st[4usize];
    let v5: crate::lib::intvector_intrinsics::vec256 = st[5usize];
    let v6: crate::lib::intvector_intrinsics::vec256 = st[6usize];
    let v7: crate::lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: crate::lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: crate::lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: crate::lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: crate::lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: crate::lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: crate::lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: crate::lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: crate::lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: crate::lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: crate::lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: crate::lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: crate::lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: crate::lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: crate::lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: crate::lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: crate::lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: crate::lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: crate::lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: crate::lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: crate::lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: crate::lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: crate::lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: crate::lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: crate::lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: crate::lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: crate::lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: crate::lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: crate::lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: crate::lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: crate::lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: crate::lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: crate::lib::intvector_intrinsics::vec256 = v7·20;
    let st0·: crate::lib::intvector_intrinsics::vec256 = v0·3;
    let st1·: crate::lib::intvector_intrinsics::vec256 = v2·3;
    let st2·: crate::lib::intvector_intrinsics::vec256 = v1·3;
    let st3·: crate::lib::intvector_intrinsics::vec256 = v3·3;
    let st4·: crate::lib::intvector_intrinsics::vec256 = v4·3;
    let st5·: crate::lib::intvector_intrinsics::vec256 = v6·3;
    let st6·: crate::lib::intvector_intrinsics::vec256 = v5·3;
    let st7·: crate::lib::intvector_intrinsics::vec256 = v7·3;
    st[0usize] = st0·;
    st[1usize] = st1·;
    st[2usize] = st2·;
    st[3usize] = st3·;
    st[4usize] = st4·;
    st[5usize] = st5·;
    st[6usize] = st6·;
    st[7usize] = st7·;
    for i in 0u32..8u32
    {
        crate::lib::intvector_intrinsics::vec256_store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    };
    let b7: &mut [u8] = h.snd.snd.snd.snd.snd.snd.snd;
    let b6: &mut [u8] = h.snd.snd.snd.snd.snd.snd.fst;
    let b5: &mut [u8] = h.snd.snd.snd.snd.snd.fst;
    let b4: &mut [u8] = h.snd.snd.snd.snd.fst;
    let b3: &mut [u8] = h.snd.snd.snd.fst;
    let b2: &mut [u8] = h.snd.snd.fst;
    let b1: &mut [u8] = h.snd.fst;
    let b0: &mut [u8] = h.fst;
    (b0[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..28usize]);
    (b1[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[32usize..])[0usize..28usize]);
    (b2[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[64usize..])[0usize..28usize]);
    (b3[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[96usize..])[0usize..28usize]);
    (b4[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[128usize..])[0usize..28usize]);
    (b5[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[160usize..])[0usize..28usize]);
    (b6[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[192usize..])[0usize..28usize]);
    (b7[0usize..28usize]).copy_from_slice(&(&mut (&mut hbuf)[224usize..])[0usize..28usize])
}

#[inline] fn sha256_init8(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
{
    for i in 0u32..8u32
    {
        let hi: u32 = (&crate::hacl::hash_sha2::h256)[i as usize];
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load32(hi);
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha256_update8(
    b: crate::hacl::sha2_types::uint8_8p,
    hash: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    let mut hash_old: [crate::lib::intvector_intrinsics::vec256; 8] =
        [crate::lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 16] =
        [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    let b7: &mut [u8] = b.snd.snd.snd.snd.snd.snd.snd;
    let b6: &mut [u8] = b.snd.snd.snd.snd.snd.snd.fst;
    let b5: &mut [u8] = b.snd.snd.snd.snd.snd.fst;
    let b4: &mut [u8] = b.snd.snd.snd.snd.fst;
    let b3: &mut [u8] = b.snd.snd.snd.fst;
    let b2: &mut [u8] = b.snd.snd.fst;
    let b1: &mut [u8] = b.snd.fst;
    let b0: &mut [u8] = b.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b0[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b1[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b2[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b3[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b4[0usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b5[0usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b6[0usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b7[0usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b0[32usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b1[32usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b2[32usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b3[32usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b4[32usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b5[32usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b6[32usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load32_be(&mut b7[32usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v4: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v5: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v6: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v7: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: crate::lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: crate::lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: crate::lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: crate::lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: crate::lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: crate::lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: crate::lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: crate::lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: crate::lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: crate::lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: crate::lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: crate::lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: crate::lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: crate::lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: crate::lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: crate::lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: crate::lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: crate::lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: crate::lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: crate::lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: crate::lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: crate::lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: crate::lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: crate::lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: crate::lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: crate::lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: crate::lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: crate::lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: crate::lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: crate::lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: crate::lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: crate::lib::intvector_intrinsics::vec256 = v7·20;
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0·3;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2·3;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1·3;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3·3;
    let ws4: crate::lib::intvector_intrinsics::vec256 = v4·3;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v6·3;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v5·3;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v7·3;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v40: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v50: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v60: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v70: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v00, v10);
    let v1·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v00, v10);
    let v2·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v20, v30);
    let v3·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v20, v30);
    let v4·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v40, v50);
    let v5·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v40, v50);
    let v6·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v60, v70);
    let v7·4: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v60, v70);
    let v0·5: crate::lib::intvector_intrinsics::vec256 = v0·4;
    let v1·5: crate::lib::intvector_intrinsics::vec256 = v1·4;
    let v2·5: crate::lib::intvector_intrinsics::vec256 = v2·4;
    let v3·5: crate::lib::intvector_intrinsics::vec256 = v3·4;
    let v4·5: crate::lib::intvector_intrinsics::vec256 = v4·4;
    let v5·5: crate::lib::intvector_intrinsics::vec256 = v5·4;
    let v6·5: crate::lib::intvector_intrinsics::vec256 = v6·4;
    let v7·5: crate::lib::intvector_intrinsics::vec256 = v7·4;
    let v0·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0·5, v2·5);
    let v2·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0·5, v2·5);
    let v1·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v1·5, v3·5);
    let v3·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v1·5, v3·5);
    let v4·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v4·5, v6·5);
    let v6·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v4·5, v6·5);
    let v5·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v5·5, v7·5);
    let v7·11: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v5·5, v7·5);
    let v0·12: crate::lib::intvector_intrinsics::vec256 = v0·11;
    let v1·12: crate::lib::intvector_intrinsics::vec256 = v1·11;
    let v2·12: crate::lib::intvector_intrinsics::vec256 = v2·11;
    let v3·12: crate::lib::intvector_intrinsics::vec256 = v3·11;
    let v4·12: crate::lib::intvector_intrinsics::vec256 = v4·11;
    let v5·12: crate::lib::intvector_intrinsics::vec256 = v5·11;
    let v6·12: crate::lib::intvector_intrinsics::vec256 = v6·11;
    let v7·12: crate::lib::intvector_intrinsics::vec256 = v7·11;
    let v0·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v4·12);
    let v4·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v4·12);
    let v1·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v5·12);
    let v5·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v5·12);
    let v2·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v2·12, v6·12);
    let v6·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v2·12, v6·12);
    let v3·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v3·12, v7·12);
    let v7·21: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v3·12, v7·12);
    let v0·22: crate::lib::intvector_intrinsics::vec256 = v0·21;
    let v1·22: crate::lib::intvector_intrinsics::vec256 = v1·21;
    let v2·22: crate::lib::intvector_intrinsics::vec256 = v2·21;
    let v3·22: crate::lib::intvector_intrinsics::vec256 = v3·21;
    let v4·22: crate::lib::intvector_intrinsics::vec256 = v4·21;
    let v5·22: crate::lib::intvector_intrinsics::vec256 = v5·21;
    let v6·22: crate::lib::intvector_intrinsics::vec256 = v6·21;
    let v7·22: crate::lib::intvector_intrinsics::vec256 = v7·21;
    let v0·6: crate::lib::intvector_intrinsics::vec256 = v0·22;
    let v1·6: crate::lib::intvector_intrinsics::vec256 = v1·22;
    let v2·6: crate::lib::intvector_intrinsics::vec256 = v2·22;
    let v3·6: crate::lib::intvector_intrinsics::vec256 = v3·22;
    let v4·6: crate::lib::intvector_intrinsics::vec256 = v4·22;
    let v5·6: crate::lib::intvector_intrinsics::vec256 = v5·22;
    let v6·6: crate::lib::intvector_intrinsics::vec256 = v6·22;
    let v7·6: crate::lib::intvector_intrinsics::vec256 = v7·22;
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0·6;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2·6;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1·6;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3·6;
    let ws12: crate::lib::intvector_intrinsics::vec256 = v4·6;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v6·6;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v5·6;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v7·6;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    for i in 0u32..4u32
    {
        for i0 in 0u32..16u32
        {
            let k_t: u32 =
                (&crate::hacl::hash_sha2::k224_256)[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
            let ws_t: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
            let a0: crate::lib::intvector_intrinsics::vec256 = hash[0usize];
            let b00: crate::lib::intvector_intrinsics::vec256 = hash[1usize];
            let c0: crate::lib::intvector_intrinsics::vec256 = hash[2usize];
            let d0: crate::lib::intvector_intrinsics::vec256 = hash[3usize];
            let e0: crate::lib::intvector_intrinsics::vec256 = hash[4usize];
            let f0: crate::lib::intvector_intrinsics::vec256 = hash[5usize];
            let g0: crate::lib::intvector_intrinsics::vec256 = hash[6usize];
            let h02: crate::lib::intvector_intrinsics::vec256 = hash[7usize];
            let k_e_t: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load32(k_t);
            let t1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(
                    crate::lib::intvector_intrinsics::vec256_add32(
                        crate::lib::intvector_intrinsics::vec256_add32(
                            crate::lib::intvector_intrinsics::vec256_add32(
                                h02,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    crate::lib::intvector_intrinsics::vec256_rotate_right32(
                                        e0,
                                        6u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        crate::lib::intvector_intrinsics::vec256_rotate_right32(
                                            e0,
                                            11u32
                                        ),
                                        crate::lib::intvector_intrinsics::vec256_rotate_right32(
                                            e0,
                                            25u32
                                        )
                                    )
                                )
                            ),
                            crate::lib::intvector_intrinsics::vec256_xor(
                                crate::lib::intvector_intrinsics::vec256_and(e0, f0),
                                crate::lib::intvector_intrinsics::vec256_and(
                                    crate::lib::intvector_intrinsics::vec256_lognot(e0),
                                    g0
                                )
                            )
                        ),
                        k_e_t
                    ),
                    ws_t
                );
            let t2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right32(a0, 2u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(a0, 13u32),
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(a0, 22u32)
                        )
                    ),
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_and(a0, b00),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_and(a0, c0),
                            crate::lib::intvector_intrinsics::vec256_and(b00, c0)
                        )
                    )
                );
            let a1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(t1, t2);
            let b10: crate::lib::intvector_intrinsics::vec256 = a0;
            let c1: crate::lib::intvector_intrinsics::vec256 = b00;
            let d1: crate::lib::intvector_intrinsics::vec256 = c0;
            let e1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add32(d0, t1);
            let f1: crate::lib::intvector_intrinsics::vec256 = e0;
            let g1: crate::lib::intvector_intrinsics::vec256 = f0;
            let h12: crate::lib::intvector_intrinsics::vec256 = g0;
            hash[0usize] = a1;
            hash[1usize] = b10;
            hash[2usize] = c1;
            hash[3usize] = d1;
            hash[4usize] = e1;
            hash[5usize] = f1;
            hash[6usize] = g1;
            hash[7usize] = h12
        };
        if i < 3u32
        {
            for i0 in 0u32..16u32
            {
                let t16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
                let t15: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                let t7: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                let t2: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                let s1: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right32(t2, 17u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(t2, 19u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right32(t2, 10u32)
                        )
                    );
                let s0: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right32(t15, 7u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right32(t15, 18u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right32(t15, 3u32)
                        )
                    );
                (&mut ws)[i0 as usize] =
                    crate::lib::intvector_intrinsics::vec256_add32(
                        crate::lib::intvector_intrinsics::vec256_add32(
                            crate::lib::intvector_intrinsics::vec256_add32(s1, t7),
                            s0
                        ),
                        t16
                    )
            }
        }
    };
    for i in 0u32..8u32
    {
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add32(
                hash[i as usize],
                (&mut hash_old)[i as usize]
            );
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha256_finish8(
    st: &mut [crate::lib::intvector_intrinsics::vec256],
    h: crate::hacl::sha2_types::uint8_8p
) ->
    ()
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: crate::lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = st[3usize];
    let v4: crate::lib::intvector_intrinsics::vec256 = st[4usize];
    let v5: crate::lib::intvector_intrinsics::vec256 = st[5usize];
    let v6: crate::lib::intvector_intrinsics::vec256 = st[6usize];
    let v7: crate::lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: crate::lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: crate::lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: crate::lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: crate::lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: crate::lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: crate::lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: crate::lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: crate::lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: crate::lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: crate::lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: crate::lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: crate::lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: crate::lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: crate::lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: crate::lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: crate::lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: crate::lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: crate::lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: crate::lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: crate::lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: crate::lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: crate::lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: crate::lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: crate::lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: crate::lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: crate::lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: crate::lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: crate::lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: crate::lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: crate::lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: crate::lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: crate::lib::intvector_intrinsics::vec256 = v7·20;
    let st0·: crate::lib::intvector_intrinsics::vec256 = v0·3;
    let st1·: crate::lib::intvector_intrinsics::vec256 = v2·3;
    let st2·: crate::lib::intvector_intrinsics::vec256 = v1·3;
    let st3·: crate::lib::intvector_intrinsics::vec256 = v3·3;
    let st4·: crate::lib::intvector_intrinsics::vec256 = v4·3;
    let st5·: crate::lib::intvector_intrinsics::vec256 = v6·3;
    let st6·: crate::lib::intvector_intrinsics::vec256 = v5·3;
    let st7·: crate::lib::intvector_intrinsics::vec256 = v7·3;
    st[0usize] = st0·;
    st[1usize] = st1·;
    st[2usize] = st2·;
    st[3usize] = st3·;
    st[4usize] = st4·;
    st[5usize] = st5·;
    st[6usize] = st6·;
    st[7usize] = st7·;
    for i in 0u32..8u32
    {
        crate::lib::intvector_intrinsics::vec256_store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    };
    let b7: &mut [u8] = h.snd.snd.snd.snd.snd.snd.snd;
    let b6: &mut [u8] = h.snd.snd.snd.snd.snd.snd.fst;
    let b5: &mut [u8] = h.snd.snd.snd.snd.snd.fst;
    let b4: &mut [u8] = h.snd.snd.snd.snd.fst;
    let b3: &mut [u8] = h.snd.snd.snd.fst;
    let b2: &mut [u8] = h.snd.snd.fst;
    let b1: &mut [u8] = h.snd.fst;
    let b0: &mut [u8] = h.fst;
    (b0[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..32usize]);
    (b1[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[32usize..])[0usize..32usize]);
    (b2[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[64usize..])[0usize..32usize]);
    (b3[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[96usize..])[0usize..32usize]);
    (b4[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[128usize..])[0usize..32usize]);
    (b5[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[160usize..])[0usize..32usize]);
    (b6[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[192usize..])[0usize..32usize]);
    (b7[0usize..32usize]).copy_from_slice(&(&mut (&mut hbuf)[224usize..])[0usize..32usize])
}

#[inline] fn sha384_init4(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
{
    for i in 0u32..8u32
    {
        let hi: u64 = (&crate::hacl::hash_sha2::h384)[i as usize];
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(hi);
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha384_update4(
    b: crate::hacl::sha2_types::uint8_4p,
    hash: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    let mut hash_old: [crate::lib::intvector_intrinsics::vec256; 8] =
        [crate::lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 16] =
        [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    let b3: &mut [u8] = b.snd.snd.snd;
    let b2: &mut [u8] = b.snd.snd.fst;
    let b1: &mut [u8] = b.snd.fst;
    let b0: &mut [u8] = b.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[96usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    for i in 0u32..5u32
    {
        for i0 in 0u32..16u32
        {
            let k_t: u64 =
                (&crate::hacl::hash_sha2::k384_512)[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
            let ws_t: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
            let a0: crate::lib::intvector_intrinsics::vec256 = hash[0usize];
            let b00: crate::lib::intvector_intrinsics::vec256 = hash[1usize];
            let c0: crate::lib::intvector_intrinsics::vec256 = hash[2usize];
            let d0: crate::lib::intvector_intrinsics::vec256 = hash[3usize];
            let e0: crate::lib::intvector_intrinsics::vec256 = hash[4usize];
            let f0: crate::lib::intvector_intrinsics::vec256 = hash[5usize];
            let g0: crate::lib::intvector_intrinsics::vec256 = hash[6usize];
            let h02: crate::lib::intvector_intrinsics::vec256 = hash[7usize];
            let k_e_t: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64(k_t);
            let t1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    crate::lib::intvector_intrinsics::vec256_add64(
                        crate::lib::intvector_intrinsics::vec256_add64(
                            crate::lib::intvector_intrinsics::vec256_add64(
                                h02,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    crate::lib::intvector_intrinsics::vec256_rotate_right64(
                                        e0,
                                        14u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        crate::lib::intvector_intrinsics::vec256_rotate_right64(
                                            e0,
                                            18u32
                                        ),
                                        crate::lib::intvector_intrinsics::vec256_rotate_right64(
                                            e0,
                                            41u32
                                        )
                                    )
                                )
                            ),
                            crate::lib::intvector_intrinsics::vec256_xor(
                                crate::lib::intvector_intrinsics::vec256_and(e0, f0),
                                crate::lib::intvector_intrinsics::vec256_and(
                                    crate::lib::intvector_intrinsics::vec256_lognot(e0),
                                    g0
                                )
                            )
                        ),
                        k_e_t
                    ),
                    ws_t
                );
            let t2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right64(a0, 28u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(a0, 34u32),
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(a0, 39u32)
                        )
                    ),
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_and(a0, b00),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_and(a0, c0),
                            crate::lib::intvector_intrinsics::vec256_and(b00, c0)
                        )
                    )
                );
            let a1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(t1, t2);
            let b10: crate::lib::intvector_intrinsics::vec256 = a0;
            let c1: crate::lib::intvector_intrinsics::vec256 = b00;
            let d1: crate::lib::intvector_intrinsics::vec256 = c0;
            let e1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(d0, t1);
            let f1: crate::lib::intvector_intrinsics::vec256 = e0;
            let g1: crate::lib::intvector_intrinsics::vec256 = f0;
            let h12: crate::lib::intvector_intrinsics::vec256 = g0;
            hash[0usize] = a1;
            hash[1usize] = b10;
            hash[2usize] = c1;
            hash[3usize] = d1;
            hash[4usize] = e1;
            hash[5usize] = f1;
            hash[6usize] = g1;
            hash[7usize] = h12
        };
        if i < 4u32
        {
            for i0 in 0u32..16u32
            {
                let t16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
                let t15: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                let t7: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                let t2: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                let s1: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right64(t2, 19u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(t2, 61u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right64(t2, 6u32)
                        )
                    );
                let s0: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right64(t15, 1u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(t15, 8u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right64(t15, 7u32)
                        )
                    );
                (&mut ws)[i0 as usize] =
                    crate::lib::intvector_intrinsics::vec256_add64(
                        crate::lib::intvector_intrinsics::vec256_add64(
                            crate::lib::intvector_intrinsics::vec256_add64(s1, t7),
                            s0
                        ),
                        t16
                    )
            }
        }
    };
    for i in 0u32..8u32
    {
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                hash[i as usize],
                (&mut hash_old)[i as usize]
            );
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha384_finish4(
    st: &mut [crate::lib::intvector_intrinsics::vec256],
    h: crate::hacl::sha2_types::uint8_4p
) ->
    ()
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: crate::lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = st[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let st0·: crate::lib::intvector_intrinsics::vec256 = v0··;
    let st1·: crate::lib::intvector_intrinsics::vec256 = v2··;
    let st2·: crate::lib::intvector_intrinsics::vec256 = v1··;
    let st3·: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = st[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = st[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = st[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let st4·: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let st5·: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let st6·: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let st7·: crate::lib::intvector_intrinsics::vec256 = v3··0;
    st[0usize] = st0·;
    st[1usize] = st4·;
    st[2usize] = st1·;
    st[3usize] = st5·;
    st[4usize] = st2·;
    st[5usize] = st6·;
    st[6usize] = st3·;
    st[7usize] = st7·;
    for i in 0u32..8u32
    {
        crate::lib::intvector_intrinsics::vec256_store64_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    };
    let b3: &mut [u8] = h.snd.snd.snd;
    let b2: &mut [u8] = h.snd.snd.fst;
    let b1: &mut [u8] = h.snd.fst;
    let b0: &mut [u8] = h.fst;
    (b0[0usize..48usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..48usize]);
    (b1[0usize..48usize]).copy_from_slice(&(&mut (&mut hbuf)[64usize..])[0usize..48usize]);
    (b2[0usize..48usize]).copy_from_slice(&(&mut (&mut hbuf)[128usize..])[0usize..48usize]);
    (b3[0usize..48usize]).copy_from_slice(&(&mut (&mut hbuf)[192usize..])[0usize..48usize])
}

#[inline] fn sha512_init4(hash: &mut [crate::lib::intvector_intrinsics::vec256]) -> ()
{
    for i in 0u32..8u32
    {
        let hi: u64 = (&crate::hacl::hash_sha2::h512)[i as usize];
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_load64(hi);
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha512_update4(
    b: crate::hacl::sha2_types::uint8_4p,
    hash: &mut [crate::lib::intvector_intrinsics::vec256]
) ->
    ()
{
    let mut hash_old: [crate::lib::intvector_intrinsics::vec256; 8] =
        [crate::lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [crate::lib::intvector_intrinsics::vec256; 16] =
        [crate::lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    let b3: &mut [u8] = b.snd.snd.snd;
    let b2: &mut [u8] = b.snd.snd.fst;
    let b1: &mut [u8] = b.snd.fst;
    let b0: &mut [u8] = b.fst;
    (&mut ws)[0usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[0usize..]);
    (&mut ws)[1usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[0usize..]);
    (&mut ws)[2usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[0usize..]);
    (&mut ws)[3usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[0usize..]);
    (&mut ws)[4usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[32usize..]);
    (&mut ws)[5usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[32usize..]);
    (&mut ws)[6usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[32usize..]);
    (&mut ws)[7usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[32usize..]);
    (&mut ws)[8usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[64usize..]);
    (&mut ws)[9usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[64usize..]);
    (&mut ws)[10usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[64usize..]);
    (&mut ws)[11usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[64usize..]);
    (&mut ws)[12usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b0[96usize..]);
    (&mut ws)[13usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b1[96usize..]);
    (&mut ws)[14usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b2[96usize..]);
    (&mut ws)[15usize] = crate::lib::intvector_intrinsics::vec256_load64_be(&mut b3[96usize..]);
    let v0: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: crate::lib::intvector_intrinsics::vec256 = v0··;
    let ws1: crate::lib::intvector_intrinsics::vec256 = v2··;
    let ws2: crate::lib::intvector_intrinsics::vec256 = v1··;
    let ws3: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: crate::lib::intvector_intrinsics::vec256 = v3··0;
    let v01: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[8usize];
    let v11: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[9usize];
    let v21: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[10usize];
    let v31: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[11usize];
    let v0·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: crate::lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: crate::lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: crate::lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: crate::lib::intvector_intrinsics::vec256 = v3··1;
    let v02: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[12usize];
    let v12: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[13usize];
    let v22: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[14usize];
    let v32: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[15usize];
    let v0·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: crate::lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: crate::lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: crate::lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: crate::lib::intvector_intrinsics::vec256 = v3··2;
    (&mut ws)[0usize] = ws0;
    (&mut ws)[1usize] = ws1;
    (&mut ws)[2usize] = ws2;
    (&mut ws)[3usize] = ws3;
    (&mut ws)[4usize] = ws4;
    (&mut ws)[5usize] = ws5;
    (&mut ws)[6usize] = ws6;
    (&mut ws)[7usize] = ws7;
    (&mut ws)[8usize] = ws8;
    (&mut ws)[9usize] = ws9;
    (&mut ws)[10usize] = ws10;
    (&mut ws)[11usize] = ws11;
    (&mut ws)[12usize] = ws12;
    (&mut ws)[13usize] = ws13;
    (&mut ws)[14usize] = ws14;
    (&mut ws)[15usize] = ws15;
    for i in 0u32..5u32
    {
        for i0 in 0u32..16u32
        {
            let k_t: u64 =
                (&crate::hacl::hash_sha2::k384_512)[16u32.wrapping_mul(i).wrapping_add(i0) as usize];
            let ws_t: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
            let a0: crate::lib::intvector_intrinsics::vec256 = hash[0usize];
            let b00: crate::lib::intvector_intrinsics::vec256 = hash[1usize];
            let c0: crate::lib::intvector_intrinsics::vec256 = hash[2usize];
            let d0: crate::lib::intvector_intrinsics::vec256 = hash[3usize];
            let e0: crate::lib::intvector_intrinsics::vec256 = hash[4usize];
            let f0: crate::lib::intvector_intrinsics::vec256 = hash[5usize];
            let g0: crate::lib::intvector_intrinsics::vec256 = hash[6usize];
            let h02: crate::lib::intvector_intrinsics::vec256 = hash[7usize];
            let k_e_t: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_load64(k_t);
            let t1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    crate::lib::intvector_intrinsics::vec256_add64(
                        crate::lib::intvector_intrinsics::vec256_add64(
                            crate::lib::intvector_intrinsics::vec256_add64(
                                h02,
                                crate::lib::intvector_intrinsics::vec256_xor(
                                    crate::lib::intvector_intrinsics::vec256_rotate_right64(
                                        e0,
                                        14u32
                                    ),
                                    crate::lib::intvector_intrinsics::vec256_xor(
                                        crate::lib::intvector_intrinsics::vec256_rotate_right64(
                                            e0,
                                            18u32
                                        ),
                                        crate::lib::intvector_intrinsics::vec256_rotate_right64(
                                            e0,
                                            41u32
                                        )
                                    )
                                )
                            ),
                            crate::lib::intvector_intrinsics::vec256_xor(
                                crate::lib::intvector_intrinsics::vec256_and(e0, f0),
                                crate::lib::intvector_intrinsics::vec256_and(
                                    crate::lib::intvector_intrinsics::vec256_lognot(e0),
                                    g0
                                )
                            )
                        ),
                        k_e_t
                    ),
                    ws_t
                );
            let t2: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right64(a0, 28u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(a0, 34u32),
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(a0, 39u32)
                        )
                    ),
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_and(a0, b00),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_and(a0, c0),
                            crate::lib::intvector_intrinsics::vec256_and(b00, c0)
                        )
                    )
                );
            let a1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(t1, t2);
            let b10: crate::lib::intvector_intrinsics::vec256 = a0;
            let c1: crate::lib::intvector_intrinsics::vec256 = b00;
            let d1: crate::lib::intvector_intrinsics::vec256 = c0;
            let e1: crate::lib::intvector_intrinsics::vec256 =
                crate::lib::intvector_intrinsics::vec256_add64(d0, t1);
            let f1: crate::lib::intvector_intrinsics::vec256 = e0;
            let g1: crate::lib::intvector_intrinsics::vec256 = f0;
            let h12: crate::lib::intvector_intrinsics::vec256 = g0;
            hash[0usize] = a1;
            hash[1usize] = b10;
            hash[2usize] = c1;
            hash[3usize] = d1;
            hash[4usize] = e1;
            hash[5usize] = f1;
            hash[6usize] = g1;
            hash[7usize] = h12
        };
        if i < 4u32
        {
            for i0 in 0u32..16u32
            {
                let t16: crate::lib::intvector_intrinsics::vec256 = (&mut ws)[i0 as usize];
                let t15: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                let t7: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                let t2: crate::lib::intvector_intrinsics::vec256 =
                    (&mut ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                let s1: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right64(t2, 19u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(t2, 61u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right64(t2, 6u32)
                        )
                    );
                let s0: crate::lib::intvector_intrinsics::vec256 =
                    crate::lib::intvector_intrinsics::vec256_xor(
                        crate::lib::intvector_intrinsics::vec256_rotate_right64(t15, 1u32),
                        crate::lib::intvector_intrinsics::vec256_xor(
                            crate::lib::intvector_intrinsics::vec256_rotate_right64(t15, 8u32),
                            crate::lib::intvector_intrinsics::vec256_shift_right64(t15, 7u32)
                        )
                    );
                (&mut ws)[i0 as usize] =
                    crate::lib::intvector_intrinsics::vec256_add64(
                        crate::lib::intvector_intrinsics::vec256_add64(
                            crate::lib::intvector_intrinsics::vec256_add64(s1, t7),
                            s0
                        ),
                        t16
                    )
            }
        }
    };
    for i in 0u32..8u32
    {
        let x: crate::lib::intvector_intrinsics::vec256 =
            crate::lib::intvector_intrinsics::vec256_add64(
                hash[i as usize],
                (&mut hash_old)[i as usize]
            );
        let
        os:
        (&mut [crate::lib::intvector_intrinsics::vec256],
        &mut [crate::lib::intvector_intrinsics::vec256])
        =
            hash.split_at_mut(0usize);
        os.1[i as usize] = x
    }
}

#[inline] fn sha512_finish4(
    st: &mut [crate::lib::intvector_intrinsics::vec256],
    h: crate::hacl::sha2_types::uint8_4p
) ->
    ()
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: crate::lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: crate::lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: crate::lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: crate::lib::intvector_intrinsics::vec256 = st[3usize];
    let v0·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let st0·: crate::lib::intvector_intrinsics::vec256 = v0··;
    let st1·: crate::lib::intvector_intrinsics::vec256 = v2··;
    let st2·: crate::lib::intvector_intrinsics::vec256 = v1··;
    let st3·: crate::lib::intvector_intrinsics::vec256 = v3··;
    let v00: crate::lib::intvector_intrinsics::vec256 = st[4usize];
    let v10: crate::lib::intvector_intrinsics::vec256 = st[5usize];
    let v20: crate::lib::intvector_intrinsics::vec256 = st[6usize];
    let v30: crate::lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: crate::lib::intvector_intrinsics::vec256 =
        crate::lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let st4·: crate::lib::intvector_intrinsics::vec256 = v0··0;
    let st5·: crate::lib::intvector_intrinsics::vec256 = v2··0;
    let st6·: crate::lib::intvector_intrinsics::vec256 = v1··0;
    let st7·: crate::lib::intvector_intrinsics::vec256 = v3··0;
    st[0usize] = st0·;
    st[1usize] = st4·;
    st[2usize] = st1·;
    st[3usize] = st5·;
    st[4usize] = st2·;
    st[5usize] = st6·;
    st[6usize] = st3·;
    st[7usize] = st7·;
    for i in 0u32..8u32
    {
        crate::lib::intvector_intrinsics::vec256_store64_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    };
    let b3: &mut [u8] = h.snd.snd.snd;
    let b2: &mut [u8] = h.snd.snd.fst;
    let b1: &mut [u8] = h.snd.fst;
    let b0: &mut [u8] = h.fst;
    (b0[0usize..64usize]).copy_from_slice(&(&mut (&mut hbuf)[0usize..])[0usize..64usize]);
    (b1[0usize..64usize]).copy_from_slice(&(&mut (&mut hbuf)[64usize..])[0usize..64usize]);
    (b2[0usize..64usize]).copy_from_slice(&(&mut (&mut hbuf)[128usize..])[0usize..64usize]);
    (b3[0usize..64usize]).copy_from_slice(&(&mut (&mut hbuf)[192usize..])[0usize..64usize])
}
