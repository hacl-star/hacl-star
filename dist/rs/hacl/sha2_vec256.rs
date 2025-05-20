#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline] fn sha224_init8(hash: &mut [lib::intvector_intrinsics::vec256])
{
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let hi: u32 = (&crate::hash_sha2::h224)[i as usize];
            let x: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load32(hi);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha224_update8(
    b: crate::sha2_types::uint8_8p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let mut hash_old: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [lib::intvector_intrinsics::vec256; 16] =
        [lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    match b
    {
        crate::sha2_types::uint8_8p
        {
            fst: ref b0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: ref b1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: ref b2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: ref b3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: ref b4,
                            snd:
                            crate::sha2_types::uint8_3p
                            {
                                fst: ref b5,
                                snd: crate::sha2_types::uint8_2p { fst: ref b6, snd: ref b7 }
                            }
                        }
                    }
                }
            }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b0)[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b1)[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b2)[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b3)[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b4)[0usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b5)[0usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b6)[0usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b7)[0usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b0)[32usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b1)[32usize..]);
              (&mut ws)[10usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b2)[32usize..]);
              (&mut ws)[11usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b3)[32usize..]);
              (&mut ws)[12usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b4)[32usize..]);
              (&mut ws)[13usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b5)[32usize..]);
              (&mut ws)[14usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b6)[32usize..]);
              (&mut ws)[15usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b7)[32usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v4: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v5: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v6: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v7: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: lib::intvector_intrinsics::vec256 = v7·20;
    let ws0: lib::intvector_intrinsics::vec256 = v0·3;
    let ws1: lib::intvector_intrinsics::vec256 = v2·3;
    let ws2: lib::intvector_intrinsics::vec256 = v1·3;
    let ws3: lib::intvector_intrinsics::vec256 = v3·3;
    let ws4: lib::intvector_intrinsics::vec256 = v4·3;
    let ws5: lib::intvector_intrinsics::vec256 = v6·3;
    let ws6: lib::intvector_intrinsics::vec256 = v5·3;
    let ws7: lib::intvector_intrinsics::vec256 = v7·3;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v40: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v50: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v60: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v70: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v00, v10);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v00, v10);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v20, v30);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v20, v30);
    let v4·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v40, v50);
    let v5·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v40, v50);
    let v6·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v60, v70);
    let v7·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v60, v70);
    let v0·5: lib::intvector_intrinsics::vec256 = v0·4;
    let v1·5: lib::intvector_intrinsics::vec256 = v1·4;
    let v2·5: lib::intvector_intrinsics::vec256 = v2·4;
    let v3·5: lib::intvector_intrinsics::vec256 = v3·4;
    let v4·5: lib::intvector_intrinsics::vec256 = v4·4;
    let v5·5: lib::intvector_intrinsics::vec256 = v5·4;
    let v6·5: lib::intvector_intrinsics::vec256 = v6·4;
    let v7·5: lib::intvector_intrinsics::vec256 = v7·4;
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0·5, v2·5);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0·5, v2·5);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v1·5, v3·5);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v1·5, v3·5);
    let v4·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v4·5, v6·5);
    let v6·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v4·5, v6·5);
    let v5·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v5·5, v7·5);
    let v7·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v5·5, v7·5);
    let v0·12: lib::intvector_intrinsics::vec256 = v0·11;
    let v1·12: lib::intvector_intrinsics::vec256 = v1·11;
    let v2·12: lib::intvector_intrinsics::vec256 = v2·11;
    let v3·12: lib::intvector_intrinsics::vec256 = v3·11;
    let v4·12: lib::intvector_intrinsics::vec256 = v4·11;
    let v5·12: lib::intvector_intrinsics::vec256 = v5·11;
    let v6·12: lib::intvector_intrinsics::vec256 = v6·11;
    let v7·12: lib::intvector_intrinsics::vec256 = v7·11;
    let v0·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v4·12);
    let v4·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v4·12);
    let v1·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v5·12);
    let v5·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v5·12);
    let v2·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v2·12, v6·12);
    let v6·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v2·12, v6·12);
    let v3·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v3·12, v7·12);
    let v7·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v3·12, v7·12);
    let v0·22: lib::intvector_intrinsics::vec256 = v0·21;
    let v1·22: lib::intvector_intrinsics::vec256 = v1·21;
    let v2·22: lib::intvector_intrinsics::vec256 = v2·21;
    let v3·22: lib::intvector_intrinsics::vec256 = v3·21;
    let v4·22: lib::intvector_intrinsics::vec256 = v4·21;
    let v5·22: lib::intvector_intrinsics::vec256 = v5·21;
    let v6·22: lib::intvector_intrinsics::vec256 = v6·21;
    let v7·22: lib::intvector_intrinsics::vec256 = v7·21;
    let v0·6: lib::intvector_intrinsics::vec256 = v0·22;
    let v1·6: lib::intvector_intrinsics::vec256 = v1·22;
    let v2·6: lib::intvector_intrinsics::vec256 = v2·22;
    let v3·6: lib::intvector_intrinsics::vec256 = v3·22;
    let v4·6: lib::intvector_intrinsics::vec256 = v4·22;
    let v5·6: lib::intvector_intrinsics::vec256 = v5·22;
    let v6·6: lib::intvector_intrinsics::vec256 = v6·22;
    let v7·6: lib::intvector_intrinsics::vec256 = v7·22;
    let ws8: lib::intvector_intrinsics::vec256 = v0·6;
    let ws9: lib::intvector_intrinsics::vec256 = v2·6;
    let ws10: lib::intvector_intrinsics::vec256 = v1·6;
    let ws11: lib::intvector_intrinsics::vec256 = v3·6;
    let ws12: lib::intvector_intrinsics::vec256 = v4·6;
    let ws13: lib::intvector_intrinsics::vec256 = v6·6;
    let ws14: lib::intvector_intrinsics::vec256 = v5·6;
    let ws15: lib::intvector_intrinsics::vec256 = v7·6;
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
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            krml::unroll_for!(
                16,
                "i0",
                0u32,
                1u32,
                {
                    let k_t: u32 =
                        (&crate::hash_sha2::k224_256)[16u32.wrapping_mul(i).wrapping_add(i0)
                        as
                        usize];
                    let ws_t: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                    let a0: lib::intvector_intrinsics::vec256 = hash[0usize];
                    let b0: lib::intvector_intrinsics::vec256 = hash[1usize];
                    let c0: lib::intvector_intrinsics::vec256 = hash[2usize];
                    let d0: lib::intvector_intrinsics::vec256 = hash[3usize];
                    let e0: lib::intvector_intrinsics::vec256 = hash[4usize];
                    let f0: lib::intvector_intrinsics::vec256 = hash[5usize];
                    let g0: lib::intvector_intrinsics::vec256 = hash[6usize];
                    let h02: lib::intvector_intrinsics::vec256 = hash[7usize];
                    let k_e_t: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_load32(k_t);
                    let t1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(
                            lib::intvector_intrinsics::vec256_add32(
                                lib::intvector_intrinsics::vec256_add32(
                                    lib::intvector_intrinsics::vec256_add32(
                                        h02,
                                        lib::intvector_intrinsics::vec256_xor(
                                            lib::intvector_intrinsics::vec256_rotate_right32(
                                                e0,
                                                6u32
                                            ),
                                            lib::intvector_intrinsics::vec256_xor(
                                                lib::intvector_intrinsics::vec256_rotate_right32(
                                                    e0,
                                                    11u32
                                                ),
                                                lib::intvector_intrinsics::vec256_rotate_right32(
                                                    e0,
                                                    25u32
                                                )
                                            )
                                        )
                                    ),
                                    lib::intvector_intrinsics::vec256_xor(
                                        lib::intvector_intrinsics::vec256_and(e0, f0),
                                        lib::intvector_intrinsics::vec256_and(
                                            lib::intvector_intrinsics::vec256_lognot(e0),
                                            g0
                                        )
                                    )
                                ),
                                k_e_t
                            ),
                            ws_t
                        );
                    let t2: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right32(a0, 2u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right32(a0, 13u32),
                                    lib::intvector_intrinsics::vec256_rotate_right32(a0, 22u32)
                                )
                            ),
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_and(a0, b0),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_and(a0, c0),
                                    lib::intvector_intrinsics::vec256_and(b0, c0)
                                )
                            )
                        );
                    let a1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(t1, t2);
                    let b1: lib::intvector_intrinsics::vec256 = a0;
                    let c1: lib::intvector_intrinsics::vec256 = b0;
                    let d1: lib::intvector_intrinsics::vec256 = c0;
                    let e1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(d0, t1);
                    let f1: lib::intvector_intrinsics::vec256 = e0;
                    let g1: lib::intvector_intrinsics::vec256 = f0;
                    let h12: lib::intvector_intrinsics::vec256 = g0;
                    hash[0usize] = a1;
                    hash[1usize] = b1;
                    hash[2usize] = c1;
                    hash[3usize] = d1;
                    hash[4usize] = e1;
                    hash[5usize] = f1;
                    hash[6usize] = g1;
                    hash[7usize] = h12
                }
            );
            if i < 3u32
            {
                krml::unroll_for!(
                    16,
                    "i0",
                    0u32,
                    1u32,
                    {
                        let t16: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                        let t15: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                        let t7: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                        let t2: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                        let s1: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right32(t2, 17u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right32(t2, 19u32),
                                    lib::intvector_intrinsics::vec256_shift_right32(t2, 10u32)
                                )
                            );
                        let s0: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right32(t15, 7u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right32(t15, 18u32),
                                    lib::intvector_intrinsics::vec256_shift_right32(t15, 3u32)
                                )
                            );
                        (&mut ws)[i0 as usize] =
                            lib::intvector_intrinsics::vec256_add32(
                                lib::intvector_intrinsics::vec256_add32(
                                    lib::intvector_intrinsics::vec256_add32(s1, t7),
                                    s0
                                ),
                                t16
                            )
                    }
                )
            }
        }
    );
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add32(hash[i as usize], (&hash_old)[i as usize]);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha224_update_nblocks8(
    len: u32,
    mut b: crate::sha2_types::uint8_8p,
    st: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 = len.wrapping_div(64u32);
    for i in 0u32..blocks
    {
        let mb: crate::sha2_types::uint8_8p =
            match b
            {
                crate::sha2_types::uint8_8p
                {
                    fst: ref mut b0,
                    snd:
                    crate::sha2_types::uint8_7p
                    {
                        fst: ref mut b1,
                        snd:
                        crate::sha2_types::uint8_6p
                        {
                            fst: ref mut b2,
                            snd:
                            crate::sha2_types::uint8_5p
                            {
                                fst: ref mut b3,
                                snd:
                                crate::sha2_types::uint8_4p
                                {
                                    fst: ref mut b4,
                                    snd:
                                    crate::sha2_types::uint8_3p
                                    {
                                        fst: ref mut b5,
                                        snd:
                                        crate::sha2_types::uint8_2p
                                        { fst: ref mut b6, snd: ref mut b7 }
                                    }
                                }
                            }
                        }
                    }
                }
                =>
                  {
                      let bl0: (&mut [u8], &mut [u8]) =
                          b0.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl1: (&mut [u8], &mut [u8]) =
                          b1.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl2: (&mut [u8], &mut [u8]) =
                          b2.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl3: (&mut [u8], &mut [u8]) =
                          b3.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl4: (&mut [u8], &mut [u8]) =
                          b4.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl5: (&mut [u8], &mut [u8]) =
                          b5.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl6: (&mut [u8], &mut [u8]) =
                          b6.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl7: (&mut [u8], &mut [u8]) =
                          b7.split_at_mut(i.wrapping_mul(64u32) as usize);
                      crate::sha2_types::uint8_8p
                      {
                          fst: bl0.1,
                          snd:
                          crate::sha2_types::uint8_7p
                          {
                              fst: bl1.1,
                              snd:
                              crate::sha2_types::uint8_6p
                              {
                                  fst: bl2.1,
                                  snd:
                                  crate::sha2_types::uint8_5p
                                  {
                                      fst: bl3.1,
                                      snd:
                                      crate::sha2_types::uint8_4p
                                      {
                                          fst: bl4.1,
                                          snd:
                                          crate::sha2_types::uint8_3p
                                          {
                                              fst: bl5.1,
                                              snd:
                                              crate::sha2_types::uint8_2p { fst: bl6.1, snd: bl7.1 }
                                          }
                                      }
                                  }
                              }
                          }
                      }
                  }
            };
        crate::sha2_vec256::sha224_update8(mb, st)
    }
}

#[inline] fn sha224_update_last8(
    totlen: u64,
    len: u32,
    b: crate::sha2_types::uint8_8p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 = if len.wrapping_add(8u32).wrapping_add(1u32) <= 64u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(64u32);
    let mut last: [u8; 1024] = [0u8; 1024usize];
    let mut totlen_buf: [u8; 8] = [0u8; 8usize];
    let total_len_bits: u64 = totlen.wrapping_shl(3u32);
    lowstar::endianness::store64_be(&mut totlen_buf, total_len_bits);
    let scrut: crate::sha2_types::uint8_2x8p =
        match b
        {
            crate::sha2_types::uint8_8p
            {
                fst: ref b0,
                snd:
                crate::sha2_types::uint8_7p
                {
                    fst: ref b1,
                    snd:
                    crate::sha2_types::uint8_6p
                    {
                        fst: ref b2,
                        snd:
                        crate::sha2_types::uint8_5p
                        {
                            fst: ref b3,
                            snd:
                            crate::sha2_types::uint8_4p
                            {
                                fst: ref b4,
                                snd:
                                crate::sha2_types::uint8_3p
                                {
                                    fst: ref b5,
                                    snd: crate::sha2_types::uint8_2p { fst: ref b6, snd: ref b7 }
                                }
                            }
                        }
                    }
                }
            }
            =>
              {
                  let last0: (&mut [u8], &mut [u8]) = last.split_at_mut(0usize);
                  let last1: (&mut [u8], &mut [u8]) = (last0.1).split_at_mut(128usize);
                  let last2: (&mut [u8], &mut [u8]) = (last1.1).split_at_mut(128usize);
                  let last3: (&mut [u8], &mut [u8]) = (last2.1).split_at_mut(128usize);
                  let last4: (&mut [u8], &mut [u8]) = (last3.1).split_at_mut(128usize);
                  let last5: (&mut [u8], &mut [u8]) = (last4.1).split_at_mut(128usize);
                  let last6: (&mut [u8], &mut [u8]) = (last5.1).split_at_mut(128usize);
                  let last7: (&mut [u8], &mut [u8]) = (last6.1).split_at_mut(128usize);
                  (last1.0[0usize..len as usize]).copy_from_slice(&(*b0)[0usize..len as usize]);
                  last1.0[len as usize] = 0x80u8;
                  (last1.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last01: (&mut [u8], &mut [u8]) = (last1.0).split_at_mut(0usize);
                  let last11: (&mut [u8], &mut [u8]) = (last01.1).split_at_mut(64usize);
                  let l00: &mut [u8] = last11.0;
                  let l01: &mut [u8] = last11.1;
                  (last2.0[0usize..len as usize]).copy_from_slice(&(*b1)[0usize..len as usize]);
                  last2.0[len as usize] = 0x80u8;
                  (last2.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last010: (&mut [u8], &mut [u8]) = (last2.0).split_at_mut(0usize);
                  let last110: (&mut [u8], &mut [u8]) = (last010.1).split_at_mut(64usize);
                  let l10: &mut [u8] = last110.0;
                  let l11: &mut [u8] = last110.1;
                  (last3.0[0usize..len as usize]).copy_from_slice(&(*b2)[0usize..len as usize]);
                  last3.0[len as usize] = 0x80u8;
                  (last3.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last011: (&mut [u8], &mut [u8]) = (last3.0).split_at_mut(0usize);
                  let last111: (&mut [u8], &mut [u8]) = (last011.1).split_at_mut(64usize);
                  let l20: &mut [u8] = last111.0;
                  let l21: &mut [u8] = last111.1;
                  (last4.0[0usize..len as usize]).copy_from_slice(&(*b3)[0usize..len as usize]);
                  last4.0[len as usize] = 0x80u8;
                  (last4.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last012: (&mut [u8], &mut [u8]) = (last4.0).split_at_mut(0usize);
                  let last112: (&mut [u8], &mut [u8]) = (last012.1).split_at_mut(64usize);
                  let l30: &mut [u8] = last112.0;
                  let l31: &mut [u8] = last112.1;
                  (last5.0[0usize..len as usize]).copy_from_slice(&(*b4)[0usize..len as usize]);
                  last5.0[len as usize] = 0x80u8;
                  (last5.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last013: (&mut [u8], &mut [u8]) = (last5.0).split_at_mut(0usize);
                  let last113: (&mut [u8], &mut [u8]) = (last013.1).split_at_mut(64usize);
                  let l40: &mut [u8] = last113.0;
                  let l41: &mut [u8] = last113.1;
                  (last6.0[0usize..len as usize]).copy_from_slice(&(*b5)[0usize..len as usize]);
                  last6.0[len as usize] = 0x80u8;
                  (last6.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last014: (&mut [u8], &mut [u8]) = (last6.0).split_at_mut(0usize);
                  let last114: (&mut [u8], &mut [u8]) = (last014.1).split_at_mut(64usize);
                  let l50: &mut [u8] = last114.0;
                  let l51: &mut [u8] = last114.1;
                  (last7.0[0usize..len as usize]).copy_from_slice(&(*b6)[0usize..len as usize]);
                  last7.0[len as usize] = 0x80u8;
                  (last7.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last015: (&mut [u8], &mut [u8]) = (last7.0).split_at_mut(0usize);
                  let last115: (&mut [u8], &mut [u8]) = (last015.1).split_at_mut(64usize);
                  let l60: &mut [u8] = last115.0;
                  let l61: &mut [u8] = last115.1;
                  (last7.1[0usize..len as usize]).copy_from_slice(&(*b7)[0usize..len as usize]);
                  last7.1[len as usize] = 0x80u8;
                  (last7.1[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last016: (&mut [u8], &mut [u8]) = (last7.1).split_at_mut(0usize);
                  let last116: (&mut [u8], &mut [u8]) = (last016.1).split_at_mut(64usize);
                  let l70: &mut [u8] = last116.0;
                  let l71: &mut [u8] = last116.1;
                  let mb0: crate::sha2_types::uint8_8p =
                      crate::sha2_types::uint8_8p
                      {
                          fst: l00,
                          snd:
                          crate::sha2_types::uint8_7p
                          {
                              fst: l10,
                              snd:
                              crate::sha2_types::uint8_6p
                              {
                                  fst: l20,
                                  snd:
                                  crate::sha2_types::uint8_5p
                                  {
                                      fst: l30,
                                      snd:
                                      crate::sha2_types::uint8_4p
                                      {
                                          fst: l40,
                                          snd:
                                          crate::sha2_types::uint8_3p
                                          {
                                              fst: l50,
                                              snd:
                                              crate::sha2_types::uint8_2p { fst: l60, snd: l70 }
                                          }
                                      }
                                  }
                              }
                          }
                      };
                  let mb1: crate::sha2_types::uint8_8p =
                      crate::sha2_types::uint8_8p
                      {
                          fst: l01,
                          snd:
                          crate::sha2_types::uint8_7p
                          {
                              fst: l11,
                              snd:
                              crate::sha2_types::uint8_6p
                              {
                                  fst: l21,
                                  snd:
                                  crate::sha2_types::uint8_5p
                                  {
                                      fst: l31,
                                      snd:
                                      crate::sha2_types::uint8_4p
                                      {
                                          fst: l41,
                                          snd:
                                          crate::sha2_types::uint8_3p
                                          {
                                              fst: l51,
                                              snd:
                                              crate::sha2_types::uint8_2p { fst: l61, snd: l71 }
                                          }
                                      }
                                  }
                              }
                          }
                      };
                  crate::sha2_types::uint8_2x8p { fst: mb0, snd: mb1 }
              }
        };
    let last0: crate::sha2_types::uint8_8p = scrut.fst;
    let last1: crate::sha2_types::uint8_8p = scrut.snd;
    crate::sha2_vec256::sha224_update8(last0, hash);
    if blocks > 1u32 { crate::sha2_vec256::sha224_update8(last1, hash) }
}

#[inline] fn sha224_finish8(
    st: &mut [lib::intvector_intrinsics::vec256],
    mut h: crate::sha2_types::uint8_8p
)
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: lib::intvector_intrinsics::vec256 = st[3usize];
    let v4: lib::intvector_intrinsics::vec256 = st[4usize];
    let v5: lib::intvector_intrinsics::vec256 = st[5usize];
    let v6: lib::intvector_intrinsics::vec256 = st[6usize];
    let v7: lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: lib::intvector_intrinsics::vec256 = v7·20;
    let st0·: lib::intvector_intrinsics::vec256 = v0·3;
    let st1·: lib::intvector_intrinsics::vec256 = v2·3;
    let st2·: lib::intvector_intrinsics::vec256 = v1·3;
    let st3·: lib::intvector_intrinsics::vec256 = v3·3;
    let st4·: lib::intvector_intrinsics::vec256 = v4·3;
    let st5·: lib::intvector_intrinsics::vec256 = v6·3;
    let st6·: lib::intvector_intrinsics::vec256 = v5·3;
    let st7·: lib::intvector_intrinsics::vec256 = v7·3;
    st[0usize] = st0·;
    st[1usize] = st1·;
    st[2usize] = st2·;
    st[3usize] = st3·;
    st[4usize] = st4·;
    st[5usize] = st5·;
    st[6usize] = st6·;
    st[7usize] = st7·;
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    );
    match h
    {
        crate::sha2_types::uint8_8p
        {
            fst: ref mut b0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: ref mut b1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: ref mut b2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: ref mut b3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: ref mut b4,
                            snd:
                            crate::sha2_types::uint8_3p
                            {
                                fst: ref mut b5,
                                snd:
                                crate::sha2_types::uint8_2p { fst: ref mut b6, snd: ref mut b7 }
                            }
                        }
                    }
                }
            }
        }
        =>
          {
              ((*b0)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..28usize]);
              ((*b1)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[32usize..])[0usize..28usize]);
              ((*b2)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[64usize..])[0usize..28usize]);
              ((*b3)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[96usize..])[0usize..28usize]);
              ((*b4)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[128usize..])[0usize..28usize]);
              ((*b5)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[160usize..])[0usize..28usize]);
              ((*b6)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[192usize..])[0usize..28usize]);
              ((*b7)[0usize..28usize]).copy_from_slice(&(&(&hbuf)[224usize..])[0usize..28usize])
          }
    }
}

pub fn sha224_8(
    dst0: &mut [u8],
    dst1: &mut [u8],
    dst2: &mut [u8],
    dst3: &mut [u8],
    dst4: &mut [u8],
    dst5: &mut [u8],
    dst6: &mut [u8],
    dst7: &mut [u8],
    input_len: u32,
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    input4: &mut [u8],
    input5: &mut [u8],
    input6: &mut [u8],
    input7: &mut [u8]
)
{
    let mut ib: crate::sha2_types::uint8_8p =
        crate::sha2_types::uint8_8p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: input1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: input2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: input3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: input4,
                            snd:
                            crate::sha2_types::uint8_3p
                            {
                                fst: input5,
                                snd: crate::sha2_types::uint8_2p { fst: input6, snd: input7 }
                            }
                        }
                    }
                }
            }
        };
    let rb: crate::sha2_types::uint8_8p =
        crate::sha2_types::uint8_8p
        {
            fst: dst0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: dst1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: dst2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: dst3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: dst4,
                            snd:
                            crate::sha2_types::uint8_3p
                            { fst: dst5, snd: crate::sha2_types::uint8_2p { fst: dst6, snd: dst7 } }
                        }
                    }
                }
            }
        };
    let mut st: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    crate::sha2_vec256::sha224_init8(&mut st);
    let rem: u32 = input_len.wrapping_rem(64u32);
    let len·: u64 = input_len as u64;
    crate::sha2_vec256::sha224_update_nblocks8(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(64u32);
    let lb: crate::sha2_types::uint8_8p =
        match ib
        {
            crate::sha2_types::uint8_8p
            {
                fst: ref mut b0,
                snd:
                crate::sha2_types::uint8_7p
                {
                    fst: ref mut b1,
                    snd:
                    crate::sha2_types::uint8_6p
                    {
                        fst: ref mut b2,
                        snd:
                        crate::sha2_types::uint8_5p
                        {
                            fst: ref mut b3,
                            snd:
                            crate::sha2_types::uint8_4p
                            {
                                fst: ref mut b4,
                                snd:
                                crate::sha2_types::uint8_3p
                                {
                                    fst: ref mut b5,
                                    snd:
                                    crate::sha2_types::uint8_2p { fst: ref mut b6, snd: ref mut b7 }
                                }
                            }
                        }
                    }
                }
            }
            =>
              {
                  let bl0: (&mut [u8], &mut [u8]) =
                      b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl1: (&mut [u8], &mut [u8]) =
                      b1.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl2: (&mut [u8], &mut [u8]) =
                      b2.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl3: (&mut [u8], &mut [u8]) =
                      b3.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl4: (&mut [u8], &mut [u8]) =
                      b4.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl5: (&mut [u8], &mut [u8]) =
                      b5.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl6: (&mut [u8], &mut [u8]) =
                      b6.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl7: (&mut [u8], &mut [u8]) =
                      b7.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  crate::sha2_types::uint8_8p
                  {
                      fst: bl0.1,
                      snd:
                      crate::sha2_types::uint8_7p
                      {
                          fst: bl1.1,
                          snd:
                          crate::sha2_types::uint8_6p
                          {
                              fst: bl2.1,
                              snd:
                              crate::sha2_types::uint8_5p
                              {
                                  fst: bl3.1,
                                  snd:
                                  crate::sha2_types::uint8_4p
                                  {
                                      fst: bl4.1,
                                      snd:
                                      crate::sha2_types::uint8_3p
                                      {
                                          fst: bl5.1,
                                          snd:
                                          crate::sha2_types::uint8_2p { fst: bl6.1, snd: bl7.1 }
                                      }
                                  }
                              }
                          }
                      }
                  }
              }
        };
    crate::sha2_vec256::sha224_update_last8(len·, rem, lb, &mut st);
    crate::sha2_vec256::sha224_finish8(&mut st, rb)
}

#[inline] fn sha256_init8(hash: &mut [lib::intvector_intrinsics::vec256])
{
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let hi: u32 = (&crate::hash_sha2::h256)[i as usize];
            let x: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load32(hi);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha256_update8(
    b: crate::sha2_types::uint8_8p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let mut hash_old: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [lib::intvector_intrinsics::vec256; 16] =
        [lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    match b
    {
        crate::sha2_types::uint8_8p
        {
            fst: ref b0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: ref b1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: ref b2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: ref b3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: ref b4,
                            snd:
                            crate::sha2_types::uint8_3p
                            {
                                fst: ref b5,
                                snd: crate::sha2_types::uint8_2p { fst: ref b6, snd: ref b7 }
                            }
                        }
                    }
                }
            }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b0)[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b1)[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b2)[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b3)[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b4)[0usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b5)[0usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b6)[0usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b7)[0usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b0)[32usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b1)[32usize..]);
              (&mut ws)[10usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b2)[32usize..]);
              (&mut ws)[11usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b3)[32usize..]);
              (&mut ws)[12usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b4)[32usize..]);
              (&mut ws)[13usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b5)[32usize..]);
              (&mut ws)[14usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b6)[32usize..]);
              (&mut ws)[15usize] = lib::intvector_intrinsics::vec256_load32_be(&(*b7)[32usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v4: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v5: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v6: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v7: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: lib::intvector_intrinsics::vec256 = v7·20;
    let ws0: lib::intvector_intrinsics::vec256 = v0·3;
    let ws1: lib::intvector_intrinsics::vec256 = v2·3;
    let ws2: lib::intvector_intrinsics::vec256 = v1·3;
    let ws3: lib::intvector_intrinsics::vec256 = v3·3;
    let ws4: lib::intvector_intrinsics::vec256 = v4·3;
    let ws5: lib::intvector_intrinsics::vec256 = v6·3;
    let ws6: lib::intvector_intrinsics::vec256 = v5·3;
    let ws7: lib::intvector_intrinsics::vec256 = v7·3;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v40: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v50: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v60: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v70: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v00, v10);
    let v1·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v00, v10);
    let v2·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v20, v30);
    let v3·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v20, v30);
    let v4·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v40, v50);
    let v5·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v40, v50);
    let v6·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v60, v70);
    let v7·4: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v60, v70);
    let v0·5: lib::intvector_intrinsics::vec256 = v0·4;
    let v1·5: lib::intvector_intrinsics::vec256 = v1·4;
    let v2·5: lib::intvector_intrinsics::vec256 = v2·4;
    let v3·5: lib::intvector_intrinsics::vec256 = v3·4;
    let v4·5: lib::intvector_intrinsics::vec256 = v4·4;
    let v5·5: lib::intvector_intrinsics::vec256 = v5·4;
    let v6·5: lib::intvector_intrinsics::vec256 = v6·4;
    let v7·5: lib::intvector_intrinsics::vec256 = v7·4;
    let v0·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0·5, v2·5);
    let v2·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0·5, v2·5);
    let v1·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v1·5, v3·5);
    let v3·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v1·5, v3·5);
    let v4·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v4·5, v6·5);
    let v6·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v4·5, v6·5);
    let v5·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v5·5, v7·5);
    let v7·11: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v5·5, v7·5);
    let v0·12: lib::intvector_intrinsics::vec256 = v0·11;
    let v1·12: lib::intvector_intrinsics::vec256 = v1·11;
    let v2·12: lib::intvector_intrinsics::vec256 = v2·11;
    let v3·12: lib::intvector_intrinsics::vec256 = v3·11;
    let v4·12: lib::intvector_intrinsics::vec256 = v4·11;
    let v5·12: lib::intvector_intrinsics::vec256 = v5·11;
    let v6·12: lib::intvector_intrinsics::vec256 = v6·11;
    let v7·12: lib::intvector_intrinsics::vec256 = v7·11;
    let v0·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·12, v4·12);
    let v4·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·12, v4·12);
    let v1·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·12, v5·12);
    let v5·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·12, v5·12);
    let v2·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v2·12, v6·12);
    let v6·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v2·12, v6·12);
    let v3·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v3·12, v7·12);
    let v7·21: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v3·12, v7·12);
    let v0·22: lib::intvector_intrinsics::vec256 = v0·21;
    let v1·22: lib::intvector_intrinsics::vec256 = v1·21;
    let v2·22: lib::intvector_intrinsics::vec256 = v2·21;
    let v3·22: lib::intvector_intrinsics::vec256 = v3·21;
    let v4·22: lib::intvector_intrinsics::vec256 = v4·21;
    let v5·22: lib::intvector_intrinsics::vec256 = v5·21;
    let v6·22: lib::intvector_intrinsics::vec256 = v6·21;
    let v7·22: lib::intvector_intrinsics::vec256 = v7·21;
    let v0·6: lib::intvector_intrinsics::vec256 = v0·22;
    let v1·6: lib::intvector_intrinsics::vec256 = v1·22;
    let v2·6: lib::intvector_intrinsics::vec256 = v2·22;
    let v3·6: lib::intvector_intrinsics::vec256 = v3·22;
    let v4·6: lib::intvector_intrinsics::vec256 = v4·22;
    let v5·6: lib::intvector_intrinsics::vec256 = v5·22;
    let v6·6: lib::intvector_intrinsics::vec256 = v6·22;
    let v7·6: lib::intvector_intrinsics::vec256 = v7·22;
    let ws8: lib::intvector_intrinsics::vec256 = v0·6;
    let ws9: lib::intvector_intrinsics::vec256 = v2·6;
    let ws10: lib::intvector_intrinsics::vec256 = v1·6;
    let ws11: lib::intvector_intrinsics::vec256 = v3·6;
    let ws12: lib::intvector_intrinsics::vec256 = v4·6;
    let ws13: lib::intvector_intrinsics::vec256 = v6·6;
    let ws14: lib::intvector_intrinsics::vec256 = v5·6;
    let ws15: lib::intvector_intrinsics::vec256 = v7·6;
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
    krml::unroll_for!(
        4,
        "i",
        0u32,
        1u32,
        {
            krml::unroll_for!(
                16,
                "i0",
                0u32,
                1u32,
                {
                    let k_t: u32 =
                        (&crate::hash_sha2::k224_256)[16u32.wrapping_mul(i).wrapping_add(i0)
                        as
                        usize];
                    let ws_t: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                    let a0: lib::intvector_intrinsics::vec256 = hash[0usize];
                    let b0: lib::intvector_intrinsics::vec256 = hash[1usize];
                    let c0: lib::intvector_intrinsics::vec256 = hash[2usize];
                    let d0: lib::intvector_intrinsics::vec256 = hash[3usize];
                    let e0: lib::intvector_intrinsics::vec256 = hash[4usize];
                    let f0: lib::intvector_intrinsics::vec256 = hash[5usize];
                    let g0: lib::intvector_intrinsics::vec256 = hash[6usize];
                    let h02: lib::intvector_intrinsics::vec256 = hash[7usize];
                    let k_e_t: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_load32(k_t);
                    let t1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(
                            lib::intvector_intrinsics::vec256_add32(
                                lib::intvector_intrinsics::vec256_add32(
                                    lib::intvector_intrinsics::vec256_add32(
                                        h02,
                                        lib::intvector_intrinsics::vec256_xor(
                                            lib::intvector_intrinsics::vec256_rotate_right32(
                                                e0,
                                                6u32
                                            ),
                                            lib::intvector_intrinsics::vec256_xor(
                                                lib::intvector_intrinsics::vec256_rotate_right32(
                                                    e0,
                                                    11u32
                                                ),
                                                lib::intvector_intrinsics::vec256_rotate_right32(
                                                    e0,
                                                    25u32
                                                )
                                            )
                                        )
                                    ),
                                    lib::intvector_intrinsics::vec256_xor(
                                        lib::intvector_intrinsics::vec256_and(e0, f0),
                                        lib::intvector_intrinsics::vec256_and(
                                            lib::intvector_intrinsics::vec256_lognot(e0),
                                            g0
                                        )
                                    )
                                ),
                                k_e_t
                            ),
                            ws_t
                        );
                    let t2: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right32(a0, 2u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right32(a0, 13u32),
                                    lib::intvector_intrinsics::vec256_rotate_right32(a0, 22u32)
                                )
                            ),
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_and(a0, b0),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_and(a0, c0),
                                    lib::intvector_intrinsics::vec256_and(b0, c0)
                                )
                            )
                        );
                    let a1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(t1, t2);
                    let b1: lib::intvector_intrinsics::vec256 = a0;
                    let c1: lib::intvector_intrinsics::vec256 = b0;
                    let d1: lib::intvector_intrinsics::vec256 = c0;
                    let e1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add32(d0, t1);
                    let f1: lib::intvector_intrinsics::vec256 = e0;
                    let g1: lib::intvector_intrinsics::vec256 = f0;
                    let h12: lib::intvector_intrinsics::vec256 = g0;
                    hash[0usize] = a1;
                    hash[1usize] = b1;
                    hash[2usize] = c1;
                    hash[3usize] = d1;
                    hash[4usize] = e1;
                    hash[5usize] = f1;
                    hash[6usize] = g1;
                    hash[7usize] = h12
                }
            );
            if i < 3u32
            {
                krml::unroll_for!(
                    16,
                    "i0",
                    0u32,
                    1u32,
                    {
                        let t16: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                        let t15: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                        let t7: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                        let t2: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                        let s1: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right32(t2, 17u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right32(t2, 19u32),
                                    lib::intvector_intrinsics::vec256_shift_right32(t2, 10u32)
                                )
                            );
                        let s0: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right32(t15, 7u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right32(t15, 18u32),
                                    lib::intvector_intrinsics::vec256_shift_right32(t15, 3u32)
                                )
                            );
                        (&mut ws)[i0 as usize] =
                            lib::intvector_intrinsics::vec256_add32(
                                lib::intvector_intrinsics::vec256_add32(
                                    lib::intvector_intrinsics::vec256_add32(s1, t7),
                                    s0
                                ),
                                t16
                            )
                    }
                )
            }
        }
    );
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add32(hash[i as usize], (&hash_old)[i as usize]);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha256_update_nblocks8(
    len: u32,
    mut b: crate::sha2_types::uint8_8p,
    st: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 = len.wrapping_div(64u32);
    for i in 0u32..blocks
    {
        let mb: crate::sha2_types::uint8_8p =
            match b
            {
                crate::sha2_types::uint8_8p
                {
                    fst: ref mut b0,
                    snd:
                    crate::sha2_types::uint8_7p
                    {
                        fst: ref mut b1,
                        snd:
                        crate::sha2_types::uint8_6p
                        {
                            fst: ref mut b2,
                            snd:
                            crate::sha2_types::uint8_5p
                            {
                                fst: ref mut b3,
                                snd:
                                crate::sha2_types::uint8_4p
                                {
                                    fst: ref mut b4,
                                    snd:
                                    crate::sha2_types::uint8_3p
                                    {
                                        fst: ref mut b5,
                                        snd:
                                        crate::sha2_types::uint8_2p
                                        { fst: ref mut b6, snd: ref mut b7 }
                                    }
                                }
                            }
                        }
                    }
                }
                =>
                  {
                      let bl0: (&mut [u8], &mut [u8]) =
                          b0.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl1: (&mut [u8], &mut [u8]) =
                          b1.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl2: (&mut [u8], &mut [u8]) =
                          b2.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl3: (&mut [u8], &mut [u8]) =
                          b3.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl4: (&mut [u8], &mut [u8]) =
                          b4.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl5: (&mut [u8], &mut [u8]) =
                          b5.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl6: (&mut [u8], &mut [u8]) =
                          b6.split_at_mut(i.wrapping_mul(64u32) as usize);
                      let bl7: (&mut [u8], &mut [u8]) =
                          b7.split_at_mut(i.wrapping_mul(64u32) as usize);
                      crate::sha2_types::uint8_8p
                      {
                          fst: bl0.1,
                          snd:
                          crate::sha2_types::uint8_7p
                          {
                              fst: bl1.1,
                              snd:
                              crate::sha2_types::uint8_6p
                              {
                                  fst: bl2.1,
                                  snd:
                                  crate::sha2_types::uint8_5p
                                  {
                                      fst: bl3.1,
                                      snd:
                                      crate::sha2_types::uint8_4p
                                      {
                                          fst: bl4.1,
                                          snd:
                                          crate::sha2_types::uint8_3p
                                          {
                                              fst: bl5.1,
                                              snd:
                                              crate::sha2_types::uint8_2p { fst: bl6.1, snd: bl7.1 }
                                          }
                                      }
                                  }
                              }
                          }
                      }
                  }
            };
        crate::sha2_vec256::sha256_update8(mb, st)
    }
}

#[inline] fn sha256_update_last8(
    totlen: u64,
    len: u32,
    b: crate::sha2_types::uint8_8p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 = if len.wrapping_add(8u32).wrapping_add(1u32) <= 64u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(64u32);
    let mut last: [u8; 1024] = [0u8; 1024usize];
    let mut totlen_buf: [u8; 8] = [0u8; 8usize];
    let total_len_bits: u64 = totlen.wrapping_shl(3u32);
    lowstar::endianness::store64_be(&mut totlen_buf, total_len_bits);
    let scrut: crate::sha2_types::uint8_2x8p =
        match b
        {
            crate::sha2_types::uint8_8p
            {
                fst: ref b0,
                snd:
                crate::sha2_types::uint8_7p
                {
                    fst: ref b1,
                    snd:
                    crate::sha2_types::uint8_6p
                    {
                        fst: ref b2,
                        snd:
                        crate::sha2_types::uint8_5p
                        {
                            fst: ref b3,
                            snd:
                            crate::sha2_types::uint8_4p
                            {
                                fst: ref b4,
                                snd:
                                crate::sha2_types::uint8_3p
                                {
                                    fst: ref b5,
                                    snd: crate::sha2_types::uint8_2p { fst: ref b6, snd: ref b7 }
                                }
                            }
                        }
                    }
                }
            }
            =>
              {
                  let last0: (&mut [u8], &mut [u8]) = last.split_at_mut(0usize);
                  let last1: (&mut [u8], &mut [u8]) = (last0.1).split_at_mut(128usize);
                  let last2: (&mut [u8], &mut [u8]) = (last1.1).split_at_mut(128usize);
                  let last3: (&mut [u8], &mut [u8]) = (last2.1).split_at_mut(128usize);
                  let last4: (&mut [u8], &mut [u8]) = (last3.1).split_at_mut(128usize);
                  let last5: (&mut [u8], &mut [u8]) = (last4.1).split_at_mut(128usize);
                  let last6: (&mut [u8], &mut [u8]) = (last5.1).split_at_mut(128usize);
                  let last7: (&mut [u8], &mut [u8]) = (last6.1).split_at_mut(128usize);
                  (last1.0[0usize..len as usize]).copy_from_slice(&(*b0)[0usize..len as usize]);
                  last1.0[len as usize] = 0x80u8;
                  (last1.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last01: (&mut [u8], &mut [u8]) = (last1.0).split_at_mut(0usize);
                  let last11: (&mut [u8], &mut [u8]) = (last01.1).split_at_mut(64usize);
                  let l00: &mut [u8] = last11.0;
                  let l01: &mut [u8] = last11.1;
                  (last2.0[0usize..len as usize]).copy_from_slice(&(*b1)[0usize..len as usize]);
                  last2.0[len as usize] = 0x80u8;
                  (last2.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last010: (&mut [u8], &mut [u8]) = (last2.0).split_at_mut(0usize);
                  let last110: (&mut [u8], &mut [u8]) = (last010.1).split_at_mut(64usize);
                  let l10: &mut [u8] = last110.0;
                  let l11: &mut [u8] = last110.1;
                  (last3.0[0usize..len as usize]).copy_from_slice(&(*b2)[0usize..len as usize]);
                  last3.0[len as usize] = 0x80u8;
                  (last3.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last011: (&mut [u8], &mut [u8]) = (last3.0).split_at_mut(0usize);
                  let last111: (&mut [u8], &mut [u8]) = (last011.1).split_at_mut(64usize);
                  let l20: &mut [u8] = last111.0;
                  let l21: &mut [u8] = last111.1;
                  (last4.0[0usize..len as usize]).copy_from_slice(&(*b3)[0usize..len as usize]);
                  last4.0[len as usize] = 0x80u8;
                  (last4.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last012: (&mut [u8], &mut [u8]) = (last4.0).split_at_mut(0usize);
                  let last112: (&mut [u8], &mut [u8]) = (last012.1).split_at_mut(64usize);
                  let l30: &mut [u8] = last112.0;
                  let l31: &mut [u8] = last112.1;
                  (last5.0[0usize..len as usize]).copy_from_slice(&(*b4)[0usize..len as usize]);
                  last5.0[len as usize] = 0x80u8;
                  (last5.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last013: (&mut [u8], &mut [u8]) = (last5.0).split_at_mut(0usize);
                  let last113: (&mut [u8], &mut [u8]) = (last013.1).split_at_mut(64usize);
                  let l40: &mut [u8] = last113.0;
                  let l41: &mut [u8] = last113.1;
                  (last6.0[0usize..len as usize]).copy_from_slice(&(*b5)[0usize..len as usize]);
                  last6.0[len as usize] = 0x80u8;
                  (last6.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last014: (&mut [u8], &mut [u8]) = (last6.0).split_at_mut(0usize);
                  let last114: (&mut [u8], &mut [u8]) = (last014.1).split_at_mut(64usize);
                  let l50: &mut [u8] = last114.0;
                  let l51: &mut [u8] = last114.1;
                  (last7.0[0usize..len as usize]).copy_from_slice(&(*b6)[0usize..len as usize]);
                  last7.0[len as usize] = 0x80u8;
                  (last7.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last015: (&mut [u8], &mut [u8]) = (last7.0).split_at_mut(0usize);
                  let last115: (&mut [u8], &mut [u8]) = (last015.1).split_at_mut(64usize);
                  let l60: &mut [u8] = last115.0;
                  let l61: &mut [u8] = last115.1;
                  (last7.1[0usize..len as usize]).copy_from_slice(&(*b7)[0usize..len as usize]);
                  last7.1[len as usize] = 0x80u8;
                  (last7.1[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last016: (&mut [u8], &mut [u8]) = (last7.1).split_at_mut(0usize);
                  let last116: (&mut [u8], &mut [u8]) = (last016.1).split_at_mut(64usize);
                  let l70: &mut [u8] = last116.0;
                  let l71: &mut [u8] = last116.1;
                  let mb0: crate::sha2_types::uint8_8p =
                      crate::sha2_types::uint8_8p
                      {
                          fst: l00,
                          snd:
                          crate::sha2_types::uint8_7p
                          {
                              fst: l10,
                              snd:
                              crate::sha2_types::uint8_6p
                              {
                                  fst: l20,
                                  snd:
                                  crate::sha2_types::uint8_5p
                                  {
                                      fst: l30,
                                      snd:
                                      crate::sha2_types::uint8_4p
                                      {
                                          fst: l40,
                                          snd:
                                          crate::sha2_types::uint8_3p
                                          {
                                              fst: l50,
                                              snd:
                                              crate::sha2_types::uint8_2p { fst: l60, snd: l70 }
                                          }
                                      }
                                  }
                              }
                          }
                      };
                  let mb1: crate::sha2_types::uint8_8p =
                      crate::sha2_types::uint8_8p
                      {
                          fst: l01,
                          snd:
                          crate::sha2_types::uint8_7p
                          {
                              fst: l11,
                              snd:
                              crate::sha2_types::uint8_6p
                              {
                                  fst: l21,
                                  snd:
                                  crate::sha2_types::uint8_5p
                                  {
                                      fst: l31,
                                      snd:
                                      crate::sha2_types::uint8_4p
                                      {
                                          fst: l41,
                                          snd:
                                          crate::sha2_types::uint8_3p
                                          {
                                              fst: l51,
                                              snd:
                                              crate::sha2_types::uint8_2p { fst: l61, snd: l71 }
                                          }
                                      }
                                  }
                              }
                          }
                      };
                  crate::sha2_types::uint8_2x8p { fst: mb0, snd: mb1 }
              }
        };
    let last0: crate::sha2_types::uint8_8p = scrut.fst;
    let last1: crate::sha2_types::uint8_8p = scrut.snd;
    crate::sha2_vec256::sha256_update8(last0, hash);
    if blocks > 1u32 { crate::sha2_vec256::sha256_update8(last1, hash) }
}

#[inline] fn sha256_finish8(
    st: &mut [lib::intvector_intrinsics::vec256],
    mut h: crate::sha2_types::uint8_8p
)
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: lib::intvector_intrinsics::vec256 = st[3usize];
    let v4: lib::intvector_intrinsics::vec256 = st[4usize];
    let v5: lib::intvector_intrinsics::vec256 = st[5usize];
    let v6: lib::intvector_intrinsics::vec256 = st[6usize];
    let v7: lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v2, v3);
    let v4·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v4, v5);
    let v5·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v4, v5);
    let v6·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low32(v6, v7);
    let v7·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high32(v6, v7);
    let v0·0: lib::intvector_intrinsics::vec256 = v0·;
    let v1·0: lib::intvector_intrinsics::vec256 = v1·;
    let v2·0: lib::intvector_intrinsics::vec256 = v2·;
    let v3·0: lib::intvector_intrinsics::vec256 = v3·;
    let v4·0: lib::intvector_intrinsics::vec256 = v4·;
    let v5·0: lib::intvector_intrinsics::vec256 = v5·;
    let v6·0: lib::intvector_intrinsics::vec256 = v6·;
    let v7·0: lib::intvector_intrinsics::vec256 = v7·;
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0·0, v2·0);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0·0, v2·0);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v1·0, v3·0);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v1·0, v3·0);
    let v4·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v4·0, v6·0);
    let v6·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v4·0, v6·0);
    let v5·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v5·0, v7·0);
    let v7·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v5·0, v7·0);
    let v0·10: lib::intvector_intrinsics::vec256 = v0·1;
    let v1·10: lib::intvector_intrinsics::vec256 = v1·1;
    let v2·10: lib::intvector_intrinsics::vec256 = v2·1;
    let v3·10: lib::intvector_intrinsics::vec256 = v3·1;
    let v4·10: lib::intvector_intrinsics::vec256 = v4·1;
    let v5·10: lib::intvector_intrinsics::vec256 = v5·1;
    let v6·10: lib::intvector_intrinsics::vec256 = v6·1;
    let v7·10: lib::intvector_intrinsics::vec256 = v7·1;
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·10, v4·10);
    let v4·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·10, v4·10);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·10, v5·10);
    let v5·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·10, v5·10);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v2·10, v6·10);
    let v6·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v2·10, v6·10);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v3·10, v7·10);
    let v7·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v3·10, v7·10);
    let v0·20: lib::intvector_intrinsics::vec256 = v0·2;
    let v1·20: lib::intvector_intrinsics::vec256 = v1·2;
    let v2·20: lib::intvector_intrinsics::vec256 = v2·2;
    let v3·20: lib::intvector_intrinsics::vec256 = v3·2;
    let v4·20: lib::intvector_intrinsics::vec256 = v4·2;
    let v5·20: lib::intvector_intrinsics::vec256 = v5·2;
    let v6·20: lib::intvector_intrinsics::vec256 = v6·2;
    let v7·20: lib::intvector_intrinsics::vec256 = v7·2;
    let v0·3: lib::intvector_intrinsics::vec256 = v0·20;
    let v1·3: lib::intvector_intrinsics::vec256 = v1·20;
    let v2·3: lib::intvector_intrinsics::vec256 = v2·20;
    let v3·3: lib::intvector_intrinsics::vec256 = v3·20;
    let v4·3: lib::intvector_intrinsics::vec256 = v4·20;
    let v5·3: lib::intvector_intrinsics::vec256 = v5·20;
    let v6·3: lib::intvector_intrinsics::vec256 = v6·20;
    let v7·3: lib::intvector_intrinsics::vec256 = v7·20;
    let st0·: lib::intvector_intrinsics::vec256 = v0·3;
    let st1·: lib::intvector_intrinsics::vec256 = v2·3;
    let st2·: lib::intvector_intrinsics::vec256 = v1·3;
    let st3·: lib::intvector_intrinsics::vec256 = v3·3;
    let st4·: lib::intvector_intrinsics::vec256 = v4·3;
    let st5·: lib::intvector_intrinsics::vec256 = v6·3;
    let st6·: lib::intvector_intrinsics::vec256 = v5·3;
    let st7·: lib::intvector_intrinsics::vec256 = v7·3;
    st[0usize] = st0·;
    st[1usize] = st1·;
    st[2usize] = st2·;
    st[3usize] = st3·;
    st[4usize] = st4·;
    st[5usize] = st5·;
    st[6usize] = st6·;
    st[7usize] = st7·;
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    );
    match h
    {
        crate::sha2_types::uint8_8p
        {
            fst: ref mut b0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: ref mut b1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: ref mut b2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: ref mut b3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: ref mut b4,
                            snd:
                            crate::sha2_types::uint8_3p
                            {
                                fst: ref mut b5,
                                snd:
                                crate::sha2_types::uint8_2p { fst: ref mut b6, snd: ref mut b7 }
                            }
                        }
                    }
                }
            }
        }
        =>
          {
              ((*b0)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..32usize]);
              ((*b1)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[32usize..])[0usize..32usize]);
              ((*b2)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[64usize..])[0usize..32usize]);
              ((*b3)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[96usize..])[0usize..32usize]);
              ((*b4)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[128usize..])[0usize..32usize]);
              ((*b5)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[160usize..])[0usize..32usize]);
              ((*b6)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[192usize..])[0usize..32usize]);
              ((*b7)[0usize..32usize]).copy_from_slice(&(&(&hbuf)[224usize..])[0usize..32usize])
          }
    }
}

pub fn sha256_8(
    dst0: &mut [u8],
    dst1: &mut [u8],
    dst2: &mut [u8],
    dst3: &mut [u8],
    dst4: &mut [u8],
    dst5: &mut [u8],
    dst6: &mut [u8],
    dst7: &mut [u8],
    input_len: u32,
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8],
    input4: &mut [u8],
    input5: &mut [u8],
    input6: &mut [u8],
    input7: &mut [u8]
)
{
    let mut ib: crate::sha2_types::uint8_8p =
        crate::sha2_types::uint8_8p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: input1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: input2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: input3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: input4,
                            snd:
                            crate::sha2_types::uint8_3p
                            {
                                fst: input5,
                                snd: crate::sha2_types::uint8_2p { fst: input6, snd: input7 }
                            }
                        }
                    }
                }
            }
        };
    let rb: crate::sha2_types::uint8_8p =
        crate::sha2_types::uint8_8p
        {
            fst: dst0,
            snd:
            crate::sha2_types::uint8_7p
            {
                fst: dst1,
                snd:
                crate::sha2_types::uint8_6p
                {
                    fst: dst2,
                    snd:
                    crate::sha2_types::uint8_5p
                    {
                        fst: dst3,
                        snd:
                        crate::sha2_types::uint8_4p
                        {
                            fst: dst4,
                            snd:
                            crate::sha2_types::uint8_3p
                            { fst: dst5, snd: crate::sha2_types::uint8_2p { fst: dst6, snd: dst7 } }
                        }
                    }
                }
            }
        };
    let mut st: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    crate::sha2_vec256::sha256_init8(&mut st);
    let rem: u32 = input_len.wrapping_rem(64u32);
    let len·: u64 = input_len as u64;
    crate::sha2_vec256::sha256_update_nblocks8(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(64u32);
    let lb: crate::sha2_types::uint8_8p =
        match ib
        {
            crate::sha2_types::uint8_8p
            {
                fst: ref mut b0,
                snd:
                crate::sha2_types::uint8_7p
                {
                    fst: ref mut b1,
                    snd:
                    crate::sha2_types::uint8_6p
                    {
                        fst: ref mut b2,
                        snd:
                        crate::sha2_types::uint8_5p
                        {
                            fst: ref mut b3,
                            snd:
                            crate::sha2_types::uint8_4p
                            {
                                fst: ref mut b4,
                                snd:
                                crate::sha2_types::uint8_3p
                                {
                                    fst: ref mut b5,
                                    snd:
                                    crate::sha2_types::uint8_2p { fst: ref mut b6, snd: ref mut b7 }
                                }
                            }
                        }
                    }
                }
            }
            =>
              {
                  let bl0: (&mut [u8], &mut [u8]) =
                      b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl1: (&mut [u8], &mut [u8]) =
                      b1.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl2: (&mut [u8], &mut [u8]) =
                      b2.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl3: (&mut [u8], &mut [u8]) =
                      b3.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl4: (&mut [u8], &mut [u8]) =
                      b4.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl5: (&mut [u8], &mut [u8]) =
                      b5.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl6: (&mut [u8], &mut [u8]) =
                      b6.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl7: (&mut [u8], &mut [u8]) =
                      b7.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  crate::sha2_types::uint8_8p
                  {
                      fst: bl0.1,
                      snd:
                      crate::sha2_types::uint8_7p
                      {
                          fst: bl1.1,
                          snd:
                          crate::sha2_types::uint8_6p
                          {
                              fst: bl2.1,
                              snd:
                              crate::sha2_types::uint8_5p
                              {
                                  fst: bl3.1,
                                  snd:
                                  crate::sha2_types::uint8_4p
                                  {
                                      fst: bl4.1,
                                      snd:
                                      crate::sha2_types::uint8_3p
                                      {
                                          fst: bl5.1,
                                          snd:
                                          crate::sha2_types::uint8_2p { fst: bl6.1, snd: bl7.1 }
                                      }
                                  }
                              }
                          }
                      }
                  }
              }
        };
    crate::sha2_vec256::sha256_update_last8(len·, rem, lb, &mut st);
    crate::sha2_vec256::sha256_finish8(&mut st, rb)
}

#[inline] fn sha384_init4(hash: &mut [lib::intvector_intrinsics::vec256])
{
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let hi: u64 = (&crate::hash_sha2::h384)[i as usize];
            let x: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(hi);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha384_update4(
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let mut hash_old: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [lib::intvector_intrinsics::vec256; 16] =
        [lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b1, snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[32usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[32usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[32usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[32usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[64usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[64usize..]);
              (&mut ws)[10usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[64usize..]);
              (&mut ws)[11usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[64usize..]);
              (&mut ws)[12usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[96usize..]);
              (&mut ws)[13usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[96usize..]);
              (&mut ws)[14usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[96usize..]);
              (&mut ws)[15usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[96usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
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
    krml::unroll_for!(
        5,
        "i",
        0u32,
        1u32,
        {
            krml::unroll_for!(
                16,
                "i0",
                0u32,
                1u32,
                {
                    let k_t: u64 =
                        (&crate::hash_sha2::k384_512)[16u32.wrapping_mul(i).wrapping_add(i0)
                        as
                        usize];
                    let ws_t: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                    let a0: lib::intvector_intrinsics::vec256 = hash[0usize];
                    let b0: lib::intvector_intrinsics::vec256 = hash[1usize];
                    let c0: lib::intvector_intrinsics::vec256 = hash[2usize];
                    let d0: lib::intvector_intrinsics::vec256 = hash[3usize];
                    let e0: lib::intvector_intrinsics::vec256 = hash[4usize];
                    let f0: lib::intvector_intrinsics::vec256 = hash[5usize];
                    let g0: lib::intvector_intrinsics::vec256 = hash[6usize];
                    let h02: lib::intvector_intrinsics::vec256 = hash[7usize];
                    let k_e_t: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_load64(k_t);
                    let t1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(
                            lib::intvector_intrinsics::vec256_add64(
                                lib::intvector_intrinsics::vec256_add64(
                                    lib::intvector_intrinsics::vec256_add64(
                                        h02,
                                        lib::intvector_intrinsics::vec256_xor(
                                            lib::intvector_intrinsics::vec256_rotate_right64(
                                                e0,
                                                14u32
                                            ),
                                            lib::intvector_intrinsics::vec256_xor(
                                                lib::intvector_intrinsics::vec256_rotate_right64(
                                                    e0,
                                                    18u32
                                                ),
                                                lib::intvector_intrinsics::vec256_rotate_right64(
                                                    e0,
                                                    41u32
                                                )
                                            )
                                        )
                                    ),
                                    lib::intvector_intrinsics::vec256_xor(
                                        lib::intvector_intrinsics::vec256_and(e0, f0),
                                        lib::intvector_intrinsics::vec256_and(
                                            lib::intvector_intrinsics::vec256_lognot(e0),
                                            g0
                                        )
                                    )
                                ),
                                k_e_t
                            ),
                            ws_t
                        );
                    let t2: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right64(a0, 28u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right64(a0, 34u32),
                                    lib::intvector_intrinsics::vec256_rotate_right64(a0, 39u32)
                                )
                            ),
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_and(a0, b0),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_and(a0, c0),
                                    lib::intvector_intrinsics::vec256_and(b0, c0)
                                )
                            )
                        );
                    let a1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(t1, t2);
                    let b1: lib::intvector_intrinsics::vec256 = a0;
                    let c1: lib::intvector_intrinsics::vec256 = b0;
                    let d1: lib::intvector_intrinsics::vec256 = c0;
                    let e1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(d0, t1);
                    let f1: lib::intvector_intrinsics::vec256 = e0;
                    let g1: lib::intvector_intrinsics::vec256 = f0;
                    let h12: lib::intvector_intrinsics::vec256 = g0;
                    hash[0usize] = a1;
                    hash[1usize] = b1;
                    hash[2usize] = c1;
                    hash[3usize] = d1;
                    hash[4usize] = e1;
                    hash[5usize] = f1;
                    hash[6usize] = g1;
                    hash[7usize] = h12
                }
            );
            if i < 4u32
            {
                krml::unroll_for!(
                    16,
                    "i0",
                    0u32,
                    1u32,
                    {
                        let t16: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                        let t15: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                        let t7: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                        let t2: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                        let s1: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right64(t2, 19u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right64(t2, 61u32),
                                    lib::intvector_intrinsics::vec256_shift_right64(t2, 6u32)
                                )
                            );
                        let s0: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right64(t15, 1u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right64(t15, 8u32),
                                    lib::intvector_intrinsics::vec256_shift_right64(t15, 7u32)
                                )
                            );
                        (&mut ws)[i0 as usize] =
                            lib::intvector_intrinsics::vec256_add64(
                                lib::intvector_intrinsics::vec256_add64(
                                    lib::intvector_intrinsics::vec256_add64(s1, t7),
                                    s0
                                ),
                                t16
                            )
                    }
                )
            }
        }
    );
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(hash[i as usize], (&hash_old)[i as usize]);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha384_update_nblocks4(
    len: u32,
    mut b: crate::sha2_types::uint8_4p,
    st: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 = len.wrapping_div(128u32);
    for i in 0u32..blocks
    {
        let mb: crate::sha2_types::uint8_4p =
            match b
            {
                crate::sha2_types::uint8_4p
                {
                    fst: ref mut b0,
                    snd:
                    crate::sha2_types::uint8_3p
                    {
                        fst: ref mut b1,
                        snd: crate::sha2_types::uint8_2p { fst: ref mut b2, snd: ref mut b3 }
                    }
                }
                =>
                  {
                      let bl0: (&mut [u8], &mut [u8]) =
                          b0.split_at_mut(i.wrapping_mul(128u32) as usize);
                      let bl1: (&mut [u8], &mut [u8]) =
                          b1.split_at_mut(i.wrapping_mul(128u32) as usize);
                      let bl2: (&mut [u8], &mut [u8]) =
                          b2.split_at_mut(i.wrapping_mul(128u32) as usize);
                      let bl3: (&mut [u8], &mut [u8]) =
                          b3.split_at_mut(i.wrapping_mul(128u32) as usize);
                      crate::sha2_types::uint8_4p
                      {
                          fst: bl0.1,
                          snd:
                          crate::sha2_types::uint8_3p
                          {
                              fst: bl1.1,
                              snd: crate::sha2_types::uint8_2p { fst: bl2.1, snd: bl3.1 }
                          }
                      }
                  }
            };
        crate::sha2_vec256::sha384_update4(mb, st)
    }
}

#[inline] fn sha384_update_last4(
    totlen: fstar::uint128::uint128,
    len: u32,
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 =
        if len.wrapping_add(16u32).wrapping_add(1u32) <= 128u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(128u32);
    let mut last: [u8; 1024] = [0u8; 1024usize];
    let mut totlen_buf: [u8; 16] = [0u8; 16usize];
    let total_len_bits: fstar::uint128::uint128 = fstar::uint128::shift_left(totlen, 3u32);
    lowstar::endianness::store128_be(&mut totlen_buf, total_len_bits);
    let scrut: crate::sha2_types::uint8_2x4p =
        match b
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: ref b1, snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 } }
            }
            =>
              {
                  let last0: (&mut [u8], &mut [u8]) = last.split_at_mut(0usize);
                  let last1: (&mut [u8], &mut [u8]) = (last0.1).split_at_mut(256usize);
                  let last2: (&mut [u8], &mut [u8]) = (last1.1).split_at_mut(256usize);
                  let last3: (&mut [u8], &mut [u8]) = (last2.1).split_at_mut(256usize);
                  (last1.0[0usize..len as usize]).copy_from_slice(&(*b0)[0usize..len as usize]);
                  last1.0[len as usize] = 0x80u8;
                  (last1.0[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last01: (&mut [u8], &mut [u8]) = (last1.0).split_at_mut(0usize);
                  let last11: (&mut [u8], &mut [u8]) = (last01.1).split_at_mut(128usize);
                  let l00: &mut [u8] = last11.0;
                  let l01: &mut [u8] = last11.1;
                  (last2.0[0usize..len as usize]).copy_from_slice(&(*b1)[0usize..len as usize]);
                  last2.0[len as usize] = 0x80u8;
                  (last2.0[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last010: (&mut [u8], &mut [u8]) = (last2.0).split_at_mut(0usize);
                  let last110: (&mut [u8], &mut [u8]) = (last010.1).split_at_mut(128usize);
                  let l10: &mut [u8] = last110.0;
                  let l11: &mut [u8] = last110.1;
                  (last3.0[0usize..len as usize]).copy_from_slice(&(*b2)[0usize..len as usize]);
                  last3.0[len as usize] = 0x80u8;
                  (last3.0[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last011: (&mut [u8], &mut [u8]) = (last3.0).split_at_mut(0usize);
                  let last111: (&mut [u8], &mut [u8]) = (last011.1).split_at_mut(128usize);
                  let l20: &mut [u8] = last111.0;
                  let l21: &mut [u8] = last111.1;
                  (last3.1[0usize..len as usize]).copy_from_slice(&(*b3)[0usize..len as usize]);
                  last3.1[len as usize] = 0x80u8;
                  (last3.1[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last012: (&mut [u8], &mut [u8]) = (last3.1).split_at_mut(0usize);
                  let last112: (&mut [u8], &mut [u8]) = (last012.1).split_at_mut(128usize);
                  let l30: &mut [u8] = last112.0;
                  let l31: &mut [u8] = last112.1;
                  let mb0: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l00,
                          snd:
                          crate::sha2_types::uint8_3p
                          { fst: l10, snd: crate::sha2_types::uint8_2p { fst: l20, snd: l30 } }
                      };
                  let mb1: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l01,
                          snd:
                          crate::sha2_types::uint8_3p
                          { fst: l11, snd: crate::sha2_types::uint8_2p { fst: l21, snd: l31 } }
                      };
                  crate::sha2_types::uint8_2x4p { fst: mb0, snd: mb1 }
              }
        };
    let last0: crate::sha2_types::uint8_4p = scrut.fst;
    let last1: crate::sha2_types::uint8_4p = scrut.snd;
    crate::sha2_vec256::sha384_update4(last0, hash);
    if blocks > 1u32 { crate::sha2_vec256::sha384_update4(last1, hash) }
}

#[inline] fn sha384_finish4(
    st: &mut [lib::intvector_intrinsics::vec256],
    mut h: crate::sha2_types::uint8_4p
)
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: lib::intvector_intrinsics::vec256 = st[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let st0·: lib::intvector_intrinsics::vec256 = v0··;
    let st1·: lib::intvector_intrinsics::vec256 = v2··;
    let st2·: lib::intvector_intrinsics::vec256 = v1··;
    let st3·: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = st[4usize];
    let v10: lib::intvector_intrinsics::vec256 = st[5usize];
    let v20: lib::intvector_intrinsics::vec256 = st[6usize];
    let v30: lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let st4·: lib::intvector_intrinsics::vec256 = v0··0;
    let st5·: lib::intvector_intrinsics::vec256 = v2··0;
    let st6·: lib::intvector_intrinsics::vec256 = v1··0;
    let st7·: lib::intvector_intrinsics::vec256 = v3··0;
    st[0usize] = st0·;
    st[1usize] = st4·;
    st[2usize] = st1·;
    st[3usize] = st5·;
    st[4usize] = st2·;
    st[5usize] = st6·;
    st[6usize] = st3·;
    st[7usize] = st7·;
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    );
    match h
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b0,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b1,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b2, snd: ref mut b3 }
            }
        }
        =>
          {
              ((*b0)[0usize..48usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..48usize]);
              ((*b1)[0usize..48usize]).copy_from_slice(&(&(&hbuf)[64usize..])[0usize..48usize]);
              ((*b2)[0usize..48usize]).copy_from_slice(&(&(&hbuf)[128usize..])[0usize..48usize]);
              ((*b3)[0usize..48usize]).copy_from_slice(&(&(&hbuf)[192usize..])[0usize..48usize])
          }
    }
}

pub fn sha384_4(
    dst0: &mut [u8],
    dst1: &mut [u8],
    dst2: &mut [u8],
    dst3: &mut [u8],
    input_len: u32,
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8]
)
{
    let mut ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: dst0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: dst1, snd: crate::sha2_types::uint8_2p { fst: dst2, snd: dst3 } }
        };
    let mut st: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    crate::sha2_vec256::sha384_init4(&mut st);
    let rem: u32 = input_len.wrapping_rem(128u32);
    let len·: fstar::uint128::uint128 = fstar::uint128::uint64_to_uint128(input_len as u64);
    crate::sha2_vec256::sha384_update_nblocks4(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(128u32);
    let lb: crate::sha2_types::uint8_4p =
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b0,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b1,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b2, snd: ref mut b3 }
                }
            }
            =>
              {
                  let bl0: (&mut [u8], &mut [u8]) =
                      b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl1: (&mut [u8], &mut [u8]) =
                      b1.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl2: (&mut [u8], &mut [u8]) =
                      b2.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl3: (&mut [u8], &mut [u8]) =
                      b3.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  crate::sha2_types::uint8_4p
                  {
                      fst: bl0.1,
                      snd:
                      crate::sha2_types::uint8_3p
                      { fst: bl1.1, snd: crate::sha2_types::uint8_2p { fst: bl2.1, snd: bl3.1 } }
                  }
              }
        };
    crate::sha2_vec256::sha384_update_last4(len·, rem, lb, &mut st);
    crate::sha2_vec256::sha384_finish4(&mut st, rb)
}

#[inline] fn sha512_init4(hash: &mut [lib::intvector_intrinsics::vec256])
{
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let hi: u64 = (&crate::hash_sha2::h512)[i as usize];
            let x: lib::intvector_intrinsics::vec256 = lib::intvector_intrinsics::vec256_load64(hi);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha512_update4(
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let mut hash_old: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    let mut ws: [lib::intvector_intrinsics::vec256; 16] =
        [lib::intvector_intrinsics::vec256_zero; 16usize];
    ((&mut hash_old)[0usize..8usize]).copy_from_slice(&hash[0usize..8usize]);
    match b
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref b0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: ref b1, snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 } }
        }
        =>
          {
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[32usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[32usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[32usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[32usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[64usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[64usize..]);
              (&mut ws)[10usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[64usize..]);
              (&mut ws)[11usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[64usize..]);
              (&mut ws)[12usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b0)[96usize..]);
              (&mut ws)[13usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b1)[96usize..]);
              (&mut ws)[14usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b2)[96usize..]);
              (&mut ws)[15usize] = lib::intvector_intrinsics::vec256_load64_be(&(*b3)[96usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec256 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec256 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec256 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec256 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let ws0: lib::intvector_intrinsics::vec256 = v0··;
    let ws1: lib::intvector_intrinsics::vec256 = v2··;
    let ws2: lib::intvector_intrinsics::vec256 = v1··;
    let ws3: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec256 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec256 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec256 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let ws4: lib::intvector_intrinsics::vec256 = v0··0;
    let ws5: lib::intvector_intrinsics::vec256 = v2··0;
    let ws6: lib::intvector_intrinsics::vec256 = v1··0;
    let ws7: lib::intvector_intrinsics::vec256 = v3··0;
    let v01: lib::intvector_intrinsics::vec256 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec256 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec256 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec256 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v21, v31);
    let v0··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·1, v2·1);
    let v1··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·1, v2·1);
    let v2··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·1, v3·1);
    let v3··1: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·1, v3·1);
    let ws8: lib::intvector_intrinsics::vec256 = v0··1;
    let ws9: lib::intvector_intrinsics::vec256 = v2··1;
    let ws10: lib::intvector_intrinsics::vec256 = v1··1;
    let ws11: lib::intvector_intrinsics::vec256 = v3··1;
    let v02: lib::intvector_intrinsics::vec256 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec256 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec256 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec256 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v22, v32);
    let v0··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·2, v2·2);
    let v1··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·2, v2·2);
    let v2··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·2, v3·2);
    let v3··2: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·2, v3·2);
    let ws12: lib::intvector_intrinsics::vec256 = v0··2;
    let ws13: lib::intvector_intrinsics::vec256 = v2··2;
    let ws14: lib::intvector_intrinsics::vec256 = v1··2;
    let ws15: lib::intvector_intrinsics::vec256 = v3··2;
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
    krml::unroll_for!(
        5,
        "i",
        0u32,
        1u32,
        {
            krml::unroll_for!(
                16,
                "i0",
                0u32,
                1u32,
                {
                    let k_t: u64 =
                        (&crate::hash_sha2::k384_512)[16u32.wrapping_mul(i).wrapping_add(i0)
                        as
                        usize];
                    let ws_t: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                    let a0: lib::intvector_intrinsics::vec256 = hash[0usize];
                    let b0: lib::intvector_intrinsics::vec256 = hash[1usize];
                    let c0: lib::intvector_intrinsics::vec256 = hash[2usize];
                    let d0: lib::intvector_intrinsics::vec256 = hash[3usize];
                    let e0: lib::intvector_intrinsics::vec256 = hash[4usize];
                    let f0: lib::intvector_intrinsics::vec256 = hash[5usize];
                    let g0: lib::intvector_intrinsics::vec256 = hash[6usize];
                    let h02: lib::intvector_intrinsics::vec256 = hash[7usize];
                    let k_e_t: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_load64(k_t);
                    let t1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(
                            lib::intvector_intrinsics::vec256_add64(
                                lib::intvector_intrinsics::vec256_add64(
                                    lib::intvector_intrinsics::vec256_add64(
                                        h02,
                                        lib::intvector_intrinsics::vec256_xor(
                                            lib::intvector_intrinsics::vec256_rotate_right64(
                                                e0,
                                                14u32
                                            ),
                                            lib::intvector_intrinsics::vec256_xor(
                                                lib::intvector_intrinsics::vec256_rotate_right64(
                                                    e0,
                                                    18u32
                                                ),
                                                lib::intvector_intrinsics::vec256_rotate_right64(
                                                    e0,
                                                    41u32
                                                )
                                            )
                                        )
                                    ),
                                    lib::intvector_intrinsics::vec256_xor(
                                        lib::intvector_intrinsics::vec256_and(e0, f0),
                                        lib::intvector_intrinsics::vec256_and(
                                            lib::intvector_intrinsics::vec256_lognot(e0),
                                            g0
                                        )
                                    )
                                ),
                                k_e_t
                            ),
                            ws_t
                        );
                    let t2: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right64(a0, 28u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right64(a0, 34u32),
                                    lib::intvector_intrinsics::vec256_rotate_right64(a0, 39u32)
                                )
                            ),
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_and(a0, b0),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_and(a0, c0),
                                    lib::intvector_intrinsics::vec256_and(b0, c0)
                                )
                            )
                        );
                    let a1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(t1, t2);
                    let b1: lib::intvector_intrinsics::vec256 = a0;
                    let c1: lib::intvector_intrinsics::vec256 = b0;
                    let d1: lib::intvector_intrinsics::vec256 = c0;
                    let e1: lib::intvector_intrinsics::vec256 =
                        lib::intvector_intrinsics::vec256_add64(d0, t1);
                    let f1: lib::intvector_intrinsics::vec256 = e0;
                    let g1: lib::intvector_intrinsics::vec256 = f0;
                    let h12: lib::intvector_intrinsics::vec256 = g0;
                    hash[0usize] = a1;
                    hash[1usize] = b1;
                    hash[2usize] = c1;
                    hash[3usize] = d1;
                    hash[4usize] = e1;
                    hash[5usize] = f1;
                    hash[6usize] = g1;
                    hash[7usize] = h12
                }
            );
            if i < 4u32
            {
                krml::unroll_for!(
                    16,
                    "i0",
                    0u32,
                    1u32,
                    {
                        let t16: lib::intvector_intrinsics::vec256 = (&ws)[i0 as usize];
                        let t15: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                        let t7: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                        let t2: lib::intvector_intrinsics::vec256 =
                            (&ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                        let s1: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right64(t2, 19u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right64(t2, 61u32),
                                    lib::intvector_intrinsics::vec256_shift_right64(t2, 6u32)
                                )
                            );
                        let s0: lib::intvector_intrinsics::vec256 =
                            lib::intvector_intrinsics::vec256_xor(
                                lib::intvector_intrinsics::vec256_rotate_right64(t15, 1u32),
                                lib::intvector_intrinsics::vec256_xor(
                                    lib::intvector_intrinsics::vec256_rotate_right64(t15, 8u32),
                                    lib::intvector_intrinsics::vec256_shift_right64(t15, 7u32)
                                )
                            );
                        (&mut ws)[i0 as usize] =
                            lib::intvector_intrinsics::vec256_add64(
                                lib::intvector_intrinsics::vec256_add64(
                                    lib::intvector_intrinsics::vec256_add64(s1, t7),
                                    s0
                                ),
                                t16
                            )
                    }
                )
            }
        }
    );
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let x: lib::intvector_intrinsics::vec256 =
                lib::intvector_intrinsics::vec256_add64(hash[i as usize], (&hash_old)[i as usize]);
            let
            os: (&mut [lib::intvector_intrinsics::vec256], &mut [lib::intvector_intrinsics::vec256])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha512_update_nblocks4(
    len: u32,
    mut b: crate::sha2_types::uint8_4p,
    st: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 = len.wrapping_div(128u32);
    for i in 0u32..blocks
    {
        let mb: crate::sha2_types::uint8_4p =
            match b
            {
                crate::sha2_types::uint8_4p
                {
                    fst: ref mut b0,
                    snd:
                    crate::sha2_types::uint8_3p
                    {
                        fst: ref mut b1,
                        snd: crate::sha2_types::uint8_2p { fst: ref mut b2, snd: ref mut b3 }
                    }
                }
                =>
                  {
                      let bl0: (&mut [u8], &mut [u8]) =
                          b0.split_at_mut(i.wrapping_mul(128u32) as usize);
                      let bl1: (&mut [u8], &mut [u8]) =
                          b1.split_at_mut(i.wrapping_mul(128u32) as usize);
                      let bl2: (&mut [u8], &mut [u8]) =
                          b2.split_at_mut(i.wrapping_mul(128u32) as usize);
                      let bl3: (&mut [u8], &mut [u8]) =
                          b3.split_at_mut(i.wrapping_mul(128u32) as usize);
                      crate::sha2_types::uint8_4p
                      {
                          fst: bl0.1,
                          snd:
                          crate::sha2_types::uint8_3p
                          {
                              fst: bl1.1,
                              snd: crate::sha2_types::uint8_2p { fst: bl2.1, snd: bl3.1 }
                          }
                      }
                  }
            };
        crate::sha2_vec256::sha512_update4(mb, st)
    }
}

#[inline] fn sha512_update_last4(
    totlen: fstar::uint128::uint128,
    len: u32,
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec256]
)
{
    let blocks: u32 =
        if len.wrapping_add(16u32).wrapping_add(1u32) <= 128u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(128u32);
    let mut last: [u8; 1024] = [0u8; 1024usize];
    let mut totlen_buf: [u8; 16] = [0u8; 16usize];
    let total_len_bits: fstar::uint128::uint128 = fstar::uint128::shift_left(totlen, 3u32);
    lowstar::endianness::store128_be(&mut totlen_buf, total_len_bits);
    let scrut: crate::sha2_types::uint8_2x4p =
        match b
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref b0,
                snd:
                crate::sha2_types::uint8_3p
                { fst: ref b1, snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 } }
            }
            =>
              {
                  let last0: (&mut [u8], &mut [u8]) = last.split_at_mut(0usize);
                  let last1: (&mut [u8], &mut [u8]) = (last0.1).split_at_mut(256usize);
                  let last2: (&mut [u8], &mut [u8]) = (last1.1).split_at_mut(256usize);
                  let last3: (&mut [u8], &mut [u8]) = (last2.1).split_at_mut(256usize);
                  (last1.0[0usize..len as usize]).copy_from_slice(&(*b0)[0usize..len as usize]);
                  last1.0[len as usize] = 0x80u8;
                  (last1.0[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last01: (&mut [u8], &mut [u8]) = (last1.0).split_at_mut(0usize);
                  let last11: (&mut [u8], &mut [u8]) = (last01.1).split_at_mut(128usize);
                  let l00: &mut [u8] = last11.0;
                  let l01: &mut [u8] = last11.1;
                  (last2.0[0usize..len as usize]).copy_from_slice(&(*b1)[0usize..len as usize]);
                  last2.0[len as usize] = 0x80u8;
                  (last2.0[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last010: (&mut [u8], &mut [u8]) = (last2.0).split_at_mut(0usize);
                  let last110: (&mut [u8], &mut [u8]) = (last010.1).split_at_mut(128usize);
                  let l10: &mut [u8] = last110.0;
                  let l11: &mut [u8] = last110.1;
                  (last3.0[0usize..len as usize]).copy_from_slice(&(*b2)[0usize..len as usize]);
                  last3.0[len as usize] = 0x80u8;
                  (last3.0[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last011: (&mut [u8], &mut [u8]) = (last3.0).split_at_mut(0usize);
                  let last111: (&mut [u8], &mut [u8]) = (last011.1).split_at_mut(128usize);
                  let l20: &mut [u8] = last111.0;
                  let l21: &mut [u8] = last111.1;
                  (last3.1[0usize..len as usize]).copy_from_slice(&(*b3)[0usize..len as usize]);
                  last3.1[len as usize] = 0x80u8;
                  (last3.1[fin.wrapping_sub(16u32) as usize..fin.wrapping_sub(16u32) as usize
                  +
                  16usize]).copy_from_slice(&(&totlen_buf)[0usize..16usize]);
                  let last012: (&mut [u8], &mut [u8]) = (last3.1).split_at_mut(0usize);
                  let last112: (&mut [u8], &mut [u8]) = (last012.1).split_at_mut(128usize);
                  let l30: &mut [u8] = last112.0;
                  let l31: &mut [u8] = last112.1;
                  let mb0: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l00,
                          snd:
                          crate::sha2_types::uint8_3p
                          { fst: l10, snd: crate::sha2_types::uint8_2p { fst: l20, snd: l30 } }
                      };
                  let mb1: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l01,
                          snd:
                          crate::sha2_types::uint8_3p
                          { fst: l11, snd: crate::sha2_types::uint8_2p { fst: l21, snd: l31 } }
                      };
                  crate::sha2_types::uint8_2x4p { fst: mb0, snd: mb1 }
              }
        };
    let last0: crate::sha2_types::uint8_4p = scrut.fst;
    let last1: crate::sha2_types::uint8_4p = scrut.snd;
    crate::sha2_vec256::sha512_update4(last0, hash);
    if blocks > 1u32 { crate::sha2_vec256::sha512_update4(last1, hash) }
}

#[inline] fn sha512_finish4(
    st: &mut [lib::intvector_intrinsics::vec256],
    mut h: crate::sha2_types::uint8_4p
)
{
    let mut hbuf: [u8; 256] = [0u8; 256usize];
    let v0: lib::intvector_intrinsics::vec256 = st[0usize];
    let v1: lib::intvector_intrinsics::vec256 = st[1usize];
    let v2: lib::intvector_intrinsics::vec256 = st[2usize];
    let v3: lib::intvector_intrinsics::vec256 = st[3usize];
    let v0·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v0, v1);
    let v1·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v0, v1);
    let v2·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v2, v3);
    let v3·: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v2, v3);
    let v0··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·, v3·);
    let st0·: lib::intvector_intrinsics::vec256 = v0··;
    let st1·: lib::intvector_intrinsics::vec256 = v2··;
    let st2·: lib::intvector_intrinsics::vec256 = v1··;
    let st3·: lib::intvector_intrinsics::vec256 = v3··;
    let v00: lib::intvector_intrinsics::vec256 = st[4usize];
    let v10: lib::intvector_intrinsics::vec256 = st[5usize];
    let v20: lib::intvector_intrinsics::vec256 = st[6usize];
    let v30: lib::intvector_intrinsics::vec256 = st[7usize];
    let v0·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low64(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high64(v20, v30);
    let v0··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v0·0, v2·0);
    let v1··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v0·0, v2·0);
    let v2··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_low128(v1·0, v3·0);
    let v3··0: lib::intvector_intrinsics::vec256 =
        lib::intvector_intrinsics::vec256_interleave_high128(v1·0, v3·0);
    let st4·: lib::intvector_intrinsics::vec256 = v0··0;
    let st5·: lib::intvector_intrinsics::vec256 = v2··0;
    let st6·: lib::intvector_intrinsics::vec256 = v1··0;
    let st7·: lib::intvector_intrinsics::vec256 = v3··0;
    st[0usize] = st0·;
    st[1usize] = st4·;
    st[2usize] = st1·;
    st[3usize] = st5·;
    st[4usize] = st2·;
    st[5usize] = st6·;
    st[6usize] = st3·;
    st[7usize] = st7·;
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        lib::intvector_intrinsics::vec256_store64_be(
            &mut (&mut hbuf)[i.wrapping_mul(32u32) as usize..],
            st[i as usize]
        )
    );
    match h
    {
        crate::sha2_types::uint8_4p
        {
            fst: ref mut b0,
            snd:
            crate::sha2_types::uint8_3p
            {
                fst: ref mut b1,
                snd: crate::sha2_types::uint8_2p { fst: ref mut b2, snd: ref mut b3 }
            }
        }
        =>
          {
              ((*b0)[0usize..64usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..64usize]);
              ((*b1)[0usize..64usize]).copy_from_slice(&(&(&hbuf)[64usize..])[0usize..64usize]);
              ((*b2)[0usize..64usize]).copy_from_slice(&(&(&hbuf)[128usize..])[0usize..64usize]);
              ((*b3)[0usize..64usize]).copy_from_slice(&(&(&hbuf)[192usize..])[0usize..64usize])
          }
    }
}

pub fn sha512_4(
    dst0: &mut [u8],
    dst1: &mut [u8],
    dst2: &mut [u8],
    dst3: &mut [u8],
    input_len: u32,
    input0: &mut [u8],
    input1: &mut [u8],
    input2: &mut [u8],
    input3: &mut [u8]
)
{
    let mut ib: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: input0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: input1, snd: crate::sha2_types::uint8_2p { fst: input2, snd: input3 } }
        };
    let rb: crate::sha2_types::uint8_4p =
        crate::sha2_types::uint8_4p
        {
            fst: dst0,
            snd:
            crate::sha2_types::uint8_3p
            { fst: dst1, snd: crate::sha2_types::uint8_2p { fst: dst2, snd: dst3 } }
        };
    let mut st: [lib::intvector_intrinsics::vec256; 8] =
        [lib::intvector_intrinsics::vec256_zero; 8usize];
    crate::sha2_vec256::sha512_init4(&mut st);
    let rem: u32 = input_len.wrapping_rem(128u32);
    let len·: fstar::uint128::uint128 = fstar::uint128::uint64_to_uint128(input_len as u64);
    crate::sha2_vec256::sha512_update_nblocks4(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(128u32);
    let lb: crate::sha2_types::uint8_4p =
        match ib
        {
            crate::sha2_types::uint8_4p
            {
                fst: ref mut b0,
                snd:
                crate::sha2_types::uint8_3p
                {
                    fst: ref mut b1,
                    snd: crate::sha2_types::uint8_2p { fst: ref mut b2, snd: ref mut b3 }
                }
            }
            =>
              {
                  let bl0: (&mut [u8], &mut [u8]) =
                      b0.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl1: (&mut [u8], &mut [u8]) =
                      b1.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl2: (&mut [u8], &mut [u8]) =
                      b2.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  let bl3: (&mut [u8], &mut [u8]) =
                      b3.split_at_mut(input_len.wrapping_sub(rem1) as usize);
                  crate::sha2_types::uint8_4p
                  {
                      fst: bl0.1,
                      snd:
                      crate::sha2_types::uint8_3p
                      { fst: bl1.1, snd: crate::sha2_types::uint8_2p { fst: bl2.1, snd: bl3.1 } }
                  }
              }
        };
    crate::sha2_vec256::sha512_update_last4(len·, rem, lb, &mut st);
    crate::sha2_vec256::sha512_finish4(&mut st, rb)
}
