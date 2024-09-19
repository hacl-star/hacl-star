#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(const_item_mutation)]

#[inline] fn sha224_init4(hash: &mut [lib::intvector_intrinsics::vec128])
{
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let hi: u32 = (&crate::hash_sha2::h224)[i as usize];
            let x: lib::intvector_intrinsics::vec128 =
                lib::intvector_intrinsics::vec128_load32(hi);
            let
            os:
            (&mut [lib::intvector_intrinsics::vec128],
            &mut [lib::intvector_intrinsics::vec128])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha224_update4(
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec128]
)
{
    let mut hash_old: [lib::intvector_intrinsics::vec128; 8] =
        [lib::intvector_intrinsics::vec128_zero; 8usize];
    let mut ws: [lib::intvector_intrinsics::vec128; 16] =
        [lib::intvector_intrinsics::vec128_zero; 16usize];
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
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec128_load32_be(&b0[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec128_load32_be(&b1[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec128_load32_be(&b2[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec128_load32_be(&b3[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec128_load32_be(&b0[16usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec128_load32_be(&b1[16usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec128_load32_be(&b2[16usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec128_load32_be(&b3[16usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec128_load32_be(&b0[32usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec128_load32_be(&b1[32usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b2[32usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b3[32usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b0[48usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b1[48usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b2[48usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b3[48usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec128 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec128 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec128 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec128 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v2, v3);
    let v0··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
    let v0··0: lib::intvector_intrinsics::vec128 = v0··;
    let v2··0: lib::intvector_intrinsics::vec128 = v2··;
    let v1··0: lib::intvector_intrinsics::vec128 = v1··;
    let v3··0: lib::intvector_intrinsics::vec128 = v3··;
    let ws0: lib::intvector_intrinsics::vec128 = v0··0;
    let ws1: lib::intvector_intrinsics::vec128 = v1··0;
    let ws2: lib::intvector_intrinsics::vec128 = v2··0;
    let ws3: lib::intvector_intrinsics::vec128 = v3··0;
    let v00: lib::intvector_intrinsics::vec128 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec128 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec128 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec128 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v20, v30);
    let v0··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
    let v1··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
    let v2··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
    let v3··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
    let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
    let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
    let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
    let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
    let ws4: lib::intvector_intrinsics::vec128 = v0··2;
    let ws5: lib::intvector_intrinsics::vec128 = v1··2;
    let ws6: lib::intvector_intrinsics::vec128 = v2··2;
    let ws7: lib::intvector_intrinsics::vec128 = v3··2;
    let v01: lib::intvector_intrinsics::vec128 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec128 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec128 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec128 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v21, v31);
    let v0··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·1, v2·1);
    let v1··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·1, v2·1);
    let v2··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·1, v3·1);
    let v3··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·1, v3·1);
    let v0··4: lib::intvector_intrinsics::vec128 = v0··3;
    let v2··4: lib::intvector_intrinsics::vec128 = v2··3;
    let v1··4: lib::intvector_intrinsics::vec128 = v1··3;
    let v3··4: lib::intvector_intrinsics::vec128 = v3··3;
    let ws8: lib::intvector_intrinsics::vec128 = v0··4;
    let ws9: lib::intvector_intrinsics::vec128 = v1··4;
    let ws10: lib::intvector_intrinsics::vec128 = v2··4;
    let ws11: lib::intvector_intrinsics::vec128 = v3··4;
    let v02: lib::intvector_intrinsics::vec128 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec128 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec128 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec128 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v22, v32);
    let v0··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·2, v2·2);
    let v1··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·2, v2·2);
    let v2··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·2, v3·2);
    let v3··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·2, v3·2);
    let v0··6: lib::intvector_intrinsics::vec128 = v0··5;
    let v2··6: lib::intvector_intrinsics::vec128 = v2··5;
    let v1··6: lib::intvector_intrinsics::vec128 = v1··5;
    let v3··6: lib::intvector_intrinsics::vec128 = v3··5;
    let ws12: lib::intvector_intrinsics::vec128 = v0··6;
    let ws13: lib::intvector_intrinsics::vec128 = v1··6;
    let ws14: lib::intvector_intrinsics::vec128 = v2··6;
    let ws15: lib::intvector_intrinsics::vec128 = v3··6;
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
                    let ws_t: lib::intvector_intrinsics::vec128 = (&ws)[i0 as usize];
                    let a0: lib::intvector_intrinsics::vec128 = hash[0usize];
                    let b0: lib::intvector_intrinsics::vec128 = hash[1usize];
                    let c0: lib::intvector_intrinsics::vec128 = hash[2usize];
                    let d0: lib::intvector_intrinsics::vec128 = hash[3usize];
                    let e0: lib::intvector_intrinsics::vec128 = hash[4usize];
                    let f0: lib::intvector_intrinsics::vec128 = hash[5usize];
                    let g0: lib::intvector_intrinsics::vec128 = hash[6usize];
                    let h02: lib::intvector_intrinsics::vec128 = hash[7usize];
                    let k_e_t: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_load32(k_t);
                    let t1: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(
                            lib::intvector_intrinsics::vec128_add32(
                                lib::intvector_intrinsics::vec128_add32(
                                    lib::intvector_intrinsics::vec128_add32(
                                        h02,
                                        lib::intvector_intrinsics::vec128_xor(
                                            lib::intvector_intrinsics::vec128_rotate_right32(
                                                e0,
                                                6u32
                                            ),
                                            lib::intvector_intrinsics::vec128_xor(
                                                lib::intvector_intrinsics::vec128_rotate_right32(
                                                    e0,
                                                    11u32
                                                ),
                                                lib::intvector_intrinsics::vec128_rotate_right32(
                                                    e0,
                                                    25u32
                                                )
                                            )
                                        )
                                    ),
                                    lib::intvector_intrinsics::vec128_xor(
                                        lib::intvector_intrinsics::vec128_and(e0, f0),
                                        lib::intvector_intrinsics::vec128_and(
                                            lib::intvector_intrinsics::vec128_lognot(e0),
                                            g0
                                        )
                                    )
                                ),
                                k_e_t
                            ),
                            ws_t
                        );
                    let t2: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_rotate_right32(a0, 2u32),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        a0,
                                        13u32
                                    ),
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        a0,
                                        22u32
                                    )
                                )
                            ),
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_and(a0, b0),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_and(a0, c0),
                                    lib::intvector_intrinsics::vec128_and(b0, c0)
                                )
                            )
                        );
                    let a1: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(t1, t2);
                    let b1: lib::intvector_intrinsics::vec128 = a0;
                    let c1: lib::intvector_intrinsics::vec128 = b0;
                    let d1: lib::intvector_intrinsics::vec128 = c0;
                    let e1: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(d0, t1);
                    let f1: lib::intvector_intrinsics::vec128 = e0;
                    let g1: lib::intvector_intrinsics::vec128 = f0;
                    let h12: lib::intvector_intrinsics::vec128 = g0;
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
                        let t16: lib::intvector_intrinsics::vec128 = (&ws)[i0 as usize];
                        let t15: lib::intvector_intrinsics::vec128 =
                            (&ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                        let t7: lib::intvector_intrinsics::vec128 =
                            (&ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                        let t2: lib::intvector_intrinsics::vec128 =
                            (&ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                        let s1: lib::intvector_intrinsics::vec128 =
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_rotate_right32(t2, 17u32),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        t2,
                                        19u32
                                    ),
                                    lib::intvector_intrinsics::vec128_shift_right32(
                                        t2,
                                        10u32
                                    )
                                )
                            );
                        let s0: lib::intvector_intrinsics::vec128 =
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_rotate_right32(t15, 7u32),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        t15,
                                        18u32
                                    ),
                                    lib::intvector_intrinsics::vec128_shift_right32(
                                        t15,
                                        3u32
                                    )
                                )
                            );
                        (&mut ws)[i0 as usize] =
                            lib::intvector_intrinsics::vec128_add32(
                                lib::intvector_intrinsics::vec128_add32(
                                    lib::intvector_intrinsics::vec128_add32(s1, t7),
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
            let x: lib::intvector_intrinsics::vec128 =
                lib::intvector_intrinsics::vec128_add32(
                    hash[i as usize],
                    (&hash_old)[i as usize]
                );
            let
            os:
            (&mut [lib::intvector_intrinsics::vec128],
            &mut [lib::intvector_intrinsics::vec128])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha224_update_nblocks4(
    len: u32,
    b: crate::sha2_types::uint8_4p,
    st: &mut [lib::intvector_intrinsics::vec128]
)
{
    let blocks: u32 = len.wrapping_div(64u32);
    for i in 0u32..blocks
    {
        let mb: crate::sha2_types::uint8_4p =
            match b
            {
                crate::sha2_types::uint8_4p
                {
                    fst: ref b0,
                    snd:
                    crate::sha2_types::uint8_3p
                    {
                        fst: ref b1,
                        snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 }
                    }
                }
                =>
                  {
                      let bl0: (&[u8], &[u8]) = b0.split_at(i.wrapping_mul(64u32) as usize);
                      let bl1: (&[u8], &[u8]) = b1.split_at(i.wrapping_mul(64u32) as usize);
                      let bl2: (&[u8], &[u8]) = b2.split_at(i.wrapping_mul(64u32) as usize);
                      let bl3: (&[u8], &[u8]) = b3.split_at(i.wrapping_mul(64u32) as usize);
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
        sha224_update4(mb, st)
    }
}

#[inline] fn sha224_update_last4(
    totlen: u64,
    len: u32,
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec128]
)
{
    let blocks: u32 = if len.wrapping_add(8u32).wrapping_add(1u32) <= 64u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(64u32);
    let mut last: [u8; 512] = [0u8; 512usize];
    let mut totlen_buf: [u8; 8] = [0u8; 8usize];
    let total_len_bits: u64 = totlen.wrapping_shl(3u32);
    lowstar::endianness::store64_be(&mut totlen_buf, total_len_bits);
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
                  let last1: (&mut [u8], &mut [u8]) = last0.1.split_at_mut(128usize);
                  let last2: (&mut [u8], &mut [u8]) = last1.1.split_at_mut(128usize);
                  let last3: (&mut [u8], &mut [u8]) = last2.1.split_at_mut(128usize);
                  (last1.0[0usize..len as usize]).copy_from_slice(&b0[0usize..len as usize]);
                  last1.0[len as usize] = 0x80u8;
                  (last1.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last01: (&[u8], &[u8]) = last1.0.split_at(0usize);
                  let last11: (&[u8], &[u8]) = last01.1.split_at(64usize);
                  let l00: &[u8] = last11.0;
                  let l01: &[u8] = last11.1;
                  (last2.0[0usize..len as usize]).copy_from_slice(&b1[0usize..len as usize]);
                  last2.0[len as usize] = 0x80u8;
                  (last2.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last010: (&[u8], &[u8]) = last2.0.split_at(0usize);
                  let last110: (&[u8], &[u8]) = last010.1.split_at(64usize);
                  let l10: &[u8] = last110.0;
                  let l11: &[u8] = last110.1;
                  (last3.0[0usize..len as usize]).copy_from_slice(&b2[0usize..len as usize]);
                  last3.0[len as usize] = 0x80u8;
                  (last3.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last011: (&[u8], &[u8]) = last3.0.split_at(0usize);
                  let last111: (&[u8], &[u8]) = last011.1.split_at(64usize);
                  let l20: &[u8] = last111.0;
                  let l21: &[u8] = last111.1;
                  (last3.1[0usize..len as usize]).copy_from_slice(&b3[0usize..len as usize]);
                  last3.1[len as usize] = 0x80u8;
                  (last3.1[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last012: (&[u8], &[u8]) = last3.1.split_at(0usize);
                  let last112: (&[u8], &[u8]) = last012.1.split_at(64usize);
                  let l30: &[u8] = last112.0;
                  let l31: &[u8] = last112.1;
                  let mb0: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l00,
                          snd:
                          crate::sha2_types::uint8_3p
                          {
                              fst: l10,
                              snd: crate::sha2_types::uint8_2p { fst: l20, snd: l30 }
                          }
                      };
                  let mb1: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l01,
                          snd:
                          crate::sha2_types::uint8_3p
                          {
                              fst: l11,
                              snd: crate::sha2_types::uint8_2p { fst: l21, snd: l31 }
                          }
                      };
                  crate::sha2_types::uint8_2x4p { fst: mb0, snd: mb1 }
              }
        };
    let last0: &crate::sha2_types::uint8_4p = &scrut.fst;
    let last1: &crate::sha2_types::uint8_4p = &scrut.snd;
    sha224_update4(*last0, hash);
    if blocks > 1u32 { sha224_update4(*last1, hash) }
}

#[inline] fn sha224_finish4(
    st: &mut [lib::intvector_intrinsics::vec128],
    mut h: crate::sha2_types::uint8_4p
)
{
    let mut hbuf: [u8; 128] = [0u8; 128usize];
    let v0: lib::intvector_intrinsics::vec128 = st[0usize];
    let v1: lib::intvector_intrinsics::vec128 = st[1usize];
    let v2: lib::intvector_intrinsics::vec128 = st[2usize];
    let v3: lib::intvector_intrinsics::vec128 = st[3usize];
    let v0·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v2, v3);
    let v0··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
    let v0··0: lib::intvector_intrinsics::vec128 = v0··;
    let v2··0: lib::intvector_intrinsics::vec128 = v2··;
    let v1··0: lib::intvector_intrinsics::vec128 = v1··;
    let v3··0: lib::intvector_intrinsics::vec128 = v3··;
    let st0·: lib::intvector_intrinsics::vec128 = v0··0;
    let st1·: lib::intvector_intrinsics::vec128 = v1··0;
    let st2·: lib::intvector_intrinsics::vec128 = v2··0;
    let st3·: lib::intvector_intrinsics::vec128 = v3··0;
    let v00: lib::intvector_intrinsics::vec128 = st[4usize];
    let v10: lib::intvector_intrinsics::vec128 = st[5usize];
    let v20: lib::intvector_intrinsics::vec128 = st[6usize];
    let v30: lib::intvector_intrinsics::vec128 = st[7usize];
    let v0·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v20, v30);
    let v0··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
    let v1··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
    let v2··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
    let v3··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
    let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
    let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
    let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
    let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
    let st4·: lib::intvector_intrinsics::vec128 = v0··2;
    let st5·: lib::intvector_intrinsics::vec128 = v1··2;
    let st6·: lib::intvector_intrinsics::vec128 = v2··2;
    let st7·: lib::intvector_intrinsics::vec128 = v3··2;
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
        lib::intvector_intrinsics::vec128_store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(16u32) as usize..],
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
              (b0[0usize..28usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..28usize]);
              (b1[0usize..28usize]).copy_from_slice(&(&(&hbuf)[32usize..])[0usize..28usize]);
              (b2[0usize..28usize]).copy_from_slice(&(&(&hbuf)[64usize..])[0usize..28usize]);
              (b3[0usize..28usize]).copy_from_slice(&(&(&hbuf)[96usize..])[0usize..28usize])
          }
    }
}

pub fn sha224_4(
    dst0: &[u8],
    dst1: &[u8],
    dst2: &[u8],
    dst3: &[u8],
    input_len: u32,
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8]
)
{
    let ib: crate::sha2_types::uint8_4p =
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
    let mut st: [lib::intvector_intrinsics::vec128; 8] =
        [lib::intvector_intrinsics::vec128_zero; 8usize];
    sha224_init4(&mut st);
    let rem: u32 = input_len.wrapping_rem(64u32);
    let len·: u64 = input_len as u64;
    sha224_update_nblocks4(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(64u32);
    let lb: crate::sha2_types::uint8_4p =
        match ib
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
                  let bl0: (&[u8], &[u8]) = b0.split_at(input_len.wrapping_sub(rem1) as usize);
                  let bl1: (&[u8], &[u8]) = b1.split_at(input_len.wrapping_sub(rem1) as usize);
                  let bl2: (&[u8], &[u8]) = b2.split_at(input_len.wrapping_sub(rem1) as usize);
                  let bl3: (&[u8], &[u8]) = b3.split_at(input_len.wrapping_sub(rem1) as usize);
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
    sha224_update_last4(len·, rem, lb, &mut st);
    sha224_finish4(&mut st, rb)
}

#[inline] fn sha256_init4(hash: &mut [lib::intvector_intrinsics::vec128])
{
    krml::unroll_for!(
        8,
        "i",
        0u32,
        1u32,
        {
            let hi: u32 = (&crate::hash_sha2::h256)[i as usize];
            let x: lib::intvector_intrinsics::vec128 =
                lib::intvector_intrinsics::vec128_load32(hi);
            let
            os:
            (&mut [lib::intvector_intrinsics::vec128],
            &mut [lib::intvector_intrinsics::vec128])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha256_update4(
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec128]
)
{
    let mut hash_old: [lib::intvector_intrinsics::vec128; 8] =
        [lib::intvector_intrinsics::vec128_zero; 8usize];
    let mut ws: [lib::intvector_intrinsics::vec128; 16] =
        [lib::intvector_intrinsics::vec128_zero; 16usize];
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
              (&mut ws)[0usize] = lib::intvector_intrinsics::vec128_load32_be(&b0[0usize..]);
              (&mut ws)[1usize] = lib::intvector_intrinsics::vec128_load32_be(&b1[0usize..]);
              (&mut ws)[2usize] = lib::intvector_intrinsics::vec128_load32_be(&b2[0usize..]);
              (&mut ws)[3usize] = lib::intvector_intrinsics::vec128_load32_be(&b3[0usize..]);
              (&mut ws)[4usize] = lib::intvector_intrinsics::vec128_load32_be(&b0[16usize..]);
              (&mut ws)[5usize] = lib::intvector_intrinsics::vec128_load32_be(&b1[16usize..]);
              (&mut ws)[6usize] = lib::intvector_intrinsics::vec128_load32_be(&b2[16usize..]);
              (&mut ws)[7usize] = lib::intvector_intrinsics::vec128_load32_be(&b3[16usize..]);
              (&mut ws)[8usize] = lib::intvector_intrinsics::vec128_load32_be(&b0[32usize..]);
              (&mut ws)[9usize] = lib::intvector_intrinsics::vec128_load32_be(&b1[32usize..]);
              (&mut ws)[10usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b2[32usize..]);
              (&mut ws)[11usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b3[32usize..]);
              (&mut ws)[12usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b0[48usize..]);
              (&mut ws)[13usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b1[48usize..]);
              (&mut ws)[14usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b2[48usize..]);
              (&mut ws)[15usize] =
                  lib::intvector_intrinsics::vec128_load32_be(&b3[48usize..])
          }
    };
    let v0: lib::intvector_intrinsics::vec128 = (&ws)[0usize];
    let v1: lib::intvector_intrinsics::vec128 = (&ws)[1usize];
    let v2: lib::intvector_intrinsics::vec128 = (&ws)[2usize];
    let v3: lib::intvector_intrinsics::vec128 = (&ws)[3usize];
    let v0·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v2, v3);
    let v0··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
    let v0··0: lib::intvector_intrinsics::vec128 = v0··;
    let v2··0: lib::intvector_intrinsics::vec128 = v2··;
    let v1··0: lib::intvector_intrinsics::vec128 = v1··;
    let v3··0: lib::intvector_intrinsics::vec128 = v3··;
    let ws0: lib::intvector_intrinsics::vec128 = v0··0;
    let ws1: lib::intvector_intrinsics::vec128 = v1··0;
    let ws2: lib::intvector_intrinsics::vec128 = v2··0;
    let ws3: lib::intvector_intrinsics::vec128 = v3··0;
    let v00: lib::intvector_intrinsics::vec128 = (&ws)[4usize];
    let v10: lib::intvector_intrinsics::vec128 = (&ws)[5usize];
    let v20: lib::intvector_intrinsics::vec128 = (&ws)[6usize];
    let v30: lib::intvector_intrinsics::vec128 = (&ws)[7usize];
    let v0·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v20, v30);
    let v0··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
    let v1··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
    let v2··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
    let v3··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
    let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
    let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
    let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
    let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
    let ws4: lib::intvector_intrinsics::vec128 = v0··2;
    let ws5: lib::intvector_intrinsics::vec128 = v1··2;
    let ws6: lib::intvector_intrinsics::vec128 = v2··2;
    let ws7: lib::intvector_intrinsics::vec128 = v3··2;
    let v01: lib::intvector_intrinsics::vec128 = (&ws)[8usize];
    let v11: lib::intvector_intrinsics::vec128 = (&ws)[9usize];
    let v21: lib::intvector_intrinsics::vec128 = (&ws)[10usize];
    let v31: lib::intvector_intrinsics::vec128 = (&ws)[11usize];
    let v0·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v01, v11);
    let v1·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v01, v11);
    let v2·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v21, v31);
    let v3·1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v21, v31);
    let v0··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·1, v2·1);
    let v1··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·1, v2·1);
    let v2··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·1, v3·1);
    let v3··3: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·1, v3·1);
    let v0··4: lib::intvector_intrinsics::vec128 = v0··3;
    let v2··4: lib::intvector_intrinsics::vec128 = v2··3;
    let v1··4: lib::intvector_intrinsics::vec128 = v1··3;
    let v3··4: lib::intvector_intrinsics::vec128 = v3··3;
    let ws8: lib::intvector_intrinsics::vec128 = v0··4;
    let ws9: lib::intvector_intrinsics::vec128 = v1··4;
    let ws10: lib::intvector_intrinsics::vec128 = v2··4;
    let ws11: lib::intvector_intrinsics::vec128 = v3··4;
    let v02: lib::intvector_intrinsics::vec128 = (&ws)[12usize];
    let v12: lib::intvector_intrinsics::vec128 = (&ws)[13usize];
    let v22: lib::intvector_intrinsics::vec128 = (&ws)[14usize];
    let v32: lib::intvector_intrinsics::vec128 = (&ws)[15usize];
    let v0·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v02, v12);
    let v1·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v02, v12);
    let v2·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v22, v32);
    let v3·2: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v22, v32);
    let v0··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·2, v2·2);
    let v1··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·2, v2·2);
    let v2··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·2, v3·2);
    let v3··5: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·2, v3·2);
    let v0··6: lib::intvector_intrinsics::vec128 = v0··5;
    let v2··6: lib::intvector_intrinsics::vec128 = v2··5;
    let v1··6: lib::intvector_intrinsics::vec128 = v1··5;
    let v3··6: lib::intvector_intrinsics::vec128 = v3··5;
    let ws12: lib::intvector_intrinsics::vec128 = v0··6;
    let ws13: lib::intvector_intrinsics::vec128 = v1··6;
    let ws14: lib::intvector_intrinsics::vec128 = v2··6;
    let ws15: lib::intvector_intrinsics::vec128 = v3··6;
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
                    let ws_t: lib::intvector_intrinsics::vec128 = (&ws)[i0 as usize];
                    let a0: lib::intvector_intrinsics::vec128 = hash[0usize];
                    let b0: lib::intvector_intrinsics::vec128 = hash[1usize];
                    let c0: lib::intvector_intrinsics::vec128 = hash[2usize];
                    let d0: lib::intvector_intrinsics::vec128 = hash[3usize];
                    let e0: lib::intvector_intrinsics::vec128 = hash[4usize];
                    let f0: lib::intvector_intrinsics::vec128 = hash[5usize];
                    let g0: lib::intvector_intrinsics::vec128 = hash[6usize];
                    let h02: lib::intvector_intrinsics::vec128 = hash[7usize];
                    let k_e_t: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_load32(k_t);
                    let t1: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(
                            lib::intvector_intrinsics::vec128_add32(
                                lib::intvector_intrinsics::vec128_add32(
                                    lib::intvector_intrinsics::vec128_add32(
                                        h02,
                                        lib::intvector_intrinsics::vec128_xor(
                                            lib::intvector_intrinsics::vec128_rotate_right32(
                                                e0,
                                                6u32
                                            ),
                                            lib::intvector_intrinsics::vec128_xor(
                                                lib::intvector_intrinsics::vec128_rotate_right32(
                                                    e0,
                                                    11u32
                                                ),
                                                lib::intvector_intrinsics::vec128_rotate_right32(
                                                    e0,
                                                    25u32
                                                )
                                            )
                                        )
                                    ),
                                    lib::intvector_intrinsics::vec128_xor(
                                        lib::intvector_intrinsics::vec128_and(e0, f0),
                                        lib::intvector_intrinsics::vec128_and(
                                            lib::intvector_intrinsics::vec128_lognot(e0),
                                            g0
                                        )
                                    )
                                ),
                                k_e_t
                            ),
                            ws_t
                        );
                    let t2: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_rotate_right32(a0, 2u32),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        a0,
                                        13u32
                                    ),
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        a0,
                                        22u32
                                    )
                                )
                            ),
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_and(a0, b0),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_and(a0, c0),
                                    lib::intvector_intrinsics::vec128_and(b0, c0)
                                )
                            )
                        );
                    let a1: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(t1, t2);
                    let b1: lib::intvector_intrinsics::vec128 = a0;
                    let c1: lib::intvector_intrinsics::vec128 = b0;
                    let d1: lib::intvector_intrinsics::vec128 = c0;
                    let e1: lib::intvector_intrinsics::vec128 =
                        lib::intvector_intrinsics::vec128_add32(d0, t1);
                    let f1: lib::intvector_intrinsics::vec128 = e0;
                    let g1: lib::intvector_intrinsics::vec128 = f0;
                    let h12: lib::intvector_intrinsics::vec128 = g0;
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
                        let t16: lib::intvector_intrinsics::vec128 = (&ws)[i0 as usize];
                        let t15: lib::intvector_intrinsics::vec128 =
                            (&ws)[i0.wrapping_add(1u32).wrapping_rem(16u32) as usize];
                        let t7: lib::intvector_intrinsics::vec128 =
                            (&ws)[i0.wrapping_add(9u32).wrapping_rem(16u32) as usize];
                        let t2: lib::intvector_intrinsics::vec128 =
                            (&ws)[i0.wrapping_add(14u32).wrapping_rem(16u32) as usize];
                        let s1: lib::intvector_intrinsics::vec128 =
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_rotate_right32(t2, 17u32),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        t2,
                                        19u32
                                    ),
                                    lib::intvector_intrinsics::vec128_shift_right32(
                                        t2,
                                        10u32
                                    )
                                )
                            );
                        let s0: lib::intvector_intrinsics::vec128 =
                            lib::intvector_intrinsics::vec128_xor(
                                lib::intvector_intrinsics::vec128_rotate_right32(t15, 7u32),
                                lib::intvector_intrinsics::vec128_xor(
                                    lib::intvector_intrinsics::vec128_rotate_right32(
                                        t15,
                                        18u32
                                    ),
                                    lib::intvector_intrinsics::vec128_shift_right32(
                                        t15,
                                        3u32
                                    )
                                )
                            );
                        (&mut ws)[i0 as usize] =
                            lib::intvector_intrinsics::vec128_add32(
                                lib::intvector_intrinsics::vec128_add32(
                                    lib::intvector_intrinsics::vec128_add32(s1, t7),
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
            let x: lib::intvector_intrinsics::vec128 =
                lib::intvector_intrinsics::vec128_add32(
                    hash[i as usize],
                    (&hash_old)[i as usize]
                );
            let
            os:
            (&mut [lib::intvector_intrinsics::vec128],
            &mut [lib::intvector_intrinsics::vec128])
            =
                hash.split_at_mut(0usize);
            os.1[i as usize] = x
        }
    )
}

#[inline] fn sha256_update_nblocks4(
    len: u32,
    b: crate::sha2_types::uint8_4p,
    st: &mut [lib::intvector_intrinsics::vec128]
)
{
    let blocks: u32 = len.wrapping_div(64u32);
    for i in 0u32..blocks
    {
        let mb: crate::sha2_types::uint8_4p =
            match b
            {
                crate::sha2_types::uint8_4p
                {
                    fst: ref b0,
                    snd:
                    crate::sha2_types::uint8_3p
                    {
                        fst: ref b1,
                        snd: crate::sha2_types::uint8_2p { fst: ref b2, snd: ref b3 }
                    }
                }
                =>
                  {
                      let bl0: (&[u8], &[u8]) = b0.split_at(i.wrapping_mul(64u32) as usize);
                      let bl1: (&[u8], &[u8]) = b1.split_at(i.wrapping_mul(64u32) as usize);
                      let bl2: (&[u8], &[u8]) = b2.split_at(i.wrapping_mul(64u32) as usize);
                      let bl3: (&[u8], &[u8]) = b3.split_at(i.wrapping_mul(64u32) as usize);
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
        sha256_update4(mb, st)
    }
}

#[inline] fn sha256_update_last4(
    totlen: u64,
    len: u32,
    b: crate::sha2_types::uint8_4p,
    hash: &mut [lib::intvector_intrinsics::vec128]
)
{
    let blocks: u32 = if len.wrapping_add(8u32).wrapping_add(1u32) <= 64u32 { 1u32 } else { 2u32 };
    let fin: u32 = blocks.wrapping_mul(64u32);
    let mut last: [u8; 512] = [0u8; 512usize];
    let mut totlen_buf: [u8; 8] = [0u8; 8usize];
    let total_len_bits: u64 = totlen.wrapping_shl(3u32);
    lowstar::endianness::store64_be(&mut totlen_buf, total_len_bits);
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
                  let last1: (&mut [u8], &mut [u8]) = last0.1.split_at_mut(128usize);
                  let last2: (&mut [u8], &mut [u8]) = last1.1.split_at_mut(128usize);
                  let last3: (&mut [u8], &mut [u8]) = last2.1.split_at_mut(128usize);
                  (last1.0[0usize..len as usize]).copy_from_slice(&b0[0usize..len as usize]);
                  last1.0[len as usize] = 0x80u8;
                  (last1.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last01: (&[u8], &[u8]) = last1.0.split_at(0usize);
                  let last11: (&[u8], &[u8]) = last01.1.split_at(64usize);
                  let l00: &[u8] = last11.0;
                  let l01: &[u8] = last11.1;
                  (last2.0[0usize..len as usize]).copy_from_slice(&b1[0usize..len as usize]);
                  last2.0[len as usize] = 0x80u8;
                  (last2.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last010: (&[u8], &[u8]) = last2.0.split_at(0usize);
                  let last110: (&[u8], &[u8]) = last010.1.split_at(64usize);
                  let l10: &[u8] = last110.0;
                  let l11: &[u8] = last110.1;
                  (last3.0[0usize..len as usize]).copy_from_slice(&b2[0usize..len as usize]);
                  last3.0[len as usize] = 0x80u8;
                  (last3.0[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last011: (&[u8], &[u8]) = last3.0.split_at(0usize);
                  let last111: (&[u8], &[u8]) = last011.1.split_at(64usize);
                  let l20: &[u8] = last111.0;
                  let l21: &[u8] = last111.1;
                  (last3.1[0usize..len as usize]).copy_from_slice(&b3[0usize..len as usize]);
                  last3.1[len as usize] = 0x80u8;
                  (last3.1[fin.wrapping_sub(8u32) as usize..fin.wrapping_sub(8u32) as usize + 8usize]).copy_from_slice(
                      &(&totlen_buf)[0usize..8usize]
                  );
                  let last012: (&[u8], &[u8]) = last3.1.split_at(0usize);
                  let last112: (&[u8], &[u8]) = last012.1.split_at(64usize);
                  let l30: &[u8] = last112.0;
                  let l31: &[u8] = last112.1;
                  let mb0: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l00,
                          snd:
                          crate::sha2_types::uint8_3p
                          {
                              fst: l10,
                              snd: crate::sha2_types::uint8_2p { fst: l20, snd: l30 }
                          }
                      };
                  let mb1: crate::sha2_types::uint8_4p =
                      crate::sha2_types::uint8_4p
                      {
                          fst: l01,
                          snd:
                          crate::sha2_types::uint8_3p
                          {
                              fst: l11,
                              snd: crate::sha2_types::uint8_2p { fst: l21, snd: l31 }
                          }
                      };
                  crate::sha2_types::uint8_2x4p { fst: mb0, snd: mb1 }
              }
        };
    let last0: &crate::sha2_types::uint8_4p = &scrut.fst;
    let last1: &crate::sha2_types::uint8_4p = &scrut.snd;
    sha256_update4(*last0, hash);
    if blocks > 1u32 { sha256_update4(*last1, hash) }
}

#[inline] fn sha256_finish4(
    st: &mut [lib::intvector_intrinsics::vec128],
    mut h: crate::sha2_types::uint8_4p
)
{
    let mut hbuf: [u8; 128] = [0u8; 128usize];
    let v0: lib::intvector_intrinsics::vec128 = st[0usize];
    let v1: lib::intvector_intrinsics::vec128 = st[1usize];
    let v2: lib::intvector_intrinsics::vec128 = st[2usize];
    let v3: lib::intvector_intrinsics::vec128 = st[3usize];
    let v0·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v0, v1);
    let v1·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v0, v1);
    let v2·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v2, v3);
    let v3·: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v2, v3);
    let v0··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·, v2·);
    let v1··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·, v2·);
    let v2··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·, v3·);
    let v3··: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·, v3·);
    let v0··0: lib::intvector_intrinsics::vec128 = v0··;
    let v2··0: lib::intvector_intrinsics::vec128 = v2··;
    let v1··0: lib::intvector_intrinsics::vec128 = v1··;
    let v3··0: lib::intvector_intrinsics::vec128 = v3··;
    let st0·: lib::intvector_intrinsics::vec128 = v0··0;
    let st1·: lib::intvector_intrinsics::vec128 = v1··0;
    let st2·: lib::intvector_intrinsics::vec128 = v2··0;
    let st3·: lib::intvector_intrinsics::vec128 = v3··0;
    let v00: lib::intvector_intrinsics::vec128 = st[4usize];
    let v10: lib::intvector_intrinsics::vec128 = st[5usize];
    let v20: lib::intvector_intrinsics::vec128 = st[6usize];
    let v30: lib::intvector_intrinsics::vec128 = st[7usize];
    let v0·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v00, v10);
    let v1·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v00, v10);
    let v2·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low32(v20, v30);
    let v3·0: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high32(v20, v30);
    let v0··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v0·0, v2·0);
    let v1··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v0·0, v2·0);
    let v2··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_low64(v1·0, v3·0);
    let v3··1: lib::intvector_intrinsics::vec128 =
        lib::intvector_intrinsics::vec128_interleave_high64(v1·0, v3·0);
    let v0··2: lib::intvector_intrinsics::vec128 = v0··1;
    let v2··2: lib::intvector_intrinsics::vec128 = v2··1;
    let v1··2: lib::intvector_intrinsics::vec128 = v1··1;
    let v3··2: lib::intvector_intrinsics::vec128 = v3··1;
    let st4·: lib::intvector_intrinsics::vec128 = v0··2;
    let st5·: lib::intvector_intrinsics::vec128 = v1··2;
    let st6·: lib::intvector_intrinsics::vec128 = v2··2;
    let st7·: lib::intvector_intrinsics::vec128 = v3··2;
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
        lib::intvector_intrinsics::vec128_store32_be(
            &mut (&mut hbuf)[i.wrapping_mul(16u32) as usize..],
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
              (b0[0usize..32usize]).copy_from_slice(&(&(&hbuf)[0usize..])[0usize..32usize]);
              (b1[0usize..32usize]).copy_from_slice(&(&(&hbuf)[32usize..])[0usize..32usize]);
              (b2[0usize..32usize]).copy_from_slice(&(&(&hbuf)[64usize..])[0usize..32usize]);
              (b3[0usize..32usize]).copy_from_slice(&(&(&hbuf)[96usize..])[0usize..32usize])
          }
    }
}

pub fn sha256_4(
    dst0: &[u8],
    dst1: &[u8],
    dst2: &[u8],
    dst3: &[u8],
    input_len: u32,
    input0: &[u8],
    input1: &[u8],
    input2: &[u8],
    input3: &[u8]
)
{
    let ib: crate::sha2_types::uint8_4p =
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
    let mut st: [lib::intvector_intrinsics::vec128; 8] =
        [lib::intvector_intrinsics::vec128_zero; 8usize];
    sha256_init4(&mut st);
    let rem: u32 = input_len.wrapping_rem(64u32);
    let len·: u64 = input_len as u64;
    sha256_update_nblocks4(input_len, ib, &mut st);
    let rem1: u32 = input_len.wrapping_rem(64u32);
    let lb: crate::sha2_types::uint8_4p =
        match ib
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
                  let bl0: (&[u8], &[u8]) = b0.split_at(input_len.wrapping_sub(rem1) as usize);
                  let bl1: (&[u8], &[u8]) = b1.split_at(input_len.wrapping_sub(rem1) as usize);
                  let bl2: (&[u8], &[u8]) = b2.split_at(input_len.wrapping_sub(rem1) as usize);
                  let bl3: (&[u8], &[u8]) = b3.split_at(input_len.wrapping_sub(rem1) as usize);
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
    sha256_update_last4(len·, rem, lb, &mut st);
    sha256_finish4(&mut st, rb)
}
