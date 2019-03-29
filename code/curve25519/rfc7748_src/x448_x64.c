/**
 * Copyright (c) 2017, Armando Faz <armfazh@ic.unicamp.br>. All rights reserved.
 * Institute of Computing.
 * University of Campinas, Brazil.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *  * Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *  * Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *  * Neither the name of University of Campinas nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "fp448_x64.h"
#include "rfc7748_precomputed.h"
#include "table_ladder_x448.h"

static inline void cswap_x64(uint64_t bit, uint64_t *const px,
                             uint64_t *const py) {
  int i = 0;
  uint64_t mask = (uint64_t)0 - bit;
  for (i = 0; i < NUM_WORDS_ELTFP448_X64; i++) {
    uint64_t t = mask & (px[i] ^ py[i]);
    px[i] = px[i] ^ t;
    py[i] = py[i] ^ t;
  }
}

static void x448_shared_x64(argKey shared, argKey session_key,
                            argKey private_key) {
  ALIGN uint64_t buffer[4 * NUM_WORDS_ELTFP448_X64];
  ALIGN uint64_t coordinates[4 * NUM_WORDS_ELTFP448_X64];
  ALIGN uint64_t workspace[6 * NUM_WORDS_ELTFP448_X64];
  uint64_t save;

  int i = 0, j = 0;
  uint64_t prev = 0;
  uint64_t *const X1 = (uint64_t *)session_key;
  uint64_t *const key = (uint64_t *)private_key;
  uint64_t *const Px = coordinates + 0;
  uint64_t *const Pz = coordinates + 7;
  uint64_t *const Qx = coordinates + 14;
  uint64_t *const Qz = coordinates + 21;
  uint64_t *const X2 = Qx;
  uint64_t *const Z2 = Qz;
  uint64_t *const X3 = Px;
  uint64_t *const Z3 = Pz;

  uint64_t *const A = workspace + 0;
  uint64_t *const B = workspace + 7;
  uint64_t *const D = workspace + 14;
  uint64_t *const C = workspace + 21;
  uint64_t *const DA = workspace + 28;
  uint64_t *const CB = workspace + 35;
  uint64_t *const buffer_1w = buffer;

  /** clamp function */
  save = private_key[X448_KEYSIZE_BYTES - 1] << 16 | private_key[0];
  private_key[0] = private_key[0] & (~(uint8_t)0x3);
  private_key[X448_KEYSIZE_BYTES - 1] |= 0x80;

  for (i = 0; i < NUM_WORDS_ELTFP448_X64; i++) {
    Px[i] = ((uint64_t *)session_key)[i];
    Pz[i] = 0;
    Qx[i] = 0;
    Qz[i] = 0;
  }

  Pz[0] = 1;
  Qx[0] = 1;

  /* main-loop */
  j = 63;
  for (i = 6; i >= 0; i--) {
    while (j >= 0) {
      uint64_t bit = (key[i] >> j) & 0x1;
      uint64_t swap = bit ^ prev;
      prev = bit;

      add_EltFp448_1w_x64(A, X2, Z2); /* A = (X2+Z2) */
      sub_EltFp448_1w_x64(B, X2, Z2); /* B = (X2-Z2) */
      add_EltFp448_1w_x64(C, X3, Z3); /* C = (X3+Z3) */
      sub_EltFp448_1w_x64(D, X3, Z3); /* D = (X3-Z3) */

      mul_EltFp448_1w_x64(DA, A, D); /* DA = A*D    */
      mul_EltFp448_1w_x64(CB, C, B); /* CB = C*B    */

      cswap_x64(swap, A, C);
      cswap_x64(swap, B, D);

      sqr_EltFp448_1w_x64(A); /* A = A^2          */
      sqr_EltFp448_1w_x64(B); /* B = B^2          */

      add_EltFp448_1w_x64(X3, DA, CB); /* X3 = (DA+CB)     */
      sub_EltFp448_1w_x64(Z3, DA, CB); /* Z3 = (DA-CB)     */
      sqr_EltFp448_1w_x64(X3);         /* X3 = (DA+CB)^2   */
      sqr_EltFp448_1w_x64(Z3);         /* Z3 = (DA*CB)^2   */

      copy_EltFp448_1w_x64(X2, B);     /* X2 = B^2         */
      sub_EltFp448_1w_x64(Z2, A, B);   /* Z2 = E = AA-BB   */
      mul_a24_EltFp448_1w_x64(B, Z2);  /*  B = a24*E       */
      add_EltFp448_1w_x64(B, B, X2);   /*  B = a24*E+B     */
      mul_EltFp448_1w_x64(X2, X2, A);  /* X2 = A*B         */
      mul_EltFp448_1w_x64(Z2, Z2, B);  /* Z2 = E*(a24*E+B) */
      mul_EltFp448_1w_x64(Z3, Z3, X1); /* Z3 = Z3*X1       */

      j--;
    }
    j = 63;
  }
  inv_EltFp448_1w_x64(A, Qz);
  mul_EltFp448_1w_x64((uint64_t *)shared, Qx, A);
  fred_EltFp448_1w_x64((uint64_t *)shared);
  private_key[X448_KEYSIZE_BYTES - 1] = (uint8_t)((save >> 16) & 0xFF);
  private_key[0] = (uint8_t)(save & 0xFF);
}

static void x448_keygen_x64(argKey public_key, argKey private_key) {
  ALIGN uint64_t buffer[4 * NUM_WORDS_ELTFP448_X64];
  ALIGN uint64_t coordinates[4 * NUM_WORDS_ELTFP448_X64];
  ALIGN uint64_t workspace[4 * NUM_WORDS_ELTFP448_X64];
  uint64_t save;

  int i = 0, j = 0, k = 0;
  uint64_t *const key = (uint64_t *)private_key;
  uint64_t *const Ur1 = coordinates + 0;
  uint64_t *const Zr1 = coordinates + 7;
  uint64_t *const Ur2 = coordinates + 14;
  uint64_t *const Zr2 = coordinates + 21;
  uint64_t *const A = workspace + 0;
  uint64_t *const B = workspace + 7;
  uint64_t *const C = workspace + 14;
  uint64_t *const D = workspace + 21;
  uint64_t *const buffer_1w = buffer;

  uint64_t *P = (uint64_t *)Table_Ladder_24k;

  /** clamp function */
  save = private_key[X448_KEYSIZE_BYTES - 1] << 16 | private_key[0];
  private_key[0] = private_key[0] & (~(uint8_t)0x3);
  private_key[X448_KEYSIZE_BYTES - 1] |= 0x80;

  for (i = 0; i < NUM_WORDS_ELTFP448_X64; i++) {
    Ur1[i] = 0;
    Zr1[i] = 0;
    Zr2[i] = 0;
  }

  /* G-S */
  Ur2[0] = 0xacb1197dc99d2720;
  Ur2[1] = 0x23ac33ff1c69baf8;
  Ur2[2] = 0xf1bd65643ace1b51;
  Ur2[3] = 0x2954459d84c1f823;
  Ur2[4] = 0xdacdd1031c81b967;
  Ur2[5] = 0x3acf03881affeb7b;
  Ur2[6] = 0xf0fab72501324442;

  /* Ur1 = -1 mod p */
  Ur1[0] = 0xfffffffffffffffe;
  Ur1[1] = 0xffffffffffffffff;
  Ur1[2] = 0xffffffffffffffff;
  Ur1[3] = 0xfffffffeffffffff;
  Ur1[4] = 0xffffffffffffffff;
  Ur1[5] = 0xffffffffffffffff;
  Ur1[6] = 0xffffffffffffffff;

  Zr1[0] = 1;
  Zr2[0] = 1;

  /* main-loop */
  const int q = 2;
  uint64_t swap = 1;

  j = q;
  for (i = 0; i < NUM_WORDS_ELTFP448_X64; i++) {
    while (j < 64) {
      k = (64 * i + j - q);
      uint64_t bit = (key[i] >> j) & 0x1;
      swap = swap ^ bit;
      cswap_x64(swap, Ur1, Ur2);
      cswap_x64(swap, Zr1, Zr2);
      swap = bit;

      /** Addition */
      add_EltFp448_1w_x64(A, Ur1, Zr1);     /* A = Ur1+Zr1  */
      sub_EltFp448_1w_x64(B, Ur1, Zr1);     /* B = Ur1-Zr1  */
      mul_EltFp448_1w_x64(C, &P[7 * k], B); /* C = M0-B     */
      sub_EltFp448_1w_x64(B, A, C);         /* B = (Ur1+Zr1) - M*(Ur1-Zr1) */
      add_EltFp448_1w_x64(A, A, C);         /* A = (Ur1+Zr1) + M*(Ur1-Zr1) */
      sqr_EltFp448_1w_x64(A);               /* A = A^2      */
      sqr_EltFp448_1w_x64(B);               /* B = B^2      */
      mul_EltFp448_1w_x64(Ur1, Zr2, A);     /* Ur1 = Zr2*A  */
      mul_EltFp448_1w_x64(Zr1, Ur2, B);     /* Zr1 = Ur2*B  */

      j++;
    }
    j = 0;
  }

  /** Doubling */
  for (i = 0; i < q; i++) {
    add_EltFp448_1w_x64(A, Ur1, Zr1); /* A = Ur1+Zr1   */
    sub_EltFp448_1w_x64(B, Ur1, Zr1); /* B = Ur1-Zr1   */
    sqr_EltFp448_1w_x64(A);           /* A = A**2     B = B**2   */
    sqr_EltFp448_1w_x64(B);           /* A = A**2     B = B**2   */
    copy_EltFp448_1w_x64(C, B);       /* C = B         */
    sub_EltFp448_1w_x64(B, A, B);     /* B = A-B       */
    mul_a24_EltFp448_1w_x64(D, B);    /* D = my_a24*B  */
    add_EltFp448_1w_x64(D, D, C);     /* D = D+C       */
    mul_EltFp448_1w_x64(Ur1, A, C);   /* Ur1 = A*B   Zr1 = Zr1*A */
    mul_EltFp448_1w_x64(Zr1, B, D);   /* Ur1 = A*B   Zr1 = Zr1*A */
  }

  /* Convert to affine coordinates */
  inv_EltFp448_1w_x64(A, Zr1);
  mul_EltFp448_1w_x64((uint64_t *)public_key, Ur1, A);
  fred_EltFp448_1w_x64((uint64_t *)public_key);
  private_key[X448_KEYSIZE_BYTES - 1] = (uint8_t)((save >> 16) & 0xFF);
  private_key[0] = (uint8_t)(save & 0xFF);
}

const KeyGen X448_KeyGen = x448_keygen_x64;
const Shared X448_Shared = x448_shared_x64;
