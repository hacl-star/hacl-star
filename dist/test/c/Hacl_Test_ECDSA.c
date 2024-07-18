/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#include "Hacl_Test_ECDSA.h"

extern void C_String_print(Prims_string uu___);


/*******************************************************************************

 Verified C library for ECDSA and ECDH functions over the P-256 NIST curve.

 This module implements signing and verification, key validation, conversions
 between various point representations, and ECDH key agreement.

*******************************************************************************/

/*****************/
/* ECDSA signing */
/*****************/

/*
  As per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/

/**
Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
extern bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Create an ECDSA signature using SHA2-384.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
extern bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);

/**
Create an ECDSA signature using SHA2-512.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve
*/
extern bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);


/**********************/
/* ECDSA verification */
/**********************/

/**
Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
extern bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);

/**
Verify an ECDSA signature using SHA2-384.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
extern bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);

/**
Verify an ECDSA signature using SHA2-512.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The argument `public_key` (x || y) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `signature_r` and `signature_s` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `public_key` is valid
*/
extern bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);

extern void LowStar_Printf_print_string(Prims_string uu___);

extern void LowStar_Printf_print_u32(uint32_t uu___);

extern void LowStar_Printf_print_lmbuffer_u8(uint32_t l, uint8_t *b);

static uint8_t
sigver_vectors256_low0[128U] =
  {
    228U, 121U, 109U, 181U, 247U, 133U, 242U, 7U, 170U, 48U, 211U, 17U, 105U, 59U, 55U, 2U, 130U,
    29U, 255U, 17U, 104U, 253U, 46U, 4U, 192U, 131U, 104U, 37U, 174U, 253U, 133U, 13U, 154U, 166U,
    3U, 38U, 216U, 140U, 222U, 26U, 35U, 199U, 116U, 83U, 81U, 57U, 44U, 162U, 40U, 141U, 99U, 44U,
    38U, 79U, 25U, 125U, 5U, 205U, 66U, 74U, 48U, 51U, 108U, 25U, 253U, 9U, 187U, 34U, 150U, 84U,
    240U, 34U, 47U, 203U, 136U, 26U, 75U, 53U, 194U, 144U, 160U, 147U, 172U, 21U, 156U, 225U, 52U,
    9U, 17U, 31U, 240U, 53U, 132U, 17U, 19U, 60U, 36U, 245U, 184U, 226U, 9U, 13U, 109U, 182U, 85U,
    138U, 252U, 54U, 240U, 108U, 161U, 246U, 239U, 119U, 151U, 133U, 173U, 186U, 104U, 219U, 39U,
    164U, 9U, 133U, 159U, 196U, 196U, 160U
  };

static uint8_t
sigver_vectors256_low1[32U] =
  {
    135U, 248U, 242U, 178U, 24U, 244U, 152U, 69U, 246U, 241U, 14U, 236U, 56U, 119U, 19U, 98U, 105U,
    245U, 193U, 165U, 71U, 54U, 219U, 223U, 105U, 248U, 153U, 64U, 202U, 212U, 21U, 85U
  };

static uint8_t
sigver_vectors256_low2[32U] =
  {
    225U, 95U, 54U, 144U, 54U, 244U, 152U, 66U, 250U, 199U, 168U, 108U, 138U, 43U, 5U, 87U, 96U,
    151U, 118U, 129U, 68U, 72U, 184U, 245U, 232U, 74U, 169U, 244U, 57U, 82U, 5U, 233U
  };

static uint8_t
sigver_vectors256_low3[32U] =
  {
    209U, 159U, 244U, 139U, 50U, 73U, 21U, 87U, 100U, 22U, 9U, 125U, 37U, 68U, 247U, 203U, 223U,
    135U, 104U, 177U, 69U, 74U, 210U, 14U, 11U, 170U, 197U, 14U, 33U, 31U, 35U, 176U
  };

static uint8_t
sigver_vectors256_low4[32U] =
  {
    163U, 232U, 30U, 89U, 49U, 28U, 223U, 255U, 45U, 71U, 132U, 148U, 159U, 122U, 44U, 181U, 11U,
    166U, 195U, 169U, 31U, 165U, 71U, 16U, 86U, 142U, 97U, 172U, 163U, 232U, 71U, 198U
  };

static uint8_t
sigver_vectors256_low5[128U] =
  {
    6U, 154U, 110U, 107U, 147U, 223U, 238U, 109U, 246U, 239U, 105U, 151U, 205U, 128U, 221U, 33U,
    130U, 195U, 102U, 83U, 206U, 241U, 12U, 101U, 93U, 82U, 69U, 133U, 101U, 84U, 98U, 214U, 131U,
    135U, 127U, 149U, 236U, 198U, 214U, 200U, 22U, 35U, 216U, 250U, 196U, 233U, 0U, 237U, 0U, 25U,
    150U, 64U, 148U, 231U, 222U, 145U, 241U, 72U, 25U, 137U, 174U, 24U, 115U, 0U, 69U, 101U, 120U,
    156U, 191U, 93U, 197U, 108U, 98U, 174U, 220U, 99U, 246U, 47U, 59U, 137U, 76U, 156U, 111U, 119U,
    136U, 200U, 236U, 170U, 220U, 155U, 208U, 232U, 26U, 217U, 27U, 43U, 53U, 105U, 234U, 18U, 38U,
    14U, 147U, 146U, 79U, 221U, 221U, 57U, 114U, 175U, 82U, 115U, 25U, 143U, 94U, 253U, 160U, 116U,
    98U, 25U, 71U, 80U, 23U, 85U, 118U, 22U, 23U, 14U
  };

static uint8_t
sigver_vectors256_low6[32U] =
  {
    92U, 240U, 42U, 0U, 210U, 5U, 189U, 254U, 226U, 1U, 111U, 116U, 33U, 128U, 127U, 195U, 138U,
    230U, 158U, 107U, 124U, 205U, 6U, 78U, 230U, 137U, 252U, 26U, 148U, 169U, 247U, 210U
  };

static uint8_t
sigver_vectors256_low7[32U] =
  {
    236U, 83U, 12U, 227U, 204U, 92U, 157U, 26U, 244U, 99U, 242U, 100U, 214U, 133U, 175U, 226U, 180U,
    219U, 75U, 88U, 40U, 215U, 230U, 27U, 116U, 137U, 48U, 243U, 206U, 98U, 42U, 133U
  };

static uint8_t
sigver_vectors256_low8[32U] =
  {
    220U, 35U, 209U, 48U, 198U, 17U, 127U, 181U, 117U, 18U, 1U, 69U, 94U, 153U, 243U, 111U, 89U,
    171U, 161U, 166U, 162U, 28U, 242U, 208U, 231U, 72U, 26U, 151U, 69U, 29U, 102U, 147U
  };

static uint8_t
sigver_vectors256_low9[32U] =
  {
    214U, 206U, 119U, 8U, 193U, 141U, 191U, 53U, 212U, 248U, 170U, 114U, 64U, 146U, 45U, 198U, 130U,
    63U, 46U, 112U, 88U, 203U, 193U, 72U, 79U, 202U, 209U, 89U, 157U, 181U, 1U, 140U
  };

static uint8_t
sigver_vectors256_low10[128U] =
  {
    223U, 4U, 163U, 70U, 207U, 77U, 14U, 51U, 26U, 109U, 183U, 140U, 202U, 45U, 69U, 109U, 49U,
    176U, 160U, 0U, 170U, 81U, 68U, 29U, 239U, 219U, 151U, 187U, 235U, 32U, 185U, 77U, 141U, 116U,
    100U, 41U, 163U, 147U, 186U, 136U, 132U, 13U, 102U, 22U, 21U, 224U, 125U, 239U, 97U, 90U, 52U,
    42U, 190U, 223U, 164U, 206U, 145U, 46U, 86U, 42U, 247U, 20U, 149U, 152U, 150U, 133U, 138U, 248U,
    23U, 49U, 122U, 132U, 13U, 207U, 248U, 90U, 5U, 123U, 185U, 26U, 60U, 43U, 249U, 1U, 5U, 80U,
    3U, 98U, 117U, 74U, 109U, 211U, 33U, 205U, 216U, 97U, 40U, 207U, 197U, 240U, 70U, 103U, 181U,
    122U, 167U, 140U, 17U, 36U, 17U, 228U, 45U, 163U, 4U, 241U, 1U, 45U, 72U, 205U, 106U, 112U, 82U,
    215U, 222U, 68U, 235U, 204U, 1U, 222U
  };

static uint8_t
sigver_vectors256_low11[32U] =
  {
    45U, 223U, 209U, 69U, 118U, 120U, 131U, 255U, 187U, 10U, 192U, 3U, 171U, 74U, 68U, 52U, 109U,
    8U, 250U, 37U, 112U, 179U, 18U, 13U, 204U, 233U, 69U, 98U, 66U, 34U, 68U, 203U
  };

static uint8_t
sigver_vectors256_low12[32U] =
  {
    95U, 112U, 199U, 209U, 26U, 194U, 183U, 164U, 53U, 204U, 251U, 186U, 224U, 44U, 61U, 241U, 234U,
    107U, 83U, 44U, 192U, 233U, 219U, 116U, 249U, 63U, 255U, 202U, 124U, 111U, 154U, 100U
  };

static uint8_t
sigver_vectors256_low13[32U] =
  {
    153U, 19U, 17U, 28U, 255U, 111U, 32U, 197U, 191U, 69U, 58U, 153U, 205U, 44U, 32U, 25U, 164U,
    231U, 73U, 164U, 151U, 36U, 160U, 135U, 116U, 209U, 78U, 76U, 17U, 62U, 221U, 168U
  };

static uint8_t
sigver_vectors256_low14[32U] =
  {
    148U, 103U, 205U, 76U, 210U, 30U, 203U, 86U, 176U, 202U, 176U, 169U, 164U, 83U, 180U, 51U, 134U,
    132U, 84U, 89U, 18U, 122U, 149U, 36U, 33U, 245U, 198U, 56U, 40U, 102U, 197U, 204U
  };

static uint8_t
sigver_vectors256_low15[128U] =
  {
    225U, 19U, 10U, 246U, 163U, 140U, 203U, 65U, 42U, 156U, 141U, 19U, 225U, 93U, 191U, 201U, 230U,
    154U, 22U, 56U, 90U, 243U, 195U, 241U, 229U, 218U, 149U, 79U, 213U, 231U, 196U, 95U, 215U, 94U,
    43U, 140U, 54U, 105U, 146U, 40U, 233U, 40U, 64U, 192U, 86U, 47U, 191U, 55U, 114U, 240U, 126U,
    23U, 241U, 173U, 213U, 101U, 136U, 221U, 69U, 247U, 69U, 14U, 18U, 23U, 173U, 35U, 153U, 34U,
    221U, 156U, 50U, 105U, 93U, 199U, 31U, 242U, 66U, 76U, 160U, 222U, 193U, 50U, 26U, 164U, 112U,
    100U, 160U, 68U, 183U, 254U, 60U, 43U, 151U, 208U, 60U, 228U, 112U, 165U, 146U, 48U, 76U, 94U,
    242U, 30U, 237U, 159U, 147U, 218U, 86U, 187U, 35U, 45U, 30U, 235U, 0U, 53U, 249U, 191U, 13U,
    250U, 253U, 204U, 70U, 6U, 39U, 43U, 32U, 163U
  };

static uint8_t
sigver_vectors256_low16[32U] =
  {
    228U, 36U, 220U, 97U, 212U, 187U, 60U, 183U, 239U, 67U, 68U, 167U, 248U, 149U, 122U, 12U, 81U,
    52U, 225U, 111U, 122U, 103U, 192U, 116U, 248U, 46U, 110U, 18U, 244U, 154U, 191U, 60U
  };

static uint8_t
sigver_vectors256_low17[32U] =
  {
    151U, 14U, 237U, 122U, 162U, 188U, 72U, 101U, 21U, 69U, 148U, 157U, 225U, 221U, 218U, 240U, 18U,
    126U, 89U, 101U, 172U, 133U, 209U, 36U, 61U, 111U, 96U, 231U, 223U, 174U, 233U, 39U
  };

static uint8_t
sigver_vectors256_low18[32U] =
  {
    191U, 150U, 185U, 154U, 164U, 156U, 112U, 92U, 145U, 11U, 227U, 49U, 66U, 1U, 124U, 100U, 47U,
    245U, 64U, 199U, 99U, 73U, 185U, 218U, 183U, 47U, 152U, 31U, 217U, 52U, 127U, 79U
  };

static uint8_t
sigver_vectors256_low19[32U] =
  {
    23U, 197U, 80U, 149U, 129U, 144U, 137U, 194U, 224U, 59U, 156U, 212U, 21U, 171U, 223U, 18U, 68U,
    78U, 50U, 48U, 117U, 217U, 143U, 49U, 146U, 11U, 158U, 15U, 87U, 236U, 135U, 28U
  };

static uint8_t
sigver_vectors256_low20[128U] =
  {
    115U, 197U, 246U, 166U, 116U, 86U, 174U, 72U, 32U, 155U, 95U, 133U, 209U, 231U, 222U, 119U, 88U,
    191U, 35U, 83U, 0U, 198U, 174U, 43U, 220U, 235U, 29U, 203U, 39U, 167U, 115U, 15U, 182U, 140U,
    149U, 11U, 127U, 202U, 218U, 14U, 204U, 70U, 97U, 211U, 87U, 130U, 48U, 242U, 37U, 168U, 117U,
    230U, 154U, 170U, 23U, 241U, 231U, 28U, 107U, 229U, 200U, 49U, 242U, 38U, 99U, 186U, 198U, 61U,
    12U, 122U, 150U, 53U, 237U, 176U, 4U, 63U, 248U, 198U, 242U, 100U, 112U, 240U, 42U, 123U, 197U,
    101U, 86U, 241U, 67U, 127U, 6U, 223U, 162U, 123U, 72U, 122U, 108U, 66U, 144U, 216U, 186U, 211U,
    141U, 72U, 121U, 179U, 52U, 227U, 65U, 186U, 9U, 45U, 222U, 78U, 74U, 230U, 148U, 169U, 192U,
    147U, 2U, 226U, 219U, 244U, 67U, 88U, 28U, 8U
  };

static uint8_t
sigver_vectors256_low21[32U] =
  {
    224U, 252U, 106U, 111U, 80U, 225U, 197U, 116U, 117U, 103U, 62U, 229U, 78U, 58U, 87U, 249U, 164U,
    159U, 51U, 40U, 231U, 67U, 191U, 82U, 243U, 53U, 227U, 238U, 170U, 61U, 40U, 100U
  };

static uint8_t
sigver_vectors256_low22[32U] =
  {
    127U, 89U, 214U, 137U, 201U, 30U, 70U, 54U, 7U, 217U, 25U, 77U, 153U, 250U, 243U, 22U, 226U,
    84U, 50U, 135U, 8U, 22U, 221U, 230U, 63U, 93U, 75U, 55U, 63U, 18U, 242U, 42U
  };

static uint8_t
sigver_vectors256_low23[32U] =
  {
    29U, 117U, 131U, 12U, 211U, 111U, 76U, 154U, 161U, 129U, 178U, 196U, 34U, 30U, 135U, 241U, 118U,
    183U, 240U, 91U, 124U, 135U, 130U, 78U, 130U, 227U, 150U, 200U, 131U, 21U, 196U, 7U
  };

static uint8_t
sigver_vectors256_low24[32U] =
  {
    203U, 42U, 203U, 1U, 218U, 201U, 110U, 252U, 83U, 163U, 45U, 74U, 13U, 133U, 208U, 194U, 228U,
    137U, 85U, 33U, 71U, 131U, 236U, 245U, 10U, 79U, 4U, 20U, 163U, 25U, 192U, 90U
  };

static uint8_t
sigver_vectors256_low25[128U] =
  {
    102U, 96U, 54U, 217U, 180U, 162U, 66U, 110U, 214U, 88U, 90U, 78U, 15U, 217U, 49U, 168U, 118U,
    20U, 81U, 210U, 154U, 176U, 75U, 215U, 220U, 109U, 12U, 91U, 158U, 56U, 230U, 194U, 178U, 99U,
    255U, 108U, 184U, 55U, 189U, 4U, 57U, 157U, 227U, 215U, 87U, 198U, 199U, 0U, 95U, 109U, 122U,
    152U, 112U, 99U, 207U, 109U, 126U, 140U, 179U, 138U, 75U, 240U, 215U, 74U, 40U, 37U, 114U, 189U,
    1U, 208U, 244U, 30U, 63U, 208U, 102U, 227U, 2U, 21U, 117U, 240U, 250U, 4U, 242U, 123U, 112U,
    13U, 91U, 125U, 221U, 223U, 80U, 150U, 89U, 147U, 195U, 249U, 199U, 17U, 142U, 215U, 136U, 136U,
    218U, 124U, 178U, 33U, 132U, 155U, 50U, 96U, 89U, 43U, 142U, 99U, 45U, 124U, 81U, 233U, 53U,
    160U, 206U, 174U, 21U, 32U, 123U, 237U, 213U, 72U
  };

static uint8_t
sigver_vectors256_low26[32U] =
  {
    168U, 73U, 190U, 245U, 117U, 202U, 195U, 198U, 146U, 15U, 188U, 230U, 117U, 195U, 183U, 135U,
    19U, 98U, 9U, 248U, 85U, 222U, 25U, 255U, 226U, 232U, 210U, 155U, 49U, 165U, 173U, 134U
  };

static uint8_t
sigver_vectors256_low27[32U] =
  {
    191U, 95U, 228U, 247U, 133U, 143U, 155U, 128U, 91U, 216U, 220U, 192U, 90U, 213U, 231U, 251U,
    136U, 157U, 226U, 248U, 34U, 243U, 216U, 180U, 22U, 148U, 230U, 197U, 92U, 22U, 180U, 113U
  };

static uint8_t
sigver_vectors256_low28[32U] =
  {
    37U, 172U, 195U, 170U, 157U, 158U, 132U, 199U, 171U, 240U, 143U, 115U, 250U, 65U, 149U, 172U,
    197U, 6U, 73U, 29U, 111U, 195U, 124U, 185U, 7U, 69U, 40U, 167U, 219U, 135U, 185U, 214U
  };

static uint8_t
sigver_vectors256_low29[32U] =
  {
    155U, 33U, 213U, 181U, 37U, 158U, 211U, 242U, 239U, 7U, 223U, 236U, 108U, 201U, 13U, 58U, 55U,
    133U, 93U, 28U, 225U, 34U, 168U, 91U, 166U, 163U, 51U, 243U, 7U, 211U, 21U, 55U
  };

static uint8_t
sigver_vectors256_low30[128U] =
  {
    126U, 128U, 67U, 107U, 206U, 87U, 51U, 156U, 232U, 218U, 27U, 86U, 96U, 20U, 154U, 32U, 36U,
    11U, 20U, 109U, 16U, 141U, 238U, 243U, 236U, 93U, 164U, 174U, 37U, 111U, 143U, 137U, 78U, 220U,
    187U, 197U, 123U, 52U, 206U, 55U, 8U, 156U, 13U, 170U, 23U, 240U, 196U, 108U, 216U, 43U, 90U,
    21U, 153U, 49U, 79U, 215U, 157U, 47U, 210U, 244U, 70U, 189U, 90U, 37U, 184U, 227U, 47U, 207U,
    5U, 183U, 109U, 100U, 69U, 115U, 166U, 223U, 74U, 209U, 223U, 234U, 112U, 123U, 71U, 157U, 151U,
    35U, 122U, 52U, 111U, 30U, 198U, 50U, 234U, 86U, 96U, 239U, 181U, 126U, 135U, 23U, 168U, 98U,
    141U, 127U, 130U, 175U, 80U, 164U, 232U, 75U, 17U, 242U, 27U, 223U, 246U, 131U, 145U, 150U,
    168U, 128U, 174U, 32U, 178U, 160U, 145U, 141U, 88U, 205U
  };

static uint8_t
sigver_vectors256_low31[32U] =
  {
    61U, 251U, 111U, 64U, 242U, 71U, 27U, 41U, 183U, 127U, 220U, 203U, 167U, 45U, 55U, 194U, 27U,
    186U, 1U, 158U, 250U, 64U, 193U, 200U, 249U, 30U, 196U, 5U, 215U, 220U, 197U, 223U
  };

static uint8_t
sigver_vectors256_low32[32U] =
  {
    242U, 47U, 149U, 63U, 30U, 57U, 90U, 82U, 234U, 215U, 243U, 174U, 63U, 196U, 116U, 81U, 180U,
    56U, 17U, 123U, 30U, 4U, 214U, 19U, 188U, 133U, 85U, 183U, 214U, 230U, 209U, 187U
  };

static uint8_t
sigver_vectors256_low33[32U] =
  {
    84U, 136U, 134U, 39U, 142U, 94U, 194U, 107U, 237U, 129U, 29U, 187U, 114U, 219U, 30U, 21U, 75U,
    111U, 23U, 190U, 112U, 222U, 177U, 178U, 16U, 16U, 125U, 236U, 177U, 236U, 42U, 90U
  };

static uint8_t
sigver_vectors256_low34[32U] =
  {
    233U, 59U, 254U, 189U, 47U, 20U, 243U, 216U, 39U, 202U, 50U, 180U, 100U, 190U, 110U, 105U, 24U,
    127U, 94U, 219U, 213U, 45U, 239U, 79U, 150U, 89U, 156U, 55U, 213U, 142U, 238U, 117U
  };

static uint8_t
sigver_vectors256_low35[128U] =
  {
    22U, 105U, 191U, 182U, 87U, 253U, 198U, 44U, 61U, 221U, 99U, 38U, 151U, 135U, 252U, 28U, 150U,
    159U, 24U, 80U, 251U, 4U, 201U, 51U, 221U, 160U, 99U, 239U, 116U, 165U, 108U, 225U, 62U, 58U,
    100U, 151U, 0U, 130U, 15U, 0U, 97U, 239U, 171U, 248U, 73U, 168U, 93U, 71U, 67U, 38U, 200U, 165U,
    65U, 217U, 152U, 48U, 238U, 168U, 19U, 30U, 174U, 165U, 132U, 242U, 45U, 136U, 195U, 83U, 150U,
    93U, 171U, 205U, 196U, 191U, 107U, 85U, 148U, 159U, 213U, 41U, 80U, 125U, 251U, 128U, 58U, 182U,
    180U, 128U, 205U, 115U, 202U, 11U, 160U, 12U, 161U, 156U, 67U, 136U, 73U, 226U, 206U, 162U, 98U,
    161U, 197U, 125U, 143U, 129U, 205U, 37U, 127U, 181U, 142U, 25U, 222U, 199U, 144U, 77U, 169U,
    125U, 131U, 134U, 232U, 123U, 132U, 148U, 129U, 105U
  };

static uint8_t
sigver_vectors256_low36[32U] =
  {
    105U, 183U, 102U, 112U, 86U, 225U, 225U, 29U, 108U, 175U, 110U, 69U, 100U, 63U, 139U, 33U, 231U,
    164U, 190U, 189U, 164U, 99U, 199U, 253U, 188U, 19U, 188U, 152U, 239U, 189U, 2U, 20U
  };

static uint8_t
sigver_vectors256_low37[32U] =
  {
    211U, 249U, 177U, 46U, 180U, 108U, 124U, 111U, 218U, 13U, 163U, 252U, 133U, 188U, 31U, 216U,
    49U, 85U, 127U, 154U, 188U, 144U, 42U, 59U, 227U, 203U, 62U, 139U, 231U, 209U, 170U, 47U
  };

static uint8_t
sigver_vectors256_low38[32U] =
  {
    40U, 143U, 122U, 28U, 211U, 145U, 132U, 44U, 206U, 33U, 240U, 14U, 111U, 21U, 71U, 28U, 4U,
    220U, 24U, 47U, 228U, 177U, 77U, 146U, 220U, 24U, 145U, 8U, 121U, 121U, 151U, 144U
  };

static uint8_t
sigver_vectors256_low39[32U] =
  {
    36U, 123U, 60U, 78U, 137U, 163U, 188U, 173U, 254U, 167U, 60U, 123U, 253U, 54U, 29U, 239U, 67U,
    113U, 95U, 163U, 130U, 184U, 195U, 237U, 244U, 174U, 21U, 214U, 229U, 94U, 153U, 121U
  };

static uint8_t
sigver_vectors256_low40[128U] =
  {
    63U, 230U, 13U, 217U, 173U, 108U, 172U, 207U, 90U, 111U, 88U, 59U, 58U, 230U, 89U, 83U, 86U,
    52U, 70U, 196U, 81U, 11U, 112U, 218U, 17U, 95U, 250U, 160U, 186U, 4U, 192U, 118U, 17U, 92U,
    112U, 67U, 171U, 135U, 51U, 64U, 60U, 214U, 156U, 125U, 20U, 194U, 18U, 198U, 85U, 192U, 123U,
    67U, 167U, 199U, 27U, 154U, 76U, 255U, 226U, 44U, 38U, 132U, 120U, 142U, 198U, 135U, 13U, 194U,
    1U, 63U, 38U, 145U, 114U, 200U, 34U, 37U, 111U, 158U, 124U, 198U, 116U, 121U, 27U, 242U, 216U,
    72U, 108U, 15U, 86U, 132U, 40U, 62U, 22U, 73U, 87U, 110U, 252U, 152U, 46U, 222U, 23U, 199U,
    183U, 75U, 33U, 71U, 84U, 215U, 4U, 2U, 251U, 75U, 180U, 90U, 208U, 134U, 207U, 44U, 247U, 107U,
    61U, 99U, 247U, 252U, 227U, 154U, 201U, 112U
  };

static uint8_t
sigver_vectors256_low41[32U] =
  {
    191U, 2U, 203U, 207U, 109U, 140U, 194U, 110U, 145U, 118U, 109U, 138U, 240U, 177U, 100U, 252U,
    89U, 104U, 83U, 94U, 132U, 193U, 88U, 235U, 59U, 196U, 226U, 215U, 156U, 60U, 198U, 130U
  };

static uint8_t
sigver_vectors256_low42[32U] =
  {
    6U, 155U, 166U, 203U, 6U, 180U, 157U, 96U, 129U, 32U, 102U, 175U, 161U, 110U, 207U, 123U, 81U,
    53U, 47U, 44U, 3U, 189U, 147U, 236U, 34U, 8U, 34U, 177U, 243U, 223U, 186U, 3U
  };

static uint8_t
sigver_vectors256_low43[32U] =
  {
    245U, 172U, 176U, 108U, 89U, 194U, 180U, 146U, 127U, 184U, 82U, 250U, 160U, 127U, 175U, 75U,
    24U, 82U, 187U, 181U, 208U, 104U, 64U, 147U, 94U, 132U, 156U, 77U, 41U, 61U, 27U, 173U
  };

static uint8_t
sigver_vectors256_low44[32U] =
  {
    4U, 157U, 171U, 121U, 200U, 156U, 192U, 47U, 20U, 132U, 196U, 55U, 245U, 35U, 224U, 128U, 167U,
    95U, 19U, 73U, 23U, 253U, 167U, 82U, 242U, 213U, 202U, 57U, 122U, 221U, 254U, 93U
  };

static uint8_t
sigver_vectors256_low45[128U] =
  {
    152U, 58U, 113U, 185U, 153U, 77U, 149U, 232U, 118U, 216U, 77U, 40U, 148U, 106U, 4U, 31U, 143U,
    10U, 63U, 84U, 76U, 252U, 192U, 85U, 73U, 101U, 128U, 241U, 223U, 212U, 227U, 18U, 162U, 173U,
    65U, 143U, 230U, 157U, 188U, 97U, 219U, 35U, 12U, 192U, 192U, 237U, 151U, 227U, 96U, 171U, 171U,
    125U, 111U, 244U, 184U, 30U, 233U, 112U, 167U, 233U, 116U, 102U, 172U, 253U, 150U, 68U, 248U,
    40U, 255U, 236U, 83U, 138U, 188U, 56U, 61U, 14U, 146U, 50U, 109U, 28U, 136U, 197U, 94U, 31U,
    70U, 166U, 104U, 160U, 57U, 190U, 170U, 27U, 230U, 49U, 168U, 145U, 41U, 147U, 140U, 0U, 168U,
    26U, 58U, 228U, 109U, 74U, 236U, 191U, 151U, 7U, 247U, 100U, 219U, 172U, 206U, 163U, 239U, 118U,
    101U, 228U, 196U, 48U, 127U, 160U, 176U, 163U, 7U, 92U
  };

static uint8_t
sigver_vectors256_low46[32U] =
  {
    34U, 74U, 77U, 101U, 185U, 88U, 246U, 214U, 175U, 178U, 144U, 72U, 99U, 239U, 210U, 167U, 52U,
    179U, 23U, 152U, 136U, 72U, 1U, 252U, 171U, 90U, 89U, 15U, 77U, 109U, 169U, 222U
  };

static uint8_t
sigver_vectors256_low47[32U] =
  {
    23U, 141U, 81U, 253U, 218U, 218U, 98U, 128U, 111U, 9U, 122U, 166U, 21U, 211U, 59U, 143U, 36U,
    4U, 230U, 177U, 71U, 159U, 95U, 212U, 133U, 157U, 89U, 87U, 52U, 214U, 210U, 185U
  };

static uint8_t
sigver_vectors256_low48[32U] =
  {
    135U, 185U, 62U, 226U, 254U, 207U, 218U, 84U, 222U, 184U, 223U, 248U, 228U, 38U, 243U, 199U,
    44U, 136U, 100U, 153U, 31U, 142U, 194U, 179U, 32U, 91U, 179U, 180U, 22U, 222U, 147U, 210U
  };

static uint8_t
sigver_vectors256_low49[32U] =
  {
    64U, 68U, 162U, 77U, 248U, 91U, 224U, 204U, 118U, 242U, 26U, 68U, 48U, 183U, 91U, 142U, 119U,
    185U, 50U, 168U, 127U, 81U, 228U, 236U, 203U, 196U, 92U, 38U, 62U, 191U, 143U, 102U
  };

static uint8_t
sigver_vectors256_low50[128U] =
  {
    74U, 140U, 7U, 26U, 196U, 253U, 13U, 82U, 250U, 164U, 7U, 176U, 254U, 93U, 171U, 117U, 159U,
    115U, 148U, 165U, 131U, 33U, 39U, 242U, 163U, 73U, 143U, 52U, 170U, 194U, 135U, 51U, 158U, 4U,
    59U, 79U, 250U, 121U, 82U, 143U, 175U, 25U, 157U, 201U, 23U, 247U, 176U, 102U, 173U, 101U, 80U,
    93U, 171U, 14U, 17U, 230U, 148U, 133U, 21U, 5U, 44U, 226U, 12U, 253U, 184U, 146U, 255U, 184U,
    170U, 155U, 243U, 241U, 170U, 91U, 227U, 10U, 91U, 190U, 133U, 130U, 59U, 221U, 247U, 11U, 57U,
    253U, 126U, 189U, 74U, 147U, 162U, 247U, 84U, 114U, 193U, 212U, 246U, 6U, 36U, 122U, 152U, 33U,
    241U, 168U, 196U, 90U, 108U, 184U, 5U, 69U, 222U, 46U, 12U, 108U, 1U, 116U, 226U, 57U, 32U,
    136U, 199U, 84U, 233U, 200U, 68U, 62U, 181U, 175U
  };

static uint8_t
sigver_vectors256_low51[32U] =
  {
    67U, 105U, 28U, 119U, 149U, 165U, 126U, 173U, 140U, 92U, 104U, 83U, 111U, 233U, 52U, 83U, 141U,
    70U, 241U, 40U, 137U, 104U, 10U, 156U, 182U, 208U, 85U, 160U, 102U, 34U, 131U, 105U
  };

static uint8_t
sigver_vectors256_low52[32U] =
  {
    248U, 121U, 1U, 16U, 179U, 195U, 178U, 129U, 170U, 30U, 174U, 3U, 125U, 79U, 18U, 52U, 175U,
    245U, 135U, 217U, 3U, 217U, 59U, 163U, 175U, 34U, 92U, 39U, 221U, 201U, 204U, 172U
  };

static uint8_t
sigver_vectors256_low53[32U] =
  {
    138U, 205U, 98U, 232U, 194U, 98U, 250U, 80U, 221U, 152U, 64U, 72U, 9U, 105U, 244U, 239U, 112U,
    242U, 24U, 235U, 248U, 239U, 149U, 132U, 241U, 153U, 3U, 17U, 50U, 198U, 177U, 206U
  };

static uint8_t
sigver_vectors256_low54[32U] =
  {
    207U, 202U, 126U, 211U, 212U, 52U, 127U, 178U, 162U, 158U, 82U, 107U, 67U, 195U, 72U, 174U, 28U,
    230U, 198U, 13U, 68U, 243U, 25U, 27U, 109U, 142U, 163U, 162U, 217U, 201U, 33U, 84U
  };

static uint8_t
sigver_vectors256_low55[128U] =
  {
    10U, 58U, 18U, 195U, 8U, 76U, 134U, 93U, 175U, 29U, 48U, 44U, 120U, 33U, 93U, 57U, 191U, 224U,
    184U, 191U, 40U, 39U, 43U, 60U, 11U, 116U, 190U, 180U, 183U, 64U, 157U, 176U, 113U, 130U, 57U,
    222U, 112U, 7U, 133U, 88U, 21U, 20U, 50U, 28U, 100U, 64U, 164U, 187U, 174U, 164U, 199U, 111U,
    164U, 116U, 1U, 225U, 81U, 230U, 140U, 182U, 194U, 144U, 23U, 240U, 188U, 228U, 99U, 18U, 144U,
    175U, 94U, 165U, 226U, 191U, 62U, 215U, 66U, 174U, 17U, 11U, 4U, 173U, 232U, 58U, 93U, 189U,
    115U, 88U, 242U, 154U, 133U, 147U, 142U, 35U, 216U, 122U, 200U, 35U, 48U, 114U, 183U, 156U,
    148U, 103U, 15U, 240U, 149U, 159U, 156U, 127U, 69U, 23U, 134U, 47U, 248U, 41U, 69U, 32U, 150U,
    199U, 143U, 95U, 46U, 154U, 126U, 78U, 146U, 22U
  };

static uint8_t
sigver_vectors256_low56[32U] =
  {
    145U, 87U, 219U, 252U, 248U, 207U, 56U, 95U, 91U, 177U, 86U, 138U, 213U, 198U, 226U, 168U, 101U,
    43U, 166U, 223U, 198U, 59U, 193U, 117U, 62U, 223U, 82U, 104U, 203U, 126U, 181U, 150U
  };

static uint8_t
sigver_vectors256_low57[32U] =
  {
    151U, 37U, 112U, 244U, 49U, 61U, 71U, 252U, 150U, 247U, 192U, 45U, 85U, 148U, 215U, 125U, 70U,
    249U, 30U, 148U, 152U, 8U, 130U, 91U, 61U, 49U, 240U, 41U, 232U, 41U, 100U, 5U
  };

static uint8_t
sigver_vectors256_low58[32U] =
  {
    223U, 174U, 166U, 242U, 151U, 250U, 50U, 11U, 112U, 120U, 102U, 18U, 92U, 42U, 125U, 93U, 81U,
    91U, 81U, 165U, 3U, 190U, 232U, 23U, 222U, 159U, 170U, 52U, 60U, 196U, 142U, 235U
  };

static uint8_t
sigver_vectors256_low59[32U] =
  {
    143U, 120U, 10U, 215U, 19U, 249U, 195U, 229U, 164U, 247U, 250U, 76U, 81U, 152U, 51U, 223U, 239U,
    198U, 167U, 67U, 35U, 137U, 177U, 228U, 175U, 70U, 57U, 97U, 240U, 151U, 100U, 242U
  };

static uint8_t
sigver_vectors256_low60[128U] =
  {
    120U, 93U, 7U, 163U, 197U, 79U, 99U, 220U, 161U, 31U, 93U, 26U, 95U, 73U, 110U, 226U, 194U,
    249U, 40U, 142U, 85U, 0U, 126U, 102U, 108U, 120U, 176U, 7U, 217U, 92U, 194U, 133U, 129U, 220U,
    229U, 31U, 73U, 11U, 48U, 250U, 115U, 220U, 158U, 45U, 69U, 208U, 117U, 215U, 227U, 169U, 95U,
    184U, 169U, 225U, 70U, 90U, 209U, 145U, 144U, 65U, 36U, 22U, 11U, 124U, 96U, 250U, 114U, 14U,
    244U, 239U, 28U, 93U, 41U, 152U, 244U, 5U, 112U, 174U, 42U, 135U, 14U, 243U, 232U, 148U, 194U,
    188U, 97U, 125U, 138U, 29U, 200U, 92U, 60U, 85U, 119U, 73U, 40U, 195U, 135U, 137U, 180U, 230U,
    97U, 52U, 157U, 63U, 132U, 210U, 68U, 26U, 59U, 133U, 106U, 118U, 148U, 155U, 159U, 31U, 128U,
    188U, 22U, 22U, 72U, 161U, 202U, 213U, 88U, 142U
  };

static uint8_t
sigver_vectors256_low61[32U] =
  {
    7U, 43U, 16U, 192U, 129U, 164U, 193U, 113U, 58U, 41U, 79U, 36U, 138U, 239U, 133U, 14U, 41U,
    121U, 145U, 172U, 164U, 127U, 169U, 106U, 116U, 112U, 171U, 227U, 184U, 172U, 253U, 218U
  };

static uint8_t
sigver_vectors256_low62[32U] =
  {
    149U, 129U, 20U, 92U, 202U, 4U, 160U, 251U, 148U, 206U, 220U, 231U, 82U, 200U, 240U, 55U, 8U,
    97U, 145U, 109U, 42U, 148U, 231U, 198U, 71U, 197U, 55U, 60U, 230U, 164U, 200U, 245U
  };

static uint8_t
sigver_vectors256_low63[32U] =
  {
    9U, 245U, 72U, 62U, 204U, 236U, 128U, 249U, 209U, 4U, 129U, 90U, 27U, 233U, 204U, 26U, 142U,
    91U, 18U, 182U, 235U, 72U, 42U, 101U, 198U, 144U, 123U, 116U, 128U, 207U, 79U, 25U
  };

static uint8_t
sigver_vectors256_low64[32U] =
  {
    164U, 249U, 14U, 86U, 12U, 94U, 78U, 184U, 105U, 108U, 178U, 118U, 229U, 22U, 91U, 106U, 157U,
    72U, 99U, 69U, 222U, 223U, 176U, 148U, 167U, 110U, 132U, 66U, 208U, 38U, 55U, 141U
  };

static uint8_t
sigver_vectors256_low65[128U] =
  {
    118U, 249U, 135U, 236U, 84U, 72U, 221U, 114U, 33U, 155U, 211U, 11U, 246U, 182U, 107U, 7U, 117U,
    200U, 11U, 57U, 72U, 81U, 164U, 63U, 241U, 245U, 55U, 241U, 64U, 166U, 231U, 34U, 158U, 248U,
    205U, 114U, 173U, 88U, 177U, 210U, 210U, 2U, 152U, 83U, 157U, 99U, 71U, 221U, 85U, 152U, 129U,
    43U, 198U, 83U, 35U, 172U, 234U, 240U, 82U, 40U, 247U, 56U, 181U, 173U, 62U, 141U, 159U, 228U,
    16U, 15U, 215U, 103U, 194U, 240U, 152U, 199U, 124U, 185U, 156U, 41U, 146U, 132U, 59U, 163U,
    238U, 217U, 29U, 50U, 68U, 79U, 59U, 109U, 182U, 205U, 33U, 45U, 212U, 229U, 96U, 149U, 72U,
    244U, 187U, 98U, 129U, 42U, 146U, 15U, 110U, 43U, 241U, 88U, 27U, 225U, 235U, 238U, 189U, 208U,
    110U, 196U, 233U, 113U, 134U, 44U, 196U, 32U, 85U, 202U
  };

static uint8_t
sigver_vectors256_low66[32U] =
  {
    9U, 48U, 142U, 165U, 191U, 173U, 110U, 90U, 223U, 64U, 134U, 52U, 179U, 213U, 206U, 146U, 64U,
    211U, 84U, 66U, 247U, 254U, 17U, 100U, 82U, 170U, 236U, 13U, 37U, 190U, 140U, 36U
  };

static uint8_t
sigver_vectors256_low67[32U] =
  {
    244U, 12U, 147U, 224U, 35U, 239U, 73U, 75U, 28U, 48U, 121U, 178U, 209U, 14U, 246U, 127U, 49U,
    112U, 116U, 4U, 149U, 206U, 44U, 197U, 127U, 142U, 228U, 176U, 97U, 139U, 142U, 229U
  };

static uint8_t
sigver_vectors256_low68[32U] =
  {
    92U, 200U, 170U, 124U, 53U, 116U, 62U, 192U, 194U, 61U, 222U, 136U, 218U, 189U, 94U, 79U, 205U,
    1U, 146U, 210U, 17U, 111U, 105U, 38U, 254U, 247U, 136U, 205U, 219U, 117U, 78U, 115U
  };

static uint8_t
sigver_vectors256_low69[32U] =
  {
    156U, 156U, 4U, 94U, 186U, 161U, 184U, 40U, 195U, 47U, 130U, 172U, 224U, 209U, 141U, 174U, 191U,
    94U, 21U, 110U, 183U, 203U, 253U, 193U, 239U, 244U, 57U, 154U, 138U, 144U, 10U, 231U
  };

static uint8_t
sigver_vectors256_low70[128U] =
  {
    96U, 205U, 100U, 178U, 205U, 43U, 230U, 195U, 56U, 89U, 185U, 72U, 117U, 18U, 3U, 97U, 162U,
    64U, 133U, 243U, 118U, 92U, 184U, 178U, 191U, 17U, 224U, 38U, 250U, 157U, 136U, 85U, 219U, 228U,
    53U, 172U, 247U, 136U, 46U, 132U, 243U, 199U, 133U, 127U, 150U, 226U, 186U, 171U, 77U, 154U,
    254U, 69U, 136U, 228U, 168U, 46U, 23U, 167U, 136U, 39U, 191U, 219U, 93U, 219U, 209U, 194U, 17U,
    251U, 194U, 230U, 216U, 132U, 205U, 221U, 124U, 185U, 217U, 13U, 91U, 244U, 167U, 49U, 27U,
    131U, 243U, 82U, 80U, 128U, 51U, 129U, 44U, 119U, 106U, 14U, 0U, 192U, 3U, 199U, 224U, 214U,
    40U, 229U, 7U, 54U, 199U, 81U, 45U, 240U, 172U, 250U, 159U, 35U, 32U, 189U, 16U, 34U, 41U, 244U,
    100U, 149U, 174U, 109U, 8U, 87U, 204U, 69U, 42U, 132U
  };

static uint8_t
sigver_vectors256_low71[32U] =
  {
    45U, 152U, 234U, 1U, 247U, 84U, 211U, 75U, 188U, 48U, 3U, 223U, 80U, 80U, 32U, 10U, 191U, 68U,
    94U, 199U, 40U, 85U, 109U, 126U, 215U, 213U, 197U, 76U, 85U, 85U, 43U, 109U
  };

static uint8_t
sigver_vectors256_low72[32U] =
  {
    155U, 82U, 103U, 39U, 66U, 214U, 55U, 163U, 42U, 221U, 5U, 109U, 253U, 109U, 135U, 146U, 242U,
    163U, 60U, 46U, 105U, 218U, 250U, 190U, 160U, 155U, 150U, 11U, 198U, 30U, 35U, 10U
  };

static uint8_t
sigver_vectors256_low73[32U] =
  {
    6U, 16U, 142U, 82U, 95U, 132U, 93U, 1U, 85U, 191U, 96U, 25U, 50U, 34U, 179U, 33U, 156U, 152U,
    227U, 212U, 148U, 36U, 194U, 251U, 42U, 9U, 135U, 248U, 37U, 193U, 121U, 89U
  };

static uint8_t
sigver_vectors256_low74[32U] =
  {
    98U, 181U, 205U, 213U, 145U, 229U, 181U, 7U, 229U, 96U, 22U, 123U, 168U, 246U, 247U, 205U, 167U,
    70U, 115U, 235U, 49U, 86U, 128U, 203U, 137U, 204U, 188U, 78U, 236U, 71U, 125U, 206U
  };

typedef struct lbuffer__uint8_t_s
{
  uint32_t len;
  uint8_t *b;
}
lbuffer__uint8_t;

typedef struct
__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool_s
{
  lbuffer__uint8_t fst;
  lbuffer__uint8_t snd;
  lbuffer__uint8_t thd;
  lbuffer__uint8_t f3;
  lbuffer__uint8_t f4;
  bool f5;
}
__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool;

static __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors256_low75[15U] =
  {
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low0 },
        .snd = { .len = 32U, .b = sigver_vectors256_low1 },
        .thd = { .len = 32U, .b = sigver_vectors256_low2 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low3 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low4 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low5 },
        .snd = { .len = 32U, .b = sigver_vectors256_low6 },
        .thd = { .len = 32U, .b = sigver_vectors256_low7 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low8 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low9 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low10 },
        .snd = { .len = 32U, .b = sigver_vectors256_low11 },
        .thd = { .len = 32U, .b = sigver_vectors256_low12 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low13 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low14 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low15 },
        .snd = { .len = 32U, .b = sigver_vectors256_low16 },
        .thd = { .len = 32U, .b = sigver_vectors256_low17 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low18 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low19 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low20 },
        .snd = { .len = 32U, .b = sigver_vectors256_low21 },
        .thd = { .len = 32U, .b = sigver_vectors256_low22 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low23 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low24 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low25 },
        .snd = { .len = 32U, .b = sigver_vectors256_low26 },
        .thd = { .len = 32U, .b = sigver_vectors256_low27 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low28 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low29 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low30 },
        .snd = { .len = 32U, .b = sigver_vectors256_low31 },
        .thd = { .len = 32U, .b = sigver_vectors256_low32 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low33 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low34 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low35 },
        .snd = { .len = 32U, .b = sigver_vectors256_low36 },
        .thd = { .len = 32U, .b = sigver_vectors256_low37 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low38 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low39 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low40 },
        .snd = { .len = 32U, .b = sigver_vectors256_low41 },
        .thd = { .len = 32U, .b = sigver_vectors256_low42 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low43 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low44 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low45 },
        .snd = { .len = 32U, .b = sigver_vectors256_low46 },
        .thd = { .len = 32U, .b = sigver_vectors256_low47 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low48 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low49 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low50 },
        .snd = { .len = 32U, .b = sigver_vectors256_low51 },
        .thd = { .len = 32U, .b = sigver_vectors256_low52 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low53 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low54 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low55 },
        .snd = { .len = 32U, .b = sigver_vectors256_low56 },
        .thd = { .len = 32U, .b = sigver_vectors256_low57 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low58 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low59 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low60 },
        .snd = { .len = 32U, .b = sigver_vectors256_low61 },
        .thd = { .len = 32U, .b = sigver_vectors256_low62 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low63 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low64 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low65 },
        .snd = { .len = 32U, .b = sigver_vectors256_low66 },
        .thd = { .len = 32U, .b = sigver_vectors256_low67 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low68 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low69 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors256_low70 },
        .snd = { .len = 32U, .b = sigver_vectors256_low71 },
        .thd = { .len = 32U, .b = sigver_vectors256_low72 },
        .f3 = { .len = 32U, .b = sigver_vectors256_low73 },
        .f4 = { .len = 32U, .b = sigver_vectors256_low74 },
        .f5 = true
      }
    )
  };

typedef struct
lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool_s
{
  uint32_t len;
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  *b;
}
lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool;

static lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors256_low = { .len = 15U, .b = sigver_vectors256_low75 };

static uint8_t
sigver_vectors384_low0[128U] =
  {
    254U, 152U, 56U, 240U, 7U, 189U, 198U, 175U, 205U, 98U, 105U, 116U, 252U, 198U, 131U, 63U, 6U,
    182U, 253U, 151U, 4U, 39U, 185U, 98U, 215U, 92U, 42U, 234U, 219U, 239U, 56U, 107U, 236U, 141U,
    1U, 129U, 6U, 25U, 127U, 226U, 84U, 125U, 42U, 240U, 46U, 122U, 121U, 73U, 150U, 93U, 95U, 188U,
    76U, 93U, 185U, 9U, 169U, 91U, 152U, 88U, 66U, 106U, 51U, 192U, 128U, 176U, 178U, 93U, 174U,
    139U, 86U, 197U, 203U, 198U, 196U, 238U, 195U, 219U, 216U, 22U, 53U, 199U, 148U, 87U, 234U,
    239U, 79U, 171U, 57U, 230U, 98U, 161U, 208U, 91U, 36U, 129U, 237U, 168U, 193U, 7U, 74U, 226U,
    209U, 112U, 76U, 138U, 63U, 118U, 150U, 134U, 161U, 249U, 101U, 239U, 60U, 135U, 96U, 46U, 252U,
    40U, 140U, 127U, 159U, 248U, 205U, 94U, 34U, 164U
  };

static uint8_t
sigver_vectors384_low1[32U] =
  {
    64U, 222U, 209U, 61U, 187U, 231U, 44U, 98U, 156U, 56U, 240U, 127U, 127U, 149U, 207U, 117U, 165U,
    14U, 42U, 82U, 72U, 151U, 96U, 76U, 132U, 250U, 253U, 229U, 228U, 202U, 251U, 159U
  };

static uint8_t
sigver_vectors384_low2[32U] =
  {
    161U, 114U, 2U, 233U, 45U, 125U, 106U, 55U, 196U, 56U, 119U, 147U, 73U, 253U, 121U, 86U, 125U,
    117U, 164U, 14U, 242U, 43U, 125U, 9U, 202U, 33U, 204U, 244U, 174U, 201U, 166U, 108U
  };

static uint8_t
sigver_vectors384_low3[32U] =
  {
    190U, 52U, 115U, 12U, 49U, 115U, 11U, 78U, 65U, 46U, 108U, 82U, 194U, 62U, 219U, 211U, 101U,
    131U, 172U, 226U, 16U, 43U, 57U, 175U, 161U, 29U, 36U, 182U, 132U, 140U, 183U, 127U
  };

static uint8_t
sigver_vectors384_low4[32U] =
  {
    3U, 101U, 82U, 2U, 213U, 253U, 140U, 158U, 58U, 233U, 113U, 182U, 240U, 128U, 100U, 12U, 64U,
    97U, 18U, 253U, 149U, 231U, 1U, 88U, 116U, 233U, 182U, 238U, 119U, 117U, 43U, 16U
  };

static uint8_t
sigver_vectors384_low5[128U] =
  {
    182U, 144U, 67U, 185U, 179U, 49U, 218U, 57U, 43U, 93U, 214U, 137U, 20U, 45U, 252U, 114U, 50U,
    66U, 101U, 218U, 8U, 241U, 74U, 188U, 237U, 240U, 58U, 216U, 38U, 62U, 107U, 220U, 203U, 199U,
    80U, 152U, 162U, 112U, 11U, 187U, 161U, 151U, 157U, 232U, 76U, 143U, 18U, 137U, 26U, 160U, 208U,
    0U, 248U, 161U, 171U, 173U, 125U, 222U, 73U, 129U, 83U, 63U, 33U, 218U, 89U, 204U, 128U, 217U,
    207U, 148U, 81U, 127U, 59U, 97U, 209U, 167U, 217U, 238U, 203U, 47U, 207U, 5U, 46U, 31U, 201U,
    231U, 24U, 140U, 3U, 27U, 134U, 48U, 94U, 74U, 67U, 106U, 55U, 148U, 128U, 113U, 240U, 70U,
    227U, 6U, 190U, 251U, 133U, 17U, 220U, 3U, 165U, 61U, 200U, 118U, 154U, 144U, 168U, 110U, 155U,
    79U, 219U, 240U, 93U, 205U, 250U, 53U, 171U, 115U
  };

static uint8_t
sigver_vectors384_low6[32U] =
  {
    31U, 128U, 225U, 159U, 254U, 181U, 29U, 215U, 79U, 28U, 57U, 122U, 195U, 223U, 211U, 65U, 90U,
    177U, 110U, 189U, 8U, 71U, 237U, 17U, 158U, 108U, 59U, 21U, 161U, 168U, 132U, 184U
  };

static uint8_t
sigver_vectors384_low7[32U] =
  {
    155U, 57U, 87U, 135U, 55U, 29U, 191U, 181U, 93U, 19U, 71U, 215U, 190U, 209U, 194U, 97U, 210U,
    144U, 129U, 33U, 251U, 120U, 222U, 29U, 27U, 242U, 208U, 6U, 102U, 166U, 42U, 237U
  };

static uint8_t
sigver_vectors384_low8[32U] =
  {
    36U, 156U, 162U, 195U, 235U, 110U, 4U, 172U, 87U, 51U, 76U, 47U, 117U, 220U, 94U, 101U, 139U,
    187U, 72U, 91U, 241U, 135U, 16U, 7U, 116U, 245U, 9U, 157U, 209U, 62U, 247U, 7U
  };

static uint8_t
sigver_vectors384_low9[32U] =
  {
    151U, 54U, 58U, 5U, 32U, 43U, 96U, 45U, 19U, 22U, 99U, 70U, 105U, 78U, 56U, 19U, 91U, 188U,
    224U, 37U, 190U, 148U, 149U, 14U, 146U, 51U, 244U, 200U, 1U, 59U, 245U, 191U
  };

static uint8_t
sigver_vectors384_low10[128U] =
  {
    210U, 252U, 170U, 237U, 232U, 184U, 121U, 192U, 100U, 176U, 170U, 70U, 230U, 142U, 252U, 39U,
    138U, 70U, 155U, 128U, 167U, 247U, 225U, 147U, 158U, 194U, 235U, 201U, 108U, 118U, 32U, 111U,
    35U, 57U, 89U, 103U, 39U, 156U, 24U, 31U, 234U, 21U, 126U, 187U, 121U, 223U, 173U, 198U, 142U,
    49U, 52U, 95U, 7U, 241U, 51U, 5U, 200U, 13U, 224U, 216U, 94U, 67U, 48U, 211U, 164U, 95U, 149U,
    124U, 92U, 37U, 38U, 185U, 69U, 131U, 140U, 229U, 169U, 194U, 132U, 75U, 107U, 42U, 102U, 92U,
    15U, 112U, 183U, 72U, 177U, 33U, 58U, 140U, 242U, 11U, 165U, 219U, 223U, 140U, 171U, 35U, 31U,
    67U, 61U, 165U, 34U, 16U, 74U, 92U, 208U, 39U, 211U, 227U, 107U, 179U, 115U, 196U, 237U, 64U,
    77U, 154U, 240U, 203U, 236U, 111U, 133U, 236U, 33U, 147U
  };

static uint8_t
sigver_vectors384_low11[32U] =
  {
    206U, 77U, 207U, 167U, 56U, 76U, 131U, 68U, 58U, 206U, 15U, 184U, 44U, 74U, 193U, 173U, 250U,
    16U, 10U, 155U, 44U, 123U, 240U, 159U, 9U, 63U, 139U, 109U, 8U, 78U, 80U, 194U
  };

static uint8_t
sigver_vectors384_low12[32U] =
  {
    217U, 138U, 231U, 185U, 26U, 190U, 230U, 72U, 208U, 191U, 222U, 25U, 39U, 3U, 116U, 26U, 194U,
    29U, 170U, 215U, 38U, 42U, 244U, 24U, 181U, 14U, 64U, 109U, 130U, 94U, 176U, 214U
  };

static uint8_t
sigver_vectors384_low13[32U] =
  {
    89U, 126U, 30U, 4U, 217U, 58U, 107U, 68U, 76U, 204U, 68U, 122U, 72U, 101U, 31U, 23U, 101U, 127U,
    244U, 63U, 182U, 95U, 233U, 68U, 97U, 210U, 191U, 129U, 107U, 1U, 175U, 64U
  };

static uint8_t
sigver_vectors384_low14[32U] =
  {
    53U, 159U, 227U, 129U, 121U, 99U, 84U, 142U, 103U, 109U, 109U, 163U, 76U, 45U, 8U, 102U, 170U,
    66U, 73U, 146U, 55U, 182U, 130U, 0U, 40U, 137U, 234U, 248U, 137U, 56U, 20U, 210U
  };

static uint8_t
sigver_vectors384_low15[128U] =
  {
    6U, 205U, 134U, 72U, 24U, 101U, 24U, 28U, 239U, 122U, 205U, 195U, 32U, 40U, 36U, 151U, 14U,
    194U, 217U, 118U, 98U, 181U, 25U, 196U, 181U, 136U, 220U, 158U, 81U, 97U, 124U, 6U, 130U, 130U,
    177U, 161U, 26U, 21U, 191U, 126U, 252U, 72U, 88U, 162U, 243U, 122U, 61U, 116U, 176U, 95U, 181U,
    121U, 14U, 182U, 131U, 56U, 200U, 0U, 155U, 77U, 169U, 180U, 39U, 5U, 20U, 211U, 135U, 162U,
    224U, 22U, 169U, 158U, 225U, 9U, 132U, 30U, 136U, 74U, 121U, 9U, 80U, 78U, 243U, 26U, 84U, 84U,
    226U, 20U, 102U, 63U, 131U, 15U, 35U, 165U, 167U, 111U, 145U, 64U, 47U, 202U, 95U, 93U, 97U,
    105U, 159U, 168U, 116U, 89U, 123U, 219U, 251U, 30U, 207U, 248U, 240U, 125U, 219U, 208U, 126U,
    246U, 30U, 151U, 208U, 213U, 38U, 46U, 243U, 20U
  };

static uint8_t
sigver_vectors384_low16[32U] =
  {
    27U, 103U, 127U, 83U, 90U, 198U, 157U, 26U, 205U, 69U, 146U, 192U, 209U, 47U, 172U, 19U, 201U,
    19U, 30U, 90U, 111U, 138U, 180U, 249U, 208U, 175U, 220U, 179U, 163U, 243U, 39U, 224U
  };

static uint8_t
sigver_vectors384_low17[32U] =
  {
    93U, 202U, 44U, 115U, 236U, 137U, 229U, 142U, 248U, 38U, 124U, 186U, 43U, 181U, 235U, 15U, 85U,
    31U, 65U, 47U, 157U, 192U, 135U, 193U, 166U, 148U, 79U, 12U, 228U, 117U, 39U, 122U
  };

static uint8_t
sigver_vectors384_low18[32U] =
  {
    223U, 11U, 12U, 215U, 109U, 37U, 85U, 212U, 195U, 139U, 61U, 112U, 191U, 223U, 150U, 72U, 132U,
    208U, 190U, 235U, 159U, 116U, 56U, 95U, 8U, 147U, 232U, 125U, 32U, 201U, 100U, 45U
  };

static uint8_t
sigver_vectors384_low19[32U] =
  {
    18U, 130U, 153U, 170U, 191U, 31U, 84U, 150U, 17U, 43U, 225U, 254U, 4U, 54U, 95U, 95U, 130U, 21U,
    176U, 138U, 4U, 10U, 189U, 254U, 202U, 70U, 38U, 244U, 209U, 92U, 0U, 91U
  };

static uint8_t
sigver_vectors384_low20[128U] =
  {
    89U, 173U, 41U, 115U, 151U, 243U, 80U, 54U, 4U, 164U, 162U, 208U, 152U, 164U, 240U, 10U, 54U,
    138U, 217U, 92U, 97U, 1U, 179U, 211U, 143U, 157U, 73U, 217U, 8U, 119U, 108U, 90U, 108U, 134U,
    84U, 176U, 6U, 173U, 183U, 147U, 159U, 251U, 108U, 48U, 175U, 163U, 37U, 181U, 65U, 133U, 216U,
    44U, 60U, 192U, 216U, 54U, 133U, 13U, 206U, 84U, 211U, 64U, 139U, 37U, 124U, 58U, 150U, 29U,
    17U, 250U, 254U, 43U, 116U, 186U, 139U, 221U, 252U, 17U, 2U, 250U, 101U, 109U, 16U, 40U, 186U,
    249U, 76U, 56U, 52U, 12U, 38U, 161U, 30U, 153U, 42U, 171U, 113U, 206U, 55U, 50U, 39U, 27U, 118U,
    115U, 88U, 103U, 27U, 37U, 34U, 89U, 38U, 243U, 164U, 185U, 236U, 95U, 130U, 192U, 89U, 240U,
    199U, 209U, 68U, 109U, 93U, 158U, 66U, 81U
  };

static uint8_t
sigver_vectors384_low21[32U] =
  {
    127U, 252U, 40U, 83U, 243U, 225U, 120U, 135U, 221U, 161U, 59U, 14U, 180U, 63U, 24U, 60U, 229U,
    10U, 90U, 192U, 248U, 187U, 167U, 95U, 177U, 146U, 17U, 114U, 72U, 79U, 155U, 148U
  };

static uint8_t
sigver_vectors384_low22[32U] =
  {
    76U, 197U, 35U, 209U, 65U, 146U, 248U, 11U, 213U, 178U, 125U, 48U, 179U, 180U, 30U, 6U, 77U,
    168U, 123U, 251U, 174U, 21U, 87U, 45U, 211U, 130U, 185U, 161U, 118U, 193U, 35U, 162U
  };

static uint8_t
sigver_vectors384_low23[32U] =
  {
    49U, 86U, 23U, 109U, 82U, 235U, 38U, 249U, 57U, 18U, 41U, 222U, 66U, 81U, 153U, 58U, 65U, 184U,
    23U, 47U, 120U, 151U, 11U, 183U, 14U, 50U, 162U, 69U, 190U, 75U, 182U, 83U
  };

static uint8_t
sigver_vectors384_low24[32U] =
  {
    98U, 130U, 122U, 41U, 225U, 45U, 47U, 41U, 176U, 15U, 178U, 208U, 45U, 213U, 242U, 213U, 65U,
    46U, 23U, 164U, 69U, 95U, 68U, 49U, 165U, 201U, 150U, 136U, 31U, 223U, 192U, 238U
  };

static uint8_t
sigver_vectors384_low25[128U] =
  {
    130U, 21U, 218U, 202U, 135U, 230U, 137U, 162U, 3U, 146U, 100U, 106U, 101U, 17U, 187U, 123U, 90U,
    130U, 210U, 217U, 149U, 202U, 157U, 232U, 155U, 217U, 217U, 192U, 177U, 20U, 100U, 183U, 203U,
    30U, 78U, 154U, 49U, 227U, 224U, 26U, 216U, 194U, 205U, 97U, 61U, 90U, 44U, 180U, 74U, 42U,
    141U, 246U, 137U, 159U, 206U, 76U, 40U, 45U, 234U, 30U, 65U, 175U, 13U, 246U, 195U, 107U, 225U,
    243U, 32U, 3U, 101U, 103U, 248U, 208U, 211U, 42U, 170U, 121U, 201U, 95U, 229U, 59U, 22U, 102U,
    143U, 126U, 26U, 158U, 93U, 125U, 3U, 158U, 162U, 96U, 253U, 3U, 113U, 27U, 125U, 28U, 23U,
    115U, 85U, 252U, 82U, 36U, 77U, 73U, 202U, 91U, 35U, 133U, 86U, 165U, 84U, 19U, 73U, 1U, 70U,
    131U, 203U, 125U, 163U, 38U, 244U, 67U, 183U, 82U
  };

static uint8_t
sigver_vectors384_low26[32U] =
  {
    85U, 105U, 247U, 109U, 201U, 66U, 67U, 205U, 232U, 25U, 251U, 111U, 200U, 81U, 68U, 236U, 103U,
    226U, 181U, 212U, 149U, 57U, 246U, 46U, 36U, 212U, 6U, 209U, 182U, 143U, 0U, 88U
  };

static uint8_t
sigver_vectors384_low27[32U] =
  {
    18U, 8U, 195U, 141U, 190U, 37U, 135U, 13U, 234U, 181U, 60U, 72U, 111U, 121U, 58U, 30U, 37U, 12U,
    157U, 27U, 142U, 124U, 20U, 126U, 166U, 139U, 113U, 25U, 108U, 68U, 7U, 48U
  };

static uint8_t
sigver_vectors384_low28[32U] =
  {
    112U, 111U, 43U, 164U, 2U, 94U, 124U, 6U, 182U, 109U, 99U, 105U, 163U, 249U, 59U, 47U, 236U,
    70U, 197U, 30U, 206U, 255U, 66U, 161U, 88U, 247U, 67U, 25U, 25U, 80U, 108U, 251U
  };

static uint8_t
sigver_vectors384_low29[32U] =
  {
    180U, 231U, 90U, 195U, 74U, 150U, 57U, 50U, 55U, 252U, 67U, 55U, 120U, 158U, 55U, 22U, 141U,
    121U, 56U, 39U, 5U, 178U, 72U, 5U, 28U, 156U, 114U, 188U, 186U, 197U, 245U, 22U
  };

static uint8_t
sigver_vectors384_low30[128U] =
  {
    169U, 150U, 177U, 251U, 128U, 15U, 105U, 37U, 23U, 162U, 235U, 128U, 232U, 55U, 35U, 49U, 147U,
    221U, 62U, 130U, 72U, 77U, 63U, 73U, 189U, 25U, 238U, 13U, 184U, 247U, 180U, 64U, 135U, 107U,
    7U, 227U, 132U, 201U, 10U, 168U, 185U, 247U, 182U, 96U, 60U, 160U, 181U, 164U, 224U, 108U, 29U,
    160U, 237U, 185U, 116U, 162U, 251U, 155U, 110U, 124U, 114U, 13U, 223U, 62U, 92U, 14U, 49U, 76U,
    45U, 24U, 148U, 2U, 144U, 60U, 8U, 192U, 131U, 103U, 118U, 195U, 97U, 162U, 132U, 219U, 136U,
    126U, 188U, 195U, 62U, 97U, 93U, 233U, 114U, 11U, 1U, 218U, 218U, 222U, 88U, 94U, 239U, 104U,
    123U, 51U, 70U, 70U, 139U, 218U, 251U, 73U, 14U, 86U, 214U, 87U, 169U, 231U, 212U, 77U, 146U,
    1U, 64U, 105U, 0U, 90U, 54U, 193U, 207U, 99U
  };

static uint8_t
sigver_vectors384_low31[32U] =
  {
    228U, 180U, 112U, 198U, 91U, 44U, 4U, 219U, 6U, 13U, 113U, 5U, 236U, 105U, 17U, 88U, 152U, 99U,
    211U, 199U, 247U, 206U, 72U, 114U, 107U, 163U, 243U, 105U, 234U, 52U, 103U, 232U
  };

static uint8_t
sigver_vectors384_low32[32U] =
  {
    68U, 195U, 141U, 58U, 224U, 152U, 222U, 5U, 245U, 145U, 90U, 88U, 104U, 193U, 127U, 238U, 41U,
    106U, 110U, 21U, 11U, 235U, 31U, 0U, 13U, 245U, 243U, 190U, 200U, 252U, 69U, 50U
  };

static uint8_t
sigver_vectors384_low33[32U] =
  {
    201U, 195U, 71U, 238U, 87U, 23U, 228U, 199U, 89U, 221U, 175U, 9U, 232U, 111U, 78U, 29U, 178U,
    200U, 101U, 133U, 147U, 23U, 124U, 253U, 164U, 230U, 81U, 75U, 94U, 62U, 203U, 135U
  };

static uint8_t
sigver_vectors384_low34[32U] =
  {
    186U, 174U, 1U, 233U, 228U, 74U, 123U, 4U, 214U, 156U, 142U, 170U, 237U, 119U, 201U, 227U, 163U,
    108U, 232U, 150U, 47U, 149U, 204U, 80U, 160U, 219U, 20U, 107U, 78U, 73U, 235U, 64U
  };

static uint8_t
sigver_vectors384_low35[128U] =
  {
    26U, 110U, 73U, 163U, 119U, 160U, 142U, 153U, 35U, 83U, 214U, 172U, 197U, 87U, 182U, 135U, 177U,
    182U, 154U, 65U, 216U, 61U, 67U, 167U, 95U, 173U, 185U, 123U, 140U, 146U, 140U, 254U, 186U,
    222U, 186U, 175U, 153U, 234U, 127U, 177U, 49U, 72U, 128U, 127U, 86U, 234U, 23U, 56U, 74U, 121U,
    18U, 229U, 120U, 230U, 43U, 27U, 0U, 159U, 239U, 178U, 170U, 252U, 165U, 172U, 133U, 83U, 148U,
    51U, 97U, 155U, 40U, 111U, 16U, 100U, 58U, 86U, 248U, 223U, 164U, 123U, 164U, 208U, 28U, 2U,
    81U, 13U, 234U, 236U, 24U, 2U, 158U, 166U, 185U, 104U, 32U, 34U, 177U, 57U, 220U, 183U, 8U, 20U,
    22U, 76U, 76U, 144U, 236U, 113U, 122U, 217U, 217U, 37U, 72U, 83U, 152U, 83U, 28U, 221U, 89U,
    146U, 162U, 82U, 68U, 152U, 179U, 55U, 249U, 125U
  };

static uint8_t
sigver_vectors384_low36[32U] =
  {
    150U, 5U, 12U, 95U, 162U, 221U, 209U, 178U, 229U, 69U, 29U, 137U, 238U, 116U, 160U, 183U, 181U,
    67U, 71U, 54U, 77U, 220U, 2U, 49U, 113U, 90U, 110U, 241U, 20U, 111U, 232U, 220U
  };

static uint8_t
sigver_vectors384_low37[32U] =
  {
    224U, 136U, 138U, 158U, 120U, 174U, 234U, 135U, 246U, 225U, 233U, 0U, 43U, 38U, 81U, 22U, 159U,
    54U, 196U, 238U, 83U, 1U, 60U, 252U, 140U, 153U, 18U, 183U, 253U, 80U, 72U, 88U
  };

static uint8_t
sigver_vectors384_low38[32U] =
  {
    35U, 83U, 214U, 205U, 60U, 33U, 184U, 234U, 125U, 188U, 28U, 217U, 64U, 81U, 152U, 18U, 219U,
    227U, 101U, 163U, 177U, 92U, 214U, 174U, 187U, 169U, 209U, 28U, 242U, 105U, 134U, 122U
  };

static uint8_t
sigver_vectors384_low39[32U] =
  {
    133U, 245U, 96U, 39U, 60U, 217U, 232U, 46U, 104U, 1U, 228U, 203U, 28U, 140U, 210U, 156U, 218U,
    195U, 74U, 2U, 13U, 162U, 17U, 215U, 116U, 83U, 117U, 107U, 96U, 75U, 143U, 167U
  };

static uint8_t
sigver_vectors384_low40[128U] =
  {
    62U, 20U, 247U, 55U, 201U, 19U, 147U, 27U, 200U, 39U, 100U, 235U, 196U, 64U, 177U, 46U, 60U,
    225U, 255U, 224U, 248U, 88U, 199U, 184U, 241U, 203U, 211U, 15U, 187U, 177U, 100U, 79U, 165U,
    155U, 225U, 210U, 204U, 165U, 246U, 74U, 109U, 125U, 197U, 237U, 92U, 68U, 32U, 243U, 146U, 39U,
    81U, 106U, 232U, 235U, 48U, 25U, 239U, 134U, 39U, 77U, 14U, 77U, 6U, 205U, 231U, 191U, 94U, 92U,
    65U, 50U, 67U, 223U, 196U, 33U, 217U, 241U, 65U, 118U, 33U, 9U, 129U, 14U, 107U, 106U, 69U, 30U,
    235U, 75U, 216U, 212U, 190U, 31U, 241U, 17U, 66U, 109U, 126U, 68U, 208U, 169U, 22U, 180U, 254U,
    61U, 179U, 89U, 77U, 141U, 208U, 26U, 233U, 15U, 238U, 207U, 143U, 30U, 35U, 11U, 87U, 65U,
    128U, 205U, 11U, 141U, 67U, 163U, 211U, 59U
  };

static uint8_t
sigver_vectors384_low41[32U] =
  {
    12U, 7U, 187U, 121U, 244U, 64U, 18U, 41U, 159U, 191U, 213U, 160U, 243U, 19U, 151U, 170U, 247U,
    215U, 87U, 248U, 163U, 132U, 55U, 64U, 124U, 27U, 9U, 39U, 28U, 101U, 81U, 160U
  };

static uint8_t
sigver_vectors384_low42[32U] =
  {
    132U, 254U, 120U, 70U, 213U, 212U, 3U, 220U, 146U, 192U, 9U, 31U, 189U, 57U, 243U, 197U, 203U,
    202U, 63U, 148U, 193U, 11U, 92U, 174U, 68U, 226U, 233U, 101U, 98U, 19U, 27U, 19U
  };

static uint8_t
sigver_vectors384_low43[32U] =
  {
    73U, 233U, 66U, 95U, 130U, 208U, 168U, 197U, 3U, 0U, 156U, 234U, 210U, 78U, 18U, 173U, 201U,
    212U, 138U, 8U, 89U, 64U, 148U, 202U, 79U, 109U, 19U, 173U, 30U, 60U, 87U, 29U
  };

static uint8_t
sigver_vectors384_low44[32U] =
  {
    31U, 27U, 112U, 170U, 163U, 10U, 143U, 246U, 57U, 170U, 9U, 53U, 148U, 78U, 155U, 136U, 50U,
    106U, 33U, 58U, 184U, 252U, 229U, 25U, 76U, 26U, 157U, 236U, 7U, 14U, 180U, 51U
  };

static uint8_t
sigver_vectors384_low45[128U] =
  {
    64U, 0U, 16U, 97U, 39U, 167U, 39U, 70U, 219U, 119U, 149U, 124U, 188U, 107U, 253U, 132U, 174U,
    61U, 29U, 99U, 184U, 25U, 0U, 135U, 99U, 126U, 147U, 104U, 152U, 65U, 51U, 30U, 42U, 220U, 25U,
    48U, 214U, 223U, 67U, 2U, 147U, 95U, 69U, 32U, 187U, 238U, 81U, 53U, 5U, 205U, 207U, 202U, 153U,
    235U, 198U, 248U, 58U, 247U, 178U, 59U, 15U, 46U, 127U, 125U, 239U, 186U, 97U, 64U, 34U, 206U,
    234U, 233U, 198U, 136U, 110U, 139U, 19U, 247U, 234U, 37U, 58U, 48U, 122U, 195U, 1U, 243U, 83U,
    103U, 32U, 203U, 227U, 222U, 130U, 186U, 62U, 152U, 49U, 3U, 97U, 182U, 24U, 1U, 168U, 48U, 79U,
    252U, 145U, 255U, 119U, 73U, 72U, 227U, 49U, 118U, 221U, 205U, 223U, 27U, 118U, 67U, 123U, 63U,
    2U, 201U, 16U, 87U, 141U, 70U
  };

static uint8_t
sigver_vectors384_low46[32U] =
  {
    113U, 219U, 29U, 225U, 161U, 243U, 143U, 53U, 108U, 145U, 254U, 175U, 245U, 207U, 227U, 149U,
    209U, 165U, 185U, 210U, 60U, 246U, 170U, 25U, 243U, 138U, 224U, 188U, 201U, 10U, 72U, 109U
  };

static uint8_t
sigver_vectors384_low47[32U] =
  {
    236U, 221U, 111U, 251U, 23U, 74U, 80U, 241U, 204U, 121U, 41U, 133U, 194U, 249U, 96U, 140U, 57U,
    156U, 152U, 184U, 166U, 74U, 105U, 210U, 181U, 183U, 205U, 217U, 36U, 31U, 103U, 226U
  };

static uint8_t
sigver_vectors384_low48[32U] =
  {
    176U, 68U, 59U, 51U, 166U, 242U, 73U, 71U, 13U, 47U, 148U, 54U, 117U, 0U, 157U, 33U, 185U, 204U,
    190U, 173U, 21U, 37U, 174U, 87U, 129U, 93U, 248U, 107U, 178U, 4U, 112U, 191U
  };

static uint8_t
sigver_vectors384_low49[32U] =
  {
    49U, 109U, 190U, 226U, 125U, 153U, 142U, 9U, 18U, 133U, 57U, 194U, 105U, 226U, 151U, 172U, 143U,
    52U, 185U, 239U, 130U, 73U, 160U, 97U, 145U, 104U, 195U, 73U, 92U, 92U, 17U, 152U
  };

static uint8_t
sigver_vectors384_low50[128U] =
  {
    180U, 46U, 84U, 125U, 14U, 125U, 221U, 94U, 16U, 105U, 187U, 45U, 21U, 138U, 91U, 77U, 93U,
    156U, 67U, 16U, 148U, 42U, 27U, 253U, 9U, 73U, 3U, 17U, 166U, 230U, 132U, 189U, 60U, 41U, 176U,
    220U, 239U, 134U, 169U, 120U, 139U, 75U, 38U, 254U, 215U, 134U, 63U, 61U, 94U, 84U, 57U, 121U,
    107U, 91U, 95U, 254U, 122U, 162U, 84U, 93U, 15U, 81U, 138U, 208U, 32U, 104U, 156U, 162U, 18U,
    48U, 243U, 165U, 158U, 127U, 140U, 202U, 70U, 95U, 226U, 29U, 245U, 17U, 231U, 141U, 33U, 95U,
    168U, 5U, 245U, 240U, 248U, 137U, 56U, 233U, 209U, 152U, 81U, 94U, 107U, 156U, 129U, 153U, 48U,
    117U, 92U, 108U, 106U, 234U, 81U, 20U, 205U, 41U, 4U, 96U, 114U, 67U, 5U, 28U, 9U, 221U, 122U,
    20U, 119U, 86U, 203U, 194U, 4U, 165U
  };

static uint8_t
sigver_vectors384_low51[32U] =
  {
    130U, 25U, 178U, 37U, 170U, 21U, 71U, 34U, 98U, 198U, 72U, 202U, 200U, 222U, 154U, 173U, 65U,
    115U, 209U, 122U, 35U, 27U, 162U, 67U, 82U, 165U, 161U, 196U, 238U, 167U, 15U, 173U
  };

static uint8_t
sigver_vectors384_low52[32U] =
  {
    15U, 238U, 43U, 8U, 173U, 57U, 251U, 240U, 219U, 0U, 22U, 239U, 40U, 150U, 202U, 153U, 173U,
    192U, 126U, 252U, 140U, 65U, 95U, 100U, 15U, 55U, 32U, 73U, 139U, 226U, 96U, 55U
  };

static uint8_t
sigver_vectors384_low53[32U] =
  {
    19U, 79U, 182U, 137U, 16U, 26U, 170U, 211U, 149U, 77U, 226U, 129U, 157U, 159U, 189U, 18U, 7U,
    47U, 226U, 188U, 54U, 244U, 150U, 187U, 240U, 209U, 63U, 167U, 33U, 20U, 171U, 150U
  };

static uint8_t
sigver_vectors384_low54[32U] =
  {
    230U, 92U, 35U, 43U, 217U, 21U, 181U, 158U, 8U, 126U, 127U, 213U, 236U, 144U, 191U, 99U, 108U,
    250U, 128U, 82U, 99U, 69U, 199U, 154U, 10U, 223U, 215U, 80U, 3U, 4U, 93U, 111U
  };

static uint8_t
sigver_vectors384_low55[128U] =
  {
    170U, 86U, 50U, 35U, 167U, 213U, 32U, 31U, 235U, 223U, 19U, 202U, 184U, 10U, 3U, 220U, 230U, 7U,
    124U, 38U, 231U, 81U, 188U, 152U, 169U, 65U, 25U, 106U, 40U, 132U, 138U, 188U, 73U, 94U, 3U,
    36U, 1U, 60U, 154U, 32U, 148U, 251U, 21U, 220U, 101U, 209U, 0U, 195U, 232U, 161U, 54U, 165U,
    44U, 23U, 128U, 179U, 149U, 244U, 37U, 136U, 144U, 11U, 100U, 27U, 109U, 67U, 97U, 67U, 46U,
    33U, 115U, 25U, 90U, 47U, 96U, 24U, 159U, 63U, 204U, 133U, 244U, 233U, 101U, 156U, 174U, 82U,
    87U, 111U, 32U, 209U, 133U, 45U, 67U, 194U, 180U, 0U, 222U, 234U, 49U, 68U, 200U, 232U, 112U,
    225U, 144U, 109U, 103U, 116U, 37U, 216U, 200U, 80U, 55U, 199U, 164U, 42U, 157U, 36U, 155U, 45U,
    164U, 181U, 22U, 224U, 68U, 118U, 189U, 69U
  };

static uint8_t
sigver_vectors384_low56[32U] =
  {
    201U, 52U, 25U, 93U, 227U, 59U, 96U, 207U, 0U, 70U, 31U, 195U, 196U, 93U, 173U, 6U, 142U, 159U,
    95U, 122U, 245U, 199U, 250U, 120U, 89U, 30U, 149U, 174U, 176U, 78U, 38U, 23U
  };

static uint8_t
sigver_vectors384_low57[32U] =
  {
    181U, 136U, 221U, 95U, 153U, 101U, 253U, 170U, 82U, 59U, 71U, 92U, 40U, 18U, 194U, 81U, 188U,
    105U, 115U, 226U, 223U, 33U, 217U, 190U, 170U, 206U, 151U, 106U, 191U, 87U, 40U, 203U
  };

static uint8_t
sigver_vectors384_low58[32U] =
  {
    113U, 243U, 2U, 68U, 14U, 180U, 237U, 42U, 147U, 155U, 105U, 227U, 62U, 144U, 94U, 111U, 220U,
    84U, 92U, 116U, 52U, 88U, 211U, 143U, 126U, 26U, 29U, 69U, 110U, 53U, 243U, 137U
  };

static uint8_t
sigver_vectors384_low59[32U] =
  {
    84U, 234U, 160U, 235U, 156U, 215U, 80U, 59U, 25U, 169U, 101U, 143U, 10U, 4U, 149U, 93U, 159U,
    10U, 178U, 14U, 188U, 138U, 8U, 119U, 227U, 60U, 137U, 238U, 136U, 173U, 6U, 143U
  };

static uint8_t
sigver_vectors384_low60[128U] =
  {
    152U, 228U, 186U, 191U, 137U, 15U, 82U, 229U, 160U, 75U, 210U, 167U, 215U, 155U, 240U, 174U,
    154U, 113U, 150U, 120U, 71U, 52U, 125U, 135U, 242U, 159U, 179U, 153U, 116U, 84U, 199U, 60U,
    121U, 121U, 209U, 91U, 92U, 79U, 66U, 5U, 236U, 61U, 231U, 131U, 93U, 24U, 133U, 251U, 122U,
    188U, 248U, 220U, 222U, 148U, 186U, 240U, 139U, 29U, 105U, 26U, 12U, 116U, 132U, 83U, 23U, 40U,
    101U, 64U, 232U, 201U, 211U, 120U, 254U, 250U, 164U, 118U, 44U, 48U, 36U, 146U, 245U, 16U, 35U,
    192U, 215U, 173U, 187U, 28U, 201U, 11U, 123U, 3U, 53U, 241U, 18U, 3U, 102U, 78U, 113U, 254U,
    166U, 33U, 188U, 47U, 89U, 210U, 219U, 208U, 238U, 118U, 214U, 89U, 126U, 199U, 85U, 16U, 222U,
    89U, 182U, 210U, 95U, 166U, 117U, 10U, 113U, 197U, 148U, 53U
  };

static uint8_t
sigver_vectors384_low61[32U] =
  {
    158U, 26U, 220U, 212U, 142U, 46U, 63U, 14U, 76U, 33U, 53U, 1U, 128U, 130U, 40U, 229U, 135U,
    196U, 5U, 88U, 245U, 43U, 181U, 77U, 219U, 182U, 16U, 45U, 64U, 72U, 234U, 146U
  };

static uint8_t
sigver_vectors384_low62[32U] =
  {
    52U, 239U, 249U, 135U, 4U, 121U, 9U, 56U, 231U, 224U, 189U, 248U, 122U, 227U, 152U, 7U, 166U,
    183U, 125U, 253U, 201U, 236U, 223U, 230U, 221U, 15U, 36U, 26U, 186U, 225U, 174U, 178U
  };

static uint8_t
sigver_vectors384_low63[32U] =
  {
    206U, 79U, 13U, 116U, 128U, 82U, 44U, 141U, 209U, 176U, 45U, 208U, 235U, 56U, 47U, 34U, 64U,
    102U, 66U, 240U, 56U, 193U, 237U, 233U, 65U, 24U, 131U, 215U, 43U, 62U, 126U, 208U
  };

static uint8_t
sigver_vectors384_low64[32U] =
  {
    133U, 70U, 225U, 238U, 59U, 119U, 249U, 146U, 124U, 218U, 204U, 188U, 47U, 28U, 241U, 157U,
    107U, 85U, 118U, 176U, 247U, 56U, 187U, 27U, 134U, 160U, 198U, 107U, 57U, 202U, 86U, 251U
  };

static uint8_t
sigver_vectors384_low65[128U] =
  {
    187U, 107U, 3U, 173U, 96U, 214U, 221U, 191U, 12U, 77U, 23U, 36U, 98U, 6U, 230U, 28U, 136U, 111U,
    145U, 109U, 37U, 43U, 180U, 96U, 129U, 73U, 218U, 73U, 206U, 249U, 3U, 52U, 132U, 8U, 14U, 134U,
    31U, 145U, 187U, 36U, 0U, 186U, 160U, 205U, 108U, 93U, 144U, 194U, 242U, 117U, 226U, 250U, 188U,
    18U, 216U, 56U, 71U, 247U, 161U, 195U, 255U, 14U, 180U, 12U, 138U, 61U, 216U, 61U, 7U, 209U,
    148U, 186U, 55U, 151U, 210U, 114U, 56U, 65U, 90U, 47U, 53U, 141U, 114U, 146U, 161U, 153U, 26U,
    246U, 135U, 188U, 185U, 119U, 72U, 105U, 128U, 249U, 19U, 139U, 49U, 64U, 50U, 20U, 133U, 99U,
    138U, 199U, 189U, 34U, 236U, 218U, 0U, 255U, 229U, 0U, 155U, 131U, 185U, 3U, 151U, 239U, 242U,
    78U, 207U, 34U, 197U, 73U, 93U, 103U
  };

static uint8_t
sigver_vectors384_low66[32U] =
  {
    147U, 237U, 190U, 203U, 11U, 1U, 156U, 44U, 192U, 48U, 96U, 245U, 76U, 180U, 144U, 75U, 146U,
    15U, 219U, 52U, 235U, 131U, 186U, 221U, 117U, 43U, 233U, 68U, 48U, 54U, 174U, 19U
  };

static uint8_t
sigver_vectors384_low67[32U] =
  {
    180U, 148U, 233U, 41U, 94U, 8U, 10U, 144U, 128U, 254U, 126U, 115U, 36U, 155U, 58U, 89U, 4U,
    170U, 132U, 225U, 192U, 40U, 18U, 30U, 236U, 211U, 226U, 207U, 26U, 85U, 245U, 152U
  };

static uint8_t
sigver_vectors384_low68[32U] =
  {
    238U, 194U, 152U, 109U, 71U, 183U, 25U, 149U, 137U, 43U, 9U, 21U, 211U, 213U, 190U, 204U, 77U,
    203U, 42U, 181U, 82U, 6U, 215U, 114U, 224U, 24U, 149U, 65U, 178U, 24U, 77U, 223U
  };

static uint8_t
sigver_vectors384_low69[32U] =
  {
    138U, 108U, 30U, 222U, 182U, 69U, 38U, 39U, 173U, 39U, 200U, 49U, 149U, 153U, 197U, 74U, 196U,
    76U, 221U, 131U, 30U, 166U, 111U, 19U, 244U, 157U, 144U, 175U, 254U, 106U, 212U, 91U
  };

static uint8_t
sigver_vectors384_low70[128U] =
  {
    51U, 165U, 212U, 137U, 246U, 113U, 243U, 150U, 199U, 118U, 188U, 26U, 207U, 25U, 59U, 201U,
    167U, 67U, 6U, 244U, 105U, 45U, 216U, 224U, 91U, 205U, 254U, 40U, 253U, 239U, 189U, 92U, 9U,
    184U, 49U, 194U, 4U, 161U, 222U, 200U, 29U, 142U, 53U, 65U, 243U, 36U, 247U, 180U, 116U, 214U,
    146U, 120U, 144U, 19U, 187U, 30U, 202U, 6U, 111U, 130U, 251U, 243U, 241U, 207U, 59U, 166U, 78U,
    157U, 137U, 99U, 233U, 236U, 193U, 128U, 185U, 37U, 25U, 25U, 226U, 232U, 161U, 171U, 5U, 132U,
    122U, 13U, 118U, 255U, 103U, 164U, 124U, 0U, 225U, 112U, 227U, 142U, 91U, 49U, 154U, 86U, 245U,
    156U, 197U, 16U, 56U, 249U, 9U, 97U, 234U, 39U, 169U, 167U, 235U, 41U, 42U, 10U, 26U, 162U,
    244U, 151U, 37U, 104U, 102U, 146U, 70U, 144U, 122U, 53U
  };

static uint8_t
sigver_vectors384_low71[32U] =
  {
    50U, 5U, 186U, 232U, 118U, 249U, 189U, 80U, 176U, 113U, 57U, 89U, 231U, 36U, 87U, 22U, 94U,
    130U, 108U, 187U, 227U, 137U, 93U, 103U, 50U, 9U, 9U, 218U, 164U, 139U, 14U, 188U
  };

static uint8_t
sigver_vectors384_low72[32U] =
  {
    209U, 89U, 37U, 98U, 39U, 62U, 94U, 15U, 87U, 187U, 251U, 146U, 206U, 221U, 154U, 247U, 241U,
    51U, 37U, 86U, 132U, 238U, 5U, 10U, 249U, 182U, 240U, 32U, 25U, 187U, 202U, 250U
  };

static uint8_t
sigver_vectors384_low73[32U] =
  {
    1U, 36U, 243U, 241U, 198U, 30U, 196U, 88U, 86U, 26U, 78U, 170U, 108U, 21U, 91U, 210U, 158U, 89U,
    112U, 61U, 20U, 85U, 99U, 36U, 146U, 70U, 131U, 219U, 58U, 76U, 244U, 59U
  };

static uint8_t
sigver_vectors384_low74[32U] =
  {
    104U, 138U, 92U, 95U, 192U, 199U, 186U, 146U, 33U, 12U, 80U, 204U, 229U, 181U, 18U, 164U, 104U,
    168U, 128U, 224U, 90U, 204U, 33U, 202U, 86U, 87U, 29U, 137U, 244U, 95U, 96U, 58U
  };

static __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors384_low75[15U] =
  {
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low0 },
        .snd = { .len = 32U, .b = sigver_vectors384_low1 },
        .thd = { .len = 32U, .b = sigver_vectors384_low2 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low3 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low4 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low5 },
        .snd = { .len = 32U, .b = sigver_vectors384_low6 },
        .thd = { .len = 32U, .b = sigver_vectors384_low7 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low8 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low9 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low10 },
        .snd = { .len = 32U, .b = sigver_vectors384_low11 },
        .thd = { .len = 32U, .b = sigver_vectors384_low12 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low13 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low14 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low15 },
        .snd = { .len = 32U, .b = sigver_vectors384_low16 },
        .thd = { .len = 32U, .b = sigver_vectors384_low17 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low18 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low19 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low20 },
        .snd = { .len = 32U, .b = sigver_vectors384_low21 },
        .thd = { .len = 32U, .b = sigver_vectors384_low22 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low23 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low24 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low25 },
        .snd = { .len = 32U, .b = sigver_vectors384_low26 },
        .thd = { .len = 32U, .b = sigver_vectors384_low27 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low28 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low29 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low30 },
        .snd = { .len = 32U, .b = sigver_vectors384_low31 },
        .thd = { .len = 32U, .b = sigver_vectors384_low32 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low33 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low34 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low35 },
        .snd = { .len = 32U, .b = sigver_vectors384_low36 },
        .thd = { .len = 32U, .b = sigver_vectors384_low37 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low38 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low39 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low40 },
        .snd = { .len = 32U, .b = sigver_vectors384_low41 },
        .thd = { .len = 32U, .b = sigver_vectors384_low42 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low43 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low44 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low45 },
        .snd = { .len = 32U, .b = sigver_vectors384_low46 },
        .thd = { .len = 32U, .b = sigver_vectors384_low47 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low48 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low49 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low50 },
        .snd = { .len = 32U, .b = sigver_vectors384_low51 },
        .thd = { .len = 32U, .b = sigver_vectors384_low52 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low53 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low54 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low55 },
        .snd = { .len = 32U, .b = sigver_vectors384_low56 },
        .thd = { .len = 32U, .b = sigver_vectors384_low57 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low58 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low59 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low60 },
        .snd = { .len = 32U, .b = sigver_vectors384_low61 },
        .thd = { .len = 32U, .b = sigver_vectors384_low62 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low63 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low64 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low65 },
        .snd = { .len = 32U, .b = sigver_vectors384_low66 },
        .thd = { .len = 32U, .b = sigver_vectors384_low67 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low68 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low69 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors384_low70 },
        .snd = { .len = 32U, .b = sigver_vectors384_low71 },
        .thd = { .len = 32U, .b = sigver_vectors384_low72 },
        .f3 = { .len = 32U, .b = sigver_vectors384_low73 },
        .f4 = { .len = 32U, .b = sigver_vectors384_low74 },
        .f5 = false
      }
    )
  };

static lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors384_low = { .len = 15U, .b = sigver_vectors384_low75 };

static uint8_t
sigver_vectors512_low0[128U] =
  {
    39U, 59U, 6U, 50U, 36U, 171U, 72U, 161U, 191U, 108U, 126U, 252U, 147U, 66U, 157U, 31U, 137U,
    222U, 72U, 252U, 74U, 79U, 163U, 255U, 231U, 164U, 158U, 187U, 161U, 165U, 143U, 245U, 210U, 8U,
    169U, 228U, 191U, 242U, 123U, 65U, 130U, 82U, 82U, 98U, 67U, 186U, 4U, 45U, 22U, 5U, 182U, 223U,
    60U, 46U, 201U, 22U, 206U, 239U, 2U, 120U, 83U, 164U, 17U, 55U, 247U, 191U, 182U, 252U, 99U,
    132U, 77U, 233U, 95U, 88U, 232U, 43U, 154U, 210U, 86U, 95U, 19U, 103U, 210U, 198U, 155U, 210U,
    145U, 0U, 246U, 219U, 33U, 168U, 171U, 122U, 181U, 138U, 255U, 209U, 102U, 26U, 221U, 3U, 34U,
    189U, 145U, 87U, 33U, 55U, 141U, 249U, 250U, 35U, 62U, 240U, 183U, 224U, 160U, 168U, 91U, 227U,
    22U, 137U, 226U, 24U, 145U, 236U, 137U, 119U
  };

static uint8_t
sigver_vectors512_low1[32U] =
  {
    72U, 78U, 49U, 230U, 158U, 247U, 11U, 184U, 82U, 120U, 83U, 194U, 44U, 107U, 107U, 76U, 210U,
    165U, 19U, 17U, 221U, 230U, 108U, 123U, 99U, 240U, 151U, 219U, 182U, 171U, 39U, 191U
  };

static uint8_t
sigver_vectors512_low2[32U] =
  {
    225U, 255U, 129U, 119U, 244U, 6U, 29U, 79U, 187U, 172U, 187U, 199U, 5U, 25U, 240U, 252U, 140U,
    139U, 96U, 83U, 215U, 42U, 240U, 254U, 79U, 4U, 141U, 97U, 80U, 4U, 247U, 78U
  };

static uint8_t
sigver_vectors512_low3[32U] =
  {
    145U, 163U, 3U, 216U, 254U, 58U, 180U, 23U, 96U, 112U, 246U, 64U, 98U, 103U, 246U, 183U, 155U,
    254U, 94U, 181U, 246U, 42U, 230U, 174U, 179U, 116U, 217U, 6U, 103U, 133U, 133U, 24U
  };

static uint8_t
sigver_vectors512_low4[32U] =
  {
    225U, 82U, 17U, 156U, 239U, 162U, 104U, 38U, 234U, 7U, 236U, 64U, 164U, 40U, 134U, 145U, 50U,
    215U, 8U, 18U, 197U, 87U, 140U, 90U, 38U, 14U, 72U, 214U, 128U, 14U, 4U, 106U
  };

static uint8_t
sigver_vectors512_low5[128U] =
  {
    214U, 78U, 161U, 167U, 104U, 176U, 222U, 41U, 171U, 1U, 138U, 233U, 59U, 170U, 100U, 93U, 7U,
    140U, 112U, 162U, 247U, 170U, 74U, 205U, 74U, 231U, 82U, 101U, 56U, 235U, 213U, 246U, 151U,
    161U, 25U, 39U, 207U, 208U, 221U, 201U, 24U, 124U, 9U, 95U, 20U, 173U, 48U, 84U, 76U, 182U, 62U,
    222U, 147U, 83U, 175U, 139U, 35U, 193U, 140U, 226U, 40U, 67U, 136U, 31U, 226U, 215U, 189U, 231U,
    72U, 252U, 105U, 8U, 89U, 33U, 103U, 120U, 88U, 216U, 125U, 45U, 195U, 226U, 68U, 246U, 199U,
    226U, 194U, 178U, 189U, 121U, 31U, 69U, 13U, 253U, 212U, 255U, 13U, 221U, 53U, 171U, 42U, 218U,
    79U, 27U, 144U, 171U, 22U, 239U, 43U, 246U, 59U, 63U, 190U, 136U, 206U, 138U, 93U, 91U, 184U,
    84U, 48U, 116U, 13U, 55U, 68U, 132U, 156U, 19U
  };

static uint8_t
sigver_vectors512_low6[32U] =
  {
    139U, 117U, 252U, 1U, 41U, 201U, 167U, 143U, 131U, 149U, 198U, 58U, 233U, 105U, 75U, 5U, 205U,
    105U, 80U, 102U, 92U, 245U, 218U, 125U, 102U, 17U, 141U, 228U, 81U, 66U, 38U, 36U
  };

static uint8_t
sigver_vectors512_low7[32U] =
  {
    179U, 148U, 23U, 25U, 129U, 212U, 137U, 109U, 110U, 27U, 78U, 242U, 51U, 109U, 155U, 239U, 231U,
    210U, 126U, 30U, 184U, 127U, 28U, 20U, 184U, 221U, 218U, 98U, 42U, 243U, 121U, 220U
  };

static uint8_t
sigver_vectors512_low8[32U] =
  {
    23U, 226U, 152U, 230U, 122U, 210U, 175U, 118U, 246U, 137U, 47U, 220U, 234U, 208U, 10U, 136U,
    37U, 101U, 115U, 134U, 143U, 121U, 220U, 116U, 67U, 27U, 85U, 16U, 48U, 88U, 240U, 176U
  };

static uint8_t
sigver_vectors512_low9[32U] =
  {
    136U, 19U, 40U, 205U, 145U, 228U, 61U, 48U, 19U, 63U, 110U, 71U, 30U, 11U, 155U, 4U, 53U, 59U,
    23U, 137U, 63U, 183U, 97U, 79U, 215U, 51U, 61U, 129U, 42U, 61U, 246U, 180U
  };

static uint8_t
sigver_vectors512_low10[128U] =
  {
    29U, 184U, 84U, 69U, 201U, 216U, 209U, 71U, 138U, 151U, 221U, 157U, 111U, 251U, 241U, 30U, 188U,
    210U, 17U, 77U, 46U, 212U, 232U, 182U, 129U, 17U, 113U, 217U, 71U, 231U, 212U, 218U, 237U, 234U,
    53U, 175U, 97U, 119U, 222U, 190U, 46U, 246U, 217U, 63U, 148U, 255U, 157U, 119U, 11U, 69U, 212U,
    88U, 233U, 29U, 235U, 78U, 239U, 89U, 133U, 100U, 37U, 215U, 176U, 2U, 145U, 175U, 249U, 182U,
    201U, 250U, 2U, 55U, 94U, 193U, 160U, 111U, 113U, 247U, 84U, 135U, 33U, 121U, 0U, 35U, 48U, 28U,
    246U, 172U, 127U, 238U, 29U, 69U, 18U, 40U, 16U, 110U, 244U, 71U, 38U, 129U, 230U, 82U, 200U,
    205U, 89U, 177U, 93U, 109U, 22U, 241U, 225U, 52U, 64U, 216U, 136U, 226U, 101U, 129U, 124U, 180U,
    166U, 84U, 247U, 36U, 110U, 9U, 128U, 223U
  };

static uint8_t
sigver_vectors512_low11[32U] =
  {
    118U, 229U, 16U, 134U, 224U, 120U, 178U, 177U, 22U, 253U, 30U, 156U, 111U, 163U, 213U, 63U,
    103U, 90U, 228U, 2U, 82U, 251U, 159U, 12U, 198U, 40U, 23U, 189U, 156U, 232U, 131U, 29U
  };

static uint8_t
sigver_vectors512_low12[32U] =
  {
    202U, 126U, 96U, 154U, 11U, 29U, 20U, 183U, 201U, 36U, 155U, 83U, 218U, 11U, 32U, 80U, 69U, 14U,
    42U, 37U, 203U, 108U, 143U, 129U, 197U, 49U, 25U, 116U, 167U, 239U, 181U, 118U
  };

static uint8_t
sigver_vectors512_low13[32U] =
  {
    35U, 182U, 83U, 250U, 170U, 125U, 69U, 82U, 56U, 135U, 113U, 147U, 24U, 3U, 206U, 147U, 157U,
    213U, 238U, 98U, 211U, 250U, 114U, 176U, 25U, 190U, 27U, 34U, 114U, 200U, 85U, 146U
  };

static uint8_t
sigver_vectors512_low14[32U] =
  {
    160U, 60U, 111U, 92U, 84U, 161U, 8U, 97U, 214U, 184U, 146U, 40U, 33U, 112U, 142U, 147U, 6U,
    253U, 109U, 93U, 16U, 213U, 102U, 132U, 90U, 16U, 101U, 57U, 203U, 244U, 250U, 221U
  };

static uint8_t
sigver_vectors512_low15[128U] =
  {
    145U, 141U, 159U, 66U, 14U, 146U, 123U, 62U, 10U, 85U, 210U, 118U, 184U, 180U, 13U, 138U, 44U,
    93U, 247U, 72U, 114U, 127U, 247U, 42U, 67U, 140U, 126U, 101U, 147U, 245U, 66U, 39U, 64U, 80U,
    220U, 231U, 39U, 152U, 13U, 62U, 249U, 12U, 138U, 165U, 193U, 61U, 83U, 241U, 232U, 214U, 49U,
    235U, 182U, 80U, 222U, 225U, 27U, 148U, 144U, 43U, 189U, 124U, 146U, 184U, 24U, 106U, 249U, 3U,
    156U, 86U, 196U, 63U, 49U, 16U, 105U, 119U, 146U, 200U, 205U, 22U, 20U, 22U, 111U, 6U, 208U,
    156U, 219U, 88U, 218U, 177U, 104U, 204U, 54U, 128U, 168U, 71U, 59U, 26U, 98U, 59U, 248U, 93U,
    186U, 133U, 94U, 172U, 229U, 121U, 217U, 65U, 13U, 44U, 76U, 165U, 237U, 230U, 220U, 30U, 61U,
    184U, 30U, 35U, 60U, 52U, 174U, 146U, 47U, 73U
  };

static uint8_t
sigver_vectors512_low16[32U] =
  {
    188U, 124U, 142U, 9U, 189U, 9U, 52U, 104U, 247U, 6U, 116U, 10U, 65U, 48U, 197U, 68U, 55U, 79U,
    220U, 146U, 74U, 83U, 94U, 240U, 46U, 157U, 59U, 230U, 198U, 211U, 187U, 250U
  };

static uint8_t
sigver_vectors512_low17[32U] =
  {
    175U, 63U, 129U, 58U, 230U, 100U, 111U, 91U, 109U, 191U, 176U, 242U, 97U, 253U, 66U, 83U, 119U,
    5U, 200U, 0U, 187U, 22U, 71U, 56U, 99U, 67U, 66U, 138U, 159U, 46U, 16U, 252U
  };

static uint8_t
sigver_vectors512_low18[32U] =
  {
    107U, 215U, 206U, 149U, 175U, 37U, 171U, 251U, 241U, 74U, 239U, 75U, 23U, 57U, 47U, 29U, 168U,
    119U, 171U, 86U, 46U, 202U, 56U, 215U, 133U, 254U, 57U, 104U, 46U, 156U, 147U, 36U
  };

static uint8_t
sigver_vectors512_low19[32U] =
  {
    102U, 136U, 190U, 162U, 12U, 135U, 186U, 179U, 77U, 66U, 6U, 66U, 218U, 155U, 221U, 76U, 105U,
    69U, 107U, 222U, 197U, 8U, 53U, 136U, 115U, 103U, 187U, 79U, 183U, 205U, 134U, 80U
  };

static uint8_t
sigver_vectors512_low20[128U] =
  {
    110U, 41U, 50U, 21U, 51U, 1U, 164U, 238U, 246U, 128U, 230U, 66U, 137U, 41U, 173U, 174U, 152U,
    140U, 16U, 141U, 102U, 138U, 49U, 255U, 85U, 208U, 72U, 153U, 71U, 215U, 95U, 248U, 26U, 70U,
    191U, 137U, 232U, 77U, 100U, 1U, 240U, 35U, 190U, 110U, 135U, 104U, 143U, 188U, 215U, 132U,
    215U, 133U, 202U, 132U, 103U, 53U, 82U, 74U, 203U, 82U, 208U, 4U, 82U, 200U, 64U, 64U, 164U,
    121U, 231U, 204U, 51U, 9U, 54U, 68U, 29U, 147U, 187U, 231U, 34U, 169U, 67U, 42U, 110U, 29U,
    177U, 18U, 181U, 201U, 64U, 59U, 16U, 39U, 44U, 177U, 52U, 127U, 214U, 25U, 212U, 99U, 247U,
    169U, 210U, 35U, 173U, 118U, 253U, 224U, 109U, 138U, 104U, 131U, 80U, 15U, 184U, 67U, 35U, 90U,
    191U, 249U, 142U, 36U, 27U, 223U, 181U, 83U, 140U, 62U
  };

static uint8_t
sigver_vectors512_low21[32U] =
  {
    156U, 176U, 207U, 105U, 48U, 61U, 175U, 199U, 97U, 212U, 228U, 104U, 123U, 78U, 207U, 3U, 158U,
    109U, 52U, 171U, 150U, 74U, 248U, 8U, 16U, 216U, 213U, 88U, 164U, 168U, 214U, 247U
  };

static uint8_t
sigver_vectors512_low22[32U] =
  {
    45U, 81U, 35U, 58U, 23U, 136U, 146U, 10U, 134U, 238U, 8U, 161U, 150U, 44U, 121U, 239U, 163U,
    23U, 251U, 120U, 121U, 226U, 151U, 218U, 210U, 20U, 109U, 185U, 149U, 250U, 28U, 120U
  };

static uint8_t
sigver_vectors512_low23[32U] =
  {
    75U, 159U, 145U, 228U, 40U, 82U, 135U, 38U, 26U, 29U, 28U, 146U, 60U, 246U, 25U, 205U, 82U,
    193U, 117U, 207U, 231U, 241U, 190U, 96U, 165U, 37U, 140U, 97U, 3U, 72U, 186U, 61U
  };

static uint8_t
sigver_vectors512_low24[32U] =
  {
    40U, 196U, 95U, 144U, 29U, 113U, 196U, 27U, 41U, 134U, 56U, 236U, 13U, 106U, 133U, 215U, 252U,
    176U, 195U, 59U, 191U, 236U, 90U, 156U, 129U, 8U, 70U, 182U, 57U, 40U, 154U, 132U
  };

static uint8_t
sigver_vectors512_low25[128U] =
  {
    47U, 72U, 236U, 56U, 127U, 24U, 16U, 53U, 179U, 80U, 119U, 46U, 39U, 244U, 120U, 174U, 110U,
    199U, 72U, 121U, 35U, 105U, 47U, 174U, 33U, 126U, 15U, 134U, 54U, 172U, 208U, 98U, 166U, 172U,
    57U, 247U, 67U, 95U, 39U, 160U, 235U, 207U, 216U, 24U, 122U, 145U, 239U, 0U, 251U, 104U, 209U,
    6U, 184U, 218U, 74U, 29U, 237U, 197U, 164U, 10U, 79U, 174U, 112U, 158U, 146U, 176U, 15U, 204U,
    33U, 141U, 231U, 100U, 23U, 215U, 81U, 133U, 229U, 157U, 255U, 118U, 236U, 21U, 67U, 251U, 66U,
    157U, 135U, 194U, 202U, 129U, 52U, 255U, 90U, 233U, 180U, 84U, 86U, 202U, 217U, 63U, 198U, 114U,
    35U, 198U, 130U, 147U, 35U, 19U, 149U, 40U, 125U, 192U, 183U, 86U, 53U, 86U, 96U, 114U, 26U,
    31U, 93U, 248U, 59U, 245U, 188U, 184U, 69U, 110U
  };

static uint8_t
sigver_vectors512_low26[32U] =
  {
    227U, 16U, 150U, 194U, 213U, 18U, 251U, 248U, 79U, 129U, 233U, 189U, 177U, 111U, 51U, 18U, 23U,
    2U, 137U, 118U, 5U, 180U, 58U, 61U, 181U, 70U, 248U, 251U, 105U, 91U, 95U, 111U
  };

static uint8_t
sigver_vectors512_low27[32U] =
  {
    111U, 190U, 198U, 160U, 74U, 140U, 89U, 214U, 28U, 144U, 10U, 133U, 29U, 139U, 248U, 82U, 33U,
    135U, 211U, 236U, 38U, 55U, 177U, 15U, 168U, 243U, 119U, 104U, 158U, 8U, 107U, 186U
  };

static uint8_t
sigver_vectors512_low28[32U] =
  {
    27U, 36U, 76U, 33U, 192U, 140U, 12U, 10U, 16U, 71U, 127U, 183U, 162U, 19U, 130U, 212U, 5U, 185U,
    92U, 117U, 80U, 136U, 41U, 40U, 89U, 202U, 14U, 113U, 186U, 182U, 131U, 97U
  };

static uint8_t
sigver_vectors512_low29[32U] =
  {
    133U, 47U, 76U, 191U, 211U, 70U, 233U, 15U, 64U, 78U, 29U, 213U, 196U, 178U, 193U, 222U, 188U,
    163U, 234U, 26U, 190U, 254U, 132U, 0U, 104U, 93U, 112U, 58U, 234U, 108U, 92U, 127U
  };

static uint8_t
sigver_vectors512_low30[128U] =
  {
    253U, 46U, 93U, 228U, 33U, 238U, 70U, 201U, 254U, 98U, 144U, 163U, 63U, 149U, 179U, 148U, 189U,
    91U, 119U, 98U, 242U, 49U, 120U, 247U, 246U, 131U, 79U, 31U, 5U, 111U, 169U, 168U, 131U, 20U,
    70U, 64U, 60U, 9U, 143U, 244U, 221U, 118U, 65U, 115U, 249U, 116U, 190U, 76U, 137U, 211U, 118U,
    17U, 150U, 19U, 164U, 161U, 137U, 15U, 111U, 194U, 221U, 255U, 134U, 43U, 218U, 41U, 45U, 212U,
    159U, 84U, 16U, 217U, 177U, 207U, 225U, 217U, 126U, 244U, 88U, 43U, 97U, 82U, 73U, 67U, 114U,
    252U, 8U, 56U, 133U, 245U, 64U, 192U, 31U, 134U, 215U, 128U, 230U, 243U, 231U, 90U, 149U, 74U,
    242U, 25U, 15U, 218U, 233U, 96U, 78U, 63U, 138U, 179U, 42U, 176U, 41U, 45U, 192U, 215U, 144U,
    189U, 38U, 39U, 227U, 123U, 75U, 72U, 133U, 223U
  };

static uint8_t
sigver_vectors512_low31[32U] =
  {
    99U, 60U, 46U, 229U, 99U, 11U, 98U, 201U, 206U, 131U, 158U, 253U, 77U, 72U, 90U, 109U, 53U,
    232U, 185U, 67U, 13U, 38U, 79U, 254U, 80U, 29U, 40U, 219U, 172U, 231U, 145U, 35U
  };

static uint8_t
sigver_vectors512_low32[32U] =
  {
    75U, 102U, 138U, 26U, 109U, 26U, 37U, 176U, 137U, 247U, 92U, 43U, 216U, 216U, 198U, 169U, 161U,
    79U, 231U, 183U, 41U, 244U, 90U, 130U, 86U, 93U, 162U, 232U, 102U, 226U, 196U, 144U
  };

static uint8_t
sigver_vectors512_low33[32U] =
  {
    191U, 33U, 17U, 201U, 62U, 192U, 85U, 167U, 237U, 169U, 12U, 16U, 111U, 206U, 73U, 79U, 216U,
    102U, 4U, 86U, 52U, 253U, 42U, 162U, 141U, 110U, 1U, 143U, 145U, 6U, 153U, 78U
  };

static uint8_t
sigver_vectors512_low34[32U] =
  {
    134U, 176U, 52U, 18U, 8U, 160U, 170U, 85U, 237U, 236U, 253U, 39U, 47U, 73U, 203U, 52U, 64U,
    140U, 229U, 75U, 127U, 235U, 193U, 208U, 161U, 194U, 206U, 119U, 171U, 105U, 136U, 248U
  };

static uint8_t
sigver_vectors512_low35[128U] =
  {
    75U, 194U, 217U, 168U, 152U, 57U, 91U, 18U, 112U, 22U, 53U, 241U, 4U, 143U, 191U, 210U, 99U,
    236U, 17U, 94U, 65U, 80U, 83U, 43U, 3U, 77U, 89U, 230U, 37U, 35U, 143U, 78U, 211U, 38U, 25U,
    116U, 76U, 97U, 46U, 53U, 172U, 90U, 35U, 190U, 232U, 213U, 245U, 101U, 22U, 65U, 164U, 146U,
    33U, 125U, 48U, 94U, 80U, 81U, 50U, 28U, 39U, 54U, 71U, 241U, 75U, 199U, 196U, 175U, 171U, 81U,
    133U, 84U, 224U, 28U, 130U, 214U, 252U, 22U, 148U, 200U, 189U, 190U, 179U, 38U, 187U, 96U, 123U,
    202U, 245U, 67U, 99U, 3U, 188U, 9U, 246U, 76U, 2U, 198U, 236U, 80U, 222U, 64U, 154U, 72U, 79U,
    82U, 55U, 247U, 211U, 78U, 38U, 81U, 173U, 167U, 236U, 66U, 156U, 163U, 185U, 157U, 216U, 124U,
    96U, 21U, 210U, 244U, 179U, 66U
  };

static uint8_t
sigver_vectors512_low36[32U] =
  {
    247U, 141U, 206U, 64U, 209U, 203U, 140U, 74U, 242U, 116U, 155U, 242U, 44U, 111U, 138U, 154U,
    71U, 11U, 30U, 65U, 17U, 39U, 150U, 33U, 93U, 208U, 23U, 229U, 125U, 241U, 179U, 138U
  };

static uint8_t
sigver_vectors512_low37[32U] =
  {
    97U, 178U, 155U, 11U, 192U, 61U, 255U, 127U, 160U, 6U, 19U, 180U, 222U, 30U, 35U, 23U, 207U,
    191U, 43U, 173U, 213U, 13U, 238U, 51U, 118U, 192U, 50U, 168U, 135U, 197U, 184U, 101U
  };

static uint8_t
sigver_vectors512_low38[32U] =
  {
    74U, 150U, 22U, 154U, 93U, 234U, 54U, 162U, 89U, 64U, 17U, 83U, 126U, 224U, 220U, 25U, 232U,
    249U, 247U, 78U, 130U, 192U, 116U, 52U, 7U, 148U, 71U, 21U, 90U, 131U, 1U, 82U
  };

static uint8_t
sigver_vectors512_low39[32U] =
  {
    162U, 4U, 234U, 164U, 233U, 125U, 117U, 83U, 161U, 82U, 29U, 159U, 107U, 170U, 220U, 11U, 109U,
    97U, 131U, 186U, 15U, 56U, 93U, 133U, 147U, 214U, 202U, 131U, 96U, 124U, 77U, 130U
  };

static uint8_t
sigver_vectors512_low40[128U] =
  {
    211U, 53U, 106U, 104U, 52U, 23U, 80U, 138U, 155U, 145U, 54U, 67U, 230U, 206U, 172U, 18U, 129U,
    239U, 88U, 63U, 66U, 137U, 104U, 249U, 210U, 182U, 84U, 10U, 24U, 157U, 112U, 65U, 196U, 119U,
    218U, 141U, 32U, 125U, 5U, 41U, 114U, 15U, 112U, 218U, 182U, 176U, 218U, 140U, 33U, 104U, 131U,
    116U, 118U, 193U, 198U, 182U, 59U, 81U, 126U, 211U, 202U, 212U, 138U, 227U, 49U, 207U, 113U,
    110U, 207U, 71U, 160U, 247U, 208U, 11U, 87U, 7U, 58U, 198U, 164U, 116U, 151U, 22U, 212U, 157U,
    128U, 196U, 212U, 98U, 97U, 211U, 142U, 46U, 52U, 180U, 244U, 62U, 15U, 32U, 178U, 128U, 132U,
    47U, 110U, 62U, 163U, 79U, 239U, 221U, 223U, 185U, 250U, 42U, 4U, 15U, 254U, 145U, 94U, 135U,
    132U, 207U, 219U, 41U, 179U, 54U, 74U, 52U, 202U, 98U
  };

static uint8_t
sigver_vectors512_low41[32U] =
  {
    63U, 204U, 59U, 62U, 27U, 16U, 63U, 228U, 53U, 172U, 33U, 76U, 117U, 107U, 218U, 173U, 48U,
    147U, 137U, 225U, 200U, 3U, 230U, 216U, 75U, 187U, 194U, 112U, 57U, 252U, 249U
  };

static uint8_t
sigver_vectors512_low42[32U] =
  {
    127U, 9U, 237U, 209U, 236U, 135U, 166U, 211U, 109U, 200U, 28U, 21U, 40U, 213U, 42U, 98U, 119U,
    110U, 102U, 108U, 39U, 68U, 21U, 169U, 244U, 65U, 214U, 168U, 223U, 107U, 146U, 55U
  };

static uint8_t
sigver_vectors512_low43[32U] =
  {
    28U, 172U, 19U, 242U, 119U, 53U, 68U, 86U, 174U, 103U, 171U, 9U, 176U, 158U, 7U, 235U, 26U,
    242U, 162U, 191U, 69U, 16U, 141U, 167U, 15U, 92U, 140U, 106U, 76U, 188U, 213U, 56U
  };

static uint8_t
sigver_vectors512_low44[32U] =
  {
    93U, 131U, 117U, 46U, 84U, 5U, 37U, 96U, 43U, 167U, 230U, 254U, 228U, 212U, 38U, 63U, 62U, 218U,
    89U, 230U, 125U, 242U, 10U, 172U, 121U, 202U, 103U, 232U, 137U, 159U, 237U, 13U
  };

static uint8_t
sigver_vectors512_low45[128U] =
  {
    215U, 245U, 218U, 159U, 76U, 249U, 41U, 155U, 127U, 134U, 197U, 43U, 136U, 54U, 76U, 226U, 143U,
    233U, 173U, 165U, 93U, 213U, 81U, 161U, 1U, 135U, 144U, 249U, 225U, 32U, 94U, 36U, 5U, 172U,
    98U, 66U, 157U, 101U, 9U, 63U, 116U, 236U, 53U, 161U, 109U, 159U, 25U, 92U, 153U, 60U, 212U,
    235U, 141U, 192U, 170U, 13U, 171U, 183U, 10U, 80U, 51U, 33U, 216U, 169U, 100U, 145U, 96U, 214U,
    179U, 208U, 160U, 133U, 75U, 182U, 140U, 76U, 57U, 105U, 63U, 89U, 46U, 245U, 221U, 71U, 138U,
    162U, 67U, 45U, 8U, 101U, 216U, 125U, 72U, 179U, 174U, 169U, 199U, 215U, 209U, 20U, 22U, 92U,
    146U, 0U, 228U, 232U, 215U, 189U, 2U, 167U, 137U, 94U, 196U, 65U, 142U, 111U, 47U, 237U, 107U,
    36U, 75U, 246U, 98U, 9U, 3U, 158U, 152U, 169U
  };

static uint8_t
sigver_vectors512_low46[32U] =
  {
    94U, 199U, 2U, 212U, 58U, 103U, 173U, 168U, 110U, 251U, 252U, 19U, 108U, 241U, 109U, 150U, 7U,
    137U, 6U, 149U, 74U, 63U, 31U, 158U, 68U, 6U, 116U, 205U, 144U, 126U, 70U, 118U
  };

static uint8_t
sigver_vectors512_low47[32U] =
  {
    5U, 166U, 32U, 68U, 254U, 216U, 71U, 13U, 212U, 252U, 163U, 141U, 137U, 213U, 131U, 206U, 54U,
    213U, 13U, 40U, 182U, 106U, 176U, 181U, 25U, 34U, 178U, 29U, 169U, 44U, 86U, 217U
  };

static uint8_t
sigver_vectors512_low48[32U] =
  {
    117U, 243U, 3U, 114U, 152U, 241U, 69U, 125U, 186U, 85U, 116U, 57U, 153U, 151U, 106U, 28U, 38U,
    54U, 178U, 184U, 171U, 46U, 211U, 223U, 71U, 54U, 166U, 210U, 147U, 74U, 204U, 131U
  };

static uint8_t
sigver_vectors512_low49[32U] =
  {
    25U, 212U, 58U, 209U, 104U, 221U, 161U, 187U, 138U, 196U, 35U, 248U, 240U, 136U, 118U, 81U, 82U,
    52U, 179U, 216U, 65U, 229U, 127U, 174U, 241U, 181U, 171U, 39U, 53U, 155U, 39U, 239U
  };

static uint8_t
sigver_vectors512_low50[128U] =
  {
    104U, 244U, 180U, 68U, 225U, 204U, 32U, 37U, 232U, 255U, 85U, 232U, 4U, 110U, 173U, 115U, 94U,
    110U, 49U, 112U, 130U, 237U, 247U, 206U, 101U, 232U, 53U, 115U, 80U, 28U, 185U, 44U, 64U, 140U,
    28U, 28U, 108U, 79U, 204U, 166U, 185U, 106U, 211U, 66U, 36U, 241U, 123U, 32U, 190U, 71U, 28U,
    201U, 244U, 249U, 127U, 10U, 91U, 123U, 250U, 233U, 85U, 139U, 219U, 46U, 203U, 110U, 69U, 43U,
    183U, 67U, 96U, 55U, 36U, 39U, 61U, 158U, 141U, 44U, 162U, 42U, 253U, 218U, 53U, 200U, 163U,
    113U, 178U, 129U, 83U, 215U, 114U, 48U, 62U, 74U, 37U, 220U, 79U, 40U, 233U, 166U, 220U, 150U,
    53U, 51U, 20U, 80U, 245U, 175U, 41U, 13U, 250U, 52U, 49U, 195U, 192U, 139U, 145U, 213U, 201U,
    114U, 132U, 54U, 28U, 3U, 236U, 120U, 241U, 188U
  };

static uint8_t
sigver_vectors512_low51[32U] =
  {
    246U, 58U, 254U, 153U, 225U, 181U, 252U, 101U, 39U, 130U, 248U, 107U, 89U, 146U, 106U, 242U,
    46U, 96U, 114U, 190U, 147U, 57U, 15U, 228U, 31U, 84U, 18U, 4U, 249U, 201U, 53U, 209U
  };

static uint8_t
sigver_vectors512_low52[32U] =
  {
    246U, 225U, 156U, 229U, 147U, 94U, 51U, 97U, 131U, 194U, 27U, 236U, 246U, 101U, 150U, 184U,
    245U, 89U, 210U, 208U, 46U, 226U, 130U, 170U, 135U, 167U, 214U, 249U, 54U, 247U, 38U, 12U
  };

static uint8_t
sigver_vectors512_low53[32U] =
  {
    206U, 244U, 131U, 30U, 69U, 21U, 199U, 124U, 160U, 98U, 40U, 38U, 20U, 181U, 74U, 17U, 183U,
    220U, 64U, 87U, 230U, 153U, 118U, 133U, 194U, 251U, 250U, 149U, 179U, 146U, 191U, 114U
  };

static uint8_t
sigver_vectors512_low54[32U] =
  {
    242U, 13U, 192U, 27U, 243U, 142U, 19U, 68U, 186U, 103U, 90U, 34U, 35U, 157U, 152U, 147U, 179U,
    163U, 227U, 61U, 154U, 64U, 51U, 41U, 163U, 210U, 22U, 80U, 233U, 18U, 91U, 117U
  };

static uint8_t
sigver_vectors512_low55[128U] =
  {
    231U, 91U, 224U, 91U, 224U, 170U, 247U, 7U, 25U, 180U, 136U, 184U, 154U, 170U, 233U, 0U, 135U,
    7U, 202U, 82U, 137U, 148U, 70U, 29U, 183U, 19U, 12U, 67U, 104U, 87U, 90U, 2U, 75U, 240U, 152U,
    28U, 48U, 93U, 97U, 38U, 94U, 139U, 151U, 89U, 158U, 195U, 92U, 3U, 186U, 221U, 18U, 86U, 184U,
    13U, 107U, 247U, 5U, 71U, 173U, 96U, 137U, 185U, 131U, 227U, 188U, 195U, 72U, 24U, 40U, 243U,
    37U, 158U, 67U, 230U, 85U, 225U, 119U, 252U, 66U, 63U, 215U, 224U, 102U, 189U, 62U, 214U, 141U,
    129U, 223U, 132U, 247U, 115U, 192U, 249U, 229U, 248U, 191U, 68U, 105U, 150U, 11U, 139U, 77U,
    123U, 42U, 55U, 47U, 208U, 237U, 211U, 82U, 31U, 107U, 230U, 112U, 144U, 143U, 45U, 144U, 163U,
    67U, 244U, 22U, 53U, 142U, 167U, 14U, 126U
  };

static uint8_t
sigver_vectors512_low56[32U] =
  {
    109U, 17U, 176U, 157U, 39U, 103U, 207U, 141U, 39U, 95U, 174U, 231U, 70U, 194U, 3U, 72U, 98U,
    89U, 246U, 109U, 210U, 191U, 163U, 166U, 92U, 57U, 55U, 26U, 102U, 178U, 51U, 133U
  };

static uint8_t
sigver_vectors512_low57[32U] =
  {
    78U, 176U, 92U, 115U, 224U, 82U, 97U, 233U, 121U, 24U, 40U, 51U, 242U, 3U, 17U, 229U, 54U, 111U,
    114U, 244U, 185U, 73U, 102U, 95U, 242U, 148U, 249U, 89U, 55U, 85U, 52U, 198U
  };

static uint8_t
sigver_vectors512_low58[32U] =
  {
    21U, 166U, 151U, 205U, 182U, 20U, 225U, 28U, 8U, 16U, 225U, 231U, 100U, 205U, 80U, 31U, 202U,
    188U, 112U, 135U, 76U, 149U, 117U, 135U, 188U, 72U, 131U, 217U, 67U, 142U, 23U, 127U
  };

static uint8_t
sigver_vectors512_low59[32U] =
  {
    123U, 246U, 36U, 79U, 146U, 188U, 118U, 128U, 99U, 206U, 203U, 83U, 54U, 200U, 234U, 172U, 210U,
    61U, 185U, 48U, 178U, 135U, 3U, 86U, 15U, 36U, 28U, 125U, 147U, 149U, 13U, 253U
  };

static uint8_t
sigver_vectors512_low60[128U] =
  {
    13U, 196U, 163U, 234U, 182U, 107U, 210U, 231U, 3U, 168U, 255U, 245U, 102U, 195U, 77U, 70U, 111U,
    152U, 35U, 174U, 66U, 189U, 33U, 4U, 246U, 26U, 107U, 5U, 28U, 11U, 1U, 120U, 51U, 252U, 239U,
    77U, 96U, 157U, 19U, 122U, 217U, 124U, 32U, 156U, 128U, 238U, 190U, 37U, 40U, 87U, 170U, 127U,
    175U, 195U, 95U, 22U, 0U, 10U, 43U, 212U, 180U, 190U, 15U, 168U, 59U, 110U, 34U, 158U, 221U,
    253U, 24U, 1U, 1U, 241U, 244U, 13U, 4U, 83U, 20U, 128U, 83U, 216U, 48U, 104U, 51U, 223U, 100U,
    213U, 149U, 153U, 185U, 1U, 148U, 181U, 85U, 65U, 215U, 242U, 45U, 213U, 137U, 218U, 159U, 123U,
    229U, 25U, 203U, 187U, 157U, 180U, 22U, 199U, 27U, 254U, 64U, 236U, 9U, 11U, 91U, 122U, 96U,
    14U, 236U, 41U, 191U, 212U, 115U, 6U
  };

static uint8_t
sigver_vectors512_low61[32U] =
  {
    243U, 137U, 156U, 171U, 160U, 56U, 239U, 181U, 52U, 196U, 206U, 160U, 189U, 39U, 104U, 20U,
    255U, 216U, 1U, 148U, 71U, 60U, 144U, 59U, 129U, 175U, 17U, 200U, 192U, 92U, 182U, 230U
  };

static uint8_t
sigver_vectors512_low62[32U] =
  {
    110U, 166U, 177U, 116U, 2U, 252U, 242U, 232U, 231U, 55U, 209U, 31U, 252U, 124U, 46U, 211U, 178U,
    208U, 188U, 59U, 143U, 39U, 26U, 56U, 31U, 66U, 148U, 207U, 246U, 38U, 130U, 195U
  };

static uint8_t
sigver_vectors512_low63[32U] =
  {
    87U, 185U, 147U, 128U, 69U, 46U, 29U, 55U, 177U, 51U, 196U, 155U, 155U, 164U, 147U, 222U, 232U,
    99U, 9U, 64U, 71U, 124U, 163U, 53U, 26U, 67U, 217U, 11U, 153U, 135U, 30U, 106U
  };

static uint8_t
sigver_vectors512_low64[32U] =
  {
    223U, 89U, 156U, 58U, 55U, 16U, 90U, 243U, 236U, 193U, 89U, 179U, 182U, 133U, 204U, 179U, 225U,
    81U, 183U, 213U, 207U, 45U, 151U, 20U, 121U, 116U, 174U, 113U, 244U, 102U, 182U, 21U
  };

static uint8_t
sigver_vectors512_low65[128U] =
  {
    213U, 94U, 94U, 18U, 74U, 114U, 23U, 135U, 156U, 169U, 134U, 242U, 133U, 226U, 42U, 197U, 25U,
    64U, 179U, 89U, 89U, 187U, 245U, 84U, 49U, 4U, 181U, 84U, 115U, 86U, 253U, 26U, 14U, 195U, 124U,
    10U, 35U, 32U, 144U, 4U, 162U, 236U, 91U, 202U, 243U, 51U, 91U, 196U, 94U, 77U, 201U, 144U,
    234U, 205U, 41U, 178U, 217U, 181U, 207U, 52U, 156U, 123U, 166U, 119U, 17U, 53U, 98U, 153U, 188U,
    234U, 182U, 240U, 72U, 223U, 118U, 28U, 101U, 242U, 152U, 136U, 3U, 19U, 61U, 103U, 35U, 162U,
    130U, 15U, 239U, 178U, 101U, 76U, 199U, 197U, 240U, 50U, 248U, 51U, 186U, 120U, 163U, 77U, 40U,
    120U, 198U, 176U, 186U, 101U, 78U, 190U, 38U, 177U, 16U, 201U, 53U, 171U, 181U, 96U, 36U, 189U,
    93U, 15U, 9U, 179U, 103U, 114U, 76U, 7U
  };

static uint8_t
sigver_vectors512_low66[32U] =
  {
    31U, 214U, 244U, 185U, 141U, 7U, 85U, 41U, 30U, 122U, 35U, 14U, 159U, 129U, 236U, 249U, 9U,
    230U, 53U, 10U, 173U, 176U, 142U, 66U, 163U, 38U, 47U, 241U, 146U, 0U, 251U, 210U
  };

static uint8_t
sigver_vectors512_low67[32U] =
  {
    85U, 120U, 254U, 247U, 155U, 196U, 119U, 172U, 251U, 142U, 208U, 220U, 16U, 196U, 245U, 128U,
    156U, 20U, 220U, 84U, 146U, 64U, 91U, 55U, 146U, 167U, 148U, 6U, 80U, 179U, 5U, 215U
  };

static uint8_t
sigver_vectors512_low68[32U] =
  {
    151U, 169U, 158U, 150U, 228U, 7U, 179U, 173U, 162U, 194U, 220U, 249U, 206U, 238U, 185U, 132U,
    217U, 164U, 208U, 170U, 102U, 221U, 240U, 167U, 76U, 162U, 60U, 171U, 251U, 21U, 102U, 204U
  };

static uint8_t
sigver_vectors512_low69[32U] =
  {
    14U, 202U, 195U, 21U, 220U, 25U, 156U, 254U, 163U, 193U, 83U, 72U, 193U, 48U, 146U, 74U, 31U,
    120U, 112U, 25U, 254U, 76U, 211U, 174U, 71U, 202U, 139U, 17U, 18U, 104U, 117U, 74U
  };

static uint8_t
sigver_vectors512_low70[128U] =
  {
    119U, 83U, 192U, 59U, 66U, 2U, 203U, 56U, 188U, 1U, 144U, 169U, 249U, 49U, 235U, 49U, 133U,
    141U, 112U, 93U, 146U, 214U, 80U, 50U, 15U, 244U, 73U, 252U, 153U, 22U, 127U, 179U, 119U, 11U,
    118U, 76U, 137U, 136U, 246U, 179U, 74U, 197U, 163U, 213U, 7U, 161U, 14U, 10U, 255U, 127U, 136U,
    41U, 63U, 106U, 34U, 199U, 237U, 138U, 36U, 36U, 138U, 82U, 220U, 18U, 94U, 65U, 110U, 21U,
    136U, 51U, 252U, 56U, 175U, 41U, 25U, 159U, 140U, 164U, 147U, 16U, 104U, 212U, 204U, 170U, 135U,
    226U, 153U, 233U, 86U, 66U, 6U, 143U, 104U, 194U, 8U, 203U, 120U, 45U, 241U, 57U, 8U, 249U, 80U,
    86U, 71U, 67U, 237U, 22U, 146U, 80U, 43U, 175U, 175U, 175U, 241U, 105U, 220U, 143U, 230U, 116U,
    251U, 94U, 79U, 63U, 253U, 87U, 140U, 53U
  };

static uint8_t
sigver_vectors512_low71[32U] =
  {
    45U, 203U, 216U, 121U, 12U, 238U, 85U, 46U, 159U, 24U, 242U, 179U, 20U, 154U, 34U, 82U, 220U,
    213U, 139U, 153U, 202U, 125U, 201U, 104U, 11U, 146U, 200U, 196U, 58U, 163U, 56U, 116U
  };

static uint8_t
sigver_vectors512_low72[32U] =
  {
    93U, 188U, 139U, 184U, 129U, 60U, 142U, 1U, 157U, 128U, 225U, 154U, 205U, 176U, 121U, 47U, 83U,
    121U, 128U, 254U, 205U, 233U, 61U, 182U, 33U, 170U, 241U, 246U, 208U, 230U, 238U, 52U
  };

static uint8_t
sigver_vectors512_low73[32U] =
  {
    43U, 219U, 216U, 176U, 215U, 89U, 89U, 86U, 98U, 204U, 16U, 177U, 2U, 54U, 19U, 110U, 246U,
    206U, 66U, 150U, 65U, 246U, 140U, 246U, 72U, 15U, 71U, 47U, 204U, 119U, 188U, 159U
  };

static uint8_t
sigver_vectors512_low74[32U] =
  {
    126U, 125U, 240U, 200U, 184U, 111U, 125U, 176U, 108U, 175U, 22U, 16U, 22U, 111U, 123U, 156U,
    76U, 117U, 68U, 127U, 153U, 29U, 90U, 175U, 77U, 234U, 114U, 12U, 37U, 152U, 92U, 140U
  };

static __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors512_low75[15U] =
  {
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low0 },
        .snd = { .len = 32U, .b = sigver_vectors512_low1 },
        .thd = { .len = 32U, .b = sigver_vectors512_low2 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low3 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low4 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low5 },
        .snd = { .len = 32U, .b = sigver_vectors512_low6 },
        .thd = { .len = 32U, .b = sigver_vectors512_low7 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low8 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low9 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low10 },
        .snd = { .len = 32U, .b = sigver_vectors512_low11 },
        .thd = { .len = 32U, .b = sigver_vectors512_low12 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low13 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low14 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low15 },
        .snd = { .len = 32U, .b = sigver_vectors512_low16 },
        .thd = { .len = 32U, .b = sigver_vectors512_low17 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low18 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low19 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low20 },
        .snd = { .len = 32U, .b = sigver_vectors512_low21 },
        .thd = { .len = 32U, .b = sigver_vectors512_low22 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low23 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low24 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low25 },
        .snd = { .len = 32U, .b = sigver_vectors512_low26 },
        .thd = { .len = 32U, .b = sigver_vectors512_low27 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low28 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low29 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low30 },
        .snd = { .len = 32U, .b = sigver_vectors512_low31 },
        .thd = { .len = 32U, .b = sigver_vectors512_low32 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low33 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low34 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low35 },
        .snd = { .len = 32U, .b = sigver_vectors512_low36 },
        .thd = { .len = 32U, .b = sigver_vectors512_low37 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low38 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low39 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low40 },
        .snd = { .len = 32U, .b = sigver_vectors512_low41 },
        .thd = { .len = 32U, .b = sigver_vectors512_low42 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low43 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low44 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low45 },
        .snd = { .len = 32U, .b = sigver_vectors512_low46 },
        .thd = { .len = 32U, .b = sigver_vectors512_low47 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low48 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low49 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low50 },
        .snd = { .len = 32U, .b = sigver_vectors512_low51 },
        .thd = { .len = 32U, .b = sigver_vectors512_low52 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low53 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low54 },
        .f5 = true
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low55 },
        .snd = { .len = 32U, .b = sigver_vectors512_low56 },
        .thd = { .len = 32U, .b = sigver_vectors512_low57 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low58 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low59 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low60 },
        .snd = { .len = 32U, .b = sigver_vectors512_low61 },
        .thd = { .len = 32U, .b = sigver_vectors512_low62 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low63 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low64 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low65 },
        .snd = { .len = 32U, .b = sigver_vectors512_low66 },
        .thd = { .len = 32U, .b = sigver_vectors512_low67 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low68 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low69 },
        .f5 = false
      }
    ),
    (
      (__Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool){
        .fst = { .len = 128U, .b = sigver_vectors512_low70 },
        .snd = { .len = 32U, .b = sigver_vectors512_low71 },
        .thd = { .len = 32U, .b = sigver_vectors512_low72 },
        .f3 = { .len = 32U, .b = sigver_vectors512_low73 },
        .f4 = { .len = 32U, .b = sigver_vectors512_low74 },
        .f5 = true
      }
    )
  };

static lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors512_low = { .len = 15U, .b = sigver_vectors512_low75 };

static uint8_t
siggen_vectors256_low0[128U] =
  {
    89U, 5U, 35U, 136U, 119U, 199U, 116U, 33U, 247U, 62U, 67U, 238U, 61U, 166U, 242U, 217U, 226U,
    204U, 173U, 95U, 201U, 66U, 220U, 236U, 12U, 189U, 37U, 72U, 41U, 53U, 250U, 175U, 65U, 105U,
    131U, 254U, 22U, 91U, 26U, 4U, 94U, 226U, 188U, 210U, 230U, 220U, 163U, 189U, 244U, 108U, 67U,
    16U, 167U, 70U, 31U, 154U, 55U, 150U, 12U, 166U, 114U, 211U, 254U, 181U, 71U, 62U, 37U, 54U, 5U,
    251U, 29U, 223U, 210U, 128U, 101U, 181U, 60U, 181U, 133U, 138U, 138U, 210U, 129U, 117U, 191U,
    155U, 211U, 134U, 165U, 228U, 113U, 234U, 122U, 101U, 193U, 124U, 201U, 52U, 169U, 215U, 145U,
    233U, 20U, 145U, 235U, 55U, 84U, 208U, 55U, 153U, 121U, 15U, 226U, 211U, 8U, 209U, 97U, 70U,
    213U, 201U, 176U, 208U, 222U, 189U, 151U, 215U, 156U, 232U
  };

static uint8_t
siggen_vectors256_low1[32U] =
  {
    81U, 155U, 66U, 61U, 113U, 95U, 139U, 88U, 31U, 79U, 168U, 238U, 89U, 244U, 119U, 26U, 91U, 68U,
    200U, 19U, 11U, 78U, 62U, 172U, 202U, 84U, 165U, 109U, 218U, 114U, 180U, 100U
  };

static uint8_t
siggen_vectors256_low2[32U] =
  {
    28U, 203U, 233U, 28U, 7U, 95U, 199U, 244U, 240U, 51U, 191U, 162U, 72U, 219U, 143U, 204U, 211U,
    86U, 93U, 233U, 75U, 191U, 177U, 47U, 60U, 89U, 255U, 70U, 194U, 113U, 191U, 131U
  };

static uint8_t
siggen_vectors256_low3[32U] =
  {
    206U, 64U, 20U, 198U, 136U, 17U, 249U, 162U, 26U, 31U, 219U, 44U, 14U, 97U, 19U, 224U, 109U,
    183U, 202U, 147U, 183U, 64U, 78U, 120U, 220U, 124U, 205U, 92U, 168U, 154U, 76U, 169U
  };

static uint8_t
siggen_vectors256_low4[32U] =
  {
    148U, 161U, 187U, 177U, 75U, 144U, 106U, 97U, 162U, 128U, 242U, 69U, 249U, 233U, 60U, 127U, 59U,
    74U, 98U, 71U, 130U, 79U, 93U, 51U, 185U, 103U, 7U, 135U, 100U, 42U, 104U, 222U
  };

static uint8_t
siggen_vectors256_low5[32U] =
  {
    243U, 172U, 128U, 97U, 181U, 20U, 121U, 91U, 136U, 67U, 227U, 214U, 98U, 149U, 39U, 237U, 42U,
    253U, 107U, 31U, 106U, 85U, 90U, 122U, 202U, 187U, 94U, 111U, 121U, 200U, 194U, 172U
  };

static uint8_t
siggen_vectors256_low6[32U] =
  {
    139U, 247U, 120U, 25U, 202U, 5U, 166U, 178U, 120U, 108U, 118U, 38U, 43U, 247U, 55U, 28U, 239U,
    151U, 178U, 24U, 233U, 111U, 23U, 90U, 60U, 205U, 218U, 42U, 204U, 5U, 137U, 3U
  };

static uint8_t
siggen_vectors256_low7[128U] =
  {
    195U, 94U, 47U, 9U, 37U, 83U, 197U, 87U, 114U, 146U, 107U, 219U, 232U, 124U, 151U, 150U, 130U,
    125U, 23U, 2U, 77U, 187U, 146U, 51U, 165U, 69U, 54U, 110U, 46U, 89U, 135U, 221U, 52U, 77U, 235U,
    114U, 223U, 152U, 113U, 68U, 184U, 198U, 196U, 59U, 196U, 27U, 101U, 75U, 148U, 204U, 133U,
    110U, 22U, 185U, 109U, 122U, 130U, 28U, 142U, 192U, 57U, 181U, 3U, 227U, 216U, 103U, 40U, 196U,
    148U, 169U, 103U, 216U, 48U, 17U, 160U, 224U, 144U, 181U, 213U, 76U, 212U, 127U, 78U, 54U, 108U,
    9U, 18U, 188U, 128U, 143U, 187U, 46U, 169U, 110U, 250U, 200U, 143U, 179U, 235U, 236U, 147U, 66U,
    115U, 142U, 34U, 95U, 124U, 124U, 43U, 1U, 28U, 227U, 117U, 181U, 102U, 33U, 162U, 6U, 66U,
    180U, 211U, 110U, 6U, 13U, 180U, 82U, 74U, 241U
  };

static uint8_t
siggen_vectors256_low8[32U] =
  {
    15U, 86U, 219U, 120U, 202U, 70U, 11U, 5U, 92U, 80U, 0U, 100U, 130U, 75U, 237U, 153U, 154U, 37U,
    170U, 244U, 142U, 187U, 81U, 154U, 194U, 1U, 83U, 123U, 133U, 71U, 152U, 19U
  };

static uint8_t
siggen_vectors256_low9[32U] =
  {
    226U, 102U, 221U, 253U, 193U, 38U, 104U, 219U, 48U, 212U, 202U, 62U, 143U, 119U, 73U, 67U, 44U,
    65U, 96U, 68U, 242U, 210U, 184U, 193U, 11U, 243U, 212U, 1U, 42U, 239U, 250U, 138U
  };

static uint8_t
siggen_vectors256_low10[32U] =
  {
    191U, 168U, 100U, 4U, 162U, 233U, 255U, 230U, 125U, 71U, 197U, 135U, 239U, 122U, 151U, 167U,
    244U, 86U, 184U, 99U, 180U, 208U, 44U, 252U, 105U, 40U, 151U, 58U, 181U, 177U, 203U, 57U
  };

static uint8_t
siggen_vectors256_low11[32U] =
  {
    109U, 62U, 113U, 136U, 44U, 59U, 131U, 177U, 86U, 187U, 20U, 224U, 171U, 24U, 74U, 169U, 251U,
    114U, 128U, 104U, 211U, 174U, 159U, 172U, 66U, 17U, 135U, 174U, 11U, 47U, 52U, 198U
  };

static uint8_t
siggen_vectors256_low12[32U] =
  {
    151U, 109U, 58U, 78U, 157U, 35U, 50U, 109U, 192U, 186U, 169U, 250U, 86U, 11U, 124U, 78U, 83U,
    244U, 40U, 100U, 245U, 8U, 72U, 58U, 100U, 115U, 182U, 161U, 16U, 121U, 178U, 219U
  };

static uint8_t
siggen_vectors256_low13[32U] =
  {
    27U, 118U, 110U, 156U, 235U, 113U, 186U, 108U, 1U, 220U, 212U, 110U, 10U, 244U, 98U, 205U, 76U,
    250U, 101U, 42U, 229U, 1U, 125U, 69U, 85U, 184U, 238U, 239U, 227U, 110U, 25U, 50U
  };

static uint8_t
siggen_vectors256_low14[128U] =
  {
    60U, 5U, 78U, 51U, 58U, 148U, 37U, 156U, 54U, 175U, 9U, 171U, 91U, 79U, 249U, 190U, 179U, 73U,
    47U, 141U, 91U, 66U, 130U, 209U, 104U, 1U, 218U, 204U, 178U, 159U, 112U, 254U, 97U, 160U, 179U,
    127U, 254U, 245U, 192U, 76U, 209U, 183U, 14U, 133U, 177U, 245U, 73U, 161U, 196U, 220U, 103U,
    41U, 133U, 229U, 15U, 67U, 234U, 3U, 126U, 250U, 153U, 100U, 240U, 150U, 181U, 246U, 47U, 127U,
    253U, 248U, 214U, 191U, 178U, 204U, 133U, 149U, 88U, 245U, 163U, 147U, 203U, 148U, 157U, 189U,
    72U, 242U, 105U, 52U, 59U, 82U, 99U, 220U, 219U, 156U, 85U, 110U, 202U, 7U, 79U, 46U, 152U,
    230U, 217U, 76U, 44U, 41U, 166U, 119U, 175U, 175U, 128U, 110U, 223U, 121U, 177U, 90U, 63U, 205U,
    70U, 231U, 6U, 123U, 118U, 105U, 248U, 49U, 136U, 238U
  };

static uint8_t
siggen_vectors256_low15[32U] =
  {
    226U, 131U, 135U, 18U, 57U, 131U, 126U, 19U, 185U, 95U, 120U, 158U, 110U, 26U, 246U, 59U, 246U,
    28U, 145U, 140U, 153U, 46U, 98U, 188U, 160U, 64U, 214U, 76U, 173U, 31U, 194U, 239U
  };

static uint8_t
siggen_vectors256_low16[32U] =
  {
    116U, 204U, 216U, 166U, 47U, 186U, 14U, 102U, 124U, 80U, 146U, 154U, 83U, 247U, 140U, 33U, 184U,
    255U, 12U, 60U, 115U, 123U, 11U, 64U, 177U, 117U, 11U, 35U, 2U, 176U, 189U, 232U
  };

static uint8_t
siggen_vectors256_low17[32U] =
  {
    41U, 7U, 78U, 33U, 243U, 160U, 239U, 136U, 185U, 239U, 223U, 16U, 208U, 106U, 164U, 194U, 149U,
    204U, 22U, 113U, 247U, 88U, 202U, 14U, 76U, 209U, 8U, 128U, 61U, 15U, 38U, 20U
  };

static uint8_t
siggen_vectors256_low18[32U] =
  {
    173U, 94U, 136U, 126U, 178U, 179U, 128U, 184U, 216U, 40U, 10U, 214U, 229U, 255U, 138U, 96U,
    244U, 210U, 98U, 67U, 224U, 18U, 76U, 47U, 49U, 162U, 151U, 181U, 208U, 131U, 93U, 226U
  };

static uint8_t
siggen_vectors256_low19[32U] =
  {
    53U, 251U, 96U, 245U, 202U, 15U, 60U, 160U, 133U, 66U, 251U, 60U, 198U, 65U, 200U, 38U, 58U,
    44U, 171U, 122U, 144U, 238U, 106U, 94U, 21U, 131U, 250U, 194U, 187U, 111U, 107U, 209U
  };

static uint8_t
siggen_vectors256_low20[32U] =
  {
    238U, 89U, 216U, 27U, 201U, 219U, 16U, 85U, 204U, 14U, 217U, 123U, 21U, 157U, 135U, 132U, 175U,
    4U, 233U, 133U, 17U, 208U, 169U, 164U, 7U, 185U, 155U, 178U, 146U, 87U, 46U, 150U
  };

static uint8_t
siggen_vectors256_low21[128U] =
  {
    9U, 137U, 18U, 36U, 16U, 213U, 34U, 175U, 100U, 206U, 176U, 125U, 162U, 200U, 101U, 33U, 144U,
    70U, 180U, 195U, 217U, 217U, 155U, 1U, 39U, 140U, 7U, 255U, 99U, 234U, 241U, 3U, 156U, 183U,
    135U, 174U, 158U, 45U, 212U, 100U, 54U, 204U, 4U, 21U, 242U, 128U, 197U, 98U, 190U, 187U, 131U,
    162U, 62U, 99U, 158U, 71U, 106U, 2U, 236U, 140U, 255U, 126U, 160U, 108U, 209U, 44U, 134U, 220U,
    195U, 173U, 239U, 191U, 26U, 158U, 154U, 155U, 102U, 70U, 199U, 89U, 158U, 198U, 49U, 176U,
    218U, 154U, 96U, 222U, 190U, 185U, 179U, 225U, 147U, 36U, 151U, 127U, 59U, 79U, 54U, 137U, 44U,
    138U, 56U, 103U, 28U, 142U, 28U, 200U, 229U, 15U, 205U, 80U, 249U, 229U, 29U, 234U, 249U, 130U,
    114U, 249U, 38U, 111U, 199U, 2U, 228U, 229U, 124U, 48U
  };

static uint8_t
siggen_vectors256_low22[32U] =
  {
    163U, 210U, 211U, 183U, 89U, 111U, 101U, 146U, 206U, 152U, 180U, 191U, 225U, 13U, 65U, 131U,
    127U, 16U, 2U, 122U, 144U, 215U, 187U, 117U, 52U, 148U, 144U, 1U, 140U, 247U, 45U, 7U
  };

static uint8_t
siggen_vectors256_low23[32U] =
  {
    50U, 47U, 128U, 55U, 27U, 246U, 224U, 68U, 188U, 73U, 57U, 29U, 151U, 193U, 113U, 74U, 184U,
    127U, 153U, 11U, 148U, 155U, 193U, 120U, 203U, 124U, 67U, 183U, 194U, 45U, 137U, 225U
  };

static uint8_t
siggen_vectors256_low24[32U] =
  {
    60U, 21U, 213U, 74U, 92U, 198U, 185U, 240U, 157U, 232U, 69U, 126U, 135U, 62U, 179U, 222U, 177U,
    252U, 235U, 84U, 176U, 178U, 149U, 218U, 96U, 80U, 41U, 79U, 174U, 127U, 217U, 153U
  };

static uint8_t
siggen_vectors256_low25[32U] =
  {
    36U, 252U, 144U, 225U, 218U, 19U, 241U, 126U, 249U, 254U, 132U, 204U, 150U, 185U, 71U, 30U,
    209U, 170U, 172U, 23U, 227U, 164U, 186U, 227U, 58U, 17U, 93U, 244U, 229U, 131U, 79U, 24U
  };

static uint8_t
siggen_vectors256_low26[32U] =
  {
    215U, 197U, 98U, 55U, 10U, 246U, 23U, 181U, 129U, 200U, 74U, 36U, 104U, 204U, 139U, 213U, 11U,
    177U, 203U, 243U, 34U, 222U, 65U, 183U, 136U, 124U, 224U, 124U, 14U, 88U, 132U, 202U
  };

static uint8_t
siggen_vectors256_low27[32U] =
  {
    180U, 109U, 159U, 45U, 140U, 75U, 248U, 53U, 70U, 255U, 23U, 143U, 29U, 120U, 147U, 124U, 0U,
    141U, 100U, 232U, 236U, 197U, 203U, 184U, 37U, 203U, 33U, 217U, 77U, 103U, 13U, 137U
  };

static uint8_t
siggen_vectors256_low28[128U] =
  {
    220U, 102U, 227U, 159U, 155U, 191U, 217U, 134U, 83U, 24U, 83U, 31U, 254U, 146U, 7U, 249U, 52U,
    250U, 97U, 90U, 91U, 40U, 87U, 8U, 165U, 233U, 196U, 107U, 119U, 117U, 21U, 14U, 129U, 141U,
    127U, 36U, 210U, 161U, 35U, 223U, 54U, 114U, 255U, 242U, 9U, 78U, 63U, 211U, 223U, 111U, 190U,
    37U, 158U, 57U, 137U, 221U, 94U, 223U, 204U, 203U, 231U, 212U, 94U, 38U, 167U, 117U, 165U, 196U,
    50U, 154U, 8U, 79U, 5U, 124U, 66U, 193U, 63U, 50U, 72U, 227U, 253U, 111U, 12U, 118U, 103U, 143U,
    137U, 15U, 81U, 60U, 50U, 41U, 45U, 211U, 6U, 234U, 168U, 74U, 89U, 171U, 227U, 75U, 22U, 203U,
    94U, 56U, 208U, 232U, 133U, 82U, 93U, 16U, 51U, 108U, 164U, 67U, 225U, 104U, 42U, 160U, 74U,
    122U, 248U, 50U, 176U, 238U, 228U, 231U
  };

static uint8_t
siggen_vectors256_low29[32U] =
  {
    83U, 160U, 232U, 168U, 254U, 147U, 219U, 1U, 231U, 174U, 148U, 225U, 169U, 136U, 42U, 16U, 46U,
    189U, 7U, 155U, 58U, 83U, 88U, 39U, 213U, 131U, 98U, 108U, 39U, 45U, 40U, 13U
  };

static uint8_t
siggen_vectors256_low30[32U] =
  {
    27U, 206U, 196U, 87U, 14U, 30U, 194U, 67U, 101U, 150U, 184U, 222U, 213U, 143U, 96U, 195U, 177U,
    235U, 198U, 164U, 3U, 188U, 85U, 67U, 4U, 11U, 168U, 41U, 99U, 5U, 114U, 68U
  };

static uint8_t
siggen_vectors256_low31[32U] =
  {
    138U, 246U, 42U, 76U, 104U, 63U, 9U, 107U, 40U, 85U, 131U, 32U, 115U, 123U, 248U, 59U, 153U,
    89U, 164U, 106U, 210U, 82U, 16U, 4U, 239U, 116U, 207U, 133U, 230U, 116U, 148U, 225U
  };

static uint8_t
siggen_vectors256_low32[32U] =
  {
    93U, 131U, 62U, 141U, 36U, 204U, 122U, 64U, 45U, 126U, 231U, 236U, 133U, 42U, 53U, 135U, 205U,
    222U, 180U, 131U, 88U, 206U, 167U, 27U, 11U, 237U, 184U, 250U, 190U, 132U, 224U, 196U
  };

static uint8_t
siggen_vectors256_low33[32U] =
  {
    24U, 202U, 175U, 123U, 102U, 53U, 7U, 168U, 188U, 217U, 146U, 184U, 54U, 222U, 201U, 220U, 87U,
    3U, 192U, 128U, 175U, 94U, 81U, 223U, 163U, 169U, 167U, 195U, 135U, 24U, 38U, 4U
  };

static uint8_t
siggen_vectors256_low34[32U] =
  {
    119U, 198U, 137U, 40U, 172U, 59U, 136U, 217U, 133U, 251U, 67U, 251U, 97U, 95U, 183U, 255U, 69U,
    193U, 139U, 165U, 200U, 26U, 247U, 150U, 198U, 19U, 223U, 169U, 131U, 82U, 210U, 156U
  };

static uint8_t
siggen_vectors256_low35[128U] =
  {
    96U, 9U, 116U, 231U, 216U, 197U, 80U, 142U, 44U, 26U, 171U, 7U, 131U, 173U, 13U, 124U, 68U,
    148U, 171U, 43U, 77U, 162U, 101U, 194U, 254U, 73U, 100U, 33U, 196U, 223U, 35U, 139U, 11U, 226U,
    95U, 37U, 101U, 145U, 87U, 200U, 162U, 37U, 251U, 3U, 149U, 54U, 7U, 247U, 223U, 153U, 106U,
    207U, 212U, 2U, 241U, 71U, 227U, 122U, 238U, 47U, 22U, 147U, 227U, 191U, 28U, 53U, 234U, 179U,
    174U, 54U, 10U, 43U, 217U, 29U, 4U, 98U, 46U, 164U, 127U, 131U, 216U, 99U, 210U, 223U, 236U,
    182U, 24U, 232U, 184U, 189U, 195U, 158U, 23U, 209U, 93U, 103U, 46U, 238U, 3U, 187U, 76U, 226U,
    204U, 92U, 246U, 178U, 23U, 229U, 250U, 243U, 243U, 54U, 253U, 216U, 125U, 151U, 45U, 58U, 139U,
    138U, 89U, 59U, 168U, 89U, 85U, 204U, 157U, 113U
  };

static uint8_t
siggen_vectors256_low36[32U] =
  {
    74U, 241U, 7U, 232U, 226U, 25U, 76U, 131U, 15U, 251U, 113U, 42U, 101U, 81U, 27U, 201U, 24U,
    106U, 19U, 48U, 7U, 133U, 91U, 73U, 171U, 75U, 56U, 51U, 174U, 252U, 74U, 29U
  };

static uint8_t
siggen_vectors256_low37[32U] =
  {
    163U, 46U, 80U, 190U, 61U, 174U, 44U, 139U, 163U, 245U, 228U, 189U, 174U, 20U, 207U, 118U, 69U,
    66U, 13U, 66U, 94U, 173U, 148U, 3U, 108U, 34U, 221U, 108U, 79U, 197U, 158U
  };

static uint8_t
siggen_vectors256_low38[32U] =
  {
    214U, 35U, 191U, 100U, 17U, 96U, 194U, 137U, 214U, 116U, 44U, 98U, 87U, 174U, 107U, 165U, 116U,
    68U, 109U, 209U, 208U, 231U, 77U, 179U, 170U, 168U, 9U, 0U, 183U, 141U, 74U, 233U
  };

static uint8_t
siggen_vectors256_low39[32U] =
  {
    225U, 143U, 150U, 248U, 77U, 250U, 47U, 211U, 205U, 250U, 236U, 145U, 89U, 212U, 195U, 56U,
    205U, 84U, 173U, 49U, 65U, 52U, 240U, 179U, 30U, 32U, 89U, 31U, 194U, 56U, 208U, 171U
  };

static uint8_t
siggen_vectors256_low40[32U] =
  {
    133U, 36U, 197U, 2U, 78U, 45U, 154U, 115U, 189U, 232U, 199U, 45U, 145U, 41U, 245U, 120U, 115U,
    187U, 173U, 14U, 208U, 82U, 21U, 163U, 114U, 168U, 79U, 219U, 199U, 143U, 46U, 104U
  };

static uint8_t
siggen_vectors256_low41[32U] =
  {
    209U, 140U, 44U, 175U, 59U, 16U, 114U, 248U, 112U, 100U, 236U, 94U, 137U, 83U, 245U, 19U, 1U,
    202U, 218U, 3U, 70U, 156U, 100U, 2U, 68U, 118U, 3U, 40U, 235U, 90U, 5U, 203U
  };

static uint8_t
siggen_vectors256_low42[128U] =
  {
    223U, 166U, 203U, 155U, 57U, 173U, 218U, 108U, 116U, 204U, 139U, 42U, 139U, 83U, 161U, 44U, 73U,
    154U, 185U, 222U, 224U, 27U, 65U, 35U, 100U, 43U, 79U, 17U, 175U, 51U, 106U, 145U, 165U, 201U,
    206U, 5U, 32U, 235U, 35U, 149U, 166U, 25U, 14U, 203U, 246U, 22U, 156U, 76U, 186U, 129U, 148U,
    29U, 232U, 231U, 108U, 156U, 144U, 142U, 184U, 67U, 185U, 140U, 233U, 94U, 13U, 162U, 156U, 93U,
    67U, 136U, 4U, 2U, 100U, 224U, 94U, 7U, 3U, 10U, 87U, 124U, 197U, 209U, 118U, 56U, 113U, 84U,
    234U, 186U, 226U, 175U, 82U, 168U, 62U, 133U, 198U, 28U, 124U, 97U, 218U, 147U, 12U, 155U, 25U,
    228U, 93U, 126U, 52U, 200U, 81U, 109U, 195U, 194U, 56U, 253U, 221U, 110U, 69U, 10U, 119U, 69U,
    93U, 83U, 76U, 72U, 161U, 82U, 1U, 11U
  };

static uint8_t
siggen_vectors256_low43[32U] =
  {
    120U, 223U, 170U, 9U, 241U, 7U, 104U, 80U, 179U, 226U, 6U, 228U, 119U, 73U, 76U, 221U, 207U,
    184U, 34U, 170U, 160U, 18U, 132U, 117U, 5U, 53U, 146U, 196U, 142U, 186U, 244U, 171U
  };

static uint8_t
siggen_vectors256_low44[32U] =
  {
    139U, 207U, 226U, 167U, 33U, 202U, 109U, 117U, 57U, 104U, 245U, 100U, 236U, 67U, 21U, 190U, 72U,
    87U, 226U, 139U, 239U, 25U, 8U, 246U, 26U, 54U, 107U, 31U, 3U, 201U, 116U, 121U
  };

static uint8_t
siggen_vectors256_low45[32U] =
  {
    15U, 103U, 87U, 106U, 48U, 184U, 226U, 13U, 66U, 50U, 216U, 83U, 11U, 82U, 251U, 76U, 137U,
    203U, 197U, 137U, 237U, 226U, 145U, 228U, 153U, 221U, 209U, 95U, 232U, 112U, 171U, 150U
  };

static uint8_t
siggen_vectors256_low46[32U] =
  {
    41U, 85U, 68U, 219U, 178U, 218U, 61U, 161U, 112U, 116U, 28U, 155U, 44U, 101U, 81U, 212U, 10U,
    247U, 237U, 78U, 137U, 20U, 69U, 241U, 26U, 2U, 182U, 106U, 92U, 37U, 138U, 119U
  };

static uint8_t
siggen_vectors256_low47[32U] =
  {
    197U, 161U, 134U, 215U, 45U, 244U, 82U, 1U, 84U, 128U, 247U, 243U, 56U, 151U, 11U, 254U, 130U,
    80U, 135U, 240U, 92U, 0U, 136U, 217U, 83U, 5U, 248U, 122U, 172U, 201U, 178U, 84U
  };

static uint8_t
siggen_vectors256_low48[32U] =
  {
    132U, 165U, 143U, 158U, 157U, 158U, 115U, 83U, 68U, 179U, 22U, 177U, 170U, 26U, 181U, 24U, 86U,
    101U, 184U, 81U, 71U, 220U, 130U, 217U, 46U, 150U, 157U, 123U, 238U, 49U, 202U, 48U
  };

static uint8_t
siggen_vectors256_low49[128U] =
  {
    81U, 210U, 84U, 124U, 191U, 249U, 36U, 49U, 23U, 74U, 167U, 252U, 115U, 2U, 19U, 149U, 25U,
    217U, 128U, 113U, 199U, 85U, 255U, 28U, 146U, 228U, 105U, 75U, 88U, 88U, 126U, 165U, 96U, 247U,
    47U, 50U, 252U, 109U, 212U, 222U, 231U, 210U, 43U, 183U, 56U, 115U, 129U, 208U, 37U, 110U, 40U,
    98U, 208U, 100U, 76U, 223U, 44U, 39U, 124U, 93U, 116U, 15U, 160U, 137U, 131U, 14U, 181U, 43U,
    247U, 157U, 30U, 117U, 184U, 89U, 110U, 207U, 14U, 165U, 138U, 11U, 157U, 246U, 30U, 12U, 151U,
    84U, 191U, 205U, 98U, 239U, 171U, 110U, 161U, 189U, 33U, 107U, 241U, 129U, 197U, 89U, 61U, 167U,
    159U, 16U, 19U, 90U, 155U, 198U, 225U, 100U, 241U, 133U, 75U, 200U, 133U, 151U, 52U, 52U, 26U,
    173U, 35U, 123U, 162U, 154U, 129U, 163U, 252U, 139U
  };

static uint8_t
siggen_vectors256_low50[32U] =
  {
    128U, 230U, 146U, 227U, 235U, 159U, 205U, 140U, 125U, 68U, 231U, 222U, 159U, 122U, 89U, 82U,
    104U, 100U, 7U, 249U, 0U, 37U, 161U, 216U, 126U, 82U, 199U, 9U, 106U, 98U, 97U, 138U
  };

static uint8_t
siggen_vectors256_low51[32U] =
  {
    168U, 139U, 200U, 67U, 2U, 121U, 200U, 192U, 64U, 10U, 119U, 215U, 81U, 242U, 108U, 10U, 188U,
    147U, 229U, 222U, 74U, 217U, 164U, 22U, 99U, 87U, 149U, 47U, 224U, 65U, 231U, 103U
  };

static uint8_t
siggen_vectors256_low52[32U] =
  {
    45U, 54U, 90U, 30U, 239U, 37U, 234U, 213U, 121U, 204U, 154U, 6U, 155U, 106U, 188U, 27U, 22U,
    184U, 28U, 53U, 241U, 135U, 133U, 206U, 38U, 161U, 11U, 166U, 209U, 56U, 17U, 133U
  };

static uint8_t
siggen_vectors256_low53[32U] =
  {
    124U, 128U, 253U, 102U, 214U, 44U, 192U, 118U, 206U, 242U, 208U, 48U, 193U, 124U, 10U, 105U,
    201U, 150U, 17U, 84U, 156U, 179U, 44U, 79U, 246U, 98U, 71U, 90U, 219U, 232U, 75U, 34U
  };

static uint8_t
siggen_vectors256_low54[32U] =
  {
    157U, 12U, 106U, 251U, 109U, 243U, 188U, 237U, 69U, 91U, 69U, 156U, 194U, 19U, 135U, 225U, 73U,
    41U, 57U, 38U, 100U, 187U, 135U, 65U, 163U, 105U, 58U, 23U, 149U, 202U, 105U, 2U
  };

static uint8_t
siggen_vectors256_low55[32U] =
  {
    215U, 249U, 221U, 209U, 145U, 241U, 244U, 18U, 134U, 148U, 41U, 32U, 158U, 227U, 129U, 76U,
    117U, 199U, 47U, 164U, 106U, 156U, 204U, 248U, 4U, 162U, 245U, 204U, 11U, 126U, 115U, 159U
  };

static uint8_t
siggen_vectors256_low56[128U] =
  {
    85U, 140U, 42U, 193U, 48U, 38U, 64U, 43U, 173U, 74U, 10U, 131U, 235U, 201U, 70U, 142U, 80U,
    247U, 255U, 171U, 6U, 214U, 249U, 129U, 229U, 219U, 29U, 8U, 32U, 152U, 6U, 91U, 207U, 246U,
    242U, 26U, 122U, 116U, 85U, 139U, 30U, 134U, 18U, 145U, 75U, 139U, 90U, 10U, 162U, 142U, 213U,
    181U, 116U, 195U, 106U, 196U, 234U, 88U, 104U, 67U, 42U, 98U, 187U, 142U, 240U, 105U, 93U, 39U,
    193U, 227U, 206U, 175U, 117U, 199U, 178U, 81U, 198U, 93U, 219U, 38U, 134U, 150U, 240U, 124U,
    22U, 210U, 118U, 121U, 115U, 216U, 91U, 235U, 68U, 63U, 33U, 30U, 100U, 69U, 231U, 254U, 93U,
    70U, 240U, 220U, 231U, 13U, 88U, 164U, 205U, 159U, 231U, 6U, 136U, 192U, 53U, 104U, 142U, 168U,
    198U, 186U, 236U, 101U, 165U, 252U, 126U, 44U, 147U, 232U
  };

static uint8_t
siggen_vectors256_low57[32U] =
  {
    94U, 102U, 108U, 13U, 176U, 33U, 76U, 59U, 98U, 122U, 142U, 72U, 84U, 28U, 200U, 74U, 139U,
    111U, 209U, 95U, 48U, 13U, 164U, 223U, 245U, 209U, 138U, 236U, 108U, 85U, 184U, 129U
  };

static uint8_t
siggen_vectors256_low58[32U] =
  {
    27U, 196U, 135U, 87U, 15U, 4U, 13U, 201U, 65U, 150U, 201U, 190U, 254U, 138U, 178U, 182U, 222U,
    119U, 32U, 139U, 31U, 56U, 189U, 170U, 226U, 143U, 150U, 69U, 196U, 210U, 188U, 58U
  };

static uint8_t
siggen_vectors256_low59[32U] =
  {
    236U, 129U, 96U, 42U, 189U, 131U, 69U, 231U, 24U, 103U, 200U, 33U, 3U, 19U, 115U, 120U, 101U,
    184U, 170U, 24U, 104U, 81U, 225U, 180U, 142U, 172U, 161U, 64U, 50U, 15U, 93U, 143U
  };

static uint8_t
siggen_vectors256_low60[32U] =
  {
    46U, 118U, 37U, 164U, 136U, 116U, 216U, 108U, 158U, 70U, 127U, 137U, 10U, 170U, 124U, 214U,
    235U, 223U, 113U, 192U, 16U, 43U, 253U, 207U, 162U, 69U, 101U, 214U, 175U, 63U, 220U, 233U
  };

static uint8_t
siggen_vectors256_low61[32U] =
  {
    47U, 158U, 43U, 78U, 159U, 116U, 124U, 101U, 127U, 112U, 91U, 255U, 209U, 36U, 238U, 23U, 139U,
    188U, 83U, 145U, 200U, 109U, 5U, 103U, 23U, 177U, 64U, 193U, 83U, 87U, 15U, 217U
  };

static uint8_t
siggen_vectors256_low62[32U] =
  {
    245U, 65U, 59U, 253U, 133U, 148U, 157U, 168U, 216U, 61U, 232U, 58U, 176U, 209U, 155U, 41U, 134U,
    97U, 62U, 34U, 77U, 25U, 1U, 215U, 105U, 25U, 222U, 35U, 204U, 208U, 49U, 153U
  };

static uint8_t
siggen_vectors256_low63[128U] =
  {
    77U, 85U, 201U, 158U, 246U, 189U, 84U, 98U, 22U, 98U, 195U, 209U, 16U, 195U, 203U, 98U, 124U,
    3U, 214U, 49U, 19U, 147U, 178U, 100U, 171U, 151U, 185U, 10U, 75U, 21U, 33U, 74U, 85U, 147U,
    186U, 37U, 16U, 165U, 61U, 99U, 251U, 52U, 190U, 37U, 31U, 172U, 182U, 151U, 201U, 115U, 225U,
    27U, 102U, 92U, 183U, 146U, 15U, 22U, 132U, 176U, 3U, 27U, 77U, 211U, 112U, 203U, 146U, 124U,
    167U, 22U, 139U, 11U, 248U, 173U, 40U, 94U, 5U, 233U, 227U, 30U, 52U, 188U, 36U, 2U, 71U, 57U,
    253U, 193U, 11U, 120U, 88U, 111U, 41U, 239U, 249U, 68U, 18U, 3U, 78U, 59U, 96U, 110U, 216U, 80U,
    236U, 44U, 25U, 0U, 232U, 230U, 129U, 81U, 252U, 74U, 238U, 90U, 222U, 187U, 6U, 110U, 182U,
    218U, 78U, 170U, 86U, 129U, 55U, 142U
  };

static uint8_t
siggen_vectors256_low64[32U] =
  {
    247U, 63U, 69U, 82U, 113U, 200U, 119U, 196U, 213U, 51U, 70U, 39U, 227U, 124U, 39U, 143U, 104U,
    209U, 67U, 1U, 75U, 10U, 5U, 170U, 98U, 243U, 8U, 178U, 16U, 28U, 83U, 8U
  };

static uint8_t
siggen_vectors256_low65[32U] =
  {
    184U, 24U, 139U, 214U, 135U, 1U, 252U, 57U, 109U, 171U, 83U, 18U, 93U, 77U, 40U, 234U, 51U,
    169U, 29U, 175U, 109U, 33U, 72U, 95U, 71U, 112U, 246U, 234U, 140U, 86U, 93U, 222U
  };

static uint8_t
siggen_vectors256_low66[32U] =
  {
    66U, 63U, 5U, 136U, 16U, 242U, 119U, 248U, 254U, 7U, 111U, 109U, 181U, 110U, 146U, 133U, 161U,
    191U, 44U, 42U, 29U, 174U, 20U, 80U, 149U, 237U, 217U, 192U, 73U, 112U, 188U, 74U
  };

static uint8_t
siggen_vectors256_low67[32U] =
  {
    98U, 248U, 102U, 95U, 214U, 226U, 107U, 63U, 160U, 105U, 232U, 82U, 129U, 119U, 122U, 155U, 31U,
    13U, 253U, 44U, 11U, 159U, 84U, 160U, 134U, 208U, 193U, 9U, 255U, 159U, 214U, 21U
  };

static uint8_t
siggen_vectors256_low68[32U] =
  {
    28U, 198U, 40U, 83U, 61U, 0U, 4U, 178U, 178U, 14U, 127U, 75U, 170U, 208U, 184U, 187U, 94U, 6U,
    115U, 219U, 21U, 155U, 188U, 207U, 146U, 73U, 26U, 239U, 97U, 252U, 150U, 32U
  };

static uint8_t
siggen_vectors256_low69[32U] =
  {
    136U, 14U, 11U, 191U, 130U, 168U, 207U, 129U, 142U, 212U, 107U, 160U, 60U, 240U, 252U, 108U,
    137U, 142U, 54U, 252U, 163U, 108U, 199U, 253U, 177U, 210U, 219U, 117U, 3U, 99U, 68U, 48U
  };

static uint8_t
siggen_vectors256_low70[128U] =
  {
    248U, 36U, 138U, 212U, 125U, 151U, 193U, 140U, 152U, 79U, 31U, 92U, 16U, 149U, 13U, 193U, 64U,
    71U, 19U, 197U, 107U, 110U, 163U, 151U, 224U, 30U, 109U, 217U, 37U, 233U, 3U, 180U, 250U, 223U,
    226U, 201U, 232U, 119U, 22U, 158U, 113U, 206U, 60U, 127U, 229U, 206U, 112U, 238U, 66U, 85U,
    217U, 205U, 194U, 111U, 105U, 67U, 191U, 72U, 104U, 120U, 116U, 222U, 100U, 246U, 207U, 48U,
    160U, 18U, 81U, 46U, 120U, 123U, 136U, 5U, 155U, 191U, 86U, 17U, 98U, 189U, 204U, 35U, 163U,
    116U, 44U, 131U, 90U, 193U, 68U, 204U, 20U, 22U, 123U, 27U, 214U, 114U, 126U, 148U, 5U, 64U,
    169U, 201U, 159U, 60U, 187U, 65U, 251U, 29U, 203U, 0U, 215U, 109U, 218U, 4U, 153U, 88U, 71U,
    198U, 87U, 244U, 193U, 157U, 48U, 62U, 176U, 158U, 180U, 138U
  };

static uint8_t
siggen_vectors256_low71[32U] =
  {
    178U, 13U, 112U, 93U, 155U, 215U, 194U, 184U, 220U, 96U, 57U, 58U, 83U, 87U, 246U, 50U, 153U,
    14U, 89U, 154U, 9U, 117U, 87U, 58U, 198U, 127U, 216U, 155U, 73U, 24U, 121U, 6U
  };

static uint8_t
siggen_vectors256_low72[32U] =
  {
    81U, 249U, 157U, 45U, 82U, 212U, 166U, 231U, 52U, 72U, 74U, 1U, 139U, 124U, 162U, 248U, 149U,
    194U, 146U, 155U, 103U, 84U, 163U, 160U, 50U, 36U, 208U, 122U, 230U, 17U, 102U, 206U
  };

static uint8_t
siggen_vectors256_low73[32U] =
  {
    71U, 55U, 218U, 150U, 60U, 110U, 247U, 36U, 127U, 184U, 141U, 25U, 249U, 176U, 198U, 103U, 202U,
    199U, 254U, 18U, 131U, 127U, 218U, 184U, 140U, 102U, 241U, 13U, 60U, 20U, 202U, 209U
  };

static uint8_t
siggen_vectors256_low74[32U] =
  {
    114U, 182U, 86U, 246U, 179U, 91U, 156U, 203U, 199U, 18U, 201U, 241U, 243U, 177U, 161U, 76U,
    187U, 235U, 174U, 196U, 28U, 75U, 202U, 141U, 161U, 143U, 73U, 42U, 6U, 45U, 111U, 111U
  };

static uint8_t
siggen_vectors256_low75[32U] =
  {
    152U, 134U, 174U, 70U, 193U, 65U, 92U, 59U, 201U, 89U, 232U, 43U, 118U, 10U, 215U, 96U, 170U,
    182U, 104U, 133U, 168U, 78U, 98U, 10U, 163U, 57U, 253U, 241U, 2U, 70U, 92U, 66U
  };

static uint8_t
siggen_vectors256_low76[32U] =
  {
    43U, 243U, 168U, 11U, 192U, 79U, 170U, 53U, 235U, 236U, 192U, 244U, 134U, 74U, 192U, 45U, 52U,
    159U, 111U, 18U, 110U, 15U, 152U, 133U, 1U, 184U, 211U, 7U, 84U, 9U, 162U, 108U
  };

static uint8_t
siggen_vectors256_low77[128U] =
  {
    59U, 110U, 226U, 66U, 89U, 64U, 179U, 210U, 64U, 211U, 91U, 151U, 182U, 220U, 214U, 30U, 211U,
    66U, 61U, 142U, 113U, 160U, 173U, 163U, 93U, 71U, 179U, 34U, 209U, 123U, 53U, 234U, 4U, 114U,
    243U, 94U, 221U, 29U, 37U, 47U, 135U, 184U, 182U, 94U, 244U, 183U, 22U, 102U, 159U, 201U, 172U,
    40U, 176U, 13U, 52U, 169U, 214U, 106U, 209U, 24U, 201U, 217U, 78U, 127U, 70U, 208U, 180U, 246U,
    194U, 178U, 211U, 57U, 253U, 107U, 205U, 53U, 18U, 65U, 163U, 135U, 204U, 130U, 96U, 144U, 87U,
    4U, 140U, 18U, 196U, 236U, 61U, 133U, 198U, 97U, 151U, 92U, 69U, 179U, 0U, 203U, 150U, 147U,
    13U, 137U, 55U, 10U, 50U, 124U, 152U, 182U, 125U, 239U, 170U, 137U, 73U, 122U, 168U, 239U, 153U,
    76U, 119U, 241U, 19U, 15U, 117U, 47U, 148U, 164U
  };

static uint8_t
siggen_vectors256_low78[32U] =
  {
    212U, 35U, 75U, 235U, 251U, 200U, 33U, 5U, 3U, 65U, 163U, 126U, 18U, 64U, 239U, 229U, 227U, 55U,
    99U, 203U, 187U, 46U, 247U, 106U, 28U, 121U, 226U, 71U, 36U, 229U, 165U, 231U
  };

static uint8_t
siggen_vectors256_low79[32U] =
  {
    143U, 178U, 135U, 240U, 32U, 42U, 213U, 122U, 232U, 65U, 174U, 163U, 95U, 41U, 178U, 225U, 213U,
    62U, 25U, 109U, 13U, 221U, 154U, 236U, 36U, 129U, 61U, 100U, 192U, 146U, 47U, 183U
  };

static uint8_t
siggen_vectors256_low80[32U] =
  {
    31U, 109U, 175U, 241U, 170U, 45U, 210U, 214U, 211U, 116U, 22U, 35U, 238U, 203U, 94U, 123U, 97U,
    41U, 151U, 161U, 3U, 154U, 171U, 46U, 92U, 242U, 222U, 150U, 156U, 254U, 165U, 115U
  };

static uint8_t
siggen_vectors256_low81[32U] =
  {
    217U, 38U, 254U, 16U, 241U, 191U, 217U, 133U, 86U, 16U, 244U, 245U, 163U, 214U, 102U, 177U,
    161U, 73U, 52U, 64U, 87U, 227U, 85U, 55U, 55U, 51U, 114U, 234U, 216U, 177U, 167U, 120U
  };

static uint8_t
siggen_vectors256_low82[32U] =
  {
    73U, 14U, 253U, 16U, 107U, 225U, 31U, 195U, 101U, 199U, 70U, 126U, 184U, 155U, 141U, 57U, 225U,
    93U, 101U, 23U, 83U, 86U, 119U, 93U, 234U, 178U, 17U, 22U, 60U, 37U, 4U, 203U
  };

static uint8_t
siggen_vectors256_low83[32U] =
  {
    100U, 67U, 0U, 252U, 13U, 164U, 212U, 15U, 184U, 198U, 234U, 213U, 16U, 209U, 79U, 11U, 212U,
    225U, 50U, 26U, 70U, 158U, 156U, 10U, 88U, 20U, 100U, 199U, 24U, 107U, 122U, 167U
  };

static uint8_t
siggen_vectors256_low84[128U] =
  {
    197U, 32U, 75U, 129U, 236U, 10U, 77U, 245U, 183U, 233U, 253U, 163U, 220U, 36U, 95U, 152U, 8U,
    42U, 231U, 244U, 239U, 232U, 25U, 152U, 220U, 170U, 40U, 107U, 212U, 80U, 124U, 168U, 64U, 165U,
    61U, 33U, 176U, 30U, 144U, 79U, 85U, 227U, 143U, 120U, 195U, 117U, 125U, 90U, 90U, 74U, 68U,
    177U, 213U, 212U, 228U, 128U, 190U, 58U, 251U, 91U, 57U, 74U, 93U, 40U, 64U, 175U, 66U, 177U,
    180U, 8U, 61U, 64U, 175U, 191U, 226U, 45U, 112U, 47U, 55U, 13U, 50U, 219U, 253U, 57U, 46U, 18U,
    142U, 164U, 114U, 77U, 102U, 163U, 112U, 29U, 164U, 26U, 226U, 240U, 59U, 180U, 217U, 27U, 185U,
    70U, 199U, 150U, 148U, 4U, 203U, 84U, 79U, 113U, 235U, 122U, 73U, 235U, 76U, 78U, 197U, 87U,
    153U, 189U, 161U, 235U, 84U, 81U, 67U, 167U
  };

static uint8_t
siggen_vectors256_low85[32U] =
  {
    181U, 143U, 82U, 17U, 223U, 244U, 64U, 98U, 107U, 181U, 109U, 10U, 212U, 131U, 25U, 61U, 96U,
    108U, 242U, 31U, 54U, 217U, 131U, 5U, 67U, 50U, 114U, 146U, 244U, 210U, 93U, 140U
  };

static uint8_t
siggen_vectors256_low86[32U] =
  {
    104U, 34U, 155U, 72U, 194U, 254U, 25U, 211U, 219U, 3U, 78U, 76U, 21U, 7U, 126U, 183U, 71U, 26U,
    102U, 3U, 31U, 40U, 169U, 128U, 130U, 24U, 115U, 145U, 82U, 152U, 186U, 118U
  };

static uint8_t
siggen_vectors256_low87[32U] =
  {
    48U, 62U, 142U, 227U, 116U, 42U, 137U, 63U, 120U, 184U, 16U, 153U, 29U, 166U, 151U, 8U, 61U,
    216U, 241U, 17U, 40U, 196U, 118U, 81U, 194U, 122U, 86U, 116U, 10U, 128U, 194U, 76U
  };

static uint8_t
siggen_vectors256_low88[32U] =
  {
    225U, 88U, 191U, 74U, 45U, 25U, 169U, 145U, 73U, 217U, 205U, 184U, 121U, 41U, 76U, 203U, 122U,
    174U, 174U, 3U, 215U, 93U, 221U, 97U, 110U, 248U, 174U, 81U, 166U, 220U, 16U, 113U
  };

static uint8_t
siggen_vectors256_low89[32U] =
  {
    230U, 122U, 151U, 23U, 204U, 249U, 104U, 65U, 72U, 157U, 101U, 65U, 244U, 246U, 173U, 177U, 45U,
    23U, 181U, 154U, 107U, 239U, 132U, 123U, 97U, 131U, 184U, 252U, 241U, 106U, 50U, 235U
  };

static uint8_t
siggen_vectors256_low90[32U] =
  {
    154U, 230U, 186U, 109U, 99U, 119U, 6U, 132U, 154U, 106U, 159U, 195U, 136U, 207U, 2U, 50U, 216U,
    92U, 38U, 234U, 13U, 31U, 231U, 67U, 122U, 219U, 72U, 222U, 88U, 54U, 67U, 51U
  };

static uint8_t
siggen_vectors256_low91[128U] =
  {
    114U, 232U, 31U, 226U, 33U, 251U, 64U, 33U, 72U, 216U, 183U, 171U, 3U, 84U, 159U, 17U, 128U,
    188U, 192U, 61U, 65U, 202U, 89U, 215U, 101U, 56U, 1U, 240U, 186U, 133U, 58U, 221U, 31U, 109U,
    41U, 237U, 215U, 249U, 171U, 198U, 33U, 178U, 213U, 72U, 248U, 219U, 248U, 151U, 155U, 209U,
    102U, 8U, 210U, 216U, 252U, 50U, 96U, 180U, 235U, 192U, 221U, 66U, 72U, 36U, 129U, 213U, 72U,
    199U, 7U, 87U, 17U, 181U, 117U, 150U, 73U, 196U, 31U, 67U, 159U, 173U, 105U, 149U, 73U, 86U,
    201U, 50U, 104U, 65U, 234U, 100U, 146U, 149U, 104U, 41U, 249U, 224U, 220U, 120U, 159U, 115U,
    99U, 59U, 64U, 246U, 172U, 119U, 188U, 174U, 109U, 252U, 121U, 48U, 207U, 232U, 158U, 82U, 109U,
    22U, 132U, 54U, 92U, 91U, 11U, 226U, 67U, 127U, 219U, 1U
  };

static uint8_t
siggen_vectors256_low92[32U] =
  {
    84U, 192U, 102U, 113U, 28U, 219U, 6U, 30U, 218U, 7U, 229U, 39U, 95U, 126U, 149U, 169U, 150U,
    44U, 103U, 100U, 184U, 79U, 111U, 31U, 58U, 181U, 165U, 136U, 224U, 162U, 175U, 177U
  };

static uint8_t
siggen_vectors256_low93[32U] =
  {
    10U, 125U, 187U, 139U, 245U, 12U, 182U, 5U, 235U, 34U, 104U, 176U, 129U, 242U, 109U, 107U, 8U,
    224U, 18U, 249U, 82U, 196U, 183U, 10U, 90U, 30U, 110U, 125U, 70U, 175U, 152U, 187U
  };

static uint8_t
siggen_vectors256_low94[32U] =
  {
    242U, 109U, 215U, 215U, 153U, 147U, 0U, 98U, 72U, 8U, 73U, 150U, 44U, 207U, 80U, 4U, 237U, 207U,
    211U, 7U, 192U, 68U, 244U, 232U, 246U, 103U, 201U, 186U, 168U, 52U, 238U, 174U
  };

static uint8_t
siggen_vectors256_low95[32U] =
  {
    100U, 111U, 233U, 51U, 233U, 108U, 59U, 143U, 159U, 80U, 116U, 152U, 233U, 7U, 253U, 210U, 1U,
    240U, 132U, 120U, 208U, 32U, 44U, 117U, 42U, 124U, 44U, 254U, 191U, 77U, 6U, 26U
  };

static uint8_t
siggen_vectors256_low96[32U] =
  {
    181U, 60U, 228U, 218U, 26U, 167U, 192U, 220U, 119U, 161U, 137U, 106U, 183U, 22U, 185U, 33U, 73U,
    154U, 237U, 120U, 223U, 114U, 91U, 21U, 4U, 171U, 161U, 89U, 123U, 160U, 198U, 75U
  };

static uint8_t
siggen_vectors256_low97[32U] =
  {
    215U, 194U, 70U, 220U, 122U, 208U, 230U, 119U, 0U, 195U, 115U, 237U, 207U, 221U, 28U, 10U, 4U,
    149U, 252U, 149U, 69U, 73U, 173U, 87U, 157U, 246U, 237U, 20U, 56U, 132U, 8U, 81U
  };

static uint8_t
siggen_vectors256_low98[128U] =
  {
    33U, 24U, 140U, 62U, 221U, 93U, 224U, 136U, 218U, 204U, 16U, 118U, 185U, 225U, 188U, 236U, 215U,
    157U, 225U, 0U, 60U, 36U, 20U, 195U, 134U, 97U, 115U, 5U, 77U, 200U, 45U, 222U, 133U, 22U, 155U,
    170U, 119U, 153U, 58U, 219U, 32U, 194U, 105U, 246U, 10U, 82U, 38U, 17U, 24U, 40U, 87U, 139U,
    204U, 124U, 41U, 230U, 232U, 210U, 218U, 232U, 24U, 6U, 21U, 44U, 139U, 160U, 198U, 173U, 161U,
    152U, 106U, 25U, 131U, 235U, 238U, 193U, 71U, 58U, 115U, 160U, 71U, 149U, 182U, 49U, 157U, 72U,
    102U, 45U, 64U, 136U, 28U, 23U, 35U, 167U, 6U, 245U, 22U, 254U, 117U, 48U, 15U, 146U, 64U, 138U,
    161U, 220U, 106U, 228U, 40U, 141U, 32U, 70U, 242U, 60U, 26U, 162U, 229U, 75U, 127U, 182U, 68U,
    138U, 13U, 169U, 34U, 189U, 127U, 52U
  };

static uint8_t
siggen_vectors256_low99[32U] =
  {
    52U, 250U, 70U, 130U, 191U, 108U, 181U, 177U, 103U, 131U, 173U, 205U, 24U, 240U, 230U, 135U,
    155U, 146U, 24U, 95U, 118U, 215U, 201U, 32U, 64U, 159U, 144U, 79U, 82U, 45U, 180U, 177U
  };

static uint8_t
siggen_vectors256_low100[32U] =
  {
    16U, 93U, 34U, 217U, 198U, 38U, 82U, 15U, 172U, 161U, 62U, 124U, 237U, 56U, 45U, 203U, 233U,
    52U, 152U, 49U, 95U, 0U, 204U, 10U, 195U, 156U, 72U, 33U, 208U, 215U, 55U, 55U
  };

static uint8_t
siggen_vectors256_low101[32U] =
  {
    108U, 71U, 243U, 203U, 191U, 169U, 125U, 252U, 235U, 225U, 98U, 112U, 184U, 199U, 213U, 211U,
    165U, 144U, 11U, 136U, 140U, 66U, 82U, 13U, 117U, 30U, 143U, 175U, 59U, 64U, 30U, 244U
  };

static uint8_t
siggen_vectors256_low102[32U] =
  {
    166U, 244U, 99U, 238U, 114U, 201U, 73U, 43U, 199U, 146U, 254U, 152U, 22U, 49U, 18U, 131U, 122U,
    235U, 208U, 123U, 171U, 122U, 132U, 170U, 237U, 5U, 190U, 100U, 219U, 48U, 134U, 244U
  };

static uint8_t
siggen_vectors256_low103[32U] =
  {
    84U, 44U, 64U, 161U, 129U, 64U, 166U, 38U, 109U, 111U, 2U, 134U, 226U, 78U, 154U, 123U, 173U,
    118U, 80U, 231U, 46U, 240U, 226U, 19U, 30U, 98U, 156U, 7U, 109U, 150U, 38U, 99U
  };

static uint8_t
siggen_vectors256_low104[32U] =
  {
    79U, 127U, 101U, 48U, 94U, 36U, 166U, 187U, 181U, 207U, 247U, 20U, 186U, 143U, 90U, 44U, 238U,
    91U, 220U, 137U, 186U, 141U, 117U, 220U, 191U, 33U, 150U, 108U, 227U, 142U, 182U, 111U
  };

typedef struct
__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_s
{
  lbuffer__uint8_t fst;
  lbuffer__uint8_t snd;
  lbuffer__uint8_t thd;
  lbuffer__uint8_t f3;
  lbuffer__uint8_t f4;
  lbuffer__uint8_t f5;
  lbuffer__uint8_t f6;
}
__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t;

static __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors256_low105[15U] =
  {
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low0 },
        .snd = { .len = 32U, .b = siggen_vectors256_low1 },
        .thd = { .len = 32U, .b = siggen_vectors256_low2 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low3 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low4 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low5 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low6 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low7 },
        .snd = { .len = 32U, .b = siggen_vectors256_low8 },
        .thd = { .len = 32U, .b = siggen_vectors256_low9 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low10 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low11 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low12 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low13 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low14 },
        .snd = { .len = 32U, .b = siggen_vectors256_low15 },
        .thd = { .len = 32U, .b = siggen_vectors256_low16 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low17 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low18 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low19 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low20 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low21 },
        .snd = { .len = 32U, .b = siggen_vectors256_low22 },
        .thd = { .len = 32U, .b = siggen_vectors256_low23 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low24 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low25 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low26 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low27 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low28 },
        .snd = { .len = 32U, .b = siggen_vectors256_low29 },
        .thd = { .len = 32U, .b = siggen_vectors256_low30 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low31 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low32 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low33 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low34 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low35 },
        .snd = { .len = 32U, .b = siggen_vectors256_low36 },
        .thd = { .len = 32U, .b = siggen_vectors256_low37 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low38 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low39 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low40 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low41 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low42 },
        .snd = { .len = 32U, .b = siggen_vectors256_low43 },
        .thd = { .len = 32U, .b = siggen_vectors256_low44 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low45 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low46 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low47 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low48 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low49 },
        .snd = { .len = 32U, .b = siggen_vectors256_low50 },
        .thd = { .len = 32U, .b = siggen_vectors256_low51 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low52 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low53 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low54 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low55 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low56 },
        .snd = { .len = 32U, .b = siggen_vectors256_low57 },
        .thd = { .len = 32U, .b = siggen_vectors256_low58 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low59 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low60 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low61 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low62 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low63 },
        .snd = { .len = 32U, .b = siggen_vectors256_low64 },
        .thd = { .len = 32U, .b = siggen_vectors256_low65 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low66 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low67 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low68 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low69 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low70 },
        .snd = { .len = 32U, .b = siggen_vectors256_low71 },
        .thd = { .len = 32U, .b = siggen_vectors256_low72 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low73 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low74 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low75 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low76 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low77 },
        .snd = { .len = 32U, .b = siggen_vectors256_low78 },
        .thd = { .len = 32U, .b = siggen_vectors256_low79 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low80 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low81 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low82 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low83 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low84 },
        .snd = { .len = 32U, .b = siggen_vectors256_low85 },
        .thd = { .len = 32U, .b = siggen_vectors256_low86 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low87 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low88 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low89 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low90 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low91 },
        .snd = { .len = 32U, .b = siggen_vectors256_low92 },
        .thd = { .len = 32U, .b = siggen_vectors256_low93 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low94 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low95 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low96 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low97 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors256_low98 },
        .snd = { .len = 32U, .b = siggen_vectors256_low99 },
        .thd = { .len = 32U, .b = siggen_vectors256_low100 },
        .f3 = { .len = 32U, .b = siggen_vectors256_low101 },
        .f4 = { .len = 32U, .b = siggen_vectors256_low102 },
        .f5 = { .len = 32U, .b = siggen_vectors256_low103 },
        .f6 = { .len = 32U, .b = siggen_vectors256_low104 }
      }
    )
  };

typedef struct
lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_s
{
  uint32_t len;
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  *b;
}
lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t;

static lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors256_low = { .len = 15U, .b = siggen_vectors256_low105 };

static uint8_t
siggen_vectors384_low0[128U] =
  {
    224U, 184U, 89U, 107U, 55U, 95U, 51U, 6U, 187U, 198U, 231U, 122U, 11U, 66U, 247U, 70U, 157U,
    126U, 131U, 99U, 89U, 144U, 231U, 74U, 166U, 215U, 19U, 89U, 74U, 58U, 36U, 73U, 143U, 239U,
    245U, 0U, 103U, 144U, 116U, 45U, 156U, 46U, 155U, 71U, 215U, 20U, 190U, 233U, 50U, 67U, 93U,
    183U, 71U, 198U, 231U, 51U, 227U, 216U, 222U, 65U, 242U, 249U, 19U, 17U, 242U, 233U, 253U, 142U,
    2U, 86U, 81U, 99U, 31U, 253U, 132U, 246U, 103U, 50U, 211U, 71U, 63U, 189U, 22U, 39U, 230U, 61U,
    199U, 25U, 64U, 72U, 235U, 236U, 147U, 201U, 92U, 21U, 155U, 80U, 57U, 171U, 94U, 121U, 228U,
    44U, 128U, 180U, 132U, 169U, 67U, 241U, 37U, 222U, 61U, 161U, 224U, 78U, 91U, 249U, 193U, 102U,
    113U, 173U, 85U, 161U, 17U, 125U, 51U, 6U
  };

static uint8_t
siggen_vectors384_low1[32U] =
  {
    182U, 250U, 242U, 200U, 146U, 34U, 53U, 197U, 137U, 194U, 115U, 104U, 163U, 179U, 230U, 226U,
    244U, 46U, 182U, 7U, 59U, 249U, 80U, 127U, 25U, 238U, 208U, 116U, 108U, 121U, 220U, 237U
  };

static uint8_t
siggen_vectors384_low2[32U] =
  {
    224U, 231U, 185U, 155U, 198U, 45U, 141U, 214U, 120U, 131U, 227U, 158U, 217U, 250U, 6U, 87U,
    120U, 156U, 95U, 245U, 86U, 204U, 31U, 216U, 221U, 30U, 42U, 85U, 233U, 227U, 242U, 67U
  };

static uint8_t
siggen_vectors384_low3[32U] =
  {
    99U, 251U, 253U, 2U, 50U, 185U, 85U, 120U, 7U, 92U, 144U, 58U, 77U, 191U, 133U, 173U, 88U, 248U,
    53U, 5U, 22U, 225U, 236U, 137U, 176U, 238U, 31U, 94U, 19U, 98U, 218U, 105U
  };

static uint8_t
siggen_vectors384_low4[32U] =
  {
    153U, 128U, 185U, 205U, 252U, 239U, 58U, 184U, 226U, 25U, 185U, 130U, 126U, 214U, 175U, 221U,
    77U, 191U, 32U, 189U, 146U, 126U, 156U, 208U, 31U, 21U, 118U, 39U, 3U, 72U, 112U, 7U
  };

static uint8_t
siggen_vectors384_low5[32U] =
  {
    245U, 8U, 120U, 120U, 226U, 18U, 183U, 3U, 87U, 143U, 92U, 102U, 244U, 52U, 136U, 63U, 62U,
    244U, 20U, 220U, 35U, 226U, 232U, 216U, 171U, 106U, 141U, 21U, 158U, 213U, 173U, 131U
  };

static uint8_t
siggen_vectors384_low6[32U] =
  {
    48U, 107U, 76U, 108U, 32U, 33U, 55U, 7U, 152U, 45U, 255U, 187U, 48U, 251U, 169U, 155U, 150U,
    231U, 146U, 22U, 61U, 213U, 157U, 190U, 96U, 110U, 115U, 67U, 40U, 221U, 124U, 138U
  };

static uint8_t
siggen_vectors384_low7[128U] =
  {
    9U, 154U, 1U, 49U, 23U, 159U, 255U, 76U, 105U, 40U, 228U, 152U, 134U, 210U, 253U, 179U, 169U,
    242U, 57U, 183U, 221U, 95U, 168U, 40U, 165U, 44U, 187U, 227U, 252U, 250U, 190U, 207U, 187U,
    163U, 225U, 146U, 21U, 155U, 136U, 123U, 93U, 19U, 170U, 30U, 20U, 230U, 160U, 124U, 203U, 178U,
    31U, 106U, 216U, 183U, 232U, 143U, 238U, 107U, 234U, 155U, 134U, 222U, 164U, 15U, 251U, 150U,
    47U, 56U, 85U, 64U, 86U, 251U, 124U, 91U, 180U, 134U, 65U, 137U, 21U, 247U, 231U, 233U, 185U,
    3U, 63U, 227U, 186U, 175U, 154U, 6U, 157U, 185U, 139U, 192U, 47U, 168U, 175U, 61U, 61U, 24U,
    89U, 161U, 19U, 117U, 214U, 249U, 138U, 162U, 206U, 99U, 38U, 6U, 208U, 128U, 13U, 255U, 127U,
    85U, 180U, 15U, 151U, 26U, 133U, 134U, 237U, 107U, 57U, 233U
  };

static uint8_t
siggen_vectors384_low8[32U] =
  {
    17U, 137U, 88U, 253U, 15U, 240U, 240U, 176U, 237U, 17U, 211U, 207U, 143U, 166U, 100U, 188U, 23U,
    205U, 181U, 254U, 209U, 244U, 168U, 252U, 82U, 208U, 177U, 174U, 48U, 65U, 33U, 129U
  };

static uint8_t
siggen_vectors384_low9[32U] =
  {
    175U, 218U, 130U, 38U, 12U, 159U, 66U, 18U, 42U, 63U, 17U, 198U, 5U, 136U, 57U, 72U, 143U, 109U,
    121U, 119U, 246U, 242U, 162U, 99U, 198U, 125U, 6U, 226U, 126U, 162U, 195U, 85U
  };

static uint8_t
siggen_vectors384_low10[32U] =
  {
    10U, 226U, 187U, 221U, 34U, 7U, 197U, 144U, 51U, 44U, 91U, 254U, 180U, 200U, 181U, 177U, 102U,
    34U, 19U, 75U, 212U, 220U, 85U, 56U, 42U, 232U, 6U, 67U, 84U, 104U, 5U, 139U
  };

static uint8_t
siggen_vectors384_low11[32U] =
  {
    35U, 18U, 154U, 153U, 238U, 218U, 61U, 153U, 164U, 74U, 87U, 120U, 164U, 110U, 142U, 117U, 104U,
    185U, 28U, 49U, 251U, 122U, 134U, 40U, 197U, 217U, 130U, 13U, 75U, 237U, 74U, 107U
  };

static uint8_t
siggen_vectors384_low12[32U] =
  {
    228U, 70U, 96U, 12U, 171U, 18U, 134U, 235U, 195U, 187U, 51U, 32U, 18U, 162U, 245U, 204U, 51U,
    176U, 165U, 239U, 114U, 145U, 213U, 166U, 42U, 132U, 222U, 89U, 105U, 215U, 121U, 70U
  };

static uint8_t
siggen_vectors384_low13[32U] =
  {
    207U, 137U, 177U, 39U, 147U, 238U, 23U, 146U, 235U, 38U, 40U, 59U, 72U, 250U, 11U, 220U, 180U,
    90U, 230U, 246U, 173U, 75U, 2U, 86U, 75U, 247U, 134U, 187U, 151U, 5U, 125U, 90U
  };

static uint8_t
siggen_vectors384_low14[128U] =
  {
    15U, 188U, 7U, 234U, 148U, 124U, 148U, 107U, 234U, 38U, 175U, 161U, 12U, 81U, 81U, 16U, 57U,
    185U, 77U, 219U, 196U, 226U, 228U, 24U, 76U, 163U, 85U, 146U, 96U, 218U, 36U, 161U, 69U, 34U,
    209U, 73U, 124U, 165U, 231U, 122U, 93U, 26U, 142U, 134U, 88U, 58U, 238U, 161U, 245U, 212U, 255U,
    155U, 4U, 166U, 170U, 13U, 231U, 156U, 216U, 143U, 219U, 133U, 224U, 31U, 23U, 17U, 67U, 83U,
    95U, 47U, 124U, 35U, 176U, 80U, 40U, 157U, 126U, 5U, 206U, 188U, 205U, 209U, 49U, 136U, 133U,
    114U, 83U, 75U, 174U, 0U, 97U, 189U, 204U, 48U, 21U, 32U, 107U, 146U, 112U, 176U, 213U, 175U,
    159U, 29U, 162U, 249U, 222U, 145U, 119U, 45U, 23U, 138U, 99U, 44U, 50U, 97U, 161U, 231U, 179U,
    251U, 37U, 86U, 8U, 179U, 128U, 25U, 98U, 249U
  };

static uint8_t
siggen_vectors384_low15[32U] =
  {
    62U, 100U, 115U, 87U, 205U, 91U, 117U, 79U, 173U, 15U, 219U, 135U, 110U, 175U, 155U, 26U, 189U,
    123U, 96U, 83U, 111U, 56U, 60U, 129U, 206U, 87U, 69U, 236U, 128U, 130U, 100U, 49U
  };

static uint8_t
siggen_vectors384_low16[32U] =
  {
    112U, 43U, 44U, 148U, 208U, 57U, 229U, 144U, 221U, 92U, 143U, 151U, 54U, 231U, 83U, 207U, 88U,
    36U, 170U, 207U, 51U, 238U, 61U, 231U, 79U, 225U, 245U, 247U, 200U, 88U, 213U, 237U
  };

static uint8_t
siggen_vectors384_low17[32U] =
  {
    12U, 40U, 137U, 78U, 144U, 122U, 249U, 159U, 176U, 209U, 140U, 158U, 152U, 241U, 154U, 200U,
    13U, 215U, 122U, 191U, 164U, 190U, 190U, 69U, 5U, 92U, 8U, 87U, 184U, 42U, 15U, 77U
  };

static uint8_t
siggen_vectors384_low18[32U] =
  {
    155U, 234U, 183U, 114U, 47U, 11U, 203U, 70U, 142U, 95U, 35U, 78U, 7U, 65U, 112U, 166U, 2U, 37U,
    37U, 93U, 228U, 148U, 16U, 132U, 89U, 171U, 223U, 96U, 60U, 110U, 139U, 53U
  };

static uint8_t
siggen_vectors384_low19[32U] =
  {
    196U, 2U, 31U, 183U, 24U, 90U, 7U, 9U, 101U, 71U, 175U, 31U, 176U, 105U, 50U, 227U, 124U, 248U,
    189U, 144U, 207U, 89U, 61U, 234U, 72U, 212U, 134U, 20U, 250U, 35U, 126U, 94U
  };

static uint8_t
siggen_vectors384_low20[32U] =
  {
    127U, 180U, 93U, 9U, 226U, 23U, 43U, 236U, 141U, 62U, 51U, 10U, 160U, 108U, 67U, 251U, 181U,
    246U, 37U, 82U, 84U, 133U, 35U, 78U, 119U, 20U, 183U, 246U, 233U, 43U, 168U, 241U
  };

static uint8_t
siggen_vectors384_low21[128U] =
  {
    30U, 56U, 215U, 80U, 217U, 54U, 216U, 82U, 46U, 157U, 177U, 135U, 63U, 180U, 153U, 107U, 239U,
    151U, 248U, 218U, 60U, 102U, 116U, 161U, 34U, 61U, 41U, 38U, 63U, 18U, 52U, 169U, 11U, 117U,
    23U, 133U, 49U, 100U, 68U, 233U, 186U, 105U, 139U, 200U, 171U, 108U, 208U, 16U, 99U, 141U, 24U,
    44U, 154U, 218U, 212U, 227U, 52U, 178U, 189U, 117U, 41U, 240U, 174U, 142U, 154U, 82U, 173U, 96U,
    245U, 152U, 4U, 178U, 215U, 128U, 237U, 82U, 189U, 211U, 59U, 11U, 245U, 64U, 1U, 71U, 194U,
    139U, 67U, 4U, 229U, 227U, 67U, 69U, 5U, 174U, 124U, 227U, 13U, 75U, 35U, 158U, 126U, 111U, 14U,
    207U, 5U, 139U, 173U, 213U, 179U, 136U, 237U, 219U, 173U, 100U, 210U, 77U, 36U, 48U, 221U, 4U,
    180U, 221U, 238U, 152U, 249U, 114U, 152U, 143U
  };

static uint8_t
siggen_vectors384_low22[32U] =
  {
    118U, 193U, 124U, 46U, 252U, 153U, 137U, 31U, 54U, 151U, 186U, 77U, 113U, 133U, 14U, 88U, 22U,
    161U, 182U, 85U, 98U, 204U, 57U, 161U, 61U, 164U, 182U, 218U, 144U, 81U, 176U, 253U
  };

static uint8_t
siggen_vectors384_low23[32U] =
  {
    209U, 37U, 18U, 233U, 52U, 195U, 103U, 228U, 196U, 56U, 77U, 189U, 1U, 14U, 147U, 65U, 104U,
    64U, 40U, 138U, 11U, 160U, 11U, 41U, 155U, 78U, 124U, 13U, 145U, 87U, 139U, 87U
  };

static uint8_t
siggen_vectors384_low24[32U] =
  {
    235U, 248U, 131U, 86U, 97U, 217U, 181U, 120U, 241U, 141U, 20U, 174U, 74U, 207U, 156U, 53U, 124U,
    13U, 200U, 183U, 17U, 47U, 195U, 40U, 36U, 166U, 133U, 237U, 114U, 117U, 78U, 35U
  };

static uint8_t
siggen_vectors384_low25[32U] =
  {
    119U, 207U, 250U, 111U, 154U, 115U, 144U, 67U, 6U, 249U, 252U, 211U, 246U, 187U, 179U, 127U,
    82U, 215U, 30U, 57U, 147U, 27U, 180U, 174U, 194U, 143U, 155U, 7U, 110U, 67U, 108U, 207U
  };

static uint8_t
siggen_vectors384_low26[32U] =
  {
    77U, 90U, 157U, 149U, 176U, 240U, 156U, 232U, 112U, 75U, 15U, 69U, 123U, 57U, 5U, 158U, 230U,
    6U, 9U, 35U, 16U, 223U, 101U, 211U, 248U, 174U, 122U, 42U, 66U, 76U, 242U, 50U
  };

static uint8_t
siggen_vectors384_low27[32U] =
  {
    125U, 60U, 1U, 76U, 164U, 112U, 167U, 60U, 239U, 29U, 29U, 168U, 111U, 42U, 84U, 17U, 72U, 173U,
    84U, 47U, 188U, 202U, 249U, 20U, 157U, 27U, 11U, 3U, 4U, 65U, 167U, 235U
  };

static uint8_t
siggen_vectors384_low28[128U] =
  {
    171U, 207U, 14U, 15U, 4U, 107U, 46U, 6U, 114U, 209U, 204U, 108U, 10U, 17U, 73U, 5U, 98U, 124U,
    187U, 222U, 253U, 249U, 117U, 47U, 12U, 49U, 102U, 10U, 169U, 95U, 45U, 14U, 222U, 114U, 209U,
    121U, 25U, 169U, 233U, 177U, 173U, 211U, 33U, 49U, 100U, 224U, 201U, 181U, 174U, 60U, 118U,
    241U, 162U, 247U, 157U, 62U, 235U, 68U, 78U, 103U, 65U, 82U, 16U, 25U, 216U, 189U, 92U, 163U,
    145U, 178U, 140U, 16U, 99U, 52U, 127U, 7U, 175U, 207U, 187U, 112U, 91U, 228U, 181U, 34U, 97U,
    193U, 158U, 186U, 241U, 214U, 240U, 84U, 167U, 77U, 134U, 251U, 93U, 9U, 31U, 167U, 242U, 41U,
    69U, 9U, 150U, 183U, 111U, 10U, 218U, 95U, 151U, 123U, 9U, 181U, 132U, 136U, 238U, 191U, 181U,
    245U, 233U, 83U, 154U, 143U, 216U, 150U, 98U, 171U
  };

static uint8_t
siggen_vectors384_low29[32U] =
  {
    103U, 185U, 222U, 166U, 165U, 117U, 181U, 16U, 57U, 153U, 239U, 255U, 206U, 41U, 204U, 166U,
    136U, 199U, 129U, 120U, 42U, 65U, 18U, 159U, 222U, 203U, 206U, 118U, 96U, 129U, 116U, 222U
  };

static uint8_t
siggen_vectors384_low30[32U] =
  {
    180U, 35U, 139U, 2U, 159U, 192U, 183U, 217U, 165U, 40U, 109U, 140U, 41U, 182U, 243U, 213U, 165U,
    105U, 233U, 16U, 141U, 68U, 216U, 137U, 205U, 121U, 92U, 74U, 56U, 89U, 5U, 190U
  };

static uint8_t
siggen_vectors384_low31[32U] =
  {
    140U, 179U, 255U, 248U, 246U, 204U, 167U, 24U, 124U, 106U, 154U, 208U, 162U, 177U, 217U, 244U,
    10U, 224U, 27U, 50U, 167U, 232U, 248U, 196U, 202U, 117U, 215U, 26U, 31U, 255U, 179U, 9U
  };

static uint8_t
siggen_vectors384_low32[32U] =
  {
    208U, 38U, 23U, 242U, 110U, 222U, 53U, 132U, 240U, 175U, 207U, 200U, 149U, 84U, 205U, 251U, 42U,
    225U, 136U, 193U, 146U, 9U, 47U, 221U, 227U, 67U, 99U, 53U, 250U, 254U, 67U, 241U
  };

static uint8_t
siggen_vectors384_low33[32U] =
  {
    38U, 253U, 145U, 71U, 208U, 200U, 100U, 64U, 104U, 159U, 242U, 215U, 85U, 105U, 121U, 86U, 80U,
    20U, 5U, 6U, 151U, 7U, 145U, 201U, 10U, 206U, 9U, 36U, 180U, 79U, 21U, 134U
  };

static uint8_t
siggen_vectors384_low34[32U] =
  {
    0U, 163U, 75U, 0U, 194U, 10U, 128U, 153U, 223U, 75U, 10U, 117U, 124U, 190U, 248U, 254U, 161U,
    203U, 62U, 167U, 206U, 213U, 251U, 247U, 233U, 135U, 247U, 11U, 37U, 238U, 109U, 79U
  };

static uint8_t
siggen_vectors384_low35[128U] =
  {
    220U, 61U, 72U, 132U, 199U, 65U, 164U, 166U, 135U, 89U, 60U, 121U, 251U, 78U, 53U, 197U, 193U,
    60U, 120U, 29U, 202U, 22U, 219U, 86U, 29U, 126U, 57U, 53U, 119U, 247U, 182U, 44U, 164U, 26U,
    110U, 37U, 159U, 193U, 251U, 141U, 12U, 78U, 30U, 6U, 37U, 23U, 160U, 253U, 249U, 85U, 88U,
    183U, 121U, 159U, 32U, 194U, 17U, 121U, 97U, 103U, 149U, 62U, 99U, 114U, 193U, 24U, 41U, 190U,
    236U, 100U, 134U, 157U, 103U, 191U, 62U, 225U, 241U, 69U, 93U, 216U, 122U, 207U, 189U, 188U,
    197U, 151U, 5U, 110U, 127U, 179U, 71U, 161U, 118U, 136U, 173U, 50U, 253U, 167U, 204U, 195U, 87U,
    45U, 167U, 103U, 125U, 114U, 85U, 194U, 97U, 115U, 143U, 7U, 118U, 60U, 212U, 89U, 115U, 199U,
    40U, 198U, 233U, 173U, 190U, 236U, 173U, 195U, 217U, 97U
  };

static uint8_t
siggen_vectors384_low36[32U] =
  {
    236U, 246U, 68U, 234U, 155U, 108U, 58U, 4U, 253U, 254U, 45U, 228U, 253U, 203U, 85U, 253U, 205U,
    252U, 247U, 56U, 192U, 179U, 23U, 101U, 117U, 250U, 145U, 81U, 81U, 148U, 181U, 102U
  };

static uint8_t
siggen_vectors384_low37[32U] =
  {
    195U, 189U, 199U, 199U, 149U, 236U, 148U, 98U, 10U, 44U, 255U, 246U, 20U, 193U, 58U, 51U, 144U,
    165U, 232U, 108U, 137U, 46U, 83U, 162U, 77U, 62U, 210U, 34U, 40U, 188U, 133U, 191U
  };

static uint8_t
siggen_vectors384_low38[32U] =
  {
    112U, 72U, 15U, 197U, 207U, 74U, 172U, 215U, 62U, 36U, 97U, 139U, 97U, 181U, 197U, 108U, 28U,
    237U, 140U, 79U, 27U, 134U, 149U, 128U, 234U, 83U, 142U, 104U, 199U, 166U, 28U, 163U
  };

static uint8_t
siggen_vectors384_low39[32U] =
  {
    83U, 41U, 29U, 81U, 246U, 141U, 154U, 18U, 209U, 220U, 220U, 88U, 137U, 43U, 47U, 120U, 108U,
    193U, 95U, 99U, 31U, 22U, 153U, 125U, 42U, 73U, 186U, 206U, 81U, 53U, 87U, 212U
  };

static uint8_t
siggen_vectors384_low40[32U] =
  {
    168U, 96U, 200U, 178U, 134U, 237U, 249U, 115U, 206U, 76U, 228U, 207U, 110U, 112U, 220U, 155U,
    191U, 56U, 24U, 195U, 108U, 2U, 58U, 132U, 86U, 119U, 169U, 150U, 55U, 5U, 223U, 139U
  };

static uint8_t
siggen_vectors384_low41[32U] =
  {
    86U, 48U, 249U, 134U, 177U, 196U, 94U, 54U, 225U, 39U, 221U, 121U, 50U, 34U, 28U, 66U, 114U,
    168U, 204U, 110U, 37U, 94U, 137U, 240U, 240U, 202U, 78U, 195U, 169U, 247U, 100U, 148U
  };

static uint8_t
siggen_vectors384_low42[128U] =
  {
    113U, 155U, 241U, 145U, 26U, 229U, 181U, 224U, 143U, 29U, 151U, 185U, 42U, 80U, 137U, 192U,
    171U, 157U, 111U, 28U, 23U, 90U, 199U, 25U, 144U, 134U, 174U, 234U, 164U, 22U, 161U, 126U, 109U,
    111U, 132U, 134U, 199U, 17U, 211U, 134U, 242U, 132U, 240U, 150U, 41U, 102U, 137U, 165U, 77U,
    51U, 12U, 142U, 251U, 15U, 95U, 161U, 197U, 186U, 18U, 141U, 50U, 52U, 163U, 218U, 133U, 108U,
    42U, 148U, 102U, 126U, 247U, 16U, 54U, 22U, 166U, 76U, 145U, 49U, 53U, 244U, 225U, 220U, 80U,
    227U, 141U, 170U, 96U, 97U, 15U, 115U, 42U, 209U, 190U, 223U, 204U, 57U, 111U, 135U, 22U, 147U,
    146U, 82U, 3U, 20U, 166U, 182U, 185U, 175U, 103U, 147U, 219U, 171U, 173U, 69U, 153U, 82U, 82U,
    40U, 204U, 124U, 156U, 50U, 196U, 216U, 224U, 151U, 221U, 246U
  };

static uint8_t
siggen_vectors384_low43[32U] =
  {
    73U, 97U, 72U, 92U, 188U, 151U, 143U, 132U, 86U, 236U, 90U, 199U, 207U, 201U, 247U, 217U, 41U,
    143U, 153U, 65U, 94U, 202U, 230U, 156U, 132U, 145U, 178U, 88U, 192U, 41U, 191U, 238U
  };

static uint8_t
siggen_vectors384_low44[32U] =
  {
    141U, 64U, 191U, 34U, 153U, 224U, 93U, 117U, 141U, 66U, 25U, 114U, 232U, 28U, 251U, 12U, 206U,
    104U, 185U, 73U, 36U, 13U, 195U, 15U, 49U, 88U, 54U, 172U, 199U, 11U, 239U, 3U
  };

static uint8_t
siggen_vectors384_low45[32U] =
  {
    86U, 116U, 230U, 247U, 127U, 139U, 70U, 244U, 108U, 202U, 147U, 125U, 131U, 177U, 40U, 223U,
    251U, 233U, 189U, 126U, 13U, 61U, 8U, 170U, 44U, 187U, 253U, 251U, 22U, 247U, 44U, 154U
  };

static uint8_t
siggen_vectors384_low46[32U] =
  {
    55U, 58U, 130U, 91U, 90U, 116U, 183U, 185U, 224U, 47U, 141U, 77U, 135U, 107U, 87U, 123U, 76U,
    57U, 132U, 22U, 141U, 112U, 75U, 169U, 249U, 91U, 25U, 192U, 94U, 213U, 144U, 175U
  };

static uint8_t
siggen_vectors384_low47[32U] =
  {
    239U, 111U, 179U, 134U, 173U, 4U, 75U, 99U, 254U, 183U, 68U, 95U, 161U, 107U, 16U, 49U, 144U,
    24U, 233U, 206U, 169U, 239U, 66U, 188U, 168U, 59U, 218U, 208U, 25U, 146U, 35U, 74U
  };

static uint8_t
siggen_vectors384_low48[32U] =
  {
    172U, 31U, 66U, 246U, 82U, 235U, 23U, 134U, 229U, 123U, 224U, 29U, 132U, 124U, 129U, 247U, 239U,
    160U, 114U, 186U, 86U, 109U, 69U, 131U, 175U, 79U, 21U, 81U, 163U, 247U, 108U, 101U
  };

static uint8_t
siggen_vectors384_low49[128U] =
  {
    124U, 241U, 159U, 76U, 133U, 30U, 151U, 197U, 188U, 161U, 26U, 57U, 240U, 7U, 76U, 59U, 123U,
    211U, 39U, 78U, 125U, 215U, 93U, 4U, 71U, 183U, 184U, 73U, 149U, 223U, 201U, 247U, 22U, 191U,
    8U, 194U, 83U, 71U, 245U, 111U, 204U, 94U, 81U, 73U, 203U, 63U, 156U, 251U, 57U, 212U, 8U, 172U,
    229U, 165U, 196U, 126U, 117U, 247U, 168U, 39U, 250U, 11U, 185U, 146U, 27U, 181U, 178U, 58U, 96U,
    83U, 219U, 225U, 250U, 43U, 186U, 52U, 26U, 200U, 116U, 217U, 177U, 51U, 63U, 196U, 220U, 34U,
    72U, 84U, 148U, 159U, 92U, 141U, 138U, 95U, 237U, 208U, 47U, 178U, 111U, 223U, 205U, 59U, 227U,
    81U, 174U, 192U, 252U, 190U, 241U, 137U, 114U, 149U, 108U, 110U, 192U, 239U, 250U, 240U, 87U,
    235U, 68U, 32U, 182U, 210U, 142U, 12U, 0U, 140U
  };

static uint8_t
siggen_vectors384_low50[32U] =
  {
    88U, 121U, 7U, 231U, 242U, 21U, 207U, 13U, 44U, 178U, 201U, 230U, 150U, 61U, 69U, 182U, 229U,
    53U, 237U, 66U, 108U, 130U, 138U, 110U, 162U, 251U, 99U, 124U, 202U, 76U, 92U, 189U
  };

static uint8_t
siggen_vectors384_low51[32U] =
  {
    102U, 13U, 164U, 92U, 65U, 60U, 201U, 201U, 82U, 98U, 2U, 193U, 107U, 64U, 42U, 246U, 2U, 211U,
    13U, 170U, 167U, 195U, 66U, 241U, 231U, 34U, 241U, 81U, 153U, 64U, 127U, 49U
  };

static uint8_t
siggen_vectors384_low52[32U] =
  {
    230U, 248U, 203U, 176U, 105U, 19U, 204U, 113U, 143U, 45U, 105U, 186U, 47U, 179U, 19U, 127U, 4U,
    164U, 28U, 39U, 198U, 118U, 209U, 168U, 15U, 191U, 48U, 234U, 60U, 164U, 100U, 57U
  };

static uint8_t
siggen_vectors384_low53[32U] =
  {
    107U, 142U, 183U, 192U, 216U, 175U, 148U, 86U, 185U, 93U, 215U, 5U, 97U, 160U, 233U, 2U, 134U,
    62U, 109U, 250U, 28U, 40U, 208U, 253U, 74U, 5U, 9U, 241U, 194U, 166U, 71U, 178U
  };

static uint8_t
siggen_vectors384_low54[32U] =
  {
    8U, 250U, 191U, 155U, 87U, 222U, 129U, 135U, 91U, 250U, 122U, 65U, 24U, 227U, 228U, 76U, 251U,
    56U, 236U, 106U, 155U, 32U, 20U, 148U, 2U, 7U, 186U, 59U, 28U, 88U, 48U, 56U
  };

static uint8_t
siggen_vectors384_low55[32U] =
  {
    165U, 141U, 25U, 155U, 29U, 235U, 167U, 53U, 6U, 22U, 35U, 13U, 134U, 123U, 39U, 71U, 163U, 69U,
    148U, 33U, 129U, 28U, 41U, 24U, 54U, 171U, 238U, 113U, 91U, 143U, 103U, 180U
  };

static uint8_t
siggen_vectors384_low56[128U] =
  {
    184U, 146U, 255U, 171U, 184U, 9U, 233U, 138U, 153U, 176U, 167U, 152U, 149U, 68U, 95U, 199U, 52U,
    250U, 27U, 97U, 89U, 249U, 205U, 219U, 109U, 33U, 229U, 16U, 112U, 139U, 218U, 182U, 7U, 102U,
    51U, 172U, 48U, 170U, 239U, 67U, 219U, 86U, 108U, 13U, 33U, 244U, 56U, 29U, 180U, 103U, 17U,
    254U, 56U, 18U, 197U, 206U, 15U, 180U, 164U, 14U, 61U, 93U, 138U, 178U, 78U, 78U, 130U, 211U,
    86U, 12U, 109U, 199U, 195U, 119U, 148U, 238U, 23U, 212U, 161U, 68U, 6U, 94U, 249U, 156U, 141U,
    28U, 136U, 188U, 34U, 173U, 140U, 76U, 39U, 216U, 90U, 213U, 24U, 250U, 87U, 71U, 174U, 53U,
    39U, 111U, 193U, 4U, 130U, 157U, 63U, 92U, 114U, 252U, 42U, 158U, 165U, 90U, 28U, 58U, 135U, 0U,
    124U, 209U, 51U, 38U, 63U, 121U, 228U, 5U
  };

static uint8_t
siggen_vectors384_low57[32U] =
  {
    36U, 177U, 229U, 103U, 109U, 26U, 157U, 107U, 100U, 90U, 152U, 65U, 65U, 161U, 87U, 193U, 36U,
    83U, 31U, 238U, 185U, 45U, 145U, 81U, 16U, 174U, 244U, 116U, 177U, 226U, 118U, 102U
  };

static uint8_t
siggen_vectors384_low58[32U] =
  {
    180U, 144U, 154U, 91U, 223U, 37U, 247U, 101U, 159U, 78U, 243U, 94U, 75U, 129U, 20U, 41U, 251U,
    44U, 89U, 18U, 110U, 61U, 173U, 9U, 16U, 11U, 70U, 174U, 166U, 235U, 231U, 166U
  };

static uint8_t
siggen_vectors384_low59[32U] =
  {
    118U, 10U, 224U, 21U, 250U, 106U, 245U, 201U, 116U, 156U, 64U, 48U, 253U, 181U, 222U, 110U, 88U,
    198U, 181U, 177U, 148U, 72U, 41U, 16U, 92U, 247U, 237U, 247U, 211U, 162U, 44U, 251U
  };

static uint8_t
siggen_vectors384_low60[32U] =
  {
    136U, 121U, 73U, 35U, 216U, 148U, 59U, 93U, 188U, 199U, 167U, 167U, 101U, 3U, 136U, 15U, 247U,
    218U, 99U, 43U, 8U, 131U, 170U, 166U, 10U, 159U, 204U, 113U, 191U, 136U, 15U, 214U
  };

static uint8_t
siggen_vectors384_low61[32U] =
  {
    110U, 201U, 163U, 64U, 183U, 127U, 174U, 60U, 120U, 39U, 250U, 150U, 217U, 151U, 233U, 39U, 34U,
    255U, 42U, 146U, 130U, 23U, 182U, 221U, 60U, 98U, 143U, 61U, 73U, 174U, 76U, 230U
  };

static uint8_t
siggen_vectors384_low62[32U] =
  {
    99U, 123U, 84U, 187U, 207U, 183U, 231U, 216U, 164U, 30U, 163U, 23U, 252U, 252U, 168U, 173U,
    116U, 235U, 59U, 182U, 183U, 120U, 188U, 126U, 249U, 222U, 192U, 9U, 40U, 25U, 118U, 247U
  };

static uint8_t
siggen_vectors384_low63[128U] =
  {
    129U, 68U, 227U, 112U, 20U, 201U, 94U, 19U, 35U, 28U, 189U, 111U, 166U, 71U, 114U, 119U, 31U,
    147U, 180U, 78U, 55U, 247U, 176U, 47U, 89U, 32U, 153U, 204U, 20U, 99U, 67U, 237U, 212U, 244U,
    236U, 159U, 161U, 188U, 104U, 215U, 242U, 233U, 238U, 120U, 252U, 55U, 4U, 67U, 170U, 40U, 3U,
    255U, 76U, 165U, 46U, 228U, 154U, 47U, 77U, 175U, 44U, 129U, 129U, 234U, 123U, 132U, 117U, 179U,
    160U, 246U, 8U, 252U, 50U, 121U, 208U, 158U, 45U, 5U, 127U, 190U, 63U, 47U, 251U, 229U, 19U,
    55U, 150U, 18U, 71U, 129U, 41U, 156U, 109U, 166U, 12U, 254U, 126U, 206U, 163U, 171U, 195U, 7U,
    6U, 222U, 210U, 205U, 241U, 143U, 157U, 120U, 142U, 89U, 242U, 195U, 22U, 98U, 223U, 58U, 190U,
    1U, 169U, 177U, 35U, 4U, 251U, 141U, 92U, 140U
  };

static uint8_t
siggen_vectors384_low64[32U] =
  {
    188U, 228U, 156U, 123U, 3U, 220U, 220U, 114U, 57U, 59U, 10U, 103U, 207U, 90U, 165U, 223U, 135U,
    15U, 90U, 170U, 97U, 55U, 173U, 161U, 237U, 199U, 134U, 46U, 9U, 129U, 236U, 103U
  };

static uint8_t
siggen_vectors384_low65[32U] =
  {
    199U, 134U, 217U, 66U, 29U, 103U, 183U, 43U, 146U, 44U, 243U, 222U, 242U, 162U, 94U, 235U, 94U,
    115U, 243U, 69U, 67U, 235U, 80U, 177U, 82U, 231U, 56U, 169U, 138U, 251U, 12U, 165U
  };

static uint8_t
siggen_vectors384_low66[32U] =
  {
    103U, 150U, 39U, 30U, 121U, 226U, 73U, 111U, 158U, 116U, 177U, 38U, 177U, 18U, 58U, 61U, 6U,
    125U, 229U, 107U, 86U, 5U, 214U, 245U, 28U, 143U, 110U, 29U, 91U, 185U, 58U, 186U
  };

static uint8_t
siggen_vectors384_low67[32U] =
  {
    137U, 230U, 144U, 215U, 138U, 94U, 13U, 43U, 140U, 233U, 247U, 252U, 191U, 52U, 226U, 96U, 95U,
    217U, 88U, 71U, 96U, 250U, 119U, 41U, 4U, 51U, 151U, 97U, 45U, 210U, 31U, 148U
  };

static uint8_t
siggen_vectors384_low68[32U] =
  {
    7U, 229U, 5U, 76U, 56U, 72U, 57U, 88U, 70U, 36U, 232U, 215U, 48U, 69U, 77U, 194U, 126U, 103U,
    60U, 74U, 144U, 203U, 241U, 41U, 216U, 139U, 145U, 37U, 3U, 65U, 133U, 77U
  };

static uint8_t
siggen_vectors384_low69[32U] =
  {
    247U, 230U, 101U, 184U, 134U, 20U, 208U, 197U, 203U, 179U, 0U, 124U, 175U, 231U, 19U, 118U, 61U,
    129U, 131U, 21U, 37U, 151U, 31U, 23U, 71U, 217U, 46U, 77U, 28U, 162U, 99U, 167U
  };

static uint8_t
siggen_vectors384_low70[128U] =
  {
    163U, 104U, 61U, 18U, 8U, 7U, 240U, 160U, 48U, 254U, 237U, 103U, 151U, 133U, 50U, 102U, 152U,
    195U, 112U, 47U, 25U, 131U, 234U, 186U, 27U, 112U, 221U, 250U, 127U, 11U, 49U, 136U, 6U, 11U,
    132U, 94U, 43U, 103U, 237U, 87U, 238U, 104U, 8U, 119U, 70U, 113U, 4U, 80U, 247U, 66U, 124U,
    179U, 70U, 85U, 215U, 25U, 192U, 172U, 188U, 9U, 172U, 105U, 106U, 219U, 75U, 34U, 171U, 161U,
    185U, 50U, 43U, 113U, 17U, 7U, 110U, 103U, 5U, 58U, 85U, 246U, 43U, 80U, 26U, 75U, 202U, 10U,
    217U, 213U, 10U, 134U, 143U, 81U, 174U, 235U, 78U, 242U, 120U, 35U, 35U, 111U, 82U, 103U, 232U,
    218U, 131U, 225U, 67U, 4U, 116U, 34U, 206U, 20U, 13U, 102U, 224U, 94U, 68U, 220U, 132U, 251U,
    58U, 69U, 6U, 178U, 165U, 215U, 202U, 168U
  };

static uint8_t
siggen_vectors384_low71[32U] =
  {
    115U, 24U, 138U, 146U, 59U, 192U, 178U, 137U, 232U, 28U, 61U, 180U, 141U, 130U, 105U, 23U, 145U,
    15U, 27U, 149U, 119U, 0U, 248U, 146U, 84U, 37U, 193U, 251U, 39U, 202U, 186U, 185U
  };

static uint8_t
siggen_vectors384_low72[32U] =
  {
    134U, 102U, 44U, 1U, 74U, 182U, 102U, 238U, 119U, 7U, 35U, 190U, 141U, 163U, 140U, 92U, 210U,
    153U, 239U, 198U, 72U, 15U, 198U, 248U, 195U, 96U, 52U, 56U, 250U, 131U, 151U, 185U
  };

static uint8_t
siggen_vectors384_low73[32U] =
  {
    242U, 107U, 51U, 7U, 166U, 80U, 195U, 134U, 63U, 170U, 165U, 246U, 66U, 243U, 186U, 19U, 132U,
    195U, 211U, 160U, 46U, 221U, 61U, 72U, 198U, 87U, 194U, 105U, 96U, 156U, 195U, 252U
  };

static uint8_t
siggen_vectors384_low74[32U] =
  {
    236U, 144U, 88U, 74U, 179U, 179U, 131U, 181U, 144U, 98U, 111U, 54U, 237U, 79U, 81U, 16U, 228U,
    152U, 136U, 174U, 199U, 174U, 122U, 156U, 94U, 166U, 45U, 210U, 220U, 55U, 134U, 102U
  };

static uint8_t
siggen_vectors384_low75[32U] =
  {
    19U, 233U, 173U, 89U, 17U, 47U, 222U, 58U, 244U, 22U, 62U, 181U, 194U, 64U, 11U, 94U, 154U, 96U,
    37U, 118U, 213U, 134U, 154U, 193U, 197U, 105U, 7U, 95U, 8U, 201U, 15U, 246U
  };

static uint8_t
siggen_vectors384_low76[32U] =
  {
    112U, 138U, 198U, 95U, 242U, 176U, 186U, 172U, 204U, 109U, 217U, 84U, 226U, 169U, 61U, 244U,
    96U, 22U, 189U, 4U, 69U, 118U, 54U, 222U, 6U, 121U, 143U, 204U, 23U, 240U, 43U, 229U
  };

static uint8_t
siggen_vectors384_low77[128U] =
  {
    177U, 223U, 128U, 81U, 178U, 19U, 252U, 95U, 99U, 101U, 55U, 227U, 126U, 33U, 46U, 178U, 11U,
    36U, 35U, 230U, 70U, 122U, 156U, 112U, 129U, 51U, 106U, 135U, 14U, 99U, 115U, 252U, 131U, 88U,
    153U, 213U, 158U, 84U, 108U, 10U, 198U, 104U, 204U, 129U, 206U, 73U, 33U, 232U, 143U, 66U, 230U,
    218U, 42U, 16U, 154U, 3U, 180U, 244U, 232U, 25U, 161U, 124U, 149U, 91U, 141U, 9U, 158U, 198U,
    178U, 130U, 251U, 73U, 82U, 88U, 220U, 161U, 62U, 199U, 121U, 196U, 89U, 218U, 144U, 148U, 117U,
    81U, 154U, 52U, 119U, 34U, 60U, 6U, 185U, 154U, 251U, 215U, 127U, 153U, 34U, 231U, 203U, 239U,
    132U, 75U, 147U, 243U, 206U, 95U, 80U, 219U, 129U, 107U, 46U, 13U, 139U, 21U, 117U, 210U, 225U,
    122U, 107U, 141U, 185U, 17U, 29U, 109U, 165U, 120U
  };

static uint8_t
siggen_vectors384_low78[32U] =
  {
    246U, 55U, 213U, 87U, 99U, 254U, 129U, 149U, 65U, 88U, 142U, 12U, 96U, 63U, 40U, 138U, 105U,
    60U, 198U, 104U, 35U, 198U, 187U, 123U, 142U, 0U, 59U, 211U, 133U, 128U, 235U, 206U
  };

static uint8_t
siggen_vectors384_low79[32U] =
  {
    116U, 164U, 98U, 12U, 87U, 134U, 1U, 71U, 95U, 193U, 105U, 169U, 184U, 75U, 230U, 19U, 180U,
    161U, 108U, 182U, 172U, 171U, 143U, 217U, 136U, 72U, 166U, 236U, 159U, 189U, 19U, 61U
  };

static uint8_t
siggen_vectors384_low80[32U] =
  {
    66U, 185U, 227U, 93U, 52U, 124U, 16U, 126U, 99U, 189U, 85U, 245U, 37U, 249U, 21U, 188U, 241U,
    227U, 210U, 184U, 29U, 0U, 45U, 60U, 57U, 172U, 241U, 15U, 195U, 6U, 69U, 161U
  };

static uint8_t
siggen_vectors384_low81[32U] =
  {
    77U, 87U, 143U, 80U, 153U, 99U, 98U, 52U, 217U, 193U, 213U, 102U, 241U, 33U, 93U, 93U, 136U,
    122U, 229U, 212U, 112U, 34U, 190U, 23U, 219U, 243U, 42U, 17U, 160U, 63U, 5U, 59U
  };

static uint8_t
siggen_vectors384_low82[32U] =
  {
    17U, 58U, 147U, 62U, 188U, 77U, 148U, 206U, 28U, 239U, 120U, 30U, 72U, 41U, 223U, 12U, 73U, 59U,
    6U, 133U, 211U, 159U, 178U, 4U, 140U, 224U, 27U, 33U, 195U, 152U, 219U, 186U
  };

static uint8_t
siggen_vectors384_low83[32U] =
  {
    48U, 5U, 189U, 78U, 198U, 61U, 189U, 4U, 206U, 159U, 240U, 198U, 36U, 106U, 214U, 93U, 39U,
    252U, 246U, 46U, 219U, 43U, 126U, 70U, 21U, 137U, 249U, 240U, 231U, 68U, 111U, 253U
  };

static uint8_t
siggen_vectors384_low84[128U] =
  {
    11U, 145U, 142U, 222U, 152U, 91U, 92U, 73U, 23U, 151U, 208U, 168U, 20U, 70U, 178U, 147U, 59U,
    227U, 18U, 244U, 25U, 178U, 18U, 227U, 170U, 233U, 186U, 89U, 20U, 192U, 10U, 244U, 49U, 116U,
    122U, 157U, 40U, 122U, 124U, 119U, 97U, 233U, 188U, 188U, 138U, 18U, 170U, 249U, 212U, 167U,
    109U, 19U, 218U, 213U, 159U, 199U, 66U, 248U, 242U, 24U, 239U, 102U, 235U, 103U, 3U, 82U, 32U,
    160U, 122U, 204U, 26U, 53U, 124U, 91U, 86U, 46U, 203U, 107U, 137U, 92U, 247U, 37U, 196U, 35U,
    4U, 18U, 254U, 250U, 199U, 32U, 151U, 242U, 194U, 184U, 41U, 237U, 88U, 116U, 45U, 124U, 50U,
    124U, 173U, 15U, 16U, 88U, 223U, 27U, 221U, 212U, 174U, 156U, 109U, 42U, 186U, 37U, 72U, 4U,
    36U, 48U, 134U, 132U, 206U, 205U, 101U, 23U, 205U, 216U
  };

static uint8_t
siggen_vectors384_low85[32U] =
  {
    46U, 53U, 125U, 81U, 81U, 127U, 249U, 59U, 130U, 31U, 137U, 89U, 50U, 253U, 221U, 237U, 131U,
    71U, 243U, 37U, 150U, 184U, 18U, 48U, 142U, 111U, 27U, 175U, 125U, 216U, 164U, 127U
  };

static uint8_t
siggen_vectors384_low86[32U] =
  {
    126U, 64U, 120U, 161U, 213U, 12U, 102U, 159U, 178U, 153U, 109U, 217U, 186U, 203U, 12U, 58U,
    199U, 237U, 228U, 245U, 143U, 160U, 250U, 18U, 34U, 231U, 141U, 191U, 93U, 31U, 65U, 134U
  };

static uint8_t
siggen_vectors384_low87[32U] =
  {
    0U, 20U, 228U, 110U, 144U, 204U, 23U, 31U, 187U, 131U, 234U, 52U, 198U, 183U, 130U, 2U, 234U,
    129U, 55U, 167U, 217U, 38U, 240U, 22U, 145U, 71U, 237U, 90U, 227U, 214U, 89U, 111U
  };

static uint8_t
siggen_vectors384_low88[32U] =
  {
    190U, 82U, 43U, 9U, 64U, 185U, 164U, 13U, 132U, 191U, 121U, 15U, 230U, 171U, 220U, 37U, 40U,
    119U, 230U, 113U, 242U, 239U, 166U, 58U, 51U, 166U, 90U, 81U, 47U, 194U, 170U, 92U
  };

static uint8_t
siggen_vectors384_low89[32U] =
  {
    162U, 107U, 154U, 215U, 117U, 172U, 55U, 255U, 76U, 127U, 4U, 44U, 220U, 72U, 114U, 197U, 228U,
    229U, 232U, 0U, 72U, 95U, 72U, 141U, 223U, 170U, 237U, 55U, 159U, 70U, 128U, 144U
  };

static uint8_t
siggen_vectors384_low90[32U] =
  {
    248U, 142U, 174U, 32U, 25U, 190U, 187U, 186U, 98U, 180U, 83U, 184U, 238U, 52U, 114U, 202U, 92U,
    103U, 194U, 103U, 150U, 76U, 255U, 224U, 207U, 45U, 41U, 51U, 193U, 114U, 61U, 255U
  };

static uint8_t
siggen_vectors384_low91[128U] =
  {
    15U, 171U, 38U, 253U, 225U, 164U, 70U, 124U, 169U, 48U, 219U, 229U, 19U, 204U, 195U, 69U, 43U,
    112U, 49U, 60U, 204U, 222U, 41U, 148U, 238U, 173U, 47U, 222U, 133U, 200U, 218U, 29U, 184U, 77U,
    125U, 6U, 160U, 36U, 201U, 232U, 134U, 41U, 213U, 52U, 66U, 36U, 164U, 234U, 224U, 27U, 33U,
    162U, 102U, 93U, 95U, 127U, 54U, 213U, 82U, 75U, 245U, 54U, 125U, 127U, 139U, 106U, 113U, 234U,
    5U, 212U, 19U, 212U, 175U, 222U, 51U, 119U, 127U, 10U, 59U, 228U, 156U, 158U, 106U, 162U, 158U,
    164U, 71U, 116U, 106U, 158U, 119U, 206U, 39U, 35U, 42U, 85U, 11U, 49U, 221U, 78U, 124U, 155U,
    200U, 145U, 52U, 133U, 242U, 220U, 131U, 165U, 98U, 152U, 5U, 28U, 146U, 70U, 31U, 212U, 107U,
    20U, 204U, 137U, 92U, 48U, 10U, 79U, 184U, 116U
  };

static uint8_t
siggen_vectors384_low92[32U] =
  {
    119U, 214U, 12U, 172U, 187U, 172U, 134U, 171U, 137U, 0U, 148U, 3U, 201U, 114U, 137U, 181U, 144U,
    4U, 102U, 133U, 104U, 135U, 211U, 230U, 17U, 42U, 244U, 39U, 247U, 240U, 245U, 11U
  };

static uint8_t
siggen_vectors384_low93[32U] =
  {
    166U, 32U, 50U, 223U, 219U, 135U, 226U, 94U, 208U, 199U, 12U, 173U, 32U, 217U, 39U, 199U, 239U,
    254U, 178U, 99U, 142U, 108U, 136U, 221U, 214U, 112U, 247U, 77U, 241U, 96U, 144U, 229U
  };

static uint8_t
siggen_vectors384_low94[32U] =
  {
    68U, 197U, 238U, 44U, 247U, 64U, 222U, 212U, 104U, 245U, 210U, 239U, 225U, 61U, 170U, 124U, 82U,
    52U, 100U, 90U, 55U, 192U, 115U, 175U, 53U, 51U, 13U, 3U, 164U, 254U, 217U, 118U
  };

static uint8_t
siggen_vectors384_low95[32U] =
  {
    6U, 193U, 230U, 146U, 176U, 69U, 244U, 37U, 162U, 19U, 71U, 236U, 247U, 40U, 51U, 208U, 36U,
    41U, 6U, 199U, 193U, 9U, 79U, 128U, 85U, 102U, 205U, 203U, 18U, 86U, 227U, 148U
  };

static uint8_t
siggen_vectors384_low96[32U] =
  {
    235U, 23U, 59U, 81U, 251U, 10U, 236U, 49U, 137U, 80U, 208U, 151U, 231U, 253U, 165U, 195U, 78U,
    82U, 149U, 25U, 99U, 28U, 62U, 44U, 155U, 69U, 80U, 185U, 3U, 218U, 65U, 125U
  };

static uint8_t
siggen_vectors384_low97[32U] =
  {
    202U, 44U, 19U, 87U, 75U, 241U, 183U, 213U, 110U, 157U, 193U, 131U, 21U, 3U, 106U, 49U, 184U,
    188U, 237U, 223U, 62U, 44U, 41U, 2U, 220U, 180U, 15U, 12U, 201U, 227U, 27U, 69U
  };

static uint8_t
siggen_vectors384_low98[128U] =
  {
    120U, 67U, 241U, 87U, 239U, 133U, 102U, 114U, 42U, 125U, 105U, 218U, 103U, 222U, 117U, 153U,
    238U, 101U, 203U, 57U, 117U, 80U, 143U, 112U, 198U, 18U, 179U, 40U, 145U, 144U, 227U, 100U, 20U,
    23U, 129U, 224U, 184U, 50U, 242U, 217U, 98U, 113U, 34U, 116U, 47U, 75U, 88U, 113U, 206U, 234U,
    252U, 208U, 155U, 165U, 236U, 144U, 202U, 230U, 188U, 192U, 26U, 227U, 43U, 80U, 241U, 63U, 99U,
    145U, 141U, 251U, 81U, 119U, 223U, 151U, 151U, 198U, 39U, 59U, 146U, 209U, 3U, 195U, 247U, 163U,
    252U, 32U, 80U, 210U, 177U, 150U, 204U, 135U, 44U, 87U, 183U, 127U, 155U, 219U, 23U, 130U, 212U,
    25U, 84U, 69U, 252U, 198U, 35U, 109U, 216U, 189U, 20U, 200U, 188U, 188U, 130U, 35U, 166U, 115U,
    159U, 106U, 23U, 201U, 168U, 97U, 232U, 200U, 33U, 166U
  };

static uint8_t
siggen_vectors384_low99[32U] =
  {
    72U, 104U, 84U, 231U, 121U, 98U, 17U, 127U, 73U, 224U, 147U, 120U, 222U, 108U, 158U, 59U, 53U,
    34U, 250U, 117U, 43U, 16U, 178U, 200U, 16U, 191U, 72U, 219U, 88U, 77U, 115U, 136U
  };

static uint8_t
siggen_vectors384_low100[32U] =
  {
    118U, 11U, 86U, 36U, 189U, 100U, 209U, 156U, 134U, 110U, 84U, 204U, 215U, 74U, 215U, 249U, 136U,
    81U, 175U, 219U, 195U, 221U, 234U, 227U, 236U, 44U, 82U, 161U, 53U, 190U, 156U, 250U
  };

static uint8_t
siggen_vectors384_low101[32U] =
  {
    254U, 202U, 21U, 206U, 147U, 80U, 135U, 113U, 2U, 238U, 224U, 245U, 175U, 24U, 178U, 254U, 216U,
    157U, 200U, 107U, 125U, 240U, 191U, 123U, 194U, 150U, 60U, 22U, 56U, 227U, 111U, 232U
  };

static uint8_t
siggen_vectors384_low102[32U] =
  {
    228U, 247U, 124U, 100U, 66U, 236U, 162U, 57U, 176U, 27U, 2U, 84U, 225U, 26U, 65U, 130U, 120U,
    45U, 150U, 244U, 138U, 181U, 33U, 204U, 61U, 29U, 104U, 223U, 18U, 181U, 164U, 26U
  };

static uint8_t
siggen_vectors384_low103[32U] =
  {
    189U, 255U, 20U, 228U, 96U, 3U, 9U, 194U, 199U, 127U, 121U, 162U, 89U, 99U, 169U, 85U, 181U,
    181U, 0U, 167U, 178U, 211U, 76U, 177U, 114U, 205U, 106U, 205U, 82U, 144U, 92U, 123U
  };

static uint8_t
siggen_vectors384_low104[32U] =
  {
    176U, 71U, 156U, 219U, 61U, 247U, 153U, 35U, 236U, 54U, 161U, 4U, 161U, 41U, 83U, 76U, 93U, 89U,
    246U, 34U, 190U, 125U, 97U, 58U, 160U, 69U, 48U, 173U, 37U, 7U, 211U, 162U
  };

static __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors384_low105[15U] =
  {
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low0 },
        .snd = { .len = 32U, .b = siggen_vectors384_low1 },
        .thd = { .len = 32U, .b = siggen_vectors384_low2 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low3 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low4 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low5 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low6 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low7 },
        .snd = { .len = 32U, .b = siggen_vectors384_low8 },
        .thd = { .len = 32U, .b = siggen_vectors384_low9 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low10 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low11 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low12 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low13 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low14 },
        .snd = { .len = 32U, .b = siggen_vectors384_low15 },
        .thd = { .len = 32U, .b = siggen_vectors384_low16 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low17 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low18 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low19 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low20 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low21 },
        .snd = { .len = 32U, .b = siggen_vectors384_low22 },
        .thd = { .len = 32U, .b = siggen_vectors384_low23 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low24 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low25 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low26 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low27 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low28 },
        .snd = { .len = 32U, .b = siggen_vectors384_low29 },
        .thd = { .len = 32U, .b = siggen_vectors384_low30 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low31 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low32 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low33 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low34 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low35 },
        .snd = { .len = 32U, .b = siggen_vectors384_low36 },
        .thd = { .len = 32U, .b = siggen_vectors384_low37 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low38 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low39 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low40 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low41 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low42 },
        .snd = { .len = 32U, .b = siggen_vectors384_low43 },
        .thd = { .len = 32U, .b = siggen_vectors384_low44 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low45 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low46 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low47 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low48 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low49 },
        .snd = { .len = 32U, .b = siggen_vectors384_low50 },
        .thd = { .len = 32U, .b = siggen_vectors384_low51 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low52 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low53 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low54 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low55 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low56 },
        .snd = { .len = 32U, .b = siggen_vectors384_low57 },
        .thd = { .len = 32U, .b = siggen_vectors384_low58 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low59 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low60 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low61 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low62 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low63 },
        .snd = { .len = 32U, .b = siggen_vectors384_low64 },
        .thd = { .len = 32U, .b = siggen_vectors384_low65 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low66 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low67 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low68 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low69 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low70 },
        .snd = { .len = 32U, .b = siggen_vectors384_low71 },
        .thd = { .len = 32U, .b = siggen_vectors384_low72 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low73 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low74 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low75 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low76 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low77 },
        .snd = { .len = 32U, .b = siggen_vectors384_low78 },
        .thd = { .len = 32U, .b = siggen_vectors384_low79 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low80 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low81 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low82 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low83 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low84 },
        .snd = { .len = 32U, .b = siggen_vectors384_low85 },
        .thd = { .len = 32U, .b = siggen_vectors384_low86 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low87 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low88 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low89 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low90 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low91 },
        .snd = { .len = 32U, .b = siggen_vectors384_low92 },
        .thd = { .len = 32U, .b = siggen_vectors384_low93 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low94 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low95 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low96 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low97 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors384_low98 },
        .snd = { .len = 32U, .b = siggen_vectors384_low99 },
        .thd = { .len = 32U, .b = siggen_vectors384_low100 },
        .f3 = { .len = 32U, .b = siggen_vectors384_low101 },
        .f4 = { .len = 32U, .b = siggen_vectors384_low102 },
        .f5 = { .len = 32U, .b = siggen_vectors384_low103 },
        .f6 = { .len = 32U, .b = siggen_vectors384_low104 }
      }
    )
  };

static lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors384_low = { .len = 15U, .b = siggen_vectors384_low105 };

static uint8_t
siggen_vectors512_low0[128U] =
  {
    108U, 133U, 114U, 182U, 163U, 164U, 169U, 232U, 224U, 61U, 190U, 237U, 153U, 51U, 77U, 65U,
    102U, 27U, 138U, 132U, 23U, 7U, 79U, 51U, 90U, 177U, 132U, 95U, 108U, 200U, 82U, 173U, 184U,
    192U, 29U, 152U, 32U, 252U, 248U, 225U, 6U, 153U, 204U, 130U, 122U, 143U, 189U, 202U, 44U, 189U,
    70U, 204U, 102U, 228U, 230U, 183U, 186U, 65U, 236U, 62U, 250U, 115U, 53U, 135U, 228U, 163U, 14U,
    197U, 82U, 205U, 141U, 218U, 184U, 22U, 62U, 20U, 142U, 80U, 244U, 208U, 144U, 120U, 40U, 151U,
    243U, 221U, 172U, 132U, 164U, 30U, 31U, 207U, 232U, 197U, 107U, 97U, 82U, 192U, 9U, 123U, 13U,
    99U, 75U, 65U, 1U, 20U, 113U, 255U, 208U, 4U, 244U, 62U, 180U, 170U, 252U, 3U, 129U, 151U, 236U,
    107U, 174U, 43U, 68U, 112U, 232U, 105U, 189U, 237U
  };

static uint8_t
siggen_vectors512_low1[32U] =
  {
    157U, 208U, 211U, 163U, 213U, 20U, 194U, 168U, 173U, 177U, 98U, 184U, 30U, 58U, 223U, 186U, 50U,
    153U, 48U, 159U, 125U, 32U, 24U, 246U, 7U, 189U, 177U, 91U, 26U, 37U, 244U, 153U
  };

static uint8_t
siggen_vectors512_low2[32U] =
  {
    107U, 115U, 141U, 227U, 57U, 139U, 106U, 197U, 123U, 149U, 145U, 249U, 215U, 152U, 93U, 212U,
    243U, 33U, 55U, 173U, 52U, 96U, 220U, 248U, 151U, 12U, 19U, 144U, 203U, 158U, 175U, 141U
  };

static uint8_t
siggen_vectors512_low3[32U] =
  {
    131U, 188U, 97U, 226U, 109U, 43U, 187U, 211U, 207U, 45U, 42U, 180U, 69U, 162U, 188U, 74U, 181U,
    221U, 228U, 31U, 74U, 19U, 7U, 143U, 209U, 211U, 204U, 54U, 171U, 89U, 109U, 87U
  };

static uint8_t
siggen_vectors512_low4[32U] =
  {
    145U, 6U, 25U, 33U, 112U, 204U, 179U, 198U, 70U, 132U, 212U, 130U, 135U, 187U, 129U, 187U, 237U,
    81U, 180U, 13U, 80U, 52U, 98U, 201U, 0U, 229U, 199U, 170U, 228U, 62U, 56U, 10U
  };

static uint8_t
siggen_vectors512_low5[32U] =
  {
    39U, 95U, 167U, 96U, 135U, 139U, 77U, 192U, 94U, 157U, 21U, 127U, 237U, 253U, 142U, 155U, 28U,
    156U, 134U, 18U, 34U, 167U, 18U, 116U, 140U, 180U, 183U, 117U, 76U, 4U, 63U, 177U
  };

static uint8_t
siggen_vectors512_low6[32U] =
  {
    105U, 157U, 144U, 107U, 184U, 67U, 90U, 5U, 52U, 90U, 243U, 179U, 126U, 59U, 53U, 119U, 134U,
    147U, 158U, 148U, 202U, 174U, 37U, 120U, 82U, 240U, 80U, 58U, 219U, 30U, 15U, 126U
  };

static uint8_t
siggen_vectors512_low7[128U] =
  {
    126U, 60U, 143U, 225U, 98U, 212U, 140U, 200U, 197U, 177U, 27U, 94U, 94U, 188U, 5U, 235U, 196U,
    92U, 67U, 155U, 219U, 192U, 176U, 144U, 33U, 69U, 146U, 27U, 131U, 131U, 3U, 124U, 176U, 129U,
    34U, 34U, 3U, 21U, 152U, 205U, 26U, 86U, 250U, 113U, 105U, 79U, 189U, 48U, 76U, 198U, 41U, 56U,
    35U, 52U, 101U, 236U, 57U, 198U, 228U, 159U, 87U, 223U, 232U, 35U, 152U, 59U, 105U, 35U, 196U,
    232U, 101U, 99U, 57U, 73U, 24U, 62U, 107U, 144U, 233U, 224U, 109U, 130U, 117U, 243U, 144U, 125U,
    151U, 150U, 125U, 71U, 182U, 35U, 159U, 226U, 132U, 123U, 125U, 73U, 207U, 22U, 186U, 105U,
    210U, 134U, 32U, 131U, 207U, 27U, 204U, 247U, 175U, 227U, 79U, 220U, 144U, 226U, 25U, 152U,
    150U, 65U, 7U, 182U, 74U, 190U, 107U, 137U, 209U, 38U
  };

static uint8_t
siggen_vectors512_low8[32U] =
  {
    249U, 191U, 144U, 155U, 121U, 115U, 191U, 14U, 61U, 173U, 14U, 67U, 220U, 178U, 215U, 250U,
    139U, 218U, 73U, 219U, 230U, 229U, 53U, 127U, 143U, 14U, 43U, 209U, 25U, 190U, 48U, 230U
  };

static uint8_t
siggen_vectors512_low9[32U] =
  {
    242U, 166U, 103U, 77U, 78U, 134U, 21U, 42U, 82U, 113U, 153U, 190U, 210U, 147U, 250U, 99U, 172U,
    222U, 27U, 77U, 138U, 146U, 182U, 46U, 85U, 34U, 16U, 186U, 69U, 195U, 135U, 146U
  };

static uint8_t
siggen_vectors512_low10[32U] =
  {
    199U, 37U, 101U, 194U, 79U, 14U, 238U, 106U, 9U, 74U, 243U, 65U, 221U, 216U, 87U, 151U, 71U,
    184U, 101U, 249U, 28U, 142U, 213U, 180U, 76U, 218U, 138U, 25U, 204U, 147U, 119U, 111U
  };

static uint8_t
siggen_vectors512_low11[32U] =
  {
    229U, 71U, 121U, 31U, 113U, 133U, 133U, 15U, 3U, 208U, 197U, 132U, 25U, 100U, 143U, 101U, 185U,
    210U, 156U, 220U, 34U, 237U, 29U, 226U, 166U, 66U, 128U, 34U, 12U, 252U, 175U, 186U
  };

static uint8_t
siggen_vectors512_low12[32U] =
  {
    71U, 130U, 144U, 61U, 42U, 175U, 139U, 25U, 13U, 171U, 92U, 174U, 34U, 35U, 56U, 141U, 45U,
    139U, 216U, 69U, 179U, 135U, 93U, 55U, 72U, 92U, 84U, 225U, 222U, 209U, 211U, 216U
  };

static uint8_t
siggen_vectors512_low13[32U] =
  {
    223U, 180U, 14U, 64U, 107U, 250U, 7U, 79U, 11U, 248U, 50U, 119U, 27U, 43U, 159U, 24U, 110U, 34U,
    17U, 240U, 188U, 162U, 121U, 100U, 74U, 12U, 168U, 85U, 154U, 207U, 57U, 218U
  };

static uint8_t
siggen_vectors512_low14[128U] =
  {
    213U, 170U, 138U, 201U, 33U, 140U, 166U, 97U, 205U, 23U, 119U, 86U, 175U, 111U, 187U, 90U, 64U,
    163U, 254U, 207U, 212U, 238U, 166U, 213U, 135U, 47U, 187U, 154U, 40U, 132U, 120U, 74U, 169U,
    181U, 240U, 192U, 35U, 166U, 224U, 218U, 92U, 246U, 54U, 71U, 84U, 238U, 100U, 101U, 180U, 238U,
    45U, 13U, 220U, 116U, 91U, 2U, 153U, 76U, 152U, 66U, 122U, 33U, 60U, 132U, 149U, 55U, 218U, 90U,
    68U, 119U, 179U, 171U, 254U, 2U, 100U, 139U, 230U, 127U, 38U, 232U, 11U, 86U, 163U, 49U, 80U,
    73U, 13U, 6U, 42U, 170U, 193U, 55U, 170U, 71U, 241U, 28U, 254U, 221U, 186U, 133U, 91U, 171U,
    158U, 78U, 2U, 133U, 50U, 165U, 99U, 50U, 109U, 146U, 127U, 158U, 110U, 50U, 146U, 177U, 251U,
    36U, 142U, 233U, 11U, 111U, 66U, 151U, 152U, 219U
  };

static uint8_t
siggen_vectors512_low15[32U] =
  {
    114U, 69U, 103U, 210U, 30U, 246U, 130U, 223U, 198U, 220U, 77U, 70U, 133U, 56U, 128U, 207U, 168U,
    111U, 230U, 254U, 160U, 239U, 213U, 31U, 172U, 69U, 111U, 3U, 195U, 211U, 110U, 173U
  };

static uint8_t
siggen_vectors512_low16[32U] =
  {
    112U, 184U, 119U, 181U, 227U, 101U, 252U, 240U, 129U, 64U, 177U, 236U, 161U, 25U, 186U, 186U,
    102U, 40U, 121U, 243U, 142U, 5U, 157U, 7U, 74U, 44U, 182U, 11U, 3U, 234U, 93U, 57U
  };

static uint8_t
siggen_vectors512_low17[32U] =
  {
    95U, 86U, 249U, 77U, 89U, 29U, 244U, 11U, 159U, 59U, 135U, 99U, 172U, 75U, 61U, 190U, 98U, 44U,
    149U, 109U, 91U, 208U, 197U, 86U, 88U, 182U, 244U, 111U, 163U, 222U, 178U, 1U
  };

static uint8_t
siggen_vectors512_low18[32U] =
  {
    121U, 214U, 201U, 103U, 237U, 35U, 199U, 99U, 236U, 233U, 202U, 75U, 2U, 98U, 24U, 0U, 76U,
    132U, 220U, 45U, 76U, 204U, 134U, 207U, 5U, 197U, 208U, 247U, 145U, 246U, 39U, 155U
  };

static uint8_t
siggen_vectors512_low19[32U] =
  {
    43U, 162U, 234U, 45U, 49U, 111U, 137U, 55U, 241U, 132U, 173U, 48U, 40U, 227U, 100U, 87U, 77U,
    32U, 162U, 2U, 228U, 231U, 81U, 61U, 122U, 245U, 122U, 194U, 69U, 104U, 4U, 209U
  };

static uint8_t
siggen_vectors512_low20[32U] =
  {
    100U, 254U, 148U, 150U, 141U, 24U, 197U, 150U, 124U, 121U, 158U, 3U, 73U, 4U, 27U, 158U, 64U,
    230U, 198U, 201U, 46U, 187U, 71U, 94U, 128U, 221U, 130U, 245U, 28U, 240U, 115U, 32U
  };

static uint8_t
siggen_vectors512_low21[128U] =
  {
    121U, 11U, 6U, 5U, 74U, 252U, 156U, 63U, 196U, 223U, 231U, 45U, 241U, 157U, 213U, 214U, 141U,
    16U, 140U, 252U, 252U, 166U, 33U, 40U, 4U, 246U, 213U, 52U, 253U, 47U, 190U, 72U, 155U, 216U,
    246U, 75U, 242U, 5U, 206U, 4U, 188U, 181U, 1U, 36U, 161U, 44U, 229U, 35U, 143U, 195U, 254U,
    125U, 215U, 110U, 111U, 166U, 64U, 32U, 106U, 245U, 37U, 73U, 241U, 51U, 213U, 147U, 161U, 191U,
    212U, 35U, 171U, 115U, 127U, 51U, 38U, 250U, 121U, 67U, 60U, 222U, 41U, 50U, 54U, 249U, 13U,
    66U, 56U, 240U, 221U, 56U, 237U, 105U, 73U, 45U, 219U, 217U, 195U, 234U, 229U, 131U, 182U, 50U,
    90U, 149U, 222U, 195U, 22U, 111U, 229U, 43U, 33U, 101U, 130U, 147U, 216U, 193U, 55U, 131U, 14U,
    244U, 82U, 151U, 214U, 120U, 19U, 183U, 165U, 8U
  };

static uint8_t
siggen_vectors512_low22[32U] =
  {
    41U, 197U, 213U, 77U, 125U, 31U, 9U, 157U, 80U, 249U, 73U, 191U, 206U, 141U, 96U, 115U, 218U,
    224U, 89U, 197U, 161U, 156U, 199U, 8U, 52U, 114U, 47U, 24U, 167U, 25U, 158U, 221U
  };

static uint8_t
siggen_vectors512_low23[32U] =
  {
    48U, 136U, 212U, 244U, 93U, 39U, 76U, 197U, 244U, 24U, 200U, 236U, 196U, 203U, 207U, 150U, 190U,
    135U, 73U, 31U, 66U, 2U, 80U, 248U, 203U, 192U, 28U, 223U, 37U, 3U, 236U, 71U
  };

static uint8_t
siggen_vectors512_low24[32U] =
  {
    99U, 77U, 180U, 129U, 152U, 18U, 146U, 55U, 237U, 6U, 140U, 136U, 255U, 88U, 9U, 246U, 33U, 25U,
    33U, 166U, 37U, 143U, 84U, 143U, 75U, 100U, 221U, 18U, 89U, 33U, 183U, 139U
  };

static uint8_t
siggen_vectors512_low25[32U] =
  {
    5U, 8U, 173U, 119U, 116U, 144U, 139U, 87U, 5U, 137U, 95U, 218U, 92U, 59U, 122U, 48U, 50U, 191U,
    133U, 218U, 183U, 35U, 43U, 249U, 129U, 23U, 112U, 25U, 243U, 215U, 100U, 96U
  };

static uint8_t
siggen_vectors512_low26[32U] =
  {
    172U, 217U, 243U, 182U, 54U, 38U, 197U, 243U, 33U, 3U, 233U, 14U, 29U, 209U, 105U, 89U, 7U,
    177U, 144U, 74U, 169U, 177U, 79U, 33U, 50U, 202U, 239U, 51U, 19U, 33U, 151U, 27U
  };

static uint8_t
siggen_vectors512_low27[32U] =
  {
    21U, 192U, 74U, 139U, 214U, 193U, 62U, 213U, 233U, 150U, 24U, 20U, 178U, 244U, 6U, 240U, 100U,
    103U, 1U, 83U, 228U, 213U, 70U, 93U, 206U, 246U, 60U, 29U, 157U, 213U, 42U, 135U
  };

static uint8_t
siggen_vectors512_low28[128U] =
  {
    109U, 84U, 154U, 168U, 122U, 253U, 184U, 191U, 166U, 13U, 34U, 166U, 142U, 39U, 131U, 178U,
    126U, 141U, 180U, 96U, 65U, 228U, 223U, 4U, 190U, 12U, 38U, 28U, 71U, 52U, 182U, 8U, 169U, 111U,
    25U, 141U, 28U, 219U, 141U, 8U, 42U, 228U, 133U, 121U, 236U, 157U, 239U, 207U, 33U, 251U, 199U,
    40U, 3U, 118U, 74U, 88U, 195U, 30U, 83U, 35U, 213U, 69U, 43U, 159U, 181U, 124U, 137U, 145U,
    211U, 23U, 73U, 20U, 13U, 167U, 239U, 6U, 123U, 24U, 191U, 13U, 125U, 251U, 174U, 110U, 239U,
    208U, 216U, 6U, 79U, 51U, 75U, 247U, 233U, 236U, 30U, 2U, 141U, 174U, 212U, 232U, 110U, 23U,
    99U, 94U, 194U, 228U, 9U, 163U, 237U, 18U, 56U, 4U, 138U, 69U, 136U, 44U, 92U, 87U, 80U, 27U,
    49U, 78U, 99U, 107U, 155U, 200U, 28U, 190U
  };

static uint8_t
siggen_vectors512_low29[32U] =
  {
    13U, 128U, 149U, 218U, 26U, 187U, 160U, 107U, 13U, 52U, 156U, 34U, 101U, 17U, 246U, 66U, 218U,
    187U, 241U, 4U, 58U, 212U, 27U, 170U, 78U, 20U, 41U, 122U, 254U, 138U, 49U, 23U
  };

static uint8_t
siggen_vectors512_low30[32U] =
  {
    117U, 164U, 87U, 88U, 206U, 212U, 94U, 207U, 85U, 247U, 85U, 203U, 86U, 202U, 38U, 1U, 215U,
    148U, 235U, 234U, 235U, 46U, 97U, 7U, 254U, 47U, 196U, 67U, 245U, 128U, 226U, 60U
  };

static uint8_t
siggen_vectors512_low31[32U] =
  {
    83U, 3U, 212U, 125U, 90U, 117U, 236U, 130U, 29U, 81U, 162U, 238U, 117U, 72U, 68U, 130U, 8U,
    198U, 153U, 236U, 160U, 205U, 137U, 129U, 15U, 252U, 26U, 164U, 250U, 248U, 30U, 173U
  };

static uint8_t
siggen_vectors512_low32[32U] =
  {
    81U, 101U, 197U, 77U, 239U, 64U, 38U, 171U, 100U, 143U, 119U, 104U, 196U, 241U, 72U, 139U, 203U,
    24U, 63U, 109U, 183U, 255U, 224U, 44U, 112U, 34U, 165U, 41U, 161U, 22U, 72U, 42U
  };

static uint8_t
siggen_vectors512_low33[32U] =
  {
    235U, 200U, 95U, 196U, 23U, 107U, 68U, 107U, 51U, 132U, 204U, 198U, 47U, 194U, 82U, 107U, 69U,
    102U, 85U, 97U, 160U, 231U, 233U, 64U, 74U, 195U, 118U, 201U, 14U, 69U, 11U, 89U
  };

static uint8_t
siggen_vectors512_low34[32U] =
  {
    139U, 44U, 9U, 66U, 142U, 98U, 197U, 16U, 157U, 23U, 237U, 12U, 248U, 249U, 253U, 124U, 55U,
    13U, 1U, 138U, 42U, 115U, 247U, 1U, 239U, 252U, 155U, 23U, 208U, 72U, 82U, 198U
  };

static uint8_t
siggen_vectors512_low35[128U] =
  {
    25U, 6U, 228U, 139U, 127U, 136U, 158U, 227U, 255U, 122U, 176U, 128U, 122U, 122U, 168U, 143U,
    83U, 244U, 1U, 136U, 8U, 135U, 11U, 254U, 214U, 55U, 42U, 119U, 51U, 12U, 115U, 118U, 71U, 150U,
    19U, 36U, 194U, 180U, 212U, 111U, 110U, 232U, 176U, 17U, 144U, 71U, 73U, 81U, 167U, 1U, 176U,
    72U, 174U, 134U, 87U, 159U, 248U, 227U, 252U, 136U, 159U, 236U, 249U, 38U, 177U, 127U, 152U,
    149U, 138U, 199U, 83U, 78U, 110U, 120U, 28U, 162U, 219U, 43U, 170U, 56U, 13U, 236U, 118U, 108U,
    251U, 42U, 62U, 202U, 42U, 157U, 88U, 24U, 150U, 125U, 100U, 223U, 171U, 132U, 247U, 104U, 210U,
    78U, 193U, 34U, 238U, 186U, 202U, 171U, 10U, 77U, 195U, 167U, 95U, 55U, 51U, 27U, 177U, 196U,
    61U, 216U, 150U, 108U, 192U, 158U, 196U, 148U, 91U, 189U
  };

static uint8_t
siggen_vectors512_low36[32U] =
  {
    82U, 254U, 87U, 218U, 52U, 39U, 177U, 167U, 92U, 184U, 22U, 246U, 28U, 78U, 142U, 14U, 5U, 81U,
    185U, 76U, 1U, 56U, 43U, 26U, 128U, 131U, 121U, 64U, 237U, 87U, 158U, 97U
  };

static uint8_t
siggen_vectors512_low37[32U] =
  {
    33U, 119U, 226U, 10U, 32U, 146U, 164U, 102U, 103U, 222U, 189U, 204U, 33U, 231U, 228U, 93U, 109U,
    167U, 47U, 18U, 74U, 222U, 203U, 197U, 173U, 166U, 167U, 188U, 199U, 180U, 1U, 213U
  };

static uint8_t
siggen_vectors512_low38[32U] =
  {
    85U, 14U, 70U, 143U, 38U, 38U, 7U, 10U, 8U, 10U, 254U, 235U, 152U, 237U, 215U, 90U, 114U, 30U,
    183U, 115U, 200U, 230U, 33U, 73U, 243U, 233U, 3U, 207U, 156U, 77U, 123U, 97U
  };

static uint8_t
siggen_vectors512_low39[32U] =
  {
    4U, 100U, 254U, 150U, 116U, 176U, 31U, 245U, 189U, 139U, 226U, 26U, 243U, 57U, 159U, 173U, 102U,
    249U, 10U, 211U, 15U, 78U, 142U, 230U, 226U, 235U, 155U, 204U, 207U, 213U, 24U, 92U
  };

static uint8_t
siggen_vectors512_low40[32U] =
  {
    248U, 37U, 15U, 7U, 63U, 52U, 3U, 76U, 28U, 222U, 88U, 246U, 154U, 133U, 226U, 245U, 160U, 48U,
    112U, 62U, 189U, 212U, 219U, 251U, 152U, 211U, 179U, 105U, 13U, 183U, 209U, 20U
  };

static uint8_t
siggen_vectors512_low41[32U] =
  {
    169U, 232U, 62U, 5U, 241U, 214U, 224U, 254U, 247U, 130U, 241U, 134U, 190U, 223U, 67U, 104U, 76U,
    130U, 90U, 196U, 128U, 23U, 77U, 72U, 176U, 228U, 211U, 21U, 5U, 226U, 116U, 152U
  };

static uint8_t
siggen_vectors512_low42[128U] =
  {
    123U, 89U, 254U, 241U, 61U, 175U, 1U, 175U, 236U, 53U, 222U, 163U, 39U, 101U, 65U, 190U, 104U,
    28U, 73U, 22U, 118U, 127U, 52U, 212U, 232U, 116U, 70U, 77U, 32U, 151U, 152U, 99U, 238U, 119U,
    173U, 15U, 209U, 99U, 91U, 205U, 249U, 62U, 159U, 98U, 237U, 105U, 174U, 82U, 236U, 144U, 170U,
    181U, 187U, 248U, 127U, 137U, 81U, 33U, 55U, 71U, 204U, 236U, 159U, 56U, 199U, 117U, 193U, 223U,
    30U, 157U, 127U, 115U, 92U, 44U, 227U, 155U, 66U, 237U, 179U, 176U, 197U, 8U, 98U, 71U, 85U,
    108U, 254U, 165U, 57U, 153U, 92U, 93U, 150U, 137U, 118U, 82U, 136U, 236U, 96U, 8U, 72U, 236U,
    240U, 133U, 192U, 28U, 167U, 56U, 187U, 239U, 17U, 245U, 209U, 45U, 68U, 87U, 219U, 152U, 139U,
    74U, 221U, 144U, 190U, 0U, 120U, 16U, 36U, 173U
  };

static uint8_t
siggen_vectors512_low43[32U] =
  {
    0U, 61U, 145U, 97U, 20U, 69U, 145U, 159U, 89U, 191U, 227U, 202U, 113U, 254U, 11U, 253U, 235U,
    14U, 57U, 167U, 25U, 94U, 131U, 172U, 3U, 163U, 124U, 126U, 206U, 239U, 13U, 242U
  };

static uint8_t
siggen_vectors512_low44[32U] =
  {
    123U, 156U, 89U, 47U, 97U, 170U, 224U, 85U, 88U, 85U, 208U, 185U, 235U, 182U, 253U, 0U, 251U,
    103U, 70U, 232U, 132U, 46U, 37U, 35U, 86U, 92U, 133U, 134U, 48U, 185U, 186U
  };

static uint8_t
siggen_vectors512_low45[32U] =
  {
    211U, 91U, 46U, 22U, 139U, 24U, 117U, 187U, 197U, 99U, 190U, 165U, 232U, 214U, 60U, 78U, 56U,
    149U, 124U, 119U, 74U, 101U, 231U, 98U, 149U, 154U, 52U, 158U, 175U, 38U, 59U, 160U
  };

static uint8_t
siggen_vectors512_low46[32U] =
  {
    239U, 157U, 242U, 145U, 234U, 39U, 164U, 180U, 87U, 8U, 247U, 96U, 135U, 35U, 194U, 125U, 125U,
    86U, 183U, 223U, 5U, 153U, 165U, 75U, 194U, 194U, 250U, 187U, 255U, 55U, 59U, 64U
  };

static uint8_t
siggen_vectors512_low47[32U] =
  {
    102U, 208U, 87U, 253U, 57U, 149U, 139U, 14U, 73U, 50U, 186U, 205U, 112U, 161U, 118U, 155U, 186U,
    220U, 182U, 46U, 68U, 112U, 147U, 123U, 69U, 73U, 122U, 61U, 69U, 0U, 250U, 187U
  };

static uint8_t
siggen_vectors512_low48[32U] =
  {
    108U, 133U, 59U, 136U, 158U, 24U, 181U, 164U, 158U, 229U, 75U, 84U, 221U, 26U, 174U, 223U, 221U,
    100U, 46U, 48U, 235U, 161U, 113U, 197U, 202U, 182U, 119U, 240U, 223U, 158U, 115U, 24U
  };

static uint8_t
siggen_vectors512_low49[128U] =
  {
    4U, 26U, 103U, 103U, 169U, 53U, 220U, 61U, 137U, 133U, 235U, 78U, 96U, 139U, 12U, 191U, 235U,
    231U, 249U, 55U, 137U, 212U, 32U, 11U, 207U, 229U, 149U, 39U, 122U, 194U, 176U, 244U, 2U, 136U,
    155U, 88U, 11U, 114U, 222U, 245U, 218U, 119U, 138U, 104U, 15U, 211U, 128U, 201U, 85U, 66U, 31U,
    98U, 109U, 82U, 221U, 154U, 131U, 234U, 24U, 1U, 135U, 184U, 80U, 225U, 183U, 42U, 78U, 198U,
    221U, 99U, 35U, 94U, 89U, 143U, 209U, 90U, 155U, 25U, 248U, 206U, 154U, 236U, 29U, 35U, 240U,
    189U, 110U, 164U, 217U, 35U, 96U, 213U, 15U, 149U, 17U, 82U, 188U, 154U, 1U, 53U, 71U, 50U,
    186U, 12U, 249U, 10U, 174U, 211U, 60U, 48U, 124U, 29U, 232U, 250U, 61U, 20U, 249U, 72U, 145U,
    81U, 184U, 55U, 123U, 87U, 199U, 33U, 95U, 11U
  };

static uint8_t
siggen_vectors512_low50[32U] =
  {
    72U, 241U, 61U, 57U, 56U, 153U, 205U, 131U, 92U, 65U, 147U, 103U, 14U, 198U, 47U, 40U, 228U,
    196U, 144U, 62U, 11U, 190U, 88U, 23U, 191U, 9U, 150U, 131U, 26U, 114U, 11U, 183U
  };

static uint8_t
siggen_vectors512_low51[32U] =
  {
    130U, 161U, 169U, 111U, 70U, 72U, 57U, 60U, 94U, 66U, 99U, 62U, 205U, 235U, 29U, 130U, 69U,
    199U, 140U, 94U, 162U, 54U, 181U, 186U, 180U, 96U, 222U, 220U, 200U, 146U, 75U, 192U
  };

static uint8_t
siggen_vectors512_low52[32U] =
  {
    232U, 203U, 240U, 60U, 52U, 181U, 21U, 79U, 135U, 109U, 225U, 159U, 59U, 182U, 253U, 67U, 205U,
    46U, 171U, 246U, 231U, 201U, 84U, 103U, 188U, 250U, 140U, 143U, 196U, 45U, 118U, 253U
  };

static uint8_t
siggen_vectors512_low53[32U] =
  {
    239U, 237U, 115U, 110U, 98U, 120U, 153U, 254U, 169U, 68U, 0U, 126U, 234U, 57U, 164U, 166U, 60U,
    12U, 46U, 38U, 73U, 28U, 209U, 42U, 219U, 84U, 107U, 227U, 229U, 198U, 143U, 125U
  };

static uint8_t
siggen_vectors512_low54[32U] =
  {
    207U, 127U, 194U, 75U, 218U, 160U, 154U, 192U, 204U, 168U, 73U, 126U, 19U, 41U, 139U, 150U, 19U,
    128U, 102U, 134U, 19U, 199U, 73U, 57U, 84U, 4U, 140U, 6U, 56U, 90U, 112U, 68U
  };

static uint8_t
siggen_vectors512_low55[32U] =
  {
    243U, 139U, 28U, 131U, 6U, 207U, 130U, 171U, 118U, 238U, 58U, 119U, 43U, 20U, 65U, 107U, 73U,
    153U, 63U, 225U, 31U, 152U, 110U, 155U, 15U, 5U, 147U, 197U, 46U, 201U, 21U, 37U
  };

static uint8_t
siggen_vectors512_low56[128U] =
  {
    121U, 5U, 169U, 3U, 110U, 2U, 44U, 120U, 178U, 201U, 239U, 212U, 11U, 119U, 176U, 161U, 148U,
    251U, 193U, 212U, 84U, 98U, 119U, 155U, 11U, 118U, 173U, 48U, 220U, 82U, 197U, 100U, 228U, 138U,
    73U, 61U, 130U, 73U, 160U, 97U, 230U, 47U, 38U, 244U, 83U, 186U, 86U, 101U, 56U, 164U, 212U,
    60U, 100U, 251U, 159U, 219U, 209U, 243U, 100U, 9U, 49U, 100U, 51U, 198U, 240U, 116U, 225U, 180U,
    123U, 84U, 74U, 132U, 125U, 226U, 95U, 198U, 125U, 129U, 172U, 128U, 30U, 217U, 247U, 55U, 26U,
    67U, 218U, 57U, 0U, 28U, 144U, 118U, 111U, 148U, 62U, 98U, 157U, 116U, 208U, 67U, 107U, 161U,
    36U, 12U, 61U, 127U, 171U, 153U, 13U, 88U, 106U, 109U, 110U, 241U, 119U, 23U, 134U, 114U, 45U,
    245U, 100U, 72U, 129U, 95U, 47U, 237U, 164U, 143U
  };

static uint8_t
siggen_vectors512_low57[32U] =
  {
    149U, 201U, 156U, 249U, 236U, 38U, 72U, 2U, 117U, 242U, 61U, 228U, 25U, 228U, 27U, 183U, 121U,
    89U, 15U, 14U, 171U, 92U, 249U, 9U, 93U, 55U, 221U, 112U, 203U, 117U, 232U, 112U
  };

static uint8_t
siggen_vectors512_low58[32U] =
  {
    66U, 194U, 146U, 176U, 251U, 204U, 159U, 69U, 122U, 227U, 97U, 217U, 64U, 169U, 212U, 90U, 217U,
    66U, 116U, 49U, 161U, 5U, 166U, 229U, 205U, 144U, 163U, 69U, 254U, 53U, 7U, 247U
  };

static uint8_t
siggen_vectors512_low59[32U] =
  {
    49U, 59U, 8U, 253U, 47U, 163U, 81U, 144U, 139U, 49U, 120U, 5U, 30U, 231U, 130U, 204U, 98U, 185U,
    149U, 74U, 217U, 93U, 65U, 25U, 170U, 86U, 73U, 0U, 248U, 173U, 231U, 12U
  };

static uint8_t
siggen_vectors512_low60[32U] =
  {
    76U, 8U, 221U, 15U, 139U, 114U, 174U, 156U, 103U, 78U, 30U, 68U, 141U, 78U, 42U, 254U, 58U, 30U,
    230U, 153U, 39U, 250U, 35U, 187U, 255U, 55U, 22U, 240U, 185U, 149U, 83U, 183U
  };

static uint8_t
siggen_vectors512_low61[32U] =
  {
    242U, 188U, 53U, 235U, 27U, 132U, 136U, 185U, 232U, 212U, 161U, 219U, 178U, 0U, 225U, 171U,
    203U, 133U, 84U, 88U, 225U, 85U, 125U, 193U, 191U, 152U, 130U, 120U, 161U, 116U, 235U, 59U
  };

static uint8_t
siggen_vectors512_low62[32U] =
  {
    237U, 154U, 46U, 192U, 67U, 161U, 213U, 120U, 232U, 235U, 166U, 245U, 114U, 23U, 151U, 99U, 16U,
    232U, 103U, 67U, 133U, 173U, 45U, 160U, 141U, 97U, 70U, 198U, 41U, 222U, 28U, 217U
  };

static uint8_t
siggen_vectors512_low63[128U] =
  {
    207U, 37U, 228U, 100U, 45U, 79U, 57U, 209U, 90U, 251U, 122U, 236U, 121U, 70U, 157U, 130U, 252U,
    154U, 237U, 184U, 248U, 153U, 100U, 231U, 155U, 116U, 154U, 133U, 45U, 147U, 29U, 55U, 67U,
    101U, 2U, 128U, 78U, 57U, 85U, 95U, 90U, 60U, 117U, 221U, 149U, 143U, 213U, 41U, 26U, 218U,
    100U, 124U, 26U, 94U, 56U, 254U, 123U, 16U, 72U, 241U, 111U, 43U, 113U, 31U, 221U, 93U, 57U,
    172U, 192U, 129U, 44U, 166U, 91U, 213U, 13U, 127U, 129U, 25U, 242U, 253U, 25U, 90U, 177U, 102U,
    51U, 80U, 58U, 120U, 238U, 145U, 2U, 193U, 249U, 196U, 194U, 37U, 104U, 224U, 181U, 75U, 212U,
    250U, 63U, 95U, 247U, 180U, 145U, 96U, 191U, 35U, 231U, 226U, 35U, 27U, 30U, 190U, 187U, 218U,
    240U, 228U, 167U, 212U, 72U, 65U, 88U, 168U, 126U, 7U
  };

static uint8_t
siggen_vectors512_low64[32U] =
  {
    225U, 94U, 131U, 93U, 14U, 34U, 23U, 188U, 124U, 111U, 5U, 164U, 152U, 242U, 10U, 241U, 205U,
    86U, 242U, 241U, 101U, 194U, 61U, 34U, 94U, 179U, 54U, 10U, 162U, 197U, 203U, 207U
  };

static uint8_t
siggen_vectors512_low65[32U] =
  {
    137U, 221U, 34U, 5U, 46U, 195U, 171U, 72U, 64U, 32U, 106U, 98U, 242U, 39U, 12U, 33U, 231U, 131U,
    109U, 26U, 145U, 9U, 163U, 64U, 125U, 208U, 151U, 76U, 120U, 2U, 185U, 174U
  };

static uint8_t
siggen_vectors512_low66[32U] =
  {
    233U, 22U, 9U, 186U, 53U, 199U, 0U, 139U, 8U, 12U, 119U, 169U, 6U, 141U, 151U, 161U, 76U, 167U,
    123U, 151U, 41U, 158U, 116U, 148U, 82U, 23U, 103U, 43U, 47U, 213U, 250U, 240U
  };

static uint8_t
siggen_vectors512_low67[32U] =
  {
    201U, 246U, 33U, 68U, 28U, 35U, 95U, 196U, 126U, 195U, 78U, 239U, 76U, 8U, 98U, 93U, 241U, 236U,
    116U, 145U, 142U, 31U, 134U, 7U, 91U, 117U, 63U, 37U, 137U, 244U, 198U, 11U
  };

static uint8_t
siggen_vectors512_low68[32U] =
  {
    167U, 13U, 26U, 45U, 85U, 93U, 89U, 155U, 251U, 140U, 155U, 31U, 13U, 67U, 114U, 83U, 65U, 21U,
    29U, 23U, 168U, 208U, 132U, 95U, 165U, 111U, 53U, 99U, 112U, 53U, 40U, 167U
  };

static uint8_t
siggen_vectors512_low69[32U] =
  {
    78U, 5U, 196U, 90U, 223U, 65U, 120U, 62U, 57U, 74U, 83U, 18U, 248U, 110U, 102U, 135U, 28U, 75U,
    228U, 137U, 105U, 72U, 200U, 89U, 102U, 135U, 157U, 92U, 102U, 213U, 75U, 55U
  };

static uint8_t
siggen_vectors512_low70[128U] =
  {
    117U, 98U, 196U, 69U, 179U, 88U, 131U, 204U, 147U, 123U, 230U, 52U, 155U, 76U, 239U, 195U, 85U,
    106U, 128U, 37U, 93U, 112U, 240U, 158U, 40U, 195U, 243U, 147U, 218U, 172U, 25U, 68U, 42U, 126U,
    236U, 237U, 205U, 251U, 232U, 247U, 98U, 142U, 48U, 205U, 137U, 57U, 83U, 126U, 197U, 109U, 92U,
    150U, 69U, 212U, 51U, 64U, 235U, 78U, 120U, 252U, 93U, 212U, 50U, 45U, 232U, 160U, 121U, 102U,
    178U, 98U, 119U, 13U, 127U, 241U, 58U, 7U, 31U, 243U, 220U, 229U, 96U, 113U, 142U, 96U, 237U,
    48U, 134U, 183U, 224U, 0U, 58U, 106U, 186U, 254U, 145U, 175U, 144U, 175U, 134U, 115U, 60U, 232U,
    104U, 148U, 64U, 191U, 115U, 210U, 170U, 10U, 207U, 233U, 119U, 96U, 54U, 232U, 119U, 89U, 154U,
    203U, 171U, 252U, 176U, 59U, 179U, 181U, 15U, 170U
  };

static uint8_t
siggen_vectors512_low71[32U] =
  {
    128U, 140U, 8U, 192U, 215U, 116U, 35U, 166U, 254U, 170U, 255U, 200U, 249U, 138U, 41U, 72U, 241U,
    119U, 38U, 230U, 124U, 21U, 238U, 174U, 78U, 103U, 46U, 219U, 227U, 136U, 249U, 140U
  };

static uint8_t
siggen_vectors512_low72[32U] =
  {
    176U, 192U, 173U, 94U, 31U, 96U, 1U, 216U, 233U, 1U, 142U, 198U, 17U, 178U, 227U, 185U, 25U,
    35U, 230U, 159U, 166U, 201U, 134U, 144U, 171U, 100U, 77U, 101U, 15U, 100U, 12U, 66U
  };

static uint8_t
siggen_vectors512_low73[32U] =
  {
    97U, 5U, 57U, 192U, 185U, 237U, 33U, 172U, 10U, 47U, 39U, 82U, 124U, 26U, 97U, 217U, 180U, 124U,
    191U, 3U, 49U, 135U, 177U, 166U, 173U, 160U, 6U, 235U, 91U, 38U, 98U, 237U
  };

static uint8_t
siggen_vectors512_low74[32U] =
  {
    31U, 109U, 74U, 144U, 92U, 118U, 26U, 83U, 213U, 76U, 54U, 41U, 118U, 113U, 125U, 13U, 127U,
    201U, 77U, 34U, 43U, 181U, 72U, 158U, 72U, 48U, 8U, 10U, 26U, 103U, 83U, 93U
  };

static uint8_t
siggen_vectors512_low75[32U] =
  {
    131U, 64U, 77U, 207U, 131U, 32U, 186U, 242U, 6U, 56U, 24U, 0U, 7U, 30U, 106U, 117U, 22U, 3U,
    66U, 209U, 151U, 67U, 180U, 241U, 118U, 150U, 13U, 102U, 157U, 208U, 61U, 7U
  };

static uint8_t
siggen_vectors512_low76[32U] =
  {
    63U, 117U, 220U, 241U, 2U, 0U, 139U, 41U, 137U, 248U, 22U, 131U, 174U, 69U, 233U, 241U, 212U,
    182U, 122U, 110U, 246U, 253U, 92U, 138U, 244U, 72U, 40U, 175U, 128U, 225U, 207U, 181U
  };

static uint8_t
siggen_vectors512_low77[128U] =
  {
    5U, 28U, 45U, 184U, 231U, 30U, 68U, 101U, 62U, 161U, 203U, 10U, 252U, 158U, 10U, 189U, 241U,
    38U, 88U, 233U, 231U, 97U, 191U, 183U, 103U, 194U, 12U, 122U, 180U, 173U, 252U, 177U, 142U,
    217U, 181U, 195U, 114U, 163U, 172U, 17U, 216U, 164U, 60U, 85U, 247U, 249U, 155U, 51U, 53U, 84U,
    55U, 137U, 22U, 134U, 212U, 35U, 98U, 171U, 215U, 29U, 184U, 182U, 216U, 77U, 214U, 148U, 214U,
    152U, 47U, 6U, 18U, 23U, 138U, 147U, 122U, 169U, 52U, 185U, 172U, 60U, 7U, 148U, 195U, 144U,
    39U, 189U, 215U, 103U, 132U, 28U, 67U, 112U, 102U, 108U, 128U, 219U, 192U, 248U, 19U, 44U, 162U,
    116U, 116U, 245U, 83U, 210U, 102U, 222U, 239U, 215U, 201U, 219U, 173U, 109U, 115U, 79U, 144U,
    6U, 187U, 85U, 117U, 103U, 112U, 27U, 183U, 230U, 167U, 201U
  };

static uint8_t
siggen_vectors512_low78[32U] =
  {
    247U, 198U, 49U, 95U, 0U, 129U, 172U, 216U, 240U, 156U, 122U, 44U, 62U, 193U, 183U, 236U, 226U,
    1U, 128U, 176U, 166U, 54U, 90U, 39U, 220U, 216U, 247U, 27U, 114U, 149U, 88U, 249U
  };

static uint8_t
siggen_vectors512_low79[32U] =
  {
    37U, 15U, 113U, 18U, 211U, 129U, 193U, 117U, 24U, 96U, 4U, 93U, 155U, 202U, 242U, 13U, 190U,
    178U, 90U, 0U, 20U, 49U, 249U, 106U, 198U, 241U, 145U, 9U, 54U, 47U, 254U, 187U
  };

static uint8_t
siggen_vectors512_low80[32U] =
  {
    73U, 251U, 169U, 239U, 231U, 53U, 70U, 19U, 90U, 90U, 49U, 171U, 55U, 83U, 226U, 71U, 3U, 71U,
    65U, 206U, 131U, 157U, 61U, 148U, 189U, 115U, 147U, 108U, 74U, 23U, 228U, 170U
  };

static uint8_t
siggen_vectors512_low81[32U] =
  {
    104U, 194U, 153U, 190U, 44U, 12U, 109U, 82U, 210U, 8U, 213U, 209U, 169U, 224U, 255U, 162U, 175U,
    25U, 180U, 131U, 50U, 113U, 64U, 78U, 88U, 118U, 224U, 170U, 147U, 152U, 120U, 102U
  };

static uint8_t
siggen_vectors512_low82[32U] =
  {
    123U, 25U, 94U, 146U, 210U, 186U, 149U, 145U, 28U, 218U, 117U, 112U, 96U, 126U, 17U, 45U, 2U,
    161U, 200U, 71U, 221U, 170U, 51U, 146U, 71U, 52U, 181U, 31U, 93U, 129U, 173U, 171U
  };

static uint8_t
siggen_vectors512_low83[32U] =
  {
    16U, 217U, 242U, 6U, 117U, 92U, 239U, 112U, 171U, 81U, 67U, 172U, 67U, 243U, 248U, 211U, 138U,
    234U, 38U, 68U, 243U, 29U, 82U, 234U, 243U, 180U, 114U, 238U, 129U, 110U, 17U, 229U
  };

static uint8_t
siggen_vectors512_low84[128U] =
  {
    77U, 203U, 123U, 98U, 186U, 49U, 184U, 102U, 252U, 231U, 193U, 254U, 237U, 240U, 190U, 31U,
    103U, 191U, 97U, 29U, 188U, 46U, 46U, 134U, 240U, 4U, 66U, 47U, 103U, 179U, 188U, 24U, 57U,
    198U, 149U, 142U, 177U, 220U, 62U, 173U, 19U, 124U, 61U, 127U, 136U, 170U, 151U, 36U, 69U, 119U,
    167U, 117U, 200U, 2U, 27U, 22U, 66U, 168U, 100U, 123U, 186U, 130U, 135U, 30U, 60U, 21U, 208U,
    116U, 158U, 211U, 67U, 234U, 108U, 173U, 56U, 241U, 35U, 131U, 93U, 142U, 246U, 107U, 7U, 25U,
    39U, 49U, 5U, 233U, 36U, 232U, 104U, 91U, 101U, 253U, 93U, 196U, 48U, 239U, 188U, 53U, 176U,
    90U, 96U, 151U, 241U, 126U, 188U, 89U, 67U, 205U, 205U, 154U, 188U, 186U, 117U, 43U, 127U, 143U,
    55U, 2U, 116U, 9U, 189U, 110U, 17U, 205U, 21U, 143U
  };

static uint8_t
siggen_vectors512_low85[32U] =
  {
    245U, 71U, 115U, 90U, 148U, 9U, 56U, 109U, 191U, 247U, 25U, 206U, 45U, 174U, 3U, 197U, 12U,
    180U, 55U, 214U, 179U, 12U, 199U, 250U, 62U, 162U, 13U, 154U, 236U, 23U, 229U, 165U
  };

static uint8_t
siggen_vectors512_low86[32U] =
  {
    76U, 168U, 124U, 88U, 69U, 251U, 4U, 194U, 247U, 106U, 227U, 39U, 48U, 115U, 176U, 82U, 62U,
    53U, 106U, 68U, 94U, 78U, 149U, 115U, 114U, 96U, 235U, 169U, 226U, 208U, 33U, 219U
  };

static uint8_t
siggen_vectors512_low87[32U] =
  {
    15U, 134U, 71U, 93U, 7U, 248U, 38U, 85U, 50U, 15U, 223U, 44U, 216U, 219U, 35U, 178U, 25U, 5U,
    177U, 177U, 242U, 249U, 196U, 142U, 45U, 248U, 126U, 36U, 17U, 156U, 72U, 128U
  };

static uint8_t
siggen_vectors512_low88[32U] =
  {
    145U, 189U, 125U, 151U, 247U, 237U, 50U, 83U, 206U, 222U, 252U, 20U, 71U, 113U, 187U, 138U,
    203U, 189U, 166U, 235U, 36U, 249U, 215U, 82U, 187U, 225U, 221U, 1U, 142U, 19U, 132U, 199U
  };

static uint8_t
siggen_vectors512_low89[32U] =
  {
    0U, 140U, 23U, 85U, 211U, 223U, 129U, 230U, 78U, 37U, 39U, 13U, 186U, 169U, 57U, 102U, 65U, 85U,
    109U, 247U, 255U, 199U, 172U, 154U, 221U, 103U, 57U, 195U, 130U, 112U, 83U, 151U
  };

static uint8_t
siggen_vectors512_low90[32U] =
  {
    119U, 223U, 68U, 60U, 114U, 155U, 3U, 154U, 222U, 213U, 181U, 22U, 177U, 7U, 127U, 236U, 221U,
    153U, 134U, 64U, 45U, 44U, 75U, 1U, 115U, 75U, 169U, 30U, 5U, 94U, 135U, 252U
  };

static uint8_t
siggen_vectors512_low91[128U] =
  {
    239U, 229U, 87U, 55U, 119U, 16U, 112U, 213U, 172U, 121U, 35U, 107U, 4U, 227U, 251U, 175U, 79U,
    46U, 155U, 237U, 24U, 125U, 25U, 48U, 104U, 15U, 207U, 26U, 186U, 118U, 150U, 116U, 191U, 66U,
    99U, 16U, 242U, 18U, 69U, 0U, 111U, 82U, 135U, 121U, 52U, 125U, 40U, 184U, 174U, 172U, 210U,
    177U, 213U, 227U, 69U, 109U, 203U, 241U, 136U, 178U, 190U, 140U, 7U, 241U, 146U, 25U, 228U, 6U,
    124U, 30U, 124U, 151U, 20U, 120U, 66U, 133U, 216U, 186U, 199U, 154U, 118U, 181U, 111U, 46U, 38U,
    118U, 234U, 147U, 153U, 79U, 17U, 235U, 87U, 58U, 241U, 208U, 63U, 200U, 237U, 17U, 24U, 234U,
    252U, 127U, 7U, 168U, 47U, 50U, 99U, 195U, 62U, 184U, 94U, 73U, 126U, 24U, 244U, 53U, 212U, 7U,
    106U, 119U, 79U, 66U, 210U, 118U, 195U, 35U
  };

static uint8_t
siggen_vectors512_low92[32U] =
  {
    38U, 161U, 170U, 75U, 146U, 122U, 81U, 107U, 102U, 25U, 134U, 137U, 90U, 255U, 88U, 244U, 11U,
    120U, 204U, 93U, 12U, 118U, 126U, 218U, 126U, 170U, 61U, 187U, 131U, 91U, 86U, 40U
  };

static uint8_t
siggen_vectors512_low93[32U] =
  {
    40U, 175U, 163U, 176U, 248U, 26U, 14U, 149U, 173U, 48U, 47U, 72U, 122U, 155U, 103U, 159U, 205U,
    239U, 141U, 63U, 64U, 35U, 110U, 196U, 212U, 219U, 244U, 187U, 12U, 187U, 168U, 178U
  };

static uint8_t
siggen_vectors512_low94[32U] =
  {
    187U, 74U, 193U, 190U, 132U, 5U, 203U, 174U, 138U, 85U, 63U, 188U, 40U, 226U, 158U, 46U, 104U,
    159U, 171U, 231U, 222U, 242U, 109U, 101U, 58U, 29U, 175U, 192U, 35U, 243U, 206U, 207U
  };

static uint8_t
siggen_vectors512_low95[32U] =
  {
    249U, 142U, 25U, 51U, 199U, 250U, 212U, 172U, 190U, 148U, 217U, 92U, 27U, 1U, 62U, 29U, 105U,
    49U, 250U, 143U, 103U, 230U, 219U, 182U, 119U, 181U, 100U, 239U, 124U, 62U, 86U, 206U
  };

static uint8_t
siggen_vectors512_low96[32U] =
  {
    21U, 169U, 165U, 65U, 45U, 106U, 3U, 237U, 215U, 27U, 132U, 193U, 33U, 206U, 154U, 148U, 205U,
    209U, 102U, 228U, 13U, 169U, 206U, 77U, 121U, 241U, 175U, 255U, 106U, 57U, 90U, 83U
  };

static uint8_t
siggen_vectors512_low97[32U] =
  {
    134U, 187U, 194U, 182U, 198U, 59U, 173U, 112U, 110U, 192U, 176U, 147U, 87U, 142U, 63U, 6U, 71U,
    54U, 236U, 105U, 192U, 219U, 165U, 155U, 158U, 62U, 127U, 115U, 118U, 42U, 77U, 195U
  };

static uint8_t
siggen_vectors512_low98[128U] =
  {
    234U, 149U, 133U, 156U, 193U, 60U, 204U, 179U, 113U, 152U, 217U, 25U, 128U, 59U, 232U, 156U,
    46U, 225U, 11U, 239U, 220U, 175U, 93U, 90U, 250U, 9U, 220U, 197U, 41U, 211U, 51U, 174U, 30U,
    79U, 253U, 59U, 216U, 186U, 134U, 66U, 32U, 59U, 173U, 215U, 168U, 10U, 63U, 119U, 238U, 238U,
    148U, 2U, 238U, 211U, 101U, 213U, 63U, 5U, 193U, 169U, 149U, 197U, 54U, 248U, 35U, 107U, 166U,
    182U, 255U, 136U, 151U, 57U, 53U, 6U, 102U, 12U, 200U, 234U, 130U, 178U, 22U, 58U, 166U, 161U,
    133U, 82U, 81U, 200U, 125U, 147U, 94U, 35U, 133U, 127U, 227U, 91U, 136U, 148U, 39U, 180U, 73U,
    222U, 114U, 116U, 215U, 117U, 75U, 222U, 172U, 233U, 96U, 180U, 48U, 60U, 93U, 213U, 247U, 69U,
    165U, 207U, 213U, 128U, 41U, 61U, 101U, 72U, 200U, 50U
  };

static uint8_t
siggen_vectors512_low99[32U] =
  {
    106U, 92U, 163U, 154U, 174U, 45U, 69U, 170U, 51U, 31U, 24U, 168U, 89U, 138U, 63U, 45U, 179U,
    39U, 129U, 247U, 201U, 46U, 253U, 79U, 100U, 238U, 59U, 190U, 12U, 76U, 78U, 73U
  };

static uint8_t
siggen_vectors512_low100[32U] =
  {
    198U, 44U, 196U, 163U, 154U, 206U, 1U, 0U, 106U, 212U, 140U, 244U, 154U, 62U, 113U, 70U, 105U,
    85U, 187U, 238U, 202U, 93U, 49U, 141U, 103U, 38U, 149U, 223U, 146U, 107U, 58U, 164U
  };

static uint8_t
siggen_vectors512_low101[32U] =
  {
    200U, 92U, 207U, 81U, 123U, 242U, 235U, 217U, 173U, 106U, 158U, 153U, 37U, 77U, 239U, 13U, 116U,
    209U, 210U, 253U, 97U, 30U, 50U, 139U, 74U, 57U, 136U, 212U, 240U, 69U, 254U, 111U
  };

static uint8_t
siggen_vectors512_low102[32U] =
  {
    218U, 192U, 12U, 70U, 43U, 200U, 91U, 243U, 156U, 49U, 181U, 224U, 29U, 243U, 62U, 46U, 193U,
    86U, 158U, 110U, 252U, 179U, 52U, 191U, 24U, 240U, 149U, 25U, 146U, 172U, 97U, 96U
  };

static uint8_t
siggen_vectors512_low103[32U] =
  {
    110U, 127U, 248U, 236U, 122U, 92U, 72U, 224U, 135U, 114U, 36U, 169U, 250U, 132U, 129U, 40U, 61U,
    228U, 95U, 203U, 238U, 35U, 180U, 194U, 82U, 176U, 198U, 34U, 68U, 44U, 38U, 173U
  };

static uint8_t
siggen_vectors512_low104[32U] =
  {
    61U, 250U, 195U, 32U, 185U, 200U, 115U, 49U, 129U, 23U, 218U, 107U, 216U, 86U, 0U, 10U, 57U,
    43U, 129U, 86U, 89U, 229U, 170U, 42U, 106U, 24U, 82U, 204U, 178U, 80U, 29U, 243U
  };

static __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors512_low105[15U] =
  {
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low0 },
        .snd = { .len = 32U, .b = siggen_vectors512_low1 },
        .thd = { .len = 32U, .b = siggen_vectors512_low2 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low3 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low4 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low5 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low6 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low7 },
        .snd = { .len = 32U, .b = siggen_vectors512_low8 },
        .thd = { .len = 32U, .b = siggen_vectors512_low9 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low10 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low11 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low12 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low13 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low14 },
        .snd = { .len = 32U, .b = siggen_vectors512_low15 },
        .thd = { .len = 32U, .b = siggen_vectors512_low16 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low17 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low18 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low19 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low20 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low21 },
        .snd = { .len = 32U, .b = siggen_vectors512_low22 },
        .thd = { .len = 32U, .b = siggen_vectors512_low23 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low24 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low25 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low26 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low27 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low28 },
        .snd = { .len = 32U, .b = siggen_vectors512_low29 },
        .thd = { .len = 32U, .b = siggen_vectors512_low30 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low31 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low32 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low33 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low34 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low35 },
        .snd = { .len = 32U, .b = siggen_vectors512_low36 },
        .thd = { .len = 32U, .b = siggen_vectors512_low37 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low38 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low39 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low40 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low41 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low42 },
        .snd = { .len = 32U, .b = siggen_vectors512_low43 },
        .thd = { .len = 32U, .b = siggen_vectors512_low44 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low45 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low46 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low47 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low48 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low49 },
        .snd = { .len = 32U, .b = siggen_vectors512_low50 },
        .thd = { .len = 32U, .b = siggen_vectors512_low51 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low52 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low53 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low54 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low55 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low56 },
        .snd = { .len = 32U, .b = siggen_vectors512_low57 },
        .thd = { .len = 32U, .b = siggen_vectors512_low58 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low59 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low60 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low61 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low62 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low63 },
        .snd = { .len = 32U, .b = siggen_vectors512_low64 },
        .thd = { .len = 32U, .b = siggen_vectors512_low65 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low66 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low67 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low68 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low69 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low70 },
        .snd = { .len = 32U, .b = siggen_vectors512_low71 },
        .thd = { .len = 32U, .b = siggen_vectors512_low72 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low73 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low74 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low75 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low76 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low77 },
        .snd = { .len = 32U, .b = siggen_vectors512_low78 },
        .thd = { .len = 32U, .b = siggen_vectors512_low79 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low80 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low81 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low82 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low83 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low84 },
        .snd = { .len = 32U, .b = siggen_vectors512_low85 },
        .thd = { .len = 32U, .b = siggen_vectors512_low86 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low87 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low88 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low89 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low90 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low91 },
        .snd = { .len = 32U, .b = siggen_vectors512_low92 },
        .thd = { .len = 32U, .b = siggen_vectors512_low93 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low94 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low95 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low96 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low97 }
      }
    ),
    (
      (__Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t){
        .fst = { .len = 128U, .b = siggen_vectors512_low98 },
        .snd = { .len = 32U, .b = siggen_vectors512_low99 },
        .thd = { .len = 32U, .b = siggen_vectors512_low100 },
        .f3 = { .len = 32U, .b = siggen_vectors512_low101 },
        .f4 = { .len = 32U, .b = siggen_vectors512_low102 },
        .f5 = { .len = 32U, .b = siggen_vectors512_low103 },
        .f6 = { .len = 32U, .b = siggen_vectors512_low104 }
      }
    )
  };

static lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors512_low = { .len = 15U, .b = siggen_vectors512_low105 };

static bool compare_and_print(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  LowStar_Printf_print_string("Expected: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b1);
  LowStar_Printf_print_string("\n");
  LowStar_Printf_print_string("Computed: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b2);
  LowStar_Printf_print_string("\n");
  uint8_t res = 255U;
  for (uint32_t i = 0U; i < len; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(b1[i], b2[i]);
    res = (uint32_t)uu____0 & (uint32_t)res;
  }
  uint8_t z = res;
  bool b = z == 255U;
  if (b)
  {
    LowStar_Printf_print_string("PASS\n");
  }
  else
  {
    LowStar_Printf_print_string("FAIL\n");
  }
  return b;
}

static void
test_sigver256(
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  vec
)
{
  bool result = vec.f5;
  uint8_t *s = vec.f4.b;
  uint32_t s_len = vec.f4.len;
  uint8_t *r = vec.f3.b;
  uint32_t r_len = vec.f3.len;
  uint8_t *qy = vec.thd.b;
  uint32_t qy_len = vec.thd.len;
  uint8_t *qx = vec.snd.b;
  uint32_t qx_len = vec.snd.len;
  uint8_t *msg = vec.fst.b;
  uint32_t msg_len = vec.fst.len;
  if (!(qx_len == 32U && qy_len == 32U && r_len == 32U && s_len == 32U))
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, 32U * sizeof (uint8_t));
    memcpy(qxy + 32U, qy, 32U * sizeof (uint8_t));
    bool result_ = Hacl_P256_ecdsa_verif_p256_sha2(msg_len, msg, qxy, r, s);
    if (!(result_ == result))
    {
      LowStar_Printf_print_string("FAIL\n");
      exit((int32_t)1);
    }
  }
}

static void
test_sigver384(
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  vec
)
{
  bool result = vec.f5;
  uint8_t *s = vec.f4.b;
  uint32_t s_len = vec.f4.len;
  uint8_t *r = vec.f3.b;
  uint32_t r_len = vec.f3.len;
  uint8_t *qy = vec.thd.b;
  uint32_t qy_len = vec.thd.len;
  uint8_t *qx = vec.snd.b;
  uint32_t qx_len = vec.snd.len;
  uint8_t *msg = vec.fst.b;
  uint32_t msg_len = vec.fst.len;
  if (!(qx_len == 32U && qy_len == 32U && r_len == 32U && s_len == 32U))
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, 32U * sizeof (uint8_t));
    memcpy(qxy + 32U, qy, 32U * sizeof (uint8_t));
    bool result_ = Hacl_P256_ecdsa_verif_p256_sha384(msg_len, msg, qxy, r, s);
    if (!(result_ == result))
    {
      LowStar_Printf_print_string("FAIL\n");
      exit((int32_t)1);
    }
  }
}

static void
test_sigver512(
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  vec
)
{
  bool result = vec.f5;
  uint8_t *s = vec.f4.b;
  uint32_t s_len = vec.f4.len;
  uint8_t *r = vec.f3.b;
  uint32_t r_len = vec.f3.len;
  uint8_t *qy = vec.thd.b;
  uint32_t qy_len = vec.thd.len;
  uint8_t *qx = vec.snd.b;
  uint32_t qx_len = vec.snd.len;
  uint8_t *msg = vec.fst.b;
  uint32_t msg_len = vec.fst.len;
  if (!(qx_len == 32U && qy_len == 32U && r_len == 32U && s_len == 32U))
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, 32U * sizeof (uint8_t));
    memcpy(qxy + 32U, qy, 32U * sizeof (uint8_t));
    bool result_ = Hacl_P256_ecdsa_verif_p256_sha512(msg_len, msg, qxy, r, s);
    if (!(result_ == result))
    {
      LowStar_Printf_print_string("FAIL\n");
      exit((int32_t)1);
    }
  }
}

static bool check_bound(uint8_t *b)
{
  uint64_t zero = 0ULL;
  uint64_t q1 = 17562291160714782033ULL;
  uint64_t q2 = 13611842547513532036ULL;
  uint64_t q3 = 18446744073709551615ULL;
  uint64_t q4 = 18446744069414584320ULL;
  uint64_t u0 = load64_be(b);
  uint64_t x1 = u0;
  uint64_t u1 = load64_be(b + 8U);
  uint64_t x2 = u1;
  uint64_t u2 = load64_be(b + 16U);
  uint64_t x3 = u2;
  uint64_t u = load64_be(b + 24U);
  uint64_t x4 = u;
  uint64_t x11 = x1;
  uint64_t x21 = x2;
  uint64_t x31 = x3;
  uint64_t x41 = x4;
  bool
  r =
    x11
    < q4
    || (x11 == q4 && (x21 < q3 || (x21 == q3 && (x31 < q2 || (x31 == q2 && x41 < q1)))));
  bool r1 = x11 == zero && x21 == zero && x31 == zero && x41 == zero;
  return r && !r1;
}

static void
test_siggen_256(
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  vec
)
{
  uint8_t *s = vec.f6.b;
  uint32_t s_len = vec.f6.len;
  uint8_t *r = vec.f5.b;
  uint32_t r_len = vec.f5.len;
  uint8_t *k = vec.f4.b;
  uint32_t k_len = vec.f4.len;
  uint8_t *qy = vec.f3.b;
  uint32_t qy_len = vec.f3.len;
  uint8_t *qx = vec.thd.b;
  uint32_t qx_len = vec.thd.len;
  uint8_t *d = vec.snd.b;
  uint32_t d_len = vec.snd.len;
  uint8_t *msg = vec.fst.b;
  uint32_t msg_len = vec.fst.len;
  if (!(k_len == 32U && d_len == 32U))
  {
    exit((int32_t)-1);
  }
  bool bound_k = check_bound(k);
  bool bound_d = check_bound(d);
  if (!(bound_k && bound_d && qx_len == 32U && qy_len == 32U && r_len == 32U && s_len == 32U))
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t rs[64U] = { 0U };
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, 32U * sizeof (uint8_t));
    memcpy(qxy + 32U, qy, 32U * sizeof (uint8_t));
    bool flag = Hacl_P256_ecdsa_sign_p256_sha2(rs, msg_len, msg, d, k);
    if (flag)
    {
      bool okr = compare_and_print(rs, r, 32U);
      bool oks = compare_and_print(rs + 32U, s, 32U);
      if (okr && oks)
      {
        bool result = Hacl_P256_ecdsa_verif_p256_sha2(msg_len, msg, qxy, r, s);
        if (!result)
        {
          LowStar_Printf_print_string("FAIL: verification\n");
          exit((int32_t)1);
        }
      }
      else
      {
        LowStar_Printf_print_string("FAIL: signing\n");
        exit((int32_t)1);
      }
    }
    else
    {
      LowStar_Printf_print_string("FAIL: signing\n");
      exit((int32_t)1);
    }
  }
}

static void
test_siggen_384(
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  vec
)
{
  uint8_t *s = vec.f6.b;
  uint32_t s_len = vec.f6.len;
  uint8_t *r = vec.f5.b;
  uint32_t r_len = vec.f5.len;
  uint8_t *k = vec.f4.b;
  uint32_t k_len = vec.f4.len;
  uint8_t *qy = vec.f3.b;
  uint32_t qy_len = vec.f3.len;
  uint8_t *qx = vec.thd.b;
  uint32_t qx_len = vec.thd.len;
  uint8_t *d = vec.snd.b;
  uint32_t d_len = vec.snd.len;
  uint8_t *msg = vec.fst.b;
  uint32_t msg_len = vec.fst.len;
  if (!(k_len == 32U && d_len == 32U))
  {
    exit((int32_t)-1);
  }
  bool bound_k = check_bound(k);
  bool bound_d = check_bound(d);
  if (!(bound_k && bound_d && qx_len == 32U && qy_len == 32U && r_len == 32U && s_len == 32U))
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t rs[64U] = { 0U };
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, 32U * sizeof (uint8_t));
    memcpy(qxy + 32U, qy, 32U * sizeof (uint8_t));
    bool flag = Hacl_P256_ecdsa_sign_p256_sha384(rs, msg_len, msg, d, k);
    if (flag)
    {
      bool okr = compare_and_print(rs, r, 32U);
      bool oks = compare_and_print(rs + 32U, s, 32U);
      if (okr && oks)
      {
        bool result = Hacl_P256_ecdsa_verif_p256_sha384(msg_len, msg, qxy, r, s);
        if (!result)
        {
          LowStar_Printf_print_string("FAIL: verification\n");
          exit((int32_t)1);
        }
      }
      else
      {
        LowStar_Printf_print_string("FAIL: signing\n");
        exit((int32_t)1);
      }
    }
    else
    {
      LowStar_Printf_print_string("FAIL: signing\n");
      exit((int32_t)1);
    }
  }
}

static void
test_siggen_512(
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  vec
)
{
  uint8_t *s = vec.f6.b;
  uint32_t s_len = vec.f6.len;
  uint8_t *r = vec.f5.b;
  uint32_t r_len = vec.f5.len;
  uint8_t *k = vec.f4.b;
  uint32_t k_len = vec.f4.len;
  uint8_t *qy = vec.f3.b;
  uint32_t qy_len = vec.f3.len;
  uint8_t *qx = vec.thd.b;
  uint32_t qx_len = vec.thd.len;
  uint8_t *d = vec.snd.b;
  uint32_t d_len = vec.snd.len;
  uint8_t *msg = vec.fst.b;
  uint32_t msg_len = vec.fst.len;
  if (!(k_len == 32U && d_len == 32U))
  {
    exit((int32_t)-1);
  }
  bool bound_k = check_bound(k);
  bool bound_d = check_bound(d);
  if (!(bound_k && bound_d && qx_len == 32U && qy_len == 32U && r_len == 32U && s_len == 32U))
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t rs[64U] = { 0U };
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, 32U * sizeof (uint8_t));
    memcpy(qxy + 32U, qy, 32U * sizeof (uint8_t));
    bool flag = Hacl_P256_ecdsa_sign_p256_sha512(rs, msg_len, msg, d, k);
    if (flag)
    {
      bool okr = compare_and_print(rs, r, 32U);
      bool oks = compare_and_print(rs + 32U, s, 32U);
      if (okr && oks)
      {
        bool result = Hacl_P256_ecdsa_verif_p256_sha512(msg_len, msg, qxy, r, s);
        if (!result)
        {
          LowStar_Printf_print_string("FAIL: verification\n");
          exit((int32_t)1);
        }
      }
      else
      {
        LowStar_Printf_print_string("FAIL: signing\n");
        exit((int32_t)1);
      }
    }
    else
    {
      LowStar_Printf_print_string("FAIL: signing\n");
      exit((int32_t)1);
    }
  }
}

exit_code main(void)
{
  C_String_print("[ECDSA SigVer]");
  C_String_print("\n");
  uint32_t len = sigver_vectors256_low.len;
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  *vs0 = sigver_vectors256_low.b;
  for (uint32_t i = 0U; i < len; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len);
    LowStar_Printf_print_string("\n");
    test_sigver256(vs0[i]);
  }
  C_String_print("[ECDSA SigGen]");
  C_String_print("\n");
  uint32_t len0 = siggen_vectors256_low.len;
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  *vs1 = siggen_vectors256_low.b;
  for (uint32_t i = 0U; i < len0; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len0);
    LowStar_Printf_print_string("\n");
    test_siggen_256(vs1[i]);
  }
  C_String_print("[ECDSA SigVer - SHA384]");
  C_String_print("\n");
  uint32_t len1 = sigver_vectors384_low.len;
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  *vs2 = sigver_vectors384_low.b;
  for (uint32_t i = 0U; i < len1; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len1);
    LowStar_Printf_print_string("\n");
    test_sigver384(vs2[i]);
  }
  C_String_print("[ECDSA SigGen - SHA384]");
  C_String_print("\n");
  uint32_t len2 = siggen_vectors384_low.len;
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  *vs3 = siggen_vectors384_low.b;
  for (uint32_t i = 0U; i < len2; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len2);
    LowStar_Printf_print_string("\n");
    test_siggen_384(vs3[i]);
  }
  C_String_print("[ECDSA SigVer - SHA512]");
  C_String_print("\n");
  uint32_t len3 = sigver_vectors512_low.len;
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  *vs4 = sigver_vectors512_low.b;
  for (uint32_t i = 0U; i < len3; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len3);
    LowStar_Printf_print_string("\n");
    test_sigver512(vs4[i]);
  }
  C_String_print("[ECDSA SigGen - SHA512]");
  C_String_print("\n");
  uint32_t len4 = siggen_vectors512_low.len;
  __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
  *vs = siggen_vectors512_low.b;
  for (uint32_t i = 0U; i < len4; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + 1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len4);
    LowStar_Printf_print_string("\n");
    test_siggen_512(vs[i]);
  }
  return EXIT_SUCCESS;
}

