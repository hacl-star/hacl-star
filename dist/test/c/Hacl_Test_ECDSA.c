/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
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



extern void C_String_print(C_String_t uu___);


/*******************************************************************************

ECDSA and ECDH functions over the P-256 NIST curve.

This module implements signing and verification, key validation, conversions
between various point representations, and ECDH key agreement.

*******************************************************************************/

/**************/
/* Signatures */
/**************/

/*
  Per the standard, a hash function *shall* be used. Therefore, we recommend
  using one of the three combined hash-and-sign variants.
*/

/**
Hash the message with SHA2-256, then sign the resulting digest with the P256 signature function.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
extern bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/**
Hash the message with SHA2-384, then sign the resulting digest with the P256 signature function.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
extern bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);

/**
Hash the message with SHA2-512, then sign the resulting digest with the P256 signature function.

Input: result buffer: uint8[64], 
 m buffer: uint8 [mLen], 
 priv(ate)Key: uint8[32], 
 k (nonce): uint32[32]. 
  
 Output: bool, where True stands for the correct signature generation. False value means that an error has occurred. 
  
 The private key and the nonce are expected to be more than 0 and less than the curve order.
*/
extern bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *result,
  uint32_t mLen,
  uint8_t *m,
  uint8_t *privKey,
  uint8_t *k
);


/****************/
/* Verification */
/****************/

/*
  Verify a message signature. These functions internally validate the public key using validate_public_key.
*/


/**
 The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
extern bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/**
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
extern bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

/**
  The input of the function is considered to be public, 
  thus this code is not secret independent with respect to the operations done over the input.
  
 Input: m buffer: uint8 [mLen], 
 pub(lic)Key: uint8[64], 
 r: uint8[32], 
 s: uint8[32]. 
  
 Output: bool, where true stands for the correct signature verification. 
*/
extern bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t mLen,
  uint8_t *m,
  uint8_t *pubKey,
  uint8_t *r,
  uint8_t *s
);

extern void LowStar_Printf_print_string(Prims_string uu___);

extern void LowStar_Printf_print_u32(uint32_t uu___);

extern void LowStar_Printf_print_lmbuffer_u8(uint32_t l, uint8_t *b);

static uint8_t
sigver_vectors256_low0[128U] =
  {
    (uint8_t)228U, (uint8_t)121U, (uint8_t)109U, (uint8_t)181U, (uint8_t)247U, (uint8_t)133U,
    (uint8_t)242U, (uint8_t)7U, (uint8_t)170U, (uint8_t)48U, (uint8_t)211U, (uint8_t)17U,
    (uint8_t)105U, (uint8_t)59U, (uint8_t)55U, (uint8_t)2U, (uint8_t)130U, (uint8_t)29U,
    (uint8_t)255U, (uint8_t)17U, (uint8_t)104U, (uint8_t)253U, (uint8_t)46U, (uint8_t)4U,
    (uint8_t)192U, (uint8_t)131U, (uint8_t)104U, (uint8_t)37U, (uint8_t)174U, (uint8_t)253U,
    (uint8_t)133U, (uint8_t)13U, (uint8_t)154U, (uint8_t)166U, (uint8_t)3U, (uint8_t)38U,
    (uint8_t)216U, (uint8_t)140U, (uint8_t)222U, (uint8_t)26U, (uint8_t)35U, (uint8_t)199U,
    (uint8_t)116U, (uint8_t)83U, (uint8_t)81U, (uint8_t)57U, (uint8_t)44U, (uint8_t)162U,
    (uint8_t)40U, (uint8_t)141U, (uint8_t)99U, (uint8_t)44U, (uint8_t)38U, (uint8_t)79U,
    (uint8_t)25U, (uint8_t)125U, (uint8_t)5U, (uint8_t)205U, (uint8_t)66U, (uint8_t)74U,
    (uint8_t)48U, (uint8_t)51U, (uint8_t)108U, (uint8_t)25U, (uint8_t)253U, (uint8_t)9U,
    (uint8_t)187U, (uint8_t)34U, (uint8_t)150U, (uint8_t)84U, (uint8_t)240U, (uint8_t)34U,
    (uint8_t)47U, (uint8_t)203U, (uint8_t)136U, (uint8_t)26U, (uint8_t)75U, (uint8_t)53U,
    (uint8_t)194U, (uint8_t)144U, (uint8_t)160U, (uint8_t)147U, (uint8_t)172U, (uint8_t)21U,
    (uint8_t)156U, (uint8_t)225U, (uint8_t)52U, (uint8_t)9U, (uint8_t)17U, (uint8_t)31U,
    (uint8_t)240U, (uint8_t)53U, (uint8_t)132U, (uint8_t)17U, (uint8_t)19U, (uint8_t)60U,
    (uint8_t)36U, (uint8_t)245U, (uint8_t)184U, (uint8_t)226U, (uint8_t)9U, (uint8_t)13U,
    (uint8_t)109U, (uint8_t)182U, (uint8_t)85U, (uint8_t)138U, (uint8_t)252U, (uint8_t)54U,
    (uint8_t)240U, (uint8_t)108U, (uint8_t)161U, (uint8_t)246U, (uint8_t)239U, (uint8_t)119U,
    (uint8_t)151U, (uint8_t)133U, (uint8_t)173U, (uint8_t)186U, (uint8_t)104U, (uint8_t)219U,
    (uint8_t)39U, (uint8_t)164U, (uint8_t)9U, (uint8_t)133U, (uint8_t)159U, (uint8_t)196U,
    (uint8_t)196U, (uint8_t)160U
  };

static uint8_t
sigver_vectors256_low1[32U] =
  {
    (uint8_t)135U, (uint8_t)248U, (uint8_t)242U, (uint8_t)178U, (uint8_t)24U, (uint8_t)244U,
    (uint8_t)152U, (uint8_t)69U, (uint8_t)246U, (uint8_t)241U, (uint8_t)14U, (uint8_t)236U,
    (uint8_t)56U, (uint8_t)119U, (uint8_t)19U, (uint8_t)98U, (uint8_t)105U, (uint8_t)245U,
    (uint8_t)193U, (uint8_t)165U, (uint8_t)71U, (uint8_t)54U, (uint8_t)219U, (uint8_t)223U,
    (uint8_t)105U, (uint8_t)248U, (uint8_t)153U, (uint8_t)64U, (uint8_t)202U, (uint8_t)212U,
    (uint8_t)21U, (uint8_t)85U
  };

static uint8_t
sigver_vectors256_low2[32U] =
  {
    (uint8_t)225U, (uint8_t)95U, (uint8_t)54U, (uint8_t)144U, (uint8_t)54U, (uint8_t)244U,
    (uint8_t)152U, (uint8_t)66U, (uint8_t)250U, (uint8_t)199U, (uint8_t)168U, (uint8_t)108U,
    (uint8_t)138U, (uint8_t)43U, (uint8_t)5U, (uint8_t)87U, (uint8_t)96U, (uint8_t)151U,
    (uint8_t)118U, (uint8_t)129U, (uint8_t)68U, (uint8_t)72U, (uint8_t)184U, (uint8_t)245U,
    (uint8_t)232U, (uint8_t)74U, (uint8_t)169U, (uint8_t)244U, (uint8_t)57U, (uint8_t)82U,
    (uint8_t)5U, (uint8_t)233U
  };

static uint8_t
sigver_vectors256_low3[32U] =
  {
    (uint8_t)209U, (uint8_t)159U, (uint8_t)244U, (uint8_t)139U, (uint8_t)50U, (uint8_t)73U,
    (uint8_t)21U, (uint8_t)87U, (uint8_t)100U, (uint8_t)22U, (uint8_t)9U, (uint8_t)125U,
    (uint8_t)37U, (uint8_t)68U, (uint8_t)247U, (uint8_t)203U, (uint8_t)223U, (uint8_t)135U,
    (uint8_t)104U, (uint8_t)177U, (uint8_t)69U, (uint8_t)74U, (uint8_t)210U, (uint8_t)14U,
    (uint8_t)11U, (uint8_t)170U, (uint8_t)197U, (uint8_t)14U, (uint8_t)33U, (uint8_t)31U,
    (uint8_t)35U, (uint8_t)176U
  };

static uint8_t
sigver_vectors256_low4[32U] =
  {
    (uint8_t)163U, (uint8_t)232U, (uint8_t)30U, (uint8_t)89U, (uint8_t)49U, (uint8_t)28U,
    (uint8_t)223U, (uint8_t)255U, (uint8_t)45U, (uint8_t)71U, (uint8_t)132U, (uint8_t)148U,
    (uint8_t)159U, (uint8_t)122U, (uint8_t)44U, (uint8_t)181U, (uint8_t)11U, (uint8_t)166U,
    (uint8_t)195U, (uint8_t)169U, (uint8_t)31U, (uint8_t)165U, (uint8_t)71U, (uint8_t)16U,
    (uint8_t)86U, (uint8_t)142U, (uint8_t)97U, (uint8_t)172U, (uint8_t)163U, (uint8_t)232U,
    (uint8_t)71U, (uint8_t)198U
  };

static uint8_t
sigver_vectors256_low5[128U] =
  {
    (uint8_t)6U, (uint8_t)154U, (uint8_t)110U, (uint8_t)107U, (uint8_t)147U, (uint8_t)223U,
    (uint8_t)238U, (uint8_t)109U, (uint8_t)246U, (uint8_t)239U, (uint8_t)105U, (uint8_t)151U,
    (uint8_t)205U, (uint8_t)128U, (uint8_t)221U, (uint8_t)33U, (uint8_t)130U, (uint8_t)195U,
    (uint8_t)102U, (uint8_t)83U, (uint8_t)206U, (uint8_t)241U, (uint8_t)12U, (uint8_t)101U,
    (uint8_t)93U, (uint8_t)82U, (uint8_t)69U, (uint8_t)133U, (uint8_t)101U, (uint8_t)84U,
    (uint8_t)98U, (uint8_t)214U, (uint8_t)131U, (uint8_t)135U, (uint8_t)127U, (uint8_t)149U,
    (uint8_t)236U, (uint8_t)198U, (uint8_t)214U, (uint8_t)200U, (uint8_t)22U, (uint8_t)35U,
    (uint8_t)216U, (uint8_t)250U, (uint8_t)196U, (uint8_t)233U, (uint8_t)0U, (uint8_t)237U,
    (uint8_t)0U, (uint8_t)25U, (uint8_t)150U, (uint8_t)64U, (uint8_t)148U, (uint8_t)231U,
    (uint8_t)222U, (uint8_t)145U, (uint8_t)241U, (uint8_t)72U, (uint8_t)25U, (uint8_t)137U,
    (uint8_t)174U, (uint8_t)24U, (uint8_t)115U, (uint8_t)0U, (uint8_t)69U, (uint8_t)101U,
    (uint8_t)120U, (uint8_t)156U, (uint8_t)191U, (uint8_t)93U, (uint8_t)197U, (uint8_t)108U,
    (uint8_t)98U, (uint8_t)174U, (uint8_t)220U, (uint8_t)99U, (uint8_t)246U, (uint8_t)47U,
    (uint8_t)59U, (uint8_t)137U, (uint8_t)76U, (uint8_t)156U, (uint8_t)111U, (uint8_t)119U,
    (uint8_t)136U, (uint8_t)200U, (uint8_t)236U, (uint8_t)170U, (uint8_t)220U, (uint8_t)155U,
    (uint8_t)208U, (uint8_t)232U, (uint8_t)26U, (uint8_t)217U, (uint8_t)27U, (uint8_t)43U,
    (uint8_t)53U, (uint8_t)105U, (uint8_t)234U, (uint8_t)18U, (uint8_t)38U, (uint8_t)14U,
    (uint8_t)147U, (uint8_t)146U, (uint8_t)79U, (uint8_t)221U, (uint8_t)221U, (uint8_t)57U,
    (uint8_t)114U, (uint8_t)175U, (uint8_t)82U, (uint8_t)115U, (uint8_t)25U, (uint8_t)143U,
    (uint8_t)94U, (uint8_t)253U, (uint8_t)160U, (uint8_t)116U, (uint8_t)98U, (uint8_t)25U,
    (uint8_t)71U, (uint8_t)80U, (uint8_t)23U, (uint8_t)85U, (uint8_t)118U, (uint8_t)22U,
    (uint8_t)23U, (uint8_t)14U
  };

static uint8_t
sigver_vectors256_low6[32U] =
  {
    (uint8_t)92U, (uint8_t)240U, (uint8_t)42U, (uint8_t)0U, (uint8_t)210U, (uint8_t)5U,
    (uint8_t)189U, (uint8_t)254U, (uint8_t)226U, (uint8_t)1U, (uint8_t)111U, (uint8_t)116U,
    (uint8_t)33U, (uint8_t)128U, (uint8_t)127U, (uint8_t)195U, (uint8_t)138U, (uint8_t)230U,
    (uint8_t)158U, (uint8_t)107U, (uint8_t)124U, (uint8_t)205U, (uint8_t)6U, (uint8_t)78U,
    (uint8_t)230U, (uint8_t)137U, (uint8_t)252U, (uint8_t)26U, (uint8_t)148U, (uint8_t)169U,
    (uint8_t)247U, (uint8_t)210U
  };

static uint8_t
sigver_vectors256_low7[32U] =
  {
    (uint8_t)236U, (uint8_t)83U, (uint8_t)12U, (uint8_t)227U, (uint8_t)204U, (uint8_t)92U,
    (uint8_t)157U, (uint8_t)26U, (uint8_t)244U, (uint8_t)99U, (uint8_t)242U, (uint8_t)100U,
    (uint8_t)214U, (uint8_t)133U, (uint8_t)175U, (uint8_t)226U, (uint8_t)180U, (uint8_t)219U,
    (uint8_t)75U, (uint8_t)88U, (uint8_t)40U, (uint8_t)215U, (uint8_t)230U, (uint8_t)27U,
    (uint8_t)116U, (uint8_t)137U, (uint8_t)48U, (uint8_t)243U, (uint8_t)206U, (uint8_t)98U,
    (uint8_t)42U, (uint8_t)133U
  };

static uint8_t
sigver_vectors256_low8[32U] =
  {
    (uint8_t)220U, (uint8_t)35U, (uint8_t)209U, (uint8_t)48U, (uint8_t)198U, (uint8_t)17U,
    (uint8_t)127U, (uint8_t)181U, (uint8_t)117U, (uint8_t)18U, (uint8_t)1U, (uint8_t)69U,
    (uint8_t)94U, (uint8_t)153U, (uint8_t)243U, (uint8_t)111U, (uint8_t)89U, (uint8_t)171U,
    (uint8_t)161U, (uint8_t)166U, (uint8_t)162U, (uint8_t)28U, (uint8_t)242U, (uint8_t)208U,
    (uint8_t)231U, (uint8_t)72U, (uint8_t)26U, (uint8_t)151U, (uint8_t)69U, (uint8_t)29U,
    (uint8_t)102U, (uint8_t)147U
  };

static uint8_t
sigver_vectors256_low9[32U] =
  {
    (uint8_t)214U, (uint8_t)206U, (uint8_t)119U, (uint8_t)8U, (uint8_t)193U, (uint8_t)141U,
    (uint8_t)191U, (uint8_t)53U, (uint8_t)212U, (uint8_t)248U, (uint8_t)170U, (uint8_t)114U,
    (uint8_t)64U, (uint8_t)146U, (uint8_t)45U, (uint8_t)198U, (uint8_t)130U, (uint8_t)63U,
    (uint8_t)46U, (uint8_t)112U, (uint8_t)88U, (uint8_t)203U, (uint8_t)193U, (uint8_t)72U,
    (uint8_t)79U, (uint8_t)202U, (uint8_t)209U, (uint8_t)89U, (uint8_t)157U, (uint8_t)181U,
    (uint8_t)1U, (uint8_t)140U
  };

static uint8_t
sigver_vectors256_low10[128U] =
  {
    (uint8_t)223U, (uint8_t)4U, (uint8_t)163U, (uint8_t)70U, (uint8_t)207U, (uint8_t)77U,
    (uint8_t)14U, (uint8_t)51U, (uint8_t)26U, (uint8_t)109U, (uint8_t)183U, (uint8_t)140U,
    (uint8_t)202U, (uint8_t)45U, (uint8_t)69U, (uint8_t)109U, (uint8_t)49U, (uint8_t)176U,
    (uint8_t)160U, (uint8_t)0U, (uint8_t)170U, (uint8_t)81U, (uint8_t)68U, (uint8_t)29U,
    (uint8_t)239U, (uint8_t)219U, (uint8_t)151U, (uint8_t)187U, (uint8_t)235U, (uint8_t)32U,
    (uint8_t)185U, (uint8_t)77U, (uint8_t)141U, (uint8_t)116U, (uint8_t)100U, (uint8_t)41U,
    (uint8_t)163U, (uint8_t)147U, (uint8_t)186U, (uint8_t)136U, (uint8_t)132U, (uint8_t)13U,
    (uint8_t)102U, (uint8_t)22U, (uint8_t)21U, (uint8_t)224U, (uint8_t)125U, (uint8_t)239U,
    (uint8_t)97U, (uint8_t)90U, (uint8_t)52U, (uint8_t)42U, (uint8_t)190U, (uint8_t)223U,
    (uint8_t)164U, (uint8_t)206U, (uint8_t)145U, (uint8_t)46U, (uint8_t)86U, (uint8_t)42U,
    (uint8_t)247U, (uint8_t)20U, (uint8_t)149U, (uint8_t)152U, (uint8_t)150U, (uint8_t)133U,
    (uint8_t)138U, (uint8_t)248U, (uint8_t)23U, (uint8_t)49U, (uint8_t)122U, (uint8_t)132U,
    (uint8_t)13U, (uint8_t)207U, (uint8_t)248U, (uint8_t)90U, (uint8_t)5U, (uint8_t)123U,
    (uint8_t)185U, (uint8_t)26U, (uint8_t)60U, (uint8_t)43U, (uint8_t)249U, (uint8_t)1U,
    (uint8_t)5U, (uint8_t)80U, (uint8_t)3U, (uint8_t)98U, (uint8_t)117U, (uint8_t)74U,
    (uint8_t)109U, (uint8_t)211U, (uint8_t)33U, (uint8_t)205U, (uint8_t)216U, (uint8_t)97U,
    (uint8_t)40U, (uint8_t)207U, (uint8_t)197U, (uint8_t)240U, (uint8_t)70U, (uint8_t)103U,
    (uint8_t)181U, (uint8_t)122U, (uint8_t)167U, (uint8_t)140U, (uint8_t)17U, (uint8_t)36U,
    (uint8_t)17U, (uint8_t)228U, (uint8_t)45U, (uint8_t)163U, (uint8_t)4U, (uint8_t)241U,
    (uint8_t)1U, (uint8_t)45U, (uint8_t)72U, (uint8_t)205U, (uint8_t)106U, (uint8_t)112U,
    (uint8_t)82U, (uint8_t)215U, (uint8_t)222U, (uint8_t)68U, (uint8_t)235U, (uint8_t)204U,
    (uint8_t)1U, (uint8_t)222U
  };

static uint8_t
sigver_vectors256_low11[32U] =
  {
    (uint8_t)45U, (uint8_t)223U, (uint8_t)209U, (uint8_t)69U, (uint8_t)118U, (uint8_t)120U,
    (uint8_t)131U, (uint8_t)255U, (uint8_t)187U, (uint8_t)10U, (uint8_t)192U, (uint8_t)3U,
    (uint8_t)171U, (uint8_t)74U, (uint8_t)68U, (uint8_t)52U, (uint8_t)109U, (uint8_t)8U,
    (uint8_t)250U, (uint8_t)37U, (uint8_t)112U, (uint8_t)179U, (uint8_t)18U, (uint8_t)13U,
    (uint8_t)204U, (uint8_t)233U, (uint8_t)69U, (uint8_t)98U, (uint8_t)66U, (uint8_t)34U,
    (uint8_t)68U, (uint8_t)203U
  };

static uint8_t
sigver_vectors256_low12[32U] =
  {
    (uint8_t)95U, (uint8_t)112U, (uint8_t)199U, (uint8_t)209U, (uint8_t)26U, (uint8_t)194U,
    (uint8_t)183U, (uint8_t)164U, (uint8_t)53U, (uint8_t)204U, (uint8_t)251U, (uint8_t)186U,
    (uint8_t)224U, (uint8_t)44U, (uint8_t)61U, (uint8_t)241U, (uint8_t)234U, (uint8_t)107U,
    (uint8_t)83U, (uint8_t)44U, (uint8_t)192U, (uint8_t)233U, (uint8_t)219U, (uint8_t)116U,
    (uint8_t)249U, (uint8_t)63U, (uint8_t)255U, (uint8_t)202U, (uint8_t)124U, (uint8_t)111U,
    (uint8_t)154U, (uint8_t)100U
  };

static uint8_t
sigver_vectors256_low13[32U] =
  {
    (uint8_t)153U, (uint8_t)19U, (uint8_t)17U, (uint8_t)28U, (uint8_t)255U, (uint8_t)111U,
    (uint8_t)32U, (uint8_t)197U, (uint8_t)191U, (uint8_t)69U, (uint8_t)58U, (uint8_t)153U,
    (uint8_t)205U, (uint8_t)44U, (uint8_t)32U, (uint8_t)25U, (uint8_t)164U, (uint8_t)231U,
    (uint8_t)73U, (uint8_t)164U, (uint8_t)151U, (uint8_t)36U, (uint8_t)160U, (uint8_t)135U,
    (uint8_t)116U, (uint8_t)209U, (uint8_t)78U, (uint8_t)76U, (uint8_t)17U, (uint8_t)62U,
    (uint8_t)221U, (uint8_t)168U
  };

static uint8_t
sigver_vectors256_low14[32U] =
  {
    (uint8_t)148U, (uint8_t)103U, (uint8_t)205U, (uint8_t)76U, (uint8_t)210U, (uint8_t)30U,
    (uint8_t)203U, (uint8_t)86U, (uint8_t)176U, (uint8_t)202U, (uint8_t)176U, (uint8_t)169U,
    (uint8_t)164U, (uint8_t)83U, (uint8_t)180U, (uint8_t)51U, (uint8_t)134U, (uint8_t)132U,
    (uint8_t)84U, (uint8_t)89U, (uint8_t)18U, (uint8_t)122U, (uint8_t)149U, (uint8_t)36U,
    (uint8_t)33U, (uint8_t)245U, (uint8_t)198U, (uint8_t)56U, (uint8_t)40U, (uint8_t)102U,
    (uint8_t)197U, (uint8_t)204U
  };

static uint8_t
sigver_vectors256_low15[128U] =
  {
    (uint8_t)225U, (uint8_t)19U, (uint8_t)10U, (uint8_t)246U, (uint8_t)163U, (uint8_t)140U,
    (uint8_t)203U, (uint8_t)65U, (uint8_t)42U, (uint8_t)156U, (uint8_t)141U, (uint8_t)19U,
    (uint8_t)225U, (uint8_t)93U, (uint8_t)191U, (uint8_t)201U, (uint8_t)230U, (uint8_t)154U,
    (uint8_t)22U, (uint8_t)56U, (uint8_t)90U, (uint8_t)243U, (uint8_t)195U, (uint8_t)241U,
    (uint8_t)229U, (uint8_t)218U, (uint8_t)149U, (uint8_t)79U, (uint8_t)213U, (uint8_t)231U,
    (uint8_t)196U, (uint8_t)95U, (uint8_t)215U, (uint8_t)94U, (uint8_t)43U, (uint8_t)140U,
    (uint8_t)54U, (uint8_t)105U, (uint8_t)146U, (uint8_t)40U, (uint8_t)233U, (uint8_t)40U,
    (uint8_t)64U, (uint8_t)192U, (uint8_t)86U, (uint8_t)47U, (uint8_t)191U, (uint8_t)55U,
    (uint8_t)114U, (uint8_t)240U, (uint8_t)126U, (uint8_t)23U, (uint8_t)241U, (uint8_t)173U,
    (uint8_t)213U, (uint8_t)101U, (uint8_t)136U, (uint8_t)221U, (uint8_t)69U, (uint8_t)247U,
    (uint8_t)69U, (uint8_t)14U, (uint8_t)18U, (uint8_t)23U, (uint8_t)173U, (uint8_t)35U,
    (uint8_t)153U, (uint8_t)34U, (uint8_t)221U, (uint8_t)156U, (uint8_t)50U, (uint8_t)105U,
    (uint8_t)93U, (uint8_t)199U, (uint8_t)31U, (uint8_t)242U, (uint8_t)66U, (uint8_t)76U,
    (uint8_t)160U, (uint8_t)222U, (uint8_t)193U, (uint8_t)50U, (uint8_t)26U, (uint8_t)164U,
    (uint8_t)112U, (uint8_t)100U, (uint8_t)160U, (uint8_t)68U, (uint8_t)183U, (uint8_t)254U,
    (uint8_t)60U, (uint8_t)43U, (uint8_t)151U, (uint8_t)208U, (uint8_t)60U, (uint8_t)228U,
    (uint8_t)112U, (uint8_t)165U, (uint8_t)146U, (uint8_t)48U, (uint8_t)76U, (uint8_t)94U,
    (uint8_t)242U, (uint8_t)30U, (uint8_t)237U, (uint8_t)159U, (uint8_t)147U, (uint8_t)218U,
    (uint8_t)86U, (uint8_t)187U, (uint8_t)35U, (uint8_t)45U, (uint8_t)30U, (uint8_t)235U,
    (uint8_t)0U, (uint8_t)53U, (uint8_t)249U, (uint8_t)191U, (uint8_t)13U, (uint8_t)250U,
    (uint8_t)253U, (uint8_t)204U, (uint8_t)70U, (uint8_t)6U, (uint8_t)39U, (uint8_t)43U,
    (uint8_t)32U, (uint8_t)163U
  };

static uint8_t
sigver_vectors256_low16[32U] =
  {
    (uint8_t)228U, (uint8_t)36U, (uint8_t)220U, (uint8_t)97U, (uint8_t)212U, (uint8_t)187U,
    (uint8_t)60U, (uint8_t)183U, (uint8_t)239U, (uint8_t)67U, (uint8_t)68U, (uint8_t)167U,
    (uint8_t)248U, (uint8_t)149U, (uint8_t)122U, (uint8_t)12U, (uint8_t)81U, (uint8_t)52U,
    (uint8_t)225U, (uint8_t)111U, (uint8_t)122U, (uint8_t)103U, (uint8_t)192U, (uint8_t)116U,
    (uint8_t)248U, (uint8_t)46U, (uint8_t)110U, (uint8_t)18U, (uint8_t)244U, (uint8_t)154U,
    (uint8_t)191U, (uint8_t)60U
  };

static uint8_t
sigver_vectors256_low17[32U] =
  {
    (uint8_t)151U, (uint8_t)14U, (uint8_t)237U, (uint8_t)122U, (uint8_t)162U, (uint8_t)188U,
    (uint8_t)72U, (uint8_t)101U, (uint8_t)21U, (uint8_t)69U, (uint8_t)148U, (uint8_t)157U,
    (uint8_t)225U, (uint8_t)221U, (uint8_t)218U, (uint8_t)240U, (uint8_t)18U, (uint8_t)126U,
    (uint8_t)89U, (uint8_t)101U, (uint8_t)172U, (uint8_t)133U, (uint8_t)209U, (uint8_t)36U,
    (uint8_t)61U, (uint8_t)111U, (uint8_t)96U, (uint8_t)231U, (uint8_t)223U, (uint8_t)174U,
    (uint8_t)233U, (uint8_t)39U
  };

static uint8_t
sigver_vectors256_low18[32U] =
  {
    (uint8_t)191U, (uint8_t)150U, (uint8_t)185U, (uint8_t)154U, (uint8_t)164U, (uint8_t)156U,
    (uint8_t)112U, (uint8_t)92U, (uint8_t)145U, (uint8_t)11U, (uint8_t)227U, (uint8_t)49U,
    (uint8_t)66U, (uint8_t)1U, (uint8_t)124U, (uint8_t)100U, (uint8_t)47U, (uint8_t)245U,
    (uint8_t)64U, (uint8_t)199U, (uint8_t)99U, (uint8_t)73U, (uint8_t)185U, (uint8_t)218U,
    (uint8_t)183U, (uint8_t)47U, (uint8_t)152U, (uint8_t)31U, (uint8_t)217U, (uint8_t)52U,
    (uint8_t)127U, (uint8_t)79U
  };

static uint8_t
sigver_vectors256_low19[32U] =
  {
    (uint8_t)23U, (uint8_t)197U, (uint8_t)80U, (uint8_t)149U, (uint8_t)129U, (uint8_t)144U,
    (uint8_t)137U, (uint8_t)194U, (uint8_t)224U, (uint8_t)59U, (uint8_t)156U, (uint8_t)212U,
    (uint8_t)21U, (uint8_t)171U, (uint8_t)223U, (uint8_t)18U, (uint8_t)68U, (uint8_t)78U,
    (uint8_t)50U, (uint8_t)48U, (uint8_t)117U, (uint8_t)217U, (uint8_t)143U, (uint8_t)49U,
    (uint8_t)146U, (uint8_t)11U, (uint8_t)158U, (uint8_t)15U, (uint8_t)87U, (uint8_t)236U,
    (uint8_t)135U, (uint8_t)28U
  };

static uint8_t
sigver_vectors256_low20[128U] =
  {
    (uint8_t)115U, (uint8_t)197U, (uint8_t)246U, (uint8_t)166U, (uint8_t)116U, (uint8_t)86U,
    (uint8_t)174U, (uint8_t)72U, (uint8_t)32U, (uint8_t)155U, (uint8_t)95U, (uint8_t)133U,
    (uint8_t)209U, (uint8_t)231U, (uint8_t)222U, (uint8_t)119U, (uint8_t)88U, (uint8_t)191U,
    (uint8_t)35U, (uint8_t)83U, (uint8_t)0U, (uint8_t)198U, (uint8_t)174U, (uint8_t)43U,
    (uint8_t)220U, (uint8_t)235U, (uint8_t)29U, (uint8_t)203U, (uint8_t)39U, (uint8_t)167U,
    (uint8_t)115U, (uint8_t)15U, (uint8_t)182U, (uint8_t)140U, (uint8_t)149U, (uint8_t)11U,
    (uint8_t)127U, (uint8_t)202U, (uint8_t)218U, (uint8_t)14U, (uint8_t)204U, (uint8_t)70U,
    (uint8_t)97U, (uint8_t)211U, (uint8_t)87U, (uint8_t)130U, (uint8_t)48U, (uint8_t)242U,
    (uint8_t)37U, (uint8_t)168U, (uint8_t)117U, (uint8_t)230U, (uint8_t)154U, (uint8_t)170U,
    (uint8_t)23U, (uint8_t)241U, (uint8_t)231U, (uint8_t)28U, (uint8_t)107U, (uint8_t)229U,
    (uint8_t)200U, (uint8_t)49U, (uint8_t)242U, (uint8_t)38U, (uint8_t)99U, (uint8_t)186U,
    (uint8_t)198U, (uint8_t)61U, (uint8_t)12U, (uint8_t)122U, (uint8_t)150U, (uint8_t)53U,
    (uint8_t)237U, (uint8_t)176U, (uint8_t)4U, (uint8_t)63U, (uint8_t)248U, (uint8_t)198U,
    (uint8_t)242U, (uint8_t)100U, (uint8_t)112U, (uint8_t)240U, (uint8_t)42U, (uint8_t)123U,
    (uint8_t)197U, (uint8_t)101U, (uint8_t)86U, (uint8_t)241U, (uint8_t)67U, (uint8_t)127U,
    (uint8_t)6U, (uint8_t)223U, (uint8_t)162U, (uint8_t)123U, (uint8_t)72U, (uint8_t)122U,
    (uint8_t)108U, (uint8_t)66U, (uint8_t)144U, (uint8_t)216U, (uint8_t)186U, (uint8_t)211U,
    (uint8_t)141U, (uint8_t)72U, (uint8_t)121U, (uint8_t)179U, (uint8_t)52U, (uint8_t)227U,
    (uint8_t)65U, (uint8_t)186U, (uint8_t)9U, (uint8_t)45U, (uint8_t)222U, (uint8_t)78U,
    (uint8_t)74U, (uint8_t)230U, (uint8_t)148U, (uint8_t)169U, (uint8_t)192U, (uint8_t)147U,
    (uint8_t)2U, (uint8_t)226U, (uint8_t)219U, (uint8_t)244U, (uint8_t)67U, (uint8_t)88U,
    (uint8_t)28U, (uint8_t)8U
  };

static uint8_t
sigver_vectors256_low21[32U] =
  {
    (uint8_t)224U, (uint8_t)252U, (uint8_t)106U, (uint8_t)111U, (uint8_t)80U, (uint8_t)225U,
    (uint8_t)197U, (uint8_t)116U, (uint8_t)117U, (uint8_t)103U, (uint8_t)62U, (uint8_t)229U,
    (uint8_t)78U, (uint8_t)58U, (uint8_t)87U, (uint8_t)249U, (uint8_t)164U, (uint8_t)159U,
    (uint8_t)51U, (uint8_t)40U, (uint8_t)231U, (uint8_t)67U, (uint8_t)191U, (uint8_t)82U,
    (uint8_t)243U, (uint8_t)53U, (uint8_t)227U, (uint8_t)238U, (uint8_t)170U, (uint8_t)61U,
    (uint8_t)40U, (uint8_t)100U
  };

static uint8_t
sigver_vectors256_low22[32U] =
  {
    (uint8_t)127U, (uint8_t)89U, (uint8_t)214U, (uint8_t)137U, (uint8_t)201U, (uint8_t)30U,
    (uint8_t)70U, (uint8_t)54U, (uint8_t)7U, (uint8_t)217U, (uint8_t)25U, (uint8_t)77U,
    (uint8_t)153U, (uint8_t)250U, (uint8_t)243U, (uint8_t)22U, (uint8_t)226U, (uint8_t)84U,
    (uint8_t)50U, (uint8_t)135U, (uint8_t)8U, (uint8_t)22U, (uint8_t)221U, (uint8_t)230U,
    (uint8_t)63U, (uint8_t)93U, (uint8_t)75U, (uint8_t)55U, (uint8_t)63U, (uint8_t)18U,
    (uint8_t)242U, (uint8_t)42U
  };

static uint8_t
sigver_vectors256_low23[32U] =
  {
    (uint8_t)29U, (uint8_t)117U, (uint8_t)131U, (uint8_t)12U, (uint8_t)211U, (uint8_t)111U,
    (uint8_t)76U, (uint8_t)154U, (uint8_t)161U, (uint8_t)129U, (uint8_t)178U, (uint8_t)196U,
    (uint8_t)34U, (uint8_t)30U, (uint8_t)135U, (uint8_t)241U, (uint8_t)118U, (uint8_t)183U,
    (uint8_t)240U, (uint8_t)91U, (uint8_t)124U, (uint8_t)135U, (uint8_t)130U, (uint8_t)78U,
    (uint8_t)130U, (uint8_t)227U, (uint8_t)150U, (uint8_t)200U, (uint8_t)131U, (uint8_t)21U,
    (uint8_t)196U, (uint8_t)7U
  };

static uint8_t
sigver_vectors256_low24[32U] =
  {
    (uint8_t)203U, (uint8_t)42U, (uint8_t)203U, (uint8_t)1U, (uint8_t)218U, (uint8_t)201U,
    (uint8_t)110U, (uint8_t)252U, (uint8_t)83U, (uint8_t)163U, (uint8_t)45U, (uint8_t)74U,
    (uint8_t)13U, (uint8_t)133U, (uint8_t)208U, (uint8_t)194U, (uint8_t)228U, (uint8_t)137U,
    (uint8_t)85U, (uint8_t)33U, (uint8_t)71U, (uint8_t)131U, (uint8_t)236U, (uint8_t)245U,
    (uint8_t)10U, (uint8_t)79U, (uint8_t)4U, (uint8_t)20U, (uint8_t)163U, (uint8_t)25U,
    (uint8_t)192U, (uint8_t)90U
  };

static uint8_t
sigver_vectors256_low25[128U] =
  {
    (uint8_t)102U, (uint8_t)96U, (uint8_t)54U, (uint8_t)217U, (uint8_t)180U, (uint8_t)162U,
    (uint8_t)66U, (uint8_t)110U, (uint8_t)214U, (uint8_t)88U, (uint8_t)90U, (uint8_t)78U,
    (uint8_t)15U, (uint8_t)217U, (uint8_t)49U, (uint8_t)168U, (uint8_t)118U, (uint8_t)20U,
    (uint8_t)81U, (uint8_t)210U, (uint8_t)154U, (uint8_t)176U, (uint8_t)75U, (uint8_t)215U,
    (uint8_t)220U, (uint8_t)109U, (uint8_t)12U, (uint8_t)91U, (uint8_t)158U, (uint8_t)56U,
    (uint8_t)230U, (uint8_t)194U, (uint8_t)178U, (uint8_t)99U, (uint8_t)255U, (uint8_t)108U,
    (uint8_t)184U, (uint8_t)55U, (uint8_t)189U, (uint8_t)4U, (uint8_t)57U, (uint8_t)157U,
    (uint8_t)227U, (uint8_t)215U, (uint8_t)87U, (uint8_t)198U, (uint8_t)199U, (uint8_t)0U,
    (uint8_t)95U, (uint8_t)109U, (uint8_t)122U, (uint8_t)152U, (uint8_t)112U, (uint8_t)99U,
    (uint8_t)207U, (uint8_t)109U, (uint8_t)126U, (uint8_t)140U, (uint8_t)179U, (uint8_t)138U,
    (uint8_t)75U, (uint8_t)240U, (uint8_t)215U, (uint8_t)74U, (uint8_t)40U, (uint8_t)37U,
    (uint8_t)114U, (uint8_t)189U, (uint8_t)1U, (uint8_t)208U, (uint8_t)244U, (uint8_t)30U,
    (uint8_t)63U, (uint8_t)208U, (uint8_t)102U, (uint8_t)227U, (uint8_t)2U, (uint8_t)21U,
    (uint8_t)117U, (uint8_t)240U, (uint8_t)250U, (uint8_t)4U, (uint8_t)242U, (uint8_t)123U,
    (uint8_t)112U, (uint8_t)13U, (uint8_t)91U, (uint8_t)125U, (uint8_t)221U, (uint8_t)223U,
    (uint8_t)80U, (uint8_t)150U, (uint8_t)89U, (uint8_t)147U, (uint8_t)195U, (uint8_t)249U,
    (uint8_t)199U, (uint8_t)17U, (uint8_t)142U, (uint8_t)215U, (uint8_t)136U, (uint8_t)136U,
    (uint8_t)218U, (uint8_t)124U, (uint8_t)178U, (uint8_t)33U, (uint8_t)132U, (uint8_t)155U,
    (uint8_t)50U, (uint8_t)96U, (uint8_t)89U, (uint8_t)43U, (uint8_t)142U, (uint8_t)99U,
    (uint8_t)45U, (uint8_t)124U, (uint8_t)81U, (uint8_t)233U, (uint8_t)53U, (uint8_t)160U,
    (uint8_t)206U, (uint8_t)174U, (uint8_t)21U, (uint8_t)32U, (uint8_t)123U, (uint8_t)237U,
    (uint8_t)213U, (uint8_t)72U
  };

static uint8_t
sigver_vectors256_low26[32U] =
  {
    (uint8_t)168U, (uint8_t)73U, (uint8_t)190U, (uint8_t)245U, (uint8_t)117U, (uint8_t)202U,
    (uint8_t)195U, (uint8_t)198U, (uint8_t)146U, (uint8_t)15U, (uint8_t)188U, (uint8_t)230U,
    (uint8_t)117U, (uint8_t)195U, (uint8_t)183U, (uint8_t)135U, (uint8_t)19U, (uint8_t)98U,
    (uint8_t)9U, (uint8_t)248U, (uint8_t)85U, (uint8_t)222U, (uint8_t)25U, (uint8_t)255U,
    (uint8_t)226U, (uint8_t)232U, (uint8_t)210U, (uint8_t)155U, (uint8_t)49U, (uint8_t)165U,
    (uint8_t)173U, (uint8_t)134U
  };

static uint8_t
sigver_vectors256_low27[32U] =
  {
    (uint8_t)191U, (uint8_t)95U, (uint8_t)228U, (uint8_t)247U, (uint8_t)133U, (uint8_t)143U,
    (uint8_t)155U, (uint8_t)128U, (uint8_t)91U, (uint8_t)216U, (uint8_t)220U, (uint8_t)192U,
    (uint8_t)90U, (uint8_t)213U, (uint8_t)231U, (uint8_t)251U, (uint8_t)136U, (uint8_t)157U,
    (uint8_t)226U, (uint8_t)248U, (uint8_t)34U, (uint8_t)243U, (uint8_t)216U, (uint8_t)180U,
    (uint8_t)22U, (uint8_t)148U, (uint8_t)230U, (uint8_t)197U, (uint8_t)92U, (uint8_t)22U,
    (uint8_t)180U, (uint8_t)113U
  };

static uint8_t
sigver_vectors256_low28[32U] =
  {
    (uint8_t)37U, (uint8_t)172U, (uint8_t)195U, (uint8_t)170U, (uint8_t)157U, (uint8_t)158U,
    (uint8_t)132U, (uint8_t)199U, (uint8_t)171U, (uint8_t)240U, (uint8_t)143U, (uint8_t)115U,
    (uint8_t)250U, (uint8_t)65U, (uint8_t)149U, (uint8_t)172U, (uint8_t)197U, (uint8_t)6U,
    (uint8_t)73U, (uint8_t)29U, (uint8_t)111U, (uint8_t)195U, (uint8_t)124U, (uint8_t)185U,
    (uint8_t)7U, (uint8_t)69U, (uint8_t)40U, (uint8_t)167U, (uint8_t)219U, (uint8_t)135U,
    (uint8_t)185U, (uint8_t)214U
  };

static uint8_t
sigver_vectors256_low29[32U] =
  {
    (uint8_t)155U, (uint8_t)33U, (uint8_t)213U, (uint8_t)181U, (uint8_t)37U, (uint8_t)158U,
    (uint8_t)211U, (uint8_t)242U, (uint8_t)239U, (uint8_t)7U, (uint8_t)223U, (uint8_t)236U,
    (uint8_t)108U, (uint8_t)201U, (uint8_t)13U, (uint8_t)58U, (uint8_t)55U, (uint8_t)133U,
    (uint8_t)93U, (uint8_t)28U, (uint8_t)225U, (uint8_t)34U, (uint8_t)168U, (uint8_t)91U,
    (uint8_t)166U, (uint8_t)163U, (uint8_t)51U, (uint8_t)243U, (uint8_t)7U, (uint8_t)211U,
    (uint8_t)21U, (uint8_t)55U
  };

static uint8_t
sigver_vectors256_low30[128U] =
  {
    (uint8_t)126U, (uint8_t)128U, (uint8_t)67U, (uint8_t)107U, (uint8_t)206U, (uint8_t)87U,
    (uint8_t)51U, (uint8_t)156U, (uint8_t)232U, (uint8_t)218U, (uint8_t)27U, (uint8_t)86U,
    (uint8_t)96U, (uint8_t)20U, (uint8_t)154U, (uint8_t)32U, (uint8_t)36U, (uint8_t)11U,
    (uint8_t)20U, (uint8_t)109U, (uint8_t)16U, (uint8_t)141U, (uint8_t)238U, (uint8_t)243U,
    (uint8_t)236U, (uint8_t)93U, (uint8_t)164U, (uint8_t)174U, (uint8_t)37U, (uint8_t)111U,
    (uint8_t)143U, (uint8_t)137U, (uint8_t)78U, (uint8_t)220U, (uint8_t)187U, (uint8_t)197U,
    (uint8_t)123U, (uint8_t)52U, (uint8_t)206U, (uint8_t)55U, (uint8_t)8U, (uint8_t)156U,
    (uint8_t)13U, (uint8_t)170U, (uint8_t)23U, (uint8_t)240U, (uint8_t)196U, (uint8_t)108U,
    (uint8_t)216U, (uint8_t)43U, (uint8_t)90U, (uint8_t)21U, (uint8_t)153U, (uint8_t)49U,
    (uint8_t)79U, (uint8_t)215U, (uint8_t)157U, (uint8_t)47U, (uint8_t)210U, (uint8_t)244U,
    (uint8_t)70U, (uint8_t)189U, (uint8_t)90U, (uint8_t)37U, (uint8_t)184U, (uint8_t)227U,
    (uint8_t)47U, (uint8_t)207U, (uint8_t)5U, (uint8_t)183U, (uint8_t)109U, (uint8_t)100U,
    (uint8_t)69U, (uint8_t)115U, (uint8_t)166U, (uint8_t)223U, (uint8_t)74U, (uint8_t)209U,
    (uint8_t)223U, (uint8_t)234U, (uint8_t)112U, (uint8_t)123U, (uint8_t)71U, (uint8_t)157U,
    (uint8_t)151U, (uint8_t)35U, (uint8_t)122U, (uint8_t)52U, (uint8_t)111U, (uint8_t)30U,
    (uint8_t)198U, (uint8_t)50U, (uint8_t)234U, (uint8_t)86U, (uint8_t)96U, (uint8_t)239U,
    (uint8_t)181U, (uint8_t)126U, (uint8_t)135U, (uint8_t)23U, (uint8_t)168U, (uint8_t)98U,
    (uint8_t)141U, (uint8_t)127U, (uint8_t)130U, (uint8_t)175U, (uint8_t)80U, (uint8_t)164U,
    (uint8_t)232U, (uint8_t)75U, (uint8_t)17U, (uint8_t)242U, (uint8_t)27U, (uint8_t)223U,
    (uint8_t)246U, (uint8_t)131U, (uint8_t)145U, (uint8_t)150U, (uint8_t)168U, (uint8_t)128U,
    (uint8_t)174U, (uint8_t)32U, (uint8_t)178U, (uint8_t)160U, (uint8_t)145U, (uint8_t)141U,
    (uint8_t)88U, (uint8_t)205U
  };

static uint8_t
sigver_vectors256_low31[32U] =
  {
    (uint8_t)61U, (uint8_t)251U, (uint8_t)111U, (uint8_t)64U, (uint8_t)242U, (uint8_t)71U,
    (uint8_t)27U, (uint8_t)41U, (uint8_t)183U, (uint8_t)127U, (uint8_t)220U, (uint8_t)203U,
    (uint8_t)167U, (uint8_t)45U, (uint8_t)55U, (uint8_t)194U, (uint8_t)27U, (uint8_t)186U,
    (uint8_t)1U, (uint8_t)158U, (uint8_t)250U, (uint8_t)64U, (uint8_t)193U, (uint8_t)200U,
    (uint8_t)249U, (uint8_t)30U, (uint8_t)196U, (uint8_t)5U, (uint8_t)215U, (uint8_t)220U,
    (uint8_t)197U, (uint8_t)223U
  };

static uint8_t
sigver_vectors256_low32[32U] =
  {
    (uint8_t)242U, (uint8_t)47U, (uint8_t)149U, (uint8_t)63U, (uint8_t)30U, (uint8_t)57U,
    (uint8_t)90U, (uint8_t)82U, (uint8_t)234U, (uint8_t)215U, (uint8_t)243U, (uint8_t)174U,
    (uint8_t)63U, (uint8_t)196U, (uint8_t)116U, (uint8_t)81U, (uint8_t)180U, (uint8_t)56U,
    (uint8_t)17U, (uint8_t)123U, (uint8_t)30U, (uint8_t)4U, (uint8_t)214U, (uint8_t)19U,
    (uint8_t)188U, (uint8_t)133U, (uint8_t)85U, (uint8_t)183U, (uint8_t)214U, (uint8_t)230U,
    (uint8_t)209U, (uint8_t)187U
  };

static uint8_t
sigver_vectors256_low33[32U] =
  {
    (uint8_t)84U, (uint8_t)136U, (uint8_t)134U, (uint8_t)39U, (uint8_t)142U, (uint8_t)94U,
    (uint8_t)194U, (uint8_t)107U, (uint8_t)237U, (uint8_t)129U, (uint8_t)29U, (uint8_t)187U,
    (uint8_t)114U, (uint8_t)219U, (uint8_t)30U, (uint8_t)21U, (uint8_t)75U, (uint8_t)111U,
    (uint8_t)23U, (uint8_t)190U, (uint8_t)112U, (uint8_t)222U, (uint8_t)177U, (uint8_t)178U,
    (uint8_t)16U, (uint8_t)16U, (uint8_t)125U, (uint8_t)236U, (uint8_t)177U, (uint8_t)236U,
    (uint8_t)42U, (uint8_t)90U
  };

static uint8_t
sigver_vectors256_low34[32U] =
  {
    (uint8_t)233U, (uint8_t)59U, (uint8_t)254U, (uint8_t)189U, (uint8_t)47U, (uint8_t)20U,
    (uint8_t)243U, (uint8_t)216U, (uint8_t)39U, (uint8_t)202U, (uint8_t)50U, (uint8_t)180U,
    (uint8_t)100U, (uint8_t)190U, (uint8_t)110U, (uint8_t)105U, (uint8_t)24U, (uint8_t)127U,
    (uint8_t)94U, (uint8_t)219U, (uint8_t)213U, (uint8_t)45U, (uint8_t)239U, (uint8_t)79U,
    (uint8_t)150U, (uint8_t)89U, (uint8_t)156U, (uint8_t)55U, (uint8_t)213U, (uint8_t)142U,
    (uint8_t)238U, (uint8_t)117U
  };

static uint8_t
sigver_vectors256_low35[128U] =
  {
    (uint8_t)22U, (uint8_t)105U, (uint8_t)191U, (uint8_t)182U, (uint8_t)87U, (uint8_t)253U,
    (uint8_t)198U, (uint8_t)44U, (uint8_t)61U, (uint8_t)221U, (uint8_t)99U, (uint8_t)38U,
    (uint8_t)151U, (uint8_t)135U, (uint8_t)252U, (uint8_t)28U, (uint8_t)150U, (uint8_t)159U,
    (uint8_t)24U, (uint8_t)80U, (uint8_t)251U, (uint8_t)4U, (uint8_t)201U, (uint8_t)51U,
    (uint8_t)221U, (uint8_t)160U, (uint8_t)99U, (uint8_t)239U, (uint8_t)116U, (uint8_t)165U,
    (uint8_t)108U, (uint8_t)225U, (uint8_t)62U, (uint8_t)58U, (uint8_t)100U, (uint8_t)151U,
    (uint8_t)0U, (uint8_t)130U, (uint8_t)15U, (uint8_t)0U, (uint8_t)97U, (uint8_t)239U,
    (uint8_t)171U, (uint8_t)248U, (uint8_t)73U, (uint8_t)168U, (uint8_t)93U, (uint8_t)71U,
    (uint8_t)67U, (uint8_t)38U, (uint8_t)200U, (uint8_t)165U, (uint8_t)65U, (uint8_t)217U,
    (uint8_t)152U, (uint8_t)48U, (uint8_t)238U, (uint8_t)168U, (uint8_t)19U, (uint8_t)30U,
    (uint8_t)174U, (uint8_t)165U, (uint8_t)132U, (uint8_t)242U, (uint8_t)45U, (uint8_t)136U,
    (uint8_t)195U, (uint8_t)83U, (uint8_t)150U, (uint8_t)93U, (uint8_t)171U, (uint8_t)205U,
    (uint8_t)196U, (uint8_t)191U, (uint8_t)107U, (uint8_t)85U, (uint8_t)148U, (uint8_t)159U,
    (uint8_t)213U, (uint8_t)41U, (uint8_t)80U, (uint8_t)125U, (uint8_t)251U, (uint8_t)128U,
    (uint8_t)58U, (uint8_t)182U, (uint8_t)180U, (uint8_t)128U, (uint8_t)205U, (uint8_t)115U,
    (uint8_t)202U, (uint8_t)11U, (uint8_t)160U, (uint8_t)12U, (uint8_t)161U, (uint8_t)156U,
    (uint8_t)67U, (uint8_t)136U, (uint8_t)73U, (uint8_t)226U, (uint8_t)206U, (uint8_t)162U,
    (uint8_t)98U, (uint8_t)161U, (uint8_t)197U, (uint8_t)125U, (uint8_t)143U, (uint8_t)129U,
    (uint8_t)205U, (uint8_t)37U, (uint8_t)127U, (uint8_t)181U, (uint8_t)142U, (uint8_t)25U,
    (uint8_t)222U, (uint8_t)199U, (uint8_t)144U, (uint8_t)77U, (uint8_t)169U, (uint8_t)125U,
    (uint8_t)131U, (uint8_t)134U, (uint8_t)232U, (uint8_t)123U, (uint8_t)132U, (uint8_t)148U,
    (uint8_t)129U, (uint8_t)105U
  };

static uint8_t
sigver_vectors256_low36[32U] =
  {
    (uint8_t)105U, (uint8_t)183U, (uint8_t)102U, (uint8_t)112U, (uint8_t)86U, (uint8_t)225U,
    (uint8_t)225U, (uint8_t)29U, (uint8_t)108U, (uint8_t)175U, (uint8_t)110U, (uint8_t)69U,
    (uint8_t)100U, (uint8_t)63U, (uint8_t)139U, (uint8_t)33U, (uint8_t)231U, (uint8_t)164U,
    (uint8_t)190U, (uint8_t)189U, (uint8_t)164U, (uint8_t)99U, (uint8_t)199U, (uint8_t)253U,
    (uint8_t)188U, (uint8_t)19U, (uint8_t)188U, (uint8_t)152U, (uint8_t)239U, (uint8_t)189U,
    (uint8_t)2U, (uint8_t)20U
  };

static uint8_t
sigver_vectors256_low37[32U] =
  {
    (uint8_t)211U, (uint8_t)249U, (uint8_t)177U, (uint8_t)46U, (uint8_t)180U, (uint8_t)108U,
    (uint8_t)124U, (uint8_t)111U, (uint8_t)218U, (uint8_t)13U, (uint8_t)163U, (uint8_t)252U,
    (uint8_t)133U, (uint8_t)188U, (uint8_t)31U, (uint8_t)216U, (uint8_t)49U, (uint8_t)85U,
    (uint8_t)127U, (uint8_t)154U, (uint8_t)188U, (uint8_t)144U, (uint8_t)42U, (uint8_t)59U,
    (uint8_t)227U, (uint8_t)203U, (uint8_t)62U, (uint8_t)139U, (uint8_t)231U, (uint8_t)209U,
    (uint8_t)170U, (uint8_t)47U
  };

static uint8_t
sigver_vectors256_low38[32U] =
  {
    (uint8_t)40U, (uint8_t)143U, (uint8_t)122U, (uint8_t)28U, (uint8_t)211U, (uint8_t)145U,
    (uint8_t)132U, (uint8_t)44U, (uint8_t)206U, (uint8_t)33U, (uint8_t)240U, (uint8_t)14U,
    (uint8_t)111U, (uint8_t)21U, (uint8_t)71U, (uint8_t)28U, (uint8_t)4U, (uint8_t)220U,
    (uint8_t)24U, (uint8_t)47U, (uint8_t)228U, (uint8_t)177U, (uint8_t)77U, (uint8_t)146U,
    (uint8_t)220U, (uint8_t)24U, (uint8_t)145U, (uint8_t)8U, (uint8_t)121U, (uint8_t)121U,
    (uint8_t)151U, (uint8_t)144U
  };

static uint8_t
sigver_vectors256_low39[32U] =
  {
    (uint8_t)36U, (uint8_t)123U, (uint8_t)60U, (uint8_t)78U, (uint8_t)137U, (uint8_t)163U,
    (uint8_t)188U, (uint8_t)173U, (uint8_t)254U, (uint8_t)167U, (uint8_t)60U, (uint8_t)123U,
    (uint8_t)253U, (uint8_t)54U, (uint8_t)29U, (uint8_t)239U, (uint8_t)67U, (uint8_t)113U,
    (uint8_t)95U, (uint8_t)163U, (uint8_t)130U, (uint8_t)184U, (uint8_t)195U, (uint8_t)237U,
    (uint8_t)244U, (uint8_t)174U, (uint8_t)21U, (uint8_t)214U, (uint8_t)229U, (uint8_t)94U,
    (uint8_t)153U, (uint8_t)121U
  };

static uint8_t
sigver_vectors256_low40[128U] =
  {
    (uint8_t)63U, (uint8_t)230U, (uint8_t)13U, (uint8_t)217U, (uint8_t)173U, (uint8_t)108U,
    (uint8_t)172U, (uint8_t)207U, (uint8_t)90U, (uint8_t)111U, (uint8_t)88U, (uint8_t)59U,
    (uint8_t)58U, (uint8_t)230U, (uint8_t)89U, (uint8_t)83U, (uint8_t)86U, (uint8_t)52U,
    (uint8_t)70U, (uint8_t)196U, (uint8_t)81U, (uint8_t)11U, (uint8_t)112U, (uint8_t)218U,
    (uint8_t)17U, (uint8_t)95U, (uint8_t)250U, (uint8_t)160U, (uint8_t)186U, (uint8_t)4U,
    (uint8_t)192U, (uint8_t)118U, (uint8_t)17U, (uint8_t)92U, (uint8_t)112U, (uint8_t)67U,
    (uint8_t)171U, (uint8_t)135U, (uint8_t)51U, (uint8_t)64U, (uint8_t)60U, (uint8_t)214U,
    (uint8_t)156U, (uint8_t)125U, (uint8_t)20U, (uint8_t)194U, (uint8_t)18U, (uint8_t)198U,
    (uint8_t)85U, (uint8_t)192U, (uint8_t)123U, (uint8_t)67U, (uint8_t)167U, (uint8_t)199U,
    (uint8_t)27U, (uint8_t)154U, (uint8_t)76U, (uint8_t)255U, (uint8_t)226U, (uint8_t)44U,
    (uint8_t)38U, (uint8_t)132U, (uint8_t)120U, (uint8_t)142U, (uint8_t)198U, (uint8_t)135U,
    (uint8_t)13U, (uint8_t)194U, (uint8_t)1U, (uint8_t)63U, (uint8_t)38U, (uint8_t)145U,
    (uint8_t)114U, (uint8_t)200U, (uint8_t)34U, (uint8_t)37U, (uint8_t)111U, (uint8_t)158U,
    (uint8_t)124U, (uint8_t)198U, (uint8_t)116U, (uint8_t)121U, (uint8_t)27U, (uint8_t)242U,
    (uint8_t)216U, (uint8_t)72U, (uint8_t)108U, (uint8_t)15U, (uint8_t)86U, (uint8_t)132U,
    (uint8_t)40U, (uint8_t)62U, (uint8_t)22U, (uint8_t)73U, (uint8_t)87U, (uint8_t)110U,
    (uint8_t)252U, (uint8_t)152U, (uint8_t)46U, (uint8_t)222U, (uint8_t)23U, (uint8_t)199U,
    (uint8_t)183U, (uint8_t)75U, (uint8_t)33U, (uint8_t)71U, (uint8_t)84U, (uint8_t)215U,
    (uint8_t)4U, (uint8_t)2U, (uint8_t)251U, (uint8_t)75U, (uint8_t)180U, (uint8_t)90U,
    (uint8_t)208U, (uint8_t)134U, (uint8_t)207U, (uint8_t)44U, (uint8_t)247U, (uint8_t)107U,
    (uint8_t)61U, (uint8_t)99U, (uint8_t)247U, (uint8_t)252U, (uint8_t)227U, (uint8_t)154U,
    (uint8_t)201U, (uint8_t)112U
  };

static uint8_t
sigver_vectors256_low41[32U] =
  {
    (uint8_t)191U, (uint8_t)2U, (uint8_t)203U, (uint8_t)207U, (uint8_t)109U, (uint8_t)140U,
    (uint8_t)194U, (uint8_t)110U, (uint8_t)145U, (uint8_t)118U, (uint8_t)109U, (uint8_t)138U,
    (uint8_t)240U, (uint8_t)177U, (uint8_t)100U, (uint8_t)252U, (uint8_t)89U, (uint8_t)104U,
    (uint8_t)83U, (uint8_t)94U, (uint8_t)132U, (uint8_t)193U, (uint8_t)88U, (uint8_t)235U,
    (uint8_t)59U, (uint8_t)196U, (uint8_t)226U, (uint8_t)215U, (uint8_t)156U, (uint8_t)60U,
    (uint8_t)198U, (uint8_t)130U
  };

static uint8_t
sigver_vectors256_low42[32U] =
  {
    (uint8_t)6U, (uint8_t)155U, (uint8_t)166U, (uint8_t)203U, (uint8_t)6U, (uint8_t)180U,
    (uint8_t)157U, (uint8_t)96U, (uint8_t)129U, (uint8_t)32U, (uint8_t)102U, (uint8_t)175U,
    (uint8_t)161U, (uint8_t)110U, (uint8_t)207U, (uint8_t)123U, (uint8_t)81U, (uint8_t)53U,
    (uint8_t)47U, (uint8_t)44U, (uint8_t)3U, (uint8_t)189U, (uint8_t)147U, (uint8_t)236U,
    (uint8_t)34U, (uint8_t)8U, (uint8_t)34U, (uint8_t)177U, (uint8_t)243U, (uint8_t)223U,
    (uint8_t)186U, (uint8_t)3U
  };

static uint8_t
sigver_vectors256_low43[32U] =
  {
    (uint8_t)245U, (uint8_t)172U, (uint8_t)176U, (uint8_t)108U, (uint8_t)89U, (uint8_t)194U,
    (uint8_t)180U, (uint8_t)146U, (uint8_t)127U, (uint8_t)184U, (uint8_t)82U, (uint8_t)250U,
    (uint8_t)160U, (uint8_t)127U, (uint8_t)175U, (uint8_t)75U, (uint8_t)24U, (uint8_t)82U,
    (uint8_t)187U, (uint8_t)181U, (uint8_t)208U, (uint8_t)104U, (uint8_t)64U, (uint8_t)147U,
    (uint8_t)94U, (uint8_t)132U, (uint8_t)156U, (uint8_t)77U, (uint8_t)41U, (uint8_t)61U,
    (uint8_t)27U, (uint8_t)173U
  };

static uint8_t
sigver_vectors256_low44[32U] =
  {
    (uint8_t)4U, (uint8_t)157U, (uint8_t)171U, (uint8_t)121U, (uint8_t)200U, (uint8_t)156U,
    (uint8_t)192U, (uint8_t)47U, (uint8_t)20U, (uint8_t)132U, (uint8_t)196U, (uint8_t)55U,
    (uint8_t)245U, (uint8_t)35U, (uint8_t)224U, (uint8_t)128U, (uint8_t)167U, (uint8_t)95U,
    (uint8_t)19U, (uint8_t)73U, (uint8_t)23U, (uint8_t)253U, (uint8_t)167U, (uint8_t)82U,
    (uint8_t)242U, (uint8_t)213U, (uint8_t)202U, (uint8_t)57U, (uint8_t)122U, (uint8_t)221U,
    (uint8_t)254U, (uint8_t)93U
  };

static uint8_t
sigver_vectors256_low45[128U] =
  {
    (uint8_t)152U, (uint8_t)58U, (uint8_t)113U, (uint8_t)185U, (uint8_t)153U, (uint8_t)77U,
    (uint8_t)149U, (uint8_t)232U, (uint8_t)118U, (uint8_t)216U, (uint8_t)77U, (uint8_t)40U,
    (uint8_t)148U, (uint8_t)106U, (uint8_t)4U, (uint8_t)31U, (uint8_t)143U, (uint8_t)10U,
    (uint8_t)63U, (uint8_t)84U, (uint8_t)76U, (uint8_t)252U, (uint8_t)192U, (uint8_t)85U,
    (uint8_t)73U, (uint8_t)101U, (uint8_t)128U, (uint8_t)241U, (uint8_t)223U, (uint8_t)212U,
    (uint8_t)227U, (uint8_t)18U, (uint8_t)162U, (uint8_t)173U, (uint8_t)65U, (uint8_t)143U,
    (uint8_t)230U, (uint8_t)157U, (uint8_t)188U, (uint8_t)97U, (uint8_t)219U, (uint8_t)35U,
    (uint8_t)12U, (uint8_t)192U, (uint8_t)192U, (uint8_t)237U, (uint8_t)151U, (uint8_t)227U,
    (uint8_t)96U, (uint8_t)171U, (uint8_t)171U, (uint8_t)125U, (uint8_t)111U, (uint8_t)244U,
    (uint8_t)184U, (uint8_t)30U, (uint8_t)233U, (uint8_t)112U, (uint8_t)167U, (uint8_t)233U,
    (uint8_t)116U, (uint8_t)102U, (uint8_t)172U, (uint8_t)253U, (uint8_t)150U, (uint8_t)68U,
    (uint8_t)248U, (uint8_t)40U, (uint8_t)255U, (uint8_t)236U, (uint8_t)83U, (uint8_t)138U,
    (uint8_t)188U, (uint8_t)56U, (uint8_t)61U, (uint8_t)14U, (uint8_t)146U, (uint8_t)50U,
    (uint8_t)109U, (uint8_t)28U, (uint8_t)136U, (uint8_t)197U, (uint8_t)94U, (uint8_t)31U,
    (uint8_t)70U, (uint8_t)166U, (uint8_t)104U, (uint8_t)160U, (uint8_t)57U, (uint8_t)190U,
    (uint8_t)170U, (uint8_t)27U, (uint8_t)230U, (uint8_t)49U, (uint8_t)168U, (uint8_t)145U,
    (uint8_t)41U, (uint8_t)147U, (uint8_t)140U, (uint8_t)0U, (uint8_t)168U, (uint8_t)26U,
    (uint8_t)58U, (uint8_t)228U, (uint8_t)109U, (uint8_t)74U, (uint8_t)236U, (uint8_t)191U,
    (uint8_t)151U, (uint8_t)7U, (uint8_t)247U, (uint8_t)100U, (uint8_t)219U, (uint8_t)172U,
    (uint8_t)206U, (uint8_t)163U, (uint8_t)239U, (uint8_t)118U, (uint8_t)101U, (uint8_t)228U,
    (uint8_t)196U, (uint8_t)48U, (uint8_t)127U, (uint8_t)160U, (uint8_t)176U, (uint8_t)163U,
    (uint8_t)7U, (uint8_t)92U
  };

static uint8_t
sigver_vectors256_low46[32U] =
  {
    (uint8_t)34U, (uint8_t)74U, (uint8_t)77U, (uint8_t)101U, (uint8_t)185U, (uint8_t)88U,
    (uint8_t)246U, (uint8_t)214U, (uint8_t)175U, (uint8_t)178U, (uint8_t)144U, (uint8_t)72U,
    (uint8_t)99U, (uint8_t)239U, (uint8_t)210U, (uint8_t)167U, (uint8_t)52U, (uint8_t)179U,
    (uint8_t)23U, (uint8_t)152U, (uint8_t)136U, (uint8_t)72U, (uint8_t)1U, (uint8_t)252U,
    (uint8_t)171U, (uint8_t)90U, (uint8_t)89U, (uint8_t)15U, (uint8_t)77U, (uint8_t)109U,
    (uint8_t)169U, (uint8_t)222U
  };

static uint8_t
sigver_vectors256_low47[32U] =
  {
    (uint8_t)23U, (uint8_t)141U, (uint8_t)81U, (uint8_t)253U, (uint8_t)218U, (uint8_t)218U,
    (uint8_t)98U, (uint8_t)128U, (uint8_t)111U, (uint8_t)9U, (uint8_t)122U, (uint8_t)166U,
    (uint8_t)21U, (uint8_t)211U, (uint8_t)59U, (uint8_t)143U, (uint8_t)36U, (uint8_t)4U,
    (uint8_t)230U, (uint8_t)177U, (uint8_t)71U, (uint8_t)159U, (uint8_t)95U, (uint8_t)212U,
    (uint8_t)133U, (uint8_t)157U, (uint8_t)89U, (uint8_t)87U, (uint8_t)52U, (uint8_t)214U,
    (uint8_t)210U, (uint8_t)185U
  };

static uint8_t
sigver_vectors256_low48[32U] =
  {
    (uint8_t)135U, (uint8_t)185U, (uint8_t)62U, (uint8_t)226U, (uint8_t)254U, (uint8_t)207U,
    (uint8_t)218U, (uint8_t)84U, (uint8_t)222U, (uint8_t)184U, (uint8_t)223U, (uint8_t)248U,
    (uint8_t)228U, (uint8_t)38U, (uint8_t)243U, (uint8_t)199U, (uint8_t)44U, (uint8_t)136U,
    (uint8_t)100U, (uint8_t)153U, (uint8_t)31U, (uint8_t)142U, (uint8_t)194U, (uint8_t)179U,
    (uint8_t)32U, (uint8_t)91U, (uint8_t)179U, (uint8_t)180U, (uint8_t)22U, (uint8_t)222U,
    (uint8_t)147U, (uint8_t)210U
  };

static uint8_t
sigver_vectors256_low49[32U] =
  {
    (uint8_t)64U, (uint8_t)68U, (uint8_t)162U, (uint8_t)77U, (uint8_t)248U, (uint8_t)91U,
    (uint8_t)224U, (uint8_t)204U, (uint8_t)118U, (uint8_t)242U, (uint8_t)26U, (uint8_t)68U,
    (uint8_t)48U, (uint8_t)183U, (uint8_t)91U, (uint8_t)142U, (uint8_t)119U, (uint8_t)185U,
    (uint8_t)50U, (uint8_t)168U, (uint8_t)127U, (uint8_t)81U, (uint8_t)228U, (uint8_t)236U,
    (uint8_t)203U, (uint8_t)196U, (uint8_t)92U, (uint8_t)38U, (uint8_t)62U, (uint8_t)191U,
    (uint8_t)143U, (uint8_t)102U
  };

static uint8_t
sigver_vectors256_low50[128U] =
  {
    (uint8_t)74U, (uint8_t)140U, (uint8_t)7U, (uint8_t)26U, (uint8_t)196U, (uint8_t)253U,
    (uint8_t)13U, (uint8_t)82U, (uint8_t)250U, (uint8_t)164U, (uint8_t)7U, (uint8_t)176U,
    (uint8_t)254U, (uint8_t)93U, (uint8_t)171U, (uint8_t)117U, (uint8_t)159U, (uint8_t)115U,
    (uint8_t)148U, (uint8_t)165U, (uint8_t)131U, (uint8_t)33U, (uint8_t)39U, (uint8_t)242U,
    (uint8_t)163U, (uint8_t)73U, (uint8_t)143U, (uint8_t)52U, (uint8_t)170U, (uint8_t)194U,
    (uint8_t)135U, (uint8_t)51U, (uint8_t)158U, (uint8_t)4U, (uint8_t)59U, (uint8_t)79U,
    (uint8_t)250U, (uint8_t)121U, (uint8_t)82U, (uint8_t)143U, (uint8_t)175U, (uint8_t)25U,
    (uint8_t)157U, (uint8_t)201U, (uint8_t)23U, (uint8_t)247U, (uint8_t)176U, (uint8_t)102U,
    (uint8_t)173U, (uint8_t)101U, (uint8_t)80U, (uint8_t)93U, (uint8_t)171U, (uint8_t)14U,
    (uint8_t)17U, (uint8_t)230U, (uint8_t)148U, (uint8_t)133U, (uint8_t)21U, (uint8_t)5U,
    (uint8_t)44U, (uint8_t)226U, (uint8_t)12U, (uint8_t)253U, (uint8_t)184U, (uint8_t)146U,
    (uint8_t)255U, (uint8_t)184U, (uint8_t)170U, (uint8_t)155U, (uint8_t)243U, (uint8_t)241U,
    (uint8_t)170U, (uint8_t)91U, (uint8_t)227U, (uint8_t)10U, (uint8_t)91U, (uint8_t)190U,
    (uint8_t)133U, (uint8_t)130U, (uint8_t)59U, (uint8_t)221U, (uint8_t)247U, (uint8_t)11U,
    (uint8_t)57U, (uint8_t)253U, (uint8_t)126U, (uint8_t)189U, (uint8_t)74U, (uint8_t)147U,
    (uint8_t)162U, (uint8_t)247U, (uint8_t)84U, (uint8_t)114U, (uint8_t)193U, (uint8_t)212U,
    (uint8_t)246U, (uint8_t)6U, (uint8_t)36U, (uint8_t)122U, (uint8_t)152U, (uint8_t)33U,
    (uint8_t)241U, (uint8_t)168U, (uint8_t)196U, (uint8_t)90U, (uint8_t)108U, (uint8_t)184U,
    (uint8_t)5U, (uint8_t)69U, (uint8_t)222U, (uint8_t)46U, (uint8_t)12U, (uint8_t)108U,
    (uint8_t)1U, (uint8_t)116U, (uint8_t)226U, (uint8_t)57U, (uint8_t)32U, (uint8_t)136U,
    (uint8_t)199U, (uint8_t)84U, (uint8_t)233U, (uint8_t)200U, (uint8_t)68U, (uint8_t)62U,
    (uint8_t)181U, (uint8_t)175U
  };

static uint8_t
sigver_vectors256_low51[32U] =
  {
    (uint8_t)67U, (uint8_t)105U, (uint8_t)28U, (uint8_t)119U, (uint8_t)149U, (uint8_t)165U,
    (uint8_t)126U, (uint8_t)173U, (uint8_t)140U, (uint8_t)92U, (uint8_t)104U, (uint8_t)83U,
    (uint8_t)111U, (uint8_t)233U, (uint8_t)52U, (uint8_t)83U, (uint8_t)141U, (uint8_t)70U,
    (uint8_t)241U, (uint8_t)40U, (uint8_t)137U, (uint8_t)104U, (uint8_t)10U, (uint8_t)156U,
    (uint8_t)182U, (uint8_t)208U, (uint8_t)85U, (uint8_t)160U, (uint8_t)102U, (uint8_t)34U,
    (uint8_t)131U, (uint8_t)105U
  };

static uint8_t
sigver_vectors256_low52[32U] =
  {
    (uint8_t)248U, (uint8_t)121U, (uint8_t)1U, (uint8_t)16U, (uint8_t)179U, (uint8_t)195U,
    (uint8_t)178U, (uint8_t)129U, (uint8_t)170U, (uint8_t)30U, (uint8_t)174U, (uint8_t)3U,
    (uint8_t)125U, (uint8_t)79U, (uint8_t)18U, (uint8_t)52U, (uint8_t)175U, (uint8_t)245U,
    (uint8_t)135U, (uint8_t)217U, (uint8_t)3U, (uint8_t)217U, (uint8_t)59U, (uint8_t)163U,
    (uint8_t)175U, (uint8_t)34U, (uint8_t)92U, (uint8_t)39U, (uint8_t)221U, (uint8_t)201U,
    (uint8_t)204U, (uint8_t)172U
  };

static uint8_t
sigver_vectors256_low53[32U] =
  {
    (uint8_t)138U, (uint8_t)205U, (uint8_t)98U, (uint8_t)232U, (uint8_t)194U, (uint8_t)98U,
    (uint8_t)250U, (uint8_t)80U, (uint8_t)221U, (uint8_t)152U, (uint8_t)64U, (uint8_t)72U,
    (uint8_t)9U, (uint8_t)105U, (uint8_t)244U, (uint8_t)239U, (uint8_t)112U, (uint8_t)242U,
    (uint8_t)24U, (uint8_t)235U, (uint8_t)248U, (uint8_t)239U, (uint8_t)149U, (uint8_t)132U,
    (uint8_t)241U, (uint8_t)153U, (uint8_t)3U, (uint8_t)17U, (uint8_t)50U, (uint8_t)198U,
    (uint8_t)177U, (uint8_t)206U
  };

static uint8_t
sigver_vectors256_low54[32U] =
  {
    (uint8_t)207U, (uint8_t)202U, (uint8_t)126U, (uint8_t)211U, (uint8_t)212U, (uint8_t)52U,
    (uint8_t)127U, (uint8_t)178U, (uint8_t)162U, (uint8_t)158U, (uint8_t)82U, (uint8_t)107U,
    (uint8_t)67U, (uint8_t)195U, (uint8_t)72U, (uint8_t)174U, (uint8_t)28U, (uint8_t)230U,
    (uint8_t)198U, (uint8_t)13U, (uint8_t)68U, (uint8_t)243U, (uint8_t)25U, (uint8_t)27U,
    (uint8_t)109U, (uint8_t)142U, (uint8_t)163U, (uint8_t)162U, (uint8_t)217U, (uint8_t)201U,
    (uint8_t)33U, (uint8_t)84U
  };

static uint8_t
sigver_vectors256_low55[128U] =
  {
    (uint8_t)10U, (uint8_t)58U, (uint8_t)18U, (uint8_t)195U, (uint8_t)8U, (uint8_t)76U,
    (uint8_t)134U, (uint8_t)93U, (uint8_t)175U, (uint8_t)29U, (uint8_t)48U, (uint8_t)44U,
    (uint8_t)120U, (uint8_t)33U, (uint8_t)93U, (uint8_t)57U, (uint8_t)191U, (uint8_t)224U,
    (uint8_t)184U, (uint8_t)191U, (uint8_t)40U, (uint8_t)39U, (uint8_t)43U, (uint8_t)60U,
    (uint8_t)11U, (uint8_t)116U, (uint8_t)190U, (uint8_t)180U, (uint8_t)183U, (uint8_t)64U,
    (uint8_t)157U, (uint8_t)176U, (uint8_t)113U, (uint8_t)130U, (uint8_t)57U, (uint8_t)222U,
    (uint8_t)112U, (uint8_t)7U, (uint8_t)133U, (uint8_t)88U, (uint8_t)21U, (uint8_t)20U,
    (uint8_t)50U, (uint8_t)28U, (uint8_t)100U, (uint8_t)64U, (uint8_t)164U, (uint8_t)187U,
    (uint8_t)174U, (uint8_t)164U, (uint8_t)199U, (uint8_t)111U, (uint8_t)164U, (uint8_t)116U,
    (uint8_t)1U, (uint8_t)225U, (uint8_t)81U, (uint8_t)230U, (uint8_t)140U, (uint8_t)182U,
    (uint8_t)194U, (uint8_t)144U, (uint8_t)23U, (uint8_t)240U, (uint8_t)188U, (uint8_t)228U,
    (uint8_t)99U, (uint8_t)18U, (uint8_t)144U, (uint8_t)175U, (uint8_t)94U, (uint8_t)165U,
    (uint8_t)226U, (uint8_t)191U, (uint8_t)62U, (uint8_t)215U, (uint8_t)66U, (uint8_t)174U,
    (uint8_t)17U, (uint8_t)11U, (uint8_t)4U, (uint8_t)173U, (uint8_t)232U, (uint8_t)58U,
    (uint8_t)93U, (uint8_t)189U, (uint8_t)115U, (uint8_t)88U, (uint8_t)242U, (uint8_t)154U,
    (uint8_t)133U, (uint8_t)147U, (uint8_t)142U, (uint8_t)35U, (uint8_t)216U, (uint8_t)122U,
    (uint8_t)200U, (uint8_t)35U, (uint8_t)48U, (uint8_t)114U, (uint8_t)183U, (uint8_t)156U,
    (uint8_t)148U, (uint8_t)103U, (uint8_t)15U, (uint8_t)240U, (uint8_t)149U, (uint8_t)159U,
    (uint8_t)156U, (uint8_t)127U, (uint8_t)69U, (uint8_t)23U, (uint8_t)134U, (uint8_t)47U,
    (uint8_t)248U, (uint8_t)41U, (uint8_t)69U, (uint8_t)32U, (uint8_t)150U, (uint8_t)199U,
    (uint8_t)143U, (uint8_t)95U, (uint8_t)46U, (uint8_t)154U, (uint8_t)126U, (uint8_t)78U,
    (uint8_t)146U, (uint8_t)22U
  };

static uint8_t
sigver_vectors256_low56[32U] =
  {
    (uint8_t)145U, (uint8_t)87U, (uint8_t)219U, (uint8_t)252U, (uint8_t)248U, (uint8_t)207U,
    (uint8_t)56U, (uint8_t)95U, (uint8_t)91U, (uint8_t)177U, (uint8_t)86U, (uint8_t)138U,
    (uint8_t)213U, (uint8_t)198U, (uint8_t)226U, (uint8_t)168U, (uint8_t)101U, (uint8_t)43U,
    (uint8_t)166U, (uint8_t)223U, (uint8_t)198U, (uint8_t)59U, (uint8_t)193U, (uint8_t)117U,
    (uint8_t)62U, (uint8_t)223U, (uint8_t)82U, (uint8_t)104U, (uint8_t)203U, (uint8_t)126U,
    (uint8_t)181U, (uint8_t)150U
  };

static uint8_t
sigver_vectors256_low57[32U] =
  {
    (uint8_t)151U, (uint8_t)37U, (uint8_t)112U, (uint8_t)244U, (uint8_t)49U, (uint8_t)61U,
    (uint8_t)71U, (uint8_t)252U, (uint8_t)150U, (uint8_t)247U, (uint8_t)192U, (uint8_t)45U,
    (uint8_t)85U, (uint8_t)148U, (uint8_t)215U, (uint8_t)125U, (uint8_t)70U, (uint8_t)249U,
    (uint8_t)30U, (uint8_t)148U, (uint8_t)152U, (uint8_t)8U, (uint8_t)130U, (uint8_t)91U,
    (uint8_t)61U, (uint8_t)49U, (uint8_t)240U, (uint8_t)41U, (uint8_t)232U, (uint8_t)41U,
    (uint8_t)100U, (uint8_t)5U
  };

static uint8_t
sigver_vectors256_low58[32U] =
  {
    (uint8_t)223U, (uint8_t)174U, (uint8_t)166U, (uint8_t)242U, (uint8_t)151U, (uint8_t)250U,
    (uint8_t)50U, (uint8_t)11U, (uint8_t)112U, (uint8_t)120U, (uint8_t)102U, (uint8_t)18U,
    (uint8_t)92U, (uint8_t)42U, (uint8_t)125U, (uint8_t)93U, (uint8_t)81U, (uint8_t)91U,
    (uint8_t)81U, (uint8_t)165U, (uint8_t)3U, (uint8_t)190U, (uint8_t)232U, (uint8_t)23U,
    (uint8_t)222U, (uint8_t)159U, (uint8_t)170U, (uint8_t)52U, (uint8_t)60U, (uint8_t)196U,
    (uint8_t)142U, (uint8_t)235U
  };

static uint8_t
sigver_vectors256_low59[32U] =
  {
    (uint8_t)143U, (uint8_t)120U, (uint8_t)10U, (uint8_t)215U, (uint8_t)19U, (uint8_t)249U,
    (uint8_t)195U, (uint8_t)229U, (uint8_t)164U, (uint8_t)247U, (uint8_t)250U, (uint8_t)76U,
    (uint8_t)81U, (uint8_t)152U, (uint8_t)51U, (uint8_t)223U, (uint8_t)239U, (uint8_t)198U,
    (uint8_t)167U, (uint8_t)67U, (uint8_t)35U, (uint8_t)137U, (uint8_t)177U, (uint8_t)228U,
    (uint8_t)175U, (uint8_t)70U, (uint8_t)57U, (uint8_t)97U, (uint8_t)240U, (uint8_t)151U,
    (uint8_t)100U, (uint8_t)242U
  };

static uint8_t
sigver_vectors256_low60[128U] =
  {
    (uint8_t)120U, (uint8_t)93U, (uint8_t)7U, (uint8_t)163U, (uint8_t)197U, (uint8_t)79U,
    (uint8_t)99U, (uint8_t)220U, (uint8_t)161U, (uint8_t)31U, (uint8_t)93U, (uint8_t)26U,
    (uint8_t)95U, (uint8_t)73U, (uint8_t)110U, (uint8_t)226U, (uint8_t)194U, (uint8_t)249U,
    (uint8_t)40U, (uint8_t)142U, (uint8_t)85U, (uint8_t)0U, (uint8_t)126U, (uint8_t)102U,
    (uint8_t)108U, (uint8_t)120U, (uint8_t)176U, (uint8_t)7U, (uint8_t)217U, (uint8_t)92U,
    (uint8_t)194U, (uint8_t)133U, (uint8_t)129U, (uint8_t)220U, (uint8_t)229U, (uint8_t)31U,
    (uint8_t)73U, (uint8_t)11U, (uint8_t)48U, (uint8_t)250U, (uint8_t)115U, (uint8_t)220U,
    (uint8_t)158U, (uint8_t)45U, (uint8_t)69U, (uint8_t)208U, (uint8_t)117U, (uint8_t)215U,
    (uint8_t)227U, (uint8_t)169U, (uint8_t)95U, (uint8_t)184U, (uint8_t)169U, (uint8_t)225U,
    (uint8_t)70U, (uint8_t)90U, (uint8_t)209U, (uint8_t)145U, (uint8_t)144U, (uint8_t)65U,
    (uint8_t)36U, (uint8_t)22U, (uint8_t)11U, (uint8_t)124U, (uint8_t)96U, (uint8_t)250U,
    (uint8_t)114U, (uint8_t)14U, (uint8_t)244U, (uint8_t)239U, (uint8_t)28U, (uint8_t)93U,
    (uint8_t)41U, (uint8_t)152U, (uint8_t)244U, (uint8_t)5U, (uint8_t)112U, (uint8_t)174U,
    (uint8_t)42U, (uint8_t)135U, (uint8_t)14U, (uint8_t)243U, (uint8_t)232U, (uint8_t)148U,
    (uint8_t)194U, (uint8_t)188U, (uint8_t)97U, (uint8_t)125U, (uint8_t)138U, (uint8_t)29U,
    (uint8_t)200U, (uint8_t)92U, (uint8_t)60U, (uint8_t)85U, (uint8_t)119U, (uint8_t)73U,
    (uint8_t)40U, (uint8_t)195U, (uint8_t)135U, (uint8_t)137U, (uint8_t)180U, (uint8_t)230U,
    (uint8_t)97U, (uint8_t)52U, (uint8_t)157U, (uint8_t)63U, (uint8_t)132U, (uint8_t)210U,
    (uint8_t)68U, (uint8_t)26U, (uint8_t)59U, (uint8_t)133U, (uint8_t)106U, (uint8_t)118U,
    (uint8_t)148U, (uint8_t)155U, (uint8_t)159U, (uint8_t)31U, (uint8_t)128U, (uint8_t)188U,
    (uint8_t)22U, (uint8_t)22U, (uint8_t)72U, (uint8_t)161U, (uint8_t)202U, (uint8_t)213U,
    (uint8_t)88U, (uint8_t)142U
  };

static uint8_t
sigver_vectors256_low61[32U] =
  {
    (uint8_t)7U, (uint8_t)43U, (uint8_t)16U, (uint8_t)192U, (uint8_t)129U, (uint8_t)164U,
    (uint8_t)193U, (uint8_t)113U, (uint8_t)58U, (uint8_t)41U, (uint8_t)79U, (uint8_t)36U,
    (uint8_t)138U, (uint8_t)239U, (uint8_t)133U, (uint8_t)14U, (uint8_t)41U, (uint8_t)121U,
    (uint8_t)145U, (uint8_t)172U, (uint8_t)164U, (uint8_t)127U, (uint8_t)169U, (uint8_t)106U,
    (uint8_t)116U, (uint8_t)112U, (uint8_t)171U, (uint8_t)227U, (uint8_t)184U, (uint8_t)172U,
    (uint8_t)253U, (uint8_t)218U
  };

static uint8_t
sigver_vectors256_low62[32U] =
  {
    (uint8_t)149U, (uint8_t)129U, (uint8_t)20U, (uint8_t)92U, (uint8_t)202U, (uint8_t)4U,
    (uint8_t)160U, (uint8_t)251U, (uint8_t)148U, (uint8_t)206U, (uint8_t)220U, (uint8_t)231U,
    (uint8_t)82U, (uint8_t)200U, (uint8_t)240U, (uint8_t)55U, (uint8_t)8U, (uint8_t)97U,
    (uint8_t)145U, (uint8_t)109U, (uint8_t)42U, (uint8_t)148U, (uint8_t)231U, (uint8_t)198U,
    (uint8_t)71U, (uint8_t)197U, (uint8_t)55U, (uint8_t)60U, (uint8_t)230U, (uint8_t)164U,
    (uint8_t)200U, (uint8_t)245U
  };

static uint8_t
sigver_vectors256_low63[32U] =
  {
    (uint8_t)9U, (uint8_t)245U, (uint8_t)72U, (uint8_t)62U, (uint8_t)204U, (uint8_t)236U,
    (uint8_t)128U, (uint8_t)249U, (uint8_t)209U, (uint8_t)4U, (uint8_t)129U, (uint8_t)90U,
    (uint8_t)27U, (uint8_t)233U, (uint8_t)204U, (uint8_t)26U, (uint8_t)142U, (uint8_t)91U,
    (uint8_t)18U, (uint8_t)182U, (uint8_t)235U, (uint8_t)72U, (uint8_t)42U, (uint8_t)101U,
    (uint8_t)198U, (uint8_t)144U, (uint8_t)123U, (uint8_t)116U, (uint8_t)128U, (uint8_t)207U,
    (uint8_t)79U, (uint8_t)25U
  };

static uint8_t
sigver_vectors256_low64[32U] =
  {
    (uint8_t)164U, (uint8_t)249U, (uint8_t)14U, (uint8_t)86U, (uint8_t)12U, (uint8_t)94U,
    (uint8_t)78U, (uint8_t)184U, (uint8_t)105U, (uint8_t)108U, (uint8_t)178U, (uint8_t)118U,
    (uint8_t)229U, (uint8_t)22U, (uint8_t)91U, (uint8_t)106U, (uint8_t)157U, (uint8_t)72U,
    (uint8_t)99U, (uint8_t)69U, (uint8_t)222U, (uint8_t)223U, (uint8_t)176U, (uint8_t)148U,
    (uint8_t)167U, (uint8_t)110U, (uint8_t)132U, (uint8_t)66U, (uint8_t)208U, (uint8_t)38U,
    (uint8_t)55U, (uint8_t)141U
  };

static uint8_t
sigver_vectors256_low65[128U] =
  {
    (uint8_t)118U, (uint8_t)249U, (uint8_t)135U, (uint8_t)236U, (uint8_t)84U, (uint8_t)72U,
    (uint8_t)221U, (uint8_t)114U, (uint8_t)33U, (uint8_t)155U, (uint8_t)211U, (uint8_t)11U,
    (uint8_t)246U, (uint8_t)182U, (uint8_t)107U, (uint8_t)7U, (uint8_t)117U, (uint8_t)200U,
    (uint8_t)11U, (uint8_t)57U, (uint8_t)72U, (uint8_t)81U, (uint8_t)164U, (uint8_t)63U,
    (uint8_t)241U, (uint8_t)245U, (uint8_t)55U, (uint8_t)241U, (uint8_t)64U, (uint8_t)166U,
    (uint8_t)231U, (uint8_t)34U, (uint8_t)158U, (uint8_t)248U, (uint8_t)205U, (uint8_t)114U,
    (uint8_t)173U, (uint8_t)88U, (uint8_t)177U, (uint8_t)210U, (uint8_t)210U, (uint8_t)2U,
    (uint8_t)152U, (uint8_t)83U, (uint8_t)157U, (uint8_t)99U, (uint8_t)71U, (uint8_t)221U,
    (uint8_t)85U, (uint8_t)152U, (uint8_t)129U, (uint8_t)43U, (uint8_t)198U, (uint8_t)83U,
    (uint8_t)35U, (uint8_t)172U, (uint8_t)234U, (uint8_t)240U, (uint8_t)82U, (uint8_t)40U,
    (uint8_t)247U, (uint8_t)56U, (uint8_t)181U, (uint8_t)173U, (uint8_t)62U, (uint8_t)141U,
    (uint8_t)159U, (uint8_t)228U, (uint8_t)16U, (uint8_t)15U, (uint8_t)215U, (uint8_t)103U,
    (uint8_t)194U, (uint8_t)240U, (uint8_t)152U, (uint8_t)199U, (uint8_t)124U, (uint8_t)185U,
    (uint8_t)156U, (uint8_t)41U, (uint8_t)146U, (uint8_t)132U, (uint8_t)59U, (uint8_t)163U,
    (uint8_t)238U, (uint8_t)217U, (uint8_t)29U, (uint8_t)50U, (uint8_t)68U, (uint8_t)79U,
    (uint8_t)59U, (uint8_t)109U, (uint8_t)182U, (uint8_t)205U, (uint8_t)33U, (uint8_t)45U,
    (uint8_t)212U, (uint8_t)229U, (uint8_t)96U, (uint8_t)149U, (uint8_t)72U, (uint8_t)244U,
    (uint8_t)187U, (uint8_t)98U, (uint8_t)129U, (uint8_t)42U, (uint8_t)146U, (uint8_t)15U,
    (uint8_t)110U, (uint8_t)43U, (uint8_t)241U, (uint8_t)88U, (uint8_t)27U, (uint8_t)225U,
    (uint8_t)235U, (uint8_t)238U, (uint8_t)189U, (uint8_t)208U, (uint8_t)110U, (uint8_t)196U,
    (uint8_t)233U, (uint8_t)113U, (uint8_t)134U, (uint8_t)44U, (uint8_t)196U, (uint8_t)32U,
    (uint8_t)85U, (uint8_t)202U
  };

static uint8_t
sigver_vectors256_low66[32U] =
  {
    (uint8_t)9U, (uint8_t)48U, (uint8_t)142U, (uint8_t)165U, (uint8_t)191U, (uint8_t)173U,
    (uint8_t)110U, (uint8_t)90U, (uint8_t)223U, (uint8_t)64U, (uint8_t)134U, (uint8_t)52U,
    (uint8_t)179U, (uint8_t)213U, (uint8_t)206U, (uint8_t)146U, (uint8_t)64U, (uint8_t)211U,
    (uint8_t)84U, (uint8_t)66U, (uint8_t)247U, (uint8_t)254U, (uint8_t)17U, (uint8_t)100U,
    (uint8_t)82U, (uint8_t)170U, (uint8_t)236U, (uint8_t)13U, (uint8_t)37U, (uint8_t)190U,
    (uint8_t)140U, (uint8_t)36U
  };

static uint8_t
sigver_vectors256_low67[32U] =
  {
    (uint8_t)244U, (uint8_t)12U, (uint8_t)147U, (uint8_t)224U, (uint8_t)35U, (uint8_t)239U,
    (uint8_t)73U, (uint8_t)75U, (uint8_t)28U, (uint8_t)48U, (uint8_t)121U, (uint8_t)178U,
    (uint8_t)209U, (uint8_t)14U, (uint8_t)246U, (uint8_t)127U, (uint8_t)49U, (uint8_t)112U,
    (uint8_t)116U, (uint8_t)4U, (uint8_t)149U, (uint8_t)206U, (uint8_t)44U, (uint8_t)197U,
    (uint8_t)127U, (uint8_t)142U, (uint8_t)228U, (uint8_t)176U, (uint8_t)97U, (uint8_t)139U,
    (uint8_t)142U, (uint8_t)229U
  };

static uint8_t
sigver_vectors256_low68[32U] =
  {
    (uint8_t)92U, (uint8_t)200U, (uint8_t)170U, (uint8_t)124U, (uint8_t)53U, (uint8_t)116U,
    (uint8_t)62U, (uint8_t)192U, (uint8_t)194U, (uint8_t)61U, (uint8_t)222U, (uint8_t)136U,
    (uint8_t)218U, (uint8_t)189U, (uint8_t)94U, (uint8_t)79U, (uint8_t)205U, (uint8_t)1U,
    (uint8_t)146U, (uint8_t)210U, (uint8_t)17U, (uint8_t)111U, (uint8_t)105U, (uint8_t)38U,
    (uint8_t)254U, (uint8_t)247U, (uint8_t)136U, (uint8_t)205U, (uint8_t)219U, (uint8_t)117U,
    (uint8_t)78U, (uint8_t)115U
  };

static uint8_t
sigver_vectors256_low69[32U] =
  {
    (uint8_t)156U, (uint8_t)156U, (uint8_t)4U, (uint8_t)94U, (uint8_t)186U, (uint8_t)161U,
    (uint8_t)184U, (uint8_t)40U, (uint8_t)195U, (uint8_t)47U, (uint8_t)130U, (uint8_t)172U,
    (uint8_t)224U, (uint8_t)209U, (uint8_t)141U, (uint8_t)174U, (uint8_t)191U, (uint8_t)94U,
    (uint8_t)21U, (uint8_t)110U, (uint8_t)183U, (uint8_t)203U, (uint8_t)253U, (uint8_t)193U,
    (uint8_t)239U, (uint8_t)244U, (uint8_t)57U, (uint8_t)154U, (uint8_t)138U, (uint8_t)144U,
    (uint8_t)10U, (uint8_t)231U
  };

static uint8_t
sigver_vectors256_low70[128U] =
  {
    (uint8_t)96U, (uint8_t)205U, (uint8_t)100U, (uint8_t)178U, (uint8_t)205U, (uint8_t)43U,
    (uint8_t)230U, (uint8_t)195U, (uint8_t)56U, (uint8_t)89U, (uint8_t)185U, (uint8_t)72U,
    (uint8_t)117U, (uint8_t)18U, (uint8_t)3U, (uint8_t)97U, (uint8_t)162U, (uint8_t)64U,
    (uint8_t)133U, (uint8_t)243U, (uint8_t)118U, (uint8_t)92U, (uint8_t)184U, (uint8_t)178U,
    (uint8_t)191U, (uint8_t)17U, (uint8_t)224U, (uint8_t)38U, (uint8_t)250U, (uint8_t)157U,
    (uint8_t)136U, (uint8_t)85U, (uint8_t)219U, (uint8_t)228U, (uint8_t)53U, (uint8_t)172U,
    (uint8_t)247U, (uint8_t)136U, (uint8_t)46U, (uint8_t)132U, (uint8_t)243U, (uint8_t)199U,
    (uint8_t)133U, (uint8_t)127U, (uint8_t)150U, (uint8_t)226U, (uint8_t)186U, (uint8_t)171U,
    (uint8_t)77U, (uint8_t)154U, (uint8_t)254U, (uint8_t)69U, (uint8_t)136U, (uint8_t)228U,
    (uint8_t)168U, (uint8_t)46U, (uint8_t)23U, (uint8_t)167U, (uint8_t)136U, (uint8_t)39U,
    (uint8_t)191U, (uint8_t)219U, (uint8_t)93U, (uint8_t)219U, (uint8_t)209U, (uint8_t)194U,
    (uint8_t)17U, (uint8_t)251U, (uint8_t)194U, (uint8_t)230U, (uint8_t)216U, (uint8_t)132U,
    (uint8_t)205U, (uint8_t)221U, (uint8_t)124U, (uint8_t)185U, (uint8_t)217U, (uint8_t)13U,
    (uint8_t)91U, (uint8_t)244U, (uint8_t)167U, (uint8_t)49U, (uint8_t)27U, (uint8_t)131U,
    (uint8_t)243U, (uint8_t)82U, (uint8_t)80U, (uint8_t)128U, (uint8_t)51U, (uint8_t)129U,
    (uint8_t)44U, (uint8_t)119U, (uint8_t)106U, (uint8_t)14U, (uint8_t)0U, (uint8_t)192U,
    (uint8_t)3U, (uint8_t)199U, (uint8_t)224U, (uint8_t)214U, (uint8_t)40U, (uint8_t)229U,
    (uint8_t)7U, (uint8_t)54U, (uint8_t)199U, (uint8_t)81U, (uint8_t)45U, (uint8_t)240U,
    (uint8_t)172U, (uint8_t)250U, (uint8_t)159U, (uint8_t)35U, (uint8_t)32U, (uint8_t)189U,
    (uint8_t)16U, (uint8_t)34U, (uint8_t)41U, (uint8_t)244U, (uint8_t)100U, (uint8_t)149U,
    (uint8_t)174U, (uint8_t)109U, (uint8_t)8U, (uint8_t)87U, (uint8_t)204U, (uint8_t)69U,
    (uint8_t)42U, (uint8_t)132U
  };

static uint8_t
sigver_vectors256_low71[32U] =
  {
    (uint8_t)45U, (uint8_t)152U, (uint8_t)234U, (uint8_t)1U, (uint8_t)247U, (uint8_t)84U,
    (uint8_t)211U, (uint8_t)75U, (uint8_t)188U, (uint8_t)48U, (uint8_t)3U, (uint8_t)223U,
    (uint8_t)80U, (uint8_t)80U, (uint8_t)32U, (uint8_t)10U, (uint8_t)191U, (uint8_t)68U,
    (uint8_t)94U, (uint8_t)199U, (uint8_t)40U, (uint8_t)85U, (uint8_t)109U, (uint8_t)126U,
    (uint8_t)215U, (uint8_t)213U, (uint8_t)197U, (uint8_t)76U, (uint8_t)85U, (uint8_t)85U,
    (uint8_t)43U, (uint8_t)109U
  };

static uint8_t
sigver_vectors256_low72[32U] =
  {
    (uint8_t)155U, (uint8_t)82U, (uint8_t)103U, (uint8_t)39U, (uint8_t)66U, (uint8_t)214U,
    (uint8_t)55U, (uint8_t)163U, (uint8_t)42U, (uint8_t)221U, (uint8_t)5U, (uint8_t)109U,
    (uint8_t)253U, (uint8_t)109U, (uint8_t)135U, (uint8_t)146U, (uint8_t)242U, (uint8_t)163U,
    (uint8_t)60U, (uint8_t)46U, (uint8_t)105U, (uint8_t)218U, (uint8_t)250U, (uint8_t)190U,
    (uint8_t)160U, (uint8_t)155U, (uint8_t)150U, (uint8_t)11U, (uint8_t)198U, (uint8_t)30U,
    (uint8_t)35U, (uint8_t)10U
  };

static uint8_t
sigver_vectors256_low73[32U] =
  {
    (uint8_t)6U, (uint8_t)16U, (uint8_t)142U, (uint8_t)82U, (uint8_t)95U, (uint8_t)132U,
    (uint8_t)93U, (uint8_t)1U, (uint8_t)85U, (uint8_t)191U, (uint8_t)96U, (uint8_t)25U,
    (uint8_t)50U, (uint8_t)34U, (uint8_t)179U, (uint8_t)33U, (uint8_t)156U, (uint8_t)152U,
    (uint8_t)227U, (uint8_t)212U, (uint8_t)148U, (uint8_t)36U, (uint8_t)194U, (uint8_t)251U,
    (uint8_t)42U, (uint8_t)9U, (uint8_t)135U, (uint8_t)248U, (uint8_t)37U, (uint8_t)193U,
    (uint8_t)121U, (uint8_t)89U
  };

static uint8_t
sigver_vectors256_low74[32U] =
  {
    (uint8_t)98U, (uint8_t)181U, (uint8_t)205U, (uint8_t)213U, (uint8_t)145U, (uint8_t)229U,
    (uint8_t)181U, (uint8_t)7U, (uint8_t)229U, (uint8_t)96U, (uint8_t)22U, (uint8_t)123U,
    (uint8_t)168U, (uint8_t)246U, (uint8_t)247U, (uint8_t)205U, (uint8_t)167U, (uint8_t)70U,
    (uint8_t)115U, (uint8_t)235U, (uint8_t)49U, (uint8_t)86U, (uint8_t)128U, (uint8_t)203U,
    (uint8_t)137U, (uint8_t)204U, (uint8_t)188U, (uint8_t)78U, (uint8_t)236U, (uint8_t)71U,
    (uint8_t)125U, (uint8_t)206U
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
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low0 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low1 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low2 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low3 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low4 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low5 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low6 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low7 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low8 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low9 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low10 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low11 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low12 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low13 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low14 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low15 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low16 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low17 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low18 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low19 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low20 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low21 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low22 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low23 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low24 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low25 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low26 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low27 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low28 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low29 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low30 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low31 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low32 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low33 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low34 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low35 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low36 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low37 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low38 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low39 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low40 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low41 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low42 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low43 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low44 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low45 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low46 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low47 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low48 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low49 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low50 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low51 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low52 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low53 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low54 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low55 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low56 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low57 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low58 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low59 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low60 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low61 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low62 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low63 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low64 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low65 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low66 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low67 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low68 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low69 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors256_low70 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors256_low71 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors256_low72 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors256_low73 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors256_low74 }, .f5 = true
    }
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
sigver_vectors256_low = { .len = (uint32_t)15U, .b = sigver_vectors256_low75 };

static uint8_t
sigver_vectors384_low0[128U] =
  {
    (uint8_t)254U, (uint8_t)152U, (uint8_t)56U, (uint8_t)240U, (uint8_t)7U, (uint8_t)189U,
    (uint8_t)198U, (uint8_t)175U, (uint8_t)205U, (uint8_t)98U, (uint8_t)105U, (uint8_t)116U,
    (uint8_t)252U, (uint8_t)198U, (uint8_t)131U, (uint8_t)63U, (uint8_t)6U, (uint8_t)182U,
    (uint8_t)253U, (uint8_t)151U, (uint8_t)4U, (uint8_t)39U, (uint8_t)185U, (uint8_t)98U,
    (uint8_t)215U, (uint8_t)92U, (uint8_t)42U, (uint8_t)234U, (uint8_t)219U, (uint8_t)239U,
    (uint8_t)56U, (uint8_t)107U, (uint8_t)236U, (uint8_t)141U, (uint8_t)1U, (uint8_t)129U,
    (uint8_t)6U, (uint8_t)25U, (uint8_t)127U, (uint8_t)226U, (uint8_t)84U, (uint8_t)125U,
    (uint8_t)42U, (uint8_t)240U, (uint8_t)46U, (uint8_t)122U, (uint8_t)121U, (uint8_t)73U,
    (uint8_t)150U, (uint8_t)93U, (uint8_t)95U, (uint8_t)188U, (uint8_t)76U, (uint8_t)93U,
    (uint8_t)185U, (uint8_t)9U, (uint8_t)169U, (uint8_t)91U, (uint8_t)152U, (uint8_t)88U,
    (uint8_t)66U, (uint8_t)106U, (uint8_t)51U, (uint8_t)192U, (uint8_t)128U, (uint8_t)176U,
    (uint8_t)178U, (uint8_t)93U, (uint8_t)174U, (uint8_t)139U, (uint8_t)86U, (uint8_t)197U,
    (uint8_t)203U, (uint8_t)198U, (uint8_t)196U, (uint8_t)238U, (uint8_t)195U, (uint8_t)219U,
    (uint8_t)216U, (uint8_t)22U, (uint8_t)53U, (uint8_t)199U, (uint8_t)148U, (uint8_t)87U,
    (uint8_t)234U, (uint8_t)239U, (uint8_t)79U, (uint8_t)171U, (uint8_t)57U, (uint8_t)230U,
    (uint8_t)98U, (uint8_t)161U, (uint8_t)208U, (uint8_t)91U, (uint8_t)36U, (uint8_t)129U,
    (uint8_t)237U, (uint8_t)168U, (uint8_t)193U, (uint8_t)7U, (uint8_t)74U, (uint8_t)226U,
    (uint8_t)209U, (uint8_t)112U, (uint8_t)76U, (uint8_t)138U, (uint8_t)63U, (uint8_t)118U,
    (uint8_t)150U, (uint8_t)134U, (uint8_t)161U, (uint8_t)249U, (uint8_t)101U, (uint8_t)239U,
    (uint8_t)60U, (uint8_t)135U, (uint8_t)96U, (uint8_t)46U, (uint8_t)252U, (uint8_t)40U,
    (uint8_t)140U, (uint8_t)127U, (uint8_t)159U, (uint8_t)248U, (uint8_t)205U, (uint8_t)94U,
    (uint8_t)34U, (uint8_t)164U
  };

static uint8_t
sigver_vectors384_low1[32U] =
  {
    (uint8_t)64U, (uint8_t)222U, (uint8_t)209U, (uint8_t)61U, (uint8_t)187U, (uint8_t)231U,
    (uint8_t)44U, (uint8_t)98U, (uint8_t)156U, (uint8_t)56U, (uint8_t)240U, (uint8_t)127U,
    (uint8_t)127U, (uint8_t)149U, (uint8_t)207U, (uint8_t)117U, (uint8_t)165U, (uint8_t)14U,
    (uint8_t)42U, (uint8_t)82U, (uint8_t)72U, (uint8_t)151U, (uint8_t)96U, (uint8_t)76U,
    (uint8_t)132U, (uint8_t)250U, (uint8_t)253U, (uint8_t)229U, (uint8_t)228U, (uint8_t)202U,
    (uint8_t)251U, (uint8_t)159U
  };

static uint8_t
sigver_vectors384_low2[32U] =
  {
    (uint8_t)161U, (uint8_t)114U, (uint8_t)2U, (uint8_t)233U, (uint8_t)45U, (uint8_t)125U,
    (uint8_t)106U, (uint8_t)55U, (uint8_t)196U, (uint8_t)56U, (uint8_t)119U, (uint8_t)147U,
    (uint8_t)73U, (uint8_t)253U, (uint8_t)121U, (uint8_t)86U, (uint8_t)125U, (uint8_t)117U,
    (uint8_t)164U, (uint8_t)14U, (uint8_t)242U, (uint8_t)43U, (uint8_t)125U, (uint8_t)9U,
    (uint8_t)202U, (uint8_t)33U, (uint8_t)204U, (uint8_t)244U, (uint8_t)174U, (uint8_t)201U,
    (uint8_t)166U, (uint8_t)108U
  };

static uint8_t
sigver_vectors384_low3[32U] =
  {
    (uint8_t)190U, (uint8_t)52U, (uint8_t)115U, (uint8_t)12U, (uint8_t)49U, (uint8_t)115U,
    (uint8_t)11U, (uint8_t)78U, (uint8_t)65U, (uint8_t)46U, (uint8_t)108U, (uint8_t)82U,
    (uint8_t)194U, (uint8_t)62U, (uint8_t)219U, (uint8_t)211U, (uint8_t)101U, (uint8_t)131U,
    (uint8_t)172U, (uint8_t)226U, (uint8_t)16U, (uint8_t)43U, (uint8_t)57U, (uint8_t)175U,
    (uint8_t)161U, (uint8_t)29U, (uint8_t)36U, (uint8_t)182U, (uint8_t)132U, (uint8_t)140U,
    (uint8_t)183U, (uint8_t)127U
  };

static uint8_t
sigver_vectors384_low4[32U] =
  {
    (uint8_t)3U, (uint8_t)101U, (uint8_t)82U, (uint8_t)2U, (uint8_t)213U, (uint8_t)253U,
    (uint8_t)140U, (uint8_t)158U, (uint8_t)58U, (uint8_t)233U, (uint8_t)113U, (uint8_t)182U,
    (uint8_t)240U, (uint8_t)128U, (uint8_t)100U, (uint8_t)12U, (uint8_t)64U, (uint8_t)97U,
    (uint8_t)18U, (uint8_t)253U, (uint8_t)149U, (uint8_t)231U, (uint8_t)1U, (uint8_t)88U,
    (uint8_t)116U, (uint8_t)233U, (uint8_t)182U, (uint8_t)238U, (uint8_t)119U, (uint8_t)117U,
    (uint8_t)43U, (uint8_t)16U
  };

static uint8_t
sigver_vectors384_low5[128U] =
  {
    (uint8_t)182U, (uint8_t)144U, (uint8_t)67U, (uint8_t)185U, (uint8_t)179U, (uint8_t)49U,
    (uint8_t)218U, (uint8_t)57U, (uint8_t)43U, (uint8_t)93U, (uint8_t)214U, (uint8_t)137U,
    (uint8_t)20U, (uint8_t)45U, (uint8_t)252U, (uint8_t)114U, (uint8_t)50U, (uint8_t)66U,
    (uint8_t)101U, (uint8_t)218U, (uint8_t)8U, (uint8_t)241U, (uint8_t)74U, (uint8_t)188U,
    (uint8_t)237U, (uint8_t)240U, (uint8_t)58U, (uint8_t)216U, (uint8_t)38U, (uint8_t)62U,
    (uint8_t)107U, (uint8_t)220U, (uint8_t)203U, (uint8_t)199U, (uint8_t)80U, (uint8_t)152U,
    (uint8_t)162U, (uint8_t)112U, (uint8_t)11U, (uint8_t)187U, (uint8_t)161U, (uint8_t)151U,
    (uint8_t)157U, (uint8_t)232U, (uint8_t)76U, (uint8_t)143U, (uint8_t)18U, (uint8_t)137U,
    (uint8_t)26U, (uint8_t)160U, (uint8_t)208U, (uint8_t)0U, (uint8_t)248U, (uint8_t)161U,
    (uint8_t)171U, (uint8_t)173U, (uint8_t)125U, (uint8_t)222U, (uint8_t)73U, (uint8_t)129U,
    (uint8_t)83U, (uint8_t)63U, (uint8_t)33U, (uint8_t)218U, (uint8_t)89U, (uint8_t)204U,
    (uint8_t)128U, (uint8_t)217U, (uint8_t)207U, (uint8_t)148U, (uint8_t)81U, (uint8_t)127U,
    (uint8_t)59U, (uint8_t)97U, (uint8_t)209U, (uint8_t)167U, (uint8_t)217U, (uint8_t)238U,
    (uint8_t)203U, (uint8_t)47U, (uint8_t)207U, (uint8_t)5U, (uint8_t)46U, (uint8_t)31U,
    (uint8_t)201U, (uint8_t)231U, (uint8_t)24U, (uint8_t)140U, (uint8_t)3U, (uint8_t)27U,
    (uint8_t)134U, (uint8_t)48U, (uint8_t)94U, (uint8_t)74U, (uint8_t)67U, (uint8_t)106U,
    (uint8_t)55U, (uint8_t)148U, (uint8_t)128U, (uint8_t)113U, (uint8_t)240U, (uint8_t)70U,
    (uint8_t)227U, (uint8_t)6U, (uint8_t)190U, (uint8_t)251U, (uint8_t)133U, (uint8_t)17U,
    (uint8_t)220U, (uint8_t)3U, (uint8_t)165U, (uint8_t)61U, (uint8_t)200U, (uint8_t)118U,
    (uint8_t)154U, (uint8_t)144U, (uint8_t)168U, (uint8_t)110U, (uint8_t)155U, (uint8_t)79U,
    (uint8_t)219U, (uint8_t)240U, (uint8_t)93U, (uint8_t)205U, (uint8_t)250U, (uint8_t)53U,
    (uint8_t)171U, (uint8_t)115U
  };

static uint8_t
sigver_vectors384_low6[32U] =
  {
    (uint8_t)31U, (uint8_t)128U, (uint8_t)225U, (uint8_t)159U, (uint8_t)254U, (uint8_t)181U,
    (uint8_t)29U, (uint8_t)215U, (uint8_t)79U, (uint8_t)28U, (uint8_t)57U, (uint8_t)122U,
    (uint8_t)195U, (uint8_t)223U, (uint8_t)211U, (uint8_t)65U, (uint8_t)90U, (uint8_t)177U,
    (uint8_t)110U, (uint8_t)189U, (uint8_t)8U, (uint8_t)71U, (uint8_t)237U, (uint8_t)17U,
    (uint8_t)158U, (uint8_t)108U, (uint8_t)59U, (uint8_t)21U, (uint8_t)161U, (uint8_t)168U,
    (uint8_t)132U, (uint8_t)184U
  };

static uint8_t
sigver_vectors384_low7[32U] =
  {
    (uint8_t)155U, (uint8_t)57U, (uint8_t)87U, (uint8_t)135U, (uint8_t)55U, (uint8_t)29U,
    (uint8_t)191U, (uint8_t)181U, (uint8_t)93U, (uint8_t)19U, (uint8_t)71U, (uint8_t)215U,
    (uint8_t)190U, (uint8_t)209U, (uint8_t)194U, (uint8_t)97U, (uint8_t)210U, (uint8_t)144U,
    (uint8_t)129U, (uint8_t)33U, (uint8_t)251U, (uint8_t)120U, (uint8_t)222U, (uint8_t)29U,
    (uint8_t)27U, (uint8_t)242U, (uint8_t)208U, (uint8_t)6U, (uint8_t)102U, (uint8_t)166U,
    (uint8_t)42U, (uint8_t)237U
  };

static uint8_t
sigver_vectors384_low8[32U] =
  {
    (uint8_t)36U, (uint8_t)156U, (uint8_t)162U, (uint8_t)195U, (uint8_t)235U, (uint8_t)110U,
    (uint8_t)4U, (uint8_t)172U, (uint8_t)87U, (uint8_t)51U, (uint8_t)76U, (uint8_t)47U,
    (uint8_t)117U, (uint8_t)220U, (uint8_t)94U, (uint8_t)101U, (uint8_t)139U, (uint8_t)187U,
    (uint8_t)72U, (uint8_t)91U, (uint8_t)241U, (uint8_t)135U, (uint8_t)16U, (uint8_t)7U,
    (uint8_t)116U, (uint8_t)245U, (uint8_t)9U, (uint8_t)157U, (uint8_t)209U, (uint8_t)62U,
    (uint8_t)247U, (uint8_t)7U
  };

static uint8_t
sigver_vectors384_low9[32U] =
  {
    (uint8_t)151U, (uint8_t)54U, (uint8_t)58U, (uint8_t)5U, (uint8_t)32U, (uint8_t)43U,
    (uint8_t)96U, (uint8_t)45U, (uint8_t)19U, (uint8_t)22U, (uint8_t)99U, (uint8_t)70U,
    (uint8_t)105U, (uint8_t)78U, (uint8_t)56U, (uint8_t)19U, (uint8_t)91U, (uint8_t)188U,
    (uint8_t)224U, (uint8_t)37U, (uint8_t)190U, (uint8_t)148U, (uint8_t)149U, (uint8_t)14U,
    (uint8_t)146U, (uint8_t)51U, (uint8_t)244U, (uint8_t)200U, (uint8_t)1U, (uint8_t)59U,
    (uint8_t)245U, (uint8_t)191U
  };

static uint8_t
sigver_vectors384_low10[128U] =
  {
    (uint8_t)210U, (uint8_t)252U, (uint8_t)170U, (uint8_t)237U, (uint8_t)232U, (uint8_t)184U,
    (uint8_t)121U, (uint8_t)192U, (uint8_t)100U, (uint8_t)176U, (uint8_t)170U, (uint8_t)70U,
    (uint8_t)230U, (uint8_t)142U, (uint8_t)252U, (uint8_t)39U, (uint8_t)138U, (uint8_t)70U,
    (uint8_t)155U, (uint8_t)128U, (uint8_t)167U, (uint8_t)247U, (uint8_t)225U, (uint8_t)147U,
    (uint8_t)158U, (uint8_t)194U, (uint8_t)235U, (uint8_t)201U, (uint8_t)108U, (uint8_t)118U,
    (uint8_t)32U, (uint8_t)111U, (uint8_t)35U, (uint8_t)57U, (uint8_t)89U, (uint8_t)103U,
    (uint8_t)39U, (uint8_t)156U, (uint8_t)24U, (uint8_t)31U, (uint8_t)234U, (uint8_t)21U,
    (uint8_t)126U, (uint8_t)187U, (uint8_t)121U, (uint8_t)223U, (uint8_t)173U, (uint8_t)198U,
    (uint8_t)142U, (uint8_t)49U, (uint8_t)52U, (uint8_t)95U, (uint8_t)7U, (uint8_t)241U,
    (uint8_t)51U, (uint8_t)5U, (uint8_t)200U, (uint8_t)13U, (uint8_t)224U, (uint8_t)216U,
    (uint8_t)94U, (uint8_t)67U, (uint8_t)48U, (uint8_t)211U, (uint8_t)164U, (uint8_t)95U,
    (uint8_t)149U, (uint8_t)124U, (uint8_t)92U, (uint8_t)37U, (uint8_t)38U, (uint8_t)185U,
    (uint8_t)69U, (uint8_t)131U, (uint8_t)140U, (uint8_t)229U, (uint8_t)169U, (uint8_t)194U,
    (uint8_t)132U, (uint8_t)75U, (uint8_t)107U, (uint8_t)42U, (uint8_t)102U, (uint8_t)92U,
    (uint8_t)15U, (uint8_t)112U, (uint8_t)183U, (uint8_t)72U, (uint8_t)177U, (uint8_t)33U,
    (uint8_t)58U, (uint8_t)140U, (uint8_t)242U, (uint8_t)11U, (uint8_t)165U, (uint8_t)219U,
    (uint8_t)223U, (uint8_t)140U, (uint8_t)171U, (uint8_t)35U, (uint8_t)31U, (uint8_t)67U,
    (uint8_t)61U, (uint8_t)165U, (uint8_t)34U, (uint8_t)16U, (uint8_t)74U, (uint8_t)92U,
    (uint8_t)208U, (uint8_t)39U, (uint8_t)211U, (uint8_t)227U, (uint8_t)107U, (uint8_t)179U,
    (uint8_t)115U, (uint8_t)196U, (uint8_t)237U, (uint8_t)64U, (uint8_t)77U, (uint8_t)154U,
    (uint8_t)240U, (uint8_t)203U, (uint8_t)236U, (uint8_t)111U, (uint8_t)133U, (uint8_t)236U,
    (uint8_t)33U, (uint8_t)147U
  };

static uint8_t
sigver_vectors384_low11[32U] =
  {
    (uint8_t)206U, (uint8_t)77U, (uint8_t)207U, (uint8_t)167U, (uint8_t)56U, (uint8_t)76U,
    (uint8_t)131U, (uint8_t)68U, (uint8_t)58U, (uint8_t)206U, (uint8_t)15U, (uint8_t)184U,
    (uint8_t)44U, (uint8_t)74U, (uint8_t)193U, (uint8_t)173U, (uint8_t)250U, (uint8_t)16U,
    (uint8_t)10U, (uint8_t)155U, (uint8_t)44U, (uint8_t)123U, (uint8_t)240U, (uint8_t)159U,
    (uint8_t)9U, (uint8_t)63U, (uint8_t)139U, (uint8_t)109U, (uint8_t)8U, (uint8_t)78U,
    (uint8_t)80U, (uint8_t)194U
  };

static uint8_t
sigver_vectors384_low12[32U] =
  {
    (uint8_t)217U, (uint8_t)138U, (uint8_t)231U, (uint8_t)185U, (uint8_t)26U, (uint8_t)190U,
    (uint8_t)230U, (uint8_t)72U, (uint8_t)208U, (uint8_t)191U, (uint8_t)222U, (uint8_t)25U,
    (uint8_t)39U, (uint8_t)3U, (uint8_t)116U, (uint8_t)26U, (uint8_t)194U, (uint8_t)29U,
    (uint8_t)170U, (uint8_t)215U, (uint8_t)38U, (uint8_t)42U, (uint8_t)244U, (uint8_t)24U,
    (uint8_t)181U, (uint8_t)14U, (uint8_t)64U, (uint8_t)109U, (uint8_t)130U, (uint8_t)94U,
    (uint8_t)176U, (uint8_t)214U
  };

static uint8_t
sigver_vectors384_low13[32U] =
  {
    (uint8_t)89U, (uint8_t)126U, (uint8_t)30U, (uint8_t)4U, (uint8_t)217U, (uint8_t)58U,
    (uint8_t)107U, (uint8_t)68U, (uint8_t)76U, (uint8_t)204U, (uint8_t)68U, (uint8_t)122U,
    (uint8_t)72U, (uint8_t)101U, (uint8_t)31U, (uint8_t)23U, (uint8_t)101U, (uint8_t)127U,
    (uint8_t)244U, (uint8_t)63U, (uint8_t)182U, (uint8_t)95U, (uint8_t)233U, (uint8_t)68U,
    (uint8_t)97U, (uint8_t)210U, (uint8_t)191U, (uint8_t)129U, (uint8_t)107U, (uint8_t)1U,
    (uint8_t)175U, (uint8_t)64U
  };

static uint8_t
sigver_vectors384_low14[32U] =
  {
    (uint8_t)53U, (uint8_t)159U, (uint8_t)227U, (uint8_t)129U, (uint8_t)121U, (uint8_t)99U,
    (uint8_t)84U, (uint8_t)142U, (uint8_t)103U, (uint8_t)109U, (uint8_t)109U, (uint8_t)163U,
    (uint8_t)76U, (uint8_t)45U, (uint8_t)8U, (uint8_t)102U, (uint8_t)170U, (uint8_t)66U,
    (uint8_t)73U, (uint8_t)146U, (uint8_t)55U, (uint8_t)182U, (uint8_t)130U, (uint8_t)0U,
    (uint8_t)40U, (uint8_t)137U, (uint8_t)234U, (uint8_t)248U, (uint8_t)137U, (uint8_t)56U,
    (uint8_t)20U, (uint8_t)210U
  };

static uint8_t
sigver_vectors384_low15[128U] =
  {
    (uint8_t)6U, (uint8_t)205U, (uint8_t)134U, (uint8_t)72U, (uint8_t)24U, (uint8_t)101U,
    (uint8_t)24U, (uint8_t)28U, (uint8_t)239U, (uint8_t)122U, (uint8_t)205U, (uint8_t)195U,
    (uint8_t)32U, (uint8_t)40U, (uint8_t)36U, (uint8_t)151U, (uint8_t)14U, (uint8_t)194U,
    (uint8_t)217U, (uint8_t)118U, (uint8_t)98U, (uint8_t)181U, (uint8_t)25U, (uint8_t)196U,
    (uint8_t)181U, (uint8_t)136U, (uint8_t)220U, (uint8_t)158U, (uint8_t)81U, (uint8_t)97U,
    (uint8_t)124U, (uint8_t)6U, (uint8_t)130U, (uint8_t)130U, (uint8_t)177U, (uint8_t)161U,
    (uint8_t)26U, (uint8_t)21U, (uint8_t)191U, (uint8_t)126U, (uint8_t)252U, (uint8_t)72U,
    (uint8_t)88U, (uint8_t)162U, (uint8_t)243U, (uint8_t)122U, (uint8_t)61U, (uint8_t)116U,
    (uint8_t)176U, (uint8_t)95U, (uint8_t)181U, (uint8_t)121U, (uint8_t)14U, (uint8_t)182U,
    (uint8_t)131U, (uint8_t)56U, (uint8_t)200U, (uint8_t)0U, (uint8_t)155U, (uint8_t)77U,
    (uint8_t)169U, (uint8_t)180U, (uint8_t)39U, (uint8_t)5U, (uint8_t)20U, (uint8_t)211U,
    (uint8_t)135U, (uint8_t)162U, (uint8_t)224U, (uint8_t)22U, (uint8_t)169U, (uint8_t)158U,
    (uint8_t)225U, (uint8_t)9U, (uint8_t)132U, (uint8_t)30U, (uint8_t)136U, (uint8_t)74U,
    (uint8_t)121U, (uint8_t)9U, (uint8_t)80U, (uint8_t)78U, (uint8_t)243U, (uint8_t)26U,
    (uint8_t)84U, (uint8_t)84U, (uint8_t)226U, (uint8_t)20U, (uint8_t)102U, (uint8_t)63U,
    (uint8_t)131U, (uint8_t)15U, (uint8_t)35U, (uint8_t)165U, (uint8_t)167U, (uint8_t)111U,
    (uint8_t)145U, (uint8_t)64U, (uint8_t)47U, (uint8_t)202U, (uint8_t)95U, (uint8_t)93U,
    (uint8_t)97U, (uint8_t)105U, (uint8_t)159U, (uint8_t)168U, (uint8_t)116U, (uint8_t)89U,
    (uint8_t)123U, (uint8_t)219U, (uint8_t)251U, (uint8_t)30U, (uint8_t)207U, (uint8_t)248U,
    (uint8_t)240U, (uint8_t)125U, (uint8_t)219U, (uint8_t)208U, (uint8_t)126U, (uint8_t)246U,
    (uint8_t)30U, (uint8_t)151U, (uint8_t)208U, (uint8_t)213U, (uint8_t)38U, (uint8_t)46U,
    (uint8_t)243U, (uint8_t)20U
  };

static uint8_t
sigver_vectors384_low16[32U] =
  {
    (uint8_t)27U, (uint8_t)103U, (uint8_t)127U, (uint8_t)83U, (uint8_t)90U, (uint8_t)198U,
    (uint8_t)157U, (uint8_t)26U, (uint8_t)205U, (uint8_t)69U, (uint8_t)146U, (uint8_t)192U,
    (uint8_t)209U, (uint8_t)47U, (uint8_t)172U, (uint8_t)19U, (uint8_t)201U, (uint8_t)19U,
    (uint8_t)30U, (uint8_t)90U, (uint8_t)111U, (uint8_t)138U, (uint8_t)180U, (uint8_t)249U,
    (uint8_t)208U, (uint8_t)175U, (uint8_t)220U, (uint8_t)179U, (uint8_t)163U, (uint8_t)243U,
    (uint8_t)39U, (uint8_t)224U
  };

static uint8_t
sigver_vectors384_low17[32U] =
  {
    (uint8_t)93U, (uint8_t)202U, (uint8_t)44U, (uint8_t)115U, (uint8_t)236U, (uint8_t)137U,
    (uint8_t)229U, (uint8_t)142U, (uint8_t)248U, (uint8_t)38U, (uint8_t)124U, (uint8_t)186U,
    (uint8_t)43U, (uint8_t)181U, (uint8_t)235U, (uint8_t)15U, (uint8_t)85U, (uint8_t)31U,
    (uint8_t)65U, (uint8_t)47U, (uint8_t)157U, (uint8_t)192U, (uint8_t)135U, (uint8_t)193U,
    (uint8_t)166U, (uint8_t)148U, (uint8_t)79U, (uint8_t)12U, (uint8_t)228U, (uint8_t)117U,
    (uint8_t)39U, (uint8_t)122U
  };

static uint8_t
sigver_vectors384_low18[32U] =
  {
    (uint8_t)223U, (uint8_t)11U, (uint8_t)12U, (uint8_t)215U, (uint8_t)109U, (uint8_t)37U,
    (uint8_t)85U, (uint8_t)212U, (uint8_t)195U, (uint8_t)139U, (uint8_t)61U, (uint8_t)112U,
    (uint8_t)191U, (uint8_t)223U, (uint8_t)150U, (uint8_t)72U, (uint8_t)132U, (uint8_t)208U,
    (uint8_t)190U, (uint8_t)235U, (uint8_t)159U, (uint8_t)116U, (uint8_t)56U, (uint8_t)95U,
    (uint8_t)8U, (uint8_t)147U, (uint8_t)232U, (uint8_t)125U, (uint8_t)32U, (uint8_t)201U,
    (uint8_t)100U, (uint8_t)45U
  };

static uint8_t
sigver_vectors384_low19[32U] =
  {
    (uint8_t)18U, (uint8_t)130U, (uint8_t)153U, (uint8_t)170U, (uint8_t)191U, (uint8_t)31U,
    (uint8_t)84U, (uint8_t)150U, (uint8_t)17U, (uint8_t)43U, (uint8_t)225U, (uint8_t)254U,
    (uint8_t)4U, (uint8_t)54U, (uint8_t)95U, (uint8_t)95U, (uint8_t)130U, (uint8_t)21U,
    (uint8_t)176U, (uint8_t)138U, (uint8_t)4U, (uint8_t)10U, (uint8_t)189U, (uint8_t)254U,
    (uint8_t)202U, (uint8_t)70U, (uint8_t)38U, (uint8_t)244U, (uint8_t)209U, (uint8_t)92U,
    (uint8_t)0U, (uint8_t)91U
  };

static uint8_t
sigver_vectors384_low20[128U] =
  {
    (uint8_t)89U, (uint8_t)173U, (uint8_t)41U, (uint8_t)115U, (uint8_t)151U, (uint8_t)243U,
    (uint8_t)80U, (uint8_t)54U, (uint8_t)4U, (uint8_t)164U, (uint8_t)162U, (uint8_t)208U,
    (uint8_t)152U, (uint8_t)164U, (uint8_t)240U, (uint8_t)10U, (uint8_t)54U, (uint8_t)138U,
    (uint8_t)217U, (uint8_t)92U, (uint8_t)97U, (uint8_t)1U, (uint8_t)179U, (uint8_t)211U,
    (uint8_t)143U, (uint8_t)157U, (uint8_t)73U, (uint8_t)217U, (uint8_t)8U, (uint8_t)119U,
    (uint8_t)108U, (uint8_t)90U, (uint8_t)108U, (uint8_t)134U, (uint8_t)84U, (uint8_t)176U,
    (uint8_t)6U, (uint8_t)173U, (uint8_t)183U, (uint8_t)147U, (uint8_t)159U, (uint8_t)251U,
    (uint8_t)108U, (uint8_t)48U, (uint8_t)175U, (uint8_t)163U, (uint8_t)37U, (uint8_t)181U,
    (uint8_t)65U, (uint8_t)133U, (uint8_t)216U, (uint8_t)44U, (uint8_t)60U, (uint8_t)192U,
    (uint8_t)216U, (uint8_t)54U, (uint8_t)133U, (uint8_t)13U, (uint8_t)206U, (uint8_t)84U,
    (uint8_t)211U, (uint8_t)64U, (uint8_t)139U, (uint8_t)37U, (uint8_t)124U, (uint8_t)58U,
    (uint8_t)150U, (uint8_t)29U, (uint8_t)17U, (uint8_t)250U, (uint8_t)254U, (uint8_t)43U,
    (uint8_t)116U, (uint8_t)186U, (uint8_t)139U, (uint8_t)221U, (uint8_t)252U, (uint8_t)17U,
    (uint8_t)2U, (uint8_t)250U, (uint8_t)101U, (uint8_t)109U, (uint8_t)16U, (uint8_t)40U,
    (uint8_t)186U, (uint8_t)249U, (uint8_t)76U, (uint8_t)56U, (uint8_t)52U, (uint8_t)12U,
    (uint8_t)38U, (uint8_t)161U, (uint8_t)30U, (uint8_t)153U, (uint8_t)42U, (uint8_t)171U,
    (uint8_t)113U, (uint8_t)206U, (uint8_t)55U, (uint8_t)50U, (uint8_t)39U, (uint8_t)27U,
    (uint8_t)118U, (uint8_t)115U, (uint8_t)88U, (uint8_t)103U, (uint8_t)27U, (uint8_t)37U,
    (uint8_t)34U, (uint8_t)89U, (uint8_t)38U, (uint8_t)243U, (uint8_t)164U, (uint8_t)185U,
    (uint8_t)236U, (uint8_t)95U, (uint8_t)130U, (uint8_t)192U, (uint8_t)89U, (uint8_t)240U,
    (uint8_t)199U, (uint8_t)209U, (uint8_t)68U, (uint8_t)109U, (uint8_t)93U, (uint8_t)158U,
    (uint8_t)66U, (uint8_t)81U
  };

static uint8_t
sigver_vectors384_low21[32U] =
  {
    (uint8_t)127U, (uint8_t)252U, (uint8_t)40U, (uint8_t)83U, (uint8_t)243U, (uint8_t)225U,
    (uint8_t)120U, (uint8_t)135U, (uint8_t)221U, (uint8_t)161U, (uint8_t)59U, (uint8_t)14U,
    (uint8_t)180U, (uint8_t)63U, (uint8_t)24U, (uint8_t)60U, (uint8_t)229U, (uint8_t)10U,
    (uint8_t)90U, (uint8_t)192U, (uint8_t)248U, (uint8_t)187U, (uint8_t)167U, (uint8_t)95U,
    (uint8_t)177U, (uint8_t)146U, (uint8_t)17U, (uint8_t)114U, (uint8_t)72U, (uint8_t)79U,
    (uint8_t)155U, (uint8_t)148U
  };

static uint8_t
sigver_vectors384_low22[32U] =
  {
    (uint8_t)76U, (uint8_t)197U, (uint8_t)35U, (uint8_t)209U, (uint8_t)65U, (uint8_t)146U,
    (uint8_t)248U, (uint8_t)11U, (uint8_t)213U, (uint8_t)178U, (uint8_t)125U, (uint8_t)48U,
    (uint8_t)179U, (uint8_t)180U, (uint8_t)30U, (uint8_t)6U, (uint8_t)77U, (uint8_t)168U,
    (uint8_t)123U, (uint8_t)251U, (uint8_t)174U, (uint8_t)21U, (uint8_t)87U, (uint8_t)45U,
    (uint8_t)211U, (uint8_t)130U, (uint8_t)185U, (uint8_t)161U, (uint8_t)118U, (uint8_t)193U,
    (uint8_t)35U, (uint8_t)162U
  };

static uint8_t
sigver_vectors384_low23[32U] =
  {
    (uint8_t)49U, (uint8_t)86U, (uint8_t)23U, (uint8_t)109U, (uint8_t)82U, (uint8_t)235U,
    (uint8_t)38U, (uint8_t)249U, (uint8_t)57U, (uint8_t)18U, (uint8_t)41U, (uint8_t)222U,
    (uint8_t)66U, (uint8_t)81U, (uint8_t)153U, (uint8_t)58U, (uint8_t)65U, (uint8_t)184U,
    (uint8_t)23U, (uint8_t)47U, (uint8_t)120U, (uint8_t)151U, (uint8_t)11U, (uint8_t)183U,
    (uint8_t)14U, (uint8_t)50U, (uint8_t)162U, (uint8_t)69U, (uint8_t)190U, (uint8_t)75U,
    (uint8_t)182U, (uint8_t)83U
  };

static uint8_t
sigver_vectors384_low24[32U] =
  {
    (uint8_t)98U, (uint8_t)130U, (uint8_t)122U, (uint8_t)41U, (uint8_t)225U, (uint8_t)45U,
    (uint8_t)47U, (uint8_t)41U, (uint8_t)176U, (uint8_t)15U, (uint8_t)178U, (uint8_t)208U,
    (uint8_t)45U, (uint8_t)213U, (uint8_t)242U, (uint8_t)213U, (uint8_t)65U, (uint8_t)46U,
    (uint8_t)23U, (uint8_t)164U, (uint8_t)69U, (uint8_t)95U, (uint8_t)68U, (uint8_t)49U,
    (uint8_t)165U, (uint8_t)201U, (uint8_t)150U, (uint8_t)136U, (uint8_t)31U, (uint8_t)223U,
    (uint8_t)192U, (uint8_t)238U
  };

static uint8_t
sigver_vectors384_low25[128U] =
  {
    (uint8_t)130U, (uint8_t)21U, (uint8_t)218U, (uint8_t)202U, (uint8_t)135U, (uint8_t)230U,
    (uint8_t)137U, (uint8_t)162U, (uint8_t)3U, (uint8_t)146U, (uint8_t)100U, (uint8_t)106U,
    (uint8_t)101U, (uint8_t)17U, (uint8_t)187U, (uint8_t)123U, (uint8_t)90U, (uint8_t)130U,
    (uint8_t)210U, (uint8_t)217U, (uint8_t)149U, (uint8_t)202U, (uint8_t)157U, (uint8_t)232U,
    (uint8_t)155U, (uint8_t)217U, (uint8_t)217U, (uint8_t)192U, (uint8_t)177U, (uint8_t)20U,
    (uint8_t)100U, (uint8_t)183U, (uint8_t)203U, (uint8_t)30U, (uint8_t)78U, (uint8_t)154U,
    (uint8_t)49U, (uint8_t)227U, (uint8_t)224U, (uint8_t)26U, (uint8_t)216U, (uint8_t)194U,
    (uint8_t)205U, (uint8_t)97U, (uint8_t)61U, (uint8_t)90U, (uint8_t)44U, (uint8_t)180U,
    (uint8_t)74U, (uint8_t)42U, (uint8_t)141U, (uint8_t)246U, (uint8_t)137U, (uint8_t)159U,
    (uint8_t)206U, (uint8_t)76U, (uint8_t)40U, (uint8_t)45U, (uint8_t)234U, (uint8_t)30U,
    (uint8_t)65U, (uint8_t)175U, (uint8_t)13U, (uint8_t)246U, (uint8_t)195U, (uint8_t)107U,
    (uint8_t)225U, (uint8_t)243U, (uint8_t)32U, (uint8_t)3U, (uint8_t)101U, (uint8_t)103U,
    (uint8_t)248U, (uint8_t)208U, (uint8_t)211U, (uint8_t)42U, (uint8_t)170U, (uint8_t)121U,
    (uint8_t)201U, (uint8_t)95U, (uint8_t)229U, (uint8_t)59U, (uint8_t)22U, (uint8_t)102U,
    (uint8_t)143U, (uint8_t)126U, (uint8_t)26U, (uint8_t)158U, (uint8_t)93U, (uint8_t)125U,
    (uint8_t)3U, (uint8_t)158U, (uint8_t)162U, (uint8_t)96U, (uint8_t)253U, (uint8_t)3U,
    (uint8_t)113U, (uint8_t)27U, (uint8_t)125U, (uint8_t)28U, (uint8_t)23U, (uint8_t)115U,
    (uint8_t)85U, (uint8_t)252U, (uint8_t)82U, (uint8_t)36U, (uint8_t)77U, (uint8_t)73U,
    (uint8_t)202U, (uint8_t)91U, (uint8_t)35U, (uint8_t)133U, (uint8_t)86U, (uint8_t)165U,
    (uint8_t)84U, (uint8_t)19U, (uint8_t)73U, (uint8_t)1U, (uint8_t)70U, (uint8_t)131U,
    (uint8_t)203U, (uint8_t)125U, (uint8_t)163U, (uint8_t)38U, (uint8_t)244U, (uint8_t)67U,
    (uint8_t)183U, (uint8_t)82U
  };

static uint8_t
sigver_vectors384_low26[32U] =
  {
    (uint8_t)85U, (uint8_t)105U, (uint8_t)247U, (uint8_t)109U, (uint8_t)201U, (uint8_t)66U,
    (uint8_t)67U, (uint8_t)205U, (uint8_t)232U, (uint8_t)25U, (uint8_t)251U, (uint8_t)111U,
    (uint8_t)200U, (uint8_t)81U, (uint8_t)68U, (uint8_t)236U, (uint8_t)103U, (uint8_t)226U,
    (uint8_t)181U, (uint8_t)212U, (uint8_t)149U, (uint8_t)57U, (uint8_t)246U, (uint8_t)46U,
    (uint8_t)36U, (uint8_t)212U, (uint8_t)6U, (uint8_t)209U, (uint8_t)182U, (uint8_t)143U,
    (uint8_t)0U, (uint8_t)88U
  };

static uint8_t
sigver_vectors384_low27[32U] =
  {
    (uint8_t)18U, (uint8_t)8U, (uint8_t)195U, (uint8_t)141U, (uint8_t)190U, (uint8_t)37U,
    (uint8_t)135U, (uint8_t)13U, (uint8_t)234U, (uint8_t)181U, (uint8_t)60U, (uint8_t)72U,
    (uint8_t)111U, (uint8_t)121U, (uint8_t)58U, (uint8_t)30U, (uint8_t)37U, (uint8_t)12U,
    (uint8_t)157U, (uint8_t)27U, (uint8_t)142U, (uint8_t)124U, (uint8_t)20U, (uint8_t)126U,
    (uint8_t)166U, (uint8_t)139U, (uint8_t)113U, (uint8_t)25U, (uint8_t)108U, (uint8_t)68U,
    (uint8_t)7U, (uint8_t)48U
  };

static uint8_t
sigver_vectors384_low28[32U] =
  {
    (uint8_t)112U, (uint8_t)111U, (uint8_t)43U, (uint8_t)164U, (uint8_t)2U, (uint8_t)94U,
    (uint8_t)124U, (uint8_t)6U, (uint8_t)182U, (uint8_t)109U, (uint8_t)99U, (uint8_t)105U,
    (uint8_t)163U, (uint8_t)249U, (uint8_t)59U, (uint8_t)47U, (uint8_t)236U, (uint8_t)70U,
    (uint8_t)197U, (uint8_t)30U, (uint8_t)206U, (uint8_t)255U, (uint8_t)66U, (uint8_t)161U,
    (uint8_t)88U, (uint8_t)247U, (uint8_t)67U, (uint8_t)25U, (uint8_t)25U, (uint8_t)80U,
    (uint8_t)108U, (uint8_t)251U
  };

static uint8_t
sigver_vectors384_low29[32U] =
  {
    (uint8_t)180U, (uint8_t)231U, (uint8_t)90U, (uint8_t)195U, (uint8_t)74U, (uint8_t)150U,
    (uint8_t)57U, (uint8_t)50U, (uint8_t)55U, (uint8_t)252U, (uint8_t)67U, (uint8_t)55U,
    (uint8_t)120U, (uint8_t)158U, (uint8_t)55U, (uint8_t)22U, (uint8_t)141U, (uint8_t)121U,
    (uint8_t)56U, (uint8_t)39U, (uint8_t)5U, (uint8_t)178U, (uint8_t)72U, (uint8_t)5U, (uint8_t)28U,
    (uint8_t)156U, (uint8_t)114U, (uint8_t)188U, (uint8_t)186U, (uint8_t)197U, (uint8_t)245U,
    (uint8_t)22U
  };

static uint8_t
sigver_vectors384_low30[128U] =
  {
    (uint8_t)169U, (uint8_t)150U, (uint8_t)177U, (uint8_t)251U, (uint8_t)128U, (uint8_t)15U,
    (uint8_t)105U, (uint8_t)37U, (uint8_t)23U, (uint8_t)162U, (uint8_t)235U, (uint8_t)128U,
    (uint8_t)232U, (uint8_t)55U, (uint8_t)35U, (uint8_t)49U, (uint8_t)147U, (uint8_t)221U,
    (uint8_t)62U, (uint8_t)130U, (uint8_t)72U, (uint8_t)77U, (uint8_t)63U, (uint8_t)73U,
    (uint8_t)189U, (uint8_t)25U, (uint8_t)238U, (uint8_t)13U, (uint8_t)184U, (uint8_t)247U,
    (uint8_t)180U, (uint8_t)64U, (uint8_t)135U, (uint8_t)107U, (uint8_t)7U, (uint8_t)227U,
    (uint8_t)132U, (uint8_t)201U, (uint8_t)10U, (uint8_t)168U, (uint8_t)185U, (uint8_t)247U,
    (uint8_t)182U, (uint8_t)96U, (uint8_t)60U, (uint8_t)160U, (uint8_t)181U, (uint8_t)164U,
    (uint8_t)224U, (uint8_t)108U, (uint8_t)29U, (uint8_t)160U, (uint8_t)237U, (uint8_t)185U,
    (uint8_t)116U, (uint8_t)162U, (uint8_t)251U, (uint8_t)155U, (uint8_t)110U, (uint8_t)124U,
    (uint8_t)114U, (uint8_t)13U, (uint8_t)223U, (uint8_t)62U, (uint8_t)92U, (uint8_t)14U,
    (uint8_t)49U, (uint8_t)76U, (uint8_t)45U, (uint8_t)24U, (uint8_t)148U, (uint8_t)2U,
    (uint8_t)144U, (uint8_t)60U, (uint8_t)8U, (uint8_t)192U, (uint8_t)131U, (uint8_t)103U,
    (uint8_t)118U, (uint8_t)195U, (uint8_t)97U, (uint8_t)162U, (uint8_t)132U, (uint8_t)219U,
    (uint8_t)136U, (uint8_t)126U, (uint8_t)188U, (uint8_t)195U, (uint8_t)62U, (uint8_t)97U,
    (uint8_t)93U, (uint8_t)233U, (uint8_t)114U, (uint8_t)11U, (uint8_t)1U, (uint8_t)218U,
    (uint8_t)218U, (uint8_t)222U, (uint8_t)88U, (uint8_t)94U, (uint8_t)239U, (uint8_t)104U,
    (uint8_t)123U, (uint8_t)51U, (uint8_t)70U, (uint8_t)70U, (uint8_t)139U, (uint8_t)218U,
    (uint8_t)251U, (uint8_t)73U, (uint8_t)14U, (uint8_t)86U, (uint8_t)214U, (uint8_t)87U,
    (uint8_t)169U, (uint8_t)231U, (uint8_t)212U, (uint8_t)77U, (uint8_t)146U, (uint8_t)1U,
    (uint8_t)64U, (uint8_t)105U, (uint8_t)0U, (uint8_t)90U, (uint8_t)54U, (uint8_t)193U,
    (uint8_t)207U, (uint8_t)99U
  };

static uint8_t
sigver_vectors384_low31[32U] =
  {
    (uint8_t)228U, (uint8_t)180U, (uint8_t)112U, (uint8_t)198U, (uint8_t)91U, (uint8_t)44U,
    (uint8_t)4U, (uint8_t)219U, (uint8_t)6U, (uint8_t)13U, (uint8_t)113U, (uint8_t)5U,
    (uint8_t)236U, (uint8_t)105U, (uint8_t)17U, (uint8_t)88U, (uint8_t)152U, (uint8_t)99U,
    (uint8_t)211U, (uint8_t)199U, (uint8_t)247U, (uint8_t)206U, (uint8_t)72U, (uint8_t)114U,
    (uint8_t)107U, (uint8_t)163U, (uint8_t)243U, (uint8_t)105U, (uint8_t)234U, (uint8_t)52U,
    (uint8_t)103U, (uint8_t)232U
  };

static uint8_t
sigver_vectors384_low32[32U] =
  {
    (uint8_t)68U, (uint8_t)195U, (uint8_t)141U, (uint8_t)58U, (uint8_t)224U, (uint8_t)152U,
    (uint8_t)222U, (uint8_t)5U, (uint8_t)245U, (uint8_t)145U, (uint8_t)90U, (uint8_t)88U,
    (uint8_t)104U, (uint8_t)193U, (uint8_t)127U, (uint8_t)238U, (uint8_t)41U, (uint8_t)106U,
    (uint8_t)110U, (uint8_t)21U, (uint8_t)11U, (uint8_t)235U, (uint8_t)31U, (uint8_t)0U,
    (uint8_t)13U, (uint8_t)245U, (uint8_t)243U, (uint8_t)190U, (uint8_t)200U, (uint8_t)252U,
    (uint8_t)69U, (uint8_t)50U
  };

static uint8_t
sigver_vectors384_low33[32U] =
  {
    (uint8_t)201U, (uint8_t)195U, (uint8_t)71U, (uint8_t)238U, (uint8_t)87U, (uint8_t)23U,
    (uint8_t)228U, (uint8_t)199U, (uint8_t)89U, (uint8_t)221U, (uint8_t)175U, (uint8_t)9U,
    (uint8_t)232U, (uint8_t)111U, (uint8_t)78U, (uint8_t)29U, (uint8_t)178U, (uint8_t)200U,
    (uint8_t)101U, (uint8_t)133U, (uint8_t)147U, (uint8_t)23U, (uint8_t)124U, (uint8_t)253U,
    (uint8_t)164U, (uint8_t)230U, (uint8_t)81U, (uint8_t)75U, (uint8_t)94U, (uint8_t)62U,
    (uint8_t)203U, (uint8_t)135U
  };

static uint8_t
sigver_vectors384_low34[32U] =
  {
    (uint8_t)186U, (uint8_t)174U, (uint8_t)1U, (uint8_t)233U, (uint8_t)228U, (uint8_t)74U,
    (uint8_t)123U, (uint8_t)4U, (uint8_t)214U, (uint8_t)156U, (uint8_t)142U, (uint8_t)170U,
    (uint8_t)237U, (uint8_t)119U, (uint8_t)201U, (uint8_t)227U, (uint8_t)163U, (uint8_t)108U,
    (uint8_t)232U, (uint8_t)150U, (uint8_t)47U, (uint8_t)149U, (uint8_t)204U, (uint8_t)80U,
    (uint8_t)160U, (uint8_t)219U, (uint8_t)20U, (uint8_t)107U, (uint8_t)78U, (uint8_t)73U,
    (uint8_t)235U, (uint8_t)64U
  };

static uint8_t
sigver_vectors384_low35[128U] =
  {
    (uint8_t)26U, (uint8_t)110U, (uint8_t)73U, (uint8_t)163U, (uint8_t)119U, (uint8_t)160U,
    (uint8_t)142U, (uint8_t)153U, (uint8_t)35U, (uint8_t)83U, (uint8_t)214U, (uint8_t)172U,
    (uint8_t)197U, (uint8_t)87U, (uint8_t)182U, (uint8_t)135U, (uint8_t)177U, (uint8_t)182U,
    (uint8_t)154U, (uint8_t)65U, (uint8_t)216U, (uint8_t)61U, (uint8_t)67U, (uint8_t)167U,
    (uint8_t)95U, (uint8_t)173U, (uint8_t)185U, (uint8_t)123U, (uint8_t)140U, (uint8_t)146U,
    (uint8_t)140U, (uint8_t)254U, (uint8_t)186U, (uint8_t)222U, (uint8_t)186U, (uint8_t)175U,
    (uint8_t)153U, (uint8_t)234U, (uint8_t)127U, (uint8_t)177U, (uint8_t)49U, (uint8_t)72U,
    (uint8_t)128U, (uint8_t)127U, (uint8_t)86U, (uint8_t)234U, (uint8_t)23U, (uint8_t)56U,
    (uint8_t)74U, (uint8_t)121U, (uint8_t)18U, (uint8_t)229U, (uint8_t)120U, (uint8_t)230U,
    (uint8_t)43U, (uint8_t)27U, (uint8_t)0U, (uint8_t)159U, (uint8_t)239U, (uint8_t)178U,
    (uint8_t)170U, (uint8_t)252U, (uint8_t)165U, (uint8_t)172U, (uint8_t)133U, (uint8_t)83U,
    (uint8_t)148U, (uint8_t)51U, (uint8_t)97U, (uint8_t)155U, (uint8_t)40U, (uint8_t)111U,
    (uint8_t)16U, (uint8_t)100U, (uint8_t)58U, (uint8_t)86U, (uint8_t)248U, (uint8_t)223U,
    (uint8_t)164U, (uint8_t)123U, (uint8_t)164U, (uint8_t)208U, (uint8_t)28U, (uint8_t)2U,
    (uint8_t)81U, (uint8_t)13U, (uint8_t)234U, (uint8_t)236U, (uint8_t)24U, (uint8_t)2U,
    (uint8_t)158U, (uint8_t)166U, (uint8_t)185U, (uint8_t)104U, (uint8_t)32U, (uint8_t)34U,
    (uint8_t)177U, (uint8_t)57U, (uint8_t)220U, (uint8_t)183U, (uint8_t)8U, (uint8_t)20U,
    (uint8_t)22U, (uint8_t)76U, (uint8_t)76U, (uint8_t)144U, (uint8_t)236U, (uint8_t)113U,
    (uint8_t)122U, (uint8_t)217U, (uint8_t)217U, (uint8_t)37U, (uint8_t)72U, (uint8_t)83U,
    (uint8_t)152U, (uint8_t)83U, (uint8_t)28U, (uint8_t)221U, (uint8_t)89U, (uint8_t)146U,
    (uint8_t)162U, (uint8_t)82U, (uint8_t)68U, (uint8_t)152U, (uint8_t)179U, (uint8_t)55U,
    (uint8_t)249U, (uint8_t)125U
  };

static uint8_t
sigver_vectors384_low36[32U] =
  {
    (uint8_t)150U, (uint8_t)5U, (uint8_t)12U, (uint8_t)95U, (uint8_t)162U, (uint8_t)221U,
    (uint8_t)209U, (uint8_t)178U, (uint8_t)229U, (uint8_t)69U, (uint8_t)29U, (uint8_t)137U,
    (uint8_t)238U, (uint8_t)116U, (uint8_t)160U, (uint8_t)183U, (uint8_t)181U, (uint8_t)67U,
    (uint8_t)71U, (uint8_t)54U, (uint8_t)77U, (uint8_t)220U, (uint8_t)2U, (uint8_t)49U,
    (uint8_t)113U, (uint8_t)90U, (uint8_t)110U, (uint8_t)241U, (uint8_t)20U, (uint8_t)111U,
    (uint8_t)232U, (uint8_t)220U
  };

static uint8_t
sigver_vectors384_low37[32U] =
  {
    (uint8_t)224U, (uint8_t)136U, (uint8_t)138U, (uint8_t)158U, (uint8_t)120U, (uint8_t)174U,
    (uint8_t)234U, (uint8_t)135U, (uint8_t)246U, (uint8_t)225U, (uint8_t)233U, (uint8_t)0U,
    (uint8_t)43U, (uint8_t)38U, (uint8_t)81U, (uint8_t)22U, (uint8_t)159U, (uint8_t)54U,
    (uint8_t)196U, (uint8_t)238U, (uint8_t)83U, (uint8_t)1U, (uint8_t)60U, (uint8_t)252U,
    (uint8_t)140U, (uint8_t)153U, (uint8_t)18U, (uint8_t)183U, (uint8_t)253U, (uint8_t)80U,
    (uint8_t)72U, (uint8_t)88U
  };

static uint8_t
sigver_vectors384_low38[32U] =
  {
    (uint8_t)35U, (uint8_t)83U, (uint8_t)214U, (uint8_t)205U, (uint8_t)60U, (uint8_t)33U,
    (uint8_t)184U, (uint8_t)234U, (uint8_t)125U, (uint8_t)188U, (uint8_t)28U, (uint8_t)217U,
    (uint8_t)64U, (uint8_t)81U, (uint8_t)152U, (uint8_t)18U, (uint8_t)219U, (uint8_t)227U,
    (uint8_t)101U, (uint8_t)163U, (uint8_t)177U, (uint8_t)92U, (uint8_t)214U, (uint8_t)174U,
    (uint8_t)187U, (uint8_t)169U, (uint8_t)209U, (uint8_t)28U, (uint8_t)242U, (uint8_t)105U,
    (uint8_t)134U, (uint8_t)122U
  };

static uint8_t
sigver_vectors384_low39[32U] =
  {
    (uint8_t)133U, (uint8_t)245U, (uint8_t)96U, (uint8_t)39U, (uint8_t)60U, (uint8_t)217U,
    (uint8_t)232U, (uint8_t)46U, (uint8_t)104U, (uint8_t)1U, (uint8_t)228U, (uint8_t)203U,
    (uint8_t)28U, (uint8_t)140U, (uint8_t)210U, (uint8_t)156U, (uint8_t)218U, (uint8_t)195U,
    (uint8_t)74U, (uint8_t)2U, (uint8_t)13U, (uint8_t)162U, (uint8_t)17U, (uint8_t)215U,
    (uint8_t)116U, (uint8_t)83U, (uint8_t)117U, (uint8_t)107U, (uint8_t)96U, (uint8_t)75U,
    (uint8_t)143U, (uint8_t)167U
  };

static uint8_t
sigver_vectors384_low40[128U] =
  {
    (uint8_t)62U, (uint8_t)20U, (uint8_t)247U, (uint8_t)55U, (uint8_t)201U, (uint8_t)19U,
    (uint8_t)147U, (uint8_t)27U, (uint8_t)200U, (uint8_t)39U, (uint8_t)100U, (uint8_t)235U,
    (uint8_t)196U, (uint8_t)64U, (uint8_t)177U, (uint8_t)46U, (uint8_t)60U, (uint8_t)225U,
    (uint8_t)255U, (uint8_t)224U, (uint8_t)248U, (uint8_t)88U, (uint8_t)199U, (uint8_t)184U,
    (uint8_t)241U, (uint8_t)203U, (uint8_t)211U, (uint8_t)15U, (uint8_t)187U, (uint8_t)177U,
    (uint8_t)100U, (uint8_t)79U, (uint8_t)165U, (uint8_t)155U, (uint8_t)225U, (uint8_t)210U,
    (uint8_t)204U, (uint8_t)165U, (uint8_t)246U, (uint8_t)74U, (uint8_t)109U, (uint8_t)125U,
    (uint8_t)197U, (uint8_t)237U, (uint8_t)92U, (uint8_t)68U, (uint8_t)32U, (uint8_t)243U,
    (uint8_t)146U, (uint8_t)39U, (uint8_t)81U, (uint8_t)106U, (uint8_t)232U, (uint8_t)235U,
    (uint8_t)48U, (uint8_t)25U, (uint8_t)239U, (uint8_t)134U, (uint8_t)39U, (uint8_t)77U,
    (uint8_t)14U, (uint8_t)77U, (uint8_t)6U, (uint8_t)205U, (uint8_t)231U, (uint8_t)191U,
    (uint8_t)94U, (uint8_t)92U, (uint8_t)65U, (uint8_t)50U, (uint8_t)67U, (uint8_t)223U,
    (uint8_t)196U, (uint8_t)33U, (uint8_t)217U, (uint8_t)241U, (uint8_t)65U, (uint8_t)118U,
    (uint8_t)33U, (uint8_t)9U, (uint8_t)129U, (uint8_t)14U, (uint8_t)107U, (uint8_t)106U,
    (uint8_t)69U, (uint8_t)30U, (uint8_t)235U, (uint8_t)75U, (uint8_t)216U, (uint8_t)212U,
    (uint8_t)190U, (uint8_t)31U, (uint8_t)241U, (uint8_t)17U, (uint8_t)66U, (uint8_t)109U,
    (uint8_t)126U, (uint8_t)68U, (uint8_t)208U, (uint8_t)169U, (uint8_t)22U, (uint8_t)180U,
    (uint8_t)254U, (uint8_t)61U, (uint8_t)179U, (uint8_t)89U, (uint8_t)77U, (uint8_t)141U,
    (uint8_t)208U, (uint8_t)26U, (uint8_t)233U, (uint8_t)15U, (uint8_t)238U, (uint8_t)207U,
    (uint8_t)143U, (uint8_t)30U, (uint8_t)35U, (uint8_t)11U, (uint8_t)87U, (uint8_t)65U,
    (uint8_t)128U, (uint8_t)205U, (uint8_t)11U, (uint8_t)141U, (uint8_t)67U, (uint8_t)163U,
    (uint8_t)211U, (uint8_t)59U
  };

static uint8_t
sigver_vectors384_low41[32U] =
  {
    (uint8_t)12U, (uint8_t)7U, (uint8_t)187U, (uint8_t)121U, (uint8_t)244U, (uint8_t)64U,
    (uint8_t)18U, (uint8_t)41U, (uint8_t)159U, (uint8_t)191U, (uint8_t)213U, (uint8_t)160U,
    (uint8_t)243U, (uint8_t)19U, (uint8_t)151U, (uint8_t)170U, (uint8_t)247U, (uint8_t)215U,
    (uint8_t)87U, (uint8_t)248U, (uint8_t)163U, (uint8_t)132U, (uint8_t)55U, (uint8_t)64U,
    (uint8_t)124U, (uint8_t)27U, (uint8_t)9U, (uint8_t)39U, (uint8_t)28U, (uint8_t)101U,
    (uint8_t)81U, (uint8_t)160U
  };

static uint8_t
sigver_vectors384_low42[32U] =
  {
    (uint8_t)132U, (uint8_t)254U, (uint8_t)120U, (uint8_t)70U, (uint8_t)213U, (uint8_t)212U,
    (uint8_t)3U, (uint8_t)220U, (uint8_t)146U, (uint8_t)192U, (uint8_t)9U, (uint8_t)31U,
    (uint8_t)189U, (uint8_t)57U, (uint8_t)243U, (uint8_t)197U, (uint8_t)203U, (uint8_t)202U,
    (uint8_t)63U, (uint8_t)148U, (uint8_t)193U, (uint8_t)11U, (uint8_t)92U, (uint8_t)174U,
    (uint8_t)68U, (uint8_t)226U, (uint8_t)233U, (uint8_t)101U, (uint8_t)98U, (uint8_t)19U,
    (uint8_t)27U, (uint8_t)19U
  };

static uint8_t
sigver_vectors384_low43[32U] =
  {
    (uint8_t)73U, (uint8_t)233U, (uint8_t)66U, (uint8_t)95U, (uint8_t)130U, (uint8_t)208U,
    (uint8_t)168U, (uint8_t)197U, (uint8_t)3U, (uint8_t)0U, (uint8_t)156U, (uint8_t)234U,
    (uint8_t)210U, (uint8_t)78U, (uint8_t)18U, (uint8_t)173U, (uint8_t)201U, (uint8_t)212U,
    (uint8_t)138U, (uint8_t)8U, (uint8_t)89U, (uint8_t)64U, (uint8_t)148U, (uint8_t)202U,
    (uint8_t)79U, (uint8_t)109U, (uint8_t)19U, (uint8_t)173U, (uint8_t)30U, (uint8_t)60U,
    (uint8_t)87U, (uint8_t)29U
  };

static uint8_t
sigver_vectors384_low44[32U] =
  {
    (uint8_t)31U, (uint8_t)27U, (uint8_t)112U, (uint8_t)170U, (uint8_t)163U, (uint8_t)10U,
    (uint8_t)143U, (uint8_t)246U, (uint8_t)57U, (uint8_t)170U, (uint8_t)9U, (uint8_t)53U,
    (uint8_t)148U, (uint8_t)78U, (uint8_t)155U, (uint8_t)136U, (uint8_t)50U, (uint8_t)106U,
    (uint8_t)33U, (uint8_t)58U, (uint8_t)184U, (uint8_t)252U, (uint8_t)229U, (uint8_t)25U,
    (uint8_t)76U, (uint8_t)26U, (uint8_t)157U, (uint8_t)236U, (uint8_t)7U, (uint8_t)14U,
    (uint8_t)180U, (uint8_t)51U
  };

static uint8_t
sigver_vectors384_low45[128U] =
  {
    (uint8_t)64U, (uint8_t)0U, (uint8_t)16U, (uint8_t)97U, (uint8_t)39U, (uint8_t)167U,
    (uint8_t)39U, (uint8_t)70U, (uint8_t)219U, (uint8_t)119U, (uint8_t)149U, (uint8_t)124U,
    (uint8_t)188U, (uint8_t)107U, (uint8_t)253U, (uint8_t)132U, (uint8_t)174U, (uint8_t)61U,
    (uint8_t)29U, (uint8_t)99U, (uint8_t)184U, (uint8_t)25U, (uint8_t)0U, (uint8_t)135U,
    (uint8_t)99U, (uint8_t)126U, (uint8_t)147U, (uint8_t)104U, (uint8_t)152U, (uint8_t)65U,
    (uint8_t)51U, (uint8_t)30U, (uint8_t)42U, (uint8_t)220U, (uint8_t)25U, (uint8_t)48U,
    (uint8_t)214U, (uint8_t)223U, (uint8_t)67U, (uint8_t)2U, (uint8_t)147U, (uint8_t)95U,
    (uint8_t)69U, (uint8_t)32U, (uint8_t)187U, (uint8_t)238U, (uint8_t)81U, (uint8_t)53U,
    (uint8_t)5U, (uint8_t)205U, (uint8_t)207U, (uint8_t)202U, (uint8_t)153U, (uint8_t)235U,
    (uint8_t)198U, (uint8_t)248U, (uint8_t)58U, (uint8_t)247U, (uint8_t)178U, (uint8_t)59U,
    (uint8_t)15U, (uint8_t)46U, (uint8_t)127U, (uint8_t)125U, (uint8_t)239U, (uint8_t)186U,
    (uint8_t)97U, (uint8_t)64U, (uint8_t)34U, (uint8_t)206U, (uint8_t)234U, (uint8_t)233U,
    (uint8_t)198U, (uint8_t)136U, (uint8_t)110U, (uint8_t)139U, (uint8_t)19U, (uint8_t)247U,
    (uint8_t)234U, (uint8_t)37U, (uint8_t)58U, (uint8_t)48U, (uint8_t)122U, (uint8_t)195U,
    (uint8_t)1U, (uint8_t)243U, (uint8_t)83U, (uint8_t)103U, (uint8_t)32U, (uint8_t)203U,
    (uint8_t)227U, (uint8_t)222U, (uint8_t)130U, (uint8_t)186U, (uint8_t)62U, (uint8_t)152U,
    (uint8_t)49U, (uint8_t)3U, (uint8_t)97U, (uint8_t)182U, (uint8_t)24U, (uint8_t)1U,
    (uint8_t)168U, (uint8_t)48U, (uint8_t)79U, (uint8_t)252U, (uint8_t)145U, (uint8_t)255U,
    (uint8_t)119U, (uint8_t)73U, (uint8_t)72U, (uint8_t)227U, (uint8_t)49U, (uint8_t)118U,
    (uint8_t)221U, (uint8_t)205U, (uint8_t)223U, (uint8_t)27U, (uint8_t)118U, (uint8_t)67U,
    (uint8_t)123U, (uint8_t)63U, (uint8_t)2U, (uint8_t)201U, (uint8_t)16U, (uint8_t)87U,
    (uint8_t)141U, (uint8_t)70U
  };

static uint8_t
sigver_vectors384_low46[32U] =
  {
    (uint8_t)113U, (uint8_t)219U, (uint8_t)29U, (uint8_t)225U, (uint8_t)161U, (uint8_t)243U,
    (uint8_t)143U, (uint8_t)53U, (uint8_t)108U, (uint8_t)145U, (uint8_t)254U, (uint8_t)175U,
    (uint8_t)245U, (uint8_t)207U, (uint8_t)227U, (uint8_t)149U, (uint8_t)209U, (uint8_t)165U,
    (uint8_t)185U, (uint8_t)210U, (uint8_t)60U, (uint8_t)246U, (uint8_t)170U, (uint8_t)25U,
    (uint8_t)243U, (uint8_t)138U, (uint8_t)224U, (uint8_t)188U, (uint8_t)201U, (uint8_t)10U,
    (uint8_t)72U, (uint8_t)109U
  };

static uint8_t
sigver_vectors384_low47[32U] =
  {
    (uint8_t)236U, (uint8_t)221U, (uint8_t)111U, (uint8_t)251U, (uint8_t)23U, (uint8_t)74U,
    (uint8_t)80U, (uint8_t)241U, (uint8_t)204U, (uint8_t)121U, (uint8_t)41U, (uint8_t)133U,
    (uint8_t)194U, (uint8_t)249U, (uint8_t)96U, (uint8_t)140U, (uint8_t)57U, (uint8_t)156U,
    (uint8_t)152U, (uint8_t)184U, (uint8_t)166U, (uint8_t)74U, (uint8_t)105U, (uint8_t)210U,
    (uint8_t)181U, (uint8_t)183U, (uint8_t)205U, (uint8_t)217U, (uint8_t)36U, (uint8_t)31U,
    (uint8_t)103U, (uint8_t)226U
  };

static uint8_t
sigver_vectors384_low48[32U] =
  {
    (uint8_t)176U, (uint8_t)68U, (uint8_t)59U, (uint8_t)51U, (uint8_t)166U, (uint8_t)242U,
    (uint8_t)73U, (uint8_t)71U, (uint8_t)13U, (uint8_t)47U, (uint8_t)148U, (uint8_t)54U,
    (uint8_t)117U, (uint8_t)0U, (uint8_t)157U, (uint8_t)33U, (uint8_t)185U, (uint8_t)204U,
    (uint8_t)190U, (uint8_t)173U, (uint8_t)21U, (uint8_t)37U, (uint8_t)174U, (uint8_t)87U,
    (uint8_t)129U, (uint8_t)93U, (uint8_t)248U, (uint8_t)107U, (uint8_t)178U, (uint8_t)4U,
    (uint8_t)112U, (uint8_t)191U
  };

static uint8_t
sigver_vectors384_low49[32U] =
  {
    (uint8_t)49U, (uint8_t)109U, (uint8_t)190U, (uint8_t)226U, (uint8_t)125U, (uint8_t)153U,
    (uint8_t)142U, (uint8_t)9U, (uint8_t)18U, (uint8_t)133U, (uint8_t)57U, (uint8_t)194U,
    (uint8_t)105U, (uint8_t)226U, (uint8_t)151U, (uint8_t)172U, (uint8_t)143U, (uint8_t)52U,
    (uint8_t)185U, (uint8_t)239U, (uint8_t)130U, (uint8_t)73U, (uint8_t)160U, (uint8_t)97U,
    (uint8_t)145U, (uint8_t)104U, (uint8_t)195U, (uint8_t)73U, (uint8_t)92U, (uint8_t)92U,
    (uint8_t)17U, (uint8_t)152U
  };

static uint8_t
sigver_vectors384_low50[128U] =
  {
    (uint8_t)180U, (uint8_t)46U, (uint8_t)84U, (uint8_t)125U, (uint8_t)14U, (uint8_t)125U,
    (uint8_t)221U, (uint8_t)94U, (uint8_t)16U, (uint8_t)105U, (uint8_t)187U, (uint8_t)45U,
    (uint8_t)21U, (uint8_t)138U, (uint8_t)91U, (uint8_t)77U, (uint8_t)93U, (uint8_t)156U,
    (uint8_t)67U, (uint8_t)16U, (uint8_t)148U, (uint8_t)42U, (uint8_t)27U, (uint8_t)253U,
    (uint8_t)9U, (uint8_t)73U, (uint8_t)3U, (uint8_t)17U, (uint8_t)166U, (uint8_t)230U,
    (uint8_t)132U, (uint8_t)189U, (uint8_t)60U, (uint8_t)41U, (uint8_t)176U, (uint8_t)220U,
    (uint8_t)239U, (uint8_t)134U, (uint8_t)169U, (uint8_t)120U, (uint8_t)139U, (uint8_t)75U,
    (uint8_t)38U, (uint8_t)254U, (uint8_t)215U, (uint8_t)134U, (uint8_t)63U, (uint8_t)61U,
    (uint8_t)94U, (uint8_t)84U, (uint8_t)57U, (uint8_t)121U, (uint8_t)107U, (uint8_t)91U,
    (uint8_t)95U, (uint8_t)254U, (uint8_t)122U, (uint8_t)162U, (uint8_t)84U, (uint8_t)93U,
    (uint8_t)15U, (uint8_t)81U, (uint8_t)138U, (uint8_t)208U, (uint8_t)32U, (uint8_t)104U,
    (uint8_t)156U, (uint8_t)162U, (uint8_t)18U, (uint8_t)48U, (uint8_t)243U, (uint8_t)165U,
    (uint8_t)158U, (uint8_t)127U, (uint8_t)140U, (uint8_t)202U, (uint8_t)70U, (uint8_t)95U,
    (uint8_t)226U, (uint8_t)29U, (uint8_t)245U, (uint8_t)17U, (uint8_t)231U, (uint8_t)141U,
    (uint8_t)33U, (uint8_t)95U, (uint8_t)168U, (uint8_t)5U, (uint8_t)245U, (uint8_t)240U,
    (uint8_t)248U, (uint8_t)137U, (uint8_t)56U, (uint8_t)233U, (uint8_t)209U, (uint8_t)152U,
    (uint8_t)81U, (uint8_t)94U, (uint8_t)107U, (uint8_t)156U, (uint8_t)129U, (uint8_t)153U,
    (uint8_t)48U, (uint8_t)117U, (uint8_t)92U, (uint8_t)108U, (uint8_t)106U, (uint8_t)234U,
    (uint8_t)81U, (uint8_t)20U, (uint8_t)205U, (uint8_t)41U, (uint8_t)4U, (uint8_t)96U,
    (uint8_t)114U, (uint8_t)67U, (uint8_t)5U, (uint8_t)28U, (uint8_t)9U, (uint8_t)221U,
    (uint8_t)122U, (uint8_t)20U, (uint8_t)119U, (uint8_t)86U, (uint8_t)203U, (uint8_t)194U,
    (uint8_t)4U, (uint8_t)165U
  };

static uint8_t
sigver_vectors384_low51[32U] =
  {
    (uint8_t)130U, (uint8_t)25U, (uint8_t)178U, (uint8_t)37U, (uint8_t)170U, (uint8_t)21U,
    (uint8_t)71U, (uint8_t)34U, (uint8_t)98U, (uint8_t)198U, (uint8_t)72U, (uint8_t)202U,
    (uint8_t)200U, (uint8_t)222U, (uint8_t)154U, (uint8_t)173U, (uint8_t)65U, (uint8_t)115U,
    (uint8_t)209U, (uint8_t)122U, (uint8_t)35U, (uint8_t)27U, (uint8_t)162U, (uint8_t)67U,
    (uint8_t)82U, (uint8_t)165U, (uint8_t)161U, (uint8_t)196U, (uint8_t)238U, (uint8_t)167U,
    (uint8_t)15U, (uint8_t)173U
  };

static uint8_t
sigver_vectors384_low52[32U] =
  {
    (uint8_t)15U, (uint8_t)238U, (uint8_t)43U, (uint8_t)8U, (uint8_t)173U, (uint8_t)57U,
    (uint8_t)251U, (uint8_t)240U, (uint8_t)219U, (uint8_t)0U, (uint8_t)22U, (uint8_t)239U,
    (uint8_t)40U, (uint8_t)150U, (uint8_t)202U, (uint8_t)153U, (uint8_t)173U, (uint8_t)192U,
    (uint8_t)126U, (uint8_t)252U, (uint8_t)140U, (uint8_t)65U, (uint8_t)95U, (uint8_t)100U,
    (uint8_t)15U, (uint8_t)55U, (uint8_t)32U, (uint8_t)73U, (uint8_t)139U, (uint8_t)226U,
    (uint8_t)96U, (uint8_t)55U
  };

static uint8_t
sigver_vectors384_low53[32U] =
  {
    (uint8_t)19U, (uint8_t)79U, (uint8_t)182U, (uint8_t)137U, (uint8_t)16U, (uint8_t)26U,
    (uint8_t)170U, (uint8_t)211U, (uint8_t)149U, (uint8_t)77U, (uint8_t)226U, (uint8_t)129U,
    (uint8_t)157U, (uint8_t)159U, (uint8_t)189U, (uint8_t)18U, (uint8_t)7U, (uint8_t)47U,
    (uint8_t)226U, (uint8_t)188U, (uint8_t)54U, (uint8_t)244U, (uint8_t)150U, (uint8_t)187U,
    (uint8_t)240U, (uint8_t)209U, (uint8_t)63U, (uint8_t)167U, (uint8_t)33U, (uint8_t)20U,
    (uint8_t)171U, (uint8_t)150U
  };

static uint8_t
sigver_vectors384_low54[32U] =
  {
    (uint8_t)230U, (uint8_t)92U, (uint8_t)35U, (uint8_t)43U, (uint8_t)217U, (uint8_t)21U,
    (uint8_t)181U, (uint8_t)158U, (uint8_t)8U, (uint8_t)126U, (uint8_t)127U, (uint8_t)213U,
    (uint8_t)236U, (uint8_t)144U, (uint8_t)191U, (uint8_t)99U, (uint8_t)108U, (uint8_t)250U,
    (uint8_t)128U, (uint8_t)82U, (uint8_t)99U, (uint8_t)69U, (uint8_t)199U, (uint8_t)154U,
    (uint8_t)10U, (uint8_t)223U, (uint8_t)215U, (uint8_t)80U, (uint8_t)3U, (uint8_t)4U,
    (uint8_t)93U, (uint8_t)111U
  };

static uint8_t
sigver_vectors384_low55[128U] =
  {
    (uint8_t)170U, (uint8_t)86U, (uint8_t)50U, (uint8_t)35U, (uint8_t)167U, (uint8_t)213U,
    (uint8_t)32U, (uint8_t)31U, (uint8_t)235U, (uint8_t)223U, (uint8_t)19U, (uint8_t)202U,
    (uint8_t)184U, (uint8_t)10U, (uint8_t)3U, (uint8_t)220U, (uint8_t)230U, (uint8_t)7U,
    (uint8_t)124U, (uint8_t)38U, (uint8_t)231U, (uint8_t)81U, (uint8_t)188U, (uint8_t)152U,
    (uint8_t)169U, (uint8_t)65U, (uint8_t)25U, (uint8_t)106U, (uint8_t)40U, (uint8_t)132U,
    (uint8_t)138U, (uint8_t)188U, (uint8_t)73U, (uint8_t)94U, (uint8_t)3U, (uint8_t)36U,
    (uint8_t)1U, (uint8_t)60U, (uint8_t)154U, (uint8_t)32U, (uint8_t)148U, (uint8_t)251U,
    (uint8_t)21U, (uint8_t)220U, (uint8_t)101U, (uint8_t)209U, (uint8_t)0U, (uint8_t)195U,
    (uint8_t)232U, (uint8_t)161U, (uint8_t)54U, (uint8_t)165U, (uint8_t)44U, (uint8_t)23U,
    (uint8_t)128U, (uint8_t)179U, (uint8_t)149U, (uint8_t)244U, (uint8_t)37U, (uint8_t)136U,
    (uint8_t)144U, (uint8_t)11U, (uint8_t)100U, (uint8_t)27U, (uint8_t)109U, (uint8_t)67U,
    (uint8_t)97U, (uint8_t)67U, (uint8_t)46U, (uint8_t)33U, (uint8_t)115U, (uint8_t)25U,
    (uint8_t)90U, (uint8_t)47U, (uint8_t)96U, (uint8_t)24U, (uint8_t)159U, (uint8_t)63U,
    (uint8_t)204U, (uint8_t)133U, (uint8_t)244U, (uint8_t)233U, (uint8_t)101U, (uint8_t)156U,
    (uint8_t)174U, (uint8_t)82U, (uint8_t)87U, (uint8_t)111U, (uint8_t)32U, (uint8_t)209U,
    (uint8_t)133U, (uint8_t)45U, (uint8_t)67U, (uint8_t)194U, (uint8_t)180U, (uint8_t)0U,
    (uint8_t)222U, (uint8_t)234U, (uint8_t)49U, (uint8_t)68U, (uint8_t)200U, (uint8_t)232U,
    (uint8_t)112U, (uint8_t)225U, (uint8_t)144U, (uint8_t)109U, (uint8_t)103U, (uint8_t)116U,
    (uint8_t)37U, (uint8_t)216U, (uint8_t)200U, (uint8_t)80U, (uint8_t)55U, (uint8_t)199U,
    (uint8_t)164U, (uint8_t)42U, (uint8_t)157U, (uint8_t)36U, (uint8_t)155U, (uint8_t)45U,
    (uint8_t)164U, (uint8_t)181U, (uint8_t)22U, (uint8_t)224U, (uint8_t)68U, (uint8_t)118U,
    (uint8_t)189U, (uint8_t)69U
  };

static uint8_t
sigver_vectors384_low56[32U] =
  {
    (uint8_t)201U, (uint8_t)52U, (uint8_t)25U, (uint8_t)93U, (uint8_t)227U, (uint8_t)59U,
    (uint8_t)96U, (uint8_t)207U, (uint8_t)0U, (uint8_t)70U, (uint8_t)31U, (uint8_t)195U,
    (uint8_t)196U, (uint8_t)93U, (uint8_t)173U, (uint8_t)6U, (uint8_t)142U, (uint8_t)159U,
    (uint8_t)95U, (uint8_t)122U, (uint8_t)245U, (uint8_t)199U, (uint8_t)250U, (uint8_t)120U,
    (uint8_t)89U, (uint8_t)30U, (uint8_t)149U, (uint8_t)174U, (uint8_t)176U, (uint8_t)78U,
    (uint8_t)38U, (uint8_t)23U
  };

static uint8_t
sigver_vectors384_low57[32U] =
  {
    (uint8_t)181U, (uint8_t)136U, (uint8_t)221U, (uint8_t)95U, (uint8_t)153U, (uint8_t)101U,
    (uint8_t)253U, (uint8_t)170U, (uint8_t)82U, (uint8_t)59U, (uint8_t)71U, (uint8_t)92U,
    (uint8_t)40U, (uint8_t)18U, (uint8_t)194U, (uint8_t)81U, (uint8_t)188U, (uint8_t)105U,
    (uint8_t)115U, (uint8_t)226U, (uint8_t)223U, (uint8_t)33U, (uint8_t)217U, (uint8_t)190U,
    (uint8_t)170U, (uint8_t)206U, (uint8_t)151U, (uint8_t)106U, (uint8_t)191U, (uint8_t)87U,
    (uint8_t)40U, (uint8_t)203U
  };

static uint8_t
sigver_vectors384_low58[32U] =
  {
    (uint8_t)113U, (uint8_t)243U, (uint8_t)2U, (uint8_t)68U, (uint8_t)14U, (uint8_t)180U,
    (uint8_t)237U, (uint8_t)42U, (uint8_t)147U, (uint8_t)155U, (uint8_t)105U, (uint8_t)227U,
    (uint8_t)62U, (uint8_t)144U, (uint8_t)94U, (uint8_t)111U, (uint8_t)220U, (uint8_t)84U,
    (uint8_t)92U, (uint8_t)116U, (uint8_t)52U, (uint8_t)88U, (uint8_t)211U, (uint8_t)143U,
    (uint8_t)126U, (uint8_t)26U, (uint8_t)29U, (uint8_t)69U, (uint8_t)110U, (uint8_t)53U,
    (uint8_t)243U, (uint8_t)137U
  };

static uint8_t
sigver_vectors384_low59[32U] =
  {
    (uint8_t)84U, (uint8_t)234U, (uint8_t)160U, (uint8_t)235U, (uint8_t)156U, (uint8_t)215U,
    (uint8_t)80U, (uint8_t)59U, (uint8_t)25U, (uint8_t)169U, (uint8_t)101U, (uint8_t)143U,
    (uint8_t)10U, (uint8_t)4U, (uint8_t)149U, (uint8_t)93U, (uint8_t)159U, (uint8_t)10U,
    (uint8_t)178U, (uint8_t)14U, (uint8_t)188U, (uint8_t)138U, (uint8_t)8U, (uint8_t)119U,
    (uint8_t)227U, (uint8_t)60U, (uint8_t)137U, (uint8_t)238U, (uint8_t)136U, (uint8_t)173U,
    (uint8_t)6U, (uint8_t)143U
  };

static uint8_t
sigver_vectors384_low60[128U] =
  {
    (uint8_t)152U, (uint8_t)228U, (uint8_t)186U, (uint8_t)191U, (uint8_t)137U, (uint8_t)15U,
    (uint8_t)82U, (uint8_t)229U, (uint8_t)160U, (uint8_t)75U, (uint8_t)210U, (uint8_t)167U,
    (uint8_t)215U, (uint8_t)155U, (uint8_t)240U, (uint8_t)174U, (uint8_t)154U, (uint8_t)113U,
    (uint8_t)150U, (uint8_t)120U, (uint8_t)71U, (uint8_t)52U, (uint8_t)125U, (uint8_t)135U,
    (uint8_t)242U, (uint8_t)159U, (uint8_t)179U, (uint8_t)153U, (uint8_t)116U, (uint8_t)84U,
    (uint8_t)199U, (uint8_t)60U, (uint8_t)121U, (uint8_t)121U, (uint8_t)209U, (uint8_t)91U,
    (uint8_t)92U, (uint8_t)79U, (uint8_t)66U, (uint8_t)5U, (uint8_t)236U, (uint8_t)61U,
    (uint8_t)231U, (uint8_t)131U, (uint8_t)93U, (uint8_t)24U, (uint8_t)133U, (uint8_t)251U,
    (uint8_t)122U, (uint8_t)188U, (uint8_t)248U, (uint8_t)220U, (uint8_t)222U, (uint8_t)148U,
    (uint8_t)186U, (uint8_t)240U, (uint8_t)139U, (uint8_t)29U, (uint8_t)105U, (uint8_t)26U,
    (uint8_t)12U, (uint8_t)116U, (uint8_t)132U, (uint8_t)83U, (uint8_t)23U, (uint8_t)40U,
    (uint8_t)101U, (uint8_t)64U, (uint8_t)232U, (uint8_t)201U, (uint8_t)211U, (uint8_t)120U,
    (uint8_t)254U, (uint8_t)250U, (uint8_t)164U, (uint8_t)118U, (uint8_t)44U, (uint8_t)48U,
    (uint8_t)36U, (uint8_t)146U, (uint8_t)245U, (uint8_t)16U, (uint8_t)35U, (uint8_t)192U,
    (uint8_t)215U, (uint8_t)173U, (uint8_t)187U, (uint8_t)28U, (uint8_t)201U, (uint8_t)11U,
    (uint8_t)123U, (uint8_t)3U, (uint8_t)53U, (uint8_t)241U, (uint8_t)18U, (uint8_t)3U,
    (uint8_t)102U, (uint8_t)78U, (uint8_t)113U, (uint8_t)254U, (uint8_t)166U, (uint8_t)33U,
    (uint8_t)188U, (uint8_t)47U, (uint8_t)89U, (uint8_t)210U, (uint8_t)219U, (uint8_t)208U,
    (uint8_t)238U, (uint8_t)118U, (uint8_t)214U, (uint8_t)89U, (uint8_t)126U, (uint8_t)199U,
    (uint8_t)85U, (uint8_t)16U, (uint8_t)222U, (uint8_t)89U, (uint8_t)182U, (uint8_t)210U,
    (uint8_t)95U, (uint8_t)166U, (uint8_t)117U, (uint8_t)10U, (uint8_t)113U, (uint8_t)197U,
    (uint8_t)148U, (uint8_t)53U
  };

static uint8_t
sigver_vectors384_low61[32U] =
  {
    (uint8_t)158U, (uint8_t)26U, (uint8_t)220U, (uint8_t)212U, (uint8_t)142U, (uint8_t)46U,
    (uint8_t)63U, (uint8_t)14U, (uint8_t)76U, (uint8_t)33U, (uint8_t)53U, (uint8_t)1U,
    (uint8_t)128U, (uint8_t)130U, (uint8_t)40U, (uint8_t)229U, (uint8_t)135U, (uint8_t)196U,
    (uint8_t)5U, (uint8_t)88U, (uint8_t)245U, (uint8_t)43U, (uint8_t)181U, (uint8_t)77U,
    (uint8_t)219U, (uint8_t)182U, (uint8_t)16U, (uint8_t)45U, (uint8_t)64U, (uint8_t)72U,
    (uint8_t)234U, (uint8_t)146U
  };

static uint8_t
sigver_vectors384_low62[32U] =
  {
    (uint8_t)52U, (uint8_t)239U, (uint8_t)249U, (uint8_t)135U, (uint8_t)4U, (uint8_t)121U,
    (uint8_t)9U, (uint8_t)56U, (uint8_t)231U, (uint8_t)224U, (uint8_t)189U, (uint8_t)248U,
    (uint8_t)122U, (uint8_t)227U, (uint8_t)152U, (uint8_t)7U, (uint8_t)166U, (uint8_t)183U,
    (uint8_t)125U, (uint8_t)253U, (uint8_t)201U, (uint8_t)236U, (uint8_t)223U, (uint8_t)230U,
    (uint8_t)221U, (uint8_t)15U, (uint8_t)36U, (uint8_t)26U, (uint8_t)186U, (uint8_t)225U,
    (uint8_t)174U, (uint8_t)178U
  };

static uint8_t
sigver_vectors384_low63[32U] =
  {
    (uint8_t)206U, (uint8_t)79U, (uint8_t)13U, (uint8_t)116U, (uint8_t)128U, (uint8_t)82U,
    (uint8_t)44U, (uint8_t)141U, (uint8_t)209U, (uint8_t)176U, (uint8_t)45U, (uint8_t)208U,
    (uint8_t)235U, (uint8_t)56U, (uint8_t)47U, (uint8_t)34U, (uint8_t)64U, (uint8_t)102U,
    (uint8_t)66U, (uint8_t)240U, (uint8_t)56U, (uint8_t)193U, (uint8_t)237U, (uint8_t)233U,
    (uint8_t)65U, (uint8_t)24U, (uint8_t)131U, (uint8_t)215U, (uint8_t)43U, (uint8_t)62U,
    (uint8_t)126U, (uint8_t)208U
  };

static uint8_t
sigver_vectors384_low64[32U] =
  {
    (uint8_t)133U, (uint8_t)70U, (uint8_t)225U, (uint8_t)238U, (uint8_t)59U, (uint8_t)119U,
    (uint8_t)249U, (uint8_t)146U, (uint8_t)124U, (uint8_t)218U, (uint8_t)204U, (uint8_t)188U,
    (uint8_t)47U, (uint8_t)28U, (uint8_t)241U, (uint8_t)157U, (uint8_t)107U, (uint8_t)85U,
    (uint8_t)118U, (uint8_t)176U, (uint8_t)247U, (uint8_t)56U, (uint8_t)187U, (uint8_t)27U,
    (uint8_t)134U, (uint8_t)160U, (uint8_t)198U, (uint8_t)107U, (uint8_t)57U, (uint8_t)202U,
    (uint8_t)86U, (uint8_t)251U
  };

static uint8_t
sigver_vectors384_low65[128U] =
  {
    (uint8_t)187U, (uint8_t)107U, (uint8_t)3U, (uint8_t)173U, (uint8_t)96U, (uint8_t)214U,
    (uint8_t)221U, (uint8_t)191U, (uint8_t)12U, (uint8_t)77U, (uint8_t)23U, (uint8_t)36U,
    (uint8_t)98U, (uint8_t)6U, (uint8_t)230U, (uint8_t)28U, (uint8_t)136U, (uint8_t)111U,
    (uint8_t)145U, (uint8_t)109U, (uint8_t)37U, (uint8_t)43U, (uint8_t)180U, (uint8_t)96U,
    (uint8_t)129U, (uint8_t)73U, (uint8_t)218U, (uint8_t)73U, (uint8_t)206U, (uint8_t)249U,
    (uint8_t)3U, (uint8_t)52U, (uint8_t)132U, (uint8_t)8U, (uint8_t)14U, (uint8_t)134U,
    (uint8_t)31U, (uint8_t)145U, (uint8_t)187U, (uint8_t)36U, (uint8_t)0U, (uint8_t)186U,
    (uint8_t)160U, (uint8_t)205U, (uint8_t)108U, (uint8_t)93U, (uint8_t)144U, (uint8_t)194U,
    (uint8_t)242U, (uint8_t)117U, (uint8_t)226U, (uint8_t)250U, (uint8_t)188U, (uint8_t)18U,
    (uint8_t)216U, (uint8_t)56U, (uint8_t)71U, (uint8_t)247U, (uint8_t)161U, (uint8_t)195U,
    (uint8_t)255U, (uint8_t)14U, (uint8_t)180U, (uint8_t)12U, (uint8_t)138U, (uint8_t)61U,
    (uint8_t)216U, (uint8_t)61U, (uint8_t)7U, (uint8_t)209U, (uint8_t)148U, (uint8_t)186U,
    (uint8_t)55U, (uint8_t)151U, (uint8_t)210U, (uint8_t)114U, (uint8_t)56U, (uint8_t)65U,
    (uint8_t)90U, (uint8_t)47U, (uint8_t)53U, (uint8_t)141U, (uint8_t)114U, (uint8_t)146U,
    (uint8_t)161U, (uint8_t)153U, (uint8_t)26U, (uint8_t)246U, (uint8_t)135U, (uint8_t)188U,
    (uint8_t)185U, (uint8_t)119U, (uint8_t)72U, (uint8_t)105U, (uint8_t)128U, (uint8_t)249U,
    (uint8_t)19U, (uint8_t)139U, (uint8_t)49U, (uint8_t)64U, (uint8_t)50U, (uint8_t)20U,
    (uint8_t)133U, (uint8_t)99U, (uint8_t)138U, (uint8_t)199U, (uint8_t)189U, (uint8_t)34U,
    (uint8_t)236U, (uint8_t)218U, (uint8_t)0U, (uint8_t)255U, (uint8_t)229U, (uint8_t)0U,
    (uint8_t)155U, (uint8_t)131U, (uint8_t)185U, (uint8_t)3U, (uint8_t)151U, (uint8_t)239U,
    (uint8_t)242U, (uint8_t)78U, (uint8_t)207U, (uint8_t)34U, (uint8_t)197U, (uint8_t)73U,
    (uint8_t)93U, (uint8_t)103U
  };

static uint8_t
sigver_vectors384_low66[32U] =
  {
    (uint8_t)147U, (uint8_t)237U, (uint8_t)190U, (uint8_t)203U, (uint8_t)11U, (uint8_t)1U,
    (uint8_t)156U, (uint8_t)44U, (uint8_t)192U, (uint8_t)48U, (uint8_t)96U, (uint8_t)245U,
    (uint8_t)76U, (uint8_t)180U, (uint8_t)144U, (uint8_t)75U, (uint8_t)146U, (uint8_t)15U,
    (uint8_t)219U, (uint8_t)52U, (uint8_t)235U, (uint8_t)131U, (uint8_t)186U, (uint8_t)221U,
    (uint8_t)117U, (uint8_t)43U, (uint8_t)233U, (uint8_t)68U, (uint8_t)48U, (uint8_t)54U,
    (uint8_t)174U, (uint8_t)19U
  };

static uint8_t
sigver_vectors384_low67[32U] =
  {
    (uint8_t)180U, (uint8_t)148U, (uint8_t)233U, (uint8_t)41U, (uint8_t)94U, (uint8_t)8U,
    (uint8_t)10U, (uint8_t)144U, (uint8_t)128U, (uint8_t)254U, (uint8_t)126U, (uint8_t)115U,
    (uint8_t)36U, (uint8_t)155U, (uint8_t)58U, (uint8_t)89U, (uint8_t)4U, (uint8_t)170U,
    (uint8_t)132U, (uint8_t)225U, (uint8_t)192U, (uint8_t)40U, (uint8_t)18U, (uint8_t)30U,
    (uint8_t)236U, (uint8_t)211U, (uint8_t)226U, (uint8_t)207U, (uint8_t)26U, (uint8_t)85U,
    (uint8_t)245U, (uint8_t)152U
  };

static uint8_t
sigver_vectors384_low68[32U] =
  {
    (uint8_t)238U, (uint8_t)194U, (uint8_t)152U, (uint8_t)109U, (uint8_t)71U, (uint8_t)183U,
    (uint8_t)25U, (uint8_t)149U, (uint8_t)137U, (uint8_t)43U, (uint8_t)9U, (uint8_t)21U,
    (uint8_t)211U, (uint8_t)213U, (uint8_t)190U, (uint8_t)204U, (uint8_t)77U, (uint8_t)203U,
    (uint8_t)42U, (uint8_t)181U, (uint8_t)82U, (uint8_t)6U, (uint8_t)215U, (uint8_t)114U,
    (uint8_t)224U, (uint8_t)24U, (uint8_t)149U, (uint8_t)65U, (uint8_t)178U, (uint8_t)24U,
    (uint8_t)77U, (uint8_t)223U
  };

static uint8_t
sigver_vectors384_low69[32U] =
  {
    (uint8_t)138U, (uint8_t)108U, (uint8_t)30U, (uint8_t)222U, (uint8_t)182U, (uint8_t)69U,
    (uint8_t)38U, (uint8_t)39U, (uint8_t)173U, (uint8_t)39U, (uint8_t)200U, (uint8_t)49U,
    (uint8_t)149U, (uint8_t)153U, (uint8_t)197U, (uint8_t)74U, (uint8_t)196U, (uint8_t)76U,
    (uint8_t)221U, (uint8_t)131U, (uint8_t)30U, (uint8_t)166U, (uint8_t)111U, (uint8_t)19U,
    (uint8_t)244U, (uint8_t)157U, (uint8_t)144U, (uint8_t)175U, (uint8_t)254U, (uint8_t)106U,
    (uint8_t)212U, (uint8_t)91U
  };

static uint8_t
sigver_vectors384_low70[128U] =
  {
    (uint8_t)51U, (uint8_t)165U, (uint8_t)212U, (uint8_t)137U, (uint8_t)246U, (uint8_t)113U,
    (uint8_t)243U, (uint8_t)150U, (uint8_t)199U, (uint8_t)118U, (uint8_t)188U, (uint8_t)26U,
    (uint8_t)207U, (uint8_t)25U, (uint8_t)59U, (uint8_t)201U, (uint8_t)167U, (uint8_t)67U,
    (uint8_t)6U, (uint8_t)244U, (uint8_t)105U, (uint8_t)45U, (uint8_t)216U, (uint8_t)224U,
    (uint8_t)91U, (uint8_t)205U, (uint8_t)254U, (uint8_t)40U, (uint8_t)253U, (uint8_t)239U,
    (uint8_t)189U, (uint8_t)92U, (uint8_t)9U, (uint8_t)184U, (uint8_t)49U, (uint8_t)194U,
    (uint8_t)4U, (uint8_t)161U, (uint8_t)222U, (uint8_t)200U, (uint8_t)29U, (uint8_t)142U,
    (uint8_t)53U, (uint8_t)65U, (uint8_t)243U, (uint8_t)36U, (uint8_t)247U, (uint8_t)180U,
    (uint8_t)116U, (uint8_t)214U, (uint8_t)146U, (uint8_t)120U, (uint8_t)144U, (uint8_t)19U,
    (uint8_t)187U, (uint8_t)30U, (uint8_t)202U, (uint8_t)6U, (uint8_t)111U, (uint8_t)130U,
    (uint8_t)251U, (uint8_t)243U, (uint8_t)241U, (uint8_t)207U, (uint8_t)59U, (uint8_t)166U,
    (uint8_t)78U, (uint8_t)157U, (uint8_t)137U, (uint8_t)99U, (uint8_t)233U, (uint8_t)236U,
    (uint8_t)193U, (uint8_t)128U, (uint8_t)185U, (uint8_t)37U, (uint8_t)25U, (uint8_t)25U,
    (uint8_t)226U, (uint8_t)232U, (uint8_t)161U, (uint8_t)171U, (uint8_t)5U, (uint8_t)132U,
    (uint8_t)122U, (uint8_t)13U, (uint8_t)118U, (uint8_t)255U, (uint8_t)103U, (uint8_t)164U,
    (uint8_t)124U, (uint8_t)0U, (uint8_t)225U, (uint8_t)112U, (uint8_t)227U, (uint8_t)142U,
    (uint8_t)91U, (uint8_t)49U, (uint8_t)154U, (uint8_t)86U, (uint8_t)245U, (uint8_t)156U,
    (uint8_t)197U, (uint8_t)16U, (uint8_t)56U, (uint8_t)249U, (uint8_t)9U, (uint8_t)97U,
    (uint8_t)234U, (uint8_t)39U, (uint8_t)169U, (uint8_t)167U, (uint8_t)235U, (uint8_t)41U,
    (uint8_t)42U, (uint8_t)10U, (uint8_t)26U, (uint8_t)162U, (uint8_t)244U, (uint8_t)151U,
    (uint8_t)37U, (uint8_t)104U, (uint8_t)102U, (uint8_t)146U, (uint8_t)70U, (uint8_t)144U,
    (uint8_t)122U, (uint8_t)53U
  };

static uint8_t
sigver_vectors384_low71[32U] =
  {
    (uint8_t)50U, (uint8_t)5U, (uint8_t)186U, (uint8_t)232U, (uint8_t)118U, (uint8_t)249U,
    (uint8_t)189U, (uint8_t)80U, (uint8_t)176U, (uint8_t)113U, (uint8_t)57U, (uint8_t)89U,
    (uint8_t)231U, (uint8_t)36U, (uint8_t)87U, (uint8_t)22U, (uint8_t)94U, (uint8_t)130U,
    (uint8_t)108U, (uint8_t)187U, (uint8_t)227U, (uint8_t)137U, (uint8_t)93U, (uint8_t)103U,
    (uint8_t)50U, (uint8_t)9U, (uint8_t)9U, (uint8_t)218U, (uint8_t)164U, (uint8_t)139U,
    (uint8_t)14U, (uint8_t)188U
  };

static uint8_t
sigver_vectors384_low72[32U] =
  {
    (uint8_t)209U, (uint8_t)89U, (uint8_t)37U, (uint8_t)98U, (uint8_t)39U, (uint8_t)62U,
    (uint8_t)94U, (uint8_t)15U, (uint8_t)87U, (uint8_t)187U, (uint8_t)251U, (uint8_t)146U,
    (uint8_t)206U, (uint8_t)221U, (uint8_t)154U, (uint8_t)247U, (uint8_t)241U, (uint8_t)51U,
    (uint8_t)37U, (uint8_t)86U, (uint8_t)132U, (uint8_t)238U, (uint8_t)5U, (uint8_t)10U,
    (uint8_t)249U, (uint8_t)182U, (uint8_t)240U, (uint8_t)32U, (uint8_t)25U, (uint8_t)187U,
    (uint8_t)202U, (uint8_t)250U
  };

static uint8_t
sigver_vectors384_low73[32U] =
  {
    (uint8_t)1U, (uint8_t)36U, (uint8_t)243U, (uint8_t)241U, (uint8_t)198U, (uint8_t)30U,
    (uint8_t)196U, (uint8_t)88U, (uint8_t)86U, (uint8_t)26U, (uint8_t)78U, (uint8_t)170U,
    (uint8_t)108U, (uint8_t)21U, (uint8_t)91U, (uint8_t)210U, (uint8_t)158U, (uint8_t)89U,
    (uint8_t)112U, (uint8_t)61U, (uint8_t)20U, (uint8_t)85U, (uint8_t)99U, (uint8_t)36U,
    (uint8_t)146U, (uint8_t)70U, (uint8_t)131U, (uint8_t)219U, (uint8_t)58U, (uint8_t)76U,
    (uint8_t)244U, (uint8_t)59U
  };

static uint8_t
sigver_vectors384_low74[32U] =
  {
    (uint8_t)104U, (uint8_t)138U, (uint8_t)92U, (uint8_t)95U, (uint8_t)192U, (uint8_t)199U,
    (uint8_t)186U, (uint8_t)146U, (uint8_t)33U, (uint8_t)12U, (uint8_t)80U, (uint8_t)204U,
    (uint8_t)229U, (uint8_t)181U, (uint8_t)18U, (uint8_t)164U, (uint8_t)104U, (uint8_t)168U,
    (uint8_t)128U, (uint8_t)224U, (uint8_t)90U, (uint8_t)204U, (uint8_t)33U, (uint8_t)202U,
    (uint8_t)86U, (uint8_t)87U, (uint8_t)29U, (uint8_t)137U, (uint8_t)244U, (uint8_t)95U,
    (uint8_t)96U, (uint8_t)58U
  };

static __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors384_low75[15U] =
  {
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low0 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low1 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low2 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low3 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low4 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low5 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low6 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low7 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low8 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low9 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low10 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low11 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low12 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low13 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low14 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low15 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low16 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low17 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low18 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low19 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low20 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low21 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low22 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low23 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low24 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low25 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low26 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low27 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low28 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low29 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low30 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low31 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low32 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low33 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low34 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low35 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low36 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low37 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low38 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low39 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low40 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low41 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low42 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low43 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low44 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low45 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low46 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low47 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low48 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low49 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low50 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low51 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low52 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low53 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low54 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low55 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low56 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low57 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low58 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low59 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low60 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low61 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low62 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low63 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low64 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low65 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low66 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low67 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low68 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low69 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors384_low70 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors384_low71 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors384_low72 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors384_low73 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors384_low74 }, .f5 = false
    }
  };

static lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors384_low = { .len = (uint32_t)15U, .b = sigver_vectors384_low75 };

static uint8_t
sigver_vectors512_low0[128U] =
  {
    (uint8_t)39U, (uint8_t)59U, (uint8_t)6U, (uint8_t)50U, (uint8_t)36U, (uint8_t)171U,
    (uint8_t)72U, (uint8_t)161U, (uint8_t)191U, (uint8_t)108U, (uint8_t)126U, (uint8_t)252U,
    (uint8_t)147U, (uint8_t)66U, (uint8_t)157U, (uint8_t)31U, (uint8_t)137U, (uint8_t)222U,
    (uint8_t)72U, (uint8_t)252U, (uint8_t)74U, (uint8_t)79U, (uint8_t)163U, (uint8_t)255U,
    (uint8_t)231U, (uint8_t)164U, (uint8_t)158U, (uint8_t)187U, (uint8_t)161U, (uint8_t)165U,
    (uint8_t)143U, (uint8_t)245U, (uint8_t)210U, (uint8_t)8U, (uint8_t)169U, (uint8_t)228U,
    (uint8_t)191U, (uint8_t)242U, (uint8_t)123U, (uint8_t)65U, (uint8_t)130U, (uint8_t)82U,
    (uint8_t)82U, (uint8_t)98U, (uint8_t)67U, (uint8_t)186U, (uint8_t)4U, (uint8_t)45U,
    (uint8_t)22U, (uint8_t)5U, (uint8_t)182U, (uint8_t)223U, (uint8_t)60U, (uint8_t)46U,
    (uint8_t)201U, (uint8_t)22U, (uint8_t)206U, (uint8_t)239U, (uint8_t)2U, (uint8_t)120U,
    (uint8_t)83U, (uint8_t)164U, (uint8_t)17U, (uint8_t)55U, (uint8_t)247U, (uint8_t)191U,
    (uint8_t)182U, (uint8_t)252U, (uint8_t)99U, (uint8_t)132U, (uint8_t)77U, (uint8_t)233U,
    (uint8_t)95U, (uint8_t)88U, (uint8_t)232U, (uint8_t)43U, (uint8_t)154U, (uint8_t)210U,
    (uint8_t)86U, (uint8_t)95U, (uint8_t)19U, (uint8_t)103U, (uint8_t)210U, (uint8_t)198U,
    (uint8_t)155U, (uint8_t)210U, (uint8_t)145U, (uint8_t)0U, (uint8_t)246U, (uint8_t)219U,
    (uint8_t)33U, (uint8_t)168U, (uint8_t)171U, (uint8_t)122U, (uint8_t)181U, (uint8_t)138U,
    (uint8_t)255U, (uint8_t)209U, (uint8_t)102U, (uint8_t)26U, (uint8_t)221U, (uint8_t)3U,
    (uint8_t)34U, (uint8_t)189U, (uint8_t)145U, (uint8_t)87U, (uint8_t)33U, (uint8_t)55U,
    (uint8_t)141U, (uint8_t)249U, (uint8_t)250U, (uint8_t)35U, (uint8_t)62U, (uint8_t)240U,
    (uint8_t)183U, (uint8_t)224U, (uint8_t)160U, (uint8_t)168U, (uint8_t)91U, (uint8_t)227U,
    (uint8_t)22U, (uint8_t)137U, (uint8_t)226U, (uint8_t)24U, (uint8_t)145U, (uint8_t)236U,
    (uint8_t)137U, (uint8_t)119U
  };

static uint8_t
sigver_vectors512_low1[32U] =
  {
    (uint8_t)72U, (uint8_t)78U, (uint8_t)49U, (uint8_t)230U, (uint8_t)158U, (uint8_t)247U,
    (uint8_t)11U, (uint8_t)184U, (uint8_t)82U, (uint8_t)120U, (uint8_t)83U, (uint8_t)194U,
    (uint8_t)44U, (uint8_t)107U, (uint8_t)107U, (uint8_t)76U, (uint8_t)210U, (uint8_t)165U,
    (uint8_t)19U, (uint8_t)17U, (uint8_t)221U, (uint8_t)230U, (uint8_t)108U, (uint8_t)123U,
    (uint8_t)99U, (uint8_t)240U, (uint8_t)151U, (uint8_t)219U, (uint8_t)182U, (uint8_t)171U,
    (uint8_t)39U, (uint8_t)191U
  };

static uint8_t
sigver_vectors512_low2[32U] =
  {
    (uint8_t)225U, (uint8_t)255U, (uint8_t)129U, (uint8_t)119U, (uint8_t)244U, (uint8_t)6U,
    (uint8_t)29U, (uint8_t)79U, (uint8_t)187U, (uint8_t)172U, (uint8_t)187U, (uint8_t)199U,
    (uint8_t)5U, (uint8_t)25U, (uint8_t)240U, (uint8_t)252U, (uint8_t)140U, (uint8_t)139U,
    (uint8_t)96U, (uint8_t)83U, (uint8_t)215U, (uint8_t)42U, (uint8_t)240U, (uint8_t)254U,
    (uint8_t)79U, (uint8_t)4U, (uint8_t)141U, (uint8_t)97U, (uint8_t)80U, (uint8_t)4U,
    (uint8_t)247U, (uint8_t)78U
  };

static uint8_t
sigver_vectors512_low3[32U] =
  {
    (uint8_t)145U, (uint8_t)163U, (uint8_t)3U, (uint8_t)216U, (uint8_t)254U, (uint8_t)58U,
    (uint8_t)180U, (uint8_t)23U, (uint8_t)96U, (uint8_t)112U, (uint8_t)246U, (uint8_t)64U,
    (uint8_t)98U, (uint8_t)103U, (uint8_t)246U, (uint8_t)183U, (uint8_t)155U, (uint8_t)254U,
    (uint8_t)94U, (uint8_t)181U, (uint8_t)246U, (uint8_t)42U, (uint8_t)230U, (uint8_t)174U,
    (uint8_t)179U, (uint8_t)116U, (uint8_t)217U, (uint8_t)6U, (uint8_t)103U, (uint8_t)133U,
    (uint8_t)133U, (uint8_t)24U
  };

static uint8_t
sigver_vectors512_low4[32U] =
  {
    (uint8_t)225U, (uint8_t)82U, (uint8_t)17U, (uint8_t)156U, (uint8_t)239U, (uint8_t)162U,
    (uint8_t)104U, (uint8_t)38U, (uint8_t)234U, (uint8_t)7U, (uint8_t)236U, (uint8_t)64U,
    (uint8_t)164U, (uint8_t)40U, (uint8_t)134U, (uint8_t)145U, (uint8_t)50U, (uint8_t)215U,
    (uint8_t)8U, (uint8_t)18U, (uint8_t)197U, (uint8_t)87U, (uint8_t)140U, (uint8_t)90U,
    (uint8_t)38U, (uint8_t)14U, (uint8_t)72U, (uint8_t)214U, (uint8_t)128U, (uint8_t)14U,
    (uint8_t)4U, (uint8_t)106U
  };

static uint8_t
sigver_vectors512_low5[128U] =
  {
    (uint8_t)214U, (uint8_t)78U, (uint8_t)161U, (uint8_t)167U, (uint8_t)104U, (uint8_t)176U,
    (uint8_t)222U, (uint8_t)41U, (uint8_t)171U, (uint8_t)1U, (uint8_t)138U, (uint8_t)233U,
    (uint8_t)59U, (uint8_t)170U, (uint8_t)100U, (uint8_t)93U, (uint8_t)7U, (uint8_t)140U,
    (uint8_t)112U, (uint8_t)162U, (uint8_t)247U, (uint8_t)170U, (uint8_t)74U, (uint8_t)205U,
    (uint8_t)74U, (uint8_t)231U, (uint8_t)82U, (uint8_t)101U, (uint8_t)56U, (uint8_t)235U,
    (uint8_t)213U, (uint8_t)246U, (uint8_t)151U, (uint8_t)161U, (uint8_t)25U, (uint8_t)39U,
    (uint8_t)207U, (uint8_t)208U, (uint8_t)221U, (uint8_t)201U, (uint8_t)24U, (uint8_t)124U,
    (uint8_t)9U, (uint8_t)95U, (uint8_t)20U, (uint8_t)173U, (uint8_t)48U, (uint8_t)84U,
    (uint8_t)76U, (uint8_t)182U, (uint8_t)62U, (uint8_t)222U, (uint8_t)147U, (uint8_t)83U,
    (uint8_t)175U, (uint8_t)139U, (uint8_t)35U, (uint8_t)193U, (uint8_t)140U, (uint8_t)226U,
    (uint8_t)40U, (uint8_t)67U, (uint8_t)136U, (uint8_t)31U, (uint8_t)226U, (uint8_t)215U,
    (uint8_t)189U, (uint8_t)231U, (uint8_t)72U, (uint8_t)252U, (uint8_t)105U, (uint8_t)8U,
    (uint8_t)89U, (uint8_t)33U, (uint8_t)103U, (uint8_t)120U, (uint8_t)88U, (uint8_t)216U,
    (uint8_t)125U, (uint8_t)45U, (uint8_t)195U, (uint8_t)226U, (uint8_t)68U, (uint8_t)246U,
    (uint8_t)199U, (uint8_t)226U, (uint8_t)194U, (uint8_t)178U, (uint8_t)189U, (uint8_t)121U,
    (uint8_t)31U, (uint8_t)69U, (uint8_t)13U, (uint8_t)253U, (uint8_t)212U, (uint8_t)255U,
    (uint8_t)13U, (uint8_t)221U, (uint8_t)53U, (uint8_t)171U, (uint8_t)42U, (uint8_t)218U,
    (uint8_t)79U, (uint8_t)27U, (uint8_t)144U, (uint8_t)171U, (uint8_t)22U, (uint8_t)239U,
    (uint8_t)43U, (uint8_t)246U, (uint8_t)59U, (uint8_t)63U, (uint8_t)190U, (uint8_t)136U,
    (uint8_t)206U, (uint8_t)138U, (uint8_t)93U, (uint8_t)91U, (uint8_t)184U, (uint8_t)84U,
    (uint8_t)48U, (uint8_t)116U, (uint8_t)13U, (uint8_t)55U, (uint8_t)68U, (uint8_t)132U,
    (uint8_t)156U, (uint8_t)19U
  };

static uint8_t
sigver_vectors512_low6[32U] =
  {
    (uint8_t)139U, (uint8_t)117U, (uint8_t)252U, (uint8_t)1U, (uint8_t)41U, (uint8_t)201U,
    (uint8_t)167U, (uint8_t)143U, (uint8_t)131U, (uint8_t)149U, (uint8_t)198U, (uint8_t)58U,
    (uint8_t)233U, (uint8_t)105U, (uint8_t)75U, (uint8_t)5U, (uint8_t)205U, (uint8_t)105U,
    (uint8_t)80U, (uint8_t)102U, (uint8_t)92U, (uint8_t)245U, (uint8_t)218U, (uint8_t)125U,
    (uint8_t)102U, (uint8_t)17U, (uint8_t)141U, (uint8_t)228U, (uint8_t)81U, (uint8_t)66U,
    (uint8_t)38U, (uint8_t)36U
  };

static uint8_t
sigver_vectors512_low7[32U] =
  {
    (uint8_t)179U, (uint8_t)148U, (uint8_t)23U, (uint8_t)25U, (uint8_t)129U, (uint8_t)212U,
    (uint8_t)137U, (uint8_t)109U, (uint8_t)110U, (uint8_t)27U, (uint8_t)78U, (uint8_t)242U,
    (uint8_t)51U, (uint8_t)109U, (uint8_t)155U, (uint8_t)239U, (uint8_t)231U, (uint8_t)210U,
    (uint8_t)126U, (uint8_t)30U, (uint8_t)184U, (uint8_t)127U, (uint8_t)28U, (uint8_t)20U,
    (uint8_t)184U, (uint8_t)221U, (uint8_t)218U, (uint8_t)98U, (uint8_t)42U, (uint8_t)243U,
    (uint8_t)121U, (uint8_t)220U
  };

static uint8_t
sigver_vectors512_low8[32U] =
  {
    (uint8_t)23U, (uint8_t)226U, (uint8_t)152U, (uint8_t)230U, (uint8_t)122U, (uint8_t)210U,
    (uint8_t)175U, (uint8_t)118U, (uint8_t)246U, (uint8_t)137U, (uint8_t)47U, (uint8_t)220U,
    (uint8_t)234U, (uint8_t)208U, (uint8_t)10U, (uint8_t)136U, (uint8_t)37U, (uint8_t)101U,
    (uint8_t)115U, (uint8_t)134U, (uint8_t)143U, (uint8_t)121U, (uint8_t)220U, (uint8_t)116U,
    (uint8_t)67U, (uint8_t)27U, (uint8_t)85U, (uint8_t)16U, (uint8_t)48U, (uint8_t)88U,
    (uint8_t)240U, (uint8_t)176U
  };

static uint8_t
sigver_vectors512_low9[32U] =
  {
    (uint8_t)136U, (uint8_t)19U, (uint8_t)40U, (uint8_t)205U, (uint8_t)145U, (uint8_t)228U,
    (uint8_t)61U, (uint8_t)48U, (uint8_t)19U, (uint8_t)63U, (uint8_t)110U, (uint8_t)71U,
    (uint8_t)30U, (uint8_t)11U, (uint8_t)155U, (uint8_t)4U, (uint8_t)53U, (uint8_t)59U,
    (uint8_t)23U, (uint8_t)137U, (uint8_t)63U, (uint8_t)183U, (uint8_t)97U, (uint8_t)79U,
    (uint8_t)215U, (uint8_t)51U, (uint8_t)61U, (uint8_t)129U, (uint8_t)42U, (uint8_t)61U,
    (uint8_t)246U, (uint8_t)180U
  };

static uint8_t
sigver_vectors512_low10[128U] =
  {
    (uint8_t)29U, (uint8_t)184U, (uint8_t)84U, (uint8_t)69U, (uint8_t)201U, (uint8_t)216U,
    (uint8_t)209U, (uint8_t)71U, (uint8_t)138U, (uint8_t)151U, (uint8_t)221U, (uint8_t)157U,
    (uint8_t)111U, (uint8_t)251U, (uint8_t)241U, (uint8_t)30U, (uint8_t)188U, (uint8_t)210U,
    (uint8_t)17U, (uint8_t)77U, (uint8_t)46U, (uint8_t)212U, (uint8_t)232U, (uint8_t)182U,
    (uint8_t)129U, (uint8_t)17U, (uint8_t)113U, (uint8_t)217U, (uint8_t)71U, (uint8_t)231U,
    (uint8_t)212U, (uint8_t)218U, (uint8_t)237U, (uint8_t)234U, (uint8_t)53U, (uint8_t)175U,
    (uint8_t)97U, (uint8_t)119U, (uint8_t)222U, (uint8_t)190U, (uint8_t)46U, (uint8_t)246U,
    (uint8_t)217U, (uint8_t)63U, (uint8_t)148U, (uint8_t)255U, (uint8_t)157U, (uint8_t)119U,
    (uint8_t)11U, (uint8_t)69U, (uint8_t)212U, (uint8_t)88U, (uint8_t)233U, (uint8_t)29U,
    (uint8_t)235U, (uint8_t)78U, (uint8_t)239U, (uint8_t)89U, (uint8_t)133U, (uint8_t)100U,
    (uint8_t)37U, (uint8_t)215U, (uint8_t)176U, (uint8_t)2U, (uint8_t)145U, (uint8_t)175U,
    (uint8_t)249U, (uint8_t)182U, (uint8_t)201U, (uint8_t)250U, (uint8_t)2U, (uint8_t)55U,
    (uint8_t)94U, (uint8_t)193U, (uint8_t)160U, (uint8_t)111U, (uint8_t)113U, (uint8_t)247U,
    (uint8_t)84U, (uint8_t)135U, (uint8_t)33U, (uint8_t)121U, (uint8_t)0U, (uint8_t)35U,
    (uint8_t)48U, (uint8_t)28U, (uint8_t)246U, (uint8_t)172U, (uint8_t)127U, (uint8_t)238U,
    (uint8_t)29U, (uint8_t)69U, (uint8_t)18U, (uint8_t)40U, (uint8_t)16U, (uint8_t)110U,
    (uint8_t)244U, (uint8_t)71U, (uint8_t)38U, (uint8_t)129U, (uint8_t)230U, (uint8_t)82U,
    (uint8_t)200U, (uint8_t)205U, (uint8_t)89U, (uint8_t)177U, (uint8_t)93U, (uint8_t)109U,
    (uint8_t)22U, (uint8_t)241U, (uint8_t)225U, (uint8_t)52U, (uint8_t)64U, (uint8_t)216U,
    (uint8_t)136U, (uint8_t)226U, (uint8_t)101U, (uint8_t)129U, (uint8_t)124U, (uint8_t)180U,
    (uint8_t)166U, (uint8_t)84U, (uint8_t)247U, (uint8_t)36U, (uint8_t)110U, (uint8_t)9U,
    (uint8_t)128U, (uint8_t)223U
  };

static uint8_t
sigver_vectors512_low11[32U] =
  {
    (uint8_t)118U, (uint8_t)229U, (uint8_t)16U, (uint8_t)134U, (uint8_t)224U, (uint8_t)120U,
    (uint8_t)178U, (uint8_t)177U, (uint8_t)22U, (uint8_t)253U, (uint8_t)30U, (uint8_t)156U,
    (uint8_t)111U, (uint8_t)163U, (uint8_t)213U, (uint8_t)63U, (uint8_t)103U, (uint8_t)90U,
    (uint8_t)228U, (uint8_t)2U, (uint8_t)82U, (uint8_t)251U, (uint8_t)159U, (uint8_t)12U,
    (uint8_t)198U, (uint8_t)40U, (uint8_t)23U, (uint8_t)189U, (uint8_t)156U, (uint8_t)232U,
    (uint8_t)131U, (uint8_t)29U
  };

static uint8_t
sigver_vectors512_low12[32U] =
  {
    (uint8_t)202U, (uint8_t)126U, (uint8_t)96U, (uint8_t)154U, (uint8_t)11U, (uint8_t)29U,
    (uint8_t)20U, (uint8_t)183U, (uint8_t)201U, (uint8_t)36U, (uint8_t)155U, (uint8_t)83U,
    (uint8_t)218U, (uint8_t)11U, (uint8_t)32U, (uint8_t)80U, (uint8_t)69U, (uint8_t)14U,
    (uint8_t)42U, (uint8_t)37U, (uint8_t)203U, (uint8_t)108U, (uint8_t)143U, (uint8_t)129U,
    (uint8_t)197U, (uint8_t)49U, (uint8_t)25U, (uint8_t)116U, (uint8_t)167U, (uint8_t)239U,
    (uint8_t)181U, (uint8_t)118U
  };

static uint8_t
sigver_vectors512_low13[32U] =
  {
    (uint8_t)35U, (uint8_t)182U, (uint8_t)83U, (uint8_t)250U, (uint8_t)170U, (uint8_t)125U,
    (uint8_t)69U, (uint8_t)82U, (uint8_t)56U, (uint8_t)135U, (uint8_t)113U, (uint8_t)147U,
    (uint8_t)24U, (uint8_t)3U, (uint8_t)206U, (uint8_t)147U, (uint8_t)157U, (uint8_t)213U,
    (uint8_t)238U, (uint8_t)98U, (uint8_t)211U, (uint8_t)250U, (uint8_t)114U, (uint8_t)176U,
    (uint8_t)25U, (uint8_t)190U, (uint8_t)27U, (uint8_t)34U, (uint8_t)114U, (uint8_t)200U,
    (uint8_t)85U, (uint8_t)146U
  };

static uint8_t
sigver_vectors512_low14[32U] =
  {
    (uint8_t)160U, (uint8_t)60U, (uint8_t)111U, (uint8_t)92U, (uint8_t)84U, (uint8_t)161U,
    (uint8_t)8U, (uint8_t)97U, (uint8_t)214U, (uint8_t)184U, (uint8_t)146U, (uint8_t)40U,
    (uint8_t)33U, (uint8_t)112U, (uint8_t)142U, (uint8_t)147U, (uint8_t)6U, (uint8_t)253U,
    (uint8_t)109U, (uint8_t)93U, (uint8_t)16U, (uint8_t)213U, (uint8_t)102U, (uint8_t)132U,
    (uint8_t)90U, (uint8_t)16U, (uint8_t)101U, (uint8_t)57U, (uint8_t)203U, (uint8_t)244U,
    (uint8_t)250U, (uint8_t)221U
  };

static uint8_t
sigver_vectors512_low15[128U] =
  {
    (uint8_t)145U, (uint8_t)141U, (uint8_t)159U, (uint8_t)66U, (uint8_t)14U, (uint8_t)146U,
    (uint8_t)123U, (uint8_t)62U, (uint8_t)10U, (uint8_t)85U, (uint8_t)210U, (uint8_t)118U,
    (uint8_t)184U, (uint8_t)180U, (uint8_t)13U, (uint8_t)138U, (uint8_t)44U, (uint8_t)93U,
    (uint8_t)247U, (uint8_t)72U, (uint8_t)114U, (uint8_t)127U, (uint8_t)247U, (uint8_t)42U,
    (uint8_t)67U, (uint8_t)140U, (uint8_t)126U, (uint8_t)101U, (uint8_t)147U, (uint8_t)245U,
    (uint8_t)66U, (uint8_t)39U, (uint8_t)64U, (uint8_t)80U, (uint8_t)220U, (uint8_t)231U,
    (uint8_t)39U, (uint8_t)152U, (uint8_t)13U, (uint8_t)62U, (uint8_t)249U, (uint8_t)12U,
    (uint8_t)138U, (uint8_t)165U, (uint8_t)193U, (uint8_t)61U, (uint8_t)83U, (uint8_t)241U,
    (uint8_t)232U, (uint8_t)214U, (uint8_t)49U, (uint8_t)235U, (uint8_t)182U, (uint8_t)80U,
    (uint8_t)222U, (uint8_t)225U, (uint8_t)27U, (uint8_t)148U, (uint8_t)144U, (uint8_t)43U,
    (uint8_t)189U, (uint8_t)124U, (uint8_t)146U, (uint8_t)184U, (uint8_t)24U, (uint8_t)106U,
    (uint8_t)249U, (uint8_t)3U, (uint8_t)156U, (uint8_t)86U, (uint8_t)196U, (uint8_t)63U,
    (uint8_t)49U, (uint8_t)16U, (uint8_t)105U, (uint8_t)119U, (uint8_t)146U, (uint8_t)200U,
    (uint8_t)205U, (uint8_t)22U, (uint8_t)20U, (uint8_t)22U, (uint8_t)111U, (uint8_t)6U,
    (uint8_t)208U, (uint8_t)156U, (uint8_t)219U, (uint8_t)88U, (uint8_t)218U, (uint8_t)177U,
    (uint8_t)104U, (uint8_t)204U, (uint8_t)54U, (uint8_t)128U, (uint8_t)168U, (uint8_t)71U,
    (uint8_t)59U, (uint8_t)26U, (uint8_t)98U, (uint8_t)59U, (uint8_t)248U, (uint8_t)93U,
    (uint8_t)186U, (uint8_t)133U, (uint8_t)94U, (uint8_t)172U, (uint8_t)229U, (uint8_t)121U,
    (uint8_t)217U, (uint8_t)65U, (uint8_t)13U, (uint8_t)44U, (uint8_t)76U, (uint8_t)165U,
    (uint8_t)237U, (uint8_t)230U, (uint8_t)220U, (uint8_t)30U, (uint8_t)61U, (uint8_t)184U,
    (uint8_t)30U, (uint8_t)35U, (uint8_t)60U, (uint8_t)52U, (uint8_t)174U, (uint8_t)146U,
    (uint8_t)47U, (uint8_t)73U
  };

static uint8_t
sigver_vectors512_low16[32U] =
  {
    (uint8_t)188U, (uint8_t)124U, (uint8_t)142U, (uint8_t)9U, (uint8_t)189U, (uint8_t)9U,
    (uint8_t)52U, (uint8_t)104U, (uint8_t)247U, (uint8_t)6U, (uint8_t)116U, (uint8_t)10U,
    (uint8_t)65U, (uint8_t)48U, (uint8_t)197U, (uint8_t)68U, (uint8_t)55U, (uint8_t)79U,
    (uint8_t)220U, (uint8_t)146U, (uint8_t)74U, (uint8_t)83U, (uint8_t)94U, (uint8_t)240U,
    (uint8_t)46U, (uint8_t)157U, (uint8_t)59U, (uint8_t)230U, (uint8_t)198U, (uint8_t)211U,
    (uint8_t)187U, (uint8_t)250U
  };

static uint8_t
sigver_vectors512_low17[32U] =
  {
    (uint8_t)175U, (uint8_t)63U, (uint8_t)129U, (uint8_t)58U, (uint8_t)230U, (uint8_t)100U,
    (uint8_t)111U, (uint8_t)91U, (uint8_t)109U, (uint8_t)191U, (uint8_t)176U, (uint8_t)242U,
    (uint8_t)97U, (uint8_t)253U, (uint8_t)66U, (uint8_t)83U, (uint8_t)119U, (uint8_t)5U,
    (uint8_t)200U, (uint8_t)0U, (uint8_t)187U, (uint8_t)22U, (uint8_t)71U, (uint8_t)56U,
    (uint8_t)99U, (uint8_t)67U, (uint8_t)66U, (uint8_t)138U, (uint8_t)159U, (uint8_t)46U,
    (uint8_t)16U, (uint8_t)252U
  };

static uint8_t
sigver_vectors512_low18[32U] =
  {
    (uint8_t)107U, (uint8_t)215U, (uint8_t)206U, (uint8_t)149U, (uint8_t)175U, (uint8_t)37U,
    (uint8_t)171U, (uint8_t)251U, (uint8_t)241U, (uint8_t)74U, (uint8_t)239U, (uint8_t)75U,
    (uint8_t)23U, (uint8_t)57U, (uint8_t)47U, (uint8_t)29U, (uint8_t)168U, (uint8_t)119U,
    (uint8_t)171U, (uint8_t)86U, (uint8_t)46U, (uint8_t)202U, (uint8_t)56U, (uint8_t)215U,
    (uint8_t)133U, (uint8_t)254U, (uint8_t)57U, (uint8_t)104U, (uint8_t)46U, (uint8_t)156U,
    (uint8_t)147U, (uint8_t)36U
  };

static uint8_t
sigver_vectors512_low19[32U] =
  {
    (uint8_t)102U, (uint8_t)136U, (uint8_t)190U, (uint8_t)162U, (uint8_t)12U, (uint8_t)135U,
    (uint8_t)186U, (uint8_t)179U, (uint8_t)77U, (uint8_t)66U, (uint8_t)6U, (uint8_t)66U,
    (uint8_t)218U, (uint8_t)155U, (uint8_t)221U, (uint8_t)76U, (uint8_t)105U, (uint8_t)69U,
    (uint8_t)107U, (uint8_t)222U, (uint8_t)197U, (uint8_t)8U, (uint8_t)53U, (uint8_t)136U,
    (uint8_t)115U, (uint8_t)103U, (uint8_t)187U, (uint8_t)79U, (uint8_t)183U, (uint8_t)205U,
    (uint8_t)134U, (uint8_t)80U
  };

static uint8_t
sigver_vectors512_low20[128U] =
  {
    (uint8_t)110U, (uint8_t)41U, (uint8_t)50U, (uint8_t)21U, (uint8_t)51U, (uint8_t)1U,
    (uint8_t)164U, (uint8_t)238U, (uint8_t)246U, (uint8_t)128U, (uint8_t)230U, (uint8_t)66U,
    (uint8_t)137U, (uint8_t)41U, (uint8_t)173U, (uint8_t)174U, (uint8_t)152U, (uint8_t)140U,
    (uint8_t)16U, (uint8_t)141U, (uint8_t)102U, (uint8_t)138U, (uint8_t)49U, (uint8_t)255U,
    (uint8_t)85U, (uint8_t)208U, (uint8_t)72U, (uint8_t)153U, (uint8_t)71U, (uint8_t)215U,
    (uint8_t)95U, (uint8_t)248U, (uint8_t)26U, (uint8_t)70U, (uint8_t)191U, (uint8_t)137U,
    (uint8_t)232U, (uint8_t)77U, (uint8_t)100U, (uint8_t)1U, (uint8_t)240U, (uint8_t)35U,
    (uint8_t)190U, (uint8_t)110U, (uint8_t)135U, (uint8_t)104U, (uint8_t)143U, (uint8_t)188U,
    (uint8_t)215U, (uint8_t)132U, (uint8_t)215U, (uint8_t)133U, (uint8_t)202U, (uint8_t)132U,
    (uint8_t)103U, (uint8_t)53U, (uint8_t)82U, (uint8_t)74U, (uint8_t)203U, (uint8_t)82U,
    (uint8_t)208U, (uint8_t)4U, (uint8_t)82U, (uint8_t)200U, (uint8_t)64U, (uint8_t)64U,
    (uint8_t)164U, (uint8_t)121U, (uint8_t)231U, (uint8_t)204U, (uint8_t)51U, (uint8_t)9U,
    (uint8_t)54U, (uint8_t)68U, (uint8_t)29U, (uint8_t)147U, (uint8_t)187U, (uint8_t)231U,
    (uint8_t)34U, (uint8_t)169U, (uint8_t)67U, (uint8_t)42U, (uint8_t)110U, (uint8_t)29U,
    (uint8_t)177U, (uint8_t)18U, (uint8_t)181U, (uint8_t)201U, (uint8_t)64U, (uint8_t)59U,
    (uint8_t)16U, (uint8_t)39U, (uint8_t)44U, (uint8_t)177U, (uint8_t)52U, (uint8_t)127U,
    (uint8_t)214U, (uint8_t)25U, (uint8_t)212U, (uint8_t)99U, (uint8_t)247U, (uint8_t)169U,
    (uint8_t)210U, (uint8_t)35U, (uint8_t)173U, (uint8_t)118U, (uint8_t)253U, (uint8_t)224U,
    (uint8_t)109U, (uint8_t)138U, (uint8_t)104U, (uint8_t)131U, (uint8_t)80U, (uint8_t)15U,
    (uint8_t)184U, (uint8_t)67U, (uint8_t)35U, (uint8_t)90U, (uint8_t)191U, (uint8_t)249U,
    (uint8_t)142U, (uint8_t)36U, (uint8_t)27U, (uint8_t)223U, (uint8_t)181U, (uint8_t)83U,
    (uint8_t)140U, (uint8_t)62U
  };

static uint8_t
sigver_vectors512_low21[32U] =
  {
    (uint8_t)156U, (uint8_t)176U, (uint8_t)207U, (uint8_t)105U, (uint8_t)48U, (uint8_t)61U,
    (uint8_t)175U, (uint8_t)199U, (uint8_t)97U, (uint8_t)212U, (uint8_t)228U, (uint8_t)104U,
    (uint8_t)123U, (uint8_t)78U, (uint8_t)207U, (uint8_t)3U, (uint8_t)158U, (uint8_t)109U,
    (uint8_t)52U, (uint8_t)171U, (uint8_t)150U, (uint8_t)74U, (uint8_t)248U, (uint8_t)8U,
    (uint8_t)16U, (uint8_t)216U, (uint8_t)213U, (uint8_t)88U, (uint8_t)164U, (uint8_t)168U,
    (uint8_t)214U, (uint8_t)247U
  };

static uint8_t
sigver_vectors512_low22[32U] =
  {
    (uint8_t)45U, (uint8_t)81U, (uint8_t)35U, (uint8_t)58U, (uint8_t)23U, (uint8_t)136U,
    (uint8_t)146U, (uint8_t)10U, (uint8_t)134U, (uint8_t)238U, (uint8_t)8U, (uint8_t)161U,
    (uint8_t)150U, (uint8_t)44U, (uint8_t)121U, (uint8_t)239U, (uint8_t)163U, (uint8_t)23U,
    (uint8_t)251U, (uint8_t)120U, (uint8_t)121U, (uint8_t)226U, (uint8_t)151U, (uint8_t)218U,
    (uint8_t)210U, (uint8_t)20U, (uint8_t)109U, (uint8_t)185U, (uint8_t)149U, (uint8_t)250U,
    (uint8_t)28U, (uint8_t)120U
  };

static uint8_t
sigver_vectors512_low23[32U] =
  {
    (uint8_t)75U, (uint8_t)159U, (uint8_t)145U, (uint8_t)228U, (uint8_t)40U, (uint8_t)82U,
    (uint8_t)135U, (uint8_t)38U, (uint8_t)26U, (uint8_t)29U, (uint8_t)28U, (uint8_t)146U,
    (uint8_t)60U, (uint8_t)246U, (uint8_t)25U, (uint8_t)205U, (uint8_t)82U, (uint8_t)193U,
    (uint8_t)117U, (uint8_t)207U, (uint8_t)231U, (uint8_t)241U, (uint8_t)190U, (uint8_t)96U,
    (uint8_t)165U, (uint8_t)37U, (uint8_t)140U, (uint8_t)97U, (uint8_t)3U, (uint8_t)72U,
    (uint8_t)186U, (uint8_t)61U
  };

static uint8_t
sigver_vectors512_low24[32U] =
  {
    (uint8_t)40U, (uint8_t)196U, (uint8_t)95U, (uint8_t)144U, (uint8_t)29U, (uint8_t)113U,
    (uint8_t)196U, (uint8_t)27U, (uint8_t)41U, (uint8_t)134U, (uint8_t)56U, (uint8_t)236U,
    (uint8_t)13U, (uint8_t)106U, (uint8_t)133U, (uint8_t)215U, (uint8_t)252U, (uint8_t)176U,
    (uint8_t)195U, (uint8_t)59U, (uint8_t)191U, (uint8_t)236U, (uint8_t)90U, (uint8_t)156U,
    (uint8_t)129U, (uint8_t)8U, (uint8_t)70U, (uint8_t)182U, (uint8_t)57U, (uint8_t)40U,
    (uint8_t)154U, (uint8_t)132U
  };

static uint8_t
sigver_vectors512_low25[128U] =
  {
    (uint8_t)47U, (uint8_t)72U, (uint8_t)236U, (uint8_t)56U, (uint8_t)127U, (uint8_t)24U,
    (uint8_t)16U, (uint8_t)53U, (uint8_t)179U, (uint8_t)80U, (uint8_t)119U, (uint8_t)46U,
    (uint8_t)39U, (uint8_t)244U, (uint8_t)120U, (uint8_t)174U, (uint8_t)110U, (uint8_t)199U,
    (uint8_t)72U, (uint8_t)121U, (uint8_t)35U, (uint8_t)105U, (uint8_t)47U, (uint8_t)174U,
    (uint8_t)33U, (uint8_t)126U, (uint8_t)15U, (uint8_t)134U, (uint8_t)54U, (uint8_t)172U,
    (uint8_t)208U, (uint8_t)98U, (uint8_t)166U, (uint8_t)172U, (uint8_t)57U, (uint8_t)247U,
    (uint8_t)67U, (uint8_t)95U, (uint8_t)39U, (uint8_t)160U, (uint8_t)235U, (uint8_t)207U,
    (uint8_t)216U, (uint8_t)24U, (uint8_t)122U, (uint8_t)145U, (uint8_t)239U, (uint8_t)0U,
    (uint8_t)251U, (uint8_t)104U, (uint8_t)209U, (uint8_t)6U, (uint8_t)184U, (uint8_t)218U,
    (uint8_t)74U, (uint8_t)29U, (uint8_t)237U, (uint8_t)197U, (uint8_t)164U, (uint8_t)10U,
    (uint8_t)79U, (uint8_t)174U, (uint8_t)112U, (uint8_t)158U, (uint8_t)146U, (uint8_t)176U,
    (uint8_t)15U, (uint8_t)204U, (uint8_t)33U, (uint8_t)141U, (uint8_t)231U, (uint8_t)100U,
    (uint8_t)23U, (uint8_t)215U, (uint8_t)81U, (uint8_t)133U, (uint8_t)229U, (uint8_t)157U,
    (uint8_t)255U, (uint8_t)118U, (uint8_t)236U, (uint8_t)21U, (uint8_t)67U, (uint8_t)251U,
    (uint8_t)66U, (uint8_t)157U, (uint8_t)135U, (uint8_t)194U, (uint8_t)202U, (uint8_t)129U,
    (uint8_t)52U, (uint8_t)255U, (uint8_t)90U, (uint8_t)233U, (uint8_t)180U, (uint8_t)84U,
    (uint8_t)86U, (uint8_t)202U, (uint8_t)217U, (uint8_t)63U, (uint8_t)198U, (uint8_t)114U,
    (uint8_t)35U, (uint8_t)198U, (uint8_t)130U, (uint8_t)147U, (uint8_t)35U, (uint8_t)19U,
    (uint8_t)149U, (uint8_t)40U, (uint8_t)125U, (uint8_t)192U, (uint8_t)183U, (uint8_t)86U,
    (uint8_t)53U, (uint8_t)86U, (uint8_t)96U, (uint8_t)114U, (uint8_t)26U, (uint8_t)31U,
    (uint8_t)93U, (uint8_t)248U, (uint8_t)59U, (uint8_t)245U, (uint8_t)188U, (uint8_t)184U,
    (uint8_t)69U, (uint8_t)110U
  };

static uint8_t
sigver_vectors512_low26[32U] =
  {
    (uint8_t)227U, (uint8_t)16U, (uint8_t)150U, (uint8_t)194U, (uint8_t)213U, (uint8_t)18U,
    (uint8_t)251U, (uint8_t)248U, (uint8_t)79U, (uint8_t)129U, (uint8_t)233U, (uint8_t)189U,
    (uint8_t)177U, (uint8_t)111U, (uint8_t)51U, (uint8_t)18U, (uint8_t)23U, (uint8_t)2U,
    (uint8_t)137U, (uint8_t)118U, (uint8_t)5U, (uint8_t)180U, (uint8_t)58U, (uint8_t)61U,
    (uint8_t)181U, (uint8_t)70U, (uint8_t)248U, (uint8_t)251U, (uint8_t)105U, (uint8_t)91U,
    (uint8_t)95U, (uint8_t)111U
  };

static uint8_t
sigver_vectors512_low27[32U] =
  {
    (uint8_t)111U, (uint8_t)190U, (uint8_t)198U, (uint8_t)160U, (uint8_t)74U, (uint8_t)140U,
    (uint8_t)89U, (uint8_t)214U, (uint8_t)28U, (uint8_t)144U, (uint8_t)10U, (uint8_t)133U,
    (uint8_t)29U, (uint8_t)139U, (uint8_t)248U, (uint8_t)82U, (uint8_t)33U, (uint8_t)135U,
    (uint8_t)211U, (uint8_t)236U, (uint8_t)38U, (uint8_t)55U, (uint8_t)177U, (uint8_t)15U,
    (uint8_t)168U, (uint8_t)243U, (uint8_t)119U, (uint8_t)104U, (uint8_t)158U, (uint8_t)8U,
    (uint8_t)107U, (uint8_t)186U
  };

static uint8_t
sigver_vectors512_low28[32U] =
  {
    (uint8_t)27U, (uint8_t)36U, (uint8_t)76U, (uint8_t)33U, (uint8_t)192U, (uint8_t)140U,
    (uint8_t)12U, (uint8_t)10U, (uint8_t)16U, (uint8_t)71U, (uint8_t)127U, (uint8_t)183U,
    (uint8_t)162U, (uint8_t)19U, (uint8_t)130U, (uint8_t)212U, (uint8_t)5U, (uint8_t)185U,
    (uint8_t)92U, (uint8_t)117U, (uint8_t)80U, (uint8_t)136U, (uint8_t)41U, (uint8_t)40U,
    (uint8_t)89U, (uint8_t)202U, (uint8_t)14U, (uint8_t)113U, (uint8_t)186U, (uint8_t)182U,
    (uint8_t)131U, (uint8_t)97U
  };

static uint8_t
sigver_vectors512_low29[32U] =
  {
    (uint8_t)133U, (uint8_t)47U, (uint8_t)76U, (uint8_t)191U, (uint8_t)211U, (uint8_t)70U,
    (uint8_t)233U, (uint8_t)15U, (uint8_t)64U, (uint8_t)78U, (uint8_t)29U, (uint8_t)213U,
    (uint8_t)196U, (uint8_t)178U, (uint8_t)193U, (uint8_t)222U, (uint8_t)188U, (uint8_t)163U,
    (uint8_t)234U, (uint8_t)26U, (uint8_t)190U, (uint8_t)254U, (uint8_t)132U, (uint8_t)0U,
    (uint8_t)104U, (uint8_t)93U, (uint8_t)112U, (uint8_t)58U, (uint8_t)234U, (uint8_t)108U,
    (uint8_t)92U, (uint8_t)127U
  };

static uint8_t
sigver_vectors512_low30[128U] =
  {
    (uint8_t)253U, (uint8_t)46U, (uint8_t)93U, (uint8_t)228U, (uint8_t)33U, (uint8_t)238U,
    (uint8_t)70U, (uint8_t)201U, (uint8_t)254U, (uint8_t)98U, (uint8_t)144U, (uint8_t)163U,
    (uint8_t)63U, (uint8_t)149U, (uint8_t)179U, (uint8_t)148U, (uint8_t)189U, (uint8_t)91U,
    (uint8_t)119U, (uint8_t)98U, (uint8_t)242U, (uint8_t)49U, (uint8_t)120U, (uint8_t)247U,
    (uint8_t)246U, (uint8_t)131U, (uint8_t)79U, (uint8_t)31U, (uint8_t)5U, (uint8_t)111U,
    (uint8_t)169U, (uint8_t)168U, (uint8_t)131U, (uint8_t)20U, (uint8_t)70U, (uint8_t)64U,
    (uint8_t)60U, (uint8_t)9U, (uint8_t)143U, (uint8_t)244U, (uint8_t)221U, (uint8_t)118U,
    (uint8_t)65U, (uint8_t)115U, (uint8_t)249U, (uint8_t)116U, (uint8_t)190U, (uint8_t)76U,
    (uint8_t)137U, (uint8_t)211U, (uint8_t)118U, (uint8_t)17U, (uint8_t)150U, (uint8_t)19U,
    (uint8_t)164U, (uint8_t)161U, (uint8_t)137U, (uint8_t)15U, (uint8_t)111U, (uint8_t)194U,
    (uint8_t)221U, (uint8_t)255U, (uint8_t)134U, (uint8_t)43U, (uint8_t)218U, (uint8_t)41U,
    (uint8_t)45U, (uint8_t)212U, (uint8_t)159U, (uint8_t)84U, (uint8_t)16U, (uint8_t)217U,
    (uint8_t)177U, (uint8_t)207U, (uint8_t)225U, (uint8_t)217U, (uint8_t)126U, (uint8_t)244U,
    (uint8_t)88U, (uint8_t)43U, (uint8_t)97U, (uint8_t)82U, (uint8_t)73U, (uint8_t)67U,
    (uint8_t)114U, (uint8_t)252U, (uint8_t)8U, (uint8_t)56U, (uint8_t)133U, (uint8_t)245U,
    (uint8_t)64U, (uint8_t)192U, (uint8_t)31U, (uint8_t)134U, (uint8_t)215U, (uint8_t)128U,
    (uint8_t)230U, (uint8_t)243U, (uint8_t)231U, (uint8_t)90U, (uint8_t)149U, (uint8_t)74U,
    (uint8_t)242U, (uint8_t)25U, (uint8_t)15U, (uint8_t)218U, (uint8_t)233U, (uint8_t)96U,
    (uint8_t)78U, (uint8_t)63U, (uint8_t)138U, (uint8_t)179U, (uint8_t)42U, (uint8_t)176U,
    (uint8_t)41U, (uint8_t)45U, (uint8_t)192U, (uint8_t)215U, (uint8_t)144U, (uint8_t)189U,
    (uint8_t)38U, (uint8_t)39U, (uint8_t)227U, (uint8_t)123U, (uint8_t)75U, (uint8_t)72U,
    (uint8_t)133U, (uint8_t)223U
  };

static uint8_t
sigver_vectors512_low31[32U] =
  {
    (uint8_t)99U, (uint8_t)60U, (uint8_t)46U, (uint8_t)229U, (uint8_t)99U, (uint8_t)11U,
    (uint8_t)98U, (uint8_t)201U, (uint8_t)206U, (uint8_t)131U, (uint8_t)158U, (uint8_t)253U,
    (uint8_t)77U, (uint8_t)72U, (uint8_t)90U, (uint8_t)109U, (uint8_t)53U, (uint8_t)232U,
    (uint8_t)185U, (uint8_t)67U, (uint8_t)13U, (uint8_t)38U, (uint8_t)79U, (uint8_t)254U,
    (uint8_t)80U, (uint8_t)29U, (uint8_t)40U, (uint8_t)219U, (uint8_t)172U, (uint8_t)231U,
    (uint8_t)145U, (uint8_t)35U
  };

static uint8_t
sigver_vectors512_low32[32U] =
  {
    (uint8_t)75U, (uint8_t)102U, (uint8_t)138U, (uint8_t)26U, (uint8_t)109U, (uint8_t)26U,
    (uint8_t)37U, (uint8_t)176U, (uint8_t)137U, (uint8_t)247U, (uint8_t)92U, (uint8_t)43U,
    (uint8_t)216U, (uint8_t)216U, (uint8_t)198U, (uint8_t)169U, (uint8_t)161U, (uint8_t)79U,
    (uint8_t)231U, (uint8_t)183U, (uint8_t)41U, (uint8_t)244U, (uint8_t)90U, (uint8_t)130U,
    (uint8_t)86U, (uint8_t)93U, (uint8_t)162U, (uint8_t)232U, (uint8_t)102U, (uint8_t)226U,
    (uint8_t)196U, (uint8_t)144U
  };

static uint8_t
sigver_vectors512_low33[32U] =
  {
    (uint8_t)191U, (uint8_t)33U, (uint8_t)17U, (uint8_t)201U, (uint8_t)62U, (uint8_t)192U,
    (uint8_t)85U, (uint8_t)167U, (uint8_t)237U, (uint8_t)169U, (uint8_t)12U, (uint8_t)16U,
    (uint8_t)111U, (uint8_t)206U, (uint8_t)73U, (uint8_t)79U, (uint8_t)216U, (uint8_t)102U,
    (uint8_t)4U, (uint8_t)86U, (uint8_t)52U, (uint8_t)253U, (uint8_t)42U, (uint8_t)162U,
    (uint8_t)141U, (uint8_t)110U, (uint8_t)1U, (uint8_t)143U, (uint8_t)145U, (uint8_t)6U,
    (uint8_t)153U, (uint8_t)78U
  };

static uint8_t
sigver_vectors512_low34[32U] =
  {
    (uint8_t)134U, (uint8_t)176U, (uint8_t)52U, (uint8_t)18U, (uint8_t)8U, (uint8_t)160U,
    (uint8_t)170U, (uint8_t)85U, (uint8_t)237U, (uint8_t)236U, (uint8_t)253U, (uint8_t)39U,
    (uint8_t)47U, (uint8_t)73U, (uint8_t)203U, (uint8_t)52U, (uint8_t)64U, (uint8_t)140U,
    (uint8_t)229U, (uint8_t)75U, (uint8_t)127U, (uint8_t)235U, (uint8_t)193U, (uint8_t)208U,
    (uint8_t)161U, (uint8_t)194U, (uint8_t)206U, (uint8_t)119U, (uint8_t)171U, (uint8_t)105U,
    (uint8_t)136U, (uint8_t)248U
  };

static uint8_t
sigver_vectors512_low35[128U] =
  {
    (uint8_t)75U, (uint8_t)194U, (uint8_t)217U, (uint8_t)168U, (uint8_t)152U, (uint8_t)57U,
    (uint8_t)91U, (uint8_t)18U, (uint8_t)112U, (uint8_t)22U, (uint8_t)53U, (uint8_t)241U,
    (uint8_t)4U, (uint8_t)143U, (uint8_t)191U, (uint8_t)210U, (uint8_t)99U, (uint8_t)236U,
    (uint8_t)17U, (uint8_t)94U, (uint8_t)65U, (uint8_t)80U, (uint8_t)83U, (uint8_t)43U, (uint8_t)3U,
    (uint8_t)77U, (uint8_t)89U, (uint8_t)230U, (uint8_t)37U, (uint8_t)35U, (uint8_t)143U,
    (uint8_t)78U, (uint8_t)211U, (uint8_t)38U, (uint8_t)25U, (uint8_t)116U, (uint8_t)76U,
    (uint8_t)97U, (uint8_t)46U, (uint8_t)53U, (uint8_t)172U, (uint8_t)90U, (uint8_t)35U,
    (uint8_t)190U, (uint8_t)232U, (uint8_t)213U, (uint8_t)245U, (uint8_t)101U, (uint8_t)22U,
    (uint8_t)65U, (uint8_t)164U, (uint8_t)146U, (uint8_t)33U, (uint8_t)125U, (uint8_t)48U,
    (uint8_t)94U, (uint8_t)80U, (uint8_t)81U, (uint8_t)50U, (uint8_t)28U, (uint8_t)39U,
    (uint8_t)54U, (uint8_t)71U, (uint8_t)241U, (uint8_t)75U, (uint8_t)199U, (uint8_t)196U,
    (uint8_t)175U, (uint8_t)171U, (uint8_t)81U, (uint8_t)133U, (uint8_t)84U, (uint8_t)224U,
    (uint8_t)28U, (uint8_t)130U, (uint8_t)214U, (uint8_t)252U, (uint8_t)22U, (uint8_t)148U,
    (uint8_t)200U, (uint8_t)189U, (uint8_t)190U, (uint8_t)179U, (uint8_t)38U, (uint8_t)187U,
    (uint8_t)96U, (uint8_t)123U, (uint8_t)202U, (uint8_t)245U, (uint8_t)67U, (uint8_t)99U,
    (uint8_t)3U, (uint8_t)188U, (uint8_t)9U, (uint8_t)246U, (uint8_t)76U, (uint8_t)2U,
    (uint8_t)198U, (uint8_t)236U, (uint8_t)80U, (uint8_t)222U, (uint8_t)64U, (uint8_t)154U,
    (uint8_t)72U, (uint8_t)79U, (uint8_t)82U, (uint8_t)55U, (uint8_t)247U, (uint8_t)211U,
    (uint8_t)78U, (uint8_t)38U, (uint8_t)81U, (uint8_t)173U, (uint8_t)167U, (uint8_t)236U,
    (uint8_t)66U, (uint8_t)156U, (uint8_t)163U, (uint8_t)185U, (uint8_t)157U, (uint8_t)216U,
    (uint8_t)124U, (uint8_t)96U, (uint8_t)21U, (uint8_t)210U, (uint8_t)244U, (uint8_t)179U,
    (uint8_t)66U
  };

static uint8_t
sigver_vectors512_low36[32U] =
  {
    (uint8_t)247U, (uint8_t)141U, (uint8_t)206U, (uint8_t)64U, (uint8_t)209U, (uint8_t)203U,
    (uint8_t)140U, (uint8_t)74U, (uint8_t)242U, (uint8_t)116U, (uint8_t)155U, (uint8_t)242U,
    (uint8_t)44U, (uint8_t)111U, (uint8_t)138U, (uint8_t)154U, (uint8_t)71U, (uint8_t)11U,
    (uint8_t)30U, (uint8_t)65U, (uint8_t)17U, (uint8_t)39U, (uint8_t)150U, (uint8_t)33U,
    (uint8_t)93U, (uint8_t)208U, (uint8_t)23U, (uint8_t)229U, (uint8_t)125U, (uint8_t)241U,
    (uint8_t)179U, (uint8_t)138U
  };

static uint8_t
sigver_vectors512_low37[32U] =
  {
    (uint8_t)97U, (uint8_t)178U, (uint8_t)155U, (uint8_t)11U, (uint8_t)192U, (uint8_t)61U,
    (uint8_t)255U, (uint8_t)127U, (uint8_t)160U, (uint8_t)6U, (uint8_t)19U, (uint8_t)180U,
    (uint8_t)222U, (uint8_t)30U, (uint8_t)35U, (uint8_t)23U, (uint8_t)207U, (uint8_t)191U,
    (uint8_t)43U, (uint8_t)173U, (uint8_t)213U, (uint8_t)13U, (uint8_t)238U, (uint8_t)51U,
    (uint8_t)118U, (uint8_t)192U, (uint8_t)50U, (uint8_t)168U, (uint8_t)135U, (uint8_t)197U,
    (uint8_t)184U, (uint8_t)101U
  };

static uint8_t
sigver_vectors512_low38[32U] =
  {
    (uint8_t)74U, (uint8_t)150U, (uint8_t)22U, (uint8_t)154U, (uint8_t)93U, (uint8_t)234U,
    (uint8_t)54U, (uint8_t)162U, (uint8_t)89U, (uint8_t)64U, (uint8_t)17U, (uint8_t)83U,
    (uint8_t)126U, (uint8_t)224U, (uint8_t)220U, (uint8_t)25U, (uint8_t)232U, (uint8_t)249U,
    (uint8_t)247U, (uint8_t)78U, (uint8_t)130U, (uint8_t)192U, (uint8_t)116U, (uint8_t)52U,
    (uint8_t)7U, (uint8_t)148U, (uint8_t)71U, (uint8_t)21U, (uint8_t)90U, (uint8_t)131U,
    (uint8_t)1U, (uint8_t)82U
  };

static uint8_t
sigver_vectors512_low39[32U] =
  {
    (uint8_t)162U, (uint8_t)4U, (uint8_t)234U, (uint8_t)164U, (uint8_t)233U, (uint8_t)125U,
    (uint8_t)117U, (uint8_t)83U, (uint8_t)161U, (uint8_t)82U, (uint8_t)29U, (uint8_t)159U,
    (uint8_t)107U, (uint8_t)170U, (uint8_t)220U, (uint8_t)11U, (uint8_t)109U, (uint8_t)97U,
    (uint8_t)131U, (uint8_t)186U, (uint8_t)15U, (uint8_t)56U, (uint8_t)93U, (uint8_t)133U,
    (uint8_t)147U, (uint8_t)214U, (uint8_t)202U, (uint8_t)131U, (uint8_t)96U, (uint8_t)124U,
    (uint8_t)77U, (uint8_t)130U
  };

static uint8_t
sigver_vectors512_low40[128U] =
  {
    (uint8_t)211U, (uint8_t)53U, (uint8_t)106U, (uint8_t)104U, (uint8_t)52U, (uint8_t)23U,
    (uint8_t)80U, (uint8_t)138U, (uint8_t)155U, (uint8_t)145U, (uint8_t)54U, (uint8_t)67U,
    (uint8_t)230U, (uint8_t)206U, (uint8_t)172U, (uint8_t)18U, (uint8_t)129U, (uint8_t)239U,
    (uint8_t)88U, (uint8_t)63U, (uint8_t)66U, (uint8_t)137U, (uint8_t)104U, (uint8_t)249U,
    (uint8_t)210U, (uint8_t)182U, (uint8_t)84U, (uint8_t)10U, (uint8_t)24U, (uint8_t)157U,
    (uint8_t)112U, (uint8_t)65U, (uint8_t)196U, (uint8_t)119U, (uint8_t)218U, (uint8_t)141U,
    (uint8_t)32U, (uint8_t)125U, (uint8_t)5U, (uint8_t)41U, (uint8_t)114U, (uint8_t)15U,
    (uint8_t)112U, (uint8_t)218U, (uint8_t)182U, (uint8_t)176U, (uint8_t)218U, (uint8_t)140U,
    (uint8_t)33U, (uint8_t)104U, (uint8_t)131U, (uint8_t)116U, (uint8_t)118U, (uint8_t)193U,
    (uint8_t)198U, (uint8_t)182U, (uint8_t)59U, (uint8_t)81U, (uint8_t)126U, (uint8_t)211U,
    (uint8_t)202U, (uint8_t)212U, (uint8_t)138U, (uint8_t)227U, (uint8_t)49U, (uint8_t)207U,
    (uint8_t)113U, (uint8_t)110U, (uint8_t)207U, (uint8_t)71U, (uint8_t)160U, (uint8_t)247U,
    (uint8_t)208U, (uint8_t)11U, (uint8_t)87U, (uint8_t)7U, (uint8_t)58U, (uint8_t)198U,
    (uint8_t)164U, (uint8_t)116U, (uint8_t)151U, (uint8_t)22U, (uint8_t)212U, (uint8_t)157U,
    (uint8_t)128U, (uint8_t)196U, (uint8_t)212U, (uint8_t)98U, (uint8_t)97U, (uint8_t)211U,
    (uint8_t)142U, (uint8_t)46U, (uint8_t)52U, (uint8_t)180U, (uint8_t)244U, (uint8_t)62U,
    (uint8_t)15U, (uint8_t)32U, (uint8_t)178U, (uint8_t)128U, (uint8_t)132U, (uint8_t)47U,
    (uint8_t)110U, (uint8_t)62U, (uint8_t)163U, (uint8_t)79U, (uint8_t)239U, (uint8_t)221U,
    (uint8_t)223U, (uint8_t)185U, (uint8_t)250U, (uint8_t)42U, (uint8_t)4U, (uint8_t)15U,
    (uint8_t)254U, (uint8_t)145U, (uint8_t)94U, (uint8_t)135U, (uint8_t)132U, (uint8_t)207U,
    (uint8_t)219U, (uint8_t)41U, (uint8_t)179U, (uint8_t)54U, (uint8_t)74U, (uint8_t)52U,
    (uint8_t)202U, (uint8_t)98U
  };

static uint8_t
sigver_vectors512_low41[32U] =
  {
    (uint8_t)63U, (uint8_t)204U, (uint8_t)59U, (uint8_t)62U, (uint8_t)27U, (uint8_t)16U,
    (uint8_t)63U, (uint8_t)228U, (uint8_t)53U, (uint8_t)172U, (uint8_t)33U, (uint8_t)76U,
    (uint8_t)117U, (uint8_t)107U, (uint8_t)218U, (uint8_t)173U, (uint8_t)48U, (uint8_t)147U,
    (uint8_t)137U, (uint8_t)225U, (uint8_t)200U, (uint8_t)3U, (uint8_t)230U, (uint8_t)216U,
    (uint8_t)75U, (uint8_t)187U, (uint8_t)194U, (uint8_t)112U, (uint8_t)57U, (uint8_t)252U,
    (uint8_t)249U
  };

static uint8_t
sigver_vectors512_low42[32U] =
  {
    (uint8_t)127U, (uint8_t)9U, (uint8_t)237U, (uint8_t)209U, (uint8_t)236U, (uint8_t)135U,
    (uint8_t)166U, (uint8_t)211U, (uint8_t)109U, (uint8_t)200U, (uint8_t)28U, (uint8_t)21U,
    (uint8_t)40U, (uint8_t)213U, (uint8_t)42U, (uint8_t)98U, (uint8_t)119U, (uint8_t)110U,
    (uint8_t)102U, (uint8_t)108U, (uint8_t)39U, (uint8_t)68U, (uint8_t)21U, (uint8_t)169U,
    (uint8_t)244U, (uint8_t)65U, (uint8_t)214U, (uint8_t)168U, (uint8_t)223U, (uint8_t)107U,
    (uint8_t)146U, (uint8_t)55U
  };

static uint8_t
sigver_vectors512_low43[32U] =
  {
    (uint8_t)28U, (uint8_t)172U, (uint8_t)19U, (uint8_t)242U, (uint8_t)119U, (uint8_t)53U,
    (uint8_t)68U, (uint8_t)86U, (uint8_t)174U, (uint8_t)103U, (uint8_t)171U, (uint8_t)9U,
    (uint8_t)176U, (uint8_t)158U, (uint8_t)7U, (uint8_t)235U, (uint8_t)26U, (uint8_t)242U,
    (uint8_t)162U, (uint8_t)191U, (uint8_t)69U, (uint8_t)16U, (uint8_t)141U, (uint8_t)167U,
    (uint8_t)15U, (uint8_t)92U, (uint8_t)140U, (uint8_t)106U, (uint8_t)76U, (uint8_t)188U,
    (uint8_t)213U, (uint8_t)56U
  };

static uint8_t
sigver_vectors512_low44[32U] =
  {
    (uint8_t)93U, (uint8_t)131U, (uint8_t)117U, (uint8_t)46U, (uint8_t)84U, (uint8_t)5U,
    (uint8_t)37U, (uint8_t)96U, (uint8_t)43U, (uint8_t)167U, (uint8_t)230U, (uint8_t)254U,
    (uint8_t)228U, (uint8_t)212U, (uint8_t)38U, (uint8_t)63U, (uint8_t)62U, (uint8_t)218U,
    (uint8_t)89U, (uint8_t)230U, (uint8_t)125U, (uint8_t)242U, (uint8_t)10U, (uint8_t)172U,
    (uint8_t)121U, (uint8_t)202U, (uint8_t)103U, (uint8_t)232U, (uint8_t)137U, (uint8_t)159U,
    (uint8_t)237U, (uint8_t)13U
  };

static uint8_t
sigver_vectors512_low45[128U] =
  {
    (uint8_t)215U, (uint8_t)245U, (uint8_t)218U, (uint8_t)159U, (uint8_t)76U, (uint8_t)249U,
    (uint8_t)41U, (uint8_t)155U, (uint8_t)127U, (uint8_t)134U, (uint8_t)197U, (uint8_t)43U,
    (uint8_t)136U, (uint8_t)54U, (uint8_t)76U, (uint8_t)226U, (uint8_t)143U, (uint8_t)233U,
    (uint8_t)173U, (uint8_t)165U, (uint8_t)93U, (uint8_t)213U, (uint8_t)81U, (uint8_t)161U,
    (uint8_t)1U, (uint8_t)135U, (uint8_t)144U, (uint8_t)249U, (uint8_t)225U, (uint8_t)32U,
    (uint8_t)94U, (uint8_t)36U, (uint8_t)5U, (uint8_t)172U, (uint8_t)98U, (uint8_t)66U,
    (uint8_t)157U, (uint8_t)101U, (uint8_t)9U, (uint8_t)63U, (uint8_t)116U, (uint8_t)236U,
    (uint8_t)53U, (uint8_t)161U, (uint8_t)109U, (uint8_t)159U, (uint8_t)25U, (uint8_t)92U,
    (uint8_t)153U, (uint8_t)60U, (uint8_t)212U, (uint8_t)235U, (uint8_t)141U, (uint8_t)192U,
    (uint8_t)170U, (uint8_t)13U, (uint8_t)171U, (uint8_t)183U, (uint8_t)10U, (uint8_t)80U,
    (uint8_t)51U, (uint8_t)33U, (uint8_t)216U, (uint8_t)169U, (uint8_t)100U, (uint8_t)145U,
    (uint8_t)96U, (uint8_t)214U, (uint8_t)179U, (uint8_t)208U, (uint8_t)160U, (uint8_t)133U,
    (uint8_t)75U, (uint8_t)182U, (uint8_t)140U, (uint8_t)76U, (uint8_t)57U, (uint8_t)105U,
    (uint8_t)63U, (uint8_t)89U, (uint8_t)46U, (uint8_t)245U, (uint8_t)221U, (uint8_t)71U,
    (uint8_t)138U, (uint8_t)162U, (uint8_t)67U, (uint8_t)45U, (uint8_t)8U, (uint8_t)101U,
    (uint8_t)216U, (uint8_t)125U, (uint8_t)72U, (uint8_t)179U, (uint8_t)174U, (uint8_t)169U,
    (uint8_t)199U, (uint8_t)215U, (uint8_t)209U, (uint8_t)20U, (uint8_t)22U, (uint8_t)92U,
    (uint8_t)146U, (uint8_t)0U, (uint8_t)228U, (uint8_t)232U, (uint8_t)215U, (uint8_t)189U,
    (uint8_t)2U, (uint8_t)167U, (uint8_t)137U, (uint8_t)94U, (uint8_t)196U, (uint8_t)65U,
    (uint8_t)142U, (uint8_t)111U, (uint8_t)47U, (uint8_t)237U, (uint8_t)107U, (uint8_t)36U,
    (uint8_t)75U, (uint8_t)246U, (uint8_t)98U, (uint8_t)9U, (uint8_t)3U, (uint8_t)158U,
    (uint8_t)152U, (uint8_t)169U
  };

static uint8_t
sigver_vectors512_low46[32U] =
  {
    (uint8_t)94U, (uint8_t)199U, (uint8_t)2U, (uint8_t)212U, (uint8_t)58U, (uint8_t)103U,
    (uint8_t)173U, (uint8_t)168U, (uint8_t)110U, (uint8_t)251U, (uint8_t)252U, (uint8_t)19U,
    (uint8_t)108U, (uint8_t)241U, (uint8_t)109U, (uint8_t)150U, (uint8_t)7U, (uint8_t)137U,
    (uint8_t)6U, (uint8_t)149U, (uint8_t)74U, (uint8_t)63U, (uint8_t)31U, (uint8_t)158U,
    (uint8_t)68U, (uint8_t)6U, (uint8_t)116U, (uint8_t)205U, (uint8_t)144U, (uint8_t)126U,
    (uint8_t)70U, (uint8_t)118U
  };

static uint8_t
sigver_vectors512_low47[32U] =
  {
    (uint8_t)5U, (uint8_t)166U, (uint8_t)32U, (uint8_t)68U, (uint8_t)254U, (uint8_t)216U,
    (uint8_t)71U, (uint8_t)13U, (uint8_t)212U, (uint8_t)252U, (uint8_t)163U, (uint8_t)141U,
    (uint8_t)137U, (uint8_t)213U, (uint8_t)131U, (uint8_t)206U, (uint8_t)54U, (uint8_t)213U,
    (uint8_t)13U, (uint8_t)40U, (uint8_t)182U, (uint8_t)106U, (uint8_t)176U, (uint8_t)181U,
    (uint8_t)25U, (uint8_t)34U, (uint8_t)178U, (uint8_t)29U, (uint8_t)169U, (uint8_t)44U,
    (uint8_t)86U, (uint8_t)217U
  };

static uint8_t
sigver_vectors512_low48[32U] =
  {
    (uint8_t)117U, (uint8_t)243U, (uint8_t)3U, (uint8_t)114U, (uint8_t)152U, (uint8_t)241U,
    (uint8_t)69U, (uint8_t)125U, (uint8_t)186U, (uint8_t)85U, (uint8_t)116U, (uint8_t)57U,
    (uint8_t)153U, (uint8_t)151U, (uint8_t)106U, (uint8_t)28U, (uint8_t)38U, (uint8_t)54U,
    (uint8_t)178U, (uint8_t)184U, (uint8_t)171U, (uint8_t)46U, (uint8_t)211U, (uint8_t)223U,
    (uint8_t)71U, (uint8_t)54U, (uint8_t)166U, (uint8_t)210U, (uint8_t)147U, (uint8_t)74U,
    (uint8_t)204U, (uint8_t)131U
  };

static uint8_t
sigver_vectors512_low49[32U] =
  {
    (uint8_t)25U, (uint8_t)212U, (uint8_t)58U, (uint8_t)209U, (uint8_t)104U, (uint8_t)221U,
    (uint8_t)161U, (uint8_t)187U, (uint8_t)138U, (uint8_t)196U, (uint8_t)35U, (uint8_t)248U,
    (uint8_t)240U, (uint8_t)136U, (uint8_t)118U, (uint8_t)81U, (uint8_t)82U, (uint8_t)52U,
    (uint8_t)179U, (uint8_t)216U, (uint8_t)65U, (uint8_t)229U, (uint8_t)127U, (uint8_t)174U,
    (uint8_t)241U, (uint8_t)181U, (uint8_t)171U, (uint8_t)39U, (uint8_t)53U, (uint8_t)155U,
    (uint8_t)39U, (uint8_t)239U
  };

static uint8_t
sigver_vectors512_low50[128U] =
  {
    (uint8_t)104U, (uint8_t)244U, (uint8_t)180U, (uint8_t)68U, (uint8_t)225U, (uint8_t)204U,
    (uint8_t)32U, (uint8_t)37U, (uint8_t)232U, (uint8_t)255U, (uint8_t)85U, (uint8_t)232U,
    (uint8_t)4U, (uint8_t)110U, (uint8_t)173U, (uint8_t)115U, (uint8_t)94U, (uint8_t)110U,
    (uint8_t)49U, (uint8_t)112U, (uint8_t)130U, (uint8_t)237U, (uint8_t)247U, (uint8_t)206U,
    (uint8_t)101U, (uint8_t)232U, (uint8_t)53U, (uint8_t)115U, (uint8_t)80U, (uint8_t)28U,
    (uint8_t)185U, (uint8_t)44U, (uint8_t)64U, (uint8_t)140U, (uint8_t)28U, (uint8_t)28U,
    (uint8_t)108U, (uint8_t)79U, (uint8_t)204U, (uint8_t)166U, (uint8_t)185U, (uint8_t)106U,
    (uint8_t)211U, (uint8_t)66U, (uint8_t)36U, (uint8_t)241U, (uint8_t)123U, (uint8_t)32U,
    (uint8_t)190U, (uint8_t)71U, (uint8_t)28U, (uint8_t)201U, (uint8_t)244U, (uint8_t)249U,
    (uint8_t)127U, (uint8_t)10U, (uint8_t)91U, (uint8_t)123U, (uint8_t)250U, (uint8_t)233U,
    (uint8_t)85U, (uint8_t)139U, (uint8_t)219U, (uint8_t)46U, (uint8_t)203U, (uint8_t)110U,
    (uint8_t)69U, (uint8_t)43U, (uint8_t)183U, (uint8_t)67U, (uint8_t)96U, (uint8_t)55U,
    (uint8_t)36U, (uint8_t)39U, (uint8_t)61U, (uint8_t)158U, (uint8_t)141U, (uint8_t)44U,
    (uint8_t)162U, (uint8_t)42U, (uint8_t)253U, (uint8_t)218U, (uint8_t)53U, (uint8_t)200U,
    (uint8_t)163U, (uint8_t)113U, (uint8_t)178U, (uint8_t)129U, (uint8_t)83U, (uint8_t)215U,
    (uint8_t)114U, (uint8_t)48U, (uint8_t)62U, (uint8_t)74U, (uint8_t)37U, (uint8_t)220U,
    (uint8_t)79U, (uint8_t)40U, (uint8_t)233U, (uint8_t)166U, (uint8_t)220U, (uint8_t)150U,
    (uint8_t)53U, (uint8_t)51U, (uint8_t)20U, (uint8_t)80U, (uint8_t)245U, (uint8_t)175U,
    (uint8_t)41U, (uint8_t)13U, (uint8_t)250U, (uint8_t)52U, (uint8_t)49U, (uint8_t)195U,
    (uint8_t)192U, (uint8_t)139U, (uint8_t)145U, (uint8_t)213U, (uint8_t)201U, (uint8_t)114U,
    (uint8_t)132U, (uint8_t)54U, (uint8_t)28U, (uint8_t)3U, (uint8_t)236U, (uint8_t)120U,
    (uint8_t)241U, (uint8_t)188U
  };

static uint8_t
sigver_vectors512_low51[32U] =
  {
    (uint8_t)246U, (uint8_t)58U, (uint8_t)254U, (uint8_t)153U, (uint8_t)225U, (uint8_t)181U,
    (uint8_t)252U, (uint8_t)101U, (uint8_t)39U, (uint8_t)130U, (uint8_t)248U, (uint8_t)107U,
    (uint8_t)89U, (uint8_t)146U, (uint8_t)106U, (uint8_t)242U, (uint8_t)46U, (uint8_t)96U,
    (uint8_t)114U, (uint8_t)190U, (uint8_t)147U, (uint8_t)57U, (uint8_t)15U, (uint8_t)228U,
    (uint8_t)31U, (uint8_t)84U, (uint8_t)18U, (uint8_t)4U, (uint8_t)249U, (uint8_t)201U,
    (uint8_t)53U, (uint8_t)209U
  };

static uint8_t
sigver_vectors512_low52[32U] =
  {
    (uint8_t)246U, (uint8_t)225U, (uint8_t)156U, (uint8_t)229U, (uint8_t)147U, (uint8_t)94U,
    (uint8_t)51U, (uint8_t)97U, (uint8_t)131U, (uint8_t)194U, (uint8_t)27U, (uint8_t)236U,
    (uint8_t)246U, (uint8_t)101U, (uint8_t)150U, (uint8_t)184U, (uint8_t)245U, (uint8_t)89U,
    (uint8_t)210U, (uint8_t)208U, (uint8_t)46U, (uint8_t)226U, (uint8_t)130U, (uint8_t)170U,
    (uint8_t)135U, (uint8_t)167U, (uint8_t)214U, (uint8_t)249U, (uint8_t)54U, (uint8_t)247U,
    (uint8_t)38U, (uint8_t)12U
  };

static uint8_t
sigver_vectors512_low53[32U] =
  {
    (uint8_t)206U, (uint8_t)244U, (uint8_t)131U, (uint8_t)30U, (uint8_t)69U, (uint8_t)21U,
    (uint8_t)199U, (uint8_t)124U, (uint8_t)160U, (uint8_t)98U, (uint8_t)40U, (uint8_t)38U,
    (uint8_t)20U, (uint8_t)181U, (uint8_t)74U, (uint8_t)17U, (uint8_t)183U, (uint8_t)220U,
    (uint8_t)64U, (uint8_t)87U, (uint8_t)230U, (uint8_t)153U, (uint8_t)118U, (uint8_t)133U,
    (uint8_t)194U, (uint8_t)251U, (uint8_t)250U, (uint8_t)149U, (uint8_t)179U, (uint8_t)146U,
    (uint8_t)191U, (uint8_t)114U
  };

static uint8_t
sigver_vectors512_low54[32U] =
  {
    (uint8_t)242U, (uint8_t)13U, (uint8_t)192U, (uint8_t)27U, (uint8_t)243U, (uint8_t)142U,
    (uint8_t)19U, (uint8_t)68U, (uint8_t)186U, (uint8_t)103U, (uint8_t)90U, (uint8_t)34U,
    (uint8_t)35U, (uint8_t)157U, (uint8_t)152U, (uint8_t)147U, (uint8_t)179U, (uint8_t)163U,
    (uint8_t)227U, (uint8_t)61U, (uint8_t)154U, (uint8_t)64U, (uint8_t)51U, (uint8_t)41U,
    (uint8_t)163U, (uint8_t)210U, (uint8_t)22U, (uint8_t)80U, (uint8_t)233U, (uint8_t)18U,
    (uint8_t)91U, (uint8_t)117U
  };

static uint8_t
sigver_vectors512_low55[128U] =
  {
    (uint8_t)231U, (uint8_t)91U, (uint8_t)224U, (uint8_t)91U, (uint8_t)224U, (uint8_t)170U,
    (uint8_t)247U, (uint8_t)7U, (uint8_t)25U, (uint8_t)180U, (uint8_t)136U, (uint8_t)184U,
    (uint8_t)154U, (uint8_t)170U, (uint8_t)233U, (uint8_t)0U, (uint8_t)135U, (uint8_t)7U,
    (uint8_t)202U, (uint8_t)82U, (uint8_t)137U, (uint8_t)148U, (uint8_t)70U, (uint8_t)29U,
    (uint8_t)183U, (uint8_t)19U, (uint8_t)12U, (uint8_t)67U, (uint8_t)104U, (uint8_t)87U,
    (uint8_t)90U, (uint8_t)2U, (uint8_t)75U, (uint8_t)240U, (uint8_t)152U, (uint8_t)28U,
    (uint8_t)48U, (uint8_t)93U, (uint8_t)97U, (uint8_t)38U, (uint8_t)94U, (uint8_t)139U,
    (uint8_t)151U, (uint8_t)89U, (uint8_t)158U, (uint8_t)195U, (uint8_t)92U, (uint8_t)3U,
    (uint8_t)186U, (uint8_t)221U, (uint8_t)18U, (uint8_t)86U, (uint8_t)184U, (uint8_t)13U,
    (uint8_t)107U, (uint8_t)247U, (uint8_t)5U, (uint8_t)71U, (uint8_t)173U, (uint8_t)96U,
    (uint8_t)137U, (uint8_t)185U, (uint8_t)131U, (uint8_t)227U, (uint8_t)188U, (uint8_t)195U,
    (uint8_t)72U, (uint8_t)24U, (uint8_t)40U, (uint8_t)243U, (uint8_t)37U, (uint8_t)158U,
    (uint8_t)67U, (uint8_t)230U, (uint8_t)85U, (uint8_t)225U, (uint8_t)119U, (uint8_t)252U,
    (uint8_t)66U, (uint8_t)63U, (uint8_t)215U, (uint8_t)224U, (uint8_t)102U, (uint8_t)189U,
    (uint8_t)62U, (uint8_t)214U, (uint8_t)141U, (uint8_t)129U, (uint8_t)223U, (uint8_t)132U,
    (uint8_t)247U, (uint8_t)115U, (uint8_t)192U, (uint8_t)249U, (uint8_t)229U, (uint8_t)248U,
    (uint8_t)191U, (uint8_t)68U, (uint8_t)105U, (uint8_t)150U, (uint8_t)11U, (uint8_t)139U,
    (uint8_t)77U, (uint8_t)123U, (uint8_t)42U, (uint8_t)55U, (uint8_t)47U, (uint8_t)208U,
    (uint8_t)237U, (uint8_t)211U, (uint8_t)82U, (uint8_t)31U, (uint8_t)107U, (uint8_t)230U,
    (uint8_t)112U, (uint8_t)144U, (uint8_t)143U, (uint8_t)45U, (uint8_t)144U, (uint8_t)163U,
    (uint8_t)67U, (uint8_t)244U, (uint8_t)22U, (uint8_t)53U, (uint8_t)142U, (uint8_t)167U,
    (uint8_t)14U, (uint8_t)126U
  };

static uint8_t
sigver_vectors512_low56[32U] =
  {
    (uint8_t)109U, (uint8_t)17U, (uint8_t)176U, (uint8_t)157U, (uint8_t)39U, (uint8_t)103U,
    (uint8_t)207U, (uint8_t)141U, (uint8_t)39U, (uint8_t)95U, (uint8_t)174U, (uint8_t)231U,
    (uint8_t)70U, (uint8_t)194U, (uint8_t)3U, (uint8_t)72U, (uint8_t)98U, (uint8_t)89U,
    (uint8_t)246U, (uint8_t)109U, (uint8_t)210U, (uint8_t)191U, (uint8_t)163U, (uint8_t)166U,
    (uint8_t)92U, (uint8_t)57U, (uint8_t)55U, (uint8_t)26U, (uint8_t)102U, (uint8_t)178U,
    (uint8_t)51U, (uint8_t)133U
  };

static uint8_t
sigver_vectors512_low57[32U] =
  {
    (uint8_t)78U, (uint8_t)176U, (uint8_t)92U, (uint8_t)115U, (uint8_t)224U, (uint8_t)82U,
    (uint8_t)97U, (uint8_t)233U, (uint8_t)121U, (uint8_t)24U, (uint8_t)40U, (uint8_t)51U,
    (uint8_t)242U, (uint8_t)3U, (uint8_t)17U, (uint8_t)229U, (uint8_t)54U, (uint8_t)111U,
    (uint8_t)114U, (uint8_t)244U, (uint8_t)185U, (uint8_t)73U, (uint8_t)102U, (uint8_t)95U,
    (uint8_t)242U, (uint8_t)148U, (uint8_t)249U, (uint8_t)89U, (uint8_t)55U, (uint8_t)85U,
    (uint8_t)52U, (uint8_t)198U
  };

static uint8_t
sigver_vectors512_low58[32U] =
  {
    (uint8_t)21U, (uint8_t)166U, (uint8_t)151U, (uint8_t)205U, (uint8_t)182U, (uint8_t)20U,
    (uint8_t)225U, (uint8_t)28U, (uint8_t)8U, (uint8_t)16U, (uint8_t)225U, (uint8_t)231U,
    (uint8_t)100U, (uint8_t)205U, (uint8_t)80U, (uint8_t)31U, (uint8_t)202U, (uint8_t)188U,
    (uint8_t)112U, (uint8_t)135U, (uint8_t)76U, (uint8_t)149U, (uint8_t)117U, (uint8_t)135U,
    (uint8_t)188U, (uint8_t)72U, (uint8_t)131U, (uint8_t)217U, (uint8_t)67U, (uint8_t)142U,
    (uint8_t)23U, (uint8_t)127U
  };

static uint8_t
sigver_vectors512_low59[32U] =
  {
    (uint8_t)123U, (uint8_t)246U, (uint8_t)36U, (uint8_t)79U, (uint8_t)146U, (uint8_t)188U,
    (uint8_t)118U, (uint8_t)128U, (uint8_t)99U, (uint8_t)206U, (uint8_t)203U, (uint8_t)83U,
    (uint8_t)54U, (uint8_t)200U, (uint8_t)234U, (uint8_t)172U, (uint8_t)210U, (uint8_t)61U,
    (uint8_t)185U, (uint8_t)48U, (uint8_t)178U, (uint8_t)135U, (uint8_t)3U, (uint8_t)86U,
    (uint8_t)15U, (uint8_t)36U, (uint8_t)28U, (uint8_t)125U, (uint8_t)147U, (uint8_t)149U,
    (uint8_t)13U, (uint8_t)253U
  };

static uint8_t
sigver_vectors512_low60[128U] =
  {
    (uint8_t)13U, (uint8_t)196U, (uint8_t)163U, (uint8_t)234U, (uint8_t)182U, (uint8_t)107U,
    (uint8_t)210U, (uint8_t)231U, (uint8_t)3U, (uint8_t)168U, (uint8_t)255U, (uint8_t)245U,
    (uint8_t)102U, (uint8_t)195U, (uint8_t)77U, (uint8_t)70U, (uint8_t)111U, (uint8_t)152U,
    (uint8_t)35U, (uint8_t)174U, (uint8_t)66U, (uint8_t)189U, (uint8_t)33U, (uint8_t)4U,
    (uint8_t)246U, (uint8_t)26U, (uint8_t)107U, (uint8_t)5U, (uint8_t)28U, (uint8_t)11U,
    (uint8_t)1U, (uint8_t)120U, (uint8_t)51U, (uint8_t)252U, (uint8_t)239U, (uint8_t)77U,
    (uint8_t)96U, (uint8_t)157U, (uint8_t)19U, (uint8_t)122U, (uint8_t)217U, (uint8_t)124U,
    (uint8_t)32U, (uint8_t)156U, (uint8_t)128U, (uint8_t)238U, (uint8_t)190U, (uint8_t)37U,
    (uint8_t)40U, (uint8_t)87U, (uint8_t)170U, (uint8_t)127U, (uint8_t)175U, (uint8_t)195U,
    (uint8_t)95U, (uint8_t)22U, (uint8_t)0U, (uint8_t)10U, (uint8_t)43U, (uint8_t)212U,
    (uint8_t)180U, (uint8_t)190U, (uint8_t)15U, (uint8_t)168U, (uint8_t)59U, (uint8_t)110U,
    (uint8_t)34U, (uint8_t)158U, (uint8_t)221U, (uint8_t)253U, (uint8_t)24U, (uint8_t)1U,
    (uint8_t)1U, (uint8_t)241U, (uint8_t)244U, (uint8_t)13U, (uint8_t)4U, (uint8_t)83U,
    (uint8_t)20U, (uint8_t)128U, (uint8_t)83U, (uint8_t)216U, (uint8_t)48U, (uint8_t)104U,
    (uint8_t)51U, (uint8_t)223U, (uint8_t)100U, (uint8_t)213U, (uint8_t)149U, (uint8_t)153U,
    (uint8_t)185U, (uint8_t)1U, (uint8_t)148U, (uint8_t)181U, (uint8_t)85U, (uint8_t)65U,
    (uint8_t)215U, (uint8_t)242U, (uint8_t)45U, (uint8_t)213U, (uint8_t)137U, (uint8_t)218U,
    (uint8_t)159U, (uint8_t)123U, (uint8_t)229U, (uint8_t)25U, (uint8_t)203U, (uint8_t)187U,
    (uint8_t)157U, (uint8_t)180U, (uint8_t)22U, (uint8_t)199U, (uint8_t)27U, (uint8_t)254U,
    (uint8_t)64U, (uint8_t)236U, (uint8_t)9U, (uint8_t)11U, (uint8_t)91U, (uint8_t)122U,
    (uint8_t)96U, (uint8_t)14U, (uint8_t)236U, (uint8_t)41U, (uint8_t)191U, (uint8_t)212U,
    (uint8_t)115U, (uint8_t)6U
  };

static uint8_t
sigver_vectors512_low61[32U] =
  {
    (uint8_t)243U, (uint8_t)137U, (uint8_t)156U, (uint8_t)171U, (uint8_t)160U, (uint8_t)56U,
    (uint8_t)239U, (uint8_t)181U, (uint8_t)52U, (uint8_t)196U, (uint8_t)206U, (uint8_t)160U,
    (uint8_t)189U, (uint8_t)39U, (uint8_t)104U, (uint8_t)20U, (uint8_t)255U, (uint8_t)216U,
    (uint8_t)1U, (uint8_t)148U, (uint8_t)71U, (uint8_t)60U, (uint8_t)144U, (uint8_t)59U,
    (uint8_t)129U, (uint8_t)175U, (uint8_t)17U, (uint8_t)200U, (uint8_t)192U, (uint8_t)92U,
    (uint8_t)182U, (uint8_t)230U
  };

static uint8_t
sigver_vectors512_low62[32U] =
  {
    (uint8_t)110U, (uint8_t)166U, (uint8_t)177U, (uint8_t)116U, (uint8_t)2U, (uint8_t)252U,
    (uint8_t)242U, (uint8_t)232U, (uint8_t)231U, (uint8_t)55U, (uint8_t)209U, (uint8_t)31U,
    (uint8_t)252U, (uint8_t)124U, (uint8_t)46U, (uint8_t)211U, (uint8_t)178U, (uint8_t)208U,
    (uint8_t)188U, (uint8_t)59U, (uint8_t)143U, (uint8_t)39U, (uint8_t)26U, (uint8_t)56U,
    (uint8_t)31U, (uint8_t)66U, (uint8_t)148U, (uint8_t)207U, (uint8_t)246U, (uint8_t)38U,
    (uint8_t)130U, (uint8_t)195U
  };

static uint8_t
sigver_vectors512_low63[32U] =
  {
    (uint8_t)87U, (uint8_t)185U, (uint8_t)147U, (uint8_t)128U, (uint8_t)69U, (uint8_t)46U,
    (uint8_t)29U, (uint8_t)55U, (uint8_t)177U, (uint8_t)51U, (uint8_t)196U, (uint8_t)155U,
    (uint8_t)155U, (uint8_t)164U, (uint8_t)147U, (uint8_t)222U, (uint8_t)232U, (uint8_t)99U,
    (uint8_t)9U, (uint8_t)64U, (uint8_t)71U, (uint8_t)124U, (uint8_t)163U, (uint8_t)53U,
    (uint8_t)26U, (uint8_t)67U, (uint8_t)217U, (uint8_t)11U, (uint8_t)153U, (uint8_t)135U,
    (uint8_t)30U, (uint8_t)106U
  };

static uint8_t
sigver_vectors512_low64[32U] =
  {
    (uint8_t)223U, (uint8_t)89U, (uint8_t)156U, (uint8_t)58U, (uint8_t)55U, (uint8_t)16U,
    (uint8_t)90U, (uint8_t)243U, (uint8_t)236U, (uint8_t)193U, (uint8_t)89U, (uint8_t)179U,
    (uint8_t)182U, (uint8_t)133U, (uint8_t)204U, (uint8_t)179U, (uint8_t)225U, (uint8_t)81U,
    (uint8_t)183U, (uint8_t)213U, (uint8_t)207U, (uint8_t)45U, (uint8_t)151U, (uint8_t)20U,
    (uint8_t)121U, (uint8_t)116U, (uint8_t)174U, (uint8_t)113U, (uint8_t)244U, (uint8_t)102U,
    (uint8_t)182U, (uint8_t)21U
  };

static uint8_t
sigver_vectors512_low65[128U] =
  {
    (uint8_t)213U, (uint8_t)94U, (uint8_t)94U, (uint8_t)18U, (uint8_t)74U, (uint8_t)114U,
    (uint8_t)23U, (uint8_t)135U, (uint8_t)156U, (uint8_t)169U, (uint8_t)134U, (uint8_t)242U,
    (uint8_t)133U, (uint8_t)226U, (uint8_t)42U, (uint8_t)197U, (uint8_t)25U, (uint8_t)64U,
    (uint8_t)179U, (uint8_t)89U, (uint8_t)89U, (uint8_t)187U, (uint8_t)245U, (uint8_t)84U,
    (uint8_t)49U, (uint8_t)4U, (uint8_t)181U, (uint8_t)84U, (uint8_t)115U, (uint8_t)86U,
    (uint8_t)253U, (uint8_t)26U, (uint8_t)14U, (uint8_t)195U, (uint8_t)124U, (uint8_t)10U,
    (uint8_t)35U, (uint8_t)32U, (uint8_t)144U, (uint8_t)4U, (uint8_t)162U, (uint8_t)236U,
    (uint8_t)91U, (uint8_t)202U, (uint8_t)243U, (uint8_t)51U, (uint8_t)91U, (uint8_t)196U,
    (uint8_t)94U, (uint8_t)77U, (uint8_t)201U, (uint8_t)144U, (uint8_t)234U, (uint8_t)205U,
    (uint8_t)41U, (uint8_t)178U, (uint8_t)217U, (uint8_t)181U, (uint8_t)207U, (uint8_t)52U,
    (uint8_t)156U, (uint8_t)123U, (uint8_t)166U, (uint8_t)119U, (uint8_t)17U, (uint8_t)53U,
    (uint8_t)98U, (uint8_t)153U, (uint8_t)188U, (uint8_t)234U, (uint8_t)182U, (uint8_t)240U,
    (uint8_t)72U, (uint8_t)223U, (uint8_t)118U, (uint8_t)28U, (uint8_t)101U, (uint8_t)242U,
    (uint8_t)152U, (uint8_t)136U, (uint8_t)3U, (uint8_t)19U, (uint8_t)61U, (uint8_t)103U,
    (uint8_t)35U, (uint8_t)162U, (uint8_t)130U, (uint8_t)15U, (uint8_t)239U, (uint8_t)178U,
    (uint8_t)101U, (uint8_t)76U, (uint8_t)199U, (uint8_t)197U, (uint8_t)240U, (uint8_t)50U,
    (uint8_t)248U, (uint8_t)51U, (uint8_t)186U, (uint8_t)120U, (uint8_t)163U, (uint8_t)77U,
    (uint8_t)40U, (uint8_t)120U, (uint8_t)198U, (uint8_t)176U, (uint8_t)186U, (uint8_t)101U,
    (uint8_t)78U, (uint8_t)190U, (uint8_t)38U, (uint8_t)177U, (uint8_t)16U, (uint8_t)201U,
    (uint8_t)53U, (uint8_t)171U, (uint8_t)181U, (uint8_t)96U, (uint8_t)36U, (uint8_t)189U,
    (uint8_t)93U, (uint8_t)15U, (uint8_t)9U, (uint8_t)179U, (uint8_t)103U, (uint8_t)114U,
    (uint8_t)76U, (uint8_t)7U
  };

static uint8_t
sigver_vectors512_low66[32U] =
  {
    (uint8_t)31U, (uint8_t)214U, (uint8_t)244U, (uint8_t)185U, (uint8_t)141U, (uint8_t)7U,
    (uint8_t)85U, (uint8_t)41U, (uint8_t)30U, (uint8_t)122U, (uint8_t)35U, (uint8_t)14U,
    (uint8_t)159U, (uint8_t)129U, (uint8_t)236U, (uint8_t)249U, (uint8_t)9U, (uint8_t)230U,
    (uint8_t)53U, (uint8_t)10U, (uint8_t)173U, (uint8_t)176U, (uint8_t)142U, (uint8_t)66U,
    (uint8_t)163U, (uint8_t)38U, (uint8_t)47U, (uint8_t)241U, (uint8_t)146U, (uint8_t)0U,
    (uint8_t)251U, (uint8_t)210U
  };

static uint8_t
sigver_vectors512_low67[32U] =
  {
    (uint8_t)85U, (uint8_t)120U, (uint8_t)254U, (uint8_t)247U, (uint8_t)155U, (uint8_t)196U,
    (uint8_t)119U, (uint8_t)172U, (uint8_t)251U, (uint8_t)142U, (uint8_t)208U, (uint8_t)220U,
    (uint8_t)16U, (uint8_t)196U, (uint8_t)245U, (uint8_t)128U, (uint8_t)156U, (uint8_t)20U,
    (uint8_t)220U, (uint8_t)84U, (uint8_t)146U, (uint8_t)64U, (uint8_t)91U, (uint8_t)55U,
    (uint8_t)146U, (uint8_t)167U, (uint8_t)148U, (uint8_t)6U, (uint8_t)80U, (uint8_t)179U,
    (uint8_t)5U, (uint8_t)215U
  };

static uint8_t
sigver_vectors512_low68[32U] =
  {
    (uint8_t)151U, (uint8_t)169U, (uint8_t)158U, (uint8_t)150U, (uint8_t)228U, (uint8_t)7U,
    (uint8_t)179U, (uint8_t)173U, (uint8_t)162U, (uint8_t)194U, (uint8_t)220U, (uint8_t)249U,
    (uint8_t)206U, (uint8_t)238U, (uint8_t)185U, (uint8_t)132U, (uint8_t)217U, (uint8_t)164U,
    (uint8_t)208U, (uint8_t)170U, (uint8_t)102U, (uint8_t)221U, (uint8_t)240U, (uint8_t)167U,
    (uint8_t)76U, (uint8_t)162U, (uint8_t)60U, (uint8_t)171U, (uint8_t)251U, (uint8_t)21U,
    (uint8_t)102U, (uint8_t)204U
  };

static uint8_t
sigver_vectors512_low69[32U] =
  {
    (uint8_t)14U, (uint8_t)202U, (uint8_t)195U, (uint8_t)21U, (uint8_t)220U, (uint8_t)25U,
    (uint8_t)156U, (uint8_t)254U, (uint8_t)163U, (uint8_t)193U, (uint8_t)83U, (uint8_t)72U,
    (uint8_t)193U, (uint8_t)48U, (uint8_t)146U, (uint8_t)74U, (uint8_t)31U, (uint8_t)120U,
    (uint8_t)112U, (uint8_t)25U, (uint8_t)254U, (uint8_t)76U, (uint8_t)211U, (uint8_t)174U,
    (uint8_t)71U, (uint8_t)202U, (uint8_t)139U, (uint8_t)17U, (uint8_t)18U, (uint8_t)104U,
    (uint8_t)117U, (uint8_t)74U
  };

static uint8_t
sigver_vectors512_low70[128U] =
  {
    (uint8_t)119U, (uint8_t)83U, (uint8_t)192U, (uint8_t)59U, (uint8_t)66U, (uint8_t)2U,
    (uint8_t)203U, (uint8_t)56U, (uint8_t)188U, (uint8_t)1U, (uint8_t)144U, (uint8_t)169U,
    (uint8_t)249U, (uint8_t)49U, (uint8_t)235U, (uint8_t)49U, (uint8_t)133U, (uint8_t)141U,
    (uint8_t)112U, (uint8_t)93U, (uint8_t)146U, (uint8_t)214U, (uint8_t)80U, (uint8_t)50U,
    (uint8_t)15U, (uint8_t)244U, (uint8_t)73U, (uint8_t)252U, (uint8_t)153U, (uint8_t)22U,
    (uint8_t)127U, (uint8_t)179U, (uint8_t)119U, (uint8_t)11U, (uint8_t)118U, (uint8_t)76U,
    (uint8_t)137U, (uint8_t)136U, (uint8_t)246U, (uint8_t)179U, (uint8_t)74U, (uint8_t)197U,
    (uint8_t)163U, (uint8_t)213U, (uint8_t)7U, (uint8_t)161U, (uint8_t)14U, (uint8_t)10U,
    (uint8_t)255U, (uint8_t)127U, (uint8_t)136U, (uint8_t)41U, (uint8_t)63U, (uint8_t)106U,
    (uint8_t)34U, (uint8_t)199U, (uint8_t)237U, (uint8_t)138U, (uint8_t)36U, (uint8_t)36U,
    (uint8_t)138U, (uint8_t)82U, (uint8_t)220U, (uint8_t)18U, (uint8_t)94U, (uint8_t)65U,
    (uint8_t)110U, (uint8_t)21U, (uint8_t)136U, (uint8_t)51U, (uint8_t)252U, (uint8_t)56U,
    (uint8_t)175U, (uint8_t)41U, (uint8_t)25U, (uint8_t)159U, (uint8_t)140U, (uint8_t)164U,
    (uint8_t)147U, (uint8_t)16U, (uint8_t)104U, (uint8_t)212U, (uint8_t)204U, (uint8_t)170U,
    (uint8_t)135U, (uint8_t)226U, (uint8_t)153U, (uint8_t)233U, (uint8_t)86U, (uint8_t)66U,
    (uint8_t)6U, (uint8_t)143U, (uint8_t)104U, (uint8_t)194U, (uint8_t)8U, (uint8_t)203U,
    (uint8_t)120U, (uint8_t)45U, (uint8_t)241U, (uint8_t)57U, (uint8_t)8U, (uint8_t)249U,
    (uint8_t)80U, (uint8_t)86U, (uint8_t)71U, (uint8_t)67U, (uint8_t)237U, (uint8_t)22U,
    (uint8_t)146U, (uint8_t)80U, (uint8_t)43U, (uint8_t)175U, (uint8_t)175U, (uint8_t)175U,
    (uint8_t)241U, (uint8_t)105U, (uint8_t)220U, (uint8_t)143U, (uint8_t)230U, (uint8_t)116U,
    (uint8_t)251U, (uint8_t)94U, (uint8_t)79U, (uint8_t)63U, (uint8_t)253U, (uint8_t)87U,
    (uint8_t)140U, (uint8_t)53U
  };

static uint8_t
sigver_vectors512_low71[32U] =
  {
    (uint8_t)45U, (uint8_t)203U, (uint8_t)216U, (uint8_t)121U, (uint8_t)12U, (uint8_t)238U,
    (uint8_t)85U, (uint8_t)46U, (uint8_t)159U, (uint8_t)24U, (uint8_t)242U, (uint8_t)179U,
    (uint8_t)20U, (uint8_t)154U, (uint8_t)34U, (uint8_t)82U, (uint8_t)220U, (uint8_t)213U,
    (uint8_t)139U, (uint8_t)153U, (uint8_t)202U, (uint8_t)125U, (uint8_t)201U, (uint8_t)104U,
    (uint8_t)11U, (uint8_t)146U, (uint8_t)200U, (uint8_t)196U, (uint8_t)58U, (uint8_t)163U,
    (uint8_t)56U, (uint8_t)116U
  };

static uint8_t
sigver_vectors512_low72[32U] =
  {
    (uint8_t)93U, (uint8_t)188U, (uint8_t)139U, (uint8_t)184U, (uint8_t)129U, (uint8_t)60U,
    (uint8_t)142U, (uint8_t)1U, (uint8_t)157U, (uint8_t)128U, (uint8_t)225U, (uint8_t)154U,
    (uint8_t)205U, (uint8_t)176U, (uint8_t)121U, (uint8_t)47U, (uint8_t)83U, (uint8_t)121U,
    (uint8_t)128U, (uint8_t)254U, (uint8_t)205U, (uint8_t)233U, (uint8_t)61U, (uint8_t)182U,
    (uint8_t)33U, (uint8_t)170U, (uint8_t)241U, (uint8_t)246U, (uint8_t)208U, (uint8_t)230U,
    (uint8_t)238U, (uint8_t)52U
  };

static uint8_t
sigver_vectors512_low73[32U] =
  {
    (uint8_t)43U, (uint8_t)219U, (uint8_t)216U, (uint8_t)176U, (uint8_t)215U, (uint8_t)89U,
    (uint8_t)89U, (uint8_t)86U, (uint8_t)98U, (uint8_t)204U, (uint8_t)16U, (uint8_t)177U,
    (uint8_t)2U, (uint8_t)54U, (uint8_t)19U, (uint8_t)110U, (uint8_t)246U, (uint8_t)206U,
    (uint8_t)66U, (uint8_t)150U, (uint8_t)65U, (uint8_t)246U, (uint8_t)140U, (uint8_t)246U,
    (uint8_t)72U, (uint8_t)15U, (uint8_t)71U, (uint8_t)47U, (uint8_t)204U, (uint8_t)119U,
    (uint8_t)188U, (uint8_t)159U
  };

static uint8_t
sigver_vectors512_low74[32U] =
  {
    (uint8_t)126U, (uint8_t)125U, (uint8_t)240U, (uint8_t)200U, (uint8_t)184U, (uint8_t)111U,
    (uint8_t)125U, (uint8_t)176U, (uint8_t)108U, (uint8_t)175U, (uint8_t)22U, (uint8_t)16U,
    (uint8_t)22U, (uint8_t)111U, (uint8_t)123U, (uint8_t)156U, (uint8_t)76U, (uint8_t)117U,
    (uint8_t)68U, (uint8_t)127U, (uint8_t)153U, (uint8_t)29U, (uint8_t)90U, (uint8_t)175U,
    (uint8_t)77U, (uint8_t)234U, (uint8_t)114U, (uint8_t)12U, (uint8_t)37U, (uint8_t)152U,
    (uint8_t)92U, (uint8_t)140U
  };

static __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors512_low75[15U] =
  {
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low0 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low1 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low2 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low3 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low4 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low5 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low6 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low7 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low8 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low9 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low10 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low11 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low12 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low13 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low14 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low15 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low16 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low17 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low18 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low19 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low20 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low21 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low22 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low23 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low24 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low25 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low26 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low27 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low28 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low29 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low30 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low31 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low32 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low33 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low34 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low35 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low36 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low37 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low38 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low39 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low40 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low41 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low42 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low43 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low44 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low45 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low46 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low47 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low48 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low49 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low50 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low51 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low52 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low53 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low54 }, .f5 = true
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low55 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low56 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low57 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low58 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low59 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low60 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low61 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low62 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low63 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low64 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low65 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low66 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low67 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low68 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low69 }, .f5 = false
    },
    {
      .fst = { .len = (uint32_t)128U, .b = sigver_vectors512_low70 },
      .snd = { .len = (uint32_t)32U, .b = sigver_vectors512_low71 },
      .thd = { .len = (uint32_t)32U, .b = sigver_vectors512_low72 },
      .f3 = { .len = (uint32_t)32U, .b = sigver_vectors512_low73 },
      .f4 = { .len = (uint32_t)32U, .b = sigver_vectors512_low74 }, .f5 = true
    }
  };

static lbuffer__K___Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
sigver_vectors512_low = { .len = (uint32_t)15U, .b = sigver_vectors512_low75 };

static uint8_t
siggen_vectors256_low0[128U] =
  {
    (uint8_t)89U, (uint8_t)5U, (uint8_t)35U, (uint8_t)136U, (uint8_t)119U, (uint8_t)199U,
    (uint8_t)116U, (uint8_t)33U, (uint8_t)247U, (uint8_t)62U, (uint8_t)67U, (uint8_t)238U,
    (uint8_t)61U, (uint8_t)166U, (uint8_t)242U, (uint8_t)217U, (uint8_t)226U, (uint8_t)204U,
    (uint8_t)173U, (uint8_t)95U, (uint8_t)201U, (uint8_t)66U, (uint8_t)220U, (uint8_t)236U,
    (uint8_t)12U, (uint8_t)189U, (uint8_t)37U, (uint8_t)72U, (uint8_t)41U, (uint8_t)53U,
    (uint8_t)250U, (uint8_t)175U, (uint8_t)65U, (uint8_t)105U, (uint8_t)131U, (uint8_t)254U,
    (uint8_t)22U, (uint8_t)91U, (uint8_t)26U, (uint8_t)4U, (uint8_t)94U, (uint8_t)226U,
    (uint8_t)188U, (uint8_t)210U, (uint8_t)230U, (uint8_t)220U, (uint8_t)163U, (uint8_t)189U,
    (uint8_t)244U, (uint8_t)108U, (uint8_t)67U, (uint8_t)16U, (uint8_t)167U, (uint8_t)70U,
    (uint8_t)31U, (uint8_t)154U, (uint8_t)55U, (uint8_t)150U, (uint8_t)12U, (uint8_t)166U,
    (uint8_t)114U, (uint8_t)211U, (uint8_t)254U, (uint8_t)181U, (uint8_t)71U, (uint8_t)62U,
    (uint8_t)37U, (uint8_t)54U, (uint8_t)5U, (uint8_t)251U, (uint8_t)29U, (uint8_t)223U,
    (uint8_t)210U, (uint8_t)128U, (uint8_t)101U, (uint8_t)181U, (uint8_t)60U, (uint8_t)181U,
    (uint8_t)133U, (uint8_t)138U, (uint8_t)138U, (uint8_t)210U, (uint8_t)129U, (uint8_t)117U,
    (uint8_t)191U, (uint8_t)155U, (uint8_t)211U, (uint8_t)134U, (uint8_t)165U, (uint8_t)228U,
    (uint8_t)113U, (uint8_t)234U, (uint8_t)122U, (uint8_t)101U, (uint8_t)193U, (uint8_t)124U,
    (uint8_t)201U, (uint8_t)52U, (uint8_t)169U, (uint8_t)215U, (uint8_t)145U, (uint8_t)233U,
    (uint8_t)20U, (uint8_t)145U, (uint8_t)235U, (uint8_t)55U, (uint8_t)84U, (uint8_t)208U,
    (uint8_t)55U, (uint8_t)153U, (uint8_t)121U, (uint8_t)15U, (uint8_t)226U, (uint8_t)211U,
    (uint8_t)8U, (uint8_t)209U, (uint8_t)97U, (uint8_t)70U, (uint8_t)213U, (uint8_t)201U,
    (uint8_t)176U, (uint8_t)208U, (uint8_t)222U, (uint8_t)189U, (uint8_t)151U, (uint8_t)215U,
    (uint8_t)156U, (uint8_t)232U
  };

static uint8_t
siggen_vectors256_low1[32U] =
  {
    (uint8_t)81U, (uint8_t)155U, (uint8_t)66U, (uint8_t)61U, (uint8_t)113U, (uint8_t)95U,
    (uint8_t)139U, (uint8_t)88U, (uint8_t)31U, (uint8_t)79U, (uint8_t)168U, (uint8_t)238U,
    (uint8_t)89U, (uint8_t)244U, (uint8_t)119U, (uint8_t)26U, (uint8_t)91U, (uint8_t)68U,
    (uint8_t)200U, (uint8_t)19U, (uint8_t)11U, (uint8_t)78U, (uint8_t)62U, (uint8_t)172U,
    (uint8_t)202U, (uint8_t)84U, (uint8_t)165U, (uint8_t)109U, (uint8_t)218U, (uint8_t)114U,
    (uint8_t)180U, (uint8_t)100U
  };

static uint8_t
siggen_vectors256_low2[32U] =
  {
    (uint8_t)28U, (uint8_t)203U, (uint8_t)233U, (uint8_t)28U, (uint8_t)7U, (uint8_t)95U,
    (uint8_t)199U, (uint8_t)244U, (uint8_t)240U, (uint8_t)51U, (uint8_t)191U, (uint8_t)162U,
    (uint8_t)72U, (uint8_t)219U, (uint8_t)143U, (uint8_t)204U, (uint8_t)211U, (uint8_t)86U,
    (uint8_t)93U, (uint8_t)233U, (uint8_t)75U, (uint8_t)191U, (uint8_t)177U, (uint8_t)47U,
    (uint8_t)60U, (uint8_t)89U, (uint8_t)255U, (uint8_t)70U, (uint8_t)194U, (uint8_t)113U,
    (uint8_t)191U, (uint8_t)131U
  };

static uint8_t
siggen_vectors256_low3[32U] =
  {
    (uint8_t)206U, (uint8_t)64U, (uint8_t)20U, (uint8_t)198U, (uint8_t)136U, (uint8_t)17U,
    (uint8_t)249U, (uint8_t)162U, (uint8_t)26U, (uint8_t)31U, (uint8_t)219U, (uint8_t)44U,
    (uint8_t)14U, (uint8_t)97U, (uint8_t)19U, (uint8_t)224U, (uint8_t)109U, (uint8_t)183U,
    (uint8_t)202U, (uint8_t)147U, (uint8_t)183U, (uint8_t)64U, (uint8_t)78U, (uint8_t)120U,
    (uint8_t)220U, (uint8_t)124U, (uint8_t)205U, (uint8_t)92U, (uint8_t)168U, (uint8_t)154U,
    (uint8_t)76U, (uint8_t)169U
  };

static uint8_t
siggen_vectors256_low4[32U] =
  {
    (uint8_t)148U, (uint8_t)161U, (uint8_t)187U, (uint8_t)177U, (uint8_t)75U, (uint8_t)144U,
    (uint8_t)106U, (uint8_t)97U, (uint8_t)162U, (uint8_t)128U, (uint8_t)242U, (uint8_t)69U,
    (uint8_t)249U, (uint8_t)233U, (uint8_t)60U, (uint8_t)127U, (uint8_t)59U, (uint8_t)74U,
    (uint8_t)98U, (uint8_t)71U, (uint8_t)130U, (uint8_t)79U, (uint8_t)93U, (uint8_t)51U,
    (uint8_t)185U, (uint8_t)103U, (uint8_t)7U, (uint8_t)135U, (uint8_t)100U, (uint8_t)42U,
    (uint8_t)104U, (uint8_t)222U
  };

static uint8_t
siggen_vectors256_low5[32U] =
  {
    (uint8_t)243U, (uint8_t)172U, (uint8_t)128U, (uint8_t)97U, (uint8_t)181U, (uint8_t)20U,
    (uint8_t)121U, (uint8_t)91U, (uint8_t)136U, (uint8_t)67U, (uint8_t)227U, (uint8_t)214U,
    (uint8_t)98U, (uint8_t)149U, (uint8_t)39U, (uint8_t)237U, (uint8_t)42U, (uint8_t)253U,
    (uint8_t)107U, (uint8_t)31U, (uint8_t)106U, (uint8_t)85U, (uint8_t)90U, (uint8_t)122U,
    (uint8_t)202U, (uint8_t)187U, (uint8_t)94U, (uint8_t)111U, (uint8_t)121U, (uint8_t)200U,
    (uint8_t)194U, (uint8_t)172U
  };

static uint8_t
siggen_vectors256_low6[32U] =
  {
    (uint8_t)139U, (uint8_t)247U, (uint8_t)120U, (uint8_t)25U, (uint8_t)202U, (uint8_t)5U,
    (uint8_t)166U, (uint8_t)178U, (uint8_t)120U, (uint8_t)108U, (uint8_t)118U, (uint8_t)38U,
    (uint8_t)43U, (uint8_t)247U, (uint8_t)55U, (uint8_t)28U, (uint8_t)239U, (uint8_t)151U,
    (uint8_t)178U, (uint8_t)24U, (uint8_t)233U, (uint8_t)111U, (uint8_t)23U, (uint8_t)90U,
    (uint8_t)60U, (uint8_t)205U, (uint8_t)218U, (uint8_t)42U, (uint8_t)204U, (uint8_t)5U,
    (uint8_t)137U, (uint8_t)3U
  };

static uint8_t
siggen_vectors256_low7[128U] =
  {
    (uint8_t)195U, (uint8_t)94U, (uint8_t)47U, (uint8_t)9U, (uint8_t)37U, (uint8_t)83U,
    (uint8_t)197U, (uint8_t)87U, (uint8_t)114U, (uint8_t)146U, (uint8_t)107U, (uint8_t)219U,
    (uint8_t)232U, (uint8_t)124U, (uint8_t)151U, (uint8_t)150U, (uint8_t)130U, (uint8_t)125U,
    (uint8_t)23U, (uint8_t)2U, (uint8_t)77U, (uint8_t)187U, (uint8_t)146U, (uint8_t)51U,
    (uint8_t)165U, (uint8_t)69U, (uint8_t)54U, (uint8_t)110U, (uint8_t)46U, (uint8_t)89U,
    (uint8_t)135U, (uint8_t)221U, (uint8_t)52U, (uint8_t)77U, (uint8_t)235U, (uint8_t)114U,
    (uint8_t)223U, (uint8_t)152U, (uint8_t)113U, (uint8_t)68U, (uint8_t)184U, (uint8_t)198U,
    (uint8_t)196U, (uint8_t)59U, (uint8_t)196U, (uint8_t)27U, (uint8_t)101U, (uint8_t)75U,
    (uint8_t)148U, (uint8_t)204U, (uint8_t)133U, (uint8_t)110U, (uint8_t)22U, (uint8_t)185U,
    (uint8_t)109U, (uint8_t)122U, (uint8_t)130U, (uint8_t)28U, (uint8_t)142U, (uint8_t)192U,
    (uint8_t)57U, (uint8_t)181U, (uint8_t)3U, (uint8_t)227U, (uint8_t)216U, (uint8_t)103U,
    (uint8_t)40U, (uint8_t)196U, (uint8_t)148U, (uint8_t)169U, (uint8_t)103U, (uint8_t)216U,
    (uint8_t)48U, (uint8_t)17U, (uint8_t)160U, (uint8_t)224U, (uint8_t)144U, (uint8_t)181U,
    (uint8_t)213U, (uint8_t)76U, (uint8_t)212U, (uint8_t)127U, (uint8_t)78U, (uint8_t)54U,
    (uint8_t)108U, (uint8_t)9U, (uint8_t)18U, (uint8_t)188U, (uint8_t)128U, (uint8_t)143U,
    (uint8_t)187U, (uint8_t)46U, (uint8_t)169U, (uint8_t)110U, (uint8_t)250U, (uint8_t)200U,
    (uint8_t)143U, (uint8_t)179U, (uint8_t)235U, (uint8_t)236U, (uint8_t)147U, (uint8_t)66U,
    (uint8_t)115U, (uint8_t)142U, (uint8_t)34U, (uint8_t)95U, (uint8_t)124U, (uint8_t)124U,
    (uint8_t)43U, (uint8_t)1U, (uint8_t)28U, (uint8_t)227U, (uint8_t)117U, (uint8_t)181U,
    (uint8_t)102U, (uint8_t)33U, (uint8_t)162U, (uint8_t)6U, (uint8_t)66U, (uint8_t)180U,
    (uint8_t)211U, (uint8_t)110U, (uint8_t)6U, (uint8_t)13U, (uint8_t)180U, (uint8_t)82U,
    (uint8_t)74U, (uint8_t)241U
  };

static uint8_t
siggen_vectors256_low8[32U] =
  {
    (uint8_t)15U, (uint8_t)86U, (uint8_t)219U, (uint8_t)120U, (uint8_t)202U, (uint8_t)70U,
    (uint8_t)11U, (uint8_t)5U, (uint8_t)92U, (uint8_t)80U, (uint8_t)0U, (uint8_t)100U,
    (uint8_t)130U, (uint8_t)75U, (uint8_t)237U, (uint8_t)153U, (uint8_t)154U, (uint8_t)37U,
    (uint8_t)170U, (uint8_t)244U, (uint8_t)142U, (uint8_t)187U, (uint8_t)81U, (uint8_t)154U,
    (uint8_t)194U, (uint8_t)1U, (uint8_t)83U, (uint8_t)123U, (uint8_t)133U, (uint8_t)71U,
    (uint8_t)152U, (uint8_t)19U
  };

static uint8_t
siggen_vectors256_low9[32U] =
  {
    (uint8_t)226U, (uint8_t)102U, (uint8_t)221U, (uint8_t)253U, (uint8_t)193U, (uint8_t)38U,
    (uint8_t)104U, (uint8_t)219U, (uint8_t)48U, (uint8_t)212U, (uint8_t)202U, (uint8_t)62U,
    (uint8_t)143U, (uint8_t)119U, (uint8_t)73U, (uint8_t)67U, (uint8_t)44U, (uint8_t)65U,
    (uint8_t)96U, (uint8_t)68U, (uint8_t)242U, (uint8_t)210U, (uint8_t)184U, (uint8_t)193U,
    (uint8_t)11U, (uint8_t)243U, (uint8_t)212U, (uint8_t)1U, (uint8_t)42U, (uint8_t)239U,
    (uint8_t)250U, (uint8_t)138U
  };

static uint8_t
siggen_vectors256_low10[32U] =
  {
    (uint8_t)191U, (uint8_t)168U, (uint8_t)100U, (uint8_t)4U, (uint8_t)162U, (uint8_t)233U,
    (uint8_t)255U, (uint8_t)230U, (uint8_t)125U, (uint8_t)71U, (uint8_t)197U, (uint8_t)135U,
    (uint8_t)239U, (uint8_t)122U, (uint8_t)151U, (uint8_t)167U, (uint8_t)244U, (uint8_t)86U,
    (uint8_t)184U, (uint8_t)99U, (uint8_t)180U, (uint8_t)208U, (uint8_t)44U, (uint8_t)252U,
    (uint8_t)105U, (uint8_t)40U, (uint8_t)151U, (uint8_t)58U, (uint8_t)181U, (uint8_t)177U,
    (uint8_t)203U, (uint8_t)57U
  };

static uint8_t
siggen_vectors256_low11[32U] =
  {
    (uint8_t)109U, (uint8_t)62U, (uint8_t)113U, (uint8_t)136U, (uint8_t)44U, (uint8_t)59U,
    (uint8_t)131U, (uint8_t)177U, (uint8_t)86U, (uint8_t)187U, (uint8_t)20U, (uint8_t)224U,
    (uint8_t)171U, (uint8_t)24U, (uint8_t)74U, (uint8_t)169U, (uint8_t)251U, (uint8_t)114U,
    (uint8_t)128U, (uint8_t)104U, (uint8_t)211U, (uint8_t)174U, (uint8_t)159U, (uint8_t)172U,
    (uint8_t)66U, (uint8_t)17U, (uint8_t)135U, (uint8_t)174U, (uint8_t)11U, (uint8_t)47U,
    (uint8_t)52U, (uint8_t)198U
  };

static uint8_t
siggen_vectors256_low12[32U] =
  {
    (uint8_t)151U, (uint8_t)109U, (uint8_t)58U, (uint8_t)78U, (uint8_t)157U, (uint8_t)35U,
    (uint8_t)50U, (uint8_t)109U, (uint8_t)192U, (uint8_t)186U, (uint8_t)169U, (uint8_t)250U,
    (uint8_t)86U, (uint8_t)11U, (uint8_t)124U, (uint8_t)78U, (uint8_t)83U, (uint8_t)244U,
    (uint8_t)40U, (uint8_t)100U, (uint8_t)245U, (uint8_t)8U, (uint8_t)72U, (uint8_t)58U,
    (uint8_t)100U, (uint8_t)115U, (uint8_t)182U, (uint8_t)161U, (uint8_t)16U, (uint8_t)121U,
    (uint8_t)178U, (uint8_t)219U
  };

static uint8_t
siggen_vectors256_low13[32U] =
  {
    (uint8_t)27U, (uint8_t)118U, (uint8_t)110U, (uint8_t)156U, (uint8_t)235U, (uint8_t)113U,
    (uint8_t)186U, (uint8_t)108U, (uint8_t)1U, (uint8_t)220U, (uint8_t)212U, (uint8_t)110U,
    (uint8_t)10U, (uint8_t)244U, (uint8_t)98U, (uint8_t)205U, (uint8_t)76U, (uint8_t)250U,
    (uint8_t)101U, (uint8_t)42U, (uint8_t)229U, (uint8_t)1U, (uint8_t)125U, (uint8_t)69U,
    (uint8_t)85U, (uint8_t)184U, (uint8_t)238U, (uint8_t)239U, (uint8_t)227U, (uint8_t)110U,
    (uint8_t)25U, (uint8_t)50U
  };

static uint8_t
siggen_vectors256_low14[128U] =
  {
    (uint8_t)60U, (uint8_t)5U, (uint8_t)78U, (uint8_t)51U, (uint8_t)58U, (uint8_t)148U,
    (uint8_t)37U, (uint8_t)156U, (uint8_t)54U, (uint8_t)175U, (uint8_t)9U, (uint8_t)171U,
    (uint8_t)91U, (uint8_t)79U, (uint8_t)249U, (uint8_t)190U, (uint8_t)179U, (uint8_t)73U,
    (uint8_t)47U, (uint8_t)141U, (uint8_t)91U, (uint8_t)66U, (uint8_t)130U, (uint8_t)209U,
    (uint8_t)104U, (uint8_t)1U, (uint8_t)218U, (uint8_t)204U, (uint8_t)178U, (uint8_t)159U,
    (uint8_t)112U, (uint8_t)254U, (uint8_t)97U, (uint8_t)160U, (uint8_t)179U, (uint8_t)127U,
    (uint8_t)254U, (uint8_t)245U, (uint8_t)192U, (uint8_t)76U, (uint8_t)209U, (uint8_t)183U,
    (uint8_t)14U, (uint8_t)133U, (uint8_t)177U, (uint8_t)245U, (uint8_t)73U, (uint8_t)161U,
    (uint8_t)196U, (uint8_t)220U, (uint8_t)103U, (uint8_t)41U, (uint8_t)133U, (uint8_t)229U,
    (uint8_t)15U, (uint8_t)67U, (uint8_t)234U, (uint8_t)3U, (uint8_t)126U, (uint8_t)250U,
    (uint8_t)153U, (uint8_t)100U, (uint8_t)240U, (uint8_t)150U, (uint8_t)181U, (uint8_t)246U,
    (uint8_t)47U, (uint8_t)127U, (uint8_t)253U, (uint8_t)248U, (uint8_t)214U, (uint8_t)191U,
    (uint8_t)178U, (uint8_t)204U, (uint8_t)133U, (uint8_t)149U, (uint8_t)88U, (uint8_t)245U,
    (uint8_t)163U, (uint8_t)147U, (uint8_t)203U, (uint8_t)148U, (uint8_t)157U, (uint8_t)189U,
    (uint8_t)72U, (uint8_t)242U, (uint8_t)105U, (uint8_t)52U, (uint8_t)59U, (uint8_t)82U,
    (uint8_t)99U, (uint8_t)220U, (uint8_t)219U, (uint8_t)156U, (uint8_t)85U, (uint8_t)110U,
    (uint8_t)202U, (uint8_t)7U, (uint8_t)79U, (uint8_t)46U, (uint8_t)152U, (uint8_t)230U,
    (uint8_t)217U, (uint8_t)76U, (uint8_t)44U, (uint8_t)41U, (uint8_t)166U, (uint8_t)119U,
    (uint8_t)175U, (uint8_t)175U, (uint8_t)128U, (uint8_t)110U, (uint8_t)223U, (uint8_t)121U,
    (uint8_t)177U, (uint8_t)90U, (uint8_t)63U, (uint8_t)205U, (uint8_t)70U, (uint8_t)231U,
    (uint8_t)6U, (uint8_t)123U, (uint8_t)118U, (uint8_t)105U, (uint8_t)248U, (uint8_t)49U,
    (uint8_t)136U, (uint8_t)238U
  };

static uint8_t
siggen_vectors256_low15[32U] =
  {
    (uint8_t)226U, (uint8_t)131U, (uint8_t)135U, (uint8_t)18U, (uint8_t)57U, (uint8_t)131U,
    (uint8_t)126U, (uint8_t)19U, (uint8_t)185U, (uint8_t)95U, (uint8_t)120U, (uint8_t)158U,
    (uint8_t)110U, (uint8_t)26U, (uint8_t)246U, (uint8_t)59U, (uint8_t)246U, (uint8_t)28U,
    (uint8_t)145U, (uint8_t)140U, (uint8_t)153U, (uint8_t)46U, (uint8_t)98U, (uint8_t)188U,
    (uint8_t)160U, (uint8_t)64U, (uint8_t)214U, (uint8_t)76U, (uint8_t)173U, (uint8_t)31U,
    (uint8_t)194U, (uint8_t)239U
  };

static uint8_t
siggen_vectors256_low16[32U] =
  {
    (uint8_t)116U, (uint8_t)204U, (uint8_t)216U, (uint8_t)166U, (uint8_t)47U, (uint8_t)186U,
    (uint8_t)14U, (uint8_t)102U, (uint8_t)124U, (uint8_t)80U, (uint8_t)146U, (uint8_t)154U,
    (uint8_t)83U, (uint8_t)247U, (uint8_t)140U, (uint8_t)33U, (uint8_t)184U, (uint8_t)255U,
    (uint8_t)12U, (uint8_t)60U, (uint8_t)115U, (uint8_t)123U, (uint8_t)11U, (uint8_t)64U,
    (uint8_t)177U, (uint8_t)117U, (uint8_t)11U, (uint8_t)35U, (uint8_t)2U, (uint8_t)176U,
    (uint8_t)189U, (uint8_t)232U
  };

static uint8_t
siggen_vectors256_low17[32U] =
  {
    (uint8_t)41U, (uint8_t)7U, (uint8_t)78U, (uint8_t)33U, (uint8_t)243U, (uint8_t)160U,
    (uint8_t)239U, (uint8_t)136U, (uint8_t)185U, (uint8_t)239U, (uint8_t)223U, (uint8_t)16U,
    (uint8_t)208U, (uint8_t)106U, (uint8_t)164U, (uint8_t)194U, (uint8_t)149U, (uint8_t)204U,
    (uint8_t)22U, (uint8_t)113U, (uint8_t)247U, (uint8_t)88U, (uint8_t)202U, (uint8_t)14U,
    (uint8_t)76U, (uint8_t)209U, (uint8_t)8U, (uint8_t)128U, (uint8_t)61U, (uint8_t)15U,
    (uint8_t)38U, (uint8_t)20U
  };

static uint8_t
siggen_vectors256_low18[32U] =
  {
    (uint8_t)173U, (uint8_t)94U, (uint8_t)136U, (uint8_t)126U, (uint8_t)178U, (uint8_t)179U,
    (uint8_t)128U, (uint8_t)184U, (uint8_t)216U, (uint8_t)40U, (uint8_t)10U, (uint8_t)214U,
    (uint8_t)229U, (uint8_t)255U, (uint8_t)138U, (uint8_t)96U, (uint8_t)244U, (uint8_t)210U,
    (uint8_t)98U, (uint8_t)67U, (uint8_t)224U, (uint8_t)18U, (uint8_t)76U, (uint8_t)47U,
    (uint8_t)49U, (uint8_t)162U, (uint8_t)151U, (uint8_t)181U, (uint8_t)208U, (uint8_t)131U,
    (uint8_t)93U, (uint8_t)226U
  };

static uint8_t
siggen_vectors256_low19[32U] =
  {
    (uint8_t)53U, (uint8_t)251U, (uint8_t)96U, (uint8_t)245U, (uint8_t)202U, (uint8_t)15U,
    (uint8_t)60U, (uint8_t)160U, (uint8_t)133U, (uint8_t)66U, (uint8_t)251U, (uint8_t)60U,
    (uint8_t)198U, (uint8_t)65U, (uint8_t)200U, (uint8_t)38U, (uint8_t)58U, (uint8_t)44U,
    (uint8_t)171U, (uint8_t)122U, (uint8_t)144U, (uint8_t)238U, (uint8_t)106U, (uint8_t)94U,
    (uint8_t)21U, (uint8_t)131U, (uint8_t)250U, (uint8_t)194U, (uint8_t)187U, (uint8_t)111U,
    (uint8_t)107U, (uint8_t)209U
  };

static uint8_t
siggen_vectors256_low20[32U] =
  {
    (uint8_t)238U, (uint8_t)89U, (uint8_t)216U, (uint8_t)27U, (uint8_t)201U, (uint8_t)219U,
    (uint8_t)16U, (uint8_t)85U, (uint8_t)204U, (uint8_t)14U, (uint8_t)217U, (uint8_t)123U,
    (uint8_t)21U, (uint8_t)157U, (uint8_t)135U, (uint8_t)132U, (uint8_t)175U, (uint8_t)4U,
    (uint8_t)233U, (uint8_t)133U, (uint8_t)17U, (uint8_t)208U, (uint8_t)169U, (uint8_t)164U,
    (uint8_t)7U, (uint8_t)185U, (uint8_t)155U, (uint8_t)178U, (uint8_t)146U, (uint8_t)87U,
    (uint8_t)46U, (uint8_t)150U
  };

static uint8_t
siggen_vectors256_low21[128U] =
  {
    (uint8_t)9U, (uint8_t)137U, (uint8_t)18U, (uint8_t)36U, (uint8_t)16U, (uint8_t)213U,
    (uint8_t)34U, (uint8_t)175U, (uint8_t)100U, (uint8_t)206U, (uint8_t)176U, (uint8_t)125U,
    (uint8_t)162U, (uint8_t)200U, (uint8_t)101U, (uint8_t)33U, (uint8_t)144U, (uint8_t)70U,
    (uint8_t)180U, (uint8_t)195U, (uint8_t)217U, (uint8_t)217U, (uint8_t)155U, (uint8_t)1U,
    (uint8_t)39U, (uint8_t)140U, (uint8_t)7U, (uint8_t)255U, (uint8_t)99U, (uint8_t)234U,
    (uint8_t)241U, (uint8_t)3U, (uint8_t)156U, (uint8_t)183U, (uint8_t)135U, (uint8_t)174U,
    (uint8_t)158U, (uint8_t)45U, (uint8_t)212U, (uint8_t)100U, (uint8_t)54U, (uint8_t)204U,
    (uint8_t)4U, (uint8_t)21U, (uint8_t)242U, (uint8_t)128U, (uint8_t)197U, (uint8_t)98U,
    (uint8_t)190U, (uint8_t)187U, (uint8_t)131U, (uint8_t)162U, (uint8_t)62U, (uint8_t)99U,
    (uint8_t)158U, (uint8_t)71U, (uint8_t)106U, (uint8_t)2U, (uint8_t)236U, (uint8_t)140U,
    (uint8_t)255U, (uint8_t)126U, (uint8_t)160U, (uint8_t)108U, (uint8_t)209U, (uint8_t)44U,
    (uint8_t)134U, (uint8_t)220U, (uint8_t)195U, (uint8_t)173U, (uint8_t)239U, (uint8_t)191U,
    (uint8_t)26U, (uint8_t)158U, (uint8_t)154U, (uint8_t)155U, (uint8_t)102U, (uint8_t)70U,
    (uint8_t)199U, (uint8_t)89U, (uint8_t)158U, (uint8_t)198U, (uint8_t)49U, (uint8_t)176U,
    (uint8_t)218U, (uint8_t)154U, (uint8_t)96U, (uint8_t)222U, (uint8_t)190U, (uint8_t)185U,
    (uint8_t)179U, (uint8_t)225U, (uint8_t)147U, (uint8_t)36U, (uint8_t)151U, (uint8_t)127U,
    (uint8_t)59U, (uint8_t)79U, (uint8_t)54U, (uint8_t)137U, (uint8_t)44U, (uint8_t)138U,
    (uint8_t)56U, (uint8_t)103U, (uint8_t)28U, (uint8_t)142U, (uint8_t)28U, (uint8_t)200U,
    (uint8_t)229U, (uint8_t)15U, (uint8_t)205U, (uint8_t)80U, (uint8_t)249U, (uint8_t)229U,
    (uint8_t)29U, (uint8_t)234U, (uint8_t)249U, (uint8_t)130U, (uint8_t)114U, (uint8_t)249U,
    (uint8_t)38U, (uint8_t)111U, (uint8_t)199U, (uint8_t)2U, (uint8_t)228U, (uint8_t)229U,
    (uint8_t)124U, (uint8_t)48U
  };

static uint8_t
siggen_vectors256_low22[32U] =
  {
    (uint8_t)163U, (uint8_t)210U, (uint8_t)211U, (uint8_t)183U, (uint8_t)89U, (uint8_t)111U,
    (uint8_t)101U, (uint8_t)146U, (uint8_t)206U, (uint8_t)152U, (uint8_t)180U, (uint8_t)191U,
    (uint8_t)225U, (uint8_t)13U, (uint8_t)65U, (uint8_t)131U, (uint8_t)127U, (uint8_t)16U,
    (uint8_t)2U, (uint8_t)122U, (uint8_t)144U, (uint8_t)215U, (uint8_t)187U, (uint8_t)117U,
    (uint8_t)52U, (uint8_t)148U, (uint8_t)144U, (uint8_t)1U, (uint8_t)140U, (uint8_t)247U,
    (uint8_t)45U, (uint8_t)7U
  };

static uint8_t
siggen_vectors256_low23[32U] =
  {
    (uint8_t)50U, (uint8_t)47U, (uint8_t)128U, (uint8_t)55U, (uint8_t)27U, (uint8_t)246U,
    (uint8_t)224U, (uint8_t)68U, (uint8_t)188U, (uint8_t)73U, (uint8_t)57U, (uint8_t)29U,
    (uint8_t)151U, (uint8_t)193U, (uint8_t)113U, (uint8_t)74U, (uint8_t)184U, (uint8_t)127U,
    (uint8_t)153U, (uint8_t)11U, (uint8_t)148U, (uint8_t)155U, (uint8_t)193U, (uint8_t)120U,
    (uint8_t)203U, (uint8_t)124U, (uint8_t)67U, (uint8_t)183U, (uint8_t)194U, (uint8_t)45U,
    (uint8_t)137U, (uint8_t)225U
  };

static uint8_t
siggen_vectors256_low24[32U] =
  {
    (uint8_t)60U, (uint8_t)21U, (uint8_t)213U, (uint8_t)74U, (uint8_t)92U, (uint8_t)198U,
    (uint8_t)185U, (uint8_t)240U, (uint8_t)157U, (uint8_t)232U, (uint8_t)69U, (uint8_t)126U,
    (uint8_t)135U, (uint8_t)62U, (uint8_t)179U, (uint8_t)222U, (uint8_t)177U, (uint8_t)252U,
    (uint8_t)235U, (uint8_t)84U, (uint8_t)176U, (uint8_t)178U, (uint8_t)149U, (uint8_t)218U,
    (uint8_t)96U, (uint8_t)80U, (uint8_t)41U, (uint8_t)79U, (uint8_t)174U, (uint8_t)127U,
    (uint8_t)217U, (uint8_t)153U
  };

static uint8_t
siggen_vectors256_low25[32U] =
  {
    (uint8_t)36U, (uint8_t)252U, (uint8_t)144U, (uint8_t)225U, (uint8_t)218U, (uint8_t)19U,
    (uint8_t)241U, (uint8_t)126U, (uint8_t)249U, (uint8_t)254U, (uint8_t)132U, (uint8_t)204U,
    (uint8_t)150U, (uint8_t)185U, (uint8_t)71U, (uint8_t)30U, (uint8_t)209U, (uint8_t)170U,
    (uint8_t)172U, (uint8_t)23U, (uint8_t)227U, (uint8_t)164U, (uint8_t)186U, (uint8_t)227U,
    (uint8_t)58U, (uint8_t)17U, (uint8_t)93U, (uint8_t)244U, (uint8_t)229U, (uint8_t)131U,
    (uint8_t)79U, (uint8_t)24U
  };

static uint8_t
siggen_vectors256_low26[32U] =
  {
    (uint8_t)215U, (uint8_t)197U, (uint8_t)98U, (uint8_t)55U, (uint8_t)10U, (uint8_t)246U,
    (uint8_t)23U, (uint8_t)181U, (uint8_t)129U, (uint8_t)200U, (uint8_t)74U, (uint8_t)36U,
    (uint8_t)104U, (uint8_t)204U, (uint8_t)139U, (uint8_t)213U, (uint8_t)11U, (uint8_t)177U,
    (uint8_t)203U, (uint8_t)243U, (uint8_t)34U, (uint8_t)222U, (uint8_t)65U, (uint8_t)183U,
    (uint8_t)136U, (uint8_t)124U, (uint8_t)224U, (uint8_t)124U, (uint8_t)14U, (uint8_t)88U,
    (uint8_t)132U, (uint8_t)202U
  };

static uint8_t
siggen_vectors256_low27[32U] =
  {
    (uint8_t)180U, (uint8_t)109U, (uint8_t)159U, (uint8_t)45U, (uint8_t)140U, (uint8_t)75U,
    (uint8_t)248U, (uint8_t)53U, (uint8_t)70U, (uint8_t)255U, (uint8_t)23U, (uint8_t)143U,
    (uint8_t)29U, (uint8_t)120U, (uint8_t)147U, (uint8_t)124U, (uint8_t)0U, (uint8_t)141U,
    (uint8_t)100U, (uint8_t)232U, (uint8_t)236U, (uint8_t)197U, (uint8_t)203U, (uint8_t)184U,
    (uint8_t)37U, (uint8_t)203U, (uint8_t)33U, (uint8_t)217U, (uint8_t)77U, (uint8_t)103U,
    (uint8_t)13U, (uint8_t)137U
  };

static uint8_t
siggen_vectors256_low28[128U] =
  {
    (uint8_t)220U, (uint8_t)102U, (uint8_t)227U, (uint8_t)159U, (uint8_t)155U, (uint8_t)191U,
    (uint8_t)217U, (uint8_t)134U, (uint8_t)83U, (uint8_t)24U, (uint8_t)83U, (uint8_t)31U,
    (uint8_t)254U, (uint8_t)146U, (uint8_t)7U, (uint8_t)249U, (uint8_t)52U, (uint8_t)250U,
    (uint8_t)97U, (uint8_t)90U, (uint8_t)91U, (uint8_t)40U, (uint8_t)87U, (uint8_t)8U,
    (uint8_t)165U, (uint8_t)233U, (uint8_t)196U, (uint8_t)107U, (uint8_t)119U, (uint8_t)117U,
    (uint8_t)21U, (uint8_t)14U, (uint8_t)129U, (uint8_t)141U, (uint8_t)127U, (uint8_t)36U,
    (uint8_t)210U, (uint8_t)161U, (uint8_t)35U, (uint8_t)223U, (uint8_t)54U, (uint8_t)114U,
    (uint8_t)255U, (uint8_t)242U, (uint8_t)9U, (uint8_t)78U, (uint8_t)63U, (uint8_t)211U,
    (uint8_t)223U, (uint8_t)111U, (uint8_t)190U, (uint8_t)37U, (uint8_t)158U, (uint8_t)57U,
    (uint8_t)137U, (uint8_t)221U, (uint8_t)94U, (uint8_t)223U, (uint8_t)204U, (uint8_t)203U,
    (uint8_t)231U, (uint8_t)212U, (uint8_t)94U, (uint8_t)38U, (uint8_t)167U, (uint8_t)117U,
    (uint8_t)165U, (uint8_t)196U, (uint8_t)50U, (uint8_t)154U, (uint8_t)8U, (uint8_t)79U,
    (uint8_t)5U, (uint8_t)124U, (uint8_t)66U, (uint8_t)193U, (uint8_t)63U, (uint8_t)50U,
    (uint8_t)72U, (uint8_t)227U, (uint8_t)253U, (uint8_t)111U, (uint8_t)12U, (uint8_t)118U,
    (uint8_t)103U, (uint8_t)143U, (uint8_t)137U, (uint8_t)15U, (uint8_t)81U, (uint8_t)60U,
    (uint8_t)50U, (uint8_t)41U, (uint8_t)45U, (uint8_t)211U, (uint8_t)6U, (uint8_t)234U,
    (uint8_t)168U, (uint8_t)74U, (uint8_t)89U, (uint8_t)171U, (uint8_t)227U, (uint8_t)75U,
    (uint8_t)22U, (uint8_t)203U, (uint8_t)94U, (uint8_t)56U, (uint8_t)208U, (uint8_t)232U,
    (uint8_t)133U, (uint8_t)82U, (uint8_t)93U, (uint8_t)16U, (uint8_t)51U, (uint8_t)108U,
    (uint8_t)164U, (uint8_t)67U, (uint8_t)225U, (uint8_t)104U, (uint8_t)42U, (uint8_t)160U,
    (uint8_t)74U, (uint8_t)122U, (uint8_t)248U, (uint8_t)50U, (uint8_t)176U, (uint8_t)238U,
    (uint8_t)228U, (uint8_t)231U
  };

static uint8_t
siggen_vectors256_low29[32U] =
  {
    (uint8_t)83U, (uint8_t)160U, (uint8_t)232U, (uint8_t)168U, (uint8_t)254U, (uint8_t)147U,
    (uint8_t)219U, (uint8_t)1U, (uint8_t)231U, (uint8_t)174U, (uint8_t)148U, (uint8_t)225U,
    (uint8_t)169U, (uint8_t)136U, (uint8_t)42U, (uint8_t)16U, (uint8_t)46U, (uint8_t)189U,
    (uint8_t)7U, (uint8_t)155U, (uint8_t)58U, (uint8_t)83U, (uint8_t)88U, (uint8_t)39U,
    (uint8_t)213U, (uint8_t)131U, (uint8_t)98U, (uint8_t)108U, (uint8_t)39U, (uint8_t)45U,
    (uint8_t)40U, (uint8_t)13U
  };

static uint8_t
siggen_vectors256_low30[32U] =
  {
    (uint8_t)27U, (uint8_t)206U, (uint8_t)196U, (uint8_t)87U, (uint8_t)14U, (uint8_t)30U,
    (uint8_t)194U, (uint8_t)67U, (uint8_t)101U, (uint8_t)150U, (uint8_t)184U, (uint8_t)222U,
    (uint8_t)213U, (uint8_t)143U, (uint8_t)96U, (uint8_t)195U, (uint8_t)177U, (uint8_t)235U,
    (uint8_t)198U, (uint8_t)164U, (uint8_t)3U, (uint8_t)188U, (uint8_t)85U, (uint8_t)67U,
    (uint8_t)4U, (uint8_t)11U, (uint8_t)168U, (uint8_t)41U, (uint8_t)99U, (uint8_t)5U,
    (uint8_t)114U, (uint8_t)68U
  };

static uint8_t
siggen_vectors256_low31[32U] =
  {
    (uint8_t)138U, (uint8_t)246U, (uint8_t)42U, (uint8_t)76U, (uint8_t)104U, (uint8_t)63U,
    (uint8_t)9U, (uint8_t)107U, (uint8_t)40U, (uint8_t)85U, (uint8_t)131U, (uint8_t)32U,
    (uint8_t)115U, (uint8_t)123U, (uint8_t)248U, (uint8_t)59U, (uint8_t)153U, (uint8_t)89U,
    (uint8_t)164U, (uint8_t)106U, (uint8_t)210U, (uint8_t)82U, (uint8_t)16U, (uint8_t)4U,
    (uint8_t)239U, (uint8_t)116U, (uint8_t)207U, (uint8_t)133U, (uint8_t)230U, (uint8_t)116U,
    (uint8_t)148U, (uint8_t)225U
  };

static uint8_t
siggen_vectors256_low32[32U] =
  {
    (uint8_t)93U, (uint8_t)131U, (uint8_t)62U, (uint8_t)141U, (uint8_t)36U, (uint8_t)204U,
    (uint8_t)122U, (uint8_t)64U, (uint8_t)45U, (uint8_t)126U, (uint8_t)231U, (uint8_t)236U,
    (uint8_t)133U, (uint8_t)42U, (uint8_t)53U, (uint8_t)135U, (uint8_t)205U, (uint8_t)222U,
    (uint8_t)180U, (uint8_t)131U, (uint8_t)88U, (uint8_t)206U, (uint8_t)167U, (uint8_t)27U,
    (uint8_t)11U, (uint8_t)237U, (uint8_t)184U, (uint8_t)250U, (uint8_t)190U, (uint8_t)132U,
    (uint8_t)224U, (uint8_t)196U
  };

static uint8_t
siggen_vectors256_low33[32U] =
  {
    (uint8_t)24U, (uint8_t)202U, (uint8_t)175U, (uint8_t)123U, (uint8_t)102U, (uint8_t)53U,
    (uint8_t)7U, (uint8_t)168U, (uint8_t)188U, (uint8_t)217U, (uint8_t)146U, (uint8_t)184U,
    (uint8_t)54U, (uint8_t)222U, (uint8_t)201U, (uint8_t)220U, (uint8_t)87U, (uint8_t)3U,
    (uint8_t)192U, (uint8_t)128U, (uint8_t)175U, (uint8_t)94U, (uint8_t)81U, (uint8_t)223U,
    (uint8_t)163U, (uint8_t)169U, (uint8_t)167U, (uint8_t)195U, (uint8_t)135U, (uint8_t)24U,
    (uint8_t)38U, (uint8_t)4U
  };

static uint8_t
siggen_vectors256_low34[32U] =
  {
    (uint8_t)119U, (uint8_t)198U, (uint8_t)137U, (uint8_t)40U, (uint8_t)172U, (uint8_t)59U,
    (uint8_t)136U, (uint8_t)217U, (uint8_t)133U, (uint8_t)251U, (uint8_t)67U, (uint8_t)251U,
    (uint8_t)97U, (uint8_t)95U, (uint8_t)183U, (uint8_t)255U, (uint8_t)69U, (uint8_t)193U,
    (uint8_t)139U, (uint8_t)165U, (uint8_t)200U, (uint8_t)26U, (uint8_t)247U, (uint8_t)150U,
    (uint8_t)198U, (uint8_t)19U, (uint8_t)223U, (uint8_t)169U, (uint8_t)131U, (uint8_t)82U,
    (uint8_t)210U, (uint8_t)156U
  };

static uint8_t
siggen_vectors256_low35[128U] =
  {
    (uint8_t)96U, (uint8_t)9U, (uint8_t)116U, (uint8_t)231U, (uint8_t)216U, (uint8_t)197U,
    (uint8_t)80U, (uint8_t)142U, (uint8_t)44U, (uint8_t)26U, (uint8_t)171U, (uint8_t)7U,
    (uint8_t)131U, (uint8_t)173U, (uint8_t)13U, (uint8_t)124U, (uint8_t)68U, (uint8_t)148U,
    (uint8_t)171U, (uint8_t)43U, (uint8_t)77U, (uint8_t)162U, (uint8_t)101U, (uint8_t)194U,
    (uint8_t)254U, (uint8_t)73U, (uint8_t)100U, (uint8_t)33U, (uint8_t)196U, (uint8_t)223U,
    (uint8_t)35U, (uint8_t)139U, (uint8_t)11U, (uint8_t)226U, (uint8_t)95U, (uint8_t)37U,
    (uint8_t)101U, (uint8_t)145U, (uint8_t)87U, (uint8_t)200U, (uint8_t)162U, (uint8_t)37U,
    (uint8_t)251U, (uint8_t)3U, (uint8_t)149U, (uint8_t)54U, (uint8_t)7U, (uint8_t)247U,
    (uint8_t)223U, (uint8_t)153U, (uint8_t)106U, (uint8_t)207U, (uint8_t)212U, (uint8_t)2U,
    (uint8_t)241U, (uint8_t)71U, (uint8_t)227U, (uint8_t)122U, (uint8_t)238U, (uint8_t)47U,
    (uint8_t)22U, (uint8_t)147U, (uint8_t)227U, (uint8_t)191U, (uint8_t)28U, (uint8_t)53U,
    (uint8_t)234U, (uint8_t)179U, (uint8_t)174U, (uint8_t)54U, (uint8_t)10U, (uint8_t)43U,
    (uint8_t)217U, (uint8_t)29U, (uint8_t)4U, (uint8_t)98U, (uint8_t)46U, (uint8_t)164U,
    (uint8_t)127U, (uint8_t)131U, (uint8_t)216U, (uint8_t)99U, (uint8_t)210U, (uint8_t)223U,
    (uint8_t)236U, (uint8_t)182U, (uint8_t)24U, (uint8_t)232U, (uint8_t)184U, (uint8_t)189U,
    (uint8_t)195U, (uint8_t)158U, (uint8_t)23U, (uint8_t)209U, (uint8_t)93U, (uint8_t)103U,
    (uint8_t)46U, (uint8_t)238U, (uint8_t)3U, (uint8_t)187U, (uint8_t)76U, (uint8_t)226U,
    (uint8_t)204U, (uint8_t)92U, (uint8_t)246U, (uint8_t)178U, (uint8_t)23U, (uint8_t)229U,
    (uint8_t)250U, (uint8_t)243U, (uint8_t)243U, (uint8_t)54U, (uint8_t)253U, (uint8_t)216U,
    (uint8_t)125U, (uint8_t)151U, (uint8_t)45U, (uint8_t)58U, (uint8_t)139U, (uint8_t)138U,
    (uint8_t)89U, (uint8_t)59U, (uint8_t)168U, (uint8_t)89U, (uint8_t)85U, (uint8_t)204U,
    (uint8_t)157U, (uint8_t)113U
  };

static uint8_t
siggen_vectors256_low36[32U] =
  {
    (uint8_t)74U, (uint8_t)241U, (uint8_t)7U, (uint8_t)232U, (uint8_t)226U, (uint8_t)25U,
    (uint8_t)76U, (uint8_t)131U, (uint8_t)15U, (uint8_t)251U, (uint8_t)113U, (uint8_t)42U,
    (uint8_t)101U, (uint8_t)81U, (uint8_t)27U, (uint8_t)201U, (uint8_t)24U, (uint8_t)106U,
    (uint8_t)19U, (uint8_t)48U, (uint8_t)7U, (uint8_t)133U, (uint8_t)91U, (uint8_t)73U,
    (uint8_t)171U, (uint8_t)75U, (uint8_t)56U, (uint8_t)51U, (uint8_t)174U, (uint8_t)252U,
    (uint8_t)74U, (uint8_t)29U
  };

static uint8_t
siggen_vectors256_low37[32U] =
  {
    (uint8_t)163U, (uint8_t)46U, (uint8_t)80U, (uint8_t)190U, (uint8_t)61U, (uint8_t)174U,
    (uint8_t)44U, (uint8_t)139U, (uint8_t)163U, (uint8_t)245U, (uint8_t)228U, (uint8_t)189U,
    (uint8_t)174U, (uint8_t)20U, (uint8_t)207U, (uint8_t)118U, (uint8_t)69U, (uint8_t)66U,
    (uint8_t)13U, (uint8_t)66U, (uint8_t)94U, (uint8_t)173U, (uint8_t)148U, (uint8_t)3U,
    (uint8_t)108U, (uint8_t)34U, (uint8_t)221U, (uint8_t)108U, (uint8_t)79U, (uint8_t)197U,
    (uint8_t)158U
  };

static uint8_t
siggen_vectors256_low38[32U] =
  {
    (uint8_t)214U, (uint8_t)35U, (uint8_t)191U, (uint8_t)100U, (uint8_t)17U, (uint8_t)96U,
    (uint8_t)194U, (uint8_t)137U, (uint8_t)214U, (uint8_t)116U, (uint8_t)44U, (uint8_t)98U,
    (uint8_t)87U, (uint8_t)174U, (uint8_t)107U, (uint8_t)165U, (uint8_t)116U, (uint8_t)68U,
    (uint8_t)109U, (uint8_t)209U, (uint8_t)208U, (uint8_t)231U, (uint8_t)77U, (uint8_t)179U,
    (uint8_t)170U, (uint8_t)168U, (uint8_t)9U, (uint8_t)0U, (uint8_t)183U, (uint8_t)141U,
    (uint8_t)74U, (uint8_t)233U
  };

static uint8_t
siggen_vectors256_low39[32U] =
  {
    (uint8_t)225U, (uint8_t)143U, (uint8_t)150U, (uint8_t)248U, (uint8_t)77U, (uint8_t)250U,
    (uint8_t)47U, (uint8_t)211U, (uint8_t)205U, (uint8_t)250U, (uint8_t)236U, (uint8_t)145U,
    (uint8_t)89U, (uint8_t)212U, (uint8_t)195U, (uint8_t)56U, (uint8_t)205U, (uint8_t)84U,
    (uint8_t)173U, (uint8_t)49U, (uint8_t)65U, (uint8_t)52U, (uint8_t)240U, (uint8_t)179U,
    (uint8_t)30U, (uint8_t)32U, (uint8_t)89U, (uint8_t)31U, (uint8_t)194U, (uint8_t)56U,
    (uint8_t)208U, (uint8_t)171U
  };

static uint8_t
siggen_vectors256_low40[32U] =
  {
    (uint8_t)133U, (uint8_t)36U, (uint8_t)197U, (uint8_t)2U, (uint8_t)78U, (uint8_t)45U,
    (uint8_t)154U, (uint8_t)115U, (uint8_t)189U, (uint8_t)232U, (uint8_t)199U, (uint8_t)45U,
    (uint8_t)145U, (uint8_t)41U, (uint8_t)245U, (uint8_t)120U, (uint8_t)115U, (uint8_t)187U,
    (uint8_t)173U, (uint8_t)14U, (uint8_t)208U, (uint8_t)82U, (uint8_t)21U, (uint8_t)163U,
    (uint8_t)114U, (uint8_t)168U, (uint8_t)79U, (uint8_t)219U, (uint8_t)199U, (uint8_t)143U,
    (uint8_t)46U, (uint8_t)104U
  };

static uint8_t
siggen_vectors256_low41[32U] =
  {
    (uint8_t)209U, (uint8_t)140U, (uint8_t)44U, (uint8_t)175U, (uint8_t)59U, (uint8_t)16U,
    (uint8_t)114U, (uint8_t)248U, (uint8_t)112U, (uint8_t)100U, (uint8_t)236U, (uint8_t)94U,
    (uint8_t)137U, (uint8_t)83U, (uint8_t)245U, (uint8_t)19U, (uint8_t)1U, (uint8_t)202U,
    (uint8_t)218U, (uint8_t)3U, (uint8_t)70U, (uint8_t)156U, (uint8_t)100U, (uint8_t)2U,
    (uint8_t)68U, (uint8_t)118U, (uint8_t)3U, (uint8_t)40U, (uint8_t)235U, (uint8_t)90U,
    (uint8_t)5U, (uint8_t)203U
  };

static uint8_t
siggen_vectors256_low42[128U] =
  {
    (uint8_t)223U, (uint8_t)166U, (uint8_t)203U, (uint8_t)155U, (uint8_t)57U, (uint8_t)173U,
    (uint8_t)218U, (uint8_t)108U, (uint8_t)116U, (uint8_t)204U, (uint8_t)139U, (uint8_t)42U,
    (uint8_t)139U, (uint8_t)83U, (uint8_t)161U, (uint8_t)44U, (uint8_t)73U, (uint8_t)154U,
    (uint8_t)185U, (uint8_t)222U, (uint8_t)224U, (uint8_t)27U, (uint8_t)65U, (uint8_t)35U,
    (uint8_t)100U, (uint8_t)43U, (uint8_t)79U, (uint8_t)17U, (uint8_t)175U, (uint8_t)51U,
    (uint8_t)106U, (uint8_t)145U, (uint8_t)165U, (uint8_t)201U, (uint8_t)206U, (uint8_t)5U,
    (uint8_t)32U, (uint8_t)235U, (uint8_t)35U, (uint8_t)149U, (uint8_t)166U, (uint8_t)25U,
    (uint8_t)14U, (uint8_t)203U, (uint8_t)246U, (uint8_t)22U, (uint8_t)156U, (uint8_t)76U,
    (uint8_t)186U, (uint8_t)129U, (uint8_t)148U, (uint8_t)29U, (uint8_t)232U, (uint8_t)231U,
    (uint8_t)108U, (uint8_t)156U, (uint8_t)144U, (uint8_t)142U, (uint8_t)184U, (uint8_t)67U,
    (uint8_t)185U, (uint8_t)140U, (uint8_t)233U, (uint8_t)94U, (uint8_t)13U, (uint8_t)162U,
    (uint8_t)156U, (uint8_t)93U, (uint8_t)67U, (uint8_t)136U, (uint8_t)4U, (uint8_t)2U,
    (uint8_t)100U, (uint8_t)224U, (uint8_t)94U, (uint8_t)7U, (uint8_t)3U, (uint8_t)10U,
    (uint8_t)87U, (uint8_t)124U, (uint8_t)197U, (uint8_t)209U, (uint8_t)118U, (uint8_t)56U,
    (uint8_t)113U, (uint8_t)84U, (uint8_t)234U, (uint8_t)186U, (uint8_t)226U, (uint8_t)175U,
    (uint8_t)82U, (uint8_t)168U, (uint8_t)62U, (uint8_t)133U, (uint8_t)198U, (uint8_t)28U,
    (uint8_t)124U, (uint8_t)97U, (uint8_t)218U, (uint8_t)147U, (uint8_t)12U, (uint8_t)155U,
    (uint8_t)25U, (uint8_t)228U, (uint8_t)93U, (uint8_t)126U, (uint8_t)52U, (uint8_t)200U,
    (uint8_t)81U, (uint8_t)109U, (uint8_t)195U, (uint8_t)194U, (uint8_t)56U, (uint8_t)253U,
    (uint8_t)221U, (uint8_t)110U, (uint8_t)69U, (uint8_t)10U, (uint8_t)119U, (uint8_t)69U,
    (uint8_t)93U, (uint8_t)83U, (uint8_t)76U, (uint8_t)72U, (uint8_t)161U, (uint8_t)82U,
    (uint8_t)1U, (uint8_t)11U
  };

static uint8_t
siggen_vectors256_low43[32U] =
  {
    (uint8_t)120U, (uint8_t)223U, (uint8_t)170U, (uint8_t)9U, (uint8_t)241U, (uint8_t)7U,
    (uint8_t)104U, (uint8_t)80U, (uint8_t)179U, (uint8_t)226U, (uint8_t)6U, (uint8_t)228U,
    (uint8_t)119U, (uint8_t)73U, (uint8_t)76U, (uint8_t)221U, (uint8_t)207U, (uint8_t)184U,
    (uint8_t)34U, (uint8_t)170U, (uint8_t)160U, (uint8_t)18U, (uint8_t)132U, (uint8_t)117U,
    (uint8_t)5U, (uint8_t)53U, (uint8_t)146U, (uint8_t)196U, (uint8_t)142U, (uint8_t)186U,
    (uint8_t)244U, (uint8_t)171U
  };

static uint8_t
siggen_vectors256_low44[32U] =
  {
    (uint8_t)139U, (uint8_t)207U, (uint8_t)226U, (uint8_t)167U, (uint8_t)33U, (uint8_t)202U,
    (uint8_t)109U, (uint8_t)117U, (uint8_t)57U, (uint8_t)104U, (uint8_t)245U, (uint8_t)100U,
    (uint8_t)236U, (uint8_t)67U, (uint8_t)21U, (uint8_t)190U, (uint8_t)72U, (uint8_t)87U,
    (uint8_t)226U, (uint8_t)139U, (uint8_t)239U, (uint8_t)25U, (uint8_t)8U, (uint8_t)246U,
    (uint8_t)26U, (uint8_t)54U, (uint8_t)107U, (uint8_t)31U, (uint8_t)3U, (uint8_t)201U,
    (uint8_t)116U, (uint8_t)121U
  };

static uint8_t
siggen_vectors256_low45[32U] =
  {
    (uint8_t)15U, (uint8_t)103U, (uint8_t)87U, (uint8_t)106U, (uint8_t)48U, (uint8_t)184U,
    (uint8_t)226U, (uint8_t)13U, (uint8_t)66U, (uint8_t)50U, (uint8_t)216U, (uint8_t)83U,
    (uint8_t)11U, (uint8_t)82U, (uint8_t)251U, (uint8_t)76U, (uint8_t)137U, (uint8_t)203U,
    (uint8_t)197U, (uint8_t)137U, (uint8_t)237U, (uint8_t)226U, (uint8_t)145U, (uint8_t)228U,
    (uint8_t)153U, (uint8_t)221U, (uint8_t)209U, (uint8_t)95U, (uint8_t)232U, (uint8_t)112U,
    (uint8_t)171U, (uint8_t)150U
  };

static uint8_t
siggen_vectors256_low46[32U] =
  {
    (uint8_t)41U, (uint8_t)85U, (uint8_t)68U, (uint8_t)219U, (uint8_t)178U, (uint8_t)218U,
    (uint8_t)61U, (uint8_t)161U, (uint8_t)112U, (uint8_t)116U, (uint8_t)28U, (uint8_t)155U,
    (uint8_t)44U, (uint8_t)101U, (uint8_t)81U, (uint8_t)212U, (uint8_t)10U, (uint8_t)247U,
    (uint8_t)237U, (uint8_t)78U, (uint8_t)137U, (uint8_t)20U, (uint8_t)69U, (uint8_t)241U,
    (uint8_t)26U, (uint8_t)2U, (uint8_t)182U, (uint8_t)106U, (uint8_t)92U, (uint8_t)37U,
    (uint8_t)138U, (uint8_t)119U
  };

static uint8_t
siggen_vectors256_low47[32U] =
  {
    (uint8_t)197U, (uint8_t)161U, (uint8_t)134U, (uint8_t)215U, (uint8_t)45U, (uint8_t)244U,
    (uint8_t)82U, (uint8_t)1U, (uint8_t)84U, (uint8_t)128U, (uint8_t)247U, (uint8_t)243U,
    (uint8_t)56U, (uint8_t)151U, (uint8_t)11U, (uint8_t)254U, (uint8_t)130U, (uint8_t)80U,
    (uint8_t)135U, (uint8_t)240U, (uint8_t)92U, (uint8_t)0U, (uint8_t)136U, (uint8_t)217U,
    (uint8_t)83U, (uint8_t)5U, (uint8_t)248U, (uint8_t)122U, (uint8_t)172U, (uint8_t)201U,
    (uint8_t)178U, (uint8_t)84U
  };

static uint8_t
siggen_vectors256_low48[32U] =
  {
    (uint8_t)132U, (uint8_t)165U, (uint8_t)143U, (uint8_t)158U, (uint8_t)157U, (uint8_t)158U,
    (uint8_t)115U, (uint8_t)83U, (uint8_t)68U, (uint8_t)179U, (uint8_t)22U, (uint8_t)177U,
    (uint8_t)170U, (uint8_t)26U, (uint8_t)181U, (uint8_t)24U, (uint8_t)86U, (uint8_t)101U,
    (uint8_t)184U, (uint8_t)81U, (uint8_t)71U, (uint8_t)220U, (uint8_t)130U, (uint8_t)217U,
    (uint8_t)46U, (uint8_t)150U, (uint8_t)157U, (uint8_t)123U, (uint8_t)238U, (uint8_t)49U,
    (uint8_t)202U, (uint8_t)48U
  };

static uint8_t
siggen_vectors256_low49[128U] =
  {
    (uint8_t)81U, (uint8_t)210U, (uint8_t)84U, (uint8_t)124U, (uint8_t)191U, (uint8_t)249U,
    (uint8_t)36U, (uint8_t)49U, (uint8_t)23U, (uint8_t)74U, (uint8_t)167U, (uint8_t)252U,
    (uint8_t)115U, (uint8_t)2U, (uint8_t)19U, (uint8_t)149U, (uint8_t)25U, (uint8_t)217U,
    (uint8_t)128U, (uint8_t)113U, (uint8_t)199U, (uint8_t)85U, (uint8_t)255U, (uint8_t)28U,
    (uint8_t)146U, (uint8_t)228U, (uint8_t)105U, (uint8_t)75U, (uint8_t)88U, (uint8_t)88U,
    (uint8_t)126U, (uint8_t)165U, (uint8_t)96U, (uint8_t)247U, (uint8_t)47U, (uint8_t)50U,
    (uint8_t)252U, (uint8_t)109U, (uint8_t)212U, (uint8_t)222U, (uint8_t)231U, (uint8_t)210U,
    (uint8_t)43U, (uint8_t)183U, (uint8_t)56U, (uint8_t)115U, (uint8_t)129U, (uint8_t)208U,
    (uint8_t)37U, (uint8_t)110U, (uint8_t)40U, (uint8_t)98U, (uint8_t)208U, (uint8_t)100U,
    (uint8_t)76U, (uint8_t)223U, (uint8_t)44U, (uint8_t)39U, (uint8_t)124U, (uint8_t)93U,
    (uint8_t)116U, (uint8_t)15U, (uint8_t)160U, (uint8_t)137U, (uint8_t)131U, (uint8_t)14U,
    (uint8_t)181U, (uint8_t)43U, (uint8_t)247U, (uint8_t)157U, (uint8_t)30U, (uint8_t)117U,
    (uint8_t)184U, (uint8_t)89U, (uint8_t)110U, (uint8_t)207U, (uint8_t)14U, (uint8_t)165U,
    (uint8_t)138U, (uint8_t)11U, (uint8_t)157U, (uint8_t)246U, (uint8_t)30U, (uint8_t)12U,
    (uint8_t)151U, (uint8_t)84U, (uint8_t)191U, (uint8_t)205U, (uint8_t)98U, (uint8_t)239U,
    (uint8_t)171U, (uint8_t)110U, (uint8_t)161U, (uint8_t)189U, (uint8_t)33U, (uint8_t)107U,
    (uint8_t)241U, (uint8_t)129U, (uint8_t)197U, (uint8_t)89U, (uint8_t)61U, (uint8_t)167U,
    (uint8_t)159U, (uint8_t)16U, (uint8_t)19U, (uint8_t)90U, (uint8_t)155U, (uint8_t)198U,
    (uint8_t)225U, (uint8_t)100U, (uint8_t)241U, (uint8_t)133U, (uint8_t)75U, (uint8_t)200U,
    (uint8_t)133U, (uint8_t)151U, (uint8_t)52U, (uint8_t)52U, (uint8_t)26U, (uint8_t)173U,
    (uint8_t)35U, (uint8_t)123U, (uint8_t)162U, (uint8_t)154U, (uint8_t)129U, (uint8_t)163U,
    (uint8_t)252U, (uint8_t)139U
  };

static uint8_t
siggen_vectors256_low50[32U] =
  {
    (uint8_t)128U, (uint8_t)230U, (uint8_t)146U, (uint8_t)227U, (uint8_t)235U, (uint8_t)159U,
    (uint8_t)205U, (uint8_t)140U, (uint8_t)125U, (uint8_t)68U, (uint8_t)231U, (uint8_t)222U,
    (uint8_t)159U, (uint8_t)122U, (uint8_t)89U, (uint8_t)82U, (uint8_t)104U, (uint8_t)100U,
    (uint8_t)7U, (uint8_t)249U, (uint8_t)0U, (uint8_t)37U, (uint8_t)161U, (uint8_t)216U,
    (uint8_t)126U, (uint8_t)82U, (uint8_t)199U, (uint8_t)9U, (uint8_t)106U, (uint8_t)98U,
    (uint8_t)97U, (uint8_t)138U
  };

static uint8_t
siggen_vectors256_low51[32U] =
  {
    (uint8_t)168U, (uint8_t)139U, (uint8_t)200U, (uint8_t)67U, (uint8_t)2U, (uint8_t)121U,
    (uint8_t)200U, (uint8_t)192U, (uint8_t)64U, (uint8_t)10U, (uint8_t)119U, (uint8_t)215U,
    (uint8_t)81U, (uint8_t)242U, (uint8_t)108U, (uint8_t)10U, (uint8_t)188U, (uint8_t)147U,
    (uint8_t)229U, (uint8_t)222U, (uint8_t)74U, (uint8_t)217U, (uint8_t)164U, (uint8_t)22U,
    (uint8_t)99U, (uint8_t)87U, (uint8_t)149U, (uint8_t)47U, (uint8_t)224U, (uint8_t)65U,
    (uint8_t)231U, (uint8_t)103U
  };

static uint8_t
siggen_vectors256_low52[32U] =
  {
    (uint8_t)45U, (uint8_t)54U, (uint8_t)90U, (uint8_t)30U, (uint8_t)239U, (uint8_t)37U,
    (uint8_t)234U, (uint8_t)213U, (uint8_t)121U, (uint8_t)204U, (uint8_t)154U, (uint8_t)6U,
    (uint8_t)155U, (uint8_t)106U, (uint8_t)188U, (uint8_t)27U, (uint8_t)22U, (uint8_t)184U,
    (uint8_t)28U, (uint8_t)53U, (uint8_t)241U, (uint8_t)135U, (uint8_t)133U, (uint8_t)206U,
    (uint8_t)38U, (uint8_t)161U, (uint8_t)11U, (uint8_t)166U, (uint8_t)209U, (uint8_t)56U,
    (uint8_t)17U, (uint8_t)133U
  };

static uint8_t
siggen_vectors256_low53[32U] =
  {
    (uint8_t)124U, (uint8_t)128U, (uint8_t)253U, (uint8_t)102U, (uint8_t)214U, (uint8_t)44U,
    (uint8_t)192U, (uint8_t)118U, (uint8_t)206U, (uint8_t)242U, (uint8_t)208U, (uint8_t)48U,
    (uint8_t)193U, (uint8_t)124U, (uint8_t)10U, (uint8_t)105U, (uint8_t)201U, (uint8_t)150U,
    (uint8_t)17U, (uint8_t)84U, (uint8_t)156U, (uint8_t)179U, (uint8_t)44U, (uint8_t)79U,
    (uint8_t)246U, (uint8_t)98U, (uint8_t)71U, (uint8_t)90U, (uint8_t)219U, (uint8_t)232U,
    (uint8_t)75U, (uint8_t)34U
  };

static uint8_t
siggen_vectors256_low54[32U] =
  {
    (uint8_t)157U, (uint8_t)12U, (uint8_t)106U, (uint8_t)251U, (uint8_t)109U, (uint8_t)243U,
    (uint8_t)188U, (uint8_t)237U, (uint8_t)69U, (uint8_t)91U, (uint8_t)69U, (uint8_t)156U,
    (uint8_t)194U, (uint8_t)19U, (uint8_t)135U, (uint8_t)225U, (uint8_t)73U, (uint8_t)41U,
    (uint8_t)57U, (uint8_t)38U, (uint8_t)100U, (uint8_t)187U, (uint8_t)135U, (uint8_t)65U,
    (uint8_t)163U, (uint8_t)105U, (uint8_t)58U, (uint8_t)23U, (uint8_t)149U, (uint8_t)202U,
    (uint8_t)105U, (uint8_t)2U
  };

static uint8_t
siggen_vectors256_low55[32U] =
  {
    (uint8_t)215U, (uint8_t)249U, (uint8_t)221U, (uint8_t)209U, (uint8_t)145U, (uint8_t)241U,
    (uint8_t)244U, (uint8_t)18U, (uint8_t)134U, (uint8_t)148U, (uint8_t)41U, (uint8_t)32U,
    (uint8_t)158U, (uint8_t)227U, (uint8_t)129U, (uint8_t)76U, (uint8_t)117U, (uint8_t)199U,
    (uint8_t)47U, (uint8_t)164U, (uint8_t)106U, (uint8_t)156U, (uint8_t)204U, (uint8_t)248U,
    (uint8_t)4U, (uint8_t)162U, (uint8_t)245U, (uint8_t)204U, (uint8_t)11U, (uint8_t)126U,
    (uint8_t)115U, (uint8_t)159U
  };

static uint8_t
siggen_vectors256_low56[128U] =
  {
    (uint8_t)85U, (uint8_t)140U, (uint8_t)42U, (uint8_t)193U, (uint8_t)48U, (uint8_t)38U,
    (uint8_t)64U, (uint8_t)43U, (uint8_t)173U, (uint8_t)74U, (uint8_t)10U, (uint8_t)131U,
    (uint8_t)235U, (uint8_t)201U, (uint8_t)70U, (uint8_t)142U, (uint8_t)80U, (uint8_t)247U,
    (uint8_t)255U, (uint8_t)171U, (uint8_t)6U, (uint8_t)214U, (uint8_t)249U, (uint8_t)129U,
    (uint8_t)229U, (uint8_t)219U, (uint8_t)29U, (uint8_t)8U, (uint8_t)32U, (uint8_t)152U,
    (uint8_t)6U, (uint8_t)91U, (uint8_t)207U, (uint8_t)246U, (uint8_t)242U, (uint8_t)26U,
    (uint8_t)122U, (uint8_t)116U, (uint8_t)85U, (uint8_t)139U, (uint8_t)30U, (uint8_t)134U,
    (uint8_t)18U, (uint8_t)145U, (uint8_t)75U, (uint8_t)139U, (uint8_t)90U, (uint8_t)10U,
    (uint8_t)162U, (uint8_t)142U, (uint8_t)213U, (uint8_t)181U, (uint8_t)116U, (uint8_t)195U,
    (uint8_t)106U, (uint8_t)196U, (uint8_t)234U, (uint8_t)88U, (uint8_t)104U, (uint8_t)67U,
    (uint8_t)42U, (uint8_t)98U, (uint8_t)187U, (uint8_t)142U, (uint8_t)240U, (uint8_t)105U,
    (uint8_t)93U, (uint8_t)39U, (uint8_t)193U, (uint8_t)227U, (uint8_t)206U, (uint8_t)175U,
    (uint8_t)117U, (uint8_t)199U, (uint8_t)178U, (uint8_t)81U, (uint8_t)198U, (uint8_t)93U,
    (uint8_t)219U, (uint8_t)38U, (uint8_t)134U, (uint8_t)150U, (uint8_t)240U, (uint8_t)124U,
    (uint8_t)22U, (uint8_t)210U, (uint8_t)118U, (uint8_t)121U, (uint8_t)115U, (uint8_t)216U,
    (uint8_t)91U, (uint8_t)235U, (uint8_t)68U, (uint8_t)63U, (uint8_t)33U, (uint8_t)30U,
    (uint8_t)100U, (uint8_t)69U, (uint8_t)231U, (uint8_t)254U, (uint8_t)93U, (uint8_t)70U,
    (uint8_t)240U, (uint8_t)220U, (uint8_t)231U, (uint8_t)13U, (uint8_t)88U, (uint8_t)164U,
    (uint8_t)205U, (uint8_t)159U, (uint8_t)231U, (uint8_t)6U, (uint8_t)136U, (uint8_t)192U,
    (uint8_t)53U, (uint8_t)104U, (uint8_t)142U, (uint8_t)168U, (uint8_t)198U, (uint8_t)186U,
    (uint8_t)236U, (uint8_t)101U, (uint8_t)165U, (uint8_t)252U, (uint8_t)126U, (uint8_t)44U,
    (uint8_t)147U, (uint8_t)232U
  };

static uint8_t
siggen_vectors256_low57[32U] =
  {
    (uint8_t)94U, (uint8_t)102U, (uint8_t)108U, (uint8_t)13U, (uint8_t)176U, (uint8_t)33U,
    (uint8_t)76U, (uint8_t)59U, (uint8_t)98U, (uint8_t)122U, (uint8_t)142U, (uint8_t)72U,
    (uint8_t)84U, (uint8_t)28U, (uint8_t)200U, (uint8_t)74U, (uint8_t)139U, (uint8_t)111U,
    (uint8_t)209U, (uint8_t)95U, (uint8_t)48U, (uint8_t)13U, (uint8_t)164U, (uint8_t)223U,
    (uint8_t)245U, (uint8_t)209U, (uint8_t)138U, (uint8_t)236U, (uint8_t)108U, (uint8_t)85U,
    (uint8_t)184U, (uint8_t)129U
  };

static uint8_t
siggen_vectors256_low58[32U] =
  {
    (uint8_t)27U, (uint8_t)196U, (uint8_t)135U, (uint8_t)87U, (uint8_t)15U, (uint8_t)4U,
    (uint8_t)13U, (uint8_t)201U, (uint8_t)65U, (uint8_t)150U, (uint8_t)201U, (uint8_t)190U,
    (uint8_t)254U, (uint8_t)138U, (uint8_t)178U, (uint8_t)182U, (uint8_t)222U, (uint8_t)119U,
    (uint8_t)32U, (uint8_t)139U, (uint8_t)31U, (uint8_t)56U, (uint8_t)189U, (uint8_t)170U,
    (uint8_t)226U, (uint8_t)143U, (uint8_t)150U, (uint8_t)69U, (uint8_t)196U, (uint8_t)210U,
    (uint8_t)188U, (uint8_t)58U
  };

static uint8_t
siggen_vectors256_low59[32U] =
  {
    (uint8_t)236U, (uint8_t)129U, (uint8_t)96U, (uint8_t)42U, (uint8_t)189U, (uint8_t)131U,
    (uint8_t)69U, (uint8_t)231U, (uint8_t)24U, (uint8_t)103U, (uint8_t)200U, (uint8_t)33U,
    (uint8_t)3U, (uint8_t)19U, (uint8_t)115U, (uint8_t)120U, (uint8_t)101U, (uint8_t)184U,
    (uint8_t)170U, (uint8_t)24U, (uint8_t)104U, (uint8_t)81U, (uint8_t)225U, (uint8_t)180U,
    (uint8_t)142U, (uint8_t)172U, (uint8_t)161U, (uint8_t)64U, (uint8_t)50U, (uint8_t)15U,
    (uint8_t)93U, (uint8_t)143U
  };

static uint8_t
siggen_vectors256_low60[32U] =
  {
    (uint8_t)46U, (uint8_t)118U, (uint8_t)37U, (uint8_t)164U, (uint8_t)136U, (uint8_t)116U,
    (uint8_t)216U, (uint8_t)108U, (uint8_t)158U, (uint8_t)70U, (uint8_t)127U, (uint8_t)137U,
    (uint8_t)10U, (uint8_t)170U, (uint8_t)124U, (uint8_t)214U, (uint8_t)235U, (uint8_t)223U,
    (uint8_t)113U, (uint8_t)192U, (uint8_t)16U, (uint8_t)43U, (uint8_t)253U, (uint8_t)207U,
    (uint8_t)162U, (uint8_t)69U, (uint8_t)101U, (uint8_t)214U, (uint8_t)175U, (uint8_t)63U,
    (uint8_t)220U, (uint8_t)233U
  };

static uint8_t
siggen_vectors256_low61[32U] =
  {
    (uint8_t)47U, (uint8_t)158U, (uint8_t)43U, (uint8_t)78U, (uint8_t)159U, (uint8_t)116U,
    (uint8_t)124U, (uint8_t)101U, (uint8_t)127U, (uint8_t)112U, (uint8_t)91U, (uint8_t)255U,
    (uint8_t)209U, (uint8_t)36U, (uint8_t)238U, (uint8_t)23U, (uint8_t)139U, (uint8_t)188U,
    (uint8_t)83U, (uint8_t)145U, (uint8_t)200U, (uint8_t)109U, (uint8_t)5U, (uint8_t)103U,
    (uint8_t)23U, (uint8_t)177U, (uint8_t)64U, (uint8_t)193U, (uint8_t)83U, (uint8_t)87U,
    (uint8_t)15U, (uint8_t)217U
  };

static uint8_t
siggen_vectors256_low62[32U] =
  {
    (uint8_t)245U, (uint8_t)65U, (uint8_t)59U, (uint8_t)253U, (uint8_t)133U, (uint8_t)148U,
    (uint8_t)157U, (uint8_t)168U, (uint8_t)216U, (uint8_t)61U, (uint8_t)232U, (uint8_t)58U,
    (uint8_t)176U, (uint8_t)209U, (uint8_t)155U, (uint8_t)41U, (uint8_t)134U, (uint8_t)97U,
    (uint8_t)62U, (uint8_t)34U, (uint8_t)77U, (uint8_t)25U, (uint8_t)1U, (uint8_t)215U,
    (uint8_t)105U, (uint8_t)25U, (uint8_t)222U, (uint8_t)35U, (uint8_t)204U, (uint8_t)208U,
    (uint8_t)49U, (uint8_t)153U
  };

static uint8_t
siggen_vectors256_low63[128U] =
  {
    (uint8_t)77U, (uint8_t)85U, (uint8_t)201U, (uint8_t)158U, (uint8_t)246U, (uint8_t)189U,
    (uint8_t)84U, (uint8_t)98U, (uint8_t)22U, (uint8_t)98U, (uint8_t)195U, (uint8_t)209U,
    (uint8_t)16U, (uint8_t)195U, (uint8_t)203U, (uint8_t)98U, (uint8_t)124U, (uint8_t)3U,
    (uint8_t)214U, (uint8_t)49U, (uint8_t)19U, (uint8_t)147U, (uint8_t)178U, (uint8_t)100U,
    (uint8_t)171U, (uint8_t)151U, (uint8_t)185U, (uint8_t)10U, (uint8_t)75U, (uint8_t)21U,
    (uint8_t)33U, (uint8_t)74U, (uint8_t)85U, (uint8_t)147U, (uint8_t)186U, (uint8_t)37U,
    (uint8_t)16U, (uint8_t)165U, (uint8_t)61U, (uint8_t)99U, (uint8_t)251U, (uint8_t)52U,
    (uint8_t)190U, (uint8_t)37U, (uint8_t)31U, (uint8_t)172U, (uint8_t)182U, (uint8_t)151U,
    (uint8_t)201U, (uint8_t)115U, (uint8_t)225U, (uint8_t)27U, (uint8_t)102U, (uint8_t)92U,
    (uint8_t)183U, (uint8_t)146U, (uint8_t)15U, (uint8_t)22U, (uint8_t)132U, (uint8_t)176U,
    (uint8_t)3U, (uint8_t)27U, (uint8_t)77U, (uint8_t)211U, (uint8_t)112U, (uint8_t)203U,
    (uint8_t)146U, (uint8_t)124U, (uint8_t)167U, (uint8_t)22U, (uint8_t)139U, (uint8_t)11U,
    (uint8_t)248U, (uint8_t)173U, (uint8_t)40U, (uint8_t)94U, (uint8_t)5U, (uint8_t)233U,
    (uint8_t)227U, (uint8_t)30U, (uint8_t)52U, (uint8_t)188U, (uint8_t)36U, (uint8_t)2U,
    (uint8_t)71U, (uint8_t)57U, (uint8_t)253U, (uint8_t)193U, (uint8_t)11U, (uint8_t)120U,
    (uint8_t)88U, (uint8_t)111U, (uint8_t)41U, (uint8_t)239U, (uint8_t)249U, (uint8_t)68U,
    (uint8_t)18U, (uint8_t)3U, (uint8_t)78U, (uint8_t)59U, (uint8_t)96U, (uint8_t)110U,
    (uint8_t)216U, (uint8_t)80U, (uint8_t)236U, (uint8_t)44U, (uint8_t)25U, (uint8_t)0U,
    (uint8_t)232U, (uint8_t)230U, (uint8_t)129U, (uint8_t)81U, (uint8_t)252U, (uint8_t)74U,
    (uint8_t)238U, (uint8_t)90U, (uint8_t)222U, (uint8_t)187U, (uint8_t)6U, (uint8_t)110U,
    (uint8_t)182U, (uint8_t)218U, (uint8_t)78U, (uint8_t)170U, (uint8_t)86U, (uint8_t)129U,
    (uint8_t)55U, (uint8_t)142U
  };

static uint8_t
siggen_vectors256_low64[32U] =
  {
    (uint8_t)247U, (uint8_t)63U, (uint8_t)69U, (uint8_t)82U, (uint8_t)113U, (uint8_t)200U,
    (uint8_t)119U, (uint8_t)196U, (uint8_t)213U, (uint8_t)51U, (uint8_t)70U, (uint8_t)39U,
    (uint8_t)227U, (uint8_t)124U, (uint8_t)39U, (uint8_t)143U, (uint8_t)104U, (uint8_t)209U,
    (uint8_t)67U, (uint8_t)1U, (uint8_t)75U, (uint8_t)10U, (uint8_t)5U, (uint8_t)170U, (uint8_t)98U,
    (uint8_t)243U, (uint8_t)8U, (uint8_t)178U, (uint8_t)16U, (uint8_t)28U, (uint8_t)83U,
    (uint8_t)8U
  };

static uint8_t
siggen_vectors256_low65[32U] =
  {
    (uint8_t)184U, (uint8_t)24U, (uint8_t)139U, (uint8_t)214U, (uint8_t)135U, (uint8_t)1U,
    (uint8_t)252U, (uint8_t)57U, (uint8_t)109U, (uint8_t)171U, (uint8_t)83U, (uint8_t)18U,
    (uint8_t)93U, (uint8_t)77U, (uint8_t)40U, (uint8_t)234U, (uint8_t)51U, (uint8_t)169U,
    (uint8_t)29U, (uint8_t)175U, (uint8_t)109U, (uint8_t)33U, (uint8_t)72U, (uint8_t)95U,
    (uint8_t)71U, (uint8_t)112U, (uint8_t)246U, (uint8_t)234U, (uint8_t)140U, (uint8_t)86U,
    (uint8_t)93U, (uint8_t)222U
  };

static uint8_t
siggen_vectors256_low66[32U] =
  {
    (uint8_t)66U, (uint8_t)63U, (uint8_t)5U, (uint8_t)136U, (uint8_t)16U, (uint8_t)242U,
    (uint8_t)119U, (uint8_t)248U, (uint8_t)254U, (uint8_t)7U, (uint8_t)111U, (uint8_t)109U,
    (uint8_t)181U, (uint8_t)110U, (uint8_t)146U, (uint8_t)133U, (uint8_t)161U, (uint8_t)191U,
    (uint8_t)44U, (uint8_t)42U, (uint8_t)29U, (uint8_t)174U, (uint8_t)20U, (uint8_t)80U,
    (uint8_t)149U, (uint8_t)237U, (uint8_t)217U, (uint8_t)192U, (uint8_t)73U, (uint8_t)112U,
    (uint8_t)188U, (uint8_t)74U
  };

static uint8_t
siggen_vectors256_low67[32U] =
  {
    (uint8_t)98U, (uint8_t)248U, (uint8_t)102U, (uint8_t)95U, (uint8_t)214U, (uint8_t)226U,
    (uint8_t)107U, (uint8_t)63U, (uint8_t)160U, (uint8_t)105U, (uint8_t)232U, (uint8_t)82U,
    (uint8_t)129U, (uint8_t)119U, (uint8_t)122U, (uint8_t)155U, (uint8_t)31U, (uint8_t)13U,
    (uint8_t)253U, (uint8_t)44U, (uint8_t)11U, (uint8_t)159U, (uint8_t)84U, (uint8_t)160U,
    (uint8_t)134U, (uint8_t)208U, (uint8_t)193U, (uint8_t)9U, (uint8_t)255U, (uint8_t)159U,
    (uint8_t)214U, (uint8_t)21U
  };

static uint8_t
siggen_vectors256_low68[32U] =
  {
    (uint8_t)28U, (uint8_t)198U, (uint8_t)40U, (uint8_t)83U, (uint8_t)61U, (uint8_t)0U, (uint8_t)4U,
    (uint8_t)178U, (uint8_t)178U, (uint8_t)14U, (uint8_t)127U, (uint8_t)75U, (uint8_t)170U,
    (uint8_t)208U, (uint8_t)184U, (uint8_t)187U, (uint8_t)94U, (uint8_t)6U, (uint8_t)115U,
    (uint8_t)219U, (uint8_t)21U, (uint8_t)155U, (uint8_t)188U, (uint8_t)207U, (uint8_t)146U,
    (uint8_t)73U, (uint8_t)26U, (uint8_t)239U, (uint8_t)97U, (uint8_t)252U, (uint8_t)150U,
    (uint8_t)32U
  };

static uint8_t
siggen_vectors256_low69[32U] =
  {
    (uint8_t)136U, (uint8_t)14U, (uint8_t)11U, (uint8_t)191U, (uint8_t)130U, (uint8_t)168U,
    (uint8_t)207U, (uint8_t)129U, (uint8_t)142U, (uint8_t)212U, (uint8_t)107U, (uint8_t)160U,
    (uint8_t)60U, (uint8_t)240U, (uint8_t)252U, (uint8_t)108U, (uint8_t)137U, (uint8_t)142U,
    (uint8_t)54U, (uint8_t)252U, (uint8_t)163U, (uint8_t)108U, (uint8_t)199U, (uint8_t)253U,
    (uint8_t)177U, (uint8_t)210U, (uint8_t)219U, (uint8_t)117U, (uint8_t)3U, (uint8_t)99U,
    (uint8_t)68U, (uint8_t)48U
  };

static uint8_t
siggen_vectors256_low70[128U] =
  {
    (uint8_t)248U, (uint8_t)36U, (uint8_t)138U, (uint8_t)212U, (uint8_t)125U, (uint8_t)151U,
    (uint8_t)193U, (uint8_t)140U, (uint8_t)152U, (uint8_t)79U, (uint8_t)31U, (uint8_t)92U,
    (uint8_t)16U, (uint8_t)149U, (uint8_t)13U, (uint8_t)193U, (uint8_t)64U, (uint8_t)71U,
    (uint8_t)19U, (uint8_t)197U, (uint8_t)107U, (uint8_t)110U, (uint8_t)163U, (uint8_t)151U,
    (uint8_t)224U, (uint8_t)30U, (uint8_t)109U, (uint8_t)217U, (uint8_t)37U, (uint8_t)233U,
    (uint8_t)3U, (uint8_t)180U, (uint8_t)250U, (uint8_t)223U, (uint8_t)226U, (uint8_t)201U,
    (uint8_t)232U, (uint8_t)119U, (uint8_t)22U, (uint8_t)158U, (uint8_t)113U, (uint8_t)206U,
    (uint8_t)60U, (uint8_t)127U, (uint8_t)229U, (uint8_t)206U, (uint8_t)112U, (uint8_t)238U,
    (uint8_t)66U, (uint8_t)85U, (uint8_t)217U, (uint8_t)205U, (uint8_t)194U, (uint8_t)111U,
    (uint8_t)105U, (uint8_t)67U, (uint8_t)191U, (uint8_t)72U, (uint8_t)104U, (uint8_t)120U,
    (uint8_t)116U, (uint8_t)222U, (uint8_t)100U, (uint8_t)246U, (uint8_t)207U, (uint8_t)48U,
    (uint8_t)160U, (uint8_t)18U, (uint8_t)81U, (uint8_t)46U, (uint8_t)120U, (uint8_t)123U,
    (uint8_t)136U, (uint8_t)5U, (uint8_t)155U, (uint8_t)191U, (uint8_t)86U, (uint8_t)17U,
    (uint8_t)98U, (uint8_t)189U, (uint8_t)204U, (uint8_t)35U, (uint8_t)163U, (uint8_t)116U,
    (uint8_t)44U, (uint8_t)131U, (uint8_t)90U, (uint8_t)193U, (uint8_t)68U, (uint8_t)204U,
    (uint8_t)20U, (uint8_t)22U, (uint8_t)123U, (uint8_t)27U, (uint8_t)214U, (uint8_t)114U,
    (uint8_t)126U, (uint8_t)148U, (uint8_t)5U, (uint8_t)64U, (uint8_t)169U, (uint8_t)201U,
    (uint8_t)159U, (uint8_t)60U, (uint8_t)187U, (uint8_t)65U, (uint8_t)251U, (uint8_t)29U,
    (uint8_t)203U, (uint8_t)0U, (uint8_t)215U, (uint8_t)109U, (uint8_t)218U, (uint8_t)4U,
    (uint8_t)153U, (uint8_t)88U, (uint8_t)71U, (uint8_t)198U, (uint8_t)87U, (uint8_t)244U,
    (uint8_t)193U, (uint8_t)157U, (uint8_t)48U, (uint8_t)62U, (uint8_t)176U, (uint8_t)158U,
    (uint8_t)180U, (uint8_t)138U
  };

static uint8_t
siggen_vectors256_low71[32U] =
  {
    (uint8_t)178U, (uint8_t)13U, (uint8_t)112U, (uint8_t)93U, (uint8_t)155U, (uint8_t)215U,
    (uint8_t)194U, (uint8_t)184U, (uint8_t)220U, (uint8_t)96U, (uint8_t)57U, (uint8_t)58U,
    (uint8_t)83U, (uint8_t)87U, (uint8_t)246U, (uint8_t)50U, (uint8_t)153U, (uint8_t)14U,
    (uint8_t)89U, (uint8_t)154U, (uint8_t)9U, (uint8_t)117U, (uint8_t)87U, (uint8_t)58U,
    (uint8_t)198U, (uint8_t)127U, (uint8_t)216U, (uint8_t)155U, (uint8_t)73U, (uint8_t)24U,
    (uint8_t)121U, (uint8_t)6U
  };

static uint8_t
siggen_vectors256_low72[32U] =
  {
    (uint8_t)81U, (uint8_t)249U, (uint8_t)157U, (uint8_t)45U, (uint8_t)82U, (uint8_t)212U,
    (uint8_t)166U, (uint8_t)231U, (uint8_t)52U, (uint8_t)72U, (uint8_t)74U, (uint8_t)1U,
    (uint8_t)139U, (uint8_t)124U, (uint8_t)162U, (uint8_t)248U, (uint8_t)149U, (uint8_t)194U,
    (uint8_t)146U, (uint8_t)155U, (uint8_t)103U, (uint8_t)84U, (uint8_t)163U, (uint8_t)160U,
    (uint8_t)50U, (uint8_t)36U, (uint8_t)208U, (uint8_t)122U, (uint8_t)230U, (uint8_t)17U,
    (uint8_t)102U, (uint8_t)206U
  };

static uint8_t
siggen_vectors256_low73[32U] =
  {
    (uint8_t)71U, (uint8_t)55U, (uint8_t)218U, (uint8_t)150U, (uint8_t)60U, (uint8_t)110U,
    (uint8_t)247U, (uint8_t)36U, (uint8_t)127U, (uint8_t)184U, (uint8_t)141U, (uint8_t)25U,
    (uint8_t)249U, (uint8_t)176U, (uint8_t)198U, (uint8_t)103U, (uint8_t)202U, (uint8_t)199U,
    (uint8_t)254U, (uint8_t)18U, (uint8_t)131U, (uint8_t)127U, (uint8_t)218U, (uint8_t)184U,
    (uint8_t)140U, (uint8_t)102U, (uint8_t)241U, (uint8_t)13U, (uint8_t)60U, (uint8_t)20U,
    (uint8_t)202U, (uint8_t)209U
  };

static uint8_t
siggen_vectors256_low74[32U] =
  {
    (uint8_t)114U, (uint8_t)182U, (uint8_t)86U, (uint8_t)246U, (uint8_t)179U, (uint8_t)91U,
    (uint8_t)156U, (uint8_t)203U, (uint8_t)199U, (uint8_t)18U, (uint8_t)201U, (uint8_t)241U,
    (uint8_t)243U, (uint8_t)177U, (uint8_t)161U, (uint8_t)76U, (uint8_t)187U, (uint8_t)235U,
    (uint8_t)174U, (uint8_t)196U, (uint8_t)28U, (uint8_t)75U, (uint8_t)202U, (uint8_t)141U,
    (uint8_t)161U, (uint8_t)143U, (uint8_t)73U, (uint8_t)42U, (uint8_t)6U, (uint8_t)45U,
    (uint8_t)111U, (uint8_t)111U
  };

static uint8_t
siggen_vectors256_low75[32U] =
  {
    (uint8_t)152U, (uint8_t)134U, (uint8_t)174U, (uint8_t)70U, (uint8_t)193U, (uint8_t)65U,
    (uint8_t)92U, (uint8_t)59U, (uint8_t)201U, (uint8_t)89U, (uint8_t)232U, (uint8_t)43U,
    (uint8_t)118U, (uint8_t)10U, (uint8_t)215U, (uint8_t)96U, (uint8_t)170U, (uint8_t)182U,
    (uint8_t)104U, (uint8_t)133U, (uint8_t)168U, (uint8_t)78U, (uint8_t)98U, (uint8_t)10U,
    (uint8_t)163U, (uint8_t)57U, (uint8_t)253U, (uint8_t)241U, (uint8_t)2U, (uint8_t)70U,
    (uint8_t)92U, (uint8_t)66U
  };

static uint8_t
siggen_vectors256_low76[32U] =
  {
    (uint8_t)43U, (uint8_t)243U, (uint8_t)168U, (uint8_t)11U, (uint8_t)192U, (uint8_t)79U,
    (uint8_t)170U, (uint8_t)53U, (uint8_t)235U, (uint8_t)236U, (uint8_t)192U, (uint8_t)244U,
    (uint8_t)134U, (uint8_t)74U, (uint8_t)192U, (uint8_t)45U, (uint8_t)52U, (uint8_t)159U,
    (uint8_t)111U, (uint8_t)18U, (uint8_t)110U, (uint8_t)15U, (uint8_t)152U, (uint8_t)133U,
    (uint8_t)1U, (uint8_t)184U, (uint8_t)211U, (uint8_t)7U, (uint8_t)84U, (uint8_t)9U,
    (uint8_t)162U, (uint8_t)108U
  };

static uint8_t
siggen_vectors256_low77[128U] =
  {
    (uint8_t)59U, (uint8_t)110U, (uint8_t)226U, (uint8_t)66U, (uint8_t)89U, (uint8_t)64U,
    (uint8_t)179U, (uint8_t)210U, (uint8_t)64U, (uint8_t)211U, (uint8_t)91U, (uint8_t)151U,
    (uint8_t)182U, (uint8_t)220U, (uint8_t)214U, (uint8_t)30U, (uint8_t)211U, (uint8_t)66U,
    (uint8_t)61U, (uint8_t)142U, (uint8_t)113U, (uint8_t)160U, (uint8_t)173U, (uint8_t)163U,
    (uint8_t)93U, (uint8_t)71U, (uint8_t)179U, (uint8_t)34U, (uint8_t)209U, (uint8_t)123U,
    (uint8_t)53U, (uint8_t)234U, (uint8_t)4U, (uint8_t)114U, (uint8_t)243U, (uint8_t)94U,
    (uint8_t)221U, (uint8_t)29U, (uint8_t)37U, (uint8_t)47U, (uint8_t)135U, (uint8_t)184U,
    (uint8_t)182U, (uint8_t)94U, (uint8_t)244U, (uint8_t)183U, (uint8_t)22U, (uint8_t)102U,
    (uint8_t)159U, (uint8_t)201U, (uint8_t)172U, (uint8_t)40U, (uint8_t)176U, (uint8_t)13U,
    (uint8_t)52U, (uint8_t)169U, (uint8_t)214U, (uint8_t)106U, (uint8_t)209U, (uint8_t)24U,
    (uint8_t)201U, (uint8_t)217U, (uint8_t)78U, (uint8_t)127U, (uint8_t)70U, (uint8_t)208U,
    (uint8_t)180U, (uint8_t)246U, (uint8_t)194U, (uint8_t)178U, (uint8_t)211U, (uint8_t)57U,
    (uint8_t)253U, (uint8_t)107U, (uint8_t)205U, (uint8_t)53U, (uint8_t)18U, (uint8_t)65U,
    (uint8_t)163U, (uint8_t)135U, (uint8_t)204U, (uint8_t)130U, (uint8_t)96U, (uint8_t)144U,
    (uint8_t)87U, (uint8_t)4U, (uint8_t)140U, (uint8_t)18U, (uint8_t)196U, (uint8_t)236U,
    (uint8_t)61U, (uint8_t)133U, (uint8_t)198U, (uint8_t)97U, (uint8_t)151U, (uint8_t)92U,
    (uint8_t)69U, (uint8_t)179U, (uint8_t)0U, (uint8_t)203U, (uint8_t)150U, (uint8_t)147U,
    (uint8_t)13U, (uint8_t)137U, (uint8_t)55U, (uint8_t)10U, (uint8_t)50U, (uint8_t)124U,
    (uint8_t)152U, (uint8_t)182U, (uint8_t)125U, (uint8_t)239U, (uint8_t)170U, (uint8_t)137U,
    (uint8_t)73U, (uint8_t)122U, (uint8_t)168U, (uint8_t)239U, (uint8_t)153U, (uint8_t)76U,
    (uint8_t)119U, (uint8_t)241U, (uint8_t)19U, (uint8_t)15U, (uint8_t)117U, (uint8_t)47U,
    (uint8_t)148U, (uint8_t)164U
  };

static uint8_t
siggen_vectors256_low78[32U] =
  {
    (uint8_t)212U, (uint8_t)35U, (uint8_t)75U, (uint8_t)235U, (uint8_t)251U, (uint8_t)200U,
    (uint8_t)33U, (uint8_t)5U, (uint8_t)3U, (uint8_t)65U, (uint8_t)163U, (uint8_t)126U,
    (uint8_t)18U, (uint8_t)64U, (uint8_t)239U, (uint8_t)229U, (uint8_t)227U, (uint8_t)55U,
    (uint8_t)99U, (uint8_t)203U, (uint8_t)187U, (uint8_t)46U, (uint8_t)247U, (uint8_t)106U,
    (uint8_t)28U, (uint8_t)121U, (uint8_t)226U, (uint8_t)71U, (uint8_t)36U, (uint8_t)229U,
    (uint8_t)165U, (uint8_t)231U
  };

static uint8_t
siggen_vectors256_low79[32U] =
  {
    (uint8_t)143U, (uint8_t)178U, (uint8_t)135U, (uint8_t)240U, (uint8_t)32U, (uint8_t)42U,
    (uint8_t)213U, (uint8_t)122U, (uint8_t)232U, (uint8_t)65U, (uint8_t)174U, (uint8_t)163U,
    (uint8_t)95U, (uint8_t)41U, (uint8_t)178U, (uint8_t)225U, (uint8_t)213U, (uint8_t)62U,
    (uint8_t)25U, (uint8_t)109U, (uint8_t)13U, (uint8_t)221U, (uint8_t)154U, (uint8_t)236U,
    (uint8_t)36U, (uint8_t)129U, (uint8_t)61U, (uint8_t)100U, (uint8_t)192U, (uint8_t)146U,
    (uint8_t)47U, (uint8_t)183U
  };

static uint8_t
siggen_vectors256_low80[32U] =
  {
    (uint8_t)31U, (uint8_t)109U, (uint8_t)175U, (uint8_t)241U, (uint8_t)170U, (uint8_t)45U,
    (uint8_t)210U, (uint8_t)214U, (uint8_t)211U, (uint8_t)116U, (uint8_t)22U, (uint8_t)35U,
    (uint8_t)238U, (uint8_t)203U, (uint8_t)94U, (uint8_t)123U, (uint8_t)97U, (uint8_t)41U,
    (uint8_t)151U, (uint8_t)161U, (uint8_t)3U, (uint8_t)154U, (uint8_t)171U, (uint8_t)46U,
    (uint8_t)92U, (uint8_t)242U, (uint8_t)222U, (uint8_t)150U, (uint8_t)156U, (uint8_t)254U,
    (uint8_t)165U, (uint8_t)115U
  };

static uint8_t
siggen_vectors256_low81[32U] =
  {
    (uint8_t)217U, (uint8_t)38U, (uint8_t)254U, (uint8_t)16U, (uint8_t)241U, (uint8_t)191U,
    (uint8_t)217U, (uint8_t)133U, (uint8_t)86U, (uint8_t)16U, (uint8_t)244U, (uint8_t)245U,
    (uint8_t)163U, (uint8_t)214U, (uint8_t)102U, (uint8_t)177U, (uint8_t)161U, (uint8_t)73U,
    (uint8_t)52U, (uint8_t)64U, (uint8_t)87U, (uint8_t)227U, (uint8_t)85U, (uint8_t)55U,
    (uint8_t)55U, (uint8_t)51U, (uint8_t)114U, (uint8_t)234U, (uint8_t)216U, (uint8_t)177U,
    (uint8_t)167U, (uint8_t)120U
  };

static uint8_t
siggen_vectors256_low82[32U] =
  {
    (uint8_t)73U, (uint8_t)14U, (uint8_t)253U, (uint8_t)16U, (uint8_t)107U, (uint8_t)225U,
    (uint8_t)31U, (uint8_t)195U, (uint8_t)101U, (uint8_t)199U, (uint8_t)70U, (uint8_t)126U,
    (uint8_t)184U, (uint8_t)155U, (uint8_t)141U, (uint8_t)57U, (uint8_t)225U, (uint8_t)93U,
    (uint8_t)101U, (uint8_t)23U, (uint8_t)83U, (uint8_t)86U, (uint8_t)119U, (uint8_t)93U,
    (uint8_t)234U, (uint8_t)178U, (uint8_t)17U, (uint8_t)22U, (uint8_t)60U, (uint8_t)37U,
    (uint8_t)4U, (uint8_t)203U
  };

static uint8_t
siggen_vectors256_low83[32U] =
  {
    (uint8_t)100U, (uint8_t)67U, (uint8_t)0U, (uint8_t)252U, (uint8_t)13U, (uint8_t)164U,
    (uint8_t)212U, (uint8_t)15U, (uint8_t)184U, (uint8_t)198U, (uint8_t)234U, (uint8_t)213U,
    (uint8_t)16U, (uint8_t)209U, (uint8_t)79U, (uint8_t)11U, (uint8_t)212U, (uint8_t)225U,
    (uint8_t)50U, (uint8_t)26U, (uint8_t)70U, (uint8_t)158U, (uint8_t)156U, (uint8_t)10U,
    (uint8_t)88U, (uint8_t)20U, (uint8_t)100U, (uint8_t)199U, (uint8_t)24U, (uint8_t)107U,
    (uint8_t)122U, (uint8_t)167U
  };

static uint8_t
siggen_vectors256_low84[128U] =
  {
    (uint8_t)197U, (uint8_t)32U, (uint8_t)75U, (uint8_t)129U, (uint8_t)236U, (uint8_t)10U,
    (uint8_t)77U, (uint8_t)245U, (uint8_t)183U, (uint8_t)233U, (uint8_t)253U, (uint8_t)163U,
    (uint8_t)220U, (uint8_t)36U, (uint8_t)95U, (uint8_t)152U, (uint8_t)8U, (uint8_t)42U,
    (uint8_t)231U, (uint8_t)244U, (uint8_t)239U, (uint8_t)232U, (uint8_t)25U, (uint8_t)152U,
    (uint8_t)220U, (uint8_t)170U, (uint8_t)40U, (uint8_t)107U, (uint8_t)212U, (uint8_t)80U,
    (uint8_t)124U, (uint8_t)168U, (uint8_t)64U, (uint8_t)165U, (uint8_t)61U, (uint8_t)33U,
    (uint8_t)176U, (uint8_t)30U, (uint8_t)144U, (uint8_t)79U, (uint8_t)85U, (uint8_t)227U,
    (uint8_t)143U, (uint8_t)120U, (uint8_t)195U, (uint8_t)117U, (uint8_t)125U, (uint8_t)90U,
    (uint8_t)90U, (uint8_t)74U, (uint8_t)68U, (uint8_t)177U, (uint8_t)213U, (uint8_t)212U,
    (uint8_t)228U, (uint8_t)128U, (uint8_t)190U, (uint8_t)58U, (uint8_t)251U, (uint8_t)91U,
    (uint8_t)57U, (uint8_t)74U, (uint8_t)93U, (uint8_t)40U, (uint8_t)64U, (uint8_t)175U,
    (uint8_t)66U, (uint8_t)177U, (uint8_t)180U, (uint8_t)8U, (uint8_t)61U, (uint8_t)64U,
    (uint8_t)175U, (uint8_t)191U, (uint8_t)226U, (uint8_t)45U, (uint8_t)112U, (uint8_t)47U,
    (uint8_t)55U, (uint8_t)13U, (uint8_t)50U, (uint8_t)219U, (uint8_t)253U, (uint8_t)57U,
    (uint8_t)46U, (uint8_t)18U, (uint8_t)142U, (uint8_t)164U, (uint8_t)114U, (uint8_t)77U,
    (uint8_t)102U, (uint8_t)163U, (uint8_t)112U, (uint8_t)29U, (uint8_t)164U, (uint8_t)26U,
    (uint8_t)226U, (uint8_t)240U, (uint8_t)59U, (uint8_t)180U, (uint8_t)217U, (uint8_t)27U,
    (uint8_t)185U, (uint8_t)70U, (uint8_t)199U, (uint8_t)150U, (uint8_t)148U, (uint8_t)4U,
    (uint8_t)203U, (uint8_t)84U, (uint8_t)79U, (uint8_t)113U, (uint8_t)235U, (uint8_t)122U,
    (uint8_t)73U, (uint8_t)235U, (uint8_t)76U, (uint8_t)78U, (uint8_t)197U, (uint8_t)87U,
    (uint8_t)153U, (uint8_t)189U, (uint8_t)161U, (uint8_t)235U, (uint8_t)84U, (uint8_t)81U,
    (uint8_t)67U, (uint8_t)167U
  };

static uint8_t
siggen_vectors256_low85[32U] =
  {
    (uint8_t)181U, (uint8_t)143U, (uint8_t)82U, (uint8_t)17U, (uint8_t)223U, (uint8_t)244U,
    (uint8_t)64U, (uint8_t)98U, (uint8_t)107U, (uint8_t)181U, (uint8_t)109U, (uint8_t)10U,
    (uint8_t)212U, (uint8_t)131U, (uint8_t)25U, (uint8_t)61U, (uint8_t)96U, (uint8_t)108U,
    (uint8_t)242U, (uint8_t)31U, (uint8_t)54U, (uint8_t)217U, (uint8_t)131U, (uint8_t)5U,
    (uint8_t)67U, (uint8_t)50U, (uint8_t)114U, (uint8_t)146U, (uint8_t)244U, (uint8_t)210U,
    (uint8_t)93U, (uint8_t)140U
  };

static uint8_t
siggen_vectors256_low86[32U] =
  {
    (uint8_t)104U, (uint8_t)34U, (uint8_t)155U, (uint8_t)72U, (uint8_t)194U, (uint8_t)254U,
    (uint8_t)25U, (uint8_t)211U, (uint8_t)219U, (uint8_t)3U, (uint8_t)78U, (uint8_t)76U,
    (uint8_t)21U, (uint8_t)7U, (uint8_t)126U, (uint8_t)183U, (uint8_t)71U, (uint8_t)26U,
    (uint8_t)102U, (uint8_t)3U, (uint8_t)31U, (uint8_t)40U, (uint8_t)169U, (uint8_t)128U,
    (uint8_t)130U, (uint8_t)24U, (uint8_t)115U, (uint8_t)145U, (uint8_t)82U, (uint8_t)152U,
    (uint8_t)186U, (uint8_t)118U
  };

static uint8_t
siggen_vectors256_low87[32U] =
  {
    (uint8_t)48U, (uint8_t)62U, (uint8_t)142U, (uint8_t)227U, (uint8_t)116U, (uint8_t)42U,
    (uint8_t)137U, (uint8_t)63U, (uint8_t)120U, (uint8_t)184U, (uint8_t)16U, (uint8_t)153U,
    (uint8_t)29U, (uint8_t)166U, (uint8_t)151U, (uint8_t)8U, (uint8_t)61U, (uint8_t)216U,
    (uint8_t)241U, (uint8_t)17U, (uint8_t)40U, (uint8_t)196U, (uint8_t)118U, (uint8_t)81U,
    (uint8_t)194U, (uint8_t)122U, (uint8_t)86U, (uint8_t)116U, (uint8_t)10U, (uint8_t)128U,
    (uint8_t)194U, (uint8_t)76U
  };

static uint8_t
siggen_vectors256_low88[32U] =
  {
    (uint8_t)225U, (uint8_t)88U, (uint8_t)191U, (uint8_t)74U, (uint8_t)45U, (uint8_t)25U,
    (uint8_t)169U, (uint8_t)145U, (uint8_t)73U, (uint8_t)217U, (uint8_t)205U, (uint8_t)184U,
    (uint8_t)121U, (uint8_t)41U, (uint8_t)76U, (uint8_t)203U, (uint8_t)122U, (uint8_t)174U,
    (uint8_t)174U, (uint8_t)3U, (uint8_t)215U, (uint8_t)93U, (uint8_t)221U, (uint8_t)97U,
    (uint8_t)110U, (uint8_t)248U, (uint8_t)174U, (uint8_t)81U, (uint8_t)166U, (uint8_t)220U,
    (uint8_t)16U, (uint8_t)113U
  };

static uint8_t
siggen_vectors256_low89[32U] =
  {
    (uint8_t)230U, (uint8_t)122U, (uint8_t)151U, (uint8_t)23U, (uint8_t)204U, (uint8_t)249U,
    (uint8_t)104U, (uint8_t)65U, (uint8_t)72U, (uint8_t)157U, (uint8_t)101U, (uint8_t)65U,
    (uint8_t)244U, (uint8_t)246U, (uint8_t)173U, (uint8_t)177U, (uint8_t)45U, (uint8_t)23U,
    (uint8_t)181U, (uint8_t)154U, (uint8_t)107U, (uint8_t)239U, (uint8_t)132U, (uint8_t)123U,
    (uint8_t)97U, (uint8_t)131U, (uint8_t)184U, (uint8_t)252U, (uint8_t)241U, (uint8_t)106U,
    (uint8_t)50U, (uint8_t)235U
  };

static uint8_t
siggen_vectors256_low90[32U] =
  {
    (uint8_t)154U, (uint8_t)230U, (uint8_t)186U, (uint8_t)109U, (uint8_t)99U, (uint8_t)119U,
    (uint8_t)6U, (uint8_t)132U, (uint8_t)154U, (uint8_t)106U, (uint8_t)159U, (uint8_t)195U,
    (uint8_t)136U, (uint8_t)207U, (uint8_t)2U, (uint8_t)50U, (uint8_t)216U, (uint8_t)92U,
    (uint8_t)38U, (uint8_t)234U, (uint8_t)13U, (uint8_t)31U, (uint8_t)231U, (uint8_t)67U,
    (uint8_t)122U, (uint8_t)219U, (uint8_t)72U, (uint8_t)222U, (uint8_t)88U, (uint8_t)54U,
    (uint8_t)67U, (uint8_t)51U
  };

static uint8_t
siggen_vectors256_low91[128U] =
  {
    (uint8_t)114U, (uint8_t)232U, (uint8_t)31U, (uint8_t)226U, (uint8_t)33U, (uint8_t)251U,
    (uint8_t)64U, (uint8_t)33U, (uint8_t)72U, (uint8_t)216U, (uint8_t)183U, (uint8_t)171U,
    (uint8_t)3U, (uint8_t)84U, (uint8_t)159U, (uint8_t)17U, (uint8_t)128U, (uint8_t)188U,
    (uint8_t)192U, (uint8_t)61U, (uint8_t)65U, (uint8_t)202U, (uint8_t)89U, (uint8_t)215U,
    (uint8_t)101U, (uint8_t)56U, (uint8_t)1U, (uint8_t)240U, (uint8_t)186U, (uint8_t)133U,
    (uint8_t)58U, (uint8_t)221U, (uint8_t)31U, (uint8_t)109U, (uint8_t)41U, (uint8_t)237U,
    (uint8_t)215U, (uint8_t)249U, (uint8_t)171U, (uint8_t)198U, (uint8_t)33U, (uint8_t)178U,
    (uint8_t)213U, (uint8_t)72U, (uint8_t)248U, (uint8_t)219U, (uint8_t)248U, (uint8_t)151U,
    (uint8_t)155U, (uint8_t)209U, (uint8_t)102U, (uint8_t)8U, (uint8_t)210U, (uint8_t)216U,
    (uint8_t)252U, (uint8_t)50U, (uint8_t)96U, (uint8_t)180U, (uint8_t)235U, (uint8_t)192U,
    (uint8_t)221U, (uint8_t)66U, (uint8_t)72U, (uint8_t)36U, (uint8_t)129U, (uint8_t)213U,
    (uint8_t)72U, (uint8_t)199U, (uint8_t)7U, (uint8_t)87U, (uint8_t)17U, (uint8_t)181U,
    (uint8_t)117U, (uint8_t)150U, (uint8_t)73U, (uint8_t)196U, (uint8_t)31U, (uint8_t)67U,
    (uint8_t)159U, (uint8_t)173U, (uint8_t)105U, (uint8_t)149U, (uint8_t)73U, (uint8_t)86U,
    (uint8_t)201U, (uint8_t)50U, (uint8_t)104U, (uint8_t)65U, (uint8_t)234U, (uint8_t)100U,
    (uint8_t)146U, (uint8_t)149U, (uint8_t)104U, (uint8_t)41U, (uint8_t)249U, (uint8_t)224U,
    (uint8_t)220U, (uint8_t)120U, (uint8_t)159U, (uint8_t)115U, (uint8_t)99U, (uint8_t)59U,
    (uint8_t)64U, (uint8_t)246U, (uint8_t)172U, (uint8_t)119U, (uint8_t)188U, (uint8_t)174U,
    (uint8_t)109U, (uint8_t)252U, (uint8_t)121U, (uint8_t)48U, (uint8_t)207U, (uint8_t)232U,
    (uint8_t)158U, (uint8_t)82U, (uint8_t)109U, (uint8_t)22U, (uint8_t)132U, (uint8_t)54U,
    (uint8_t)92U, (uint8_t)91U, (uint8_t)11U, (uint8_t)226U, (uint8_t)67U, (uint8_t)127U,
    (uint8_t)219U, (uint8_t)1U
  };

static uint8_t
siggen_vectors256_low92[32U] =
  {
    (uint8_t)84U, (uint8_t)192U, (uint8_t)102U, (uint8_t)113U, (uint8_t)28U, (uint8_t)219U,
    (uint8_t)6U, (uint8_t)30U, (uint8_t)218U, (uint8_t)7U, (uint8_t)229U, (uint8_t)39U,
    (uint8_t)95U, (uint8_t)126U, (uint8_t)149U, (uint8_t)169U, (uint8_t)150U, (uint8_t)44U,
    (uint8_t)103U, (uint8_t)100U, (uint8_t)184U, (uint8_t)79U, (uint8_t)111U, (uint8_t)31U,
    (uint8_t)58U, (uint8_t)181U, (uint8_t)165U, (uint8_t)136U, (uint8_t)224U, (uint8_t)162U,
    (uint8_t)175U, (uint8_t)177U
  };

static uint8_t
siggen_vectors256_low93[32U] =
  {
    (uint8_t)10U, (uint8_t)125U, (uint8_t)187U, (uint8_t)139U, (uint8_t)245U, (uint8_t)12U,
    (uint8_t)182U, (uint8_t)5U, (uint8_t)235U, (uint8_t)34U, (uint8_t)104U, (uint8_t)176U,
    (uint8_t)129U, (uint8_t)242U, (uint8_t)109U, (uint8_t)107U, (uint8_t)8U, (uint8_t)224U,
    (uint8_t)18U, (uint8_t)249U, (uint8_t)82U, (uint8_t)196U, (uint8_t)183U, (uint8_t)10U,
    (uint8_t)90U, (uint8_t)30U, (uint8_t)110U, (uint8_t)125U, (uint8_t)70U, (uint8_t)175U,
    (uint8_t)152U, (uint8_t)187U
  };

static uint8_t
siggen_vectors256_low94[32U] =
  {
    (uint8_t)242U, (uint8_t)109U, (uint8_t)215U, (uint8_t)215U, (uint8_t)153U, (uint8_t)147U,
    (uint8_t)0U, (uint8_t)98U, (uint8_t)72U, (uint8_t)8U, (uint8_t)73U, (uint8_t)150U, (uint8_t)44U,
    (uint8_t)207U, (uint8_t)80U, (uint8_t)4U, (uint8_t)237U, (uint8_t)207U, (uint8_t)211U,
    (uint8_t)7U, (uint8_t)192U, (uint8_t)68U, (uint8_t)244U, (uint8_t)232U, (uint8_t)246U,
    (uint8_t)103U, (uint8_t)201U, (uint8_t)186U, (uint8_t)168U, (uint8_t)52U, (uint8_t)238U,
    (uint8_t)174U
  };

static uint8_t
siggen_vectors256_low95[32U] =
  {
    (uint8_t)100U, (uint8_t)111U, (uint8_t)233U, (uint8_t)51U, (uint8_t)233U, (uint8_t)108U,
    (uint8_t)59U, (uint8_t)143U, (uint8_t)159U, (uint8_t)80U, (uint8_t)116U, (uint8_t)152U,
    (uint8_t)233U, (uint8_t)7U, (uint8_t)253U, (uint8_t)210U, (uint8_t)1U, (uint8_t)240U,
    (uint8_t)132U, (uint8_t)120U, (uint8_t)208U, (uint8_t)32U, (uint8_t)44U, (uint8_t)117U,
    (uint8_t)42U, (uint8_t)124U, (uint8_t)44U, (uint8_t)254U, (uint8_t)191U, (uint8_t)77U,
    (uint8_t)6U, (uint8_t)26U
  };

static uint8_t
siggen_vectors256_low96[32U] =
  {
    (uint8_t)181U, (uint8_t)60U, (uint8_t)228U, (uint8_t)218U, (uint8_t)26U, (uint8_t)167U,
    (uint8_t)192U, (uint8_t)220U, (uint8_t)119U, (uint8_t)161U, (uint8_t)137U, (uint8_t)106U,
    (uint8_t)183U, (uint8_t)22U, (uint8_t)185U, (uint8_t)33U, (uint8_t)73U, (uint8_t)154U,
    (uint8_t)237U, (uint8_t)120U, (uint8_t)223U, (uint8_t)114U, (uint8_t)91U, (uint8_t)21U,
    (uint8_t)4U, (uint8_t)171U, (uint8_t)161U, (uint8_t)89U, (uint8_t)123U, (uint8_t)160U,
    (uint8_t)198U, (uint8_t)75U
  };

static uint8_t
siggen_vectors256_low97[32U] =
  {
    (uint8_t)215U, (uint8_t)194U, (uint8_t)70U, (uint8_t)220U, (uint8_t)122U, (uint8_t)208U,
    (uint8_t)230U, (uint8_t)119U, (uint8_t)0U, (uint8_t)195U, (uint8_t)115U, (uint8_t)237U,
    (uint8_t)207U, (uint8_t)221U, (uint8_t)28U, (uint8_t)10U, (uint8_t)4U, (uint8_t)149U,
    (uint8_t)252U, (uint8_t)149U, (uint8_t)69U, (uint8_t)73U, (uint8_t)173U, (uint8_t)87U,
    (uint8_t)157U, (uint8_t)246U, (uint8_t)237U, (uint8_t)20U, (uint8_t)56U, (uint8_t)132U,
    (uint8_t)8U, (uint8_t)81U
  };

static uint8_t
siggen_vectors256_low98[128U] =
  {
    (uint8_t)33U, (uint8_t)24U, (uint8_t)140U, (uint8_t)62U, (uint8_t)221U, (uint8_t)93U,
    (uint8_t)224U, (uint8_t)136U, (uint8_t)218U, (uint8_t)204U, (uint8_t)16U, (uint8_t)118U,
    (uint8_t)185U, (uint8_t)225U, (uint8_t)188U, (uint8_t)236U, (uint8_t)215U, (uint8_t)157U,
    (uint8_t)225U, (uint8_t)0U, (uint8_t)60U, (uint8_t)36U, (uint8_t)20U, (uint8_t)195U,
    (uint8_t)134U, (uint8_t)97U, (uint8_t)115U, (uint8_t)5U, (uint8_t)77U, (uint8_t)200U,
    (uint8_t)45U, (uint8_t)222U, (uint8_t)133U, (uint8_t)22U, (uint8_t)155U, (uint8_t)170U,
    (uint8_t)119U, (uint8_t)153U, (uint8_t)58U, (uint8_t)219U, (uint8_t)32U, (uint8_t)194U,
    (uint8_t)105U, (uint8_t)246U, (uint8_t)10U, (uint8_t)82U, (uint8_t)38U, (uint8_t)17U,
    (uint8_t)24U, (uint8_t)40U, (uint8_t)87U, (uint8_t)139U, (uint8_t)204U, (uint8_t)124U,
    (uint8_t)41U, (uint8_t)230U, (uint8_t)232U, (uint8_t)210U, (uint8_t)218U, (uint8_t)232U,
    (uint8_t)24U, (uint8_t)6U, (uint8_t)21U, (uint8_t)44U, (uint8_t)139U, (uint8_t)160U,
    (uint8_t)198U, (uint8_t)173U, (uint8_t)161U, (uint8_t)152U, (uint8_t)106U, (uint8_t)25U,
    (uint8_t)131U, (uint8_t)235U, (uint8_t)238U, (uint8_t)193U, (uint8_t)71U, (uint8_t)58U,
    (uint8_t)115U, (uint8_t)160U, (uint8_t)71U, (uint8_t)149U, (uint8_t)182U, (uint8_t)49U,
    (uint8_t)157U, (uint8_t)72U, (uint8_t)102U, (uint8_t)45U, (uint8_t)64U, (uint8_t)136U,
    (uint8_t)28U, (uint8_t)23U, (uint8_t)35U, (uint8_t)167U, (uint8_t)6U, (uint8_t)245U,
    (uint8_t)22U, (uint8_t)254U, (uint8_t)117U, (uint8_t)48U, (uint8_t)15U, (uint8_t)146U,
    (uint8_t)64U, (uint8_t)138U, (uint8_t)161U, (uint8_t)220U, (uint8_t)106U, (uint8_t)228U,
    (uint8_t)40U, (uint8_t)141U, (uint8_t)32U, (uint8_t)70U, (uint8_t)242U, (uint8_t)60U,
    (uint8_t)26U, (uint8_t)162U, (uint8_t)229U, (uint8_t)75U, (uint8_t)127U, (uint8_t)182U,
    (uint8_t)68U, (uint8_t)138U, (uint8_t)13U, (uint8_t)169U, (uint8_t)34U, (uint8_t)189U,
    (uint8_t)127U, (uint8_t)52U
  };

static uint8_t
siggen_vectors256_low99[32U] =
  {
    (uint8_t)52U, (uint8_t)250U, (uint8_t)70U, (uint8_t)130U, (uint8_t)191U, (uint8_t)108U,
    (uint8_t)181U, (uint8_t)177U, (uint8_t)103U, (uint8_t)131U, (uint8_t)173U, (uint8_t)205U,
    (uint8_t)24U, (uint8_t)240U, (uint8_t)230U, (uint8_t)135U, (uint8_t)155U, (uint8_t)146U,
    (uint8_t)24U, (uint8_t)95U, (uint8_t)118U, (uint8_t)215U, (uint8_t)201U, (uint8_t)32U,
    (uint8_t)64U, (uint8_t)159U, (uint8_t)144U, (uint8_t)79U, (uint8_t)82U, (uint8_t)45U,
    (uint8_t)180U, (uint8_t)177U
  };

static uint8_t
siggen_vectors256_low100[32U] =
  {
    (uint8_t)16U, (uint8_t)93U, (uint8_t)34U, (uint8_t)217U, (uint8_t)198U, (uint8_t)38U,
    (uint8_t)82U, (uint8_t)15U, (uint8_t)172U, (uint8_t)161U, (uint8_t)62U, (uint8_t)124U,
    (uint8_t)237U, (uint8_t)56U, (uint8_t)45U, (uint8_t)203U, (uint8_t)233U, (uint8_t)52U,
    (uint8_t)152U, (uint8_t)49U, (uint8_t)95U, (uint8_t)0U, (uint8_t)204U, (uint8_t)10U,
    (uint8_t)195U, (uint8_t)156U, (uint8_t)72U, (uint8_t)33U, (uint8_t)208U, (uint8_t)215U,
    (uint8_t)55U, (uint8_t)55U
  };

static uint8_t
siggen_vectors256_low101[32U] =
  {
    (uint8_t)108U, (uint8_t)71U, (uint8_t)243U, (uint8_t)203U, (uint8_t)191U, (uint8_t)169U,
    (uint8_t)125U, (uint8_t)252U, (uint8_t)235U, (uint8_t)225U, (uint8_t)98U, (uint8_t)112U,
    (uint8_t)184U, (uint8_t)199U, (uint8_t)213U, (uint8_t)211U, (uint8_t)165U, (uint8_t)144U,
    (uint8_t)11U, (uint8_t)136U, (uint8_t)140U, (uint8_t)66U, (uint8_t)82U, (uint8_t)13U,
    (uint8_t)117U, (uint8_t)30U, (uint8_t)143U, (uint8_t)175U, (uint8_t)59U, (uint8_t)64U,
    (uint8_t)30U, (uint8_t)244U
  };

static uint8_t
siggen_vectors256_low102[32U] =
  {
    (uint8_t)166U, (uint8_t)244U, (uint8_t)99U, (uint8_t)238U, (uint8_t)114U, (uint8_t)201U,
    (uint8_t)73U, (uint8_t)43U, (uint8_t)199U, (uint8_t)146U, (uint8_t)254U, (uint8_t)152U,
    (uint8_t)22U, (uint8_t)49U, (uint8_t)18U, (uint8_t)131U, (uint8_t)122U, (uint8_t)235U,
    (uint8_t)208U, (uint8_t)123U, (uint8_t)171U, (uint8_t)122U, (uint8_t)132U, (uint8_t)170U,
    (uint8_t)237U, (uint8_t)5U, (uint8_t)190U, (uint8_t)100U, (uint8_t)219U, (uint8_t)48U,
    (uint8_t)134U, (uint8_t)244U
  };

static uint8_t
siggen_vectors256_low103[32U] =
  {
    (uint8_t)84U, (uint8_t)44U, (uint8_t)64U, (uint8_t)161U, (uint8_t)129U, (uint8_t)64U,
    (uint8_t)166U, (uint8_t)38U, (uint8_t)109U, (uint8_t)111U, (uint8_t)2U, (uint8_t)134U,
    (uint8_t)226U, (uint8_t)78U, (uint8_t)154U, (uint8_t)123U, (uint8_t)173U, (uint8_t)118U,
    (uint8_t)80U, (uint8_t)231U, (uint8_t)46U, (uint8_t)240U, (uint8_t)226U, (uint8_t)19U,
    (uint8_t)30U, (uint8_t)98U, (uint8_t)156U, (uint8_t)7U, (uint8_t)109U, (uint8_t)150U,
    (uint8_t)38U, (uint8_t)99U
  };

static uint8_t
siggen_vectors256_low104[32U] =
  {
    (uint8_t)79U, (uint8_t)127U, (uint8_t)101U, (uint8_t)48U, (uint8_t)94U, (uint8_t)36U,
    (uint8_t)166U, (uint8_t)187U, (uint8_t)181U, (uint8_t)207U, (uint8_t)247U, (uint8_t)20U,
    (uint8_t)186U, (uint8_t)143U, (uint8_t)90U, (uint8_t)44U, (uint8_t)238U, (uint8_t)91U,
    (uint8_t)220U, (uint8_t)137U, (uint8_t)186U, (uint8_t)141U, (uint8_t)117U, (uint8_t)220U,
    (uint8_t)191U, (uint8_t)33U, (uint8_t)150U, (uint8_t)108U, (uint8_t)227U, (uint8_t)142U,
    (uint8_t)182U, (uint8_t)111U
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
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low0 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low1 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low2 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low3 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low4 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low5 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low6 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low7 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low8 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low9 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low10 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low11 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low12 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low13 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low14 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low15 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low16 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low17 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low18 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low19 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low20 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low21 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low22 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low23 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low24 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low25 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low26 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low27 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low28 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low29 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low30 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low31 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low32 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low33 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low34 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low35 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low36 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low37 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low38 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low39 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low40 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low41 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low42 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low43 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low44 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low45 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low46 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low47 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low48 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low49 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low50 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low51 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low52 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low53 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low54 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low55 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low56 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low57 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low58 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low59 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low60 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low61 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low62 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low63 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low64 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low65 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low66 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low67 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low68 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low69 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low70 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low71 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low72 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low73 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low74 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low75 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low76 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low77 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low78 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low79 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low80 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low81 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low82 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low83 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low84 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low85 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low86 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low87 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low88 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low89 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low90 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low91 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low92 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low93 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low94 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low95 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low96 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low97 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors256_low98 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors256_low99 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors256_low100 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors256_low101 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors256_low102 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors256_low103 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors256_low104 }
    }
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
siggen_vectors256_low = { .len = (uint32_t)15U, .b = siggen_vectors256_low105 };

static uint8_t
siggen_vectors384_low0[128U] =
  {
    (uint8_t)224U, (uint8_t)184U, (uint8_t)89U, (uint8_t)107U, (uint8_t)55U, (uint8_t)95U,
    (uint8_t)51U, (uint8_t)6U, (uint8_t)187U, (uint8_t)198U, (uint8_t)231U, (uint8_t)122U,
    (uint8_t)11U, (uint8_t)66U, (uint8_t)247U, (uint8_t)70U, (uint8_t)157U, (uint8_t)126U,
    (uint8_t)131U, (uint8_t)99U, (uint8_t)89U, (uint8_t)144U, (uint8_t)231U, (uint8_t)74U,
    (uint8_t)166U, (uint8_t)215U, (uint8_t)19U, (uint8_t)89U, (uint8_t)74U, (uint8_t)58U,
    (uint8_t)36U, (uint8_t)73U, (uint8_t)143U, (uint8_t)239U, (uint8_t)245U, (uint8_t)0U,
    (uint8_t)103U, (uint8_t)144U, (uint8_t)116U, (uint8_t)45U, (uint8_t)156U, (uint8_t)46U,
    (uint8_t)155U, (uint8_t)71U, (uint8_t)215U, (uint8_t)20U, (uint8_t)190U, (uint8_t)233U,
    (uint8_t)50U, (uint8_t)67U, (uint8_t)93U, (uint8_t)183U, (uint8_t)71U, (uint8_t)198U,
    (uint8_t)231U, (uint8_t)51U, (uint8_t)227U, (uint8_t)216U, (uint8_t)222U, (uint8_t)65U,
    (uint8_t)242U, (uint8_t)249U, (uint8_t)19U, (uint8_t)17U, (uint8_t)242U, (uint8_t)233U,
    (uint8_t)253U, (uint8_t)142U, (uint8_t)2U, (uint8_t)86U, (uint8_t)81U, (uint8_t)99U,
    (uint8_t)31U, (uint8_t)253U, (uint8_t)132U, (uint8_t)246U, (uint8_t)103U, (uint8_t)50U,
    (uint8_t)211U, (uint8_t)71U, (uint8_t)63U, (uint8_t)189U, (uint8_t)22U, (uint8_t)39U,
    (uint8_t)230U, (uint8_t)61U, (uint8_t)199U, (uint8_t)25U, (uint8_t)64U, (uint8_t)72U,
    (uint8_t)235U, (uint8_t)236U, (uint8_t)147U, (uint8_t)201U, (uint8_t)92U, (uint8_t)21U,
    (uint8_t)155U, (uint8_t)80U, (uint8_t)57U, (uint8_t)171U, (uint8_t)94U, (uint8_t)121U,
    (uint8_t)228U, (uint8_t)44U, (uint8_t)128U, (uint8_t)180U, (uint8_t)132U, (uint8_t)169U,
    (uint8_t)67U, (uint8_t)241U, (uint8_t)37U, (uint8_t)222U, (uint8_t)61U, (uint8_t)161U,
    (uint8_t)224U, (uint8_t)78U, (uint8_t)91U, (uint8_t)249U, (uint8_t)193U, (uint8_t)102U,
    (uint8_t)113U, (uint8_t)173U, (uint8_t)85U, (uint8_t)161U, (uint8_t)17U, (uint8_t)125U,
    (uint8_t)51U, (uint8_t)6U
  };

static uint8_t
siggen_vectors384_low1[32U] =
  {
    (uint8_t)182U, (uint8_t)250U, (uint8_t)242U, (uint8_t)200U, (uint8_t)146U, (uint8_t)34U,
    (uint8_t)53U, (uint8_t)197U, (uint8_t)137U, (uint8_t)194U, (uint8_t)115U, (uint8_t)104U,
    (uint8_t)163U, (uint8_t)179U, (uint8_t)230U, (uint8_t)226U, (uint8_t)244U, (uint8_t)46U,
    (uint8_t)182U, (uint8_t)7U, (uint8_t)59U, (uint8_t)249U, (uint8_t)80U, (uint8_t)127U,
    (uint8_t)25U, (uint8_t)238U, (uint8_t)208U, (uint8_t)116U, (uint8_t)108U, (uint8_t)121U,
    (uint8_t)220U, (uint8_t)237U
  };

static uint8_t
siggen_vectors384_low2[32U] =
  {
    (uint8_t)224U, (uint8_t)231U, (uint8_t)185U, (uint8_t)155U, (uint8_t)198U, (uint8_t)45U,
    (uint8_t)141U, (uint8_t)214U, (uint8_t)120U, (uint8_t)131U, (uint8_t)227U, (uint8_t)158U,
    (uint8_t)217U, (uint8_t)250U, (uint8_t)6U, (uint8_t)87U, (uint8_t)120U, (uint8_t)156U,
    (uint8_t)95U, (uint8_t)245U, (uint8_t)86U, (uint8_t)204U, (uint8_t)31U, (uint8_t)216U,
    (uint8_t)221U, (uint8_t)30U, (uint8_t)42U, (uint8_t)85U, (uint8_t)233U, (uint8_t)227U,
    (uint8_t)242U, (uint8_t)67U
  };

static uint8_t
siggen_vectors384_low3[32U] =
  {
    (uint8_t)99U, (uint8_t)251U, (uint8_t)253U, (uint8_t)2U, (uint8_t)50U, (uint8_t)185U,
    (uint8_t)85U, (uint8_t)120U, (uint8_t)7U, (uint8_t)92U, (uint8_t)144U, (uint8_t)58U,
    (uint8_t)77U, (uint8_t)191U, (uint8_t)133U, (uint8_t)173U, (uint8_t)88U, (uint8_t)248U,
    (uint8_t)53U, (uint8_t)5U, (uint8_t)22U, (uint8_t)225U, (uint8_t)236U, (uint8_t)137U,
    (uint8_t)176U, (uint8_t)238U, (uint8_t)31U, (uint8_t)94U, (uint8_t)19U, (uint8_t)98U,
    (uint8_t)218U, (uint8_t)105U
  };

static uint8_t
siggen_vectors384_low4[32U] =
  {
    (uint8_t)153U, (uint8_t)128U, (uint8_t)185U, (uint8_t)205U, (uint8_t)252U, (uint8_t)239U,
    (uint8_t)58U, (uint8_t)184U, (uint8_t)226U, (uint8_t)25U, (uint8_t)185U, (uint8_t)130U,
    (uint8_t)126U, (uint8_t)214U, (uint8_t)175U, (uint8_t)221U, (uint8_t)77U, (uint8_t)191U,
    (uint8_t)32U, (uint8_t)189U, (uint8_t)146U, (uint8_t)126U, (uint8_t)156U, (uint8_t)208U,
    (uint8_t)31U, (uint8_t)21U, (uint8_t)118U, (uint8_t)39U, (uint8_t)3U, (uint8_t)72U,
    (uint8_t)112U, (uint8_t)7U
  };

static uint8_t
siggen_vectors384_low5[32U] =
  {
    (uint8_t)245U, (uint8_t)8U, (uint8_t)120U, (uint8_t)120U, (uint8_t)226U, (uint8_t)18U,
    (uint8_t)183U, (uint8_t)3U, (uint8_t)87U, (uint8_t)143U, (uint8_t)92U, (uint8_t)102U,
    (uint8_t)244U, (uint8_t)52U, (uint8_t)136U, (uint8_t)63U, (uint8_t)62U, (uint8_t)244U,
    (uint8_t)20U, (uint8_t)220U, (uint8_t)35U, (uint8_t)226U, (uint8_t)232U, (uint8_t)216U,
    (uint8_t)171U, (uint8_t)106U, (uint8_t)141U, (uint8_t)21U, (uint8_t)158U, (uint8_t)213U,
    (uint8_t)173U, (uint8_t)131U
  };

static uint8_t
siggen_vectors384_low6[32U] =
  {
    (uint8_t)48U, (uint8_t)107U, (uint8_t)76U, (uint8_t)108U, (uint8_t)32U, (uint8_t)33U,
    (uint8_t)55U, (uint8_t)7U, (uint8_t)152U, (uint8_t)45U, (uint8_t)255U, (uint8_t)187U,
    (uint8_t)48U, (uint8_t)251U, (uint8_t)169U, (uint8_t)155U, (uint8_t)150U, (uint8_t)231U,
    (uint8_t)146U, (uint8_t)22U, (uint8_t)61U, (uint8_t)213U, (uint8_t)157U, (uint8_t)190U,
    (uint8_t)96U, (uint8_t)110U, (uint8_t)115U, (uint8_t)67U, (uint8_t)40U, (uint8_t)221U,
    (uint8_t)124U, (uint8_t)138U
  };

static uint8_t
siggen_vectors384_low7[128U] =
  {
    (uint8_t)9U, (uint8_t)154U, (uint8_t)1U, (uint8_t)49U, (uint8_t)23U, (uint8_t)159U,
    (uint8_t)255U, (uint8_t)76U, (uint8_t)105U, (uint8_t)40U, (uint8_t)228U, (uint8_t)152U,
    (uint8_t)134U, (uint8_t)210U, (uint8_t)253U, (uint8_t)179U, (uint8_t)169U, (uint8_t)242U,
    (uint8_t)57U, (uint8_t)183U, (uint8_t)221U, (uint8_t)95U, (uint8_t)168U, (uint8_t)40U,
    (uint8_t)165U, (uint8_t)44U, (uint8_t)187U, (uint8_t)227U, (uint8_t)252U, (uint8_t)250U,
    (uint8_t)190U, (uint8_t)207U, (uint8_t)187U, (uint8_t)163U, (uint8_t)225U, (uint8_t)146U,
    (uint8_t)21U, (uint8_t)155U, (uint8_t)136U, (uint8_t)123U, (uint8_t)93U, (uint8_t)19U,
    (uint8_t)170U, (uint8_t)30U, (uint8_t)20U, (uint8_t)230U, (uint8_t)160U, (uint8_t)124U,
    (uint8_t)203U, (uint8_t)178U, (uint8_t)31U, (uint8_t)106U, (uint8_t)216U, (uint8_t)183U,
    (uint8_t)232U, (uint8_t)143U, (uint8_t)238U, (uint8_t)107U, (uint8_t)234U, (uint8_t)155U,
    (uint8_t)134U, (uint8_t)222U, (uint8_t)164U, (uint8_t)15U, (uint8_t)251U, (uint8_t)150U,
    (uint8_t)47U, (uint8_t)56U, (uint8_t)85U, (uint8_t)64U, (uint8_t)86U, (uint8_t)251U,
    (uint8_t)124U, (uint8_t)91U, (uint8_t)180U, (uint8_t)134U, (uint8_t)65U, (uint8_t)137U,
    (uint8_t)21U, (uint8_t)247U, (uint8_t)231U, (uint8_t)233U, (uint8_t)185U, (uint8_t)3U,
    (uint8_t)63U, (uint8_t)227U, (uint8_t)186U, (uint8_t)175U, (uint8_t)154U, (uint8_t)6U,
    (uint8_t)157U, (uint8_t)185U, (uint8_t)139U, (uint8_t)192U, (uint8_t)47U, (uint8_t)168U,
    (uint8_t)175U, (uint8_t)61U, (uint8_t)61U, (uint8_t)24U, (uint8_t)89U, (uint8_t)161U,
    (uint8_t)19U, (uint8_t)117U, (uint8_t)214U, (uint8_t)249U, (uint8_t)138U, (uint8_t)162U,
    (uint8_t)206U, (uint8_t)99U, (uint8_t)38U, (uint8_t)6U, (uint8_t)208U, (uint8_t)128U,
    (uint8_t)13U, (uint8_t)255U, (uint8_t)127U, (uint8_t)85U, (uint8_t)180U, (uint8_t)15U,
    (uint8_t)151U, (uint8_t)26U, (uint8_t)133U, (uint8_t)134U, (uint8_t)237U, (uint8_t)107U,
    (uint8_t)57U, (uint8_t)233U
  };

static uint8_t
siggen_vectors384_low8[32U] =
  {
    (uint8_t)17U, (uint8_t)137U, (uint8_t)88U, (uint8_t)253U, (uint8_t)15U, (uint8_t)240U,
    (uint8_t)240U, (uint8_t)176U, (uint8_t)237U, (uint8_t)17U, (uint8_t)211U, (uint8_t)207U,
    (uint8_t)143U, (uint8_t)166U, (uint8_t)100U, (uint8_t)188U, (uint8_t)23U, (uint8_t)205U,
    (uint8_t)181U, (uint8_t)254U, (uint8_t)209U, (uint8_t)244U, (uint8_t)168U, (uint8_t)252U,
    (uint8_t)82U, (uint8_t)208U, (uint8_t)177U, (uint8_t)174U, (uint8_t)48U, (uint8_t)65U,
    (uint8_t)33U, (uint8_t)129U
  };

static uint8_t
siggen_vectors384_low9[32U] =
  {
    (uint8_t)175U, (uint8_t)218U, (uint8_t)130U, (uint8_t)38U, (uint8_t)12U, (uint8_t)159U,
    (uint8_t)66U, (uint8_t)18U, (uint8_t)42U, (uint8_t)63U, (uint8_t)17U, (uint8_t)198U,
    (uint8_t)5U, (uint8_t)136U, (uint8_t)57U, (uint8_t)72U, (uint8_t)143U, (uint8_t)109U,
    (uint8_t)121U, (uint8_t)119U, (uint8_t)246U, (uint8_t)242U, (uint8_t)162U, (uint8_t)99U,
    (uint8_t)198U, (uint8_t)125U, (uint8_t)6U, (uint8_t)226U, (uint8_t)126U, (uint8_t)162U,
    (uint8_t)195U, (uint8_t)85U
  };

static uint8_t
siggen_vectors384_low10[32U] =
  {
    (uint8_t)10U, (uint8_t)226U, (uint8_t)187U, (uint8_t)221U, (uint8_t)34U, (uint8_t)7U,
    (uint8_t)197U, (uint8_t)144U, (uint8_t)51U, (uint8_t)44U, (uint8_t)91U, (uint8_t)254U,
    (uint8_t)180U, (uint8_t)200U, (uint8_t)181U, (uint8_t)177U, (uint8_t)102U, (uint8_t)34U,
    (uint8_t)19U, (uint8_t)75U, (uint8_t)212U, (uint8_t)220U, (uint8_t)85U, (uint8_t)56U,
    (uint8_t)42U, (uint8_t)232U, (uint8_t)6U, (uint8_t)67U, (uint8_t)84U, (uint8_t)104U,
    (uint8_t)5U, (uint8_t)139U
  };

static uint8_t
siggen_vectors384_low11[32U] =
  {
    (uint8_t)35U, (uint8_t)18U, (uint8_t)154U, (uint8_t)153U, (uint8_t)238U, (uint8_t)218U,
    (uint8_t)61U, (uint8_t)153U, (uint8_t)164U, (uint8_t)74U, (uint8_t)87U, (uint8_t)120U,
    (uint8_t)164U, (uint8_t)110U, (uint8_t)142U, (uint8_t)117U, (uint8_t)104U, (uint8_t)185U,
    (uint8_t)28U, (uint8_t)49U, (uint8_t)251U, (uint8_t)122U, (uint8_t)134U, (uint8_t)40U,
    (uint8_t)197U, (uint8_t)217U, (uint8_t)130U, (uint8_t)13U, (uint8_t)75U, (uint8_t)237U,
    (uint8_t)74U, (uint8_t)107U
  };

static uint8_t
siggen_vectors384_low12[32U] =
  {
    (uint8_t)228U, (uint8_t)70U, (uint8_t)96U, (uint8_t)12U, (uint8_t)171U, (uint8_t)18U,
    (uint8_t)134U, (uint8_t)235U, (uint8_t)195U, (uint8_t)187U, (uint8_t)51U, (uint8_t)32U,
    (uint8_t)18U, (uint8_t)162U, (uint8_t)245U, (uint8_t)204U, (uint8_t)51U, (uint8_t)176U,
    (uint8_t)165U, (uint8_t)239U, (uint8_t)114U, (uint8_t)145U, (uint8_t)213U, (uint8_t)166U,
    (uint8_t)42U, (uint8_t)132U, (uint8_t)222U, (uint8_t)89U, (uint8_t)105U, (uint8_t)215U,
    (uint8_t)121U, (uint8_t)70U
  };

static uint8_t
siggen_vectors384_low13[32U] =
  {
    (uint8_t)207U, (uint8_t)137U, (uint8_t)177U, (uint8_t)39U, (uint8_t)147U, (uint8_t)238U,
    (uint8_t)23U, (uint8_t)146U, (uint8_t)235U, (uint8_t)38U, (uint8_t)40U, (uint8_t)59U,
    (uint8_t)72U, (uint8_t)250U, (uint8_t)11U, (uint8_t)220U, (uint8_t)180U, (uint8_t)90U,
    (uint8_t)230U, (uint8_t)246U, (uint8_t)173U, (uint8_t)75U, (uint8_t)2U, (uint8_t)86U,
    (uint8_t)75U, (uint8_t)247U, (uint8_t)134U, (uint8_t)187U, (uint8_t)151U, (uint8_t)5U,
    (uint8_t)125U, (uint8_t)90U
  };

static uint8_t
siggen_vectors384_low14[128U] =
  {
    (uint8_t)15U, (uint8_t)188U, (uint8_t)7U, (uint8_t)234U, (uint8_t)148U, (uint8_t)124U,
    (uint8_t)148U, (uint8_t)107U, (uint8_t)234U, (uint8_t)38U, (uint8_t)175U, (uint8_t)161U,
    (uint8_t)12U, (uint8_t)81U, (uint8_t)81U, (uint8_t)16U, (uint8_t)57U, (uint8_t)185U,
    (uint8_t)77U, (uint8_t)219U, (uint8_t)196U, (uint8_t)226U, (uint8_t)228U, (uint8_t)24U,
    (uint8_t)76U, (uint8_t)163U, (uint8_t)85U, (uint8_t)146U, (uint8_t)96U, (uint8_t)218U,
    (uint8_t)36U, (uint8_t)161U, (uint8_t)69U, (uint8_t)34U, (uint8_t)209U, (uint8_t)73U,
    (uint8_t)124U, (uint8_t)165U, (uint8_t)231U, (uint8_t)122U, (uint8_t)93U, (uint8_t)26U,
    (uint8_t)142U, (uint8_t)134U, (uint8_t)88U, (uint8_t)58U, (uint8_t)238U, (uint8_t)161U,
    (uint8_t)245U, (uint8_t)212U, (uint8_t)255U, (uint8_t)155U, (uint8_t)4U, (uint8_t)166U,
    (uint8_t)170U, (uint8_t)13U, (uint8_t)231U, (uint8_t)156U, (uint8_t)216U, (uint8_t)143U,
    (uint8_t)219U, (uint8_t)133U, (uint8_t)224U, (uint8_t)31U, (uint8_t)23U, (uint8_t)17U,
    (uint8_t)67U, (uint8_t)83U, (uint8_t)95U, (uint8_t)47U, (uint8_t)124U, (uint8_t)35U,
    (uint8_t)176U, (uint8_t)80U, (uint8_t)40U, (uint8_t)157U, (uint8_t)126U, (uint8_t)5U,
    (uint8_t)206U, (uint8_t)188U, (uint8_t)205U, (uint8_t)209U, (uint8_t)49U, (uint8_t)136U,
    (uint8_t)133U, (uint8_t)114U, (uint8_t)83U, (uint8_t)75U, (uint8_t)174U, (uint8_t)0U,
    (uint8_t)97U, (uint8_t)189U, (uint8_t)204U, (uint8_t)48U, (uint8_t)21U, (uint8_t)32U,
    (uint8_t)107U, (uint8_t)146U, (uint8_t)112U, (uint8_t)176U, (uint8_t)213U, (uint8_t)175U,
    (uint8_t)159U, (uint8_t)29U, (uint8_t)162U, (uint8_t)249U, (uint8_t)222U, (uint8_t)145U,
    (uint8_t)119U, (uint8_t)45U, (uint8_t)23U, (uint8_t)138U, (uint8_t)99U, (uint8_t)44U,
    (uint8_t)50U, (uint8_t)97U, (uint8_t)161U, (uint8_t)231U, (uint8_t)179U, (uint8_t)251U,
    (uint8_t)37U, (uint8_t)86U, (uint8_t)8U, (uint8_t)179U, (uint8_t)128U, (uint8_t)25U,
    (uint8_t)98U, (uint8_t)249U
  };

static uint8_t
siggen_vectors384_low15[32U] =
  {
    (uint8_t)62U, (uint8_t)100U, (uint8_t)115U, (uint8_t)87U, (uint8_t)205U, (uint8_t)91U,
    (uint8_t)117U, (uint8_t)79U, (uint8_t)173U, (uint8_t)15U, (uint8_t)219U, (uint8_t)135U,
    (uint8_t)110U, (uint8_t)175U, (uint8_t)155U, (uint8_t)26U, (uint8_t)189U, (uint8_t)123U,
    (uint8_t)96U, (uint8_t)83U, (uint8_t)111U, (uint8_t)56U, (uint8_t)60U, (uint8_t)129U,
    (uint8_t)206U, (uint8_t)87U, (uint8_t)69U, (uint8_t)236U, (uint8_t)128U, (uint8_t)130U,
    (uint8_t)100U, (uint8_t)49U
  };

static uint8_t
siggen_vectors384_low16[32U] =
  {
    (uint8_t)112U, (uint8_t)43U, (uint8_t)44U, (uint8_t)148U, (uint8_t)208U, (uint8_t)57U,
    (uint8_t)229U, (uint8_t)144U, (uint8_t)221U, (uint8_t)92U, (uint8_t)143U, (uint8_t)151U,
    (uint8_t)54U, (uint8_t)231U, (uint8_t)83U, (uint8_t)207U, (uint8_t)88U, (uint8_t)36U,
    (uint8_t)170U, (uint8_t)207U, (uint8_t)51U, (uint8_t)238U, (uint8_t)61U, (uint8_t)231U,
    (uint8_t)79U, (uint8_t)225U, (uint8_t)245U, (uint8_t)247U, (uint8_t)200U, (uint8_t)88U,
    (uint8_t)213U, (uint8_t)237U
  };

static uint8_t
siggen_vectors384_low17[32U] =
  {
    (uint8_t)12U, (uint8_t)40U, (uint8_t)137U, (uint8_t)78U, (uint8_t)144U, (uint8_t)122U,
    (uint8_t)249U, (uint8_t)159U, (uint8_t)176U, (uint8_t)209U, (uint8_t)140U, (uint8_t)158U,
    (uint8_t)152U, (uint8_t)241U, (uint8_t)154U, (uint8_t)200U, (uint8_t)13U, (uint8_t)215U,
    (uint8_t)122U, (uint8_t)191U, (uint8_t)164U, (uint8_t)190U, (uint8_t)190U, (uint8_t)69U,
    (uint8_t)5U, (uint8_t)92U, (uint8_t)8U, (uint8_t)87U, (uint8_t)184U, (uint8_t)42U, (uint8_t)15U,
    (uint8_t)77U
  };

static uint8_t
siggen_vectors384_low18[32U] =
  {
    (uint8_t)155U, (uint8_t)234U, (uint8_t)183U, (uint8_t)114U, (uint8_t)47U, (uint8_t)11U,
    (uint8_t)203U, (uint8_t)70U, (uint8_t)142U, (uint8_t)95U, (uint8_t)35U, (uint8_t)78U,
    (uint8_t)7U, (uint8_t)65U, (uint8_t)112U, (uint8_t)166U, (uint8_t)2U, (uint8_t)37U,
    (uint8_t)37U, (uint8_t)93U, (uint8_t)228U, (uint8_t)148U, (uint8_t)16U, (uint8_t)132U,
    (uint8_t)89U, (uint8_t)171U, (uint8_t)223U, (uint8_t)96U, (uint8_t)60U, (uint8_t)110U,
    (uint8_t)139U, (uint8_t)53U
  };

static uint8_t
siggen_vectors384_low19[32U] =
  {
    (uint8_t)196U, (uint8_t)2U, (uint8_t)31U, (uint8_t)183U, (uint8_t)24U, (uint8_t)90U,
    (uint8_t)7U, (uint8_t)9U, (uint8_t)101U, (uint8_t)71U, (uint8_t)175U, (uint8_t)31U,
    (uint8_t)176U, (uint8_t)105U, (uint8_t)50U, (uint8_t)227U, (uint8_t)124U, (uint8_t)248U,
    (uint8_t)189U, (uint8_t)144U, (uint8_t)207U, (uint8_t)89U, (uint8_t)61U, (uint8_t)234U,
    (uint8_t)72U, (uint8_t)212U, (uint8_t)134U, (uint8_t)20U, (uint8_t)250U, (uint8_t)35U,
    (uint8_t)126U, (uint8_t)94U
  };

static uint8_t
siggen_vectors384_low20[32U] =
  {
    (uint8_t)127U, (uint8_t)180U, (uint8_t)93U, (uint8_t)9U, (uint8_t)226U, (uint8_t)23U,
    (uint8_t)43U, (uint8_t)236U, (uint8_t)141U, (uint8_t)62U, (uint8_t)51U, (uint8_t)10U,
    (uint8_t)160U, (uint8_t)108U, (uint8_t)67U, (uint8_t)251U, (uint8_t)181U, (uint8_t)246U,
    (uint8_t)37U, (uint8_t)82U, (uint8_t)84U, (uint8_t)133U, (uint8_t)35U, (uint8_t)78U,
    (uint8_t)119U, (uint8_t)20U, (uint8_t)183U, (uint8_t)246U, (uint8_t)233U, (uint8_t)43U,
    (uint8_t)168U, (uint8_t)241U
  };

static uint8_t
siggen_vectors384_low21[128U] =
  {
    (uint8_t)30U, (uint8_t)56U, (uint8_t)215U, (uint8_t)80U, (uint8_t)217U, (uint8_t)54U,
    (uint8_t)216U, (uint8_t)82U, (uint8_t)46U, (uint8_t)157U, (uint8_t)177U, (uint8_t)135U,
    (uint8_t)63U, (uint8_t)180U, (uint8_t)153U, (uint8_t)107U, (uint8_t)239U, (uint8_t)151U,
    (uint8_t)248U, (uint8_t)218U, (uint8_t)60U, (uint8_t)102U, (uint8_t)116U, (uint8_t)161U,
    (uint8_t)34U, (uint8_t)61U, (uint8_t)41U, (uint8_t)38U, (uint8_t)63U, (uint8_t)18U,
    (uint8_t)52U, (uint8_t)169U, (uint8_t)11U, (uint8_t)117U, (uint8_t)23U, (uint8_t)133U,
    (uint8_t)49U, (uint8_t)100U, (uint8_t)68U, (uint8_t)233U, (uint8_t)186U, (uint8_t)105U,
    (uint8_t)139U, (uint8_t)200U, (uint8_t)171U, (uint8_t)108U, (uint8_t)208U, (uint8_t)16U,
    (uint8_t)99U, (uint8_t)141U, (uint8_t)24U, (uint8_t)44U, (uint8_t)154U, (uint8_t)218U,
    (uint8_t)212U, (uint8_t)227U, (uint8_t)52U, (uint8_t)178U, (uint8_t)189U, (uint8_t)117U,
    (uint8_t)41U, (uint8_t)240U, (uint8_t)174U, (uint8_t)142U, (uint8_t)154U, (uint8_t)82U,
    (uint8_t)173U, (uint8_t)96U, (uint8_t)245U, (uint8_t)152U, (uint8_t)4U, (uint8_t)178U,
    (uint8_t)215U, (uint8_t)128U, (uint8_t)237U, (uint8_t)82U, (uint8_t)189U, (uint8_t)211U,
    (uint8_t)59U, (uint8_t)11U, (uint8_t)245U, (uint8_t)64U, (uint8_t)1U, (uint8_t)71U,
    (uint8_t)194U, (uint8_t)139U, (uint8_t)67U, (uint8_t)4U, (uint8_t)229U, (uint8_t)227U,
    (uint8_t)67U, (uint8_t)69U, (uint8_t)5U, (uint8_t)174U, (uint8_t)124U, (uint8_t)227U,
    (uint8_t)13U, (uint8_t)75U, (uint8_t)35U, (uint8_t)158U, (uint8_t)126U, (uint8_t)111U,
    (uint8_t)14U, (uint8_t)207U, (uint8_t)5U, (uint8_t)139U, (uint8_t)173U, (uint8_t)213U,
    (uint8_t)179U, (uint8_t)136U, (uint8_t)237U, (uint8_t)219U, (uint8_t)173U, (uint8_t)100U,
    (uint8_t)210U, (uint8_t)77U, (uint8_t)36U, (uint8_t)48U, (uint8_t)221U, (uint8_t)4U,
    (uint8_t)180U, (uint8_t)221U, (uint8_t)238U, (uint8_t)152U, (uint8_t)249U, (uint8_t)114U,
    (uint8_t)152U, (uint8_t)143U
  };

static uint8_t
siggen_vectors384_low22[32U] =
  {
    (uint8_t)118U, (uint8_t)193U, (uint8_t)124U, (uint8_t)46U, (uint8_t)252U, (uint8_t)153U,
    (uint8_t)137U, (uint8_t)31U, (uint8_t)54U, (uint8_t)151U, (uint8_t)186U, (uint8_t)77U,
    (uint8_t)113U, (uint8_t)133U, (uint8_t)14U, (uint8_t)88U, (uint8_t)22U, (uint8_t)161U,
    (uint8_t)182U, (uint8_t)85U, (uint8_t)98U, (uint8_t)204U, (uint8_t)57U, (uint8_t)161U,
    (uint8_t)61U, (uint8_t)164U, (uint8_t)182U, (uint8_t)218U, (uint8_t)144U, (uint8_t)81U,
    (uint8_t)176U, (uint8_t)253U
  };

static uint8_t
siggen_vectors384_low23[32U] =
  {
    (uint8_t)209U, (uint8_t)37U, (uint8_t)18U, (uint8_t)233U, (uint8_t)52U, (uint8_t)195U,
    (uint8_t)103U, (uint8_t)228U, (uint8_t)196U, (uint8_t)56U, (uint8_t)77U, (uint8_t)189U,
    (uint8_t)1U, (uint8_t)14U, (uint8_t)147U, (uint8_t)65U, (uint8_t)104U, (uint8_t)64U,
    (uint8_t)40U, (uint8_t)138U, (uint8_t)11U, (uint8_t)160U, (uint8_t)11U, (uint8_t)41U,
    (uint8_t)155U, (uint8_t)78U, (uint8_t)124U, (uint8_t)13U, (uint8_t)145U, (uint8_t)87U,
    (uint8_t)139U, (uint8_t)87U
  };

static uint8_t
siggen_vectors384_low24[32U] =
  {
    (uint8_t)235U, (uint8_t)248U, (uint8_t)131U, (uint8_t)86U, (uint8_t)97U, (uint8_t)217U,
    (uint8_t)181U, (uint8_t)120U, (uint8_t)241U, (uint8_t)141U, (uint8_t)20U, (uint8_t)174U,
    (uint8_t)74U, (uint8_t)207U, (uint8_t)156U, (uint8_t)53U, (uint8_t)124U, (uint8_t)13U,
    (uint8_t)200U, (uint8_t)183U, (uint8_t)17U, (uint8_t)47U, (uint8_t)195U, (uint8_t)40U,
    (uint8_t)36U, (uint8_t)166U, (uint8_t)133U, (uint8_t)237U, (uint8_t)114U, (uint8_t)117U,
    (uint8_t)78U, (uint8_t)35U
  };

static uint8_t
siggen_vectors384_low25[32U] =
  {
    (uint8_t)119U, (uint8_t)207U, (uint8_t)250U, (uint8_t)111U, (uint8_t)154U, (uint8_t)115U,
    (uint8_t)144U, (uint8_t)67U, (uint8_t)6U, (uint8_t)249U, (uint8_t)252U, (uint8_t)211U,
    (uint8_t)246U, (uint8_t)187U, (uint8_t)179U, (uint8_t)127U, (uint8_t)82U, (uint8_t)215U,
    (uint8_t)30U, (uint8_t)57U, (uint8_t)147U, (uint8_t)27U, (uint8_t)180U, (uint8_t)174U,
    (uint8_t)194U, (uint8_t)143U, (uint8_t)155U, (uint8_t)7U, (uint8_t)110U, (uint8_t)67U,
    (uint8_t)108U, (uint8_t)207U
  };

static uint8_t
siggen_vectors384_low26[32U] =
  {
    (uint8_t)77U, (uint8_t)90U, (uint8_t)157U, (uint8_t)149U, (uint8_t)176U, (uint8_t)240U,
    (uint8_t)156U, (uint8_t)232U, (uint8_t)112U, (uint8_t)75U, (uint8_t)15U, (uint8_t)69U,
    (uint8_t)123U, (uint8_t)57U, (uint8_t)5U, (uint8_t)158U, (uint8_t)230U, (uint8_t)6U,
    (uint8_t)9U, (uint8_t)35U, (uint8_t)16U, (uint8_t)223U, (uint8_t)101U, (uint8_t)211U,
    (uint8_t)248U, (uint8_t)174U, (uint8_t)122U, (uint8_t)42U, (uint8_t)66U, (uint8_t)76U,
    (uint8_t)242U, (uint8_t)50U
  };

static uint8_t
siggen_vectors384_low27[32U] =
  {
    (uint8_t)125U, (uint8_t)60U, (uint8_t)1U, (uint8_t)76U, (uint8_t)164U, (uint8_t)112U,
    (uint8_t)167U, (uint8_t)60U, (uint8_t)239U, (uint8_t)29U, (uint8_t)29U, (uint8_t)168U,
    (uint8_t)111U, (uint8_t)42U, (uint8_t)84U, (uint8_t)17U, (uint8_t)72U, (uint8_t)173U,
    (uint8_t)84U, (uint8_t)47U, (uint8_t)188U, (uint8_t)202U, (uint8_t)249U, (uint8_t)20U,
    (uint8_t)157U, (uint8_t)27U, (uint8_t)11U, (uint8_t)3U, (uint8_t)4U, (uint8_t)65U,
    (uint8_t)167U, (uint8_t)235U
  };

static uint8_t
siggen_vectors384_low28[128U] =
  {
    (uint8_t)171U, (uint8_t)207U, (uint8_t)14U, (uint8_t)15U, (uint8_t)4U, (uint8_t)107U,
    (uint8_t)46U, (uint8_t)6U, (uint8_t)114U, (uint8_t)209U, (uint8_t)204U, (uint8_t)108U,
    (uint8_t)10U, (uint8_t)17U, (uint8_t)73U, (uint8_t)5U, (uint8_t)98U, (uint8_t)124U,
    (uint8_t)187U, (uint8_t)222U, (uint8_t)253U, (uint8_t)249U, (uint8_t)117U, (uint8_t)47U,
    (uint8_t)12U, (uint8_t)49U, (uint8_t)102U, (uint8_t)10U, (uint8_t)169U, (uint8_t)95U,
    (uint8_t)45U, (uint8_t)14U, (uint8_t)222U, (uint8_t)114U, (uint8_t)209U, (uint8_t)121U,
    (uint8_t)25U, (uint8_t)169U, (uint8_t)233U, (uint8_t)177U, (uint8_t)173U, (uint8_t)211U,
    (uint8_t)33U, (uint8_t)49U, (uint8_t)100U, (uint8_t)224U, (uint8_t)201U, (uint8_t)181U,
    (uint8_t)174U, (uint8_t)60U, (uint8_t)118U, (uint8_t)241U, (uint8_t)162U, (uint8_t)247U,
    (uint8_t)157U, (uint8_t)62U, (uint8_t)235U, (uint8_t)68U, (uint8_t)78U, (uint8_t)103U,
    (uint8_t)65U, (uint8_t)82U, (uint8_t)16U, (uint8_t)25U, (uint8_t)216U, (uint8_t)189U,
    (uint8_t)92U, (uint8_t)163U, (uint8_t)145U, (uint8_t)178U, (uint8_t)140U, (uint8_t)16U,
    (uint8_t)99U, (uint8_t)52U, (uint8_t)127U, (uint8_t)7U, (uint8_t)175U, (uint8_t)207U,
    (uint8_t)187U, (uint8_t)112U, (uint8_t)91U, (uint8_t)228U, (uint8_t)181U, (uint8_t)34U,
    (uint8_t)97U, (uint8_t)193U, (uint8_t)158U, (uint8_t)186U, (uint8_t)241U, (uint8_t)214U,
    (uint8_t)240U, (uint8_t)84U, (uint8_t)167U, (uint8_t)77U, (uint8_t)134U, (uint8_t)251U,
    (uint8_t)93U, (uint8_t)9U, (uint8_t)31U, (uint8_t)167U, (uint8_t)242U, (uint8_t)41U,
    (uint8_t)69U, (uint8_t)9U, (uint8_t)150U, (uint8_t)183U, (uint8_t)111U, (uint8_t)10U,
    (uint8_t)218U, (uint8_t)95U, (uint8_t)151U, (uint8_t)123U, (uint8_t)9U, (uint8_t)181U,
    (uint8_t)132U, (uint8_t)136U, (uint8_t)238U, (uint8_t)191U, (uint8_t)181U, (uint8_t)245U,
    (uint8_t)233U, (uint8_t)83U, (uint8_t)154U, (uint8_t)143U, (uint8_t)216U, (uint8_t)150U,
    (uint8_t)98U, (uint8_t)171U
  };

static uint8_t
siggen_vectors384_low29[32U] =
  {
    (uint8_t)103U, (uint8_t)185U, (uint8_t)222U, (uint8_t)166U, (uint8_t)165U, (uint8_t)117U,
    (uint8_t)181U, (uint8_t)16U, (uint8_t)57U, (uint8_t)153U, (uint8_t)239U, (uint8_t)255U,
    (uint8_t)206U, (uint8_t)41U, (uint8_t)204U, (uint8_t)166U, (uint8_t)136U, (uint8_t)199U,
    (uint8_t)129U, (uint8_t)120U, (uint8_t)42U, (uint8_t)65U, (uint8_t)18U, (uint8_t)159U,
    (uint8_t)222U, (uint8_t)203U, (uint8_t)206U, (uint8_t)118U, (uint8_t)96U, (uint8_t)129U,
    (uint8_t)116U, (uint8_t)222U
  };

static uint8_t
siggen_vectors384_low30[32U] =
  {
    (uint8_t)180U, (uint8_t)35U, (uint8_t)139U, (uint8_t)2U, (uint8_t)159U, (uint8_t)192U,
    (uint8_t)183U, (uint8_t)217U, (uint8_t)165U, (uint8_t)40U, (uint8_t)109U, (uint8_t)140U,
    (uint8_t)41U, (uint8_t)182U, (uint8_t)243U, (uint8_t)213U, (uint8_t)165U, (uint8_t)105U,
    (uint8_t)233U, (uint8_t)16U, (uint8_t)141U, (uint8_t)68U, (uint8_t)216U, (uint8_t)137U,
    (uint8_t)205U, (uint8_t)121U, (uint8_t)92U, (uint8_t)74U, (uint8_t)56U, (uint8_t)89U,
    (uint8_t)5U, (uint8_t)190U
  };

static uint8_t
siggen_vectors384_low31[32U] =
  {
    (uint8_t)140U, (uint8_t)179U, (uint8_t)255U, (uint8_t)248U, (uint8_t)246U, (uint8_t)204U,
    (uint8_t)167U, (uint8_t)24U, (uint8_t)124U, (uint8_t)106U, (uint8_t)154U, (uint8_t)208U,
    (uint8_t)162U, (uint8_t)177U, (uint8_t)217U, (uint8_t)244U, (uint8_t)10U, (uint8_t)224U,
    (uint8_t)27U, (uint8_t)50U, (uint8_t)167U, (uint8_t)232U, (uint8_t)248U, (uint8_t)196U,
    (uint8_t)202U, (uint8_t)117U, (uint8_t)215U, (uint8_t)26U, (uint8_t)31U, (uint8_t)255U,
    (uint8_t)179U, (uint8_t)9U
  };

static uint8_t
siggen_vectors384_low32[32U] =
  {
    (uint8_t)208U, (uint8_t)38U, (uint8_t)23U, (uint8_t)242U, (uint8_t)110U, (uint8_t)222U,
    (uint8_t)53U, (uint8_t)132U, (uint8_t)240U, (uint8_t)175U, (uint8_t)207U, (uint8_t)200U,
    (uint8_t)149U, (uint8_t)84U, (uint8_t)205U, (uint8_t)251U, (uint8_t)42U, (uint8_t)225U,
    (uint8_t)136U, (uint8_t)193U, (uint8_t)146U, (uint8_t)9U, (uint8_t)47U, (uint8_t)221U,
    (uint8_t)227U, (uint8_t)67U, (uint8_t)99U, (uint8_t)53U, (uint8_t)250U, (uint8_t)254U,
    (uint8_t)67U, (uint8_t)241U
  };

static uint8_t
siggen_vectors384_low33[32U] =
  {
    (uint8_t)38U, (uint8_t)253U, (uint8_t)145U, (uint8_t)71U, (uint8_t)208U, (uint8_t)200U,
    (uint8_t)100U, (uint8_t)64U, (uint8_t)104U, (uint8_t)159U, (uint8_t)242U, (uint8_t)215U,
    (uint8_t)85U, (uint8_t)105U, (uint8_t)121U, (uint8_t)86U, (uint8_t)80U, (uint8_t)20U,
    (uint8_t)5U, (uint8_t)6U, (uint8_t)151U, (uint8_t)7U, (uint8_t)145U, (uint8_t)201U,
    (uint8_t)10U, (uint8_t)206U, (uint8_t)9U, (uint8_t)36U, (uint8_t)180U, (uint8_t)79U,
    (uint8_t)21U, (uint8_t)134U
  };

static uint8_t
siggen_vectors384_low34[32U] =
  {
    (uint8_t)0U, (uint8_t)163U, (uint8_t)75U, (uint8_t)0U, (uint8_t)194U, (uint8_t)10U,
    (uint8_t)128U, (uint8_t)153U, (uint8_t)223U, (uint8_t)75U, (uint8_t)10U, (uint8_t)117U,
    (uint8_t)124U, (uint8_t)190U, (uint8_t)248U, (uint8_t)254U, (uint8_t)161U, (uint8_t)203U,
    (uint8_t)62U, (uint8_t)167U, (uint8_t)206U, (uint8_t)213U, (uint8_t)251U, (uint8_t)247U,
    (uint8_t)233U, (uint8_t)135U, (uint8_t)247U, (uint8_t)11U, (uint8_t)37U, (uint8_t)238U,
    (uint8_t)109U, (uint8_t)79U
  };

static uint8_t
siggen_vectors384_low35[128U] =
  {
    (uint8_t)220U, (uint8_t)61U, (uint8_t)72U, (uint8_t)132U, (uint8_t)199U, (uint8_t)65U,
    (uint8_t)164U, (uint8_t)166U, (uint8_t)135U, (uint8_t)89U, (uint8_t)60U, (uint8_t)121U,
    (uint8_t)251U, (uint8_t)78U, (uint8_t)53U, (uint8_t)197U, (uint8_t)193U, (uint8_t)60U,
    (uint8_t)120U, (uint8_t)29U, (uint8_t)202U, (uint8_t)22U, (uint8_t)219U, (uint8_t)86U,
    (uint8_t)29U, (uint8_t)126U, (uint8_t)57U, (uint8_t)53U, (uint8_t)119U, (uint8_t)247U,
    (uint8_t)182U, (uint8_t)44U, (uint8_t)164U, (uint8_t)26U, (uint8_t)110U, (uint8_t)37U,
    (uint8_t)159U, (uint8_t)193U, (uint8_t)251U, (uint8_t)141U, (uint8_t)12U, (uint8_t)78U,
    (uint8_t)30U, (uint8_t)6U, (uint8_t)37U, (uint8_t)23U, (uint8_t)160U, (uint8_t)253U,
    (uint8_t)249U, (uint8_t)85U, (uint8_t)88U, (uint8_t)183U, (uint8_t)121U, (uint8_t)159U,
    (uint8_t)32U, (uint8_t)194U, (uint8_t)17U, (uint8_t)121U, (uint8_t)97U, (uint8_t)103U,
    (uint8_t)149U, (uint8_t)62U, (uint8_t)99U, (uint8_t)114U, (uint8_t)193U, (uint8_t)24U,
    (uint8_t)41U, (uint8_t)190U, (uint8_t)236U, (uint8_t)100U, (uint8_t)134U, (uint8_t)157U,
    (uint8_t)103U, (uint8_t)191U, (uint8_t)62U, (uint8_t)225U, (uint8_t)241U, (uint8_t)69U,
    (uint8_t)93U, (uint8_t)216U, (uint8_t)122U, (uint8_t)207U, (uint8_t)189U, (uint8_t)188U,
    (uint8_t)197U, (uint8_t)151U, (uint8_t)5U, (uint8_t)110U, (uint8_t)127U, (uint8_t)179U,
    (uint8_t)71U, (uint8_t)161U, (uint8_t)118U, (uint8_t)136U, (uint8_t)173U, (uint8_t)50U,
    (uint8_t)253U, (uint8_t)167U, (uint8_t)204U, (uint8_t)195U, (uint8_t)87U, (uint8_t)45U,
    (uint8_t)167U, (uint8_t)103U, (uint8_t)125U, (uint8_t)114U, (uint8_t)85U, (uint8_t)194U,
    (uint8_t)97U, (uint8_t)115U, (uint8_t)143U, (uint8_t)7U, (uint8_t)118U, (uint8_t)60U,
    (uint8_t)212U, (uint8_t)89U, (uint8_t)115U, (uint8_t)199U, (uint8_t)40U, (uint8_t)198U,
    (uint8_t)233U, (uint8_t)173U, (uint8_t)190U, (uint8_t)236U, (uint8_t)173U, (uint8_t)195U,
    (uint8_t)217U, (uint8_t)97U
  };

static uint8_t
siggen_vectors384_low36[32U] =
  {
    (uint8_t)236U, (uint8_t)246U, (uint8_t)68U, (uint8_t)234U, (uint8_t)155U, (uint8_t)108U,
    (uint8_t)58U, (uint8_t)4U, (uint8_t)253U, (uint8_t)254U, (uint8_t)45U, (uint8_t)228U,
    (uint8_t)253U, (uint8_t)203U, (uint8_t)85U, (uint8_t)253U, (uint8_t)205U, (uint8_t)252U,
    (uint8_t)247U, (uint8_t)56U, (uint8_t)192U, (uint8_t)179U, (uint8_t)23U, (uint8_t)101U,
    (uint8_t)117U, (uint8_t)250U, (uint8_t)145U, (uint8_t)81U, (uint8_t)81U, (uint8_t)148U,
    (uint8_t)181U, (uint8_t)102U
  };

static uint8_t
siggen_vectors384_low37[32U] =
  {
    (uint8_t)195U, (uint8_t)189U, (uint8_t)199U, (uint8_t)199U, (uint8_t)149U, (uint8_t)236U,
    (uint8_t)148U, (uint8_t)98U, (uint8_t)10U, (uint8_t)44U, (uint8_t)255U, (uint8_t)246U,
    (uint8_t)20U, (uint8_t)193U, (uint8_t)58U, (uint8_t)51U, (uint8_t)144U, (uint8_t)165U,
    (uint8_t)232U, (uint8_t)108U, (uint8_t)137U, (uint8_t)46U, (uint8_t)83U, (uint8_t)162U,
    (uint8_t)77U, (uint8_t)62U, (uint8_t)210U, (uint8_t)34U, (uint8_t)40U, (uint8_t)188U,
    (uint8_t)133U, (uint8_t)191U
  };

static uint8_t
siggen_vectors384_low38[32U] =
  {
    (uint8_t)112U, (uint8_t)72U, (uint8_t)15U, (uint8_t)197U, (uint8_t)207U, (uint8_t)74U,
    (uint8_t)172U, (uint8_t)215U, (uint8_t)62U, (uint8_t)36U, (uint8_t)97U, (uint8_t)139U,
    (uint8_t)97U, (uint8_t)181U, (uint8_t)197U, (uint8_t)108U, (uint8_t)28U, (uint8_t)237U,
    (uint8_t)140U, (uint8_t)79U, (uint8_t)27U, (uint8_t)134U, (uint8_t)149U, (uint8_t)128U,
    (uint8_t)234U, (uint8_t)83U, (uint8_t)142U, (uint8_t)104U, (uint8_t)199U, (uint8_t)166U,
    (uint8_t)28U, (uint8_t)163U
  };

static uint8_t
siggen_vectors384_low39[32U] =
  {
    (uint8_t)83U, (uint8_t)41U, (uint8_t)29U, (uint8_t)81U, (uint8_t)246U, (uint8_t)141U,
    (uint8_t)154U, (uint8_t)18U, (uint8_t)209U, (uint8_t)220U, (uint8_t)220U, (uint8_t)88U,
    (uint8_t)137U, (uint8_t)43U, (uint8_t)47U, (uint8_t)120U, (uint8_t)108U, (uint8_t)193U,
    (uint8_t)95U, (uint8_t)99U, (uint8_t)31U, (uint8_t)22U, (uint8_t)153U, (uint8_t)125U,
    (uint8_t)42U, (uint8_t)73U, (uint8_t)186U, (uint8_t)206U, (uint8_t)81U, (uint8_t)53U,
    (uint8_t)87U, (uint8_t)212U
  };

static uint8_t
siggen_vectors384_low40[32U] =
  {
    (uint8_t)168U, (uint8_t)96U, (uint8_t)200U, (uint8_t)178U, (uint8_t)134U, (uint8_t)237U,
    (uint8_t)249U, (uint8_t)115U, (uint8_t)206U, (uint8_t)76U, (uint8_t)228U, (uint8_t)207U,
    (uint8_t)110U, (uint8_t)112U, (uint8_t)220U, (uint8_t)155U, (uint8_t)191U, (uint8_t)56U,
    (uint8_t)24U, (uint8_t)195U, (uint8_t)108U, (uint8_t)2U, (uint8_t)58U, (uint8_t)132U,
    (uint8_t)86U, (uint8_t)119U, (uint8_t)169U, (uint8_t)150U, (uint8_t)55U, (uint8_t)5U,
    (uint8_t)223U, (uint8_t)139U
  };

static uint8_t
siggen_vectors384_low41[32U] =
  {
    (uint8_t)86U, (uint8_t)48U, (uint8_t)249U, (uint8_t)134U, (uint8_t)177U, (uint8_t)196U,
    (uint8_t)94U, (uint8_t)54U, (uint8_t)225U, (uint8_t)39U, (uint8_t)221U, (uint8_t)121U,
    (uint8_t)50U, (uint8_t)34U, (uint8_t)28U, (uint8_t)66U, (uint8_t)114U, (uint8_t)168U,
    (uint8_t)204U, (uint8_t)110U, (uint8_t)37U, (uint8_t)94U, (uint8_t)137U, (uint8_t)240U,
    (uint8_t)240U, (uint8_t)202U, (uint8_t)78U, (uint8_t)195U, (uint8_t)169U, (uint8_t)247U,
    (uint8_t)100U, (uint8_t)148U
  };

static uint8_t
siggen_vectors384_low42[128U] =
  {
    (uint8_t)113U, (uint8_t)155U, (uint8_t)241U, (uint8_t)145U, (uint8_t)26U, (uint8_t)229U,
    (uint8_t)181U, (uint8_t)224U, (uint8_t)143U, (uint8_t)29U, (uint8_t)151U, (uint8_t)185U,
    (uint8_t)42U, (uint8_t)80U, (uint8_t)137U, (uint8_t)192U, (uint8_t)171U, (uint8_t)157U,
    (uint8_t)111U, (uint8_t)28U, (uint8_t)23U, (uint8_t)90U, (uint8_t)199U, (uint8_t)25U,
    (uint8_t)144U, (uint8_t)134U, (uint8_t)174U, (uint8_t)234U, (uint8_t)164U, (uint8_t)22U,
    (uint8_t)161U, (uint8_t)126U, (uint8_t)109U, (uint8_t)111U, (uint8_t)132U, (uint8_t)134U,
    (uint8_t)199U, (uint8_t)17U, (uint8_t)211U, (uint8_t)134U, (uint8_t)242U, (uint8_t)132U,
    (uint8_t)240U, (uint8_t)150U, (uint8_t)41U, (uint8_t)102U, (uint8_t)137U, (uint8_t)165U,
    (uint8_t)77U, (uint8_t)51U, (uint8_t)12U, (uint8_t)142U, (uint8_t)251U, (uint8_t)15U,
    (uint8_t)95U, (uint8_t)161U, (uint8_t)197U, (uint8_t)186U, (uint8_t)18U, (uint8_t)141U,
    (uint8_t)50U, (uint8_t)52U, (uint8_t)163U, (uint8_t)218U, (uint8_t)133U, (uint8_t)108U,
    (uint8_t)42U, (uint8_t)148U, (uint8_t)102U, (uint8_t)126U, (uint8_t)247U, (uint8_t)16U,
    (uint8_t)54U, (uint8_t)22U, (uint8_t)166U, (uint8_t)76U, (uint8_t)145U, (uint8_t)49U,
    (uint8_t)53U, (uint8_t)244U, (uint8_t)225U, (uint8_t)220U, (uint8_t)80U, (uint8_t)227U,
    (uint8_t)141U, (uint8_t)170U, (uint8_t)96U, (uint8_t)97U, (uint8_t)15U, (uint8_t)115U,
    (uint8_t)42U, (uint8_t)209U, (uint8_t)190U, (uint8_t)223U, (uint8_t)204U, (uint8_t)57U,
    (uint8_t)111U, (uint8_t)135U, (uint8_t)22U, (uint8_t)147U, (uint8_t)146U, (uint8_t)82U,
    (uint8_t)3U, (uint8_t)20U, (uint8_t)166U, (uint8_t)182U, (uint8_t)185U, (uint8_t)175U,
    (uint8_t)103U, (uint8_t)147U, (uint8_t)219U, (uint8_t)171U, (uint8_t)173U, (uint8_t)69U,
    (uint8_t)153U, (uint8_t)82U, (uint8_t)82U, (uint8_t)40U, (uint8_t)204U, (uint8_t)124U,
    (uint8_t)156U, (uint8_t)50U, (uint8_t)196U, (uint8_t)216U, (uint8_t)224U, (uint8_t)151U,
    (uint8_t)221U, (uint8_t)246U
  };

static uint8_t
siggen_vectors384_low43[32U] =
  {
    (uint8_t)73U, (uint8_t)97U, (uint8_t)72U, (uint8_t)92U, (uint8_t)188U, (uint8_t)151U,
    (uint8_t)143U, (uint8_t)132U, (uint8_t)86U, (uint8_t)236U, (uint8_t)90U, (uint8_t)199U,
    (uint8_t)207U, (uint8_t)201U, (uint8_t)247U, (uint8_t)217U, (uint8_t)41U, (uint8_t)143U,
    (uint8_t)153U, (uint8_t)65U, (uint8_t)94U, (uint8_t)202U, (uint8_t)230U, (uint8_t)156U,
    (uint8_t)132U, (uint8_t)145U, (uint8_t)178U, (uint8_t)88U, (uint8_t)192U, (uint8_t)41U,
    (uint8_t)191U, (uint8_t)238U
  };

static uint8_t
siggen_vectors384_low44[32U] =
  {
    (uint8_t)141U, (uint8_t)64U, (uint8_t)191U, (uint8_t)34U, (uint8_t)153U, (uint8_t)224U,
    (uint8_t)93U, (uint8_t)117U, (uint8_t)141U, (uint8_t)66U, (uint8_t)25U, (uint8_t)114U,
    (uint8_t)232U, (uint8_t)28U, (uint8_t)251U, (uint8_t)12U, (uint8_t)206U, (uint8_t)104U,
    (uint8_t)185U, (uint8_t)73U, (uint8_t)36U, (uint8_t)13U, (uint8_t)195U, (uint8_t)15U,
    (uint8_t)49U, (uint8_t)88U, (uint8_t)54U, (uint8_t)172U, (uint8_t)199U, (uint8_t)11U,
    (uint8_t)239U, (uint8_t)3U
  };

static uint8_t
siggen_vectors384_low45[32U] =
  {
    (uint8_t)86U, (uint8_t)116U, (uint8_t)230U, (uint8_t)247U, (uint8_t)127U, (uint8_t)139U,
    (uint8_t)70U, (uint8_t)244U, (uint8_t)108U, (uint8_t)202U, (uint8_t)147U, (uint8_t)125U,
    (uint8_t)131U, (uint8_t)177U, (uint8_t)40U, (uint8_t)223U, (uint8_t)251U, (uint8_t)233U,
    (uint8_t)189U, (uint8_t)126U, (uint8_t)13U, (uint8_t)61U, (uint8_t)8U, (uint8_t)170U,
    (uint8_t)44U, (uint8_t)187U, (uint8_t)253U, (uint8_t)251U, (uint8_t)22U, (uint8_t)247U,
    (uint8_t)44U, (uint8_t)154U
  };

static uint8_t
siggen_vectors384_low46[32U] =
  {
    (uint8_t)55U, (uint8_t)58U, (uint8_t)130U, (uint8_t)91U, (uint8_t)90U, (uint8_t)116U,
    (uint8_t)183U, (uint8_t)185U, (uint8_t)224U, (uint8_t)47U, (uint8_t)141U, (uint8_t)77U,
    (uint8_t)135U, (uint8_t)107U, (uint8_t)87U, (uint8_t)123U, (uint8_t)76U, (uint8_t)57U,
    (uint8_t)132U, (uint8_t)22U, (uint8_t)141U, (uint8_t)112U, (uint8_t)75U, (uint8_t)169U,
    (uint8_t)249U, (uint8_t)91U, (uint8_t)25U, (uint8_t)192U, (uint8_t)94U, (uint8_t)213U,
    (uint8_t)144U, (uint8_t)175U
  };

static uint8_t
siggen_vectors384_low47[32U] =
  {
    (uint8_t)239U, (uint8_t)111U, (uint8_t)179U, (uint8_t)134U, (uint8_t)173U, (uint8_t)4U,
    (uint8_t)75U, (uint8_t)99U, (uint8_t)254U, (uint8_t)183U, (uint8_t)68U, (uint8_t)95U,
    (uint8_t)161U, (uint8_t)107U, (uint8_t)16U, (uint8_t)49U, (uint8_t)144U, (uint8_t)24U,
    (uint8_t)233U, (uint8_t)206U, (uint8_t)169U, (uint8_t)239U, (uint8_t)66U, (uint8_t)188U,
    (uint8_t)168U, (uint8_t)59U, (uint8_t)218U, (uint8_t)208U, (uint8_t)25U, (uint8_t)146U,
    (uint8_t)35U, (uint8_t)74U
  };

static uint8_t
siggen_vectors384_low48[32U] =
  {
    (uint8_t)172U, (uint8_t)31U, (uint8_t)66U, (uint8_t)246U, (uint8_t)82U, (uint8_t)235U,
    (uint8_t)23U, (uint8_t)134U, (uint8_t)229U, (uint8_t)123U, (uint8_t)224U, (uint8_t)29U,
    (uint8_t)132U, (uint8_t)124U, (uint8_t)129U, (uint8_t)247U, (uint8_t)239U, (uint8_t)160U,
    (uint8_t)114U, (uint8_t)186U, (uint8_t)86U, (uint8_t)109U, (uint8_t)69U, (uint8_t)131U,
    (uint8_t)175U, (uint8_t)79U, (uint8_t)21U, (uint8_t)81U, (uint8_t)163U, (uint8_t)247U,
    (uint8_t)108U, (uint8_t)101U
  };

static uint8_t
siggen_vectors384_low49[128U] =
  {
    (uint8_t)124U, (uint8_t)241U, (uint8_t)159U, (uint8_t)76U, (uint8_t)133U, (uint8_t)30U,
    (uint8_t)151U, (uint8_t)197U, (uint8_t)188U, (uint8_t)161U, (uint8_t)26U, (uint8_t)57U,
    (uint8_t)240U, (uint8_t)7U, (uint8_t)76U, (uint8_t)59U, (uint8_t)123U, (uint8_t)211U,
    (uint8_t)39U, (uint8_t)78U, (uint8_t)125U, (uint8_t)215U, (uint8_t)93U, (uint8_t)4U,
    (uint8_t)71U, (uint8_t)183U, (uint8_t)184U, (uint8_t)73U, (uint8_t)149U, (uint8_t)223U,
    (uint8_t)201U, (uint8_t)247U, (uint8_t)22U, (uint8_t)191U, (uint8_t)8U, (uint8_t)194U,
    (uint8_t)83U, (uint8_t)71U, (uint8_t)245U, (uint8_t)111U, (uint8_t)204U, (uint8_t)94U,
    (uint8_t)81U, (uint8_t)73U, (uint8_t)203U, (uint8_t)63U, (uint8_t)156U, (uint8_t)251U,
    (uint8_t)57U, (uint8_t)212U, (uint8_t)8U, (uint8_t)172U, (uint8_t)229U, (uint8_t)165U,
    (uint8_t)196U, (uint8_t)126U, (uint8_t)117U, (uint8_t)247U, (uint8_t)168U, (uint8_t)39U,
    (uint8_t)250U, (uint8_t)11U, (uint8_t)185U, (uint8_t)146U, (uint8_t)27U, (uint8_t)181U,
    (uint8_t)178U, (uint8_t)58U, (uint8_t)96U, (uint8_t)83U, (uint8_t)219U, (uint8_t)225U,
    (uint8_t)250U, (uint8_t)43U, (uint8_t)186U, (uint8_t)52U, (uint8_t)26U, (uint8_t)200U,
    (uint8_t)116U, (uint8_t)217U, (uint8_t)177U, (uint8_t)51U, (uint8_t)63U, (uint8_t)196U,
    (uint8_t)220U, (uint8_t)34U, (uint8_t)72U, (uint8_t)84U, (uint8_t)148U, (uint8_t)159U,
    (uint8_t)92U, (uint8_t)141U, (uint8_t)138U, (uint8_t)95U, (uint8_t)237U, (uint8_t)208U,
    (uint8_t)47U, (uint8_t)178U, (uint8_t)111U, (uint8_t)223U, (uint8_t)205U, (uint8_t)59U,
    (uint8_t)227U, (uint8_t)81U, (uint8_t)174U, (uint8_t)192U, (uint8_t)252U, (uint8_t)190U,
    (uint8_t)241U, (uint8_t)137U, (uint8_t)114U, (uint8_t)149U, (uint8_t)108U, (uint8_t)110U,
    (uint8_t)192U, (uint8_t)239U, (uint8_t)250U, (uint8_t)240U, (uint8_t)87U, (uint8_t)235U,
    (uint8_t)68U, (uint8_t)32U, (uint8_t)182U, (uint8_t)210U, (uint8_t)142U, (uint8_t)12U,
    (uint8_t)0U, (uint8_t)140U
  };

static uint8_t
siggen_vectors384_low50[32U] =
  {
    (uint8_t)88U, (uint8_t)121U, (uint8_t)7U, (uint8_t)231U, (uint8_t)242U, (uint8_t)21U,
    (uint8_t)207U, (uint8_t)13U, (uint8_t)44U, (uint8_t)178U, (uint8_t)201U, (uint8_t)230U,
    (uint8_t)150U, (uint8_t)61U, (uint8_t)69U, (uint8_t)182U, (uint8_t)229U, (uint8_t)53U,
    (uint8_t)237U, (uint8_t)66U, (uint8_t)108U, (uint8_t)130U, (uint8_t)138U, (uint8_t)110U,
    (uint8_t)162U, (uint8_t)251U, (uint8_t)99U, (uint8_t)124U, (uint8_t)202U, (uint8_t)76U,
    (uint8_t)92U, (uint8_t)189U
  };

static uint8_t
siggen_vectors384_low51[32U] =
  {
    (uint8_t)102U, (uint8_t)13U, (uint8_t)164U, (uint8_t)92U, (uint8_t)65U, (uint8_t)60U,
    (uint8_t)201U, (uint8_t)201U, (uint8_t)82U, (uint8_t)98U, (uint8_t)2U, (uint8_t)193U,
    (uint8_t)107U, (uint8_t)64U, (uint8_t)42U, (uint8_t)246U, (uint8_t)2U, (uint8_t)211U,
    (uint8_t)13U, (uint8_t)170U, (uint8_t)167U, (uint8_t)195U, (uint8_t)66U, (uint8_t)241U,
    (uint8_t)231U, (uint8_t)34U, (uint8_t)241U, (uint8_t)81U, (uint8_t)153U, (uint8_t)64U,
    (uint8_t)127U, (uint8_t)49U
  };

static uint8_t
siggen_vectors384_low52[32U] =
  {
    (uint8_t)230U, (uint8_t)248U, (uint8_t)203U, (uint8_t)176U, (uint8_t)105U, (uint8_t)19U,
    (uint8_t)204U, (uint8_t)113U, (uint8_t)143U, (uint8_t)45U, (uint8_t)105U, (uint8_t)186U,
    (uint8_t)47U, (uint8_t)179U, (uint8_t)19U, (uint8_t)127U, (uint8_t)4U, (uint8_t)164U,
    (uint8_t)28U, (uint8_t)39U, (uint8_t)198U, (uint8_t)118U, (uint8_t)209U, (uint8_t)168U,
    (uint8_t)15U, (uint8_t)191U, (uint8_t)48U, (uint8_t)234U, (uint8_t)60U, (uint8_t)164U,
    (uint8_t)100U, (uint8_t)57U
  };

static uint8_t
siggen_vectors384_low53[32U] =
  {
    (uint8_t)107U, (uint8_t)142U, (uint8_t)183U, (uint8_t)192U, (uint8_t)216U, (uint8_t)175U,
    (uint8_t)148U, (uint8_t)86U, (uint8_t)185U, (uint8_t)93U, (uint8_t)215U, (uint8_t)5U,
    (uint8_t)97U, (uint8_t)160U, (uint8_t)233U, (uint8_t)2U, (uint8_t)134U, (uint8_t)62U,
    (uint8_t)109U, (uint8_t)250U, (uint8_t)28U, (uint8_t)40U, (uint8_t)208U, (uint8_t)253U,
    (uint8_t)74U, (uint8_t)5U, (uint8_t)9U, (uint8_t)241U, (uint8_t)194U, (uint8_t)166U,
    (uint8_t)71U, (uint8_t)178U
  };

static uint8_t
siggen_vectors384_low54[32U] =
  {
    (uint8_t)8U, (uint8_t)250U, (uint8_t)191U, (uint8_t)155U, (uint8_t)87U, (uint8_t)222U,
    (uint8_t)129U, (uint8_t)135U, (uint8_t)91U, (uint8_t)250U, (uint8_t)122U, (uint8_t)65U,
    (uint8_t)24U, (uint8_t)227U, (uint8_t)228U, (uint8_t)76U, (uint8_t)251U, (uint8_t)56U,
    (uint8_t)236U, (uint8_t)106U, (uint8_t)155U, (uint8_t)32U, (uint8_t)20U, (uint8_t)148U,
    (uint8_t)2U, (uint8_t)7U, (uint8_t)186U, (uint8_t)59U, (uint8_t)28U, (uint8_t)88U, (uint8_t)48U,
    (uint8_t)56U
  };

static uint8_t
siggen_vectors384_low55[32U] =
  {
    (uint8_t)165U, (uint8_t)141U, (uint8_t)25U, (uint8_t)155U, (uint8_t)29U, (uint8_t)235U,
    (uint8_t)167U, (uint8_t)53U, (uint8_t)6U, (uint8_t)22U, (uint8_t)35U, (uint8_t)13U,
    (uint8_t)134U, (uint8_t)123U, (uint8_t)39U, (uint8_t)71U, (uint8_t)163U, (uint8_t)69U,
    (uint8_t)148U, (uint8_t)33U, (uint8_t)129U, (uint8_t)28U, (uint8_t)41U, (uint8_t)24U,
    (uint8_t)54U, (uint8_t)171U, (uint8_t)238U, (uint8_t)113U, (uint8_t)91U, (uint8_t)143U,
    (uint8_t)103U, (uint8_t)180U
  };

static uint8_t
siggen_vectors384_low56[128U] =
  {
    (uint8_t)184U, (uint8_t)146U, (uint8_t)255U, (uint8_t)171U, (uint8_t)184U, (uint8_t)9U,
    (uint8_t)233U, (uint8_t)138U, (uint8_t)153U, (uint8_t)176U, (uint8_t)167U, (uint8_t)152U,
    (uint8_t)149U, (uint8_t)68U, (uint8_t)95U, (uint8_t)199U, (uint8_t)52U, (uint8_t)250U,
    (uint8_t)27U, (uint8_t)97U, (uint8_t)89U, (uint8_t)249U, (uint8_t)205U, (uint8_t)219U,
    (uint8_t)109U, (uint8_t)33U, (uint8_t)229U, (uint8_t)16U, (uint8_t)112U, (uint8_t)139U,
    (uint8_t)218U, (uint8_t)182U, (uint8_t)7U, (uint8_t)102U, (uint8_t)51U, (uint8_t)172U,
    (uint8_t)48U, (uint8_t)170U, (uint8_t)239U, (uint8_t)67U, (uint8_t)219U, (uint8_t)86U,
    (uint8_t)108U, (uint8_t)13U, (uint8_t)33U, (uint8_t)244U, (uint8_t)56U, (uint8_t)29U,
    (uint8_t)180U, (uint8_t)103U, (uint8_t)17U, (uint8_t)254U, (uint8_t)56U, (uint8_t)18U,
    (uint8_t)197U, (uint8_t)206U, (uint8_t)15U, (uint8_t)180U, (uint8_t)164U, (uint8_t)14U,
    (uint8_t)61U, (uint8_t)93U, (uint8_t)138U, (uint8_t)178U, (uint8_t)78U, (uint8_t)78U,
    (uint8_t)130U, (uint8_t)211U, (uint8_t)86U, (uint8_t)12U, (uint8_t)109U, (uint8_t)199U,
    (uint8_t)195U, (uint8_t)119U, (uint8_t)148U, (uint8_t)238U, (uint8_t)23U, (uint8_t)212U,
    (uint8_t)161U, (uint8_t)68U, (uint8_t)6U, (uint8_t)94U, (uint8_t)249U, (uint8_t)156U,
    (uint8_t)141U, (uint8_t)28U, (uint8_t)136U, (uint8_t)188U, (uint8_t)34U, (uint8_t)173U,
    (uint8_t)140U, (uint8_t)76U, (uint8_t)39U, (uint8_t)216U, (uint8_t)90U, (uint8_t)213U,
    (uint8_t)24U, (uint8_t)250U, (uint8_t)87U, (uint8_t)71U, (uint8_t)174U, (uint8_t)53U,
    (uint8_t)39U, (uint8_t)111U, (uint8_t)193U, (uint8_t)4U, (uint8_t)130U, (uint8_t)157U,
    (uint8_t)63U, (uint8_t)92U, (uint8_t)114U, (uint8_t)252U, (uint8_t)42U, (uint8_t)158U,
    (uint8_t)165U, (uint8_t)90U, (uint8_t)28U, (uint8_t)58U, (uint8_t)135U, (uint8_t)0U,
    (uint8_t)124U, (uint8_t)209U, (uint8_t)51U, (uint8_t)38U, (uint8_t)63U, (uint8_t)121U,
    (uint8_t)228U, (uint8_t)5U
  };

static uint8_t
siggen_vectors384_low57[32U] =
  {
    (uint8_t)36U, (uint8_t)177U, (uint8_t)229U, (uint8_t)103U, (uint8_t)109U, (uint8_t)26U,
    (uint8_t)157U, (uint8_t)107U, (uint8_t)100U, (uint8_t)90U, (uint8_t)152U, (uint8_t)65U,
    (uint8_t)65U, (uint8_t)161U, (uint8_t)87U, (uint8_t)193U, (uint8_t)36U, (uint8_t)83U,
    (uint8_t)31U, (uint8_t)238U, (uint8_t)185U, (uint8_t)45U, (uint8_t)145U, (uint8_t)81U,
    (uint8_t)16U, (uint8_t)174U, (uint8_t)244U, (uint8_t)116U, (uint8_t)177U, (uint8_t)226U,
    (uint8_t)118U, (uint8_t)102U
  };

static uint8_t
siggen_vectors384_low58[32U] =
  {
    (uint8_t)180U, (uint8_t)144U, (uint8_t)154U, (uint8_t)91U, (uint8_t)223U, (uint8_t)37U,
    (uint8_t)247U, (uint8_t)101U, (uint8_t)159U, (uint8_t)78U, (uint8_t)243U, (uint8_t)94U,
    (uint8_t)75U, (uint8_t)129U, (uint8_t)20U, (uint8_t)41U, (uint8_t)251U, (uint8_t)44U,
    (uint8_t)89U, (uint8_t)18U, (uint8_t)110U, (uint8_t)61U, (uint8_t)173U, (uint8_t)9U,
    (uint8_t)16U, (uint8_t)11U, (uint8_t)70U, (uint8_t)174U, (uint8_t)166U, (uint8_t)235U,
    (uint8_t)231U, (uint8_t)166U
  };

static uint8_t
siggen_vectors384_low59[32U] =
  {
    (uint8_t)118U, (uint8_t)10U, (uint8_t)224U, (uint8_t)21U, (uint8_t)250U, (uint8_t)106U,
    (uint8_t)245U, (uint8_t)201U, (uint8_t)116U, (uint8_t)156U, (uint8_t)64U, (uint8_t)48U,
    (uint8_t)253U, (uint8_t)181U, (uint8_t)222U, (uint8_t)110U, (uint8_t)88U, (uint8_t)198U,
    (uint8_t)181U, (uint8_t)177U, (uint8_t)148U, (uint8_t)72U, (uint8_t)41U, (uint8_t)16U,
    (uint8_t)92U, (uint8_t)247U, (uint8_t)237U, (uint8_t)247U, (uint8_t)211U, (uint8_t)162U,
    (uint8_t)44U, (uint8_t)251U
  };

static uint8_t
siggen_vectors384_low60[32U] =
  {
    (uint8_t)136U, (uint8_t)121U, (uint8_t)73U, (uint8_t)35U, (uint8_t)216U, (uint8_t)148U,
    (uint8_t)59U, (uint8_t)93U, (uint8_t)188U, (uint8_t)199U, (uint8_t)167U, (uint8_t)167U,
    (uint8_t)101U, (uint8_t)3U, (uint8_t)136U, (uint8_t)15U, (uint8_t)247U, (uint8_t)218U,
    (uint8_t)99U, (uint8_t)43U, (uint8_t)8U, (uint8_t)131U, (uint8_t)170U, (uint8_t)166U,
    (uint8_t)10U, (uint8_t)159U, (uint8_t)204U, (uint8_t)113U, (uint8_t)191U, (uint8_t)136U,
    (uint8_t)15U, (uint8_t)214U
  };

static uint8_t
siggen_vectors384_low61[32U] =
  {
    (uint8_t)110U, (uint8_t)201U, (uint8_t)163U, (uint8_t)64U, (uint8_t)183U, (uint8_t)127U,
    (uint8_t)174U, (uint8_t)60U, (uint8_t)120U, (uint8_t)39U, (uint8_t)250U, (uint8_t)150U,
    (uint8_t)217U, (uint8_t)151U, (uint8_t)233U, (uint8_t)39U, (uint8_t)34U, (uint8_t)255U,
    (uint8_t)42U, (uint8_t)146U, (uint8_t)130U, (uint8_t)23U, (uint8_t)182U, (uint8_t)221U,
    (uint8_t)60U, (uint8_t)98U, (uint8_t)143U, (uint8_t)61U, (uint8_t)73U, (uint8_t)174U,
    (uint8_t)76U, (uint8_t)230U
  };

static uint8_t
siggen_vectors384_low62[32U] =
  {
    (uint8_t)99U, (uint8_t)123U, (uint8_t)84U, (uint8_t)187U, (uint8_t)207U, (uint8_t)183U,
    (uint8_t)231U, (uint8_t)216U, (uint8_t)164U, (uint8_t)30U, (uint8_t)163U, (uint8_t)23U,
    (uint8_t)252U, (uint8_t)252U, (uint8_t)168U, (uint8_t)173U, (uint8_t)116U, (uint8_t)235U,
    (uint8_t)59U, (uint8_t)182U, (uint8_t)183U, (uint8_t)120U, (uint8_t)188U, (uint8_t)126U,
    (uint8_t)249U, (uint8_t)222U, (uint8_t)192U, (uint8_t)9U, (uint8_t)40U, (uint8_t)25U,
    (uint8_t)118U, (uint8_t)247U
  };

static uint8_t
siggen_vectors384_low63[128U] =
  {
    (uint8_t)129U, (uint8_t)68U, (uint8_t)227U, (uint8_t)112U, (uint8_t)20U, (uint8_t)201U,
    (uint8_t)94U, (uint8_t)19U, (uint8_t)35U, (uint8_t)28U, (uint8_t)189U, (uint8_t)111U,
    (uint8_t)166U, (uint8_t)71U, (uint8_t)114U, (uint8_t)119U, (uint8_t)31U, (uint8_t)147U,
    (uint8_t)180U, (uint8_t)78U, (uint8_t)55U, (uint8_t)247U, (uint8_t)176U, (uint8_t)47U,
    (uint8_t)89U, (uint8_t)32U, (uint8_t)153U, (uint8_t)204U, (uint8_t)20U, (uint8_t)99U,
    (uint8_t)67U, (uint8_t)237U, (uint8_t)212U, (uint8_t)244U, (uint8_t)236U, (uint8_t)159U,
    (uint8_t)161U, (uint8_t)188U, (uint8_t)104U, (uint8_t)215U, (uint8_t)242U, (uint8_t)233U,
    (uint8_t)238U, (uint8_t)120U, (uint8_t)252U, (uint8_t)55U, (uint8_t)4U, (uint8_t)67U,
    (uint8_t)170U, (uint8_t)40U, (uint8_t)3U, (uint8_t)255U, (uint8_t)76U, (uint8_t)165U,
    (uint8_t)46U, (uint8_t)228U, (uint8_t)154U, (uint8_t)47U, (uint8_t)77U, (uint8_t)175U,
    (uint8_t)44U, (uint8_t)129U, (uint8_t)129U, (uint8_t)234U, (uint8_t)123U, (uint8_t)132U,
    (uint8_t)117U, (uint8_t)179U, (uint8_t)160U, (uint8_t)246U, (uint8_t)8U, (uint8_t)252U,
    (uint8_t)50U, (uint8_t)121U, (uint8_t)208U, (uint8_t)158U, (uint8_t)45U, (uint8_t)5U,
    (uint8_t)127U, (uint8_t)190U, (uint8_t)63U, (uint8_t)47U, (uint8_t)251U, (uint8_t)229U,
    (uint8_t)19U, (uint8_t)55U, (uint8_t)150U, (uint8_t)18U, (uint8_t)71U, (uint8_t)129U,
    (uint8_t)41U, (uint8_t)156U, (uint8_t)109U, (uint8_t)166U, (uint8_t)12U, (uint8_t)254U,
    (uint8_t)126U, (uint8_t)206U, (uint8_t)163U, (uint8_t)171U, (uint8_t)195U, (uint8_t)7U,
    (uint8_t)6U, (uint8_t)222U, (uint8_t)210U, (uint8_t)205U, (uint8_t)241U, (uint8_t)143U,
    (uint8_t)157U, (uint8_t)120U, (uint8_t)142U, (uint8_t)89U, (uint8_t)242U, (uint8_t)195U,
    (uint8_t)22U, (uint8_t)98U, (uint8_t)223U, (uint8_t)58U, (uint8_t)190U, (uint8_t)1U,
    (uint8_t)169U, (uint8_t)177U, (uint8_t)35U, (uint8_t)4U, (uint8_t)251U, (uint8_t)141U,
    (uint8_t)92U, (uint8_t)140U
  };

static uint8_t
siggen_vectors384_low64[32U] =
  {
    (uint8_t)188U, (uint8_t)228U, (uint8_t)156U, (uint8_t)123U, (uint8_t)3U, (uint8_t)220U,
    (uint8_t)220U, (uint8_t)114U, (uint8_t)57U, (uint8_t)59U, (uint8_t)10U, (uint8_t)103U,
    (uint8_t)207U, (uint8_t)90U, (uint8_t)165U, (uint8_t)223U, (uint8_t)135U, (uint8_t)15U,
    (uint8_t)90U, (uint8_t)170U, (uint8_t)97U, (uint8_t)55U, (uint8_t)173U, (uint8_t)161U,
    (uint8_t)237U, (uint8_t)199U, (uint8_t)134U, (uint8_t)46U, (uint8_t)9U, (uint8_t)129U,
    (uint8_t)236U, (uint8_t)103U
  };

static uint8_t
siggen_vectors384_low65[32U] =
  {
    (uint8_t)199U, (uint8_t)134U, (uint8_t)217U, (uint8_t)66U, (uint8_t)29U, (uint8_t)103U,
    (uint8_t)183U, (uint8_t)43U, (uint8_t)146U, (uint8_t)44U, (uint8_t)243U, (uint8_t)222U,
    (uint8_t)242U, (uint8_t)162U, (uint8_t)94U, (uint8_t)235U, (uint8_t)94U, (uint8_t)115U,
    (uint8_t)243U, (uint8_t)69U, (uint8_t)67U, (uint8_t)235U, (uint8_t)80U, (uint8_t)177U,
    (uint8_t)82U, (uint8_t)231U, (uint8_t)56U, (uint8_t)169U, (uint8_t)138U, (uint8_t)251U,
    (uint8_t)12U, (uint8_t)165U
  };

static uint8_t
siggen_vectors384_low66[32U] =
  {
    (uint8_t)103U, (uint8_t)150U, (uint8_t)39U, (uint8_t)30U, (uint8_t)121U, (uint8_t)226U,
    (uint8_t)73U, (uint8_t)111U, (uint8_t)158U, (uint8_t)116U, (uint8_t)177U, (uint8_t)38U,
    (uint8_t)177U, (uint8_t)18U, (uint8_t)58U, (uint8_t)61U, (uint8_t)6U, (uint8_t)125U,
    (uint8_t)229U, (uint8_t)107U, (uint8_t)86U, (uint8_t)5U, (uint8_t)214U, (uint8_t)245U,
    (uint8_t)28U, (uint8_t)143U, (uint8_t)110U, (uint8_t)29U, (uint8_t)91U, (uint8_t)185U,
    (uint8_t)58U, (uint8_t)186U
  };

static uint8_t
siggen_vectors384_low67[32U] =
  {
    (uint8_t)137U, (uint8_t)230U, (uint8_t)144U, (uint8_t)215U, (uint8_t)138U, (uint8_t)94U,
    (uint8_t)13U, (uint8_t)43U, (uint8_t)140U, (uint8_t)233U, (uint8_t)247U, (uint8_t)252U,
    (uint8_t)191U, (uint8_t)52U, (uint8_t)226U, (uint8_t)96U, (uint8_t)95U, (uint8_t)217U,
    (uint8_t)88U, (uint8_t)71U, (uint8_t)96U, (uint8_t)250U, (uint8_t)119U, (uint8_t)41U,
    (uint8_t)4U, (uint8_t)51U, (uint8_t)151U, (uint8_t)97U, (uint8_t)45U, (uint8_t)210U,
    (uint8_t)31U, (uint8_t)148U
  };

static uint8_t
siggen_vectors384_low68[32U] =
  {
    (uint8_t)7U, (uint8_t)229U, (uint8_t)5U, (uint8_t)76U, (uint8_t)56U, (uint8_t)72U, (uint8_t)57U,
    (uint8_t)88U, (uint8_t)70U, (uint8_t)36U, (uint8_t)232U, (uint8_t)215U, (uint8_t)48U,
    (uint8_t)69U, (uint8_t)77U, (uint8_t)194U, (uint8_t)126U, (uint8_t)103U, (uint8_t)60U,
    (uint8_t)74U, (uint8_t)144U, (uint8_t)203U, (uint8_t)241U, (uint8_t)41U, (uint8_t)216U,
    (uint8_t)139U, (uint8_t)145U, (uint8_t)37U, (uint8_t)3U, (uint8_t)65U, (uint8_t)133U,
    (uint8_t)77U
  };

static uint8_t
siggen_vectors384_low69[32U] =
  {
    (uint8_t)247U, (uint8_t)230U, (uint8_t)101U, (uint8_t)184U, (uint8_t)134U, (uint8_t)20U,
    (uint8_t)208U, (uint8_t)197U, (uint8_t)203U, (uint8_t)179U, (uint8_t)0U, (uint8_t)124U,
    (uint8_t)175U, (uint8_t)231U, (uint8_t)19U, (uint8_t)118U, (uint8_t)61U, (uint8_t)129U,
    (uint8_t)131U, (uint8_t)21U, (uint8_t)37U, (uint8_t)151U, (uint8_t)31U, (uint8_t)23U,
    (uint8_t)71U, (uint8_t)217U, (uint8_t)46U, (uint8_t)77U, (uint8_t)28U, (uint8_t)162U,
    (uint8_t)99U, (uint8_t)167U
  };

static uint8_t
siggen_vectors384_low70[128U] =
  {
    (uint8_t)163U, (uint8_t)104U, (uint8_t)61U, (uint8_t)18U, (uint8_t)8U, (uint8_t)7U,
    (uint8_t)240U, (uint8_t)160U, (uint8_t)48U, (uint8_t)254U, (uint8_t)237U, (uint8_t)103U,
    (uint8_t)151U, (uint8_t)133U, (uint8_t)50U, (uint8_t)102U, (uint8_t)152U, (uint8_t)195U,
    (uint8_t)112U, (uint8_t)47U, (uint8_t)25U, (uint8_t)131U, (uint8_t)234U, (uint8_t)186U,
    (uint8_t)27U, (uint8_t)112U, (uint8_t)221U, (uint8_t)250U, (uint8_t)127U, (uint8_t)11U,
    (uint8_t)49U, (uint8_t)136U, (uint8_t)6U, (uint8_t)11U, (uint8_t)132U, (uint8_t)94U,
    (uint8_t)43U, (uint8_t)103U, (uint8_t)237U, (uint8_t)87U, (uint8_t)238U, (uint8_t)104U,
    (uint8_t)8U, (uint8_t)119U, (uint8_t)70U, (uint8_t)113U, (uint8_t)4U, (uint8_t)80U,
    (uint8_t)247U, (uint8_t)66U, (uint8_t)124U, (uint8_t)179U, (uint8_t)70U, (uint8_t)85U,
    (uint8_t)215U, (uint8_t)25U, (uint8_t)192U, (uint8_t)172U, (uint8_t)188U, (uint8_t)9U,
    (uint8_t)172U, (uint8_t)105U, (uint8_t)106U, (uint8_t)219U, (uint8_t)75U, (uint8_t)34U,
    (uint8_t)171U, (uint8_t)161U, (uint8_t)185U, (uint8_t)50U, (uint8_t)43U, (uint8_t)113U,
    (uint8_t)17U, (uint8_t)7U, (uint8_t)110U, (uint8_t)103U, (uint8_t)5U, (uint8_t)58U,
    (uint8_t)85U, (uint8_t)246U, (uint8_t)43U, (uint8_t)80U, (uint8_t)26U, (uint8_t)75U,
    (uint8_t)202U, (uint8_t)10U, (uint8_t)217U, (uint8_t)213U, (uint8_t)10U, (uint8_t)134U,
    (uint8_t)143U, (uint8_t)81U, (uint8_t)174U, (uint8_t)235U, (uint8_t)78U, (uint8_t)242U,
    (uint8_t)120U, (uint8_t)35U, (uint8_t)35U, (uint8_t)111U, (uint8_t)82U, (uint8_t)103U,
    (uint8_t)232U, (uint8_t)218U, (uint8_t)131U, (uint8_t)225U, (uint8_t)67U, (uint8_t)4U,
    (uint8_t)116U, (uint8_t)34U, (uint8_t)206U, (uint8_t)20U, (uint8_t)13U, (uint8_t)102U,
    (uint8_t)224U, (uint8_t)94U, (uint8_t)68U, (uint8_t)220U, (uint8_t)132U, (uint8_t)251U,
    (uint8_t)58U, (uint8_t)69U, (uint8_t)6U, (uint8_t)178U, (uint8_t)165U, (uint8_t)215U,
    (uint8_t)202U, (uint8_t)168U
  };

static uint8_t
siggen_vectors384_low71[32U] =
  {
    (uint8_t)115U, (uint8_t)24U, (uint8_t)138U, (uint8_t)146U, (uint8_t)59U, (uint8_t)192U,
    (uint8_t)178U, (uint8_t)137U, (uint8_t)232U, (uint8_t)28U, (uint8_t)61U, (uint8_t)180U,
    (uint8_t)141U, (uint8_t)130U, (uint8_t)105U, (uint8_t)23U, (uint8_t)145U, (uint8_t)15U,
    (uint8_t)27U, (uint8_t)149U, (uint8_t)119U, (uint8_t)0U, (uint8_t)248U, (uint8_t)146U,
    (uint8_t)84U, (uint8_t)37U, (uint8_t)193U, (uint8_t)251U, (uint8_t)39U, (uint8_t)202U,
    (uint8_t)186U, (uint8_t)185U
  };

static uint8_t
siggen_vectors384_low72[32U] =
  {
    (uint8_t)134U, (uint8_t)102U, (uint8_t)44U, (uint8_t)1U, (uint8_t)74U, (uint8_t)182U,
    (uint8_t)102U, (uint8_t)238U, (uint8_t)119U, (uint8_t)7U, (uint8_t)35U, (uint8_t)190U,
    (uint8_t)141U, (uint8_t)163U, (uint8_t)140U, (uint8_t)92U, (uint8_t)210U, (uint8_t)153U,
    (uint8_t)239U, (uint8_t)198U, (uint8_t)72U, (uint8_t)15U, (uint8_t)198U, (uint8_t)248U,
    (uint8_t)195U, (uint8_t)96U, (uint8_t)52U, (uint8_t)56U, (uint8_t)250U, (uint8_t)131U,
    (uint8_t)151U, (uint8_t)185U
  };

static uint8_t
siggen_vectors384_low73[32U] =
  {
    (uint8_t)242U, (uint8_t)107U, (uint8_t)51U, (uint8_t)7U, (uint8_t)166U, (uint8_t)80U,
    (uint8_t)195U, (uint8_t)134U, (uint8_t)63U, (uint8_t)170U, (uint8_t)165U, (uint8_t)246U,
    (uint8_t)66U, (uint8_t)243U, (uint8_t)186U, (uint8_t)19U, (uint8_t)132U, (uint8_t)195U,
    (uint8_t)211U, (uint8_t)160U, (uint8_t)46U, (uint8_t)221U, (uint8_t)61U, (uint8_t)72U,
    (uint8_t)198U, (uint8_t)87U, (uint8_t)194U, (uint8_t)105U, (uint8_t)96U, (uint8_t)156U,
    (uint8_t)195U, (uint8_t)252U
  };

static uint8_t
siggen_vectors384_low74[32U] =
  {
    (uint8_t)236U, (uint8_t)144U, (uint8_t)88U, (uint8_t)74U, (uint8_t)179U, (uint8_t)179U,
    (uint8_t)131U, (uint8_t)181U, (uint8_t)144U, (uint8_t)98U, (uint8_t)111U, (uint8_t)54U,
    (uint8_t)237U, (uint8_t)79U, (uint8_t)81U, (uint8_t)16U, (uint8_t)228U, (uint8_t)152U,
    (uint8_t)136U, (uint8_t)174U, (uint8_t)199U, (uint8_t)174U, (uint8_t)122U, (uint8_t)156U,
    (uint8_t)94U, (uint8_t)166U, (uint8_t)45U, (uint8_t)210U, (uint8_t)220U, (uint8_t)55U,
    (uint8_t)134U, (uint8_t)102U
  };

static uint8_t
siggen_vectors384_low75[32U] =
  {
    (uint8_t)19U, (uint8_t)233U, (uint8_t)173U, (uint8_t)89U, (uint8_t)17U, (uint8_t)47U,
    (uint8_t)222U, (uint8_t)58U, (uint8_t)244U, (uint8_t)22U, (uint8_t)62U, (uint8_t)181U,
    (uint8_t)194U, (uint8_t)64U, (uint8_t)11U, (uint8_t)94U, (uint8_t)154U, (uint8_t)96U,
    (uint8_t)37U, (uint8_t)118U, (uint8_t)213U, (uint8_t)134U, (uint8_t)154U, (uint8_t)193U,
    (uint8_t)197U, (uint8_t)105U, (uint8_t)7U, (uint8_t)95U, (uint8_t)8U, (uint8_t)201U,
    (uint8_t)15U, (uint8_t)246U
  };

static uint8_t
siggen_vectors384_low76[32U] =
  {
    (uint8_t)112U, (uint8_t)138U, (uint8_t)198U, (uint8_t)95U, (uint8_t)242U, (uint8_t)176U,
    (uint8_t)186U, (uint8_t)172U, (uint8_t)204U, (uint8_t)109U, (uint8_t)217U, (uint8_t)84U,
    (uint8_t)226U, (uint8_t)169U, (uint8_t)61U, (uint8_t)244U, (uint8_t)96U, (uint8_t)22U,
    (uint8_t)189U, (uint8_t)4U, (uint8_t)69U, (uint8_t)118U, (uint8_t)54U, (uint8_t)222U,
    (uint8_t)6U, (uint8_t)121U, (uint8_t)143U, (uint8_t)204U, (uint8_t)23U, (uint8_t)240U,
    (uint8_t)43U, (uint8_t)229U
  };

static uint8_t
siggen_vectors384_low77[128U] =
  {
    (uint8_t)177U, (uint8_t)223U, (uint8_t)128U, (uint8_t)81U, (uint8_t)178U, (uint8_t)19U,
    (uint8_t)252U, (uint8_t)95U, (uint8_t)99U, (uint8_t)101U, (uint8_t)55U, (uint8_t)227U,
    (uint8_t)126U, (uint8_t)33U, (uint8_t)46U, (uint8_t)178U, (uint8_t)11U, (uint8_t)36U,
    (uint8_t)35U, (uint8_t)230U, (uint8_t)70U, (uint8_t)122U, (uint8_t)156U, (uint8_t)112U,
    (uint8_t)129U, (uint8_t)51U, (uint8_t)106U, (uint8_t)135U, (uint8_t)14U, (uint8_t)99U,
    (uint8_t)115U, (uint8_t)252U, (uint8_t)131U, (uint8_t)88U, (uint8_t)153U, (uint8_t)213U,
    (uint8_t)158U, (uint8_t)84U, (uint8_t)108U, (uint8_t)10U, (uint8_t)198U, (uint8_t)104U,
    (uint8_t)204U, (uint8_t)129U, (uint8_t)206U, (uint8_t)73U, (uint8_t)33U, (uint8_t)232U,
    (uint8_t)143U, (uint8_t)66U, (uint8_t)230U, (uint8_t)218U, (uint8_t)42U, (uint8_t)16U,
    (uint8_t)154U, (uint8_t)3U, (uint8_t)180U, (uint8_t)244U, (uint8_t)232U, (uint8_t)25U,
    (uint8_t)161U, (uint8_t)124U, (uint8_t)149U, (uint8_t)91U, (uint8_t)141U, (uint8_t)9U,
    (uint8_t)158U, (uint8_t)198U, (uint8_t)178U, (uint8_t)130U, (uint8_t)251U, (uint8_t)73U,
    (uint8_t)82U, (uint8_t)88U, (uint8_t)220U, (uint8_t)161U, (uint8_t)62U, (uint8_t)199U,
    (uint8_t)121U, (uint8_t)196U, (uint8_t)89U, (uint8_t)218U, (uint8_t)144U, (uint8_t)148U,
    (uint8_t)117U, (uint8_t)81U, (uint8_t)154U, (uint8_t)52U, (uint8_t)119U, (uint8_t)34U,
    (uint8_t)60U, (uint8_t)6U, (uint8_t)185U, (uint8_t)154U, (uint8_t)251U, (uint8_t)215U,
    (uint8_t)127U, (uint8_t)153U, (uint8_t)34U, (uint8_t)231U, (uint8_t)203U, (uint8_t)239U,
    (uint8_t)132U, (uint8_t)75U, (uint8_t)147U, (uint8_t)243U, (uint8_t)206U, (uint8_t)95U,
    (uint8_t)80U, (uint8_t)219U, (uint8_t)129U, (uint8_t)107U, (uint8_t)46U, (uint8_t)13U,
    (uint8_t)139U, (uint8_t)21U, (uint8_t)117U, (uint8_t)210U, (uint8_t)225U, (uint8_t)122U,
    (uint8_t)107U, (uint8_t)141U, (uint8_t)185U, (uint8_t)17U, (uint8_t)29U, (uint8_t)109U,
    (uint8_t)165U, (uint8_t)120U
  };

static uint8_t
siggen_vectors384_low78[32U] =
  {
    (uint8_t)246U, (uint8_t)55U, (uint8_t)213U, (uint8_t)87U, (uint8_t)99U, (uint8_t)254U,
    (uint8_t)129U, (uint8_t)149U, (uint8_t)65U, (uint8_t)88U, (uint8_t)142U, (uint8_t)12U,
    (uint8_t)96U, (uint8_t)63U, (uint8_t)40U, (uint8_t)138U, (uint8_t)105U, (uint8_t)60U,
    (uint8_t)198U, (uint8_t)104U, (uint8_t)35U, (uint8_t)198U, (uint8_t)187U, (uint8_t)123U,
    (uint8_t)142U, (uint8_t)0U, (uint8_t)59U, (uint8_t)211U, (uint8_t)133U, (uint8_t)128U,
    (uint8_t)235U, (uint8_t)206U
  };

static uint8_t
siggen_vectors384_low79[32U] =
  {
    (uint8_t)116U, (uint8_t)164U, (uint8_t)98U, (uint8_t)12U, (uint8_t)87U, (uint8_t)134U,
    (uint8_t)1U, (uint8_t)71U, (uint8_t)95U, (uint8_t)193U, (uint8_t)105U, (uint8_t)169U,
    (uint8_t)184U, (uint8_t)75U, (uint8_t)230U, (uint8_t)19U, (uint8_t)180U, (uint8_t)161U,
    (uint8_t)108U, (uint8_t)182U, (uint8_t)172U, (uint8_t)171U, (uint8_t)143U, (uint8_t)217U,
    (uint8_t)136U, (uint8_t)72U, (uint8_t)166U, (uint8_t)236U, (uint8_t)159U, (uint8_t)189U,
    (uint8_t)19U, (uint8_t)61U
  };

static uint8_t
siggen_vectors384_low80[32U] =
  {
    (uint8_t)66U, (uint8_t)185U, (uint8_t)227U, (uint8_t)93U, (uint8_t)52U, (uint8_t)124U,
    (uint8_t)16U, (uint8_t)126U, (uint8_t)99U, (uint8_t)189U, (uint8_t)85U, (uint8_t)245U,
    (uint8_t)37U, (uint8_t)249U, (uint8_t)21U, (uint8_t)188U, (uint8_t)241U, (uint8_t)227U,
    (uint8_t)210U, (uint8_t)184U, (uint8_t)29U, (uint8_t)0U, (uint8_t)45U, (uint8_t)60U,
    (uint8_t)57U, (uint8_t)172U, (uint8_t)241U, (uint8_t)15U, (uint8_t)195U, (uint8_t)6U,
    (uint8_t)69U, (uint8_t)161U
  };

static uint8_t
siggen_vectors384_low81[32U] =
  {
    (uint8_t)77U, (uint8_t)87U, (uint8_t)143U, (uint8_t)80U, (uint8_t)153U, (uint8_t)99U,
    (uint8_t)98U, (uint8_t)52U, (uint8_t)217U, (uint8_t)193U, (uint8_t)213U, (uint8_t)102U,
    (uint8_t)241U, (uint8_t)33U, (uint8_t)93U, (uint8_t)93U, (uint8_t)136U, (uint8_t)122U,
    (uint8_t)229U, (uint8_t)212U, (uint8_t)112U, (uint8_t)34U, (uint8_t)190U, (uint8_t)23U,
    (uint8_t)219U, (uint8_t)243U, (uint8_t)42U, (uint8_t)17U, (uint8_t)160U, (uint8_t)63U,
    (uint8_t)5U, (uint8_t)59U
  };

static uint8_t
siggen_vectors384_low82[32U] =
  {
    (uint8_t)17U, (uint8_t)58U, (uint8_t)147U, (uint8_t)62U, (uint8_t)188U, (uint8_t)77U,
    (uint8_t)148U, (uint8_t)206U, (uint8_t)28U, (uint8_t)239U, (uint8_t)120U, (uint8_t)30U,
    (uint8_t)72U, (uint8_t)41U, (uint8_t)223U, (uint8_t)12U, (uint8_t)73U, (uint8_t)59U,
    (uint8_t)6U, (uint8_t)133U, (uint8_t)211U, (uint8_t)159U, (uint8_t)178U, (uint8_t)4U,
    (uint8_t)140U, (uint8_t)224U, (uint8_t)27U, (uint8_t)33U, (uint8_t)195U, (uint8_t)152U,
    (uint8_t)219U, (uint8_t)186U
  };

static uint8_t
siggen_vectors384_low83[32U] =
  {
    (uint8_t)48U, (uint8_t)5U, (uint8_t)189U, (uint8_t)78U, (uint8_t)198U, (uint8_t)61U,
    (uint8_t)189U, (uint8_t)4U, (uint8_t)206U, (uint8_t)159U, (uint8_t)240U, (uint8_t)198U,
    (uint8_t)36U, (uint8_t)106U, (uint8_t)214U, (uint8_t)93U, (uint8_t)39U, (uint8_t)252U,
    (uint8_t)246U, (uint8_t)46U, (uint8_t)219U, (uint8_t)43U, (uint8_t)126U, (uint8_t)70U,
    (uint8_t)21U, (uint8_t)137U, (uint8_t)249U, (uint8_t)240U, (uint8_t)231U, (uint8_t)68U,
    (uint8_t)111U, (uint8_t)253U
  };

static uint8_t
siggen_vectors384_low84[128U] =
  {
    (uint8_t)11U, (uint8_t)145U, (uint8_t)142U, (uint8_t)222U, (uint8_t)152U, (uint8_t)91U,
    (uint8_t)92U, (uint8_t)73U, (uint8_t)23U, (uint8_t)151U, (uint8_t)208U, (uint8_t)168U,
    (uint8_t)20U, (uint8_t)70U, (uint8_t)178U, (uint8_t)147U, (uint8_t)59U, (uint8_t)227U,
    (uint8_t)18U, (uint8_t)244U, (uint8_t)25U, (uint8_t)178U, (uint8_t)18U, (uint8_t)227U,
    (uint8_t)170U, (uint8_t)233U, (uint8_t)186U, (uint8_t)89U, (uint8_t)20U, (uint8_t)192U,
    (uint8_t)10U, (uint8_t)244U, (uint8_t)49U, (uint8_t)116U, (uint8_t)122U, (uint8_t)157U,
    (uint8_t)40U, (uint8_t)122U, (uint8_t)124U, (uint8_t)119U, (uint8_t)97U, (uint8_t)233U,
    (uint8_t)188U, (uint8_t)188U, (uint8_t)138U, (uint8_t)18U, (uint8_t)170U, (uint8_t)249U,
    (uint8_t)212U, (uint8_t)167U, (uint8_t)109U, (uint8_t)19U, (uint8_t)218U, (uint8_t)213U,
    (uint8_t)159U, (uint8_t)199U, (uint8_t)66U, (uint8_t)248U, (uint8_t)242U, (uint8_t)24U,
    (uint8_t)239U, (uint8_t)102U, (uint8_t)235U, (uint8_t)103U, (uint8_t)3U, (uint8_t)82U,
    (uint8_t)32U, (uint8_t)160U, (uint8_t)122U, (uint8_t)204U, (uint8_t)26U, (uint8_t)53U,
    (uint8_t)124U, (uint8_t)91U, (uint8_t)86U, (uint8_t)46U, (uint8_t)203U, (uint8_t)107U,
    (uint8_t)137U, (uint8_t)92U, (uint8_t)247U, (uint8_t)37U, (uint8_t)196U, (uint8_t)35U,
    (uint8_t)4U, (uint8_t)18U, (uint8_t)254U, (uint8_t)250U, (uint8_t)199U, (uint8_t)32U,
    (uint8_t)151U, (uint8_t)242U, (uint8_t)194U, (uint8_t)184U, (uint8_t)41U, (uint8_t)237U,
    (uint8_t)88U, (uint8_t)116U, (uint8_t)45U, (uint8_t)124U, (uint8_t)50U, (uint8_t)124U,
    (uint8_t)173U, (uint8_t)15U, (uint8_t)16U, (uint8_t)88U, (uint8_t)223U, (uint8_t)27U,
    (uint8_t)221U, (uint8_t)212U, (uint8_t)174U, (uint8_t)156U, (uint8_t)109U, (uint8_t)42U,
    (uint8_t)186U, (uint8_t)37U, (uint8_t)72U, (uint8_t)4U, (uint8_t)36U, (uint8_t)48U,
    (uint8_t)134U, (uint8_t)132U, (uint8_t)206U, (uint8_t)205U, (uint8_t)101U, (uint8_t)23U,
    (uint8_t)205U, (uint8_t)216U
  };

static uint8_t
siggen_vectors384_low85[32U] =
  {
    (uint8_t)46U, (uint8_t)53U, (uint8_t)125U, (uint8_t)81U, (uint8_t)81U, (uint8_t)127U,
    (uint8_t)249U, (uint8_t)59U, (uint8_t)130U, (uint8_t)31U, (uint8_t)137U, (uint8_t)89U,
    (uint8_t)50U, (uint8_t)253U, (uint8_t)221U, (uint8_t)237U, (uint8_t)131U, (uint8_t)71U,
    (uint8_t)243U, (uint8_t)37U, (uint8_t)150U, (uint8_t)184U, (uint8_t)18U, (uint8_t)48U,
    (uint8_t)142U, (uint8_t)111U, (uint8_t)27U, (uint8_t)175U, (uint8_t)125U, (uint8_t)216U,
    (uint8_t)164U, (uint8_t)127U
  };

static uint8_t
siggen_vectors384_low86[32U] =
  {
    (uint8_t)126U, (uint8_t)64U, (uint8_t)120U, (uint8_t)161U, (uint8_t)213U, (uint8_t)12U,
    (uint8_t)102U, (uint8_t)159U, (uint8_t)178U, (uint8_t)153U, (uint8_t)109U, (uint8_t)217U,
    (uint8_t)186U, (uint8_t)203U, (uint8_t)12U, (uint8_t)58U, (uint8_t)199U, (uint8_t)237U,
    (uint8_t)228U, (uint8_t)245U, (uint8_t)143U, (uint8_t)160U, (uint8_t)250U, (uint8_t)18U,
    (uint8_t)34U, (uint8_t)231U, (uint8_t)141U, (uint8_t)191U, (uint8_t)93U, (uint8_t)31U,
    (uint8_t)65U, (uint8_t)134U
  };

static uint8_t
siggen_vectors384_low87[32U] =
  {
    (uint8_t)0U, (uint8_t)20U, (uint8_t)228U, (uint8_t)110U, (uint8_t)144U, (uint8_t)204U,
    (uint8_t)23U, (uint8_t)31U, (uint8_t)187U, (uint8_t)131U, (uint8_t)234U, (uint8_t)52U,
    (uint8_t)198U, (uint8_t)183U, (uint8_t)130U, (uint8_t)2U, (uint8_t)234U, (uint8_t)129U,
    (uint8_t)55U, (uint8_t)167U, (uint8_t)217U, (uint8_t)38U, (uint8_t)240U, (uint8_t)22U,
    (uint8_t)145U, (uint8_t)71U, (uint8_t)237U, (uint8_t)90U, (uint8_t)227U, (uint8_t)214U,
    (uint8_t)89U, (uint8_t)111U
  };

static uint8_t
siggen_vectors384_low88[32U] =
  {
    (uint8_t)190U, (uint8_t)82U, (uint8_t)43U, (uint8_t)9U, (uint8_t)64U, (uint8_t)185U,
    (uint8_t)164U, (uint8_t)13U, (uint8_t)132U, (uint8_t)191U, (uint8_t)121U, (uint8_t)15U,
    (uint8_t)230U, (uint8_t)171U, (uint8_t)220U, (uint8_t)37U, (uint8_t)40U, (uint8_t)119U,
    (uint8_t)230U, (uint8_t)113U, (uint8_t)242U, (uint8_t)239U, (uint8_t)166U, (uint8_t)58U,
    (uint8_t)51U, (uint8_t)166U, (uint8_t)90U, (uint8_t)81U, (uint8_t)47U, (uint8_t)194U,
    (uint8_t)170U, (uint8_t)92U
  };

static uint8_t
siggen_vectors384_low89[32U] =
  {
    (uint8_t)162U, (uint8_t)107U, (uint8_t)154U, (uint8_t)215U, (uint8_t)117U, (uint8_t)172U,
    (uint8_t)55U, (uint8_t)255U, (uint8_t)76U, (uint8_t)127U, (uint8_t)4U, (uint8_t)44U,
    (uint8_t)220U, (uint8_t)72U, (uint8_t)114U, (uint8_t)197U, (uint8_t)228U, (uint8_t)229U,
    (uint8_t)232U, (uint8_t)0U, (uint8_t)72U, (uint8_t)95U, (uint8_t)72U, (uint8_t)141U,
    (uint8_t)223U, (uint8_t)170U, (uint8_t)237U, (uint8_t)55U, (uint8_t)159U, (uint8_t)70U,
    (uint8_t)128U, (uint8_t)144U
  };

static uint8_t
siggen_vectors384_low90[32U] =
  {
    (uint8_t)248U, (uint8_t)142U, (uint8_t)174U, (uint8_t)32U, (uint8_t)25U, (uint8_t)190U,
    (uint8_t)187U, (uint8_t)186U, (uint8_t)98U, (uint8_t)180U, (uint8_t)83U, (uint8_t)184U,
    (uint8_t)238U, (uint8_t)52U, (uint8_t)114U, (uint8_t)202U, (uint8_t)92U, (uint8_t)103U,
    (uint8_t)194U, (uint8_t)103U, (uint8_t)150U, (uint8_t)76U, (uint8_t)255U, (uint8_t)224U,
    (uint8_t)207U, (uint8_t)45U, (uint8_t)41U, (uint8_t)51U, (uint8_t)193U, (uint8_t)114U,
    (uint8_t)61U, (uint8_t)255U
  };

static uint8_t
siggen_vectors384_low91[128U] =
  {
    (uint8_t)15U, (uint8_t)171U, (uint8_t)38U, (uint8_t)253U, (uint8_t)225U, (uint8_t)164U,
    (uint8_t)70U, (uint8_t)124U, (uint8_t)169U, (uint8_t)48U, (uint8_t)219U, (uint8_t)229U,
    (uint8_t)19U, (uint8_t)204U, (uint8_t)195U, (uint8_t)69U, (uint8_t)43U, (uint8_t)112U,
    (uint8_t)49U, (uint8_t)60U, (uint8_t)204U, (uint8_t)222U, (uint8_t)41U, (uint8_t)148U,
    (uint8_t)238U, (uint8_t)173U, (uint8_t)47U, (uint8_t)222U, (uint8_t)133U, (uint8_t)200U,
    (uint8_t)218U, (uint8_t)29U, (uint8_t)184U, (uint8_t)77U, (uint8_t)125U, (uint8_t)6U,
    (uint8_t)160U, (uint8_t)36U, (uint8_t)201U, (uint8_t)232U, (uint8_t)134U, (uint8_t)41U,
    (uint8_t)213U, (uint8_t)52U, (uint8_t)66U, (uint8_t)36U, (uint8_t)164U, (uint8_t)234U,
    (uint8_t)224U, (uint8_t)27U, (uint8_t)33U, (uint8_t)162U, (uint8_t)102U, (uint8_t)93U,
    (uint8_t)95U, (uint8_t)127U, (uint8_t)54U, (uint8_t)213U, (uint8_t)82U, (uint8_t)75U,
    (uint8_t)245U, (uint8_t)54U, (uint8_t)125U, (uint8_t)127U, (uint8_t)139U, (uint8_t)106U,
    (uint8_t)113U, (uint8_t)234U, (uint8_t)5U, (uint8_t)212U, (uint8_t)19U, (uint8_t)212U,
    (uint8_t)175U, (uint8_t)222U, (uint8_t)51U, (uint8_t)119U, (uint8_t)127U, (uint8_t)10U,
    (uint8_t)59U, (uint8_t)228U, (uint8_t)156U, (uint8_t)158U, (uint8_t)106U, (uint8_t)162U,
    (uint8_t)158U, (uint8_t)164U, (uint8_t)71U, (uint8_t)116U, (uint8_t)106U, (uint8_t)158U,
    (uint8_t)119U, (uint8_t)206U, (uint8_t)39U, (uint8_t)35U, (uint8_t)42U, (uint8_t)85U,
    (uint8_t)11U, (uint8_t)49U, (uint8_t)221U, (uint8_t)78U, (uint8_t)124U, (uint8_t)155U,
    (uint8_t)200U, (uint8_t)145U, (uint8_t)52U, (uint8_t)133U, (uint8_t)242U, (uint8_t)220U,
    (uint8_t)131U, (uint8_t)165U, (uint8_t)98U, (uint8_t)152U, (uint8_t)5U, (uint8_t)28U,
    (uint8_t)146U, (uint8_t)70U, (uint8_t)31U, (uint8_t)212U, (uint8_t)107U, (uint8_t)20U,
    (uint8_t)204U, (uint8_t)137U, (uint8_t)92U, (uint8_t)48U, (uint8_t)10U, (uint8_t)79U,
    (uint8_t)184U, (uint8_t)116U
  };

static uint8_t
siggen_vectors384_low92[32U] =
  {
    (uint8_t)119U, (uint8_t)214U, (uint8_t)12U, (uint8_t)172U, (uint8_t)187U, (uint8_t)172U,
    (uint8_t)134U, (uint8_t)171U, (uint8_t)137U, (uint8_t)0U, (uint8_t)148U, (uint8_t)3U,
    (uint8_t)201U, (uint8_t)114U, (uint8_t)137U, (uint8_t)181U, (uint8_t)144U, (uint8_t)4U,
    (uint8_t)102U, (uint8_t)133U, (uint8_t)104U, (uint8_t)135U, (uint8_t)211U, (uint8_t)230U,
    (uint8_t)17U, (uint8_t)42U, (uint8_t)244U, (uint8_t)39U, (uint8_t)247U, (uint8_t)240U,
    (uint8_t)245U, (uint8_t)11U
  };

static uint8_t
siggen_vectors384_low93[32U] =
  {
    (uint8_t)166U, (uint8_t)32U, (uint8_t)50U, (uint8_t)223U, (uint8_t)219U, (uint8_t)135U,
    (uint8_t)226U, (uint8_t)94U, (uint8_t)208U, (uint8_t)199U, (uint8_t)12U, (uint8_t)173U,
    (uint8_t)32U, (uint8_t)217U, (uint8_t)39U, (uint8_t)199U, (uint8_t)239U, (uint8_t)254U,
    (uint8_t)178U, (uint8_t)99U, (uint8_t)142U, (uint8_t)108U, (uint8_t)136U, (uint8_t)221U,
    (uint8_t)214U, (uint8_t)112U, (uint8_t)247U, (uint8_t)77U, (uint8_t)241U, (uint8_t)96U,
    (uint8_t)144U, (uint8_t)229U
  };

static uint8_t
siggen_vectors384_low94[32U] =
  {
    (uint8_t)68U, (uint8_t)197U, (uint8_t)238U, (uint8_t)44U, (uint8_t)247U, (uint8_t)64U,
    (uint8_t)222U, (uint8_t)212U, (uint8_t)104U, (uint8_t)245U, (uint8_t)210U, (uint8_t)239U,
    (uint8_t)225U, (uint8_t)61U, (uint8_t)170U, (uint8_t)124U, (uint8_t)82U, (uint8_t)52U,
    (uint8_t)100U, (uint8_t)90U, (uint8_t)55U, (uint8_t)192U, (uint8_t)115U, (uint8_t)175U,
    (uint8_t)53U, (uint8_t)51U, (uint8_t)13U, (uint8_t)3U, (uint8_t)164U, (uint8_t)254U,
    (uint8_t)217U, (uint8_t)118U
  };

static uint8_t
siggen_vectors384_low95[32U] =
  {
    (uint8_t)6U, (uint8_t)193U, (uint8_t)230U, (uint8_t)146U, (uint8_t)176U, (uint8_t)69U,
    (uint8_t)244U, (uint8_t)37U, (uint8_t)162U, (uint8_t)19U, (uint8_t)71U, (uint8_t)236U,
    (uint8_t)247U, (uint8_t)40U, (uint8_t)51U, (uint8_t)208U, (uint8_t)36U, (uint8_t)41U,
    (uint8_t)6U, (uint8_t)199U, (uint8_t)193U, (uint8_t)9U, (uint8_t)79U, (uint8_t)128U,
    (uint8_t)85U, (uint8_t)102U, (uint8_t)205U, (uint8_t)203U, (uint8_t)18U, (uint8_t)86U,
    (uint8_t)227U, (uint8_t)148U
  };

static uint8_t
siggen_vectors384_low96[32U] =
  {
    (uint8_t)235U, (uint8_t)23U, (uint8_t)59U, (uint8_t)81U, (uint8_t)251U, (uint8_t)10U,
    (uint8_t)236U, (uint8_t)49U, (uint8_t)137U, (uint8_t)80U, (uint8_t)208U, (uint8_t)151U,
    (uint8_t)231U, (uint8_t)253U, (uint8_t)165U, (uint8_t)195U, (uint8_t)78U, (uint8_t)82U,
    (uint8_t)149U, (uint8_t)25U, (uint8_t)99U, (uint8_t)28U, (uint8_t)62U, (uint8_t)44U,
    (uint8_t)155U, (uint8_t)69U, (uint8_t)80U, (uint8_t)185U, (uint8_t)3U, (uint8_t)218U,
    (uint8_t)65U, (uint8_t)125U
  };

static uint8_t
siggen_vectors384_low97[32U] =
  {
    (uint8_t)202U, (uint8_t)44U, (uint8_t)19U, (uint8_t)87U, (uint8_t)75U, (uint8_t)241U,
    (uint8_t)183U, (uint8_t)213U, (uint8_t)110U, (uint8_t)157U, (uint8_t)193U, (uint8_t)131U,
    (uint8_t)21U, (uint8_t)3U, (uint8_t)106U, (uint8_t)49U, (uint8_t)184U, (uint8_t)188U,
    (uint8_t)237U, (uint8_t)223U, (uint8_t)62U, (uint8_t)44U, (uint8_t)41U, (uint8_t)2U,
    (uint8_t)220U, (uint8_t)180U, (uint8_t)15U, (uint8_t)12U, (uint8_t)201U, (uint8_t)227U,
    (uint8_t)27U, (uint8_t)69U
  };

static uint8_t
siggen_vectors384_low98[128U] =
  {
    (uint8_t)120U, (uint8_t)67U, (uint8_t)241U, (uint8_t)87U, (uint8_t)239U, (uint8_t)133U,
    (uint8_t)102U, (uint8_t)114U, (uint8_t)42U, (uint8_t)125U, (uint8_t)105U, (uint8_t)218U,
    (uint8_t)103U, (uint8_t)222U, (uint8_t)117U, (uint8_t)153U, (uint8_t)238U, (uint8_t)101U,
    (uint8_t)203U, (uint8_t)57U, (uint8_t)117U, (uint8_t)80U, (uint8_t)143U, (uint8_t)112U,
    (uint8_t)198U, (uint8_t)18U, (uint8_t)179U, (uint8_t)40U, (uint8_t)145U, (uint8_t)144U,
    (uint8_t)227U, (uint8_t)100U, (uint8_t)20U, (uint8_t)23U, (uint8_t)129U, (uint8_t)224U,
    (uint8_t)184U, (uint8_t)50U, (uint8_t)242U, (uint8_t)217U, (uint8_t)98U, (uint8_t)113U,
    (uint8_t)34U, (uint8_t)116U, (uint8_t)47U, (uint8_t)75U, (uint8_t)88U, (uint8_t)113U,
    (uint8_t)206U, (uint8_t)234U, (uint8_t)252U, (uint8_t)208U, (uint8_t)155U, (uint8_t)165U,
    (uint8_t)236U, (uint8_t)144U, (uint8_t)202U, (uint8_t)230U, (uint8_t)188U, (uint8_t)192U,
    (uint8_t)26U, (uint8_t)227U, (uint8_t)43U, (uint8_t)80U, (uint8_t)241U, (uint8_t)63U,
    (uint8_t)99U, (uint8_t)145U, (uint8_t)141U, (uint8_t)251U, (uint8_t)81U, (uint8_t)119U,
    (uint8_t)223U, (uint8_t)151U, (uint8_t)151U, (uint8_t)198U, (uint8_t)39U, (uint8_t)59U,
    (uint8_t)146U, (uint8_t)209U, (uint8_t)3U, (uint8_t)195U, (uint8_t)247U, (uint8_t)163U,
    (uint8_t)252U, (uint8_t)32U, (uint8_t)80U, (uint8_t)210U, (uint8_t)177U, (uint8_t)150U,
    (uint8_t)204U, (uint8_t)135U, (uint8_t)44U, (uint8_t)87U, (uint8_t)183U, (uint8_t)127U,
    (uint8_t)155U, (uint8_t)219U, (uint8_t)23U, (uint8_t)130U, (uint8_t)212U, (uint8_t)25U,
    (uint8_t)84U, (uint8_t)69U, (uint8_t)252U, (uint8_t)198U, (uint8_t)35U, (uint8_t)109U,
    (uint8_t)216U, (uint8_t)189U, (uint8_t)20U, (uint8_t)200U, (uint8_t)188U, (uint8_t)188U,
    (uint8_t)130U, (uint8_t)35U, (uint8_t)166U, (uint8_t)115U, (uint8_t)159U, (uint8_t)106U,
    (uint8_t)23U, (uint8_t)201U, (uint8_t)168U, (uint8_t)97U, (uint8_t)232U, (uint8_t)200U,
    (uint8_t)33U, (uint8_t)166U
  };

static uint8_t
siggen_vectors384_low99[32U] =
  {
    (uint8_t)72U, (uint8_t)104U, (uint8_t)84U, (uint8_t)231U, (uint8_t)121U, (uint8_t)98U,
    (uint8_t)17U, (uint8_t)127U, (uint8_t)73U, (uint8_t)224U, (uint8_t)147U, (uint8_t)120U,
    (uint8_t)222U, (uint8_t)108U, (uint8_t)158U, (uint8_t)59U, (uint8_t)53U, (uint8_t)34U,
    (uint8_t)250U, (uint8_t)117U, (uint8_t)43U, (uint8_t)16U, (uint8_t)178U, (uint8_t)200U,
    (uint8_t)16U, (uint8_t)191U, (uint8_t)72U, (uint8_t)219U, (uint8_t)88U, (uint8_t)77U,
    (uint8_t)115U, (uint8_t)136U
  };

static uint8_t
siggen_vectors384_low100[32U] =
  {
    (uint8_t)118U, (uint8_t)11U, (uint8_t)86U, (uint8_t)36U, (uint8_t)189U, (uint8_t)100U,
    (uint8_t)209U, (uint8_t)156U, (uint8_t)134U, (uint8_t)110U, (uint8_t)84U, (uint8_t)204U,
    (uint8_t)215U, (uint8_t)74U, (uint8_t)215U, (uint8_t)249U, (uint8_t)136U, (uint8_t)81U,
    (uint8_t)175U, (uint8_t)219U, (uint8_t)195U, (uint8_t)221U, (uint8_t)234U, (uint8_t)227U,
    (uint8_t)236U, (uint8_t)44U, (uint8_t)82U, (uint8_t)161U, (uint8_t)53U, (uint8_t)190U,
    (uint8_t)156U, (uint8_t)250U
  };

static uint8_t
siggen_vectors384_low101[32U] =
  {
    (uint8_t)254U, (uint8_t)202U, (uint8_t)21U, (uint8_t)206U, (uint8_t)147U, (uint8_t)80U,
    (uint8_t)135U, (uint8_t)113U, (uint8_t)2U, (uint8_t)238U, (uint8_t)224U, (uint8_t)245U,
    (uint8_t)175U, (uint8_t)24U, (uint8_t)178U, (uint8_t)254U, (uint8_t)216U, (uint8_t)157U,
    (uint8_t)200U, (uint8_t)107U, (uint8_t)125U, (uint8_t)240U, (uint8_t)191U, (uint8_t)123U,
    (uint8_t)194U, (uint8_t)150U, (uint8_t)60U, (uint8_t)22U, (uint8_t)56U, (uint8_t)227U,
    (uint8_t)111U, (uint8_t)232U
  };

static uint8_t
siggen_vectors384_low102[32U] =
  {
    (uint8_t)228U, (uint8_t)247U, (uint8_t)124U, (uint8_t)100U, (uint8_t)66U, (uint8_t)236U,
    (uint8_t)162U, (uint8_t)57U, (uint8_t)176U, (uint8_t)27U, (uint8_t)2U, (uint8_t)84U,
    (uint8_t)225U, (uint8_t)26U, (uint8_t)65U, (uint8_t)130U, (uint8_t)120U, (uint8_t)45U,
    (uint8_t)150U, (uint8_t)244U, (uint8_t)138U, (uint8_t)181U, (uint8_t)33U, (uint8_t)204U,
    (uint8_t)61U, (uint8_t)29U, (uint8_t)104U, (uint8_t)223U, (uint8_t)18U, (uint8_t)181U,
    (uint8_t)164U, (uint8_t)26U
  };

static uint8_t
siggen_vectors384_low103[32U] =
  {
    (uint8_t)189U, (uint8_t)255U, (uint8_t)20U, (uint8_t)228U, (uint8_t)96U, (uint8_t)3U,
    (uint8_t)9U, (uint8_t)194U, (uint8_t)199U, (uint8_t)127U, (uint8_t)121U, (uint8_t)162U,
    (uint8_t)89U, (uint8_t)99U, (uint8_t)169U, (uint8_t)85U, (uint8_t)181U, (uint8_t)181U,
    (uint8_t)0U, (uint8_t)167U, (uint8_t)178U, (uint8_t)211U, (uint8_t)76U, (uint8_t)177U,
    (uint8_t)114U, (uint8_t)205U, (uint8_t)106U, (uint8_t)205U, (uint8_t)82U, (uint8_t)144U,
    (uint8_t)92U, (uint8_t)123U
  };

static uint8_t
siggen_vectors384_low104[32U] =
  {
    (uint8_t)176U, (uint8_t)71U, (uint8_t)156U, (uint8_t)219U, (uint8_t)61U, (uint8_t)247U,
    (uint8_t)153U, (uint8_t)35U, (uint8_t)236U, (uint8_t)54U, (uint8_t)161U, (uint8_t)4U,
    (uint8_t)161U, (uint8_t)41U, (uint8_t)83U, (uint8_t)76U, (uint8_t)93U, (uint8_t)89U,
    (uint8_t)246U, (uint8_t)34U, (uint8_t)190U, (uint8_t)125U, (uint8_t)97U, (uint8_t)58U,
    (uint8_t)160U, (uint8_t)69U, (uint8_t)48U, (uint8_t)173U, (uint8_t)37U, (uint8_t)7U,
    (uint8_t)211U, (uint8_t)162U
  };

static __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors384_low105[15U] =
  {
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low0 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low1 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low2 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low3 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low4 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low5 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low6 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low7 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low8 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low9 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low10 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low11 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low12 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low13 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low14 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low15 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low16 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low17 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low18 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low19 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low20 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low21 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low22 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low23 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low24 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low25 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low26 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low27 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low28 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low29 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low30 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low31 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low32 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low33 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low34 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low35 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low36 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low37 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low38 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low39 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low40 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low41 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low42 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low43 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low44 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low45 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low46 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low47 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low48 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low49 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low50 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low51 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low52 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low53 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low54 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low55 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low56 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low57 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low58 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low59 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low60 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low61 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low62 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low63 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low64 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low65 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low66 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low67 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low68 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low69 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low70 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low71 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low72 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low73 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low74 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low75 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low76 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low77 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low78 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low79 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low80 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low81 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low82 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low83 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low84 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low85 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low86 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low87 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low88 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low89 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low90 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low91 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low92 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low93 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low94 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low95 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low96 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low97 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors384_low98 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors384_low99 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors384_low100 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors384_low101 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors384_low102 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors384_low103 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors384_low104 }
    }
  };

static lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors384_low = { .len = (uint32_t)15U, .b = siggen_vectors384_low105 };

static uint8_t
siggen_vectors512_low0[128U] =
  {
    (uint8_t)108U, (uint8_t)133U, (uint8_t)114U, (uint8_t)182U, (uint8_t)163U, (uint8_t)164U,
    (uint8_t)169U, (uint8_t)232U, (uint8_t)224U, (uint8_t)61U, (uint8_t)190U, (uint8_t)237U,
    (uint8_t)153U, (uint8_t)51U, (uint8_t)77U, (uint8_t)65U, (uint8_t)102U, (uint8_t)27U,
    (uint8_t)138U, (uint8_t)132U, (uint8_t)23U, (uint8_t)7U, (uint8_t)79U, (uint8_t)51U,
    (uint8_t)90U, (uint8_t)177U, (uint8_t)132U, (uint8_t)95U, (uint8_t)108U, (uint8_t)200U,
    (uint8_t)82U, (uint8_t)173U, (uint8_t)184U, (uint8_t)192U, (uint8_t)29U, (uint8_t)152U,
    (uint8_t)32U, (uint8_t)252U, (uint8_t)248U, (uint8_t)225U, (uint8_t)6U, (uint8_t)153U,
    (uint8_t)204U, (uint8_t)130U, (uint8_t)122U, (uint8_t)143U, (uint8_t)189U, (uint8_t)202U,
    (uint8_t)44U, (uint8_t)189U, (uint8_t)70U, (uint8_t)204U, (uint8_t)102U, (uint8_t)228U,
    (uint8_t)230U, (uint8_t)183U, (uint8_t)186U, (uint8_t)65U, (uint8_t)236U, (uint8_t)62U,
    (uint8_t)250U, (uint8_t)115U, (uint8_t)53U, (uint8_t)135U, (uint8_t)228U, (uint8_t)163U,
    (uint8_t)14U, (uint8_t)197U, (uint8_t)82U, (uint8_t)205U, (uint8_t)141U, (uint8_t)218U,
    (uint8_t)184U, (uint8_t)22U, (uint8_t)62U, (uint8_t)20U, (uint8_t)142U, (uint8_t)80U,
    (uint8_t)244U, (uint8_t)208U, (uint8_t)144U, (uint8_t)120U, (uint8_t)40U, (uint8_t)151U,
    (uint8_t)243U, (uint8_t)221U, (uint8_t)172U, (uint8_t)132U, (uint8_t)164U, (uint8_t)30U,
    (uint8_t)31U, (uint8_t)207U, (uint8_t)232U, (uint8_t)197U, (uint8_t)107U, (uint8_t)97U,
    (uint8_t)82U, (uint8_t)192U, (uint8_t)9U, (uint8_t)123U, (uint8_t)13U, (uint8_t)99U,
    (uint8_t)75U, (uint8_t)65U, (uint8_t)1U, (uint8_t)20U, (uint8_t)113U, (uint8_t)255U,
    (uint8_t)208U, (uint8_t)4U, (uint8_t)244U, (uint8_t)62U, (uint8_t)180U, (uint8_t)170U,
    (uint8_t)252U, (uint8_t)3U, (uint8_t)129U, (uint8_t)151U, (uint8_t)236U, (uint8_t)107U,
    (uint8_t)174U, (uint8_t)43U, (uint8_t)68U, (uint8_t)112U, (uint8_t)232U, (uint8_t)105U,
    (uint8_t)189U, (uint8_t)237U
  };

static uint8_t
siggen_vectors512_low1[32U] =
  {
    (uint8_t)157U, (uint8_t)208U, (uint8_t)211U, (uint8_t)163U, (uint8_t)213U, (uint8_t)20U,
    (uint8_t)194U, (uint8_t)168U, (uint8_t)173U, (uint8_t)177U, (uint8_t)98U, (uint8_t)184U,
    (uint8_t)30U, (uint8_t)58U, (uint8_t)223U, (uint8_t)186U, (uint8_t)50U, (uint8_t)153U,
    (uint8_t)48U, (uint8_t)159U, (uint8_t)125U, (uint8_t)32U, (uint8_t)24U, (uint8_t)246U,
    (uint8_t)7U, (uint8_t)189U, (uint8_t)177U, (uint8_t)91U, (uint8_t)26U, (uint8_t)37U,
    (uint8_t)244U, (uint8_t)153U
  };

static uint8_t
siggen_vectors512_low2[32U] =
  {
    (uint8_t)107U, (uint8_t)115U, (uint8_t)141U, (uint8_t)227U, (uint8_t)57U, (uint8_t)139U,
    (uint8_t)106U, (uint8_t)197U, (uint8_t)123U, (uint8_t)149U, (uint8_t)145U, (uint8_t)249U,
    (uint8_t)215U, (uint8_t)152U, (uint8_t)93U, (uint8_t)212U, (uint8_t)243U, (uint8_t)33U,
    (uint8_t)55U, (uint8_t)173U, (uint8_t)52U, (uint8_t)96U, (uint8_t)220U, (uint8_t)248U,
    (uint8_t)151U, (uint8_t)12U, (uint8_t)19U, (uint8_t)144U, (uint8_t)203U, (uint8_t)158U,
    (uint8_t)175U, (uint8_t)141U
  };

static uint8_t
siggen_vectors512_low3[32U] =
  {
    (uint8_t)131U, (uint8_t)188U, (uint8_t)97U, (uint8_t)226U, (uint8_t)109U, (uint8_t)43U,
    (uint8_t)187U, (uint8_t)211U, (uint8_t)207U, (uint8_t)45U, (uint8_t)42U, (uint8_t)180U,
    (uint8_t)69U, (uint8_t)162U, (uint8_t)188U, (uint8_t)74U, (uint8_t)181U, (uint8_t)221U,
    (uint8_t)228U, (uint8_t)31U, (uint8_t)74U, (uint8_t)19U, (uint8_t)7U, (uint8_t)143U,
    (uint8_t)209U, (uint8_t)211U, (uint8_t)204U, (uint8_t)54U, (uint8_t)171U, (uint8_t)89U,
    (uint8_t)109U, (uint8_t)87U
  };

static uint8_t
siggen_vectors512_low4[32U] =
  {
    (uint8_t)145U, (uint8_t)6U, (uint8_t)25U, (uint8_t)33U, (uint8_t)112U, (uint8_t)204U,
    (uint8_t)179U, (uint8_t)198U, (uint8_t)70U, (uint8_t)132U, (uint8_t)212U, (uint8_t)130U,
    (uint8_t)135U, (uint8_t)187U, (uint8_t)129U, (uint8_t)187U, (uint8_t)237U, (uint8_t)81U,
    (uint8_t)180U, (uint8_t)13U, (uint8_t)80U, (uint8_t)52U, (uint8_t)98U, (uint8_t)201U,
    (uint8_t)0U, (uint8_t)229U, (uint8_t)199U, (uint8_t)170U, (uint8_t)228U, (uint8_t)62U,
    (uint8_t)56U, (uint8_t)10U
  };

static uint8_t
siggen_vectors512_low5[32U] =
  {
    (uint8_t)39U, (uint8_t)95U, (uint8_t)167U, (uint8_t)96U, (uint8_t)135U, (uint8_t)139U,
    (uint8_t)77U, (uint8_t)192U, (uint8_t)94U, (uint8_t)157U, (uint8_t)21U, (uint8_t)127U,
    (uint8_t)237U, (uint8_t)253U, (uint8_t)142U, (uint8_t)155U, (uint8_t)28U, (uint8_t)156U,
    (uint8_t)134U, (uint8_t)18U, (uint8_t)34U, (uint8_t)167U, (uint8_t)18U, (uint8_t)116U,
    (uint8_t)140U, (uint8_t)180U, (uint8_t)183U, (uint8_t)117U, (uint8_t)76U, (uint8_t)4U,
    (uint8_t)63U, (uint8_t)177U
  };

static uint8_t
siggen_vectors512_low6[32U] =
  {
    (uint8_t)105U, (uint8_t)157U, (uint8_t)144U, (uint8_t)107U, (uint8_t)184U, (uint8_t)67U,
    (uint8_t)90U, (uint8_t)5U, (uint8_t)52U, (uint8_t)90U, (uint8_t)243U, (uint8_t)179U,
    (uint8_t)126U, (uint8_t)59U, (uint8_t)53U, (uint8_t)119U, (uint8_t)134U, (uint8_t)147U,
    (uint8_t)158U, (uint8_t)148U, (uint8_t)202U, (uint8_t)174U, (uint8_t)37U, (uint8_t)120U,
    (uint8_t)82U, (uint8_t)240U, (uint8_t)80U, (uint8_t)58U, (uint8_t)219U, (uint8_t)30U,
    (uint8_t)15U, (uint8_t)126U
  };

static uint8_t
siggen_vectors512_low7[128U] =
  {
    (uint8_t)126U, (uint8_t)60U, (uint8_t)143U, (uint8_t)225U, (uint8_t)98U, (uint8_t)212U,
    (uint8_t)140U, (uint8_t)200U, (uint8_t)197U, (uint8_t)177U, (uint8_t)27U, (uint8_t)94U,
    (uint8_t)94U, (uint8_t)188U, (uint8_t)5U, (uint8_t)235U, (uint8_t)196U, (uint8_t)92U,
    (uint8_t)67U, (uint8_t)155U, (uint8_t)219U, (uint8_t)192U, (uint8_t)176U, (uint8_t)144U,
    (uint8_t)33U, (uint8_t)69U, (uint8_t)146U, (uint8_t)27U, (uint8_t)131U, (uint8_t)131U,
    (uint8_t)3U, (uint8_t)124U, (uint8_t)176U, (uint8_t)129U, (uint8_t)34U, (uint8_t)34U,
    (uint8_t)3U, (uint8_t)21U, (uint8_t)152U, (uint8_t)205U, (uint8_t)26U, (uint8_t)86U,
    (uint8_t)250U, (uint8_t)113U, (uint8_t)105U, (uint8_t)79U, (uint8_t)189U, (uint8_t)48U,
    (uint8_t)76U, (uint8_t)198U, (uint8_t)41U, (uint8_t)56U, (uint8_t)35U, (uint8_t)52U,
    (uint8_t)101U, (uint8_t)236U, (uint8_t)57U, (uint8_t)198U, (uint8_t)228U, (uint8_t)159U,
    (uint8_t)87U, (uint8_t)223U, (uint8_t)232U, (uint8_t)35U, (uint8_t)152U, (uint8_t)59U,
    (uint8_t)105U, (uint8_t)35U, (uint8_t)196U, (uint8_t)232U, (uint8_t)101U, (uint8_t)99U,
    (uint8_t)57U, (uint8_t)73U, (uint8_t)24U, (uint8_t)62U, (uint8_t)107U, (uint8_t)144U,
    (uint8_t)233U, (uint8_t)224U, (uint8_t)109U, (uint8_t)130U, (uint8_t)117U, (uint8_t)243U,
    (uint8_t)144U, (uint8_t)125U, (uint8_t)151U, (uint8_t)150U, (uint8_t)125U, (uint8_t)71U,
    (uint8_t)182U, (uint8_t)35U, (uint8_t)159U, (uint8_t)226U, (uint8_t)132U, (uint8_t)123U,
    (uint8_t)125U, (uint8_t)73U, (uint8_t)207U, (uint8_t)22U, (uint8_t)186U, (uint8_t)105U,
    (uint8_t)210U, (uint8_t)134U, (uint8_t)32U, (uint8_t)131U, (uint8_t)207U, (uint8_t)27U,
    (uint8_t)204U, (uint8_t)247U, (uint8_t)175U, (uint8_t)227U, (uint8_t)79U, (uint8_t)220U,
    (uint8_t)144U, (uint8_t)226U, (uint8_t)25U, (uint8_t)152U, (uint8_t)150U, (uint8_t)65U,
    (uint8_t)7U, (uint8_t)182U, (uint8_t)74U, (uint8_t)190U, (uint8_t)107U, (uint8_t)137U,
    (uint8_t)209U, (uint8_t)38U
  };

static uint8_t
siggen_vectors512_low8[32U] =
  {
    (uint8_t)249U, (uint8_t)191U, (uint8_t)144U, (uint8_t)155U, (uint8_t)121U, (uint8_t)115U,
    (uint8_t)191U, (uint8_t)14U, (uint8_t)61U, (uint8_t)173U, (uint8_t)14U, (uint8_t)67U,
    (uint8_t)220U, (uint8_t)178U, (uint8_t)215U, (uint8_t)250U, (uint8_t)139U, (uint8_t)218U,
    (uint8_t)73U, (uint8_t)219U, (uint8_t)230U, (uint8_t)229U, (uint8_t)53U, (uint8_t)127U,
    (uint8_t)143U, (uint8_t)14U, (uint8_t)43U, (uint8_t)209U, (uint8_t)25U, (uint8_t)190U,
    (uint8_t)48U, (uint8_t)230U
  };

static uint8_t
siggen_vectors512_low9[32U] =
  {
    (uint8_t)242U, (uint8_t)166U, (uint8_t)103U, (uint8_t)77U, (uint8_t)78U, (uint8_t)134U,
    (uint8_t)21U, (uint8_t)42U, (uint8_t)82U, (uint8_t)113U, (uint8_t)153U, (uint8_t)190U,
    (uint8_t)210U, (uint8_t)147U, (uint8_t)250U, (uint8_t)99U, (uint8_t)172U, (uint8_t)222U,
    (uint8_t)27U, (uint8_t)77U, (uint8_t)138U, (uint8_t)146U, (uint8_t)182U, (uint8_t)46U,
    (uint8_t)85U, (uint8_t)34U, (uint8_t)16U, (uint8_t)186U, (uint8_t)69U, (uint8_t)195U,
    (uint8_t)135U, (uint8_t)146U
  };

static uint8_t
siggen_vectors512_low10[32U] =
  {
    (uint8_t)199U, (uint8_t)37U, (uint8_t)101U, (uint8_t)194U, (uint8_t)79U, (uint8_t)14U,
    (uint8_t)238U, (uint8_t)106U, (uint8_t)9U, (uint8_t)74U, (uint8_t)243U, (uint8_t)65U,
    (uint8_t)221U, (uint8_t)216U, (uint8_t)87U, (uint8_t)151U, (uint8_t)71U, (uint8_t)184U,
    (uint8_t)101U, (uint8_t)249U, (uint8_t)28U, (uint8_t)142U, (uint8_t)213U, (uint8_t)180U,
    (uint8_t)76U, (uint8_t)218U, (uint8_t)138U, (uint8_t)25U, (uint8_t)204U, (uint8_t)147U,
    (uint8_t)119U, (uint8_t)111U
  };

static uint8_t
siggen_vectors512_low11[32U] =
  {
    (uint8_t)229U, (uint8_t)71U, (uint8_t)121U, (uint8_t)31U, (uint8_t)113U, (uint8_t)133U,
    (uint8_t)133U, (uint8_t)15U, (uint8_t)3U, (uint8_t)208U, (uint8_t)197U, (uint8_t)132U,
    (uint8_t)25U, (uint8_t)100U, (uint8_t)143U, (uint8_t)101U, (uint8_t)185U, (uint8_t)210U,
    (uint8_t)156U, (uint8_t)220U, (uint8_t)34U, (uint8_t)237U, (uint8_t)29U, (uint8_t)226U,
    (uint8_t)166U, (uint8_t)66U, (uint8_t)128U, (uint8_t)34U, (uint8_t)12U, (uint8_t)252U,
    (uint8_t)175U, (uint8_t)186U
  };

static uint8_t
siggen_vectors512_low12[32U] =
  {
    (uint8_t)71U, (uint8_t)130U, (uint8_t)144U, (uint8_t)61U, (uint8_t)42U, (uint8_t)175U,
    (uint8_t)139U, (uint8_t)25U, (uint8_t)13U, (uint8_t)171U, (uint8_t)92U, (uint8_t)174U,
    (uint8_t)34U, (uint8_t)35U, (uint8_t)56U, (uint8_t)141U, (uint8_t)45U, (uint8_t)139U,
    (uint8_t)216U, (uint8_t)69U, (uint8_t)179U, (uint8_t)135U, (uint8_t)93U, (uint8_t)55U,
    (uint8_t)72U, (uint8_t)92U, (uint8_t)84U, (uint8_t)225U, (uint8_t)222U, (uint8_t)209U,
    (uint8_t)211U, (uint8_t)216U
  };

static uint8_t
siggen_vectors512_low13[32U] =
  {
    (uint8_t)223U, (uint8_t)180U, (uint8_t)14U, (uint8_t)64U, (uint8_t)107U, (uint8_t)250U,
    (uint8_t)7U, (uint8_t)79U, (uint8_t)11U, (uint8_t)248U, (uint8_t)50U, (uint8_t)119U,
    (uint8_t)27U, (uint8_t)43U, (uint8_t)159U, (uint8_t)24U, (uint8_t)110U, (uint8_t)34U,
    (uint8_t)17U, (uint8_t)240U, (uint8_t)188U, (uint8_t)162U, (uint8_t)121U, (uint8_t)100U,
    (uint8_t)74U, (uint8_t)12U, (uint8_t)168U, (uint8_t)85U, (uint8_t)154U, (uint8_t)207U,
    (uint8_t)57U, (uint8_t)218U
  };

static uint8_t
siggen_vectors512_low14[128U] =
  {
    (uint8_t)213U, (uint8_t)170U, (uint8_t)138U, (uint8_t)201U, (uint8_t)33U, (uint8_t)140U,
    (uint8_t)166U, (uint8_t)97U, (uint8_t)205U, (uint8_t)23U, (uint8_t)119U, (uint8_t)86U,
    (uint8_t)175U, (uint8_t)111U, (uint8_t)187U, (uint8_t)90U, (uint8_t)64U, (uint8_t)163U,
    (uint8_t)254U, (uint8_t)207U, (uint8_t)212U, (uint8_t)238U, (uint8_t)166U, (uint8_t)213U,
    (uint8_t)135U, (uint8_t)47U, (uint8_t)187U, (uint8_t)154U, (uint8_t)40U, (uint8_t)132U,
    (uint8_t)120U, (uint8_t)74U, (uint8_t)169U, (uint8_t)181U, (uint8_t)240U, (uint8_t)192U,
    (uint8_t)35U, (uint8_t)166U, (uint8_t)224U, (uint8_t)218U, (uint8_t)92U, (uint8_t)246U,
    (uint8_t)54U, (uint8_t)71U, (uint8_t)84U, (uint8_t)238U, (uint8_t)100U, (uint8_t)101U,
    (uint8_t)180U, (uint8_t)238U, (uint8_t)45U, (uint8_t)13U, (uint8_t)220U, (uint8_t)116U,
    (uint8_t)91U, (uint8_t)2U, (uint8_t)153U, (uint8_t)76U, (uint8_t)152U, (uint8_t)66U,
    (uint8_t)122U, (uint8_t)33U, (uint8_t)60U, (uint8_t)132U, (uint8_t)149U, (uint8_t)55U,
    (uint8_t)218U, (uint8_t)90U, (uint8_t)68U, (uint8_t)119U, (uint8_t)179U, (uint8_t)171U,
    (uint8_t)254U, (uint8_t)2U, (uint8_t)100U, (uint8_t)139U, (uint8_t)230U, (uint8_t)127U,
    (uint8_t)38U, (uint8_t)232U, (uint8_t)11U, (uint8_t)86U, (uint8_t)163U, (uint8_t)49U,
    (uint8_t)80U, (uint8_t)73U, (uint8_t)13U, (uint8_t)6U, (uint8_t)42U, (uint8_t)170U,
    (uint8_t)193U, (uint8_t)55U, (uint8_t)170U, (uint8_t)71U, (uint8_t)241U, (uint8_t)28U,
    (uint8_t)254U, (uint8_t)221U, (uint8_t)186U, (uint8_t)133U, (uint8_t)91U, (uint8_t)171U,
    (uint8_t)158U, (uint8_t)78U, (uint8_t)2U, (uint8_t)133U, (uint8_t)50U, (uint8_t)165U,
    (uint8_t)99U, (uint8_t)50U, (uint8_t)109U, (uint8_t)146U, (uint8_t)127U, (uint8_t)158U,
    (uint8_t)110U, (uint8_t)50U, (uint8_t)146U, (uint8_t)177U, (uint8_t)251U, (uint8_t)36U,
    (uint8_t)142U, (uint8_t)233U, (uint8_t)11U, (uint8_t)111U, (uint8_t)66U, (uint8_t)151U,
    (uint8_t)152U, (uint8_t)219U
  };

static uint8_t
siggen_vectors512_low15[32U] =
  {
    (uint8_t)114U, (uint8_t)69U, (uint8_t)103U, (uint8_t)210U, (uint8_t)30U, (uint8_t)246U,
    (uint8_t)130U, (uint8_t)223U, (uint8_t)198U, (uint8_t)220U, (uint8_t)77U, (uint8_t)70U,
    (uint8_t)133U, (uint8_t)56U, (uint8_t)128U, (uint8_t)207U, (uint8_t)168U, (uint8_t)111U,
    (uint8_t)230U, (uint8_t)254U, (uint8_t)160U, (uint8_t)239U, (uint8_t)213U, (uint8_t)31U,
    (uint8_t)172U, (uint8_t)69U, (uint8_t)111U, (uint8_t)3U, (uint8_t)195U, (uint8_t)211U,
    (uint8_t)110U, (uint8_t)173U
  };

static uint8_t
siggen_vectors512_low16[32U] =
  {
    (uint8_t)112U, (uint8_t)184U, (uint8_t)119U, (uint8_t)181U, (uint8_t)227U, (uint8_t)101U,
    (uint8_t)252U, (uint8_t)240U, (uint8_t)129U, (uint8_t)64U, (uint8_t)177U, (uint8_t)236U,
    (uint8_t)161U, (uint8_t)25U, (uint8_t)186U, (uint8_t)186U, (uint8_t)102U, (uint8_t)40U,
    (uint8_t)121U, (uint8_t)243U, (uint8_t)142U, (uint8_t)5U, (uint8_t)157U, (uint8_t)7U,
    (uint8_t)74U, (uint8_t)44U, (uint8_t)182U, (uint8_t)11U, (uint8_t)3U, (uint8_t)234U,
    (uint8_t)93U, (uint8_t)57U
  };

static uint8_t
siggen_vectors512_low17[32U] =
  {
    (uint8_t)95U, (uint8_t)86U, (uint8_t)249U, (uint8_t)77U, (uint8_t)89U, (uint8_t)29U,
    (uint8_t)244U, (uint8_t)11U, (uint8_t)159U, (uint8_t)59U, (uint8_t)135U, (uint8_t)99U,
    (uint8_t)172U, (uint8_t)75U, (uint8_t)61U, (uint8_t)190U, (uint8_t)98U, (uint8_t)44U,
    (uint8_t)149U, (uint8_t)109U, (uint8_t)91U, (uint8_t)208U, (uint8_t)197U, (uint8_t)86U,
    (uint8_t)88U, (uint8_t)182U, (uint8_t)244U, (uint8_t)111U, (uint8_t)163U, (uint8_t)222U,
    (uint8_t)178U, (uint8_t)1U
  };

static uint8_t
siggen_vectors512_low18[32U] =
  {
    (uint8_t)121U, (uint8_t)214U, (uint8_t)201U, (uint8_t)103U, (uint8_t)237U, (uint8_t)35U,
    (uint8_t)199U, (uint8_t)99U, (uint8_t)236U, (uint8_t)233U, (uint8_t)202U, (uint8_t)75U,
    (uint8_t)2U, (uint8_t)98U, (uint8_t)24U, (uint8_t)0U, (uint8_t)76U, (uint8_t)132U,
    (uint8_t)220U, (uint8_t)45U, (uint8_t)76U, (uint8_t)204U, (uint8_t)134U, (uint8_t)207U,
    (uint8_t)5U, (uint8_t)197U, (uint8_t)208U, (uint8_t)247U, (uint8_t)145U, (uint8_t)246U,
    (uint8_t)39U, (uint8_t)155U
  };

static uint8_t
siggen_vectors512_low19[32U] =
  {
    (uint8_t)43U, (uint8_t)162U, (uint8_t)234U, (uint8_t)45U, (uint8_t)49U, (uint8_t)111U,
    (uint8_t)137U, (uint8_t)55U, (uint8_t)241U, (uint8_t)132U, (uint8_t)173U, (uint8_t)48U,
    (uint8_t)40U, (uint8_t)227U, (uint8_t)100U, (uint8_t)87U, (uint8_t)77U, (uint8_t)32U,
    (uint8_t)162U, (uint8_t)2U, (uint8_t)228U, (uint8_t)231U, (uint8_t)81U, (uint8_t)61U,
    (uint8_t)122U, (uint8_t)245U, (uint8_t)122U, (uint8_t)194U, (uint8_t)69U, (uint8_t)104U,
    (uint8_t)4U, (uint8_t)209U
  };

static uint8_t
siggen_vectors512_low20[32U] =
  {
    (uint8_t)100U, (uint8_t)254U, (uint8_t)148U, (uint8_t)150U, (uint8_t)141U, (uint8_t)24U,
    (uint8_t)197U, (uint8_t)150U, (uint8_t)124U, (uint8_t)121U, (uint8_t)158U, (uint8_t)3U,
    (uint8_t)73U, (uint8_t)4U, (uint8_t)27U, (uint8_t)158U, (uint8_t)64U, (uint8_t)230U,
    (uint8_t)198U, (uint8_t)201U, (uint8_t)46U, (uint8_t)187U, (uint8_t)71U, (uint8_t)94U,
    (uint8_t)128U, (uint8_t)221U, (uint8_t)130U, (uint8_t)245U, (uint8_t)28U, (uint8_t)240U,
    (uint8_t)115U, (uint8_t)32U
  };

static uint8_t
siggen_vectors512_low21[128U] =
  {
    (uint8_t)121U, (uint8_t)11U, (uint8_t)6U, (uint8_t)5U, (uint8_t)74U, (uint8_t)252U,
    (uint8_t)156U, (uint8_t)63U, (uint8_t)196U, (uint8_t)223U, (uint8_t)231U, (uint8_t)45U,
    (uint8_t)241U, (uint8_t)157U, (uint8_t)213U, (uint8_t)214U, (uint8_t)141U, (uint8_t)16U,
    (uint8_t)140U, (uint8_t)252U, (uint8_t)252U, (uint8_t)166U, (uint8_t)33U, (uint8_t)40U,
    (uint8_t)4U, (uint8_t)246U, (uint8_t)213U, (uint8_t)52U, (uint8_t)253U, (uint8_t)47U,
    (uint8_t)190U, (uint8_t)72U, (uint8_t)155U, (uint8_t)216U, (uint8_t)246U, (uint8_t)75U,
    (uint8_t)242U, (uint8_t)5U, (uint8_t)206U, (uint8_t)4U, (uint8_t)188U, (uint8_t)181U,
    (uint8_t)1U, (uint8_t)36U, (uint8_t)161U, (uint8_t)44U, (uint8_t)229U, (uint8_t)35U,
    (uint8_t)143U, (uint8_t)195U, (uint8_t)254U, (uint8_t)125U, (uint8_t)215U, (uint8_t)110U,
    (uint8_t)111U, (uint8_t)166U, (uint8_t)64U, (uint8_t)32U, (uint8_t)106U, (uint8_t)245U,
    (uint8_t)37U, (uint8_t)73U, (uint8_t)241U, (uint8_t)51U, (uint8_t)213U, (uint8_t)147U,
    (uint8_t)161U, (uint8_t)191U, (uint8_t)212U, (uint8_t)35U, (uint8_t)171U, (uint8_t)115U,
    (uint8_t)127U, (uint8_t)51U, (uint8_t)38U, (uint8_t)250U, (uint8_t)121U, (uint8_t)67U,
    (uint8_t)60U, (uint8_t)222U, (uint8_t)41U, (uint8_t)50U, (uint8_t)54U, (uint8_t)249U,
    (uint8_t)13U, (uint8_t)66U, (uint8_t)56U, (uint8_t)240U, (uint8_t)221U, (uint8_t)56U,
    (uint8_t)237U, (uint8_t)105U, (uint8_t)73U, (uint8_t)45U, (uint8_t)219U, (uint8_t)217U,
    (uint8_t)195U, (uint8_t)234U, (uint8_t)229U, (uint8_t)131U, (uint8_t)182U, (uint8_t)50U,
    (uint8_t)90U, (uint8_t)149U, (uint8_t)222U, (uint8_t)195U, (uint8_t)22U, (uint8_t)111U,
    (uint8_t)229U, (uint8_t)43U, (uint8_t)33U, (uint8_t)101U, (uint8_t)130U, (uint8_t)147U,
    (uint8_t)216U, (uint8_t)193U, (uint8_t)55U, (uint8_t)131U, (uint8_t)14U, (uint8_t)244U,
    (uint8_t)82U, (uint8_t)151U, (uint8_t)214U, (uint8_t)120U, (uint8_t)19U, (uint8_t)183U,
    (uint8_t)165U, (uint8_t)8U
  };

static uint8_t
siggen_vectors512_low22[32U] =
  {
    (uint8_t)41U, (uint8_t)197U, (uint8_t)213U, (uint8_t)77U, (uint8_t)125U, (uint8_t)31U,
    (uint8_t)9U, (uint8_t)157U, (uint8_t)80U, (uint8_t)249U, (uint8_t)73U, (uint8_t)191U,
    (uint8_t)206U, (uint8_t)141U, (uint8_t)96U, (uint8_t)115U, (uint8_t)218U, (uint8_t)224U,
    (uint8_t)89U, (uint8_t)197U, (uint8_t)161U, (uint8_t)156U, (uint8_t)199U, (uint8_t)8U,
    (uint8_t)52U, (uint8_t)114U, (uint8_t)47U, (uint8_t)24U, (uint8_t)167U, (uint8_t)25U,
    (uint8_t)158U, (uint8_t)221U
  };

static uint8_t
siggen_vectors512_low23[32U] =
  {
    (uint8_t)48U, (uint8_t)136U, (uint8_t)212U, (uint8_t)244U, (uint8_t)93U, (uint8_t)39U,
    (uint8_t)76U, (uint8_t)197U, (uint8_t)244U, (uint8_t)24U, (uint8_t)200U, (uint8_t)236U,
    (uint8_t)196U, (uint8_t)203U, (uint8_t)207U, (uint8_t)150U, (uint8_t)190U, (uint8_t)135U,
    (uint8_t)73U, (uint8_t)31U, (uint8_t)66U, (uint8_t)2U, (uint8_t)80U, (uint8_t)248U,
    (uint8_t)203U, (uint8_t)192U, (uint8_t)28U, (uint8_t)223U, (uint8_t)37U, (uint8_t)3U,
    (uint8_t)236U, (uint8_t)71U
  };

static uint8_t
siggen_vectors512_low24[32U] =
  {
    (uint8_t)99U, (uint8_t)77U, (uint8_t)180U, (uint8_t)129U, (uint8_t)152U, (uint8_t)18U,
    (uint8_t)146U, (uint8_t)55U, (uint8_t)237U, (uint8_t)6U, (uint8_t)140U, (uint8_t)136U,
    (uint8_t)255U, (uint8_t)88U, (uint8_t)9U, (uint8_t)246U, (uint8_t)33U, (uint8_t)25U,
    (uint8_t)33U, (uint8_t)166U, (uint8_t)37U, (uint8_t)143U, (uint8_t)84U, (uint8_t)143U,
    (uint8_t)75U, (uint8_t)100U, (uint8_t)221U, (uint8_t)18U, (uint8_t)89U, (uint8_t)33U,
    (uint8_t)183U, (uint8_t)139U
  };

static uint8_t
siggen_vectors512_low25[32U] =
  {
    (uint8_t)5U, (uint8_t)8U, (uint8_t)173U, (uint8_t)119U, (uint8_t)116U, (uint8_t)144U,
    (uint8_t)139U, (uint8_t)87U, (uint8_t)5U, (uint8_t)137U, (uint8_t)95U, (uint8_t)218U,
    (uint8_t)92U, (uint8_t)59U, (uint8_t)122U, (uint8_t)48U, (uint8_t)50U, (uint8_t)191U,
    (uint8_t)133U, (uint8_t)218U, (uint8_t)183U, (uint8_t)35U, (uint8_t)43U, (uint8_t)249U,
    (uint8_t)129U, (uint8_t)23U, (uint8_t)112U, (uint8_t)25U, (uint8_t)243U, (uint8_t)215U,
    (uint8_t)100U, (uint8_t)96U
  };

static uint8_t
siggen_vectors512_low26[32U] =
  {
    (uint8_t)172U, (uint8_t)217U, (uint8_t)243U, (uint8_t)182U, (uint8_t)54U, (uint8_t)38U,
    (uint8_t)197U, (uint8_t)243U, (uint8_t)33U, (uint8_t)3U, (uint8_t)233U, (uint8_t)14U,
    (uint8_t)29U, (uint8_t)209U, (uint8_t)105U, (uint8_t)89U, (uint8_t)7U, (uint8_t)177U,
    (uint8_t)144U, (uint8_t)74U, (uint8_t)169U, (uint8_t)177U, (uint8_t)79U, (uint8_t)33U,
    (uint8_t)50U, (uint8_t)202U, (uint8_t)239U, (uint8_t)51U, (uint8_t)19U, (uint8_t)33U,
    (uint8_t)151U, (uint8_t)27U
  };

static uint8_t
siggen_vectors512_low27[32U] =
  {
    (uint8_t)21U, (uint8_t)192U, (uint8_t)74U, (uint8_t)139U, (uint8_t)214U, (uint8_t)193U,
    (uint8_t)62U, (uint8_t)213U, (uint8_t)233U, (uint8_t)150U, (uint8_t)24U, (uint8_t)20U,
    (uint8_t)178U, (uint8_t)244U, (uint8_t)6U, (uint8_t)240U, (uint8_t)100U, (uint8_t)103U,
    (uint8_t)1U, (uint8_t)83U, (uint8_t)228U, (uint8_t)213U, (uint8_t)70U, (uint8_t)93U,
    (uint8_t)206U, (uint8_t)246U, (uint8_t)60U, (uint8_t)29U, (uint8_t)157U, (uint8_t)213U,
    (uint8_t)42U, (uint8_t)135U
  };

static uint8_t
siggen_vectors512_low28[128U] =
  {
    (uint8_t)109U, (uint8_t)84U, (uint8_t)154U, (uint8_t)168U, (uint8_t)122U, (uint8_t)253U,
    (uint8_t)184U, (uint8_t)191U, (uint8_t)166U, (uint8_t)13U, (uint8_t)34U, (uint8_t)166U,
    (uint8_t)142U, (uint8_t)39U, (uint8_t)131U, (uint8_t)178U, (uint8_t)126U, (uint8_t)141U,
    (uint8_t)180U, (uint8_t)96U, (uint8_t)65U, (uint8_t)228U, (uint8_t)223U, (uint8_t)4U,
    (uint8_t)190U, (uint8_t)12U, (uint8_t)38U, (uint8_t)28U, (uint8_t)71U, (uint8_t)52U,
    (uint8_t)182U, (uint8_t)8U, (uint8_t)169U, (uint8_t)111U, (uint8_t)25U, (uint8_t)141U,
    (uint8_t)28U, (uint8_t)219U, (uint8_t)141U, (uint8_t)8U, (uint8_t)42U, (uint8_t)228U,
    (uint8_t)133U, (uint8_t)121U, (uint8_t)236U, (uint8_t)157U, (uint8_t)239U, (uint8_t)207U,
    (uint8_t)33U, (uint8_t)251U, (uint8_t)199U, (uint8_t)40U, (uint8_t)3U, (uint8_t)118U,
    (uint8_t)74U, (uint8_t)88U, (uint8_t)195U, (uint8_t)30U, (uint8_t)83U, (uint8_t)35U,
    (uint8_t)213U, (uint8_t)69U, (uint8_t)43U, (uint8_t)159U, (uint8_t)181U, (uint8_t)124U,
    (uint8_t)137U, (uint8_t)145U, (uint8_t)211U, (uint8_t)23U, (uint8_t)73U, (uint8_t)20U,
    (uint8_t)13U, (uint8_t)167U, (uint8_t)239U, (uint8_t)6U, (uint8_t)123U, (uint8_t)24U,
    (uint8_t)191U, (uint8_t)13U, (uint8_t)125U, (uint8_t)251U, (uint8_t)174U, (uint8_t)110U,
    (uint8_t)239U, (uint8_t)208U, (uint8_t)216U, (uint8_t)6U, (uint8_t)79U, (uint8_t)51U,
    (uint8_t)75U, (uint8_t)247U, (uint8_t)233U, (uint8_t)236U, (uint8_t)30U, (uint8_t)2U,
    (uint8_t)141U, (uint8_t)174U, (uint8_t)212U, (uint8_t)232U, (uint8_t)110U, (uint8_t)23U,
    (uint8_t)99U, (uint8_t)94U, (uint8_t)194U, (uint8_t)228U, (uint8_t)9U, (uint8_t)163U,
    (uint8_t)237U, (uint8_t)18U, (uint8_t)56U, (uint8_t)4U, (uint8_t)138U, (uint8_t)69U,
    (uint8_t)136U, (uint8_t)44U, (uint8_t)92U, (uint8_t)87U, (uint8_t)80U, (uint8_t)27U,
    (uint8_t)49U, (uint8_t)78U, (uint8_t)99U, (uint8_t)107U, (uint8_t)155U, (uint8_t)200U,
    (uint8_t)28U, (uint8_t)190U
  };

static uint8_t
siggen_vectors512_low29[32U] =
  {
    (uint8_t)13U, (uint8_t)128U, (uint8_t)149U, (uint8_t)218U, (uint8_t)26U, (uint8_t)187U,
    (uint8_t)160U, (uint8_t)107U, (uint8_t)13U, (uint8_t)52U, (uint8_t)156U, (uint8_t)34U,
    (uint8_t)101U, (uint8_t)17U, (uint8_t)246U, (uint8_t)66U, (uint8_t)218U, (uint8_t)187U,
    (uint8_t)241U, (uint8_t)4U, (uint8_t)58U, (uint8_t)212U, (uint8_t)27U, (uint8_t)170U,
    (uint8_t)78U, (uint8_t)20U, (uint8_t)41U, (uint8_t)122U, (uint8_t)254U, (uint8_t)138U,
    (uint8_t)49U, (uint8_t)23U
  };

static uint8_t
siggen_vectors512_low30[32U] =
  {
    (uint8_t)117U, (uint8_t)164U, (uint8_t)87U, (uint8_t)88U, (uint8_t)206U, (uint8_t)212U,
    (uint8_t)94U, (uint8_t)207U, (uint8_t)85U, (uint8_t)247U, (uint8_t)85U, (uint8_t)203U,
    (uint8_t)86U, (uint8_t)202U, (uint8_t)38U, (uint8_t)1U, (uint8_t)215U, (uint8_t)148U,
    (uint8_t)235U, (uint8_t)234U, (uint8_t)235U, (uint8_t)46U, (uint8_t)97U, (uint8_t)7U,
    (uint8_t)254U, (uint8_t)47U, (uint8_t)196U, (uint8_t)67U, (uint8_t)245U, (uint8_t)128U,
    (uint8_t)226U, (uint8_t)60U
  };

static uint8_t
siggen_vectors512_low31[32U] =
  {
    (uint8_t)83U, (uint8_t)3U, (uint8_t)212U, (uint8_t)125U, (uint8_t)90U, (uint8_t)117U,
    (uint8_t)236U, (uint8_t)130U, (uint8_t)29U, (uint8_t)81U, (uint8_t)162U, (uint8_t)238U,
    (uint8_t)117U, (uint8_t)72U, (uint8_t)68U, (uint8_t)130U, (uint8_t)8U, (uint8_t)198U,
    (uint8_t)153U, (uint8_t)236U, (uint8_t)160U, (uint8_t)205U, (uint8_t)137U, (uint8_t)129U,
    (uint8_t)15U, (uint8_t)252U, (uint8_t)26U, (uint8_t)164U, (uint8_t)250U, (uint8_t)248U,
    (uint8_t)30U, (uint8_t)173U
  };

static uint8_t
siggen_vectors512_low32[32U] =
  {
    (uint8_t)81U, (uint8_t)101U, (uint8_t)197U, (uint8_t)77U, (uint8_t)239U, (uint8_t)64U,
    (uint8_t)38U, (uint8_t)171U, (uint8_t)100U, (uint8_t)143U, (uint8_t)119U, (uint8_t)104U,
    (uint8_t)196U, (uint8_t)241U, (uint8_t)72U, (uint8_t)139U, (uint8_t)203U, (uint8_t)24U,
    (uint8_t)63U, (uint8_t)109U, (uint8_t)183U, (uint8_t)255U, (uint8_t)224U, (uint8_t)44U,
    (uint8_t)112U, (uint8_t)34U, (uint8_t)165U, (uint8_t)41U, (uint8_t)161U, (uint8_t)22U,
    (uint8_t)72U, (uint8_t)42U
  };

static uint8_t
siggen_vectors512_low33[32U] =
  {
    (uint8_t)235U, (uint8_t)200U, (uint8_t)95U, (uint8_t)196U, (uint8_t)23U, (uint8_t)107U,
    (uint8_t)68U, (uint8_t)107U, (uint8_t)51U, (uint8_t)132U, (uint8_t)204U, (uint8_t)198U,
    (uint8_t)47U, (uint8_t)194U, (uint8_t)82U, (uint8_t)107U, (uint8_t)69U, (uint8_t)102U,
    (uint8_t)85U, (uint8_t)97U, (uint8_t)160U, (uint8_t)231U, (uint8_t)233U, (uint8_t)64U,
    (uint8_t)74U, (uint8_t)195U, (uint8_t)118U, (uint8_t)201U, (uint8_t)14U, (uint8_t)69U,
    (uint8_t)11U, (uint8_t)89U
  };

static uint8_t
siggen_vectors512_low34[32U] =
  {
    (uint8_t)139U, (uint8_t)44U, (uint8_t)9U, (uint8_t)66U, (uint8_t)142U, (uint8_t)98U,
    (uint8_t)197U, (uint8_t)16U, (uint8_t)157U, (uint8_t)23U, (uint8_t)237U, (uint8_t)12U,
    (uint8_t)248U, (uint8_t)249U, (uint8_t)253U, (uint8_t)124U, (uint8_t)55U, (uint8_t)13U,
    (uint8_t)1U, (uint8_t)138U, (uint8_t)42U, (uint8_t)115U, (uint8_t)247U, (uint8_t)1U,
    (uint8_t)239U, (uint8_t)252U, (uint8_t)155U, (uint8_t)23U, (uint8_t)208U, (uint8_t)72U,
    (uint8_t)82U, (uint8_t)198U
  };

static uint8_t
siggen_vectors512_low35[128U] =
  {
    (uint8_t)25U, (uint8_t)6U, (uint8_t)228U, (uint8_t)139U, (uint8_t)127U, (uint8_t)136U,
    (uint8_t)158U, (uint8_t)227U, (uint8_t)255U, (uint8_t)122U, (uint8_t)176U, (uint8_t)128U,
    (uint8_t)122U, (uint8_t)122U, (uint8_t)168U, (uint8_t)143U, (uint8_t)83U, (uint8_t)244U,
    (uint8_t)1U, (uint8_t)136U, (uint8_t)8U, (uint8_t)135U, (uint8_t)11U, (uint8_t)254U,
    (uint8_t)214U, (uint8_t)55U, (uint8_t)42U, (uint8_t)119U, (uint8_t)51U, (uint8_t)12U,
    (uint8_t)115U, (uint8_t)118U, (uint8_t)71U, (uint8_t)150U, (uint8_t)19U, (uint8_t)36U,
    (uint8_t)194U, (uint8_t)180U, (uint8_t)212U, (uint8_t)111U, (uint8_t)110U, (uint8_t)232U,
    (uint8_t)176U, (uint8_t)17U, (uint8_t)144U, (uint8_t)71U, (uint8_t)73U, (uint8_t)81U,
    (uint8_t)167U, (uint8_t)1U, (uint8_t)176U, (uint8_t)72U, (uint8_t)174U, (uint8_t)134U,
    (uint8_t)87U, (uint8_t)159U, (uint8_t)248U, (uint8_t)227U, (uint8_t)252U, (uint8_t)136U,
    (uint8_t)159U, (uint8_t)236U, (uint8_t)249U, (uint8_t)38U, (uint8_t)177U, (uint8_t)127U,
    (uint8_t)152U, (uint8_t)149U, (uint8_t)138U, (uint8_t)199U, (uint8_t)83U, (uint8_t)78U,
    (uint8_t)110U, (uint8_t)120U, (uint8_t)28U, (uint8_t)162U, (uint8_t)219U, (uint8_t)43U,
    (uint8_t)170U, (uint8_t)56U, (uint8_t)13U, (uint8_t)236U, (uint8_t)118U, (uint8_t)108U,
    (uint8_t)251U, (uint8_t)42U, (uint8_t)62U, (uint8_t)202U, (uint8_t)42U, (uint8_t)157U,
    (uint8_t)88U, (uint8_t)24U, (uint8_t)150U, (uint8_t)125U, (uint8_t)100U, (uint8_t)223U,
    (uint8_t)171U, (uint8_t)132U, (uint8_t)247U, (uint8_t)104U, (uint8_t)210U, (uint8_t)78U,
    (uint8_t)193U, (uint8_t)34U, (uint8_t)238U, (uint8_t)186U, (uint8_t)202U, (uint8_t)171U,
    (uint8_t)10U, (uint8_t)77U, (uint8_t)195U, (uint8_t)167U, (uint8_t)95U, (uint8_t)55U,
    (uint8_t)51U, (uint8_t)27U, (uint8_t)177U, (uint8_t)196U, (uint8_t)61U, (uint8_t)216U,
    (uint8_t)150U, (uint8_t)108U, (uint8_t)192U, (uint8_t)158U, (uint8_t)196U, (uint8_t)148U,
    (uint8_t)91U, (uint8_t)189U
  };

static uint8_t
siggen_vectors512_low36[32U] =
  {
    (uint8_t)82U, (uint8_t)254U, (uint8_t)87U, (uint8_t)218U, (uint8_t)52U, (uint8_t)39U,
    (uint8_t)177U, (uint8_t)167U, (uint8_t)92U, (uint8_t)184U, (uint8_t)22U, (uint8_t)246U,
    (uint8_t)28U, (uint8_t)78U, (uint8_t)142U, (uint8_t)14U, (uint8_t)5U, (uint8_t)81U,
    (uint8_t)185U, (uint8_t)76U, (uint8_t)1U, (uint8_t)56U, (uint8_t)43U, (uint8_t)26U,
    (uint8_t)128U, (uint8_t)131U, (uint8_t)121U, (uint8_t)64U, (uint8_t)237U, (uint8_t)87U,
    (uint8_t)158U, (uint8_t)97U
  };

static uint8_t
siggen_vectors512_low37[32U] =
  {
    (uint8_t)33U, (uint8_t)119U, (uint8_t)226U, (uint8_t)10U, (uint8_t)32U, (uint8_t)146U,
    (uint8_t)164U, (uint8_t)102U, (uint8_t)103U, (uint8_t)222U, (uint8_t)189U, (uint8_t)204U,
    (uint8_t)33U, (uint8_t)231U, (uint8_t)228U, (uint8_t)93U, (uint8_t)109U, (uint8_t)167U,
    (uint8_t)47U, (uint8_t)18U, (uint8_t)74U, (uint8_t)222U, (uint8_t)203U, (uint8_t)197U,
    (uint8_t)173U, (uint8_t)166U, (uint8_t)167U, (uint8_t)188U, (uint8_t)199U, (uint8_t)180U,
    (uint8_t)1U, (uint8_t)213U
  };

static uint8_t
siggen_vectors512_low38[32U] =
  {
    (uint8_t)85U, (uint8_t)14U, (uint8_t)70U, (uint8_t)143U, (uint8_t)38U, (uint8_t)38U,
    (uint8_t)7U, (uint8_t)10U, (uint8_t)8U, (uint8_t)10U, (uint8_t)254U, (uint8_t)235U,
    (uint8_t)152U, (uint8_t)237U, (uint8_t)215U, (uint8_t)90U, (uint8_t)114U, (uint8_t)30U,
    (uint8_t)183U, (uint8_t)115U, (uint8_t)200U, (uint8_t)230U, (uint8_t)33U, (uint8_t)73U,
    (uint8_t)243U, (uint8_t)233U, (uint8_t)3U, (uint8_t)207U, (uint8_t)156U, (uint8_t)77U,
    (uint8_t)123U, (uint8_t)97U
  };

static uint8_t
siggen_vectors512_low39[32U] =
  {
    (uint8_t)4U, (uint8_t)100U, (uint8_t)254U, (uint8_t)150U, (uint8_t)116U, (uint8_t)176U,
    (uint8_t)31U, (uint8_t)245U, (uint8_t)189U, (uint8_t)139U, (uint8_t)226U, (uint8_t)26U,
    (uint8_t)243U, (uint8_t)57U, (uint8_t)159U, (uint8_t)173U, (uint8_t)102U, (uint8_t)249U,
    (uint8_t)10U, (uint8_t)211U, (uint8_t)15U, (uint8_t)78U, (uint8_t)142U, (uint8_t)230U,
    (uint8_t)226U, (uint8_t)235U, (uint8_t)155U, (uint8_t)204U, (uint8_t)207U, (uint8_t)213U,
    (uint8_t)24U, (uint8_t)92U
  };

static uint8_t
siggen_vectors512_low40[32U] =
  {
    (uint8_t)248U, (uint8_t)37U, (uint8_t)15U, (uint8_t)7U, (uint8_t)63U, (uint8_t)52U, (uint8_t)3U,
    (uint8_t)76U, (uint8_t)28U, (uint8_t)222U, (uint8_t)88U, (uint8_t)246U, (uint8_t)154U,
    (uint8_t)133U, (uint8_t)226U, (uint8_t)245U, (uint8_t)160U, (uint8_t)48U, (uint8_t)112U,
    (uint8_t)62U, (uint8_t)189U, (uint8_t)212U, (uint8_t)219U, (uint8_t)251U, (uint8_t)152U,
    (uint8_t)211U, (uint8_t)179U, (uint8_t)105U, (uint8_t)13U, (uint8_t)183U, (uint8_t)209U,
    (uint8_t)20U
  };

static uint8_t
siggen_vectors512_low41[32U] =
  {
    (uint8_t)169U, (uint8_t)232U, (uint8_t)62U, (uint8_t)5U, (uint8_t)241U, (uint8_t)214U,
    (uint8_t)224U, (uint8_t)254U, (uint8_t)247U, (uint8_t)130U, (uint8_t)241U, (uint8_t)134U,
    (uint8_t)190U, (uint8_t)223U, (uint8_t)67U, (uint8_t)104U, (uint8_t)76U, (uint8_t)130U,
    (uint8_t)90U, (uint8_t)196U, (uint8_t)128U, (uint8_t)23U, (uint8_t)77U, (uint8_t)72U,
    (uint8_t)176U, (uint8_t)228U, (uint8_t)211U, (uint8_t)21U, (uint8_t)5U, (uint8_t)226U,
    (uint8_t)116U, (uint8_t)152U
  };

static uint8_t
siggen_vectors512_low42[128U] =
  {
    (uint8_t)123U, (uint8_t)89U, (uint8_t)254U, (uint8_t)241U, (uint8_t)61U, (uint8_t)175U,
    (uint8_t)1U, (uint8_t)175U, (uint8_t)236U, (uint8_t)53U, (uint8_t)222U, (uint8_t)163U,
    (uint8_t)39U, (uint8_t)101U, (uint8_t)65U, (uint8_t)190U, (uint8_t)104U, (uint8_t)28U,
    (uint8_t)73U, (uint8_t)22U, (uint8_t)118U, (uint8_t)127U, (uint8_t)52U, (uint8_t)212U,
    (uint8_t)232U, (uint8_t)116U, (uint8_t)70U, (uint8_t)77U, (uint8_t)32U, (uint8_t)151U,
    (uint8_t)152U, (uint8_t)99U, (uint8_t)238U, (uint8_t)119U, (uint8_t)173U, (uint8_t)15U,
    (uint8_t)209U, (uint8_t)99U, (uint8_t)91U, (uint8_t)205U, (uint8_t)249U, (uint8_t)62U,
    (uint8_t)159U, (uint8_t)98U, (uint8_t)237U, (uint8_t)105U, (uint8_t)174U, (uint8_t)82U,
    (uint8_t)236U, (uint8_t)144U, (uint8_t)170U, (uint8_t)181U, (uint8_t)187U, (uint8_t)248U,
    (uint8_t)127U, (uint8_t)137U, (uint8_t)81U, (uint8_t)33U, (uint8_t)55U, (uint8_t)71U,
    (uint8_t)204U, (uint8_t)236U, (uint8_t)159U, (uint8_t)56U, (uint8_t)199U, (uint8_t)117U,
    (uint8_t)193U, (uint8_t)223U, (uint8_t)30U, (uint8_t)157U, (uint8_t)127U, (uint8_t)115U,
    (uint8_t)92U, (uint8_t)44U, (uint8_t)227U, (uint8_t)155U, (uint8_t)66U, (uint8_t)237U,
    (uint8_t)179U, (uint8_t)176U, (uint8_t)197U, (uint8_t)8U, (uint8_t)98U, (uint8_t)71U,
    (uint8_t)85U, (uint8_t)108U, (uint8_t)254U, (uint8_t)165U, (uint8_t)57U, (uint8_t)153U,
    (uint8_t)92U, (uint8_t)93U, (uint8_t)150U, (uint8_t)137U, (uint8_t)118U, (uint8_t)82U,
    (uint8_t)136U, (uint8_t)236U, (uint8_t)96U, (uint8_t)8U, (uint8_t)72U, (uint8_t)236U,
    (uint8_t)240U, (uint8_t)133U, (uint8_t)192U, (uint8_t)28U, (uint8_t)167U, (uint8_t)56U,
    (uint8_t)187U, (uint8_t)239U, (uint8_t)17U, (uint8_t)245U, (uint8_t)209U, (uint8_t)45U,
    (uint8_t)68U, (uint8_t)87U, (uint8_t)219U, (uint8_t)152U, (uint8_t)139U, (uint8_t)74U,
    (uint8_t)221U, (uint8_t)144U, (uint8_t)190U, (uint8_t)0U, (uint8_t)120U, (uint8_t)16U,
    (uint8_t)36U, (uint8_t)173U
  };

static uint8_t
siggen_vectors512_low43[32U] =
  {
    (uint8_t)0U, (uint8_t)61U, (uint8_t)145U, (uint8_t)97U, (uint8_t)20U, (uint8_t)69U,
    (uint8_t)145U, (uint8_t)159U, (uint8_t)89U, (uint8_t)191U, (uint8_t)227U, (uint8_t)202U,
    (uint8_t)113U, (uint8_t)254U, (uint8_t)11U, (uint8_t)253U, (uint8_t)235U, (uint8_t)14U,
    (uint8_t)57U, (uint8_t)167U, (uint8_t)25U, (uint8_t)94U, (uint8_t)131U, (uint8_t)172U,
    (uint8_t)3U, (uint8_t)163U, (uint8_t)124U, (uint8_t)126U, (uint8_t)206U, (uint8_t)239U,
    (uint8_t)13U, (uint8_t)242U
  };

static uint8_t
siggen_vectors512_low44[32U] =
  {
    (uint8_t)123U, (uint8_t)156U, (uint8_t)89U, (uint8_t)47U, (uint8_t)97U, (uint8_t)170U,
    (uint8_t)224U, (uint8_t)85U, (uint8_t)88U, (uint8_t)85U, (uint8_t)208U, (uint8_t)185U,
    (uint8_t)235U, (uint8_t)182U, (uint8_t)253U, (uint8_t)0U, (uint8_t)251U, (uint8_t)103U,
    (uint8_t)70U, (uint8_t)232U, (uint8_t)132U, (uint8_t)46U, (uint8_t)37U, (uint8_t)35U,
    (uint8_t)86U, (uint8_t)92U, (uint8_t)133U, (uint8_t)134U, (uint8_t)48U, (uint8_t)185U,
    (uint8_t)186U
  };

static uint8_t
siggen_vectors512_low45[32U] =
  {
    (uint8_t)211U, (uint8_t)91U, (uint8_t)46U, (uint8_t)22U, (uint8_t)139U, (uint8_t)24U,
    (uint8_t)117U, (uint8_t)187U, (uint8_t)197U, (uint8_t)99U, (uint8_t)190U, (uint8_t)165U,
    (uint8_t)232U, (uint8_t)214U, (uint8_t)60U, (uint8_t)78U, (uint8_t)56U, (uint8_t)149U,
    (uint8_t)124U, (uint8_t)119U, (uint8_t)74U, (uint8_t)101U, (uint8_t)231U, (uint8_t)98U,
    (uint8_t)149U, (uint8_t)154U, (uint8_t)52U, (uint8_t)158U, (uint8_t)175U, (uint8_t)38U,
    (uint8_t)59U, (uint8_t)160U
  };

static uint8_t
siggen_vectors512_low46[32U] =
  {
    (uint8_t)239U, (uint8_t)157U, (uint8_t)242U, (uint8_t)145U, (uint8_t)234U, (uint8_t)39U,
    (uint8_t)164U, (uint8_t)180U, (uint8_t)87U, (uint8_t)8U, (uint8_t)247U, (uint8_t)96U,
    (uint8_t)135U, (uint8_t)35U, (uint8_t)194U, (uint8_t)125U, (uint8_t)125U, (uint8_t)86U,
    (uint8_t)183U, (uint8_t)223U, (uint8_t)5U, (uint8_t)153U, (uint8_t)165U, (uint8_t)75U,
    (uint8_t)194U, (uint8_t)194U, (uint8_t)250U, (uint8_t)187U, (uint8_t)255U, (uint8_t)55U,
    (uint8_t)59U, (uint8_t)64U
  };

static uint8_t
siggen_vectors512_low47[32U] =
  {
    (uint8_t)102U, (uint8_t)208U, (uint8_t)87U, (uint8_t)253U, (uint8_t)57U, (uint8_t)149U,
    (uint8_t)139U, (uint8_t)14U, (uint8_t)73U, (uint8_t)50U, (uint8_t)186U, (uint8_t)205U,
    (uint8_t)112U, (uint8_t)161U, (uint8_t)118U, (uint8_t)155U, (uint8_t)186U, (uint8_t)220U,
    (uint8_t)182U, (uint8_t)46U, (uint8_t)68U, (uint8_t)112U, (uint8_t)147U, (uint8_t)123U,
    (uint8_t)69U, (uint8_t)73U, (uint8_t)122U, (uint8_t)61U, (uint8_t)69U, (uint8_t)0U,
    (uint8_t)250U, (uint8_t)187U
  };

static uint8_t
siggen_vectors512_low48[32U] =
  {
    (uint8_t)108U, (uint8_t)133U, (uint8_t)59U, (uint8_t)136U, (uint8_t)158U, (uint8_t)24U,
    (uint8_t)181U, (uint8_t)164U, (uint8_t)158U, (uint8_t)229U, (uint8_t)75U, (uint8_t)84U,
    (uint8_t)221U, (uint8_t)26U, (uint8_t)174U, (uint8_t)223U, (uint8_t)221U, (uint8_t)100U,
    (uint8_t)46U, (uint8_t)48U, (uint8_t)235U, (uint8_t)161U, (uint8_t)113U, (uint8_t)197U,
    (uint8_t)202U, (uint8_t)182U, (uint8_t)119U, (uint8_t)240U, (uint8_t)223U, (uint8_t)158U,
    (uint8_t)115U, (uint8_t)24U
  };

static uint8_t
siggen_vectors512_low49[128U] =
  {
    (uint8_t)4U, (uint8_t)26U, (uint8_t)103U, (uint8_t)103U, (uint8_t)169U, (uint8_t)53U,
    (uint8_t)220U, (uint8_t)61U, (uint8_t)137U, (uint8_t)133U, (uint8_t)235U, (uint8_t)78U,
    (uint8_t)96U, (uint8_t)139U, (uint8_t)12U, (uint8_t)191U, (uint8_t)235U, (uint8_t)231U,
    (uint8_t)249U, (uint8_t)55U, (uint8_t)137U, (uint8_t)212U, (uint8_t)32U, (uint8_t)11U,
    (uint8_t)207U, (uint8_t)229U, (uint8_t)149U, (uint8_t)39U, (uint8_t)122U, (uint8_t)194U,
    (uint8_t)176U, (uint8_t)244U, (uint8_t)2U, (uint8_t)136U, (uint8_t)155U, (uint8_t)88U,
    (uint8_t)11U, (uint8_t)114U, (uint8_t)222U, (uint8_t)245U, (uint8_t)218U, (uint8_t)119U,
    (uint8_t)138U, (uint8_t)104U, (uint8_t)15U, (uint8_t)211U, (uint8_t)128U, (uint8_t)201U,
    (uint8_t)85U, (uint8_t)66U, (uint8_t)31U, (uint8_t)98U, (uint8_t)109U, (uint8_t)82U,
    (uint8_t)221U, (uint8_t)154U, (uint8_t)131U, (uint8_t)234U, (uint8_t)24U, (uint8_t)1U,
    (uint8_t)135U, (uint8_t)184U, (uint8_t)80U, (uint8_t)225U, (uint8_t)183U, (uint8_t)42U,
    (uint8_t)78U, (uint8_t)198U, (uint8_t)221U, (uint8_t)99U, (uint8_t)35U, (uint8_t)94U,
    (uint8_t)89U, (uint8_t)143U, (uint8_t)209U, (uint8_t)90U, (uint8_t)155U, (uint8_t)25U,
    (uint8_t)248U, (uint8_t)206U, (uint8_t)154U, (uint8_t)236U, (uint8_t)29U, (uint8_t)35U,
    (uint8_t)240U, (uint8_t)189U, (uint8_t)110U, (uint8_t)164U, (uint8_t)217U, (uint8_t)35U,
    (uint8_t)96U, (uint8_t)213U, (uint8_t)15U, (uint8_t)149U, (uint8_t)17U, (uint8_t)82U,
    (uint8_t)188U, (uint8_t)154U, (uint8_t)1U, (uint8_t)53U, (uint8_t)71U, (uint8_t)50U,
    (uint8_t)186U, (uint8_t)12U, (uint8_t)249U, (uint8_t)10U, (uint8_t)174U, (uint8_t)211U,
    (uint8_t)60U, (uint8_t)48U, (uint8_t)124U, (uint8_t)29U, (uint8_t)232U, (uint8_t)250U,
    (uint8_t)61U, (uint8_t)20U, (uint8_t)249U, (uint8_t)72U, (uint8_t)145U, (uint8_t)81U,
    (uint8_t)184U, (uint8_t)55U, (uint8_t)123U, (uint8_t)87U, (uint8_t)199U, (uint8_t)33U,
    (uint8_t)95U, (uint8_t)11U
  };

static uint8_t
siggen_vectors512_low50[32U] =
  {
    (uint8_t)72U, (uint8_t)241U, (uint8_t)61U, (uint8_t)57U, (uint8_t)56U, (uint8_t)153U,
    (uint8_t)205U, (uint8_t)131U, (uint8_t)92U, (uint8_t)65U, (uint8_t)147U, (uint8_t)103U,
    (uint8_t)14U, (uint8_t)198U, (uint8_t)47U, (uint8_t)40U, (uint8_t)228U, (uint8_t)196U,
    (uint8_t)144U, (uint8_t)62U, (uint8_t)11U, (uint8_t)190U, (uint8_t)88U, (uint8_t)23U,
    (uint8_t)191U, (uint8_t)9U, (uint8_t)150U, (uint8_t)131U, (uint8_t)26U, (uint8_t)114U,
    (uint8_t)11U, (uint8_t)183U
  };

static uint8_t
siggen_vectors512_low51[32U] =
  {
    (uint8_t)130U, (uint8_t)161U, (uint8_t)169U, (uint8_t)111U, (uint8_t)70U, (uint8_t)72U,
    (uint8_t)57U, (uint8_t)60U, (uint8_t)94U, (uint8_t)66U, (uint8_t)99U, (uint8_t)62U,
    (uint8_t)205U, (uint8_t)235U, (uint8_t)29U, (uint8_t)130U, (uint8_t)69U, (uint8_t)199U,
    (uint8_t)140U, (uint8_t)94U, (uint8_t)162U, (uint8_t)54U, (uint8_t)181U, (uint8_t)186U,
    (uint8_t)180U, (uint8_t)96U, (uint8_t)222U, (uint8_t)220U, (uint8_t)200U, (uint8_t)146U,
    (uint8_t)75U, (uint8_t)192U
  };

static uint8_t
siggen_vectors512_low52[32U] =
  {
    (uint8_t)232U, (uint8_t)203U, (uint8_t)240U, (uint8_t)60U, (uint8_t)52U, (uint8_t)181U,
    (uint8_t)21U, (uint8_t)79U, (uint8_t)135U, (uint8_t)109U, (uint8_t)225U, (uint8_t)159U,
    (uint8_t)59U, (uint8_t)182U, (uint8_t)253U, (uint8_t)67U, (uint8_t)205U, (uint8_t)46U,
    (uint8_t)171U, (uint8_t)246U, (uint8_t)231U, (uint8_t)201U, (uint8_t)84U, (uint8_t)103U,
    (uint8_t)188U, (uint8_t)250U, (uint8_t)140U, (uint8_t)143U, (uint8_t)196U, (uint8_t)45U,
    (uint8_t)118U, (uint8_t)253U
  };

static uint8_t
siggen_vectors512_low53[32U] =
  {
    (uint8_t)239U, (uint8_t)237U, (uint8_t)115U, (uint8_t)110U, (uint8_t)98U, (uint8_t)120U,
    (uint8_t)153U, (uint8_t)254U, (uint8_t)169U, (uint8_t)68U, (uint8_t)0U, (uint8_t)126U,
    (uint8_t)234U, (uint8_t)57U, (uint8_t)164U, (uint8_t)166U, (uint8_t)60U, (uint8_t)12U,
    (uint8_t)46U, (uint8_t)38U, (uint8_t)73U, (uint8_t)28U, (uint8_t)209U, (uint8_t)42U,
    (uint8_t)219U, (uint8_t)84U, (uint8_t)107U, (uint8_t)227U, (uint8_t)229U, (uint8_t)198U,
    (uint8_t)143U, (uint8_t)125U
  };

static uint8_t
siggen_vectors512_low54[32U] =
  {
    (uint8_t)207U, (uint8_t)127U, (uint8_t)194U, (uint8_t)75U, (uint8_t)218U, (uint8_t)160U,
    (uint8_t)154U, (uint8_t)192U, (uint8_t)204U, (uint8_t)168U, (uint8_t)73U, (uint8_t)126U,
    (uint8_t)19U, (uint8_t)41U, (uint8_t)139U, (uint8_t)150U, (uint8_t)19U, (uint8_t)128U,
    (uint8_t)102U, (uint8_t)134U, (uint8_t)19U, (uint8_t)199U, (uint8_t)73U, (uint8_t)57U,
    (uint8_t)84U, (uint8_t)4U, (uint8_t)140U, (uint8_t)6U, (uint8_t)56U, (uint8_t)90U,
    (uint8_t)112U, (uint8_t)68U
  };

static uint8_t
siggen_vectors512_low55[32U] =
  {
    (uint8_t)243U, (uint8_t)139U, (uint8_t)28U, (uint8_t)131U, (uint8_t)6U, (uint8_t)207U,
    (uint8_t)130U, (uint8_t)171U, (uint8_t)118U, (uint8_t)238U, (uint8_t)58U, (uint8_t)119U,
    (uint8_t)43U, (uint8_t)20U, (uint8_t)65U, (uint8_t)107U, (uint8_t)73U, (uint8_t)153U,
    (uint8_t)63U, (uint8_t)225U, (uint8_t)31U, (uint8_t)152U, (uint8_t)110U, (uint8_t)155U,
    (uint8_t)15U, (uint8_t)5U, (uint8_t)147U, (uint8_t)197U, (uint8_t)46U, (uint8_t)201U,
    (uint8_t)21U, (uint8_t)37U
  };

static uint8_t
siggen_vectors512_low56[128U] =
  {
    (uint8_t)121U, (uint8_t)5U, (uint8_t)169U, (uint8_t)3U, (uint8_t)110U, (uint8_t)2U,
    (uint8_t)44U, (uint8_t)120U, (uint8_t)178U, (uint8_t)201U, (uint8_t)239U, (uint8_t)212U,
    (uint8_t)11U, (uint8_t)119U, (uint8_t)176U, (uint8_t)161U, (uint8_t)148U, (uint8_t)251U,
    (uint8_t)193U, (uint8_t)212U, (uint8_t)84U, (uint8_t)98U, (uint8_t)119U, (uint8_t)155U,
    (uint8_t)11U, (uint8_t)118U, (uint8_t)173U, (uint8_t)48U, (uint8_t)220U, (uint8_t)82U,
    (uint8_t)197U, (uint8_t)100U, (uint8_t)228U, (uint8_t)138U, (uint8_t)73U, (uint8_t)61U,
    (uint8_t)130U, (uint8_t)73U, (uint8_t)160U, (uint8_t)97U, (uint8_t)230U, (uint8_t)47U,
    (uint8_t)38U, (uint8_t)244U, (uint8_t)83U, (uint8_t)186U, (uint8_t)86U, (uint8_t)101U,
    (uint8_t)56U, (uint8_t)164U, (uint8_t)212U, (uint8_t)60U, (uint8_t)100U, (uint8_t)251U,
    (uint8_t)159U, (uint8_t)219U, (uint8_t)209U, (uint8_t)243U, (uint8_t)100U, (uint8_t)9U,
    (uint8_t)49U, (uint8_t)100U, (uint8_t)51U, (uint8_t)198U, (uint8_t)240U, (uint8_t)116U,
    (uint8_t)225U, (uint8_t)180U, (uint8_t)123U, (uint8_t)84U, (uint8_t)74U, (uint8_t)132U,
    (uint8_t)125U, (uint8_t)226U, (uint8_t)95U, (uint8_t)198U, (uint8_t)125U, (uint8_t)129U,
    (uint8_t)172U, (uint8_t)128U, (uint8_t)30U, (uint8_t)217U, (uint8_t)247U, (uint8_t)55U,
    (uint8_t)26U, (uint8_t)67U, (uint8_t)218U, (uint8_t)57U, (uint8_t)0U, (uint8_t)28U,
    (uint8_t)144U, (uint8_t)118U, (uint8_t)111U, (uint8_t)148U, (uint8_t)62U, (uint8_t)98U,
    (uint8_t)157U, (uint8_t)116U, (uint8_t)208U, (uint8_t)67U, (uint8_t)107U, (uint8_t)161U,
    (uint8_t)36U, (uint8_t)12U, (uint8_t)61U, (uint8_t)127U, (uint8_t)171U, (uint8_t)153U,
    (uint8_t)13U, (uint8_t)88U, (uint8_t)106U, (uint8_t)109U, (uint8_t)110U, (uint8_t)241U,
    (uint8_t)119U, (uint8_t)23U, (uint8_t)134U, (uint8_t)114U, (uint8_t)45U, (uint8_t)245U,
    (uint8_t)100U, (uint8_t)72U, (uint8_t)129U, (uint8_t)95U, (uint8_t)47U, (uint8_t)237U,
    (uint8_t)164U, (uint8_t)143U
  };

static uint8_t
siggen_vectors512_low57[32U] =
  {
    (uint8_t)149U, (uint8_t)201U, (uint8_t)156U, (uint8_t)249U, (uint8_t)236U, (uint8_t)38U,
    (uint8_t)72U, (uint8_t)2U, (uint8_t)117U, (uint8_t)242U, (uint8_t)61U, (uint8_t)228U,
    (uint8_t)25U, (uint8_t)228U, (uint8_t)27U, (uint8_t)183U, (uint8_t)121U, (uint8_t)89U,
    (uint8_t)15U, (uint8_t)14U, (uint8_t)171U, (uint8_t)92U, (uint8_t)249U, (uint8_t)9U,
    (uint8_t)93U, (uint8_t)55U, (uint8_t)221U, (uint8_t)112U, (uint8_t)203U, (uint8_t)117U,
    (uint8_t)232U, (uint8_t)112U
  };

static uint8_t
siggen_vectors512_low58[32U] =
  {
    (uint8_t)66U, (uint8_t)194U, (uint8_t)146U, (uint8_t)176U, (uint8_t)251U, (uint8_t)204U,
    (uint8_t)159U, (uint8_t)69U, (uint8_t)122U, (uint8_t)227U, (uint8_t)97U, (uint8_t)217U,
    (uint8_t)64U, (uint8_t)169U, (uint8_t)212U, (uint8_t)90U, (uint8_t)217U, (uint8_t)66U,
    (uint8_t)116U, (uint8_t)49U, (uint8_t)161U, (uint8_t)5U, (uint8_t)166U, (uint8_t)229U,
    (uint8_t)205U, (uint8_t)144U, (uint8_t)163U, (uint8_t)69U, (uint8_t)254U, (uint8_t)53U,
    (uint8_t)7U, (uint8_t)247U
  };

static uint8_t
siggen_vectors512_low59[32U] =
  {
    (uint8_t)49U, (uint8_t)59U, (uint8_t)8U, (uint8_t)253U, (uint8_t)47U, (uint8_t)163U,
    (uint8_t)81U, (uint8_t)144U, (uint8_t)139U, (uint8_t)49U, (uint8_t)120U, (uint8_t)5U,
    (uint8_t)30U, (uint8_t)231U, (uint8_t)130U, (uint8_t)204U, (uint8_t)98U, (uint8_t)185U,
    (uint8_t)149U, (uint8_t)74U, (uint8_t)217U, (uint8_t)93U, (uint8_t)65U, (uint8_t)25U,
    (uint8_t)170U, (uint8_t)86U, (uint8_t)73U, (uint8_t)0U, (uint8_t)248U, (uint8_t)173U,
    (uint8_t)231U, (uint8_t)12U
  };

static uint8_t
siggen_vectors512_low60[32U] =
  {
    (uint8_t)76U, (uint8_t)8U, (uint8_t)221U, (uint8_t)15U, (uint8_t)139U, (uint8_t)114U,
    (uint8_t)174U, (uint8_t)156U, (uint8_t)103U, (uint8_t)78U, (uint8_t)30U, (uint8_t)68U,
    (uint8_t)141U, (uint8_t)78U, (uint8_t)42U, (uint8_t)254U, (uint8_t)58U, (uint8_t)30U,
    (uint8_t)230U, (uint8_t)153U, (uint8_t)39U, (uint8_t)250U, (uint8_t)35U, (uint8_t)187U,
    (uint8_t)255U, (uint8_t)55U, (uint8_t)22U, (uint8_t)240U, (uint8_t)185U, (uint8_t)149U,
    (uint8_t)83U, (uint8_t)183U
  };

static uint8_t
siggen_vectors512_low61[32U] =
  {
    (uint8_t)242U, (uint8_t)188U, (uint8_t)53U, (uint8_t)235U, (uint8_t)27U, (uint8_t)132U,
    (uint8_t)136U, (uint8_t)185U, (uint8_t)232U, (uint8_t)212U, (uint8_t)161U, (uint8_t)219U,
    (uint8_t)178U, (uint8_t)0U, (uint8_t)225U, (uint8_t)171U, (uint8_t)203U, (uint8_t)133U,
    (uint8_t)84U, (uint8_t)88U, (uint8_t)225U, (uint8_t)85U, (uint8_t)125U, (uint8_t)193U,
    (uint8_t)191U, (uint8_t)152U, (uint8_t)130U, (uint8_t)120U, (uint8_t)161U, (uint8_t)116U,
    (uint8_t)235U, (uint8_t)59U
  };

static uint8_t
siggen_vectors512_low62[32U] =
  {
    (uint8_t)237U, (uint8_t)154U, (uint8_t)46U, (uint8_t)192U, (uint8_t)67U, (uint8_t)161U,
    (uint8_t)213U, (uint8_t)120U, (uint8_t)232U, (uint8_t)235U, (uint8_t)166U, (uint8_t)245U,
    (uint8_t)114U, (uint8_t)23U, (uint8_t)151U, (uint8_t)99U, (uint8_t)16U, (uint8_t)232U,
    (uint8_t)103U, (uint8_t)67U, (uint8_t)133U, (uint8_t)173U, (uint8_t)45U, (uint8_t)160U,
    (uint8_t)141U, (uint8_t)97U, (uint8_t)70U, (uint8_t)198U, (uint8_t)41U, (uint8_t)222U,
    (uint8_t)28U, (uint8_t)217U
  };

static uint8_t
siggen_vectors512_low63[128U] =
  {
    (uint8_t)207U, (uint8_t)37U, (uint8_t)228U, (uint8_t)100U, (uint8_t)45U, (uint8_t)79U,
    (uint8_t)57U, (uint8_t)209U, (uint8_t)90U, (uint8_t)251U, (uint8_t)122U, (uint8_t)236U,
    (uint8_t)121U, (uint8_t)70U, (uint8_t)157U, (uint8_t)130U, (uint8_t)252U, (uint8_t)154U,
    (uint8_t)237U, (uint8_t)184U, (uint8_t)248U, (uint8_t)153U, (uint8_t)100U, (uint8_t)231U,
    (uint8_t)155U, (uint8_t)116U, (uint8_t)154U, (uint8_t)133U, (uint8_t)45U, (uint8_t)147U,
    (uint8_t)29U, (uint8_t)55U, (uint8_t)67U, (uint8_t)101U, (uint8_t)2U, (uint8_t)128U,
    (uint8_t)78U, (uint8_t)57U, (uint8_t)85U, (uint8_t)95U, (uint8_t)90U, (uint8_t)60U,
    (uint8_t)117U, (uint8_t)221U, (uint8_t)149U, (uint8_t)143U, (uint8_t)213U, (uint8_t)41U,
    (uint8_t)26U, (uint8_t)218U, (uint8_t)100U, (uint8_t)124U, (uint8_t)26U, (uint8_t)94U,
    (uint8_t)56U, (uint8_t)254U, (uint8_t)123U, (uint8_t)16U, (uint8_t)72U, (uint8_t)241U,
    (uint8_t)111U, (uint8_t)43U, (uint8_t)113U, (uint8_t)31U, (uint8_t)221U, (uint8_t)93U,
    (uint8_t)57U, (uint8_t)172U, (uint8_t)192U, (uint8_t)129U, (uint8_t)44U, (uint8_t)166U,
    (uint8_t)91U, (uint8_t)213U, (uint8_t)13U, (uint8_t)127U, (uint8_t)129U, (uint8_t)25U,
    (uint8_t)242U, (uint8_t)253U, (uint8_t)25U, (uint8_t)90U, (uint8_t)177U, (uint8_t)102U,
    (uint8_t)51U, (uint8_t)80U, (uint8_t)58U, (uint8_t)120U, (uint8_t)238U, (uint8_t)145U,
    (uint8_t)2U, (uint8_t)193U, (uint8_t)249U, (uint8_t)196U, (uint8_t)194U, (uint8_t)37U,
    (uint8_t)104U, (uint8_t)224U, (uint8_t)181U, (uint8_t)75U, (uint8_t)212U, (uint8_t)250U,
    (uint8_t)63U, (uint8_t)95U, (uint8_t)247U, (uint8_t)180U, (uint8_t)145U, (uint8_t)96U,
    (uint8_t)191U, (uint8_t)35U, (uint8_t)231U, (uint8_t)226U, (uint8_t)35U, (uint8_t)27U,
    (uint8_t)30U, (uint8_t)190U, (uint8_t)187U, (uint8_t)218U, (uint8_t)240U, (uint8_t)228U,
    (uint8_t)167U, (uint8_t)212U, (uint8_t)72U, (uint8_t)65U, (uint8_t)88U, (uint8_t)168U,
    (uint8_t)126U, (uint8_t)7U
  };

static uint8_t
siggen_vectors512_low64[32U] =
  {
    (uint8_t)225U, (uint8_t)94U, (uint8_t)131U, (uint8_t)93U, (uint8_t)14U, (uint8_t)34U,
    (uint8_t)23U, (uint8_t)188U, (uint8_t)124U, (uint8_t)111U, (uint8_t)5U, (uint8_t)164U,
    (uint8_t)152U, (uint8_t)242U, (uint8_t)10U, (uint8_t)241U, (uint8_t)205U, (uint8_t)86U,
    (uint8_t)242U, (uint8_t)241U, (uint8_t)101U, (uint8_t)194U, (uint8_t)61U, (uint8_t)34U,
    (uint8_t)94U, (uint8_t)179U, (uint8_t)54U, (uint8_t)10U, (uint8_t)162U, (uint8_t)197U,
    (uint8_t)203U, (uint8_t)207U
  };

static uint8_t
siggen_vectors512_low65[32U] =
  {
    (uint8_t)137U, (uint8_t)221U, (uint8_t)34U, (uint8_t)5U, (uint8_t)46U, (uint8_t)195U,
    (uint8_t)171U, (uint8_t)72U, (uint8_t)64U, (uint8_t)32U, (uint8_t)106U, (uint8_t)98U,
    (uint8_t)242U, (uint8_t)39U, (uint8_t)12U, (uint8_t)33U, (uint8_t)231U, (uint8_t)131U,
    (uint8_t)109U, (uint8_t)26U, (uint8_t)145U, (uint8_t)9U, (uint8_t)163U, (uint8_t)64U,
    (uint8_t)125U, (uint8_t)208U, (uint8_t)151U, (uint8_t)76U, (uint8_t)120U, (uint8_t)2U,
    (uint8_t)185U, (uint8_t)174U
  };

static uint8_t
siggen_vectors512_low66[32U] =
  {
    (uint8_t)233U, (uint8_t)22U, (uint8_t)9U, (uint8_t)186U, (uint8_t)53U, (uint8_t)199U,
    (uint8_t)0U, (uint8_t)139U, (uint8_t)8U, (uint8_t)12U, (uint8_t)119U, (uint8_t)169U,
    (uint8_t)6U, (uint8_t)141U, (uint8_t)151U, (uint8_t)161U, (uint8_t)76U, (uint8_t)167U,
    (uint8_t)123U, (uint8_t)151U, (uint8_t)41U, (uint8_t)158U, (uint8_t)116U, (uint8_t)148U,
    (uint8_t)82U, (uint8_t)23U, (uint8_t)103U, (uint8_t)43U, (uint8_t)47U, (uint8_t)213U,
    (uint8_t)250U, (uint8_t)240U
  };

static uint8_t
siggen_vectors512_low67[32U] =
  {
    (uint8_t)201U, (uint8_t)246U, (uint8_t)33U, (uint8_t)68U, (uint8_t)28U, (uint8_t)35U,
    (uint8_t)95U, (uint8_t)196U, (uint8_t)126U, (uint8_t)195U, (uint8_t)78U, (uint8_t)239U,
    (uint8_t)76U, (uint8_t)8U, (uint8_t)98U, (uint8_t)93U, (uint8_t)241U, (uint8_t)236U,
    (uint8_t)116U, (uint8_t)145U, (uint8_t)142U, (uint8_t)31U, (uint8_t)134U, (uint8_t)7U,
    (uint8_t)91U, (uint8_t)117U, (uint8_t)63U, (uint8_t)37U, (uint8_t)137U, (uint8_t)244U,
    (uint8_t)198U, (uint8_t)11U
  };

static uint8_t
siggen_vectors512_low68[32U] =
  {
    (uint8_t)167U, (uint8_t)13U, (uint8_t)26U, (uint8_t)45U, (uint8_t)85U, (uint8_t)93U,
    (uint8_t)89U, (uint8_t)155U, (uint8_t)251U, (uint8_t)140U, (uint8_t)155U, (uint8_t)31U,
    (uint8_t)13U, (uint8_t)67U, (uint8_t)114U, (uint8_t)83U, (uint8_t)65U, (uint8_t)21U,
    (uint8_t)29U, (uint8_t)23U, (uint8_t)168U, (uint8_t)208U, (uint8_t)132U, (uint8_t)95U,
    (uint8_t)165U, (uint8_t)111U, (uint8_t)53U, (uint8_t)99U, (uint8_t)112U, (uint8_t)53U,
    (uint8_t)40U, (uint8_t)167U
  };

static uint8_t
siggen_vectors512_low69[32U] =
  {
    (uint8_t)78U, (uint8_t)5U, (uint8_t)196U, (uint8_t)90U, (uint8_t)223U, (uint8_t)65U,
    (uint8_t)120U, (uint8_t)62U, (uint8_t)57U, (uint8_t)74U, (uint8_t)83U, (uint8_t)18U,
    (uint8_t)248U, (uint8_t)110U, (uint8_t)102U, (uint8_t)135U, (uint8_t)28U, (uint8_t)75U,
    (uint8_t)228U, (uint8_t)137U, (uint8_t)105U, (uint8_t)72U, (uint8_t)200U, (uint8_t)89U,
    (uint8_t)102U, (uint8_t)135U, (uint8_t)157U, (uint8_t)92U, (uint8_t)102U, (uint8_t)213U,
    (uint8_t)75U, (uint8_t)55U
  };

static uint8_t
siggen_vectors512_low70[128U] =
  {
    (uint8_t)117U, (uint8_t)98U, (uint8_t)196U, (uint8_t)69U, (uint8_t)179U, (uint8_t)88U,
    (uint8_t)131U, (uint8_t)204U, (uint8_t)147U, (uint8_t)123U, (uint8_t)230U, (uint8_t)52U,
    (uint8_t)155U, (uint8_t)76U, (uint8_t)239U, (uint8_t)195U, (uint8_t)85U, (uint8_t)106U,
    (uint8_t)128U, (uint8_t)37U, (uint8_t)93U, (uint8_t)112U, (uint8_t)240U, (uint8_t)158U,
    (uint8_t)40U, (uint8_t)195U, (uint8_t)243U, (uint8_t)147U, (uint8_t)218U, (uint8_t)172U,
    (uint8_t)25U, (uint8_t)68U, (uint8_t)42U, (uint8_t)126U, (uint8_t)236U, (uint8_t)237U,
    (uint8_t)205U, (uint8_t)251U, (uint8_t)232U, (uint8_t)247U, (uint8_t)98U, (uint8_t)142U,
    (uint8_t)48U, (uint8_t)205U, (uint8_t)137U, (uint8_t)57U, (uint8_t)83U, (uint8_t)126U,
    (uint8_t)197U, (uint8_t)109U, (uint8_t)92U, (uint8_t)150U, (uint8_t)69U, (uint8_t)212U,
    (uint8_t)51U, (uint8_t)64U, (uint8_t)235U, (uint8_t)78U, (uint8_t)120U, (uint8_t)252U,
    (uint8_t)93U, (uint8_t)212U, (uint8_t)50U, (uint8_t)45U, (uint8_t)232U, (uint8_t)160U,
    (uint8_t)121U, (uint8_t)102U, (uint8_t)178U, (uint8_t)98U, (uint8_t)119U, (uint8_t)13U,
    (uint8_t)127U, (uint8_t)241U, (uint8_t)58U, (uint8_t)7U, (uint8_t)31U, (uint8_t)243U,
    (uint8_t)220U, (uint8_t)229U, (uint8_t)96U, (uint8_t)113U, (uint8_t)142U, (uint8_t)96U,
    (uint8_t)237U, (uint8_t)48U, (uint8_t)134U, (uint8_t)183U, (uint8_t)224U, (uint8_t)0U,
    (uint8_t)58U, (uint8_t)106U, (uint8_t)186U, (uint8_t)254U, (uint8_t)145U, (uint8_t)175U,
    (uint8_t)144U, (uint8_t)175U, (uint8_t)134U, (uint8_t)115U, (uint8_t)60U, (uint8_t)232U,
    (uint8_t)104U, (uint8_t)148U, (uint8_t)64U, (uint8_t)191U, (uint8_t)115U, (uint8_t)210U,
    (uint8_t)170U, (uint8_t)10U, (uint8_t)207U, (uint8_t)233U, (uint8_t)119U, (uint8_t)96U,
    (uint8_t)54U, (uint8_t)232U, (uint8_t)119U, (uint8_t)89U, (uint8_t)154U, (uint8_t)203U,
    (uint8_t)171U, (uint8_t)252U, (uint8_t)176U, (uint8_t)59U, (uint8_t)179U, (uint8_t)181U,
    (uint8_t)15U, (uint8_t)170U
  };

static uint8_t
siggen_vectors512_low71[32U] =
  {
    (uint8_t)128U, (uint8_t)140U, (uint8_t)8U, (uint8_t)192U, (uint8_t)215U, (uint8_t)116U,
    (uint8_t)35U, (uint8_t)166U, (uint8_t)254U, (uint8_t)170U, (uint8_t)255U, (uint8_t)200U,
    (uint8_t)249U, (uint8_t)138U, (uint8_t)41U, (uint8_t)72U, (uint8_t)241U, (uint8_t)119U,
    (uint8_t)38U, (uint8_t)230U, (uint8_t)124U, (uint8_t)21U, (uint8_t)238U, (uint8_t)174U,
    (uint8_t)78U, (uint8_t)103U, (uint8_t)46U, (uint8_t)219U, (uint8_t)227U, (uint8_t)136U,
    (uint8_t)249U, (uint8_t)140U
  };

static uint8_t
siggen_vectors512_low72[32U] =
  {
    (uint8_t)176U, (uint8_t)192U, (uint8_t)173U, (uint8_t)94U, (uint8_t)31U, (uint8_t)96U,
    (uint8_t)1U, (uint8_t)216U, (uint8_t)233U, (uint8_t)1U, (uint8_t)142U, (uint8_t)198U,
    (uint8_t)17U, (uint8_t)178U, (uint8_t)227U, (uint8_t)185U, (uint8_t)25U, (uint8_t)35U,
    (uint8_t)230U, (uint8_t)159U, (uint8_t)166U, (uint8_t)201U, (uint8_t)134U, (uint8_t)144U,
    (uint8_t)171U, (uint8_t)100U, (uint8_t)77U, (uint8_t)101U, (uint8_t)15U, (uint8_t)100U,
    (uint8_t)12U, (uint8_t)66U
  };

static uint8_t
siggen_vectors512_low73[32U] =
  {
    (uint8_t)97U, (uint8_t)5U, (uint8_t)57U, (uint8_t)192U, (uint8_t)185U, (uint8_t)237U,
    (uint8_t)33U, (uint8_t)172U, (uint8_t)10U, (uint8_t)47U, (uint8_t)39U, (uint8_t)82U,
    (uint8_t)124U, (uint8_t)26U, (uint8_t)97U, (uint8_t)217U, (uint8_t)180U, (uint8_t)124U,
    (uint8_t)191U, (uint8_t)3U, (uint8_t)49U, (uint8_t)135U, (uint8_t)177U, (uint8_t)166U,
    (uint8_t)173U, (uint8_t)160U, (uint8_t)6U, (uint8_t)235U, (uint8_t)91U, (uint8_t)38U,
    (uint8_t)98U, (uint8_t)237U
  };

static uint8_t
siggen_vectors512_low74[32U] =
  {
    (uint8_t)31U, (uint8_t)109U, (uint8_t)74U, (uint8_t)144U, (uint8_t)92U, (uint8_t)118U,
    (uint8_t)26U, (uint8_t)83U, (uint8_t)213U, (uint8_t)76U, (uint8_t)54U, (uint8_t)41U,
    (uint8_t)118U, (uint8_t)113U, (uint8_t)125U, (uint8_t)13U, (uint8_t)127U, (uint8_t)201U,
    (uint8_t)77U, (uint8_t)34U, (uint8_t)43U, (uint8_t)181U, (uint8_t)72U, (uint8_t)158U,
    (uint8_t)72U, (uint8_t)48U, (uint8_t)8U, (uint8_t)10U, (uint8_t)26U, (uint8_t)103U,
    (uint8_t)83U, (uint8_t)93U
  };

static uint8_t
siggen_vectors512_low75[32U] =
  {
    (uint8_t)131U, (uint8_t)64U, (uint8_t)77U, (uint8_t)207U, (uint8_t)131U, (uint8_t)32U,
    (uint8_t)186U, (uint8_t)242U, (uint8_t)6U, (uint8_t)56U, (uint8_t)24U, (uint8_t)0U, (uint8_t)7U,
    (uint8_t)30U, (uint8_t)106U, (uint8_t)117U, (uint8_t)22U, (uint8_t)3U, (uint8_t)66U,
    (uint8_t)209U, (uint8_t)151U, (uint8_t)67U, (uint8_t)180U, (uint8_t)241U, (uint8_t)118U,
    (uint8_t)150U, (uint8_t)13U, (uint8_t)102U, (uint8_t)157U, (uint8_t)208U, (uint8_t)61U,
    (uint8_t)7U
  };

static uint8_t
siggen_vectors512_low76[32U] =
  {
    (uint8_t)63U, (uint8_t)117U, (uint8_t)220U, (uint8_t)241U, (uint8_t)2U, (uint8_t)0U,
    (uint8_t)139U, (uint8_t)41U, (uint8_t)137U, (uint8_t)248U, (uint8_t)22U, (uint8_t)131U,
    (uint8_t)174U, (uint8_t)69U, (uint8_t)233U, (uint8_t)241U, (uint8_t)212U, (uint8_t)182U,
    (uint8_t)122U, (uint8_t)110U, (uint8_t)246U, (uint8_t)253U, (uint8_t)92U, (uint8_t)138U,
    (uint8_t)244U, (uint8_t)72U, (uint8_t)40U, (uint8_t)175U, (uint8_t)128U, (uint8_t)225U,
    (uint8_t)207U, (uint8_t)181U
  };

static uint8_t
siggen_vectors512_low77[128U] =
  {
    (uint8_t)5U, (uint8_t)28U, (uint8_t)45U, (uint8_t)184U, (uint8_t)231U, (uint8_t)30U,
    (uint8_t)68U, (uint8_t)101U, (uint8_t)62U, (uint8_t)161U, (uint8_t)203U, (uint8_t)10U,
    (uint8_t)252U, (uint8_t)158U, (uint8_t)10U, (uint8_t)189U, (uint8_t)241U, (uint8_t)38U,
    (uint8_t)88U, (uint8_t)233U, (uint8_t)231U, (uint8_t)97U, (uint8_t)191U, (uint8_t)183U,
    (uint8_t)103U, (uint8_t)194U, (uint8_t)12U, (uint8_t)122U, (uint8_t)180U, (uint8_t)173U,
    (uint8_t)252U, (uint8_t)177U, (uint8_t)142U, (uint8_t)217U, (uint8_t)181U, (uint8_t)195U,
    (uint8_t)114U, (uint8_t)163U, (uint8_t)172U, (uint8_t)17U, (uint8_t)216U, (uint8_t)164U,
    (uint8_t)60U, (uint8_t)85U, (uint8_t)247U, (uint8_t)249U, (uint8_t)155U, (uint8_t)51U,
    (uint8_t)53U, (uint8_t)84U, (uint8_t)55U, (uint8_t)137U, (uint8_t)22U, (uint8_t)134U,
    (uint8_t)212U, (uint8_t)35U, (uint8_t)98U, (uint8_t)171U, (uint8_t)215U, (uint8_t)29U,
    (uint8_t)184U, (uint8_t)182U, (uint8_t)216U, (uint8_t)77U, (uint8_t)214U, (uint8_t)148U,
    (uint8_t)214U, (uint8_t)152U, (uint8_t)47U, (uint8_t)6U, (uint8_t)18U, (uint8_t)23U,
    (uint8_t)138U, (uint8_t)147U, (uint8_t)122U, (uint8_t)169U, (uint8_t)52U, (uint8_t)185U,
    (uint8_t)172U, (uint8_t)60U, (uint8_t)7U, (uint8_t)148U, (uint8_t)195U, (uint8_t)144U,
    (uint8_t)39U, (uint8_t)189U, (uint8_t)215U, (uint8_t)103U, (uint8_t)132U, (uint8_t)28U,
    (uint8_t)67U, (uint8_t)112U, (uint8_t)102U, (uint8_t)108U, (uint8_t)128U, (uint8_t)219U,
    (uint8_t)192U, (uint8_t)248U, (uint8_t)19U, (uint8_t)44U, (uint8_t)162U, (uint8_t)116U,
    (uint8_t)116U, (uint8_t)245U, (uint8_t)83U, (uint8_t)210U, (uint8_t)102U, (uint8_t)222U,
    (uint8_t)239U, (uint8_t)215U, (uint8_t)201U, (uint8_t)219U, (uint8_t)173U, (uint8_t)109U,
    (uint8_t)115U, (uint8_t)79U, (uint8_t)144U, (uint8_t)6U, (uint8_t)187U, (uint8_t)85U,
    (uint8_t)117U, (uint8_t)103U, (uint8_t)112U, (uint8_t)27U, (uint8_t)183U, (uint8_t)230U,
    (uint8_t)167U, (uint8_t)201U
  };

static uint8_t
siggen_vectors512_low78[32U] =
  {
    (uint8_t)247U, (uint8_t)198U, (uint8_t)49U, (uint8_t)95U, (uint8_t)0U, (uint8_t)129U,
    (uint8_t)172U, (uint8_t)216U, (uint8_t)240U, (uint8_t)156U, (uint8_t)122U, (uint8_t)44U,
    (uint8_t)62U, (uint8_t)193U, (uint8_t)183U, (uint8_t)236U, (uint8_t)226U, (uint8_t)1U,
    (uint8_t)128U, (uint8_t)176U, (uint8_t)166U, (uint8_t)54U, (uint8_t)90U, (uint8_t)39U,
    (uint8_t)220U, (uint8_t)216U, (uint8_t)247U, (uint8_t)27U, (uint8_t)114U, (uint8_t)149U,
    (uint8_t)88U, (uint8_t)249U
  };

static uint8_t
siggen_vectors512_low79[32U] =
  {
    (uint8_t)37U, (uint8_t)15U, (uint8_t)113U, (uint8_t)18U, (uint8_t)211U, (uint8_t)129U,
    (uint8_t)193U, (uint8_t)117U, (uint8_t)24U, (uint8_t)96U, (uint8_t)4U, (uint8_t)93U,
    (uint8_t)155U, (uint8_t)202U, (uint8_t)242U, (uint8_t)13U, (uint8_t)190U, (uint8_t)178U,
    (uint8_t)90U, (uint8_t)0U, (uint8_t)20U, (uint8_t)49U, (uint8_t)249U, (uint8_t)106U,
    (uint8_t)198U, (uint8_t)241U, (uint8_t)145U, (uint8_t)9U, (uint8_t)54U, (uint8_t)47U,
    (uint8_t)254U, (uint8_t)187U
  };

static uint8_t
siggen_vectors512_low80[32U] =
  {
    (uint8_t)73U, (uint8_t)251U, (uint8_t)169U, (uint8_t)239U, (uint8_t)231U, (uint8_t)53U,
    (uint8_t)70U, (uint8_t)19U, (uint8_t)90U, (uint8_t)90U, (uint8_t)49U, (uint8_t)171U,
    (uint8_t)55U, (uint8_t)83U, (uint8_t)226U, (uint8_t)71U, (uint8_t)3U, (uint8_t)71U,
    (uint8_t)65U, (uint8_t)206U, (uint8_t)131U, (uint8_t)157U, (uint8_t)61U, (uint8_t)148U,
    (uint8_t)189U, (uint8_t)115U, (uint8_t)147U, (uint8_t)108U, (uint8_t)74U, (uint8_t)23U,
    (uint8_t)228U, (uint8_t)170U
  };

static uint8_t
siggen_vectors512_low81[32U] =
  {
    (uint8_t)104U, (uint8_t)194U, (uint8_t)153U, (uint8_t)190U, (uint8_t)44U, (uint8_t)12U,
    (uint8_t)109U, (uint8_t)82U, (uint8_t)210U, (uint8_t)8U, (uint8_t)213U, (uint8_t)209U,
    (uint8_t)169U, (uint8_t)224U, (uint8_t)255U, (uint8_t)162U, (uint8_t)175U, (uint8_t)25U,
    (uint8_t)180U, (uint8_t)131U, (uint8_t)50U, (uint8_t)113U, (uint8_t)64U, (uint8_t)78U,
    (uint8_t)88U, (uint8_t)118U, (uint8_t)224U, (uint8_t)170U, (uint8_t)147U, (uint8_t)152U,
    (uint8_t)120U, (uint8_t)102U
  };

static uint8_t
siggen_vectors512_low82[32U] =
  {
    (uint8_t)123U, (uint8_t)25U, (uint8_t)94U, (uint8_t)146U, (uint8_t)210U, (uint8_t)186U,
    (uint8_t)149U, (uint8_t)145U, (uint8_t)28U, (uint8_t)218U, (uint8_t)117U, (uint8_t)112U,
    (uint8_t)96U, (uint8_t)126U, (uint8_t)17U, (uint8_t)45U, (uint8_t)2U, (uint8_t)161U,
    (uint8_t)200U, (uint8_t)71U, (uint8_t)221U, (uint8_t)170U, (uint8_t)51U, (uint8_t)146U,
    (uint8_t)71U, (uint8_t)52U, (uint8_t)181U, (uint8_t)31U, (uint8_t)93U, (uint8_t)129U,
    (uint8_t)173U, (uint8_t)171U
  };

static uint8_t
siggen_vectors512_low83[32U] =
  {
    (uint8_t)16U, (uint8_t)217U, (uint8_t)242U, (uint8_t)6U, (uint8_t)117U, (uint8_t)92U,
    (uint8_t)239U, (uint8_t)112U, (uint8_t)171U, (uint8_t)81U, (uint8_t)67U, (uint8_t)172U,
    (uint8_t)67U, (uint8_t)243U, (uint8_t)248U, (uint8_t)211U, (uint8_t)138U, (uint8_t)234U,
    (uint8_t)38U, (uint8_t)68U, (uint8_t)243U, (uint8_t)29U, (uint8_t)82U, (uint8_t)234U,
    (uint8_t)243U, (uint8_t)180U, (uint8_t)114U, (uint8_t)238U, (uint8_t)129U, (uint8_t)110U,
    (uint8_t)17U, (uint8_t)229U
  };

static uint8_t
siggen_vectors512_low84[128U] =
  {
    (uint8_t)77U, (uint8_t)203U, (uint8_t)123U, (uint8_t)98U, (uint8_t)186U, (uint8_t)49U,
    (uint8_t)184U, (uint8_t)102U, (uint8_t)252U, (uint8_t)231U, (uint8_t)193U, (uint8_t)254U,
    (uint8_t)237U, (uint8_t)240U, (uint8_t)190U, (uint8_t)31U, (uint8_t)103U, (uint8_t)191U,
    (uint8_t)97U, (uint8_t)29U, (uint8_t)188U, (uint8_t)46U, (uint8_t)46U, (uint8_t)134U,
    (uint8_t)240U, (uint8_t)4U, (uint8_t)66U, (uint8_t)47U, (uint8_t)103U, (uint8_t)179U,
    (uint8_t)188U, (uint8_t)24U, (uint8_t)57U, (uint8_t)198U, (uint8_t)149U, (uint8_t)142U,
    (uint8_t)177U, (uint8_t)220U, (uint8_t)62U, (uint8_t)173U, (uint8_t)19U, (uint8_t)124U,
    (uint8_t)61U, (uint8_t)127U, (uint8_t)136U, (uint8_t)170U, (uint8_t)151U, (uint8_t)36U,
    (uint8_t)69U, (uint8_t)119U, (uint8_t)167U, (uint8_t)117U, (uint8_t)200U, (uint8_t)2U,
    (uint8_t)27U, (uint8_t)22U, (uint8_t)66U, (uint8_t)168U, (uint8_t)100U, (uint8_t)123U,
    (uint8_t)186U, (uint8_t)130U, (uint8_t)135U, (uint8_t)30U, (uint8_t)60U, (uint8_t)21U,
    (uint8_t)208U, (uint8_t)116U, (uint8_t)158U, (uint8_t)211U, (uint8_t)67U, (uint8_t)234U,
    (uint8_t)108U, (uint8_t)173U, (uint8_t)56U, (uint8_t)241U, (uint8_t)35U, (uint8_t)131U,
    (uint8_t)93U, (uint8_t)142U, (uint8_t)246U, (uint8_t)107U, (uint8_t)7U, (uint8_t)25U,
    (uint8_t)39U, (uint8_t)49U, (uint8_t)5U, (uint8_t)233U, (uint8_t)36U, (uint8_t)232U,
    (uint8_t)104U, (uint8_t)91U, (uint8_t)101U, (uint8_t)253U, (uint8_t)93U, (uint8_t)196U,
    (uint8_t)48U, (uint8_t)239U, (uint8_t)188U, (uint8_t)53U, (uint8_t)176U, (uint8_t)90U,
    (uint8_t)96U, (uint8_t)151U, (uint8_t)241U, (uint8_t)126U, (uint8_t)188U, (uint8_t)89U,
    (uint8_t)67U, (uint8_t)205U, (uint8_t)205U, (uint8_t)154U, (uint8_t)188U, (uint8_t)186U,
    (uint8_t)117U, (uint8_t)43U, (uint8_t)127U, (uint8_t)143U, (uint8_t)55U, (uint8_t)2U,
    (uint8_t)116U, (uint8_t)9U, (uint8_t)189U, (uint8_t)110U, (uint8_t)17U, (uint8_t)205U,
    (uint8_t)21U, (uint8_t)143U
  };

static uint8_t
siggen_vectors512_low85[32U] =
  {
    (uint8_t)245U, (uint8_t)71U, (uint8_t)115U, (uint8_t)90U, (uint8_t)148U, (uint8_t)9U,
    (uint8_t)56U, (uint8_t)109U, (uint8_t)191U, (uint8_t)247U, (uint8_t)25U, (uint8_t)206U,
    (uint8_t)45U, (uint8_t)174U, (uint8_t)3U, (uint8_t)197U, (uint8_t)12U, (uint8_t)180U,
    (uint8_t)55U, (uint8_t)214U, (uint8_t)179U, (uint8_t)12U, (uint8_t)199U, (uint8_t)250U,
    (uint8_t)62U, (uint8_t)162U, (uint8_t)13U, (uint8_t)154U, (uint8_t)236U, (uint8_t)23U,
    (uint8_t)229U, (uint8_t)165U
  };

static uint8_t
siggen_vectors512_low86[32U] =
  {
    (uint8_t)76U, (uint8_t)168U, (uint8_t)124U, (uint8_t)88U, (uint8_t)69U, (uint8_t)251U,
    (uint8_t)4U, (uint8_t)194U, (uint8_t)247U, (uint8_t)106U, (uint8_t)227U, (uint8_t)39U,
    (uint8_t)48U, (uint8_t)115U, (uint8_t)176U, (uint8_t)82U, (uint8_t)62U, (uint8_t)53U,
    (uint8_t)106U, (uint8_t)68U, (uint8_t)94U, (uint8_t)78U, (uint8_t)149U, (uint8_t)115U,
    (uint8_t)114U, (uint8_t)96U, (uint8_t)235U, (uint8_t)169U, (uint8_t)226U, (uint8_t)208U,
    (uint8_t)33U, (uint8_t)219U
  };

static uint8_t
siggen_vectors512_low87[32U] =
  {
    (uint8_t)15U, (uint8_t)134U, (uint8_t)71U, (uint8_t)93U, (uint8_t)7U, (uint8_t)248U,
    (uint8_t)38U, (uint8_t)85U, (uint8_t)50U, (uint8_t)15U, (uint8_t)223U, (uint8_t)44U,
    (uint8_t)216U, (uint8_t)219U, (uint8_t)35U, (uint8_t)178U, (uint8_t)25U, (uint8_t)5U,
    (uint8_t)177U, (uint8_t)177U, (uint8_t)242U, (uint8_t)249U, (uint8_t)196U, (uint8_t)142U,
    (uint8_t)45U, (uint8_t)248U, (uint8_t)126U, (uint8_t)36U, (uint8_t)17U, (uint8_t)156U,
    (uint8_t)72U, (uint8_t)128U
  };

static uint8_t
siggen_vectors512_low88[32U] =
  {
    (uint8_t)145U, (uint8_t)189U, (uint8_t)125U, (uint8_t)151U, (uint8_t)247U, (uint8_t)237U,
    (uint8_t)50U, (uint8_t)83U, (uint8_t)206U, (uint8_t)222U, (uint8_t)252U, (uint8_t)20U,
    (uint8_t)71U, (uint8_t)113U, (uint8_t)187U, (uint8_t)138U, (uint8_t)203U, (uint8_t)189U,
    (uint8_t)166U, (uint8_t)235U, (uint8_t)36U, (uint8_t)249U, (uint8_t)215U, (uint8_t)82U,
    (uint8_t)187U, (uint8_t)225U, (uint8_t)221U, (uint8_t)1U, (uint8_t)142U, (uint8_t)19U,
    (uint8_t)132U, (uint8_t)199U
  };

static uint8_t
siggen_vectors512_low89[32U] =
  {
    (uint8_t)0U, (uint8_t)140U, (uint8_t)23U, (uint8_t)85U, (uint8_t)211U, (uint8_t)223U,
    (uint8_t)129U, (uint8_t)230U, (uint8_t)78U, (uint8_t)37U, (uint8_t)39U, (uint8_t)13U,
    (uint8_t)186U, (uint8_t)169U, (uint8_t)57U, (uint8_t)102U, (uint8_t)65U, (uint8_t)85U,
    (uint8_t)109U, (uint8_t)247U, (uint8_t)255U, (uint8_t)199U, (uint8_t)172U, (uint8_t)154U,
    (uint8_t)221U, (uint8_t)103U, (uint8_t)57U, (uint8_t)195U, (uint8_t)130U, (uint8_t)112U,
    (uint8_t)83U, (uint8_t)151U
  };

static uint8_t
siggen_vectors512_low90[32U] =
  {
    (uint8_t)119U, (uint8_t)223U, (uint8_t)68U, (uint8_t)60U, (uint8_t)114U, (uint8_t)155U,
    (uint8_t)3U, (uint8_t)154U, (uint8_t)222U, (uint8_t)213U, (uint8_t)181U, (uint8_t)22U,
    (uint8_t)177U, (uint8_t)7U, (uint8_t)127U, (uint8_t)236U, (uint8_t)221U, (uint8_t)153U,
    (uint8_t)134U, (uint8_t)64U, (uint8_t)45U, (uint8_t)44U, (uint8_t)75U, (uint8_t)1U,
    (uint8_t)115U, (uint8_t)75U, (uint8_t)169U, (uint8_t)30U, (uint8_t)5U, (uint8_t)94U,
    (uint8_t)135U, (uint8_t)252U
  };

static uint8_t
siggen_vectors512_low91[128U] =
  {
    (uint8_t)239U, (uint8_t)229U, (uint8_t)87U, (uint8_t)55U, (uint8_t)119U, (uint8_t)16U,
    (uint8_t)112U, (uint8_t)213U, (uint8_t)172U, (uint8_t)121U, (uint8_t)35U, (uint8_t)107U,
    (uint8_t)4U, (uint8_t)227U, (uint8_t)251U, (uint8_t)175U, (uint8_t)79U, (uint8_t)46U,
    (uint8_t)155U, (uint8_t)237U, (uint8_t)24U, (uint8_t)125U, (uint8_t)25U, (uint8_t)48U,
    (uint8_t)104U, (uint8_t)15U, (uint8_t)207U, (uint8_t)26U, (uint8_t)186U, (uint8_t)118U,
    (uint8_t)150U, (uint8_t)116U, (uint8_t)191U, (uint8_t)66U, (uint8_t)99U, (uint8_t)16U,
    (uint8_t)242U, (uint8_t)18U, (uint8_t)69U, (uint8_t)0U, (uint8_t)111U, (uint8_t)82U,
    (uint8_t)135U, (uint8_t)121U, (uint8_t)52U, (uint8_t)125U, (uint8_t)40U, (uint8_t)184U,
    (uint8_t)174U, (uint8_t)172U, (uint8_t)210U, (uint8_t)177U, (uint8_t)213U, (uint8_t)227U,
    (uint8_t)69U, (uint8_t)109U, (uint8_t)203U, (uint8_t)241U, (uint8_t)136U, (uint8_t)178U,
    (uint8_t)190U, (uint8_t)140U, (uint8_t)7U, (uint8_t)241U, (uint8_t)146U, (uint8_t)25U,
    (uint8_t)228U, (uint8_t)6U, (uint8_t)124U, (uint8_t)30U, (uint8_t)124U, (uint8_t)151U,
    (uint8_t)20U, (uint8_t)120U, (uint8_t)66U, (uint8_t)133U, (uint8_t)216U, (uint8_t)186U,
    (uint8_t)199U, (uint8_t)154U, (uint8_t)118U, (uint8_t)181U, (uint8_t)111U, (uint8_t)46U,
    (uint8_t)38U, (uint8_t)118U, (uint8_t)234U, (uint8_t)147U, (uint8_t)153U, (uint8_t)79U,
    (uint8_t)17U, (uint8_t)235U, (uint8_t)87U, (uint8_t)58U, (uint8_t)241U, (uint8_t)208U,
    (uint8_t)63U, (uint8_t)200U, (uint8_t)237U, (uint8_t)17U, (uint8_t)24U, (uint8_t)234U,
    (uint8_t)252U, (uint8_t)127U, (uint8_t)7U, (uint8_t)168U, (uint8_t)47U, (uint8_t)50U,
    (uint8_t)99U, (uint8_t)195U, (uint8_t)62U, (uint8_t)184U, (uint8_t)94U, (uint8_t)73U,
    (uint8_t)126U, (uint8_t)24U, (uint8_t)244U, (uint8_t)53U, (uint8_t)212U, (uint8_t)7U,
    (uint8_t)106U, (uint8_t)119U, (uint8_t)79U, (uint8_t)66U, (uint8_t)210U, (uint8_t)118U,
    (uint8_t)195U, (uint8_t)35U
  };

static uint8_t
siggen_vectors512_low92[32U] =
  {
    (uint8_t)38U, (uint8_t)161U, (uint8_t)170U, (uint8_t)75U, (uint8_t)146U, (uint8_t)122U,
    (uint8_t)81U, (uint8_t)107U, (uint8_t)102U, (uint8_t)25U, (uint8_t)134U, (uint8_t)137U,
    (uint8_t)90U, (uint8_t)255U, (uint8_t)88U, (uint8_t)244U, (uint8_t)11U, (uint8_t)120U,
    (uint8_t)204U, (uint8_t)93U, (uint8_t)12U, (uint8_t)118U, (uint8_t)126U, (uint8_t)218U,
    (uint8_t)126U, (uint8_t)170U, (uint8_t)61U, (uint8_t)187U, (uint8_t)131U, (uint8_t)91U,
    (uint8_t)86U, (uint8_t)40U
  };

static uint8_t
siggen_vectors512_low93[32U] =
  {
    (uint8_t)40U, (uint8_t)175U, (uint8_t)163U, (uint8_t)176U, (uint8_t)248U, (uint8_t)26U,
    (uint8_t)14U, (uint8_t)149U, (uint8_t)173U, (uint8_t)48U, (uint8_t)47U, (uint8_t)72U,
    (uint8_t)122U, (uint8_t)155U, (uint8_t)103U, (uint8_t)159U, (uint8_t)205U, (uint8_t)239U,
    (uint8_t)141U, (uint8_t)63U, (uint8_t)64U, (uint8_t)35U, (uint8_t)110U, (uint8_t)196U,
    (uint8_t)212U, (uint8_t)219U, (uint8_t)244U, (uint8_t)187U, (uint8_t)12U, (uint8_t)187U,
    (uint8_t)168U, (uint8_t)178U
  };

static uint8_t
siggen_vectors512_low94[32U] =
  {
    (uint8_t)187U, (uint8_t)74U, (uint8_t)193U, (uint8_t)190U, (uint8_t)132U, (uint8_t)5U,
    (uint8_t)203U, (uint8_t)174U, (uint8_t)138U, (uint8_t)85U, (uint8_t)63U, (uint8_t)188U,
    (uint8_t)40U, (uint8_t)226U, (uint8_t)158U, (uint8_t)46U, (uint8_t)104U, (uint8_t)159U,
    (uint8_t)171U, (uint8_t)231U, (uint8_t)222U, (uint8_t)242U, (uint8_t)109U, (uint8_t)101U,
    (uint8_t)58U, (uint8_t)29U, (uint8_t)175U, (uint8_t)192U, (uint8_t)35U, (uint8_t)243U,
    (uint8_t)206U, (uint8_t)207U
  };

static uint8_t
siggen_vectors512_low95[32U] =
  {
    (uint8_t)249U, (uint8_t)142U, (uint8_t)25U, (uint8_t)51U, (uint8_t)199U, (uint8_t)250U,
    (uint8_t)212U, (uint8_t)172U, (uint8_t)190U, (uint8_t)148U, (uint8_t)217U, (uint8_t)92U,
    (uint8_t)27U, (uint8_t)1U, (uint8_t)62U, (uint8_t)29U, (uint8_t)105U, (uint8_t)49U,
    (uint8_t)250U, (uint8_t)143U, (uint8_t)103U, (uint8_t)230U, (uint8_t)219U, (uint8_t)182U,
    (uint8_t)119U, (uint8_t)181U, (uint8_t)100U, (uint8_t)239U, (uint8_t)124U, (uint8_t)62U,
    (uint8_t)86U, (uint8_t)206U
  };

static uint8_t
siggen_vectors512_low96[32U] =
  {
    (uint8_t)21U, (uint8_t)169U, (uint8_t)165U, (uint8_t)65U, (uint8_t)45U, (uint8_t)106U,
    (uint8_t)3U, (uint8_t)237U, (uint8_t)215U, (uint8_t)27U, (uint8_t)132U, (uint8_t)193U,
    (uint8_t)33U, (uint8_t)206U, (uint8_t)154U, (uint8_t)148U, (uint8_t)205U, (uint8_t)209U,
    (uint8_t)102U, (uint8_t)228U, (uint8_t)13U, (uint8_t)169U, (uint8_t)206U, (uint8_t)77U,
    (uint8_t)121U, (uint8_t)241U, (uint8_t)175U, (uint8_t)255U, (uint8_t)106U, (uint8_t)57U,
    (uint8_t)90U, (uint8_t)83U
  };

static uint8_t
siggen_vectors512_low97[32U] =
  {
    (uint8_t)134U, (uint8_t)187U, (uint8_t)194U, (uint8_t)182U, (uint8_t)198U, (uint8_t)59U,
    (uint8_t)173U, (uint8_t)112U, (uint8_t)110U, (uint8_t)192U, (uint8_t)176U, (uint8_t)147U,
    (uint8_t)87U, (uint8_t)142U, (uint8_t)63U, (uint8_t)6U, (uint8_t)71U, (uint8_t)54U,
    (uint8_t)236U, (uint8_t)105U, (uint8_t)192U, (uint8_t)219U, (uint8_t)165U, (uint8_t)155U,
    (uint8_t)158U, (uint8_t)62U, (uint8_t)127U, (uint8_t)115U, (uint8_t)118U, (uint8_t)42U,
    (uint8_t)77U, (uint8_t)195U
  };

static uint8_t
siggen_vectors512_low98[128U] =
  {
    (uint8_t)234U, (uint8_t)149U, (uint8_t)133U, (uint8_t)156U, (uint8_t)193U, (uint8_t)60U,
    (uint8_t)204U, (uint8_t)179U, (uint8_t)113U, (uint8_t)152U, (uint8_t)217U, (uint8_t)25U,
    (uint8_t)128U, (uint8_t)59U, (uint8_t)232U, (uint8_t)156U, (uint8_t)46U, (uint8_t)225U,
    (uint8_t)11U, (uint8_t)239U, (uint8_t)220U, (uint8_t)175U, (uint8_t)93U, (uint8_t)90U,
    (uint8_t)250U, (uint8_t)9U, (uint8_t)220U, (uint8_t)197U, (uint8_t)41U, (uint8_t)211U,
    (uint8_t)51U, (uint8_t)174U, (uint8_t)30U, (uint8_t)79U, (uint8_t)253U, (uint8_t)59U,
    (uint8_t)216U, (uint8_t)186U, (uint8_t)134U, (uint8_t)66U, (uint8_t)32U, (uint8_t)59U,
    (uint8_t)173U, (uint8_t)215U, (uint8_t)168U, (uint8_t)10U, (uint8_t)63U, (uint8_t)119U,
    (uint8_t)238U, (uint8_t)238U, (uint8_t)148U, (uint8_t)2U, (uint8_t)238U, (uint8_t)211U,
    (uint8_t)101U, (uint8_t)213U, (uint8_t)63U, (uint8_t)5U, (uint8_t)193U, (uint8_t)169U,
    (uint8_t)149U, (uint8_t)197U, (uint8_t)54U, (uint8_t)248U, (uint8_t)35U, (uint8_t)107U,
    (uint8_t)166U, (uint8_t)182U, (uint8_t)255U, (uint8_t)136U, (uint8_t)151U, (uint8_t)57U,
    (uint8_t)53U, (uint8_t)6U, (uint8_t)102U, (uint8_t)12U, (uint8_t)200U, (uint8_t)234U,
    (uint8_t)130U, (uint8_t)178U, (uint8_t)22U, (uint8_t)58U, (uint8_t)166U, (uint8_t)161U,
    (uint8_t)133U, (uint8_t)82U, (uint8_t)81U, (uint8_t)200U, (uint8_t)125U, (uint8_t)147U,
    (uint8_t)94U, (uint8_t)35U, (uint8_t)133U, (uint8_t)127U, (uint8_t)227U, (uint8_t)91U,
    (uint8_t)136U, (uint8_t)148U, (uint8_t)39U, (uint8_t)180U, (uint8_t)73U, (uint8_t)222U,
    (uint8_t)114U, (uint8_t)116U, (uint8_t)215U, (uint8_t)117U, (uint8_t)75U, (uint8_t)222U,
    (uint8_t)172U, (uint8_t)233U, (uint8_t)96U, (uint8_t)180U, (uint8_t)48U, (uint8_t)60U,
    (uint8_t)93U, (uint8_t)213U, (uint8_t)247U, (uint8_t)69U, (uint8_t)165U, (uint8_t)207U,
    (uint8_t)213U, (uint8_t)128U, (uint8_t)41U, (uint8_t)61U, (uint8_t)101U, (uint8_t)72U,
    (uint8_t)200U, (uint8_t)50U
  };

static uint8_t
siggen_vectors512_low99[32U] =
  {
    (uint8_t)106U, (uint8_t)92U, (uint8_t)163U, (uint8_t)154U, (uint8_t)174U, (uint8_t)45U,
    (uint8_t)69U, (uint8_t)170U, (uint8_t)51U, (uint8_t)31U, (uint8_t)24U, (uint8_t)168U,
    (uint8_t)89U, (uint8_t)138U, (uint8_t)63U, (uint8_t)45U, (uint8_t)179U, (uint8_t)39U,
    (uint8_t)129U, (uint8_t)247U, (uint8_t)201U, (uint8_t)46U, (uint8_t)253U, (uint8_t)79U,
    (uint8_t)100U, (uint8_t)238U, (uint8_t)59U, (uint8_t)190U, (uint8_t)12U, (uint8_t)76U,
    (uint8_t)78U, (uint8_t)73U
  };

static uint8_t
siggen_vectors512_low100[32U] =
  {
    (uint8_t)198U, (uint8_t)44U, (uint8_t)196U, (uint8_t)163U, (uint8_t)154U, (uint8_t)206U,
    (uint8_t)1U, (uint8_t)0U, (uint8_t)106U, (uint8_t)212U, (uint8_t)140U, (uint8_t)244U,
    (uint8_t)154U, (uint8_t)62U, (uint8_t)113U, (uint8_t)70U, (uint8_t)105U, (uint8_t)85U,
    (uint8_t)187U, (uint8_t)238U, (uint8_t)202U, (uint8_t)93U, (uint8_t)49U, (uint8_t)141U,
    (uint8_t)103U, (uint8_t)38U, (uint8_t)149U, (uint8_t)223U, (uint8_t)146U, (uint8_t)107U,
    (uint8_t)58U, (uint8_t)164U
  };

static uint8_t
siggen_vectors512_low101[32U] =
  {
    (uint8_t)200U, (uint8_t)92U, (uint8_t)207U, (uint8_t)81U, (uint8_t)123U, (uint8_t)242U,
    (uint8_t)235U, (uint8_t)217U, (uint8_t)173U, (uint8_t)106U, (uint8_t)158U, (uint8_t)153U,
    (uint8_t)37U, (uint8_t)77U, (uint8_t)239U, (uint8_t)13U, (uint8_t)116U, (uint8_t)209U,
    (uint8_t)210U, (uint8_t)253U, (uint8_t)97U, (uint8_t)30U, (uint8_t)50U, (uint8_t)139U,
    (uint8_t)74U, (uint8_t)57U, (uint8_t)136U, (uint8_t)212U, (uint8_t)240U, (uint8_t)69U,
    (uint8_t)254U, (uint8_t)111U
  };

static uint8_t
siggen_vectors512_low102[32U] =
  {
    (uint8_t)218U, (uint8_t)192U, (uint8_t)12U, (uint8_t)70U, (uint8_t)43U, (uint8_t)200U,
    (uint8_t)91U, (uint8_t)243U, (uint8_t)156U, (uint8_t)49U, (uint8_t)181U, (uint8_t)224U,
    (uint8_t)29U, (uint8_t)243U, (uint8_t)62U, (uint8_t)46U, (uint8_t)193U, (uint8_t)86U,
    (uint8_t)158U, (uint8_t)110U, (uint8_t)252U, (uint8_t)179U, (uint8_t)52U, (uint8_t)191U,
    (uint8_t)24U, (uint8_t)240U, (uint8_t)149U, (uint8_t)25U, (uint8_t)146U, (uint8_t)172U,
    (uint8_t)97U, (uint8_t)96U
  };

static uint8_t
siggen_vectors512_low103[32U] =
  {
    (uint8_t)110U, (uint8_t)127U, (uint8_t)248U, (uint8_t)236U, (uint8_t)122U, (uint8_t)92U,
    (uint8_t)72U, (uint8_t)224U, (uint8_t)135U, (uint8_t)114U, (uint8_t)36U, (uint8_t)169U,
    (uint8_t)250U, (uint8_t)132U, (uint8_t)129U, (uint8_t)40U, (uint8_t)61U, (uint8_t)228U,
    (uint8_t)95U, (uint8_t)203U, (uint8_t)238U, (uint8_t)35U, (uint8_t)180U, (uint8_t)194U,
    (uint8_t)82U, (uint8_t)176U, (uint8_t)198U, (uint8_t)34U, (uint8_t)68U, (uint8_t)44U,
    (uint8_t)38U, (uint8_t)173U
  };

static uint8_t
siggen_vectors512_low104[32U] =
  {
    (uint8_t)61U, (uint8_t)250U, (uint8_t)195U, (uint8_t)32U, (uint8_t)185U, (uint8_t)200U,
    (uint8_t)115U, (uint8_t)49U, (uint8_t)129U, (uint8_t)23U, (uint8_t)218U, (uint8_t)107U,
    (uint8_t)216U, (uint8_t)86U, (uint8_t)0U, (uint8_t)10U, (uint8_t)57U, (uint8_t)43U,
    (uint8_t)129U, (uint8_t)86U, (uint8_t)89U, (uint8_t)229U, (uint8_t)170U, (uint8_t)42U,
    (uint8_t)106U, (uint8_t)24U, (uint8_t)82U, (uint8_t)204U, (uint8_t)178U, (uint8_t)80U,
    (uint8_t)29U, (uint8_t)243U
  };

static __Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors512_low105[15U] =
  {
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low0 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low1 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low2 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low3 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low4 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low5 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low6 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low7 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low8 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low9 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low10 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low11 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low12 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low13 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low14 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low15 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low16 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low17 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low18 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low19 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low20 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low21 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low22 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low23 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low24 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low25 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low26 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low27 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low28 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low29 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low30 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low31 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low32 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low33 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low34 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low35 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low36 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low37 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low38 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low39 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low40 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low41 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low42 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low43 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low44 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low45 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low46 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low47 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low48 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low49 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low50 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low51 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low52 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low53 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low54 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low55 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low56 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low57 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low58 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low59 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low60 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low61 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low62 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low63 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low64 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low65 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low66 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low67 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low68 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low69 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low70 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low71 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low72 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low73 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low74 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low75 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low76 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low77 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low78 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low79 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low80 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low81 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low82 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low83 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low84 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low85 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low86 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low87 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low88 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low89 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low90 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low91 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low92 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low93 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low94 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low95 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low96 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low97 }
    },
    {
      .fst = { .len = (uint32_t)128U, .b = siggen_vectors512_low98 },
      .snd = { .len = (uint32_t)32U, .b = siggen_vectors512_low99 },
      .thd = { .len = (uint32_t)32U, .b = siggen_vectors512_low100 },
      .f3 = { .len = (uint32_t)32U, .b = siggen_vectors512_low101 },
      .f4 = { .len = (uint32_t)32U, .b = siggen_vectors512_low102 },
      .f5 = { .len = (uint32_t)32U, .b = siggen_vectors512_low103 },
      .f6 = { .len = (uint32_t)32U, .b = siggen_vectors512_low104 }
    }
  };

static lbuffer__K___Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t_Test_Lowstarize_lbuffer__uint8_t
siggen_vectors512_low = { .len = (uint32_t)15U, .b = siggen_vectors512_low105 };

static bool compare_and_print(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  LowStar_Printf_print_string("Expected: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b1);
  LowStar_Printf_print_string("\n");
  LowStar_Printf_print_string("Computed: ");
  LowStar_Printf_print_lmbuffer_u8(len, (uint8_t *)b2);
  LowStar_Printf_print_string("\n");
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(b1[i], b2[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool b = z == (uint8_t)255U;
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
  if
  (
    !(qx_len
    == (uint32_t)32U
    && qy_len == (uint32_t)32U
    && r_len == (uint32_t)32U
    && s_len == (uint32_t)32U)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, (uint32_t)32U * sizeof (uint8_t));
    memcpy(qxy + (uint32_t)32U, qy, (uint32_t)32U * sizeof (uint8_t));
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
  if
  (
    !(qx_len
    == (uint32_t)32U
    && qy_len == (uint32_t)32U
    && r_len == (uint32_t)32U
    && s_len == (uint32_t)32U)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, (uint32_t)32U * sizeof (uint8_t));
    memcpy(qxy + (uint32_t)32U, qy, (uint32_t)32U * sizeof (uint8_t));
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
  if
  (
    !(qx_len
    == (uint32_t)32U
    && qy_len == (uint32_t)32U
    && r_len == (uint32_t)32U
    && s_len == (uint32_t)32U)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, (uint32_t)32U * sizeof (uint8_t));
    memcpy(qxy + (uint32_t)32U, qy, (uint32_t)32U * sizeof (uint8_t));
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
  uint64_t zero = (uint64_t)0U;
  uint64_t q1 = (uint64_t)17562291160714782033U;
  uint64_t q2 = (uint64_t)13611842547513532036U;
  uint64_t q3 = (uint64_t)18446744073709551615U;
  uint64_t q4 = (uint64_t)18446744069414584320U;
  uint64_t u0 = load64_be(b);
  uint64_t x1 = u0;
  uint64_t u1 = load64_be(b + (uint32_t)8U);
  uint64_t x2 = u1;
  uint64_t u2 = load64_be(b + (uint32_t)16U);
  uint64_t x3 = u2;
  uint64_t u = load64_be(b + (uint32_t)24U);
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
  if (!(k_len == (uint32_t)32U && d_len == (uint32_t)32U))
  {
    exit((int32_t)-1);
  }
  bool bound_k = check_bound(k);
  bool bound_d = check_bound(d);
  if
  (
    !(bound_k
    && bound_d
    && qx_len == (uint32_t)32U
    && qy_len == (uint32_t)32U
    && r_len == (uint32_t)32U
    && s_len == (uint32_t)32U)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t rs[64U] = { 0U };
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, (uint32_t)32U * sizeof (uint8_t));
    memcpy(qxy + (uint32_t)32U, qy, (uint32_t)32U * sizeof (uint8_t));
    bool flag = Hacl_P256_ecdsa_sign_p256_sha2(rs, msg_len, msg, d, k);
    if (flag)
    {
      bool okr = compare_and_print(rs, r, (uint32_t)32U);
      bool oks = compare_and_print(rs + (uint32_t)32U, s, (uint32_t)32U);
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
  if (!(k_len == (uint32_t)32U && d_len == (uint32_t)32U))
  {
    exit((int32_t)-1);
  }
  bool bound_k = check_bound(k);
  bool bound_d = check_bound(d);
  if
  (
    !(bound_k
    && bound_d
    && qx_len == (uint32_t)32U
    && qy_len == (uint32_t)32U
    && r_len == (uint32_t)32U
    && s_len == (uint32_t)32U)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t rs[64U] = { 0U };
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, (uint32_t)32U * sizeof (uint8_t));
    memcpy(qxy + (uint32_t)32U, qy, (uint32_t)32U * sizeof (uint8_t));
    bool flag = Hacl_P256_ecdsa_sign_p256_sha384(rs, msg_len, msg, d, k);
    if (flag)
    {
      bool okr = compare_and_print(rs, r, (uint32_t)32U);
      bool oks = compare_and_print(rs + (uint32_t)32U, s, (uint32_t)32U);
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
  if (!(k_len == (uint32_t)32U && d_len == (uint32_t)32U))
  {
    exit((int32_t)-1);
  }
  bool bound_k = check_bound(k);
  bool bound_d = check_bound(d);
  if
  (
    !(bound_k
    && bound_d
    && qx_len == (uint32_t)32U
    && qy_len == (uint32_t)32U
    && r_len == (uint32_t)32U
    && s_len == (uint32_t)32U)
  )
  {
    exit((int32_t)-1);
  }
  else
  {
    uint8_t rs[64U] = { 0U };
    uint8_t qxy[64U] = { 0U };
    memcpy(qxy, qx, (uint32_t)32U * sizeof (uint8_t));
    memcpy(qxy + (uint32_t)32U, qy, (uint32_t)32U * sizeof (uint8_t));
    bool flag = Hacl_P256_ecdsa_sign_p256_sha512(rs, msg_len, msg, d, k);
    if (flag)
    {
      bool okr = compare_and_print(rs, r, (uint32_t)32U);
      bool oks = compare_and_print(rs + (uint32_t)32U, s, (uint32_t)32U);
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

exit_code main()
{
  C_String_print("[ECDSA SigVer]");
  C_String_print("\n");
  uint32_t len = sigver_vectors256_low.len;
  __Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_Test_Lowstarize_lbuffer_uint8_t_bool
  *vs0 = sigver_vectors256_low.b;
  for (uint32_t i = (uint32_t)0U; i < len; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
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
  for (uint32_t i = (uint32_t)0U; i < len0; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
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
  for (uint32_t i = (uint32_t)0U; i < len1; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
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
  for (uint32_t i = (uint32_t)0U; i < len2; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
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
  for (uint32_t i = (uint32_t)0U; i < len3; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
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
  for (uint32_t i = (uint32_t)0U; i < len4; i++)
  {
    LowStar_Printf_print_string("ECDSA Test ");
    LowStar_Printf_print_u32(i + (uint32_t)1U);
    LowStar_Printf_print_string("/");
    LowStar_Printf_print_u32(len4);
    LowStar_Printf_print_string("\n");
    test_siggen_512(vs[i]);
  }
  return EXIT_SUCCESS;
}

