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


#include "Hacl_Impl_QTesla.h"

/* SNIPPET_START: Hacl_Impl_QTesla_Constants_cshake128_qtesla */

static void
Hacl_Impl_QTesla_Constants_cshake128_qtesla(
  uint32_t input_len,
  uint8_t *input,
  uint16_t cstm,
  uint32_t output_len,
  uint8_t *output
)
{
  uint64_t s[25U] = { 0U };
  s[0U] = (uint64_t)0x10010001a801U | (uint64_t)cstm << (uint32_t)48U;
  Hacl_Impl_SHA3_state_permute(s);
  Hacl_Impl_SHA3_absorb(s, (uint32_t)168U, input_len, input, (uint8_t)0x04U);
  Hacl_Impl_SHA3_squeeze(s, (uint32_t)168U, output_len, output);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Constants_cshake128_qtesla */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_n */

static uint32_t Hacl_Impl_QTesla_Params_params_n = (uint32_t)512U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_n */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_k */

static uint32_t Hacl_Impl_QTesla_Params_params_k = (uint32_t)1U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_k */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_q */

static int32_t Hacl_Impl_QTesla_Params_params_q = (int32_t)4205569;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_q */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_h */

static uint32_t Hacl_Impl_QTesla_Params_params_h = (uint32_t)30U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_h */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_Le */

static uint32_t Hacl_Impl_QTesla_Params_params_Le = (uint32_t)1586U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_Le */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_Ls */

static uint32_t Hacl_Impl_QTesla_Params_params_Ls = (uint32_t)1586U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_Ls */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_B */

static int32_t Hacl_Impl_QTesla_Params_params_B = (int32_t)1048575;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_B */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_U */

static int32_t Hacl_Impl_QTesla_Params_params_U = (int32_t)1586;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_U */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_d */

static uint32_t Hacl_Impl_QTesla_Params_params_d = (uint32_t)21U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_d */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_genA */

static uint32_t Hacl_Impl_QTesla_Params_params_genA = (uint32_t)19U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_genA */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_qinv */

static int64_t Hacl_Impl_QTesla_Params_params_qinv = (int64_t)3098553343;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_qinv */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_q_log */

static uint32_t Hacl_Impl_QTesla_Params_params_q_log = (uint32_t)23U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_q_log */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_r2_invn */

static int64_t Hacl_Impl_QTesla_Params_params_r2_invn = (int64_t)113307;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_r2_invn */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_s_bits */

static uint32_t Hacl_Impl_QTesla_Params_params_s_bits = (uint32_t)10U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_s_bits */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_rejection */

static int32_t Hacl_Impl_QTesla_Params_params_rejection = (int32_t)1586;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_rejection */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_params_r */

static int64_t Hacl_Impl_QTesla_Params_params_r = (int64_t)1081347;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_params_r */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_crypto_hmbytes */

static uint32_t Hacl_Impl_QTesla_Params_crypto_hmbytes = (uint32_t)64U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_crypto_hmbytes */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_crypto_randombytes */

static uint32_t Hacl_Impl_QTesla_Params_crypto_randombytes = (uint32_t)32U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_crypto_randombytes */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_crypto_seedbytes */

static uint32_t Hacl_Impl_QTesla_Params_crypto_seedbytes = (uint32_t)32U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_crypto_seedbytes */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_crypto_c_bytes */

static uint32_t Hacl_Impl_QTesla_Params_crypto_c_bytes = (uint32_t)32U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_crypto_c_bytes */

/* SNIPPET_START: Hacl_Impl_QTesla_Params_crypto_bytes */

static uint32_t
Hacl_Impl_QTesla_Params_crypto_bytes =
  ((uint32_t)512U * (uint32_t)21U + (uint32_t)7U)
  / (uint32_t)8U
  + (uint32_t)32U;

/* SNIPPET_END: Hacl_Impl_QTesla_Params_crypto_bytes */

/* SNIPPET_START: Hacl_Impl_QTesla_Globals_reduce */

static int32_t Hacl_Impl_QTesla_Globals_reduce(int64_t a)
{
  uint64_t aUnsigned = (uint64_t)a;
  uint64_t params_qinv_unsigned = (uint64_t)Hacl_Impl_QTesla_Params_params_qinv;
  int64_t u = (int64_t)(aUnsigned * params_qinv_unsigned & (uint64_t)0xFFFFFFFFU);
  int64_t u2 = u * (int64_t)Hacl_Impl_QTesla_Params_params_q;
  int64_t a1 = a + u2;
  int64_t result = FStar_Int64_shift_arithmetic_right(a1, (uint32_t)32U);
  return (int32_t)result;
}

/* SNIPPET_END: Hacl_Impl_QTesla_Globals_reduce */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Poly_ntt */

static void Hacl_Impl_QTesla_Heuristic_Poly_ntt(int32_t *a, int32_t *w)
{
  uint32_t numoProblems = Hacl_Impl_QTesla_Params_params_n >> (uint32_t)1U;
  uint32_t jTwiddle = (uint32_t)0U;
  while (numoProblems > (uint32_t)0U)
  {
    uint32_t uu____0 = numoProblems;
    uint32_t jFirst = (uint32_t)0U;
    while (jFirst < Hacl_Impl_QTesla_Params_params_n)
    {
      uint32_t jTwiddleVal = jTwiddle;
      int32_t wj = w[jTwiddleVal];
      jTwiddle = jTwiddleVal + (uint32_t)1U;
      uint32_t uu____1 = jFirst;
      uint32_t jBuf = uu____1;
      while (jBuf < uu____1 + uu____0)
      {
        uint32_t j = jBuf;
        uint32_t jNumo = j + uu____0;
        int32_t ajNumo = a[jNumo];
        int64_t product = (int64_t)wj * (int64_t)ajNumo;
        int32_t temp = Hacl_Impl_QTesla_Globals_reduce(product);
        int32_t aj = a[j];
        a[jNumo] = aj - temp;
        a[j] = temp + aj;
        jBuf = j + (uint32_t)1U;
      }
      uint32_t j = jBuf;
      jFirst = j + uu____0;
    }
    numoProblems = numoProblems >> (uint32_t)1U;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Poly_ntt */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Poly_poly_pointwise */

static void
Hacl_Impl_QTesla_Heuristic_Poly_poly_pointwise(int32_t *result, int32_t *x, int32_t *y)
{
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t xi = x[i];
    int32_t yi = y[i];
    result[i] = Hacl_Impl_QTesla_Globals_reduce((int64_t)xi * (int64_t)yi);
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Poly_poly_pointwise */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Poly_poly_add */

static void Hacl_Impl_QTesla_Heuristic_Poly_poly_add(int32_t *result, int32_t *x, int32_t *y)
{
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    result[i] = x[i] + y[i];
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Poly_poly_add */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Poly_poly_add_correct */

static void
Hacl_Impl_QTesla_Heuristic_Poly_poly_add_correct(int32_t *result, int32_t *x, int32_t *y)
{
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t temp = x[i] + y[i];
    int32_t
    temp1 =
      temp
      +
        (FStar_Int32_shift_arithmetic_right(temp,
          (uint32_t)32U - (uint32_t)1U)
        & Hacl_Impl_QTesla_Params_params_q);
    int32_t temp2 = temp1 - Hacl_Impl_QTesla_Params_params_q;
    int32_t
    temp3 =
      temp2
      +
        (FStar_Int32_shift_arithmetic_right(temp2,
          (uint32_t)32U - (uint32_t)1U)
        & Hacl_Impl_QTesla_Params_params_q);
    result[i] = temp3;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Poly_poly_add_correct */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_correct */

static void
Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_correct(int32_t *result, int32_t *x, int32_t *y)
{
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t temp = x[i] - y[i];
    int32_t
    temp1 =
      temp
      +
        (FStar_Int32_shift_arithmetic_right(temp,
          (uint32_t)32U - (uint32_t)1U)
        & Hacl_Impl_QTesla_Params_params_q);
    result[i] = temp1;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_correct */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_reduce */

static void
Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_reduce(int32_t *result, int32_t *x, int32_t *y)
{
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t xi = x[i];
    int32_t yi = y[i];
    result[i] =
      Hacl_Impl_QTesla_Globals_reduce(Hacl_Impl_QTesla_Params_params_r * ((int64_t)xi - (int64_t)yi));
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_reduce */

/* SNIPPET_START: Hacl_Impl_QTesla_Poly_nttinv_middlefor */

static void
Hacl_Impl_QTesla_Poly_nttinv_middlefor(
  uint32_t numoProblems,
  uint32_t *jTwiddle,
  int32_t *w,
  int32_t *a
)
{
  uint32_t jFirst = (uint32_t)0U;
  while (jFirst < Hacl_Impl_QTesla_Params_params_n)
  {
    uint32_t jTwiddleVal = jTwiddle[0U];
    int32_t wj = w[jTwiddleVal];
    jTwiddle[0U] = jTwiddleVal + (uint32_t)1U;
    uint32_t uu____0 = jFirst;
    uint32_t jBuf = uu____0;
    while (jBuf < uu____0 + numoProblems)
    {
      uint32_t j = jBuf;
      uint32_t jNumo = j + numoProblems;
      int32_t temp = a[j];
      int32_t ajNumo = a[jNumo];
      a[j] = temp + ajNumo;
      a[jNumo] = Hacl_Impl_QTesla_Globals_reduce((int64_t)wj * (int64_t)(temp - ajNumo));
      jBuf = j + (uint32_t)1U;
    }
    uint32_t j = jBuf;
    jFirst = j + numoProblems;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Poly_nttinv_middlefor */

/* SNIPPET_START: Hacl_Impl_QTesla_Poly_nttinv */

static void Hacl_Impl_QTesla_Poly_nttinv(int32_t *a, int32_t *w)
{
  uint32_t numoProblems = (uint32_t)1U;
  uint32_t jTwiddle = (uint32_t)0U;
  while (numoProblems < Hacl_Impl_QTesla_Params_params_n)
  {
    Hacl_Impl_QTesla_Poly_nttinv_middlefor(numoProblems, &jTwiddle, w, a);
    numoProblems = numoProblems * (uint32_t)2U;
  }
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)2U;
    i = i + (uint32_t)1U)
  {
    int32_t ai = a[i];
    a[i] = Hacl_Impl_QTesla_Globals_reduce(Hacl_Impl_QTesla_Params_params_r * (int64_t)ai);
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Poly_nttinv */

/* SNIPPET_START: Hacl_Impl_QTesla_Poly_poly_ntt */

static void Hacl_Impl_QTesla_Poly_poly_ntt(int32_t *x_ntt, int32_t *x)
{
  int32_t
  zeta1[512U] =
    {
      (int32_t)3359531, (int32_t)2189080, (int32_t)370173, (int32_t)677362, (int32_t)3132616,
      (int32_t)2989204, (int32_t)2362181, (int32_t)1720831, (int32_t)1203721, (int32_t)3239574,
      (int32_t)641414, (int32_t)3932234, (int32_t)3634017, (int32_t)2251707, (int32_t)355329,
      (int32_t)4152265, (int32_t)1356023, (int32_t)4021436, (int32_t)1465601, (int32_t)4145892,
      (int32_t)3348341, (int32_t)675693, (int32_t)1598775, (int32_t)2799365, (int32_t)3336234,
      (int32_t)3856839, (int32_t)603157, (int32_t)1381183, (int32_t)1069471, (int32_t)2142038,
      (int32_t)2877387, (int32_t)2653969, (int32_t)2055310, (int32_t)3837123, (int32_t)3141231,
      (int32_t)1951522, (int32_t)2375048, (int32_t)445122, (int32_t)1689285, (int32_t)3664328,
      (int32_t)676319, (int32_t)3844199, (int32_t)3669724, (int32_t)1009639, (int32_t)3666694,
      (int32_t)1585701, (int32_t)2102892, (int32_t)966523, (int32_t)4069555, (int32_t)3246046,
      (int32_t)846643, (int32_t)2088895, (int32_t)4068915, (int32_t)3715722, (int32_t)4119007,
      (int32_t)230501, (int32_t)1626667, (int32_t)2119752, (int32_t)1171284, (int32_t)3153846,
      (int32_t)17941, (int32_t)1316589, (int32_t)1814059, (int32_t)3185686, (int32_t)1183551,
      (int32_t)2533671, (int32_t)4152595, (int32_t)2616162, (int32_t)3015757, (int32_t)194860,
      (int32_t)1601807, (int32_t)1271569, (int32_t)139534, (int32_t)2581874, (int32_t)2183200,
      (int32_t)2060697, (int32_t)1036874, (int32_t)646550, (int32_t)2823563, (int32_t)3312274,
      (int32_t)391700, (int32_t)99391, (int32_t)638903, (int32_t)2397164, (int32_t)3924868,
      (int32_t)3315551, (int32_t)1170767, (int32_t)422539, (int32_t)1801679, (int32_t)166402,
      (int32_t)742283, (int32_t)222557, (int32_t)522210, (int32_t)3415900, (int32_t)177835,
      (int32_t)3243355, (int32_t)4196855, (int32_t)1821376, (int32_t)1290490, (int32_t)3624896,
      (int32_t)1546898, (int32_t)1282351, (int32_t)3960516, (int32_t)835944, (int32_t)2251927,
      (int32_t)90910, (int32_t)3034838, (int32_t)4082965, (int32_t)2311377, (int32_t)3512216,
      (int32_t)2652413, (int32_t)2191140, (int32_t)302935, (int32_t)3866228, (int32_t)2007511,
      (int32_t)744185, (int32_t)2801160, (int32_t)3993630, (int32_t)592962, (int32_t)795067,
      (int32_t)2822609, (int32_t)3471782, (int32_t)3710854, (int32_t)1824985, (int32_t)1495256,
      (int32_t)3906591, (int32_t)3111335, (int32_t)3902620, (int32_t)11234, (int32_t)1586236,
      (int32_t)3698245, (int32_t)492808, (int32_t)2729660, (int32_t)3369937, (int32_t)1869963,
      (int32_t)7244, (int32_t)1453951, (int32_t)1757304, (int32_t)1005437, (int32_t)3668653,
      (int32_t)1821321, (int32_t)4203686, (int32_t)1192473, (int32_t)113408, (int32_t)2904803,
      (int32_t)1346735, (int32_t)4161890, (int32_t)711442, (int32_t)4020959, (int32_t)1164150,
      (int32_t)2139014, (int32_t)4134238, (int32_t)731747, (int32_t)3856202, (int32_t)2351090,
      (int32_t)3382729, (int32_t)2644693, (int32_t)617098, (int32_t)2796766, (int32_t)1911274,
      (int32_t)552932, (int32_t)2476095, (int32_t)1801797, (int32_t)1381577, (int32_t)2338697,
      (int32_t)1336590, (int32_t)2798544, (int32_t)459121, (int32_t)3555631, (int32_t)741068,
      (int32_t)2302686, (int32_t)1883916, (int32_t)2148181, (int32_t)2471691, (int32_t)2174195,
      (int32_t)1684042, (int32_t)3266036, (int32_t)227434, (int32_t)4107207, (int32_t)2910899,
      (int32_t)3427718, (int32_t)2011049, (int32_t)2706372, (int32_t)4182237, (int32_t)1243355,
      (int32_t)2908998, (int32_t)15068, (int32_t)1966206, (int32_t)2157082, (int32_t)4114100,
      (int32_t)1846352, (int32_t)230880, (int32_t)1161075, (int32_t)1259576, (int32_t)1212857,
      (int32_t)1697580, (int32_t)39500, (int32_t)3079648, (int32_t)2529577, (int32_t)2082167,
      (int32_t)50282, (int32_t)476606, (int32_t)1494601, (int32_t)1334236, (int32_t)3349015,
      (int32_t)1600445, (int32_t)413060, (int32_t)3104844, (int32_t)139283, (int32_t)1688398,
      (int32_t)3230017, (int32_t)1009712, (int32_t)614253, (int32_t)2973529, (int32_t)2077610,
      (int32_t)2218429, (int32_t)4185344, (int32_t)254428, (int32_t)506799, (int32_t)196179,
      (int32_t)3310395, (int32_t)4183346, (int32_t)3897905, (int32_t)2234639, (int32_t)1859699,
      (int32_t)3322900, (int32_t)2151737, (int32_t)1904476, (int32_t)2457045, (int32_t)383438,
      (int32_t)2543045, (int32_t)2985636, (int32_t)731083, (int32_t)1609871, (int32_t)2171434,
      (int32_t)535413, (int32_t)2666041, (int32_t)405934, (int32_t)3303186, (int32_t)802974,
      (int32_t)3573046, (int32_t)1760267, (int32_t)2758359, (int32_t)2102800, (int32_t)1512274,
      (int32_t)3981750, (int32_t)1838169, (int32_t)2101846, (int32_t)1363757, (int32_t)1342163,
      (int32_t)3608830, (int32_t)321523, (int32_t)1072908, (int32_t)855117, (int32_t)1679204,
      (int32_t)3624675, (int32_t)3183259, (int32_t)2438624, (int32_t)407591, (int32_t)1549799,
      (int32_t)490068, (int32_t)2769318, (int32_t)3185950, (int32_t)990968, (int32_t)3700398,
      (int32_t)2715638, (int32_t)3672301, (int32_t)3203080, (int32_t)1775408, (int32_t)2071611,
      (int32_t)778637, (int32_t)2335351, (int32_t)3317014, (int32_t)3768001, (int32_t)571163,
      (int32_t)2618746, (int32_t)1028702, (int32_t)3174131, (int32_t)764504, (int32_t)1386439,
      (int32_t)4188876, (int32_t)1131998, (int32_t)1057083, (int32_t)39651, (int32_t)2588805,
      (int32_t)2519763, (int32_t)3838931, (int32_t)4130059, (int32_t)1893001, (int32_t)2066802,
      (int32_t)572208, (int32_t)2529031, (int32_t)220967, (int32_t)3880345, (int32_t)1820301,
      (int32_t)2205978, (int32_t)3036090, (int32_t)1648541, (int32_t)4012391, (int32_t)1432533,
      (int32_t)3068186, (int32_t)1645476, (int32_t)1397186, (int32_t)2112498, (int32_t)4168213,
      (int32_t)1234734, (int32_t)1648052, (int32_t)1803157, (int32_t)2011730, (int32_t)1648875,
      (int32_t)2547914, (int32_t)437873, (int32_t)2460774, (int32_t)3403214, (int32_t)2690605,
      (int32_t)2567052, (int32_t)739775, (int32_t)1854855, (int32_t)520305, (int32_t)3661464,
      (int32_t)1120944, (int32_t)1245195, (int32_t)1147367, (int32_t)2571134, (int32_t)696367,
      (int32_t)3009976, (int32_t)834907, (int32_t)1691662, (int32_t)1384090, (int32_t)2795844,
      (int32_t)1813845, (int32_t)3425954, (int32_t)4194068, (int32_t)1317042, (int32_t)2056507,
      (int32_t)470026, (int32_t)3097617, (int32_t)2678203, (int32_t)3077203, (int32_t)2116013,
      (int32_t)4155561, (int32_t)2844478, (int32_t)1467696, (int32_t)4150754, (int32_t)992951,
      (int32_t)471101, (int32_t)4062883, (int32_t)1584992, (int32_t)2252609, (int32_t)3322854,
      (int32_t)1597940, (int32_t)3581574, (int32_t)1115369, (int32_t)4153697, (int32_t)3236495,
      (int32_t)4075586, (int32_t)2066340, (int32_t)1262360, (int32_t)2730720, (int32_t)3664692,
      (int32_t)2681478, (int32_t)2929295, (int32_t)3831713, (int32_t)3683420, (int32_t)2511172,
      (int32_t)3689552, (int32_t)2645837, (int32_t)2414330, (int32_t)857564, (int32_t)3703853,
      (int32_t)468246, (int32_t)1574274, (int32_t)3590547, (int32_t)2348366, (int32_t)1565207,
      (int32_t)1815326, (int32_t)2508730, (int32_t)1749217, (int32_t)465029, (int32_t)260794,
      (int32_t)1630097, (int32_t)3019607, (int32_t)3872759, (int32_t)1053481, (int32_t)3958758,
      (int32_t)3415305, (int32_t)54348, (int32_t)2516, (int32_t)3045515, (int32_t)3011542,
      (int32_t)1951553, (int32_t)1882613, (int32_t)1729323, (int32_t)801736, (int32_t)3662451,
      (int32_t)909634, (int32_t)2949838, (int32_t)2598628, (int32_t)1652685, (int32_t)1945350,
      (int32_t)3221627, (int32_t)2879417, (int32_t)2732226, (int32_t)3883548, (int32_t)1891328,
      (int32_t)3215710, (int32_t)3159721, (int32_t)1318941, (int32_t)2153764, (int32_t)1870381,
      (int32_t)4039453, (int32_t)3375151, (int32_t)2655219, (int32_t)4089723, (int32_t)1388508,
      (int32_t)3436490, (int32_t)3956335, (int32_t)2748982, (int32_t)4111030, (int32_t)328986,
      (int32_t)1780674, (int32_t)2570336, (int32_t)2608795, (int32_t)2600572, (int32_t)2748827,
      (int32_t)790335, (int32_t)1988956, (int32_t)3946950, (int32_t)1789942, (int32_t)710384,
      (int32_t)3900335, (int32_t)457139, (int32_t)2550557, (int32_t)3042298, (int32_t)1952120,
      (int32_t)1998308, (int32_t)259999, (int32_t)2361900, (int32_t)119023, (int32_t)3680445,
      (int32_t)1893737, (int32_t)4050016, (int32_t)2696786, (int32_t)567472, (int32_t)3085466,
      (int32_t)1580931, (int32_t)1360307, (int32_t)3075154, (int32_t)904205, (int32_t)1306381,
      (int32_t)3257843, (int32_t)2926984, (int32_t)2065676, (int32_t)3221598, (int32_t)2551064,
      (int32_t)1580354, (int32_t)1636374, (int32_t)699891, (int32_t)1821560, (int32_t)670885,
      (int32_t)947258, (int32_t)2908840, (int32_t)3049868, (int32_t)1038075, (int32_t)1701447,
      (int32_t)2439140, (int32_t)2048478, (int32_t)3183312, (int32_t)2224644, (int32_t)320592,
      (int32_t)3304074, (int32_t)2611056, (int32_t)422256, (int32_t)1752180, (int32_t)2217951,
      (int32_t)2900510, (int32_t)1321050, (int32_t)2797671, (int32_t)312886, (int32_t)2624042,
      (int32_t)3166863, (int32_t)908176, (int32_t)24947, (int32_t)152205, (int32_t)2891981,
      (int32_t)189908, (int32_t)1959427, (int32_t)1365987, (int32_t)2071767, (int32_t)1932065,
      (int32_t)3185693, (int32_t)3889374, (int32_t)3644713, (int32_t)79765, (int32_t)969178,
      (int32_t)11268, (int32_t)1992233, (int32_t)1579325, (int32_t)1224905, (int32_t)3741957,
      (int32_t)1894871, (int32_t)3060100, (int32_t)1787540, (int32_t)4194180, (int32_t)1396587,
      (int32_t)2745514, (int32_t)26822, (int32_t)695515, (int32_t)2348201, (int32_t)249698,
      (int32_t)2988539, (int32_t)1081347
    };
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    x_ntt[i] = x[i];
  }
  Hacl_Impl_QTesla_Heuristic_Poly_ntt(x_ntt, zeta1);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Poly_poly_ntt */

/* SNIPPET_START: Hacl_Impl_QTesla_Poly_poly_mul */

static void Hacl_Impl_QTesla_Poly_poly_mul(int32_t *result, int32_t *x, int32_t *y)
{
  int32_t
  zetainv[512U] =
    {
      (int32_t)1217030, (int32_t)3955871, (int32_t)1857368, (int32_t)3510054, (int32_t)4178747,
      (int32_t)1460055, (int32_t)2808982, (int32_t)11389, (int32_t)2418029, (int32_t)1145469,
      (int32_t)2310698, (int32_t)463612, (int32_t)2980664, (int32_t)2626244, (int32_t)2213336,
      (int32_t)4194301, (int32_t)3236391, (int32_t)4125804, (int32_t)560856, (int32_t)316195,
      (int32_t)1019876, (int32_t)2273504, (int32_t)2133802, (int32_t)2839582, (int32_t)2246142,
      (int32_t)4015661, (int32_t)1313588, (int32_t)4053364, (int32_t)4180622, (int32_t)3297393,
      (int32_t)1038706, (int32_t)1581527, (int32_t)3892683, (int32_t)1407898, (int32_t)2884519,
      (int32_t)1305059, (int32_t)1987618, (int32_t)2453389, (int32_t)3783313, (int32_t)1594513,
      (int32_t)901495, (int32_t)3884977, (int32_t)1980925, (int32_t)1022257, (int32_t)2157091,
      (int32_t)1766429, (int32_t)2504122, (int32_t)3167494, (int32_t)1155701, (int32_t)1296729,
      (int32_t)3258311, (int32_t)3534684, (int32_t)2384009, (int32_t)3505678, (int32_t)2569195,
      (int32_t)2625215, (int32_t)1654505, (int32_t)983971, (int32_t)2139893, (int32_t)1278585,
      (int32_t)947726, (int32_t)2899188, (int32_t)3301364, (int32_t)1130415, (int32_t)2845262,
      (int32_t)2624638, (int32_t)1120103, (int32_t)3638097, (int32_t)1508783, (int32_t)155553,
      (int32_t)2311832, (int32_t)525124, (int32_t)4086546, (int32_t)1843669, (int32_t)3945570,
      (int32_t)2207261, (int32_t)2253449, (int32_t)1163271, (int32_t)1655012, (int32_t)3748430,
      (int32_t)305234, (int32_t)3495185, (int32_t)2415627, (int32_t)258619, (int32_t)2216613,
      (int32_t)3415234, (int32_t)1456742, (int32_t)1604997, (int32_t)1596774, (int32_t)1635233,
      (int32_t)2424895, (int32_t)3876583, (int32_t)94539, (int32_t)1456587, (int32_t)249234,
      (int32_t)769079, (int32_t)2817061, (int32_t)115846, (int32_t)1550350, (int32_t)830418,
      (int32_t)166116, (int32_t)2335188, (int32_t)2051805, (int32_t)2886628, (int32_t)1045848,
      (int32_t)989859, (int32_t)2314241, (int32_t)322021, (int32_t)1473343, (int32_t)1326152,
      (int32_t)983942, (int32_t)2260219, (int32_t)2552884, (int32_t)1606941, (int32_t)1255731,
      (int32_t)3295935, (int32_t)543118, (int32_t)3403833, (int32_t)2476246, (int32_t)2322956,
      (int32_t)2254016, (int32_t)1194027, (int32_t)1160054, (int32_t)4203053, (int32_t)4151221,
      (int32_t)790264, (int32_t)246811, (int32_t)3152088, (int32_t)332810, (int32_t)1185962,
      (int32_t)2575472, (int32_t)3944775, (int32_t)3740540, (int32_t)2456352, (int32_t)1696839,
      (int32_t)2390243, (int32_t)2640362, (int32_t)1857203, (int32_t)615022, (int32_t)2631295,
      (int32_t)3737323, (int32_t)501716, (int32_t)3348005, (int32_t)1791239, (int32_t)1559732,
      (int32_t)516017, (int32_t)1694397, (int32_t)522149, (int32_t)373856, (int32_t)1276274,
      (int32_t)1524091, (int32_t)540877, (int32_t)1474849, (int32_t)2943209, (int32_t)2139229,
      (int32_t)129983, (int32_t)969074, (int32_t)51872, (int32_t)3090200, (int32_t)623995,
      (int32_t)2607629, (int32_t)882715, (int32_t)1952960, (int32_t)2620577, (int32_t)142686,
      (int32_t)3734468, (int32_t)3212618, (int32_t)54815, (int32_t)2737873, (int32_t)1361091,
      (int32_t)50008, (int32_t)2089556, (int32_t)1128366, (int32_t)1527366, (int32_t)1107952,
      (int32_t)3735543, (int32_t)2149062, (int32_t)2888527, (int32_t)11501, (int32_t)779615,
      (int32_t)2391724, (int32_t)1409725, (int32_t)2821479, (int32_t)2513907, (int32_t)3370662,
      (int32_t)1195593, (int32_t)3509202, (int32_t)1634435, (int32_t)3058202, (int32_t)2960374,
      (int32_t)3084625, (int32_t)544105, (int32_t)3685264, (int32_t)2350714, (int32_t)3465794,
      (int32_t)1638517, (int32_t)1514964, (int32_t)802355, (int32_t)1744795, (int32_t)3767696,
      (int32_t)1657655, (int32_t)2556694, (int32_t)2193839, (int32_t)2402412, (int32_t)2557517,
      (int32_t)2970835, (int32_t)37356, (int32_t)2093071, (int32_t)2808383, (int32_t)2560093,
      (int32_t)1137383, (int32_t)2773036, (int32_t)193178, (int32_t)2557028, (int32_t)1169479,
      (int32_t)1999591, (int32_t)2385268, (int32_t)325224, (int32_t)3984602, (int32_t)1676538,
      (int32_t)3633361, (int32_t)2138767, (int32_t)2312568, (int32_t)75510, (int32_t)366638,
      (int32_t)1685806, (int32_t)1616764, (int32_t)4165918, (int32_t)3148486, (int32_t)3073571,
      (int32_t)16693, (int32_t)2819130, (int32_t)3441065, (int32_t)1031438, (int32_t)3176867,
      (int32_t)1586823, (int32_t)3634406, (int32_t)437568, (int32_t)888555, (int32_t)1870218,
      (int32_t)3426932, (int32_t)2133958, (int32_t)2430161, (int32_t)1002489, (int32_t)533268,
      (int32_t)1489931, (int32_t)505171, (int32_t)3214601, (int32_t)1019619, (int32_t)1436251,
      (int32_t)3715501, (int32_t)2655770, (int32_t)3797978, (int32_t)1766945, (int32_t)1022310,
      (int32_t)580894, (int32_t)2526365, (int32_t)3350452, (int32_t)3132661, (int32_t)3884046,
      (int32_t)596739, (int32_t)2863406, (int32_t)2841812, (int32_t)2103723, (int32_t)2367400,
      (int32_t)223819, (int32_t)2693295, (int32_t)2102769, (int32_t)1447210, (int32_t)2445302,
      (int32_t)632523, (int32_t)3402595, (int32_t)902383, (int32_t)3799635, (int32_t)1539528,
      (int32_t)3670156, (int32_t)2034135, (int32_t)2595698, (int32_t)3474486, (int32_t)1219933,
      (int32_t)1662524, (int32_t)3822131, (int32_t)1748524, (int32_t)2301093, (int32_t)2053832,
      (int32_t)882669, (int32_t)2345870, (int32_t)1970930, (int32_t)307664, (int32_t)22223,
      (int32_t)895174, (int32_t)4009390, (int32_t)3698770, (int32_t)3951141, (int32_t)20225,
      (int32_t)1987140, (int32_t)2127959, (int32_t)1232040, (int32_t)3591316, (int32_t)3195857,
      (int32_t)975552, (int32_t)2517171, (int32_t)4066286, (int32_t)1100725, (int32_t)3792509,
      (int32_t)2605124, (int32_t)856554, (int32_t)2871333, (int32_t)2710968, (int32_t)3728963,
      (int32_t)4155287, (int32_t)2123402, (int32_t)1675992, (int32_t)1125921, (int32_t)4166069,
      (int32_t)2507989, (int32_t)2992712, (int32_t)2945993, (int32_t)3044494, (int32_t)3974689,
      (int32_t)2359217, (int32_t)91469, (int32_t)2048487, (int32_t)2239363, (int32_t)4190501,
      (int32_t)1296571, (int32_t)2962214, (int32_t)23332, (int32_t)1499197, (int32_t)2194520,
      (int32_t)777851, (int32_t)1294670, (int32_t)98362, (int32_t)3978135, (int32_t)939533,
      (int32_t)2521527, (int32_t)2031374, (int32_t)1733878, (int32_t)2057388, (int32_t)2321653,
      (int32_t)1902883, (int32_t)3464501, (int32_t)649938, (int32_t)3746448, (int32_t)1407025,
      (int32_t)2868979, (int32_t)1866872, (int32_t)2823992, (int32_t)2403772, (int32_t)1729474,
      (int32_t)3652637, (int32_t)2294295, (int32_t)1408803, (int32_t)3588471, (int32_t)1560876,
      (int32_t)822840, (int32_t)1854479, (int32_t)349367, (int32_t)3473822, (int32_t)71331,
      (int32_t)2066555, (int32_t)3041419, (int32_t)184610, (int32_t)3494127, (int32_t)43679,
      (int32_t)2858834, (int32_t)1300766, (int32_t)4092161, (int32_t)3013096, (int32_t)1883,
      (int32_t)2384248, (int32_t)536916, (int32_t)3200132, (int32_t)2448265, (int32_t)2751618,
      (int32_t)4198325, (int32_t)2335606, (int32_t)835632, (int32_t)1475909, (int32_t)3712761,
      (int32_t)507324, (int32_t)2619333, (int32_t)4194335, (int32_t)302949, (int32_t)1094234,
      (int32_t)298978, (int32_t)2710313, (int32_t)2380584, (int32_t)494715, (int32_t)733787,
      (int32_t)1382960, (int32_t)3410502, (int32_t)3612607, (int32_t)211939, (int32_t)1404409,
      (int32_t)3461384, (int32_t)2198058, (int32_t)339341, (int32_t)3902634, (int32_t)2014429,
      (int32_t)1553156, (int32_t)693353, (int32_t)1894192, (int32_t)122604, (int32_t)1170731,
      (int32_t)4114659, (int32_t)1953642, (int32_t)3369625, (int32_t)245053, (int32_t)2923218,
      (int32_t)2658671, (int32_t)580673, (int32_t)2915079, (int32_t)2384193, (int32_t)8714,
      (int32_t)962214, (int32_t)4027734, (int32_t)789669, (int32_t)3683359, (int32_t)3983012,
      (int32_t)3463286, (int32_t)4039167, (int32_t)2403890, (int32_t)3783030, (int32_t)3034802,
      (int32_t)890018, (int32_t)280701, (int32_t)1808405, (int32_t)3566666, (int32_t)4106178,
      (int32_t)3813869, (int32_t)893295, (int32_t)1382006, (int32_t)3559019, (int32_t)3168695,
      (int32_t)2144872, (int32_t)2022369, (int32_t)1623695, (int32_t)4066035, (int32_t)2934000,
      (int32_t)2603762, (int32_t)4010709, (int32_t)1189812, (int32_t)1589407, (int32_t)52974,
      (int32_t)1671898, (int32_t)3022018, (int32_t)1019883, (int32_t)2391510, (int32_t)2888980,
      (int32_t)4187628, (int32_t)1051723, (int32_t)3034285, (int32_t)2085817, (int32_t)2578902,
      (int32_t)3975068, (int32_t)86562, (int32_t)489847, (int32_t)136654, (int32_t)2116674,
      (int32_t)3358926, (int32_t)959523, (int32_t)136014, (int32_t)3239046, (int32_t)2102677,
      (int32_t)2619868, (int32_t)538875, (int32_t)3195930, (int32_t)535845, (int32_t)361370,
      (int32_t)3529250, (int32_t)541241, (int32_t)2516284, (int32_t)3760447, (int32_t)1830521,
      (int32_t)2254047, (int32_t)1064338, (int32_t)368446, (int32_t)2150259, (int32_t)1551600,
      (int32_t)1328182, (int32_t)2063531, (int32_t)3136098, (int32_t)2824386, (int32_t)3602412,
      (int32_t)348730, (int32_t)869335, (int32_t)1406204, (int32_t)2606794, (int32_t)3529876,
      (int32_t)857228, (int32_t)59677, (int32_t)2739968, (int32_t)184133, (int32_t)2849546,
      (int32_t)53304, (int32_t)3850240, (int32_t)1953862, (int32_t)571552, (int32_t)273335,
      (int32_t)3564155, (int32_t)965995, (int32_t)3001848, (int32_t)2484738, (int32_t)1843388,
      (int32_t)1216365, (int32_t)1072953, (int32_t)3528207, (int32_t)3835396, (int32_t)2016489,
      (int32_t)846038, (int32_t)3124222
    };
  Hacl_Impl_QTesla_Heuristic_Poly_poly_pointwise(result, x, y);
  Hacl_Impl_QTesla_Poly_nttinv(result, zetainv);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Poly_poly_mul */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Pack_encode_pk */

static void Hacl_Impl_QTesla_Heuristic_Pack_encode_pk(uint8_t *pk, int32_t *t, uint8_t *seedA)
{
  uint32_t i = (uint32_t)0U;
  uint32_t j = (uint32_t)0U;
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)32U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t j1 = i0 * (uint32_t)32U;
    uint32_t i1 = i0 * Hacl_Impl_QTesla_Params_params_q_log;
    int32_t tj0 = t[j1 + (uint32_t)0U];
    int32_t tj1 = t[j1 + (uint32_t)1U];
    int32_t tj2 = t[j1 + (uint32_t)2U];
    int32_t tj3 = t[j1 + (uint32_t)3U];
    int32_t tj4 = t[j1 + (uint32_t)4U];
    int32_t tj5 = t[j1 + (uint32_t)5U];
    int32_t tj6 = t[j1 + (uint32_t)6U];
    int32_t tj7 = t[j1 + (uint32_t)7U];
    int32_t tj8 = t[j1 + (uint32_t)8U];
    int32_t tj9 = t[j1 + (uint32_t)9U];
    int32_t tj10 = t[j1 + (uint32_t)10U];
    int32_t tj11 = t[j1 + (uint32_t)11U];
    int32_t tj12 = t[j1 + (uint32_t)12U];
    int32_t tj13 = t[j1 + (uint32_t)13U];
    int32_t tj14 = t[j1 + (uint32_t)14U];
    int32_t tj15 = t[j1 + (uint32_t)15U];
    int32_t tj16 = t[j1 + (uint32_t)16U];
    int32_t tj17 = t[j1 + (uint32_t)17U];
    int32_t tj18 = t[j1 + (uint32_t)18U];
    int32_t tj19 = t[j1 + (uint32_t)19U];
    int32_t tj20 = t[j1 + (uint32_t)20U];
    int32_t tj21 = t[j1 + (uint32_t)21U];
    int32_t tj22 = t[j1 + (uint32_t)22U];
    int32_t tj23 = t[j1 + (uint32_t)23U];
    int32_t tj24 = t[j1 + (uint32_t)24U];
    int32_t tj25 = t[j1 + (uint32_t)25U];
    int32_t tj26 = t[j1 + (uint32_t)26U];
    int32_t tj27 = t[j1 + (uint32_t)27U];
    int32_t tj28 = t[j1 + (uint32_t)28U];
    int32_t tj29 = t[j1 + (uint32_t)29U];
    int32_t tj30 = t[j1 + (uint32_t)30U];
    int32_t tj31 = t[j1 + (uint32_t)31U];
    int32_t x2 = tj0 | (int32_t)((uint32_t)tj1 << (uint32_t)23U);
    store32_le(pk + (i1 + (uint32_t)0U) * (uint32_t)4U, (uint32_t)x2);
    int32_t
    x20 =
      FStar_Int32_shift_arithmetic_right(tj1,
        (uint32_t)9U)
      | (int32_t)((uint32_t)tj2 << (uint32_t)14U);
    store32_le(pk + (i1 + (uint32_t)1U) * (uint32_t)4U, (uint32_t)x20);
    int32_t
    x21 =
      (FStar_Int32_shift_arithmetic_right(tj2,
        (uint32_t)18U)
      | (int32_t)((uint32_t)tj3 << (uint32_t)5U))
      | (int32_t)((uint32_t)tj4 << (uint32_t)28U);
    store32_le(pk + (i1 + (uint32_t)2U) * (uint32_t)4U, (uint32_t)x21);
    int32_t
    x22 =
      FStar_Int32_shift_arithmetic_right(tj4,
        (uint32_t)4U)
      | (int32_t)((uint32_t)tj5 << (uint32_t)19U);
    store32_le(pk + (i1 + (uint32_t)3U) * (uint32_t)4U, (uint32_t)x22);
    int32_t
    x23 =
      FStar_Int32_shift_arithmetic_right(tj5,
        (uint32_t)13U)
      | (int32_t)((uint32_t)tj6 << (uint32_t)10U);
    store32_le(pk + (i1 + (uint32_t)4U) * (uint32_t)4U, (uint32_t)x23);
    int32_t
    x24 =
      (FStar_Int32_shift_arithmetic_right(tj6,
        (uint32_t)22U)
      | (int32_t)((uint32_t)tj7 << (uint32_t)1U))
      | (int32_t)((uint32_t)tj8 << (uint32_t)24U);
    store32_le(pk + (i1 + (uint32_t)5U) * (uint32_t)4U, (uint32_t)x24);
    int32_t
    x25 =
      FStar_Int32_shift_arithmetic_right(tj8,
        (uint32_t)8U)
      | (int32_t)((uint32_t)tj9 << (uint32_t)15U);
    store32_le(pk + (i1 + (uint32_t)6U) * (uint32_t)4U, (uint32_t)x25);
    int32_t
    x26 =
      (FStar_Int32_shift_arithmetic_right(tj9,
        (uint32_t)17U)
      | (int32_t)((uint32_t)tj10 << (uint32_t)6U))
      | (int32_t)((uint32_t)tj11 << (uint32_t)29U);
    store32_le(pk + (i1 + (uint32_t)7U) * (uint32_t)4U, (uint32_t)x26);
    int32_t
    x27 =
      FStar_Int32_shift_arithmetic_right(tj11,
        (uint32_t)3U)
      | (int32_t)((uint32_t)tj12 << (uint32_t)20U);
    store32_le(pk + (i1 + (uint32_t)8U) * (uint32_t)4U, (uint32_t)x27);
    int32_t
    x28 =
      FStar_Int32_shift_arithmetic_right(tj12,
        (uint32_t)12U)
      | (int32_t)((uint32_t)tj13 << (uint32_t)11U);
    store32_le(pk + (i1 + (uint32_t)9U) * (uint32_t)4U, (uint32_t)x28);
    int32_t
    x29 =
      (FStar_Int32_shift_arithmetic_right(tj13,
        (uint32_t)21U)
      | (int32_t)((uint32_t)tj14 << (uint32_t)2U))
      | (int32_t)((uint32_t)tj15 << (uint32_t)25U);
    store32_le(pk + (i1 + (uint32_t)10U) * (uint32_t)4U, (uint32_t)x29);
    int32_t
    x210 =
      FStar_Int32_shift_arithmetic_right(tj15,
        (uint32_t)7U)
      | (int32_t)((uint32_t)tj16 << (uint32_t)16U);
    store32_le(pk + (i1 + (uint32_t)11U) * (uint32_t)4U, (uint32_t)x210);
    int32_t
    x211 =
      (FStar_Int32_shift_arithmetic_right(tj16,
        (uint32_t)16U)
      | (int32_t)((uint32_t)tj17 << (uint32_t)7U))
      | (int32_t)((uint32_t)tj18 << (uint32_t)30U);
    store32_le(pk + (i1 + (uint32_t)12U) * (uint32_t)4U, (uint32_t)x211);
    int32_t
    x212 =
      FStar_Int32_shift_arithmetic_right(tj18,
        (uint32_t)2U)
      | (int32_t)((uint32_t)tj19 << (uint32_t)21U);
    store32_le(pk + (i1 + (uint32_t)13U) * (uint32_t)4U, (uint32_t)x212);
    int32_t
    x213 =
      FStar_Int32_shift_arithmetic_right(tj19,
        (uint32_t)11U)
      | (int32_t)((uint32_t)tj20 << (uint32_t)12U);
    store32_le(pk + (i1 + (uint32_t)14U) * (uint32_t)4U, (uint32_t)x213);
    int32_t
    x214 =
      (FStar_Int32_shift_arithmetic_right(tj20,
        (uint32_t)20U)
      | (int32_t)((uint32_t)tj21 << (uint32_t)3U))
      | (int32_t)((uint32_t)tj22 << (uint32_t)26U);
    store32_le(pk + (i1 + (uint32_t)15U) * (uint32_t)4U, (uint32_t)x214);
    int32_t
    x215 =
      FStar_Int32_shift_arithmetic_right(tj22,
        (uint32_t)6U)
      | (int32_t)((uint32_t)tj23 << (uint32_t)17U);
    store32_le(pk + (i1 + (uint32_t)16U) * (uint32_t)4U, (uint32_t)x215);
    int32_t
    x216 =
      (FStar_Int32_shift_arithmetic_right(tj23,
        (uint32_t)15U)
      | (int32_t)((uint32_t)tj24 << (uint32_t)8U))
      | (int32_t)((uint32_t)tj25 << (uint32_t)31U);
    store32_le(pk + (i1 + (uint32_t)17U) * (uint32_t)4U, (uint32_t)x216);
    int32_t
    x217 =
      FStar_Int32_shift_arithmetic_right(tj25,
        (uint32_t)1U)
      | (int32_t)((uint32_t)tj26 << (uint32_t)22U);
    store32_le(pk + (i1 + (uint32_t)18U) * (uint32_t)4U, (uint32_t)x217);
    int32_t
    x218 =
      FStar_Int32_shift_arithmetic_right(tj26,
        (uint32_t)10U)
      | (int32_t)((uint32_t)tj27 << (uint32_t)13U);
    store32_le(pk + (i1 + (uint32_t)19U) * (uint32_t)4U, (uint32_t)x218);
    int32_t
    x219 =
      (FStar_Int32_shift_arithmetic_right(tj27,
        (uint32_t)19U)
      | (int32_t)((uint32_t)tj28 << (uint32_t)4U))
      | (int32_t)((uint32_t)tj29 << (uint32_t)27U);
    store32_le(pk + (i1 + (uint32_t)20U) * (uint32_t)4U, (uint32_t)x219);
    int32_t
    x220 =
      FStar_Int32_shift_arithmetic_right(tj29,
        (uint32_t)5U)
      | (int32_t)((uint32_t)tj30 << (uint32_t)18U);
    store32_le(pk + (i1 + (uint32_t)21U) * (uint32_t)4U, (uint32_t)x220);
    int32_t
    x221 =
      FStar_Int32_shift_arithmetic_right(tj30,
        (uint32_t)14U)
      | (int32_t)((uint32_t)tj31 << (uint32_t)9U);
    store32_le(pk + (i1 + (uint32_t)22U) * (uint32_t)4U, (uint32_t)x221);
  }
  memcpy(pk
    + Hacl_Impl_QTesla_Params_params_n * Hacl_Impl_QTesla_Params_params_q_log / (uint32_t)8U,
    seedA,
    Hacl_Impl_QTesla_Params_crypto_seedbytes * sizeof seedA[0U]);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Pack_encode_pk */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Pack_decode_pk */

static void
Hacl_Impl_QTesla_Heuristic_Pack_decode_pk(int32_t *pk, uint8_t *seedA, uint8_t *pk_in)
{
  uint32_t mask23_left = (uint32_t)1U << Hacl_Impl_QTesla_Params_params_q_log;
  uint32_t mask23 = mask23_left - (uint32_t)1U;
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)32U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t j = i0 * (uint32_t)23U;
    uint32_t i = i0 * (uint32_t)32U;
    uint32_t u0 = load32_le(pk_in + (j + (uint32_t)0U) * (uint32_t)4U);
    uint32_t u1 = u0;
    uint32_t ppi = u1 & mask23;
    int32_t *subPk0 = pk + i;
    subPk0[0U] = (int32_t)ppi;
    uint32_t u2 = load32_le(pk_in + (j + (uint32_t)0U) * (uint32_t)4U);
    uint32_t u3 = u2;
    uint32_t uu____0 = u3 >> (uint32_t)23U;
    uint32_t u4 = load32_le(pk_in + (j + (uint32_t)1U) * (uint32_t)4U);
    uint32_t u5 = u4;
    uint32_t ppi1 = (uu____0 | u5 << (uint32_t)9U) & mask23;
    int32_t *subPk1 = pk + i;
    subPk1[1U] = (int32_t)ppi1;
    uint32_t u6 = load32_le(pk_in + (j + (uint32_t)1U) * (uint32_t)4U);
    uint32_t u7 = u6;
    uint32_t uu____1 = u7 >> (uint32_t)14U;
    uint32_t u8 = load32_le(pk_in + (j + (uint32_t)2U) * (uint32_t)4U);
    uint32_t u9 = u8;
    uint32_t ppi2 = (uu____1 | u9 << (uint32_t)18U) & mask23;
    int32_t *subPk2 = pk + i;
    subPk2[2U] = (int32_t)ppi2;
    uint32_t u10 = load32_le(pk_in + (j + (uint32_t)2U) * (uint32_t)4U);
    uint32_t u11 = u10;
    uint32_t ppi3 = u11 >> (uint32_t)5U & mask23;
    int32_t *subPk3 = pk + i;
    subPk3[3U] = (int32_t)ppi3;
    uint32_t u12 = load32_le(pk_in + (j + (uint32_t)2U) * (uint32_t)4U);
    uint32_t u13 = u12;
    uint32_t uu____2 = u13 >> (uint32_t)28U;
    uint32_t u14 = load32_le(pk_in + (j + (uint32_t)3U) * (uint32_t)4U);
    uint32_t u15 = u14;
    uint32_t ppi4 = (uu____2 | u15 << (uint32_t)4U) & mask23;
    int32_t *subPk4 = pk + i;
    subPk4[4U] = (int32_t)ppi4;
    uint32_t u16 = load32_le(pk_in + (j + (uint32_t)3U) * (uint32_t)4U);
    uint32_t u17 = u16;
    uint32_t uu____3 = u17 >> (uint32_t)19U;
    uint32_t u18 = load32_le(pk_in + (j + (uint32_t)4U) * (uint32_t)4U);
    uint32_t u19 = u18;
    uint32_t ppi5 = (uu____3 | u19 << (uint32_t)13U) & mask23;
    int32_t *subPk5 = pk + i;
    subPk5[5U] = (int32_t)ppi5;
    uint32_t u20 = load32_le(pk_in + (j + (uint32_t)4U) * (uint32_t)4U);
    uint32_t u21 = u20;
    uint32_t uu____4 = u21 >> (uint32_t)10U;
    uint32_t u22 = load32_le(pk_in + (j + (uint32_t)5U) * (uint32_t)4U);
    uint32_t u23 = u22;
    uint32_t ppi6 = (uu____4 | u23 << (uint32_t)22U) & mask23;
    int32_t *subPk6 = pk + i;
    subPk6[6U] = (int32_t)ppi6;
    uint32_t u24 = load32_le(pk_in + (j + (uint32_t)5U) * (uint32_t)4U);
    uint32_t u25 = u24;
    uint32_t ppi7 = u25 >> (uint32_t)1U & mask23;
    int32_t *subPk7 = pk + i;
    subPk7[7U] = (int32_t)ppi7;
    uint32_t u26 = load32_le(pk_in + (j + (uint32_t)5U) * (uint32_t)4U);
    uint32_t u27 = u26;
    uint32_t uu____5 = u27 >> (uint32_t)24U;
    uint32_t u28 = load32_le(pk_in + (j + (uint32_t)6U) * (uint32_t)4U);
    uint32_t u29 = u28;
    uint32_t ppi8 = (uu____5 | u29 << (uint32_t)8U) & mask23;
    int32_t *subPk8 = pk + i;
    subPk8[8U] = (int32_t)ppi8;
    uint32_t u30 = load32_le(pk_in + (j + (uint32_t)6U) * (uint32_t)4U);
    uint32_t u31 = u30;
    uint32_t uu____6 = u31 >> (uint32_t)15U;
    uint32_t u32 = load32_le(pk_in + (j + (uint32_t)7U) * (uint32_t)4U);
    uint32_t u33 = u32;
    uint32_t ppi9 = (uu____6 | u33 << (uint32_t)17U) & mask23;
    int32_t *subPk9 = pk + i;
    subPk9[9U] = (int32_t)ppi9;
    uint32_t u34 = load32_le(pk_in + (j + (uint32_t)7U) * (uint32_t)4U);
    uint32_t u35 = u34;
    uint32_t ppi10 = u35 >> (uint32_t)6U & mask23;
    int32_t *subPk10 = pk + i;
    subPk10[10U] = (int32_t)ppi10;
    uint32_t u36 = load32_le(pk_in + (j + (uint32_t)7U) * (uint32_t)4U);
    uint32_t u37 = u36;
    uint32_t uu____7 = u37 >> (uint32_t)29U;
    uint32_t u38 = load32_le(pk_in + (j + (uint32_t)8U) * (uint32_t)4U);
    uint32_t u39 = u38;
    uint32_t ppi11 = (uu____7 | u39 << (uint32_t)3U) & mask23;
    int32_t *subPk11 = pk + i;
    subPk11[11U] = (int32_t)ppi11;
    uint32_t u40 = load32_le(pk_in + (j + (uint32_t)8U) * (uint32_t)4U);
    uint32_t u41 = u40;
    uint32_t uu____8 = u41 >> (uint32_t)20U;
    uint32_t u42 = load32_le(pk_in + (j + (uint32_t)9U) * (uint32_t)4U);
    uint32_t u43 = u42;
    uint32_t ppi12 = (uu____8 | u43 << (uint32_t)12U) & mask23;
    int32_t *subPk12 = pk + i;
    subPk12[12U] = (int32_t)ppi12;
    uint32_t u44 = load32_le(pk_in + (j + (uint32_t)9U) * (uint32_t)4U);
    uint32_t u45 = u44;
    uint32_t uu____9 = u45 >> (uint32_t)11U;
    uint32_t u46 = load32_le(pk_in + (j + (uint32_t)10U) * (uint32_t)4U);
    uint32_t u47 = u46;
    uint32_t ppi13 = (uu____9 | u47 << (uint32_t)21U) & mask23;
    int32_t *subPk13 = pk + i;
    subPk13[13U] = (int32_t)ppi13;
    uint32_t u48 = load32_le(pk_in + (j + (uint32_t)10U) * (uint32_t)4U);
    uint32_t u49 = u48;
    uint32_t ppi14 = u49 >> (uint32_t)2U & mask23;
    int32_t *subPk14 = pk + i;
    subPk14[14U] = (int32_t)ppi14;
    uint32_t u50 = load32_le(pk_in + (j + (uint32_t)10U) * (uint32_t)4U);
    uint32_t u51 = u50;
    uint32_t uu____10 = u51 >> (uint32_t)25U;
    uint32_t u52 = load32_le(pk_in + (j + (uint32_t)11U) * (uint32_t)4U);
    uint32_t u53 = u52;
    uint32_t ppi15 = (uu____10 | u53 << (uint32_t)7U) & mask23;
    int32_t *subPk15 = pk + i;
    subPk15[15U] = (int32_t)ppi15;
    uint32_t u54 = load32_le(pk_in + (j + (uint32_t)11U) * (uint32_t)4U);
    uint32_t u55 = u54;
    uint32_t uu____11 = u55 >> (uint32_t)16U;
    uint32_t u56 = load32_le(pk_in + (j + (uint32_t)12U) * (uint32_t)4U);
    uint32_t u57 = u56;
    uint32_t ppi16 = (uu____11 | u57 << (uint32_t)16U) & mask23;
    int32_t *subPk16 = pk + i;
    subPk16[16U] = (int32_t)ppi16;
    uint32_t u58 = load32_le(pk_in + (j + (uint32_t)12U) * (uint32_t)4U);
    uint32_t u59 = u58;
    uint32_t ppi17 = u59 >> (uint32_t)7U & mask23;
    int32_t *subPk17 = pk + i;
    subPk17[17U] = (int32_t)ppi17;
    uint32_t u60 = load32_le(pk_in + (j + (uint32_t)12U) * (uint32_t)4U);
    uint32_t u61 = u60;
    uint32_t uu____12 = u61 >> (uint32_t)30U;
    uint32_t u62 = load32_le(pk_in + (j + (uint32_t)13U) * (uint32_t)4U);
    uint32_t u63 = u62;
    uint32_t ppi18 = (uu____12 | u63 << (uint32_t)2U) & mask23;
    int32_t *subPk18 = pk + i;
    subPk18[18U] = (int32_t)ppi18;
    uint32_t u64 = load32_le(pk_in + (j + (uint32_t)13U) * (uint32_t)4U);
    uint32_t u65 = u64;
    uint32_t uu____13 = u65 >> (uint32_t)21U;
    uint32_t u66 = load32_le(pk_in + (j + (uint32_t)14U) * (uint32_t)4U);
    uint32_t u67 = u66;
    uint32_t ppi19 = (uu____13 | u67 << (uint32_t)11U) & mask23;
    int32_t *subPk19 = pk + i;
    subPk19[19U] = (int32_t)ppi19;
    uint32_t u68 = load32_le(pk_in + (j + (uint32_t)14U) * (uint32_t)4U);
    uint32_t u69 = u68;
    uint32_t uu____14 = u69 >> (uint32_t)12U;
    uint32_t u70 = load32_le(pk_in + (j + (uint32_t)15U) * (uint32_t)4U);
    uint32_t u71 = u70;
    uint32_t ppi20 = (uu____14 | u71 << (uint32_t)20U) & mask23;
    int32_t *subPk20 = pk + i;
    subPk20[20U] = (int32_t)ppi20;
    uint32_t u72 = load32_le(pk_in + (j + (uint32_t)15U) * (uint32_t)4U);
    uint32_t u73 = u72;
    uint32_t ppi21 = u73 >> (uint32_t)3U & mask23;
    int32_t *subPk21 = pk + i;
    subPk21[21U] = (int32_t)ppi21;
    uint32_t u74 = load32_le(pk_in + (j + (uint32_t)15U) * (uint32_t)4U);
    uint32_t u75 = u74;
    uint32_t uu____15 = u75 >> (uint32_t)26U;
    uint32_t u76 = load32_le(pk_in + (j + (uint32_t)16U) * (uint32_t)4U);
    uint32_t u77 = u76;
    uint32_t ppi22 = (uu____15 | u77 << (uint32_t)6U) & mask23;
    int32_t *subPk22 = pk + i;
    subPk22[22U] = (int32_t)ppi22;
    uint32_t u78 = load32_le(pk_in + (j + (uint32_t)16U) * (uint32_t)4U);
    uint32_t u79 = u78;
    uint32_t uu____16 = u79 >> (uint32_t)17U;
    uint32_t u80 = load32_le(pk_in + (j + (uint32_t)17U) * (uint32_t)4U);
    uint32_t u81 = u80;
    uint32_t ppi23 = (uu____16 | u81 << (uint32_t)15U) & mask23;
    int32_t *subPk23 = pk + i;
    subPk23[23U] = (int32_t)ppi23;
    uint32_t u82 = load32_le(pk_in + (j + (uint32_t)17U) * (uint32_t)4U);
    uint32_t u83 = u82;
    uint32_t ppi24 = u83 >> (uint32_t)8U & mask23;
    int32_t *subPk24 = pk + i;
    subPk24[24U] = (int32_t)ppi24;
    uint32_t u84 = load32_le(pk_in + (j + (uint32_t)17U) * (uint32_t)4U);
    uint32_t u85 = u84;
    uint32_t uu____17 = u85 >> (uint32_t)31U;
    uint32_t u86 = load32_le(pk_in + (j + (uint32_t)18U) * (uint32_t)4U);
    uint32_t u87 = u86;
    uint32_t ppi25 = (uu____17 | u87 << (uint32_t)1U) & mask23;
    int32_t *subPk25 = pk + i;
    subPk25[25U] = (int32_t)ppi25;
    uint32_t u88 = load32_le(pk_in + (j + (uint32_t)18U) * (uint32_t)4U);
    uint32_t u89 = u88;
    uint32_t uu____18 = u89 >> (uint32_t)22U;
    uint32_t u90 = load32_le(pk_in + (j + (uint32_t)19U) * (uint32_t)4U);
    uint32_t u91 = u90;
    uint32_t ppi26 = (uu____18 | u91 << (uint32_t)10U) & mask23;
    int32_t *subPk26 = pk + i;
    subPk26[26U] = (int32_t)ppi26;
    uint32_t u92 = load32_le(pk_in + (j + (uint32_t)19U) * (uint32_t)4U);
    uint32_t u93 = u92;
    uint32_t uu____19 = u93 >> (uint32_t)13U;
    uint32_t u94 = load32_le(pk_in + (j + (uint32_t)20U) * (uint32_t)4U);
    uint32_t u95 = u94;
    uint32_t ppi27 = (uu____19 | u95 << (uint32_t)19U) & mask23;
    int32_t *subPk27 = pk + i;
    subPk27[27U] = (int32_t)ppi27;
    uint32_t u96 = load32_le(pk_in + (j + (uint32_t)20U) * (uint32_t)4U);
    uint32_t u97 = u96;
    uint32_t ppi28 = u97 >> (uint32_t)4U & mask23;
    int32_t *subPk28 = pk + i;
    subPk28[28U] = (int32_t)ppi28;
    uint32_t u98 = load32_le(pk_in + (j + (uint32_t)20U) * (uint32_t)4U);
    uint32_t u99 = u98;
    uint32_t uu____20 = u99 >> (uint32_t)27U;
    uint32_t u100 = load32_le(pk_in + (j + (uint32_t)21U) * (uint32_t)4U);
    uint32_t u101 = u100;
    uint32_t ppi29 = (uu____20 | u101 << (uint32_t)5U) & mask23;
    int32_t *subPk29 = pk + i;
    subPk29[29U] = (int32_t)ppi29;
    uint32_t u102 = load32_le(pk_in + (j + (uint32_t)21U) * (uint32_t)4U);
    uint32_t u103 = u102;
    uint32_t uu____21 = u103 >> (uint32_t)18U;
    uint32_t u = load32_le(pk_in + (j + (uint32_t)22U) * (uint32_t)4U);
    uint32_t u104 = u;
    uint32_t ppi30 = (uu____21 | u104 << (uint32_t)14U) & mask23;
    int32_t *subPk30 = pk + i;
    subPk30[30U] = (int32_t)ppi30;
    uint32_t u105 = load32_le(pk_in + (j + (uint32_t)22U) * (uint32_t)4U);
    uint32_t u106 = u105;
    uint32_t ppi31 = u106 >> (uint32_t)9U;
    int32_t *subPk = pk + i;
    subPk[31U] = (int32_t)ppi31;
  }
  memcpy(seedA,
    pk_in + Hacl_Impl_QTesla_Params_params_n * Hacl_Impl_QTesla_Params_params_q_log / (uint32_t)8U,
    Hacl_Impl_QTesla_Params_crypto_seedbytes
    *
      sizeof (pk_in
      + Hacl_Impl_QTesla_Params_params_n * Hacl_Impl_QTesla_Params_params_q_log / (uint32_t)8U)[0U]);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Pack_decode_pk */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Pack_encode_sig */

static void Hacl_Impl_QTesla_Heuristic_Pack_encode_sig(uint8_t *sm, uint8_t *c, int32_t *z)
{
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)32U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t i = i0 * Hacl_Impl_QTesla_Params_params_d;
    uint32_t j = i0 * (uint32_t)32U;
    int32_t zj0 = z[j + (uint32_t)0U];
    int32_t zj1 = z[j + (uint32_t)1U];
    store32_le(sm + (i + (uint32_t)0U) * (uint32_t)4U,
      ((uint32_t)zj0 & (uint32_t)2097151U) | (uint32_t)zj1 << (uint32_t)21U);
    int32_t zj2 = z[j + (uint32_t)1U];
    int32_t zj3 = z[j + (uint32_t)2U];
    int32_t zj4 = z[j + (uint32_t)3U];
    store32_le(sm + (i + (uint32_t)1U) * (uint32_t)4U,
      (((uint32_t)zj2 >> (uint32_t)11U & (uint32_t)1023U)
      | ((uint32_t)zj3 & (uint32_t)2097151U) << (uint32_t)10U)
      | (uint32_t)zj4 << (uint32_t)31U);
    int32_t zj5 = z[j + (uint32_t)3U];
    int32_t zj6 = z[j + (uint32_t)4U];
    store32_le(sm + (i + (uint32_t)2U) * (uint32_t)4U,
      ((uint32_t)zj5 >> (uint32_t)1U & (uint32_t)1048575U) | (uint32_t)zj6 << (uint32_t)20U);
    int32_t zj7 = z[j + (uint32_t)4U];
    int32_t zj8 = z[j + (uint32_t)5U];
    int32_t zj9 = z[j + (uint32_t)6U];
    store32_le(sm + (i + (uint32_t)3U) * (uint32_t)4U,
      (((uint32_t)zj7 >> (uint32_t)12U & (uint32_t)511U)
      | ((uint32_t)zj8 & (uint32_t)2097151U) << (uint32_t)9U)
      | (uint32_t)zj9 << (uint32_t)30U);
    int32_t zj10 = z[j + (uint32_t)6U];
    int32_t zj11 = z[j + (uint32_t)7U];
    store32_le(sm + (i + (uint32_t)4U) * (uint32_t)4U,
      ((uint32_t)zj10 >> (uint32_t)2U & (uint32_t)524287U) | (uint32_t)zj11 << (uint32_t)19U);
    int32_t zj12 = z[j + (uint32_t)7U];
    int32_t zj13 = z[j + (uint32_t)8U];
    int32_t zj14 = z[j + (uint32_t)9U];
    store32_le(sm + (i + (uint32_t)5U) * (uint32_t)4U,
      (((uint32_t)zj12 >> (uint32_t)13U & (uint32_t)255U)
      | ((uint32_t)zj13 & (uint32_t)2097151U) << (uint32_t)8U)
      | (uint32_t)zj14 << (uint32_t)29U);
    int32_t zj15 = z[j + (uint32_t)9U];
    int32_t zj16 = z[j + (uint32_t)10U];
    store32_le(sm + (i + (uint32_t)6U) * (uint32_t)4U,
      ((uint32_t)zj15 >> (uint32_t)3U & (uint32_t)262143U) | (uint32_t)zj16 << (uint32_t)18U);
    int32_t zj17 = z[j + (uint32_t)10U];
    int32_t zj18 = z[j + (uint32_t)11U];
    int32_t zj19 = z[j + (uint32_t)12U];
    store32_le(sm + (i + (uint32_t)7U) * (uint32_t)4U,
      (((uint32_t)zj17 >> (uint32_t)14U & (uint32_t)127U)
      | ((uint32_t)zj18 & (uint32_t)2097151U) << (uint32_t)7U)
      | (uint32_t)zj19 << (uint32_t)28U);
    int32_t zj20 = z[j + (uint32_t)12U];
    int32_t zj21 = z[j + (uint32_t)13U];
    store32_le(sm + (i + (uint32_t)8U) * (uint32_t)4U,
      ((uint32_t)zj20 >> (uint32_t)4U & (uint32_t)131071U) | (uint32_t)zj21 << (uint32_t)17U);
    int32_t zj22 = z[j + (uint32_t)13U];
    int32_t zj23 = z[j + (uint32_t)14U];
    int32_t zj24 = z[j + (uint32_t)15U];
    store32_le(sm + (i + (uint32_t)9U) * (uint32_t)4U,
      (((uint32_t)zj22 >> (uint32_t)15U & (uint32_t)63U)
      | ((uint32_t)zj23 & (uint32_t)2097151U) << (uint32_t)6U)
      | (uint32_t)zj24 << (uint32_t)27U);
    int32_t zj25 = z[j + (uint32_t)15U];
    int32_t zj26 = z[j + (uint32_t)16U];
    store32_le(sm + (i + (uint32_t)10U) * (uint32_t)4U,
      ((uint32_t)zj25 >> (uint32_t)5U & (uint32_t)65535U) | (uint32_t)zj26 << (uint32_t)16U);
    int32_t zj27 = z[j + (uint32_t)16U];
    int32_t zj28 = z[j + (uint32_t)17U];
    int32_t zj29 = z[j + (uint32_t)18U];
    store32_le(sm + (i + (uint32_t)11U) * (uint32_t)4U,
      (((uint32_t)zj27 >> (uint32_t)16U & (uint32_t)31U)
      | ((uint32_t)zj28 & (uint32_t)2097151U) << (uint32_t)5U)
      | (uint32_t)zj29 << (uint32_t)26U);
    int32_t zj30 = z[j + (uint32_t)18U];
    int32_t zj31 = z[j + (uint32_t)19U];
    store32_le(sm + (i + (uint32_t)12U) * (uint32_t)4U,
      ((uint32_t)zj30 >> (uint32_t)6U & (uint32_t)32767U) | (uint32_t)zj31 << (uint32_t)15U);
    int32_t zj32 = z[j + (uint32_t)19U];
    int32_t zj33 = z[j + (uint32_t)20U];
    int32_t zj34 = z[j + (uint32_t)21U];
    store32_le(sm + (i + (uint32_t)13U) * (uint32_t)4U,
      (((uint32_t)zj32 >> (uint32_t)17U & (uint32_t)15U)
      | ((uint32_t)zj33 & (uint32_t)2097151U) << (uint32_t)4U)
      | (uint32_t)zj34 << (uint32_t)25U);
    int32_t zj35 = z[j + (uint32_t)21U];
    int32_t zj36 = z[j + (uint32_t)22U];
    store32_le(sm + (i + (uint32_t)14U) * (uint32_t)4U,
      ((uint32_t)zj35 >> (uint32_t)7U & (uint32_t)16383U) | (uint32_t)zj36 << (uint32_t)14U);
    int32_t zj37 = z[j + (uint32_t)22U];
    int32_t zj38 = z[j + (uint32_t)23U];
    int32_t zj39 = z[j + (uint32_t)24U];
    store32_le(sm + (i + (uint32_t)15U) * (uint32_t)4U,
      (((uint32_t)zj37 >> (uint32_t)18U & (uint32_t)7U)
      | ((uint32_t)zj38 & (uint32_t)2097151U) << (uint32_t)3U)
      | (uint32_t)zj39 << (uint32_t)24U);
    int32_t zj40 = z[j + (uint32_t)24U];
    int32_t zj41 = z[j + (uint32_t)25U];
    store32_le(sm + (i + (uint32_t)16U) * (uint32_t)4U,
      ((uint32_t)zj40 >> (uint32_t)8U & (uint32_t)8191U) | (uint32_t)zj41 << (uint32_t)13U);
    int32_t zj42 = z[j + (uint32_t)25U];
    int32_t zj43 = z[j + (uint32_t)26U];
    int32_t zj44 = z[j + (uint32_t)27U];
    store32_le(sm + (i + (uint32_t)17U) * (uint32_t)4U,
      (((uint32_t)zj42 >> (uint32_t)19U & (uint32_t)3U)
      | ((uint32_t)zj43 & (uint32_t)2097151U) << (uint32_t)2U)
      | (uint32_t)zj44 << (uint32_t)23U);
    int32_t zj45 = z[j + (uint32_t)27U];
    int32_t zj46 = z[j + (uint32_t)28U];
    store32_le(sm + (i + (uint32_t)18U) * (uint32_t)4U,
      ((uint32_t)zj45 >> (uint32_t)9U & (uint32_t)4095U) | (uint32_t)zj46 << (uint32_t)12U);
    int32_t zj47 = z[j + (uint32_t)28U];
    int32_t zj48 = z[j + (uint32_t)29U];
    int32_t zj49 = z[j + (uint32_t)30U];
    store32_le(sm + (i + (uint32_t)19U) * (uint32_t)4U,
      (((uint32_t)zj47 >> (uint32_t)20U & (uint32_t)1U)
      | ((uint32_t)zj48 & (uint32_t)2097151U) << (uint32_t)1U)
      | (uint32_t)zj49 << (uint32_t)22U);
    int32_t zj50 = z[j + (uint32_t)30U];
    int32_t zj = z[j + (uint32_t)31U];
    store32_le(sm + (i + (uint32_t)20U) * (uint32_t)4U,
      ((uint32_t)zj50 >> (uint32_t)10U & (uint32_t)2047U) | (uint32_t)zj << (uint32_t)11U);
  }
  memcpy(sm + Hacl_Impl_QTesla_Params_params_n * Hacl_Impl_QTesla_Params_params_d / (uint32_t)8U,
    c,
    Hacl_Impl_QTesla_Params_crypto_c_bytes * sizeof c[0U]);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Pack_encode_sig */

/* SNIPPET_START: Hacl_Impl_QTesla_Heuristic_Pack_decode_sig */

static void Hacl_Impl_QTesla_Heuristic_Pack_decode_sig(uint8_t *c, int32_t *z, uint8_t *sm)
{
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)32U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t j = i0 * (uint32_t)21U;
    uint32_t u0 = load32_le(sm + (j + (uint32_t)0U) * (uint32_t)4U);
    uint32_t u1 = u0;
    uint32_t ptj0 = u1;
    uint32_t u2 = load32_le(sm + (j + (uint32_t)1U) * (uint32_t)4U);
    uint32_t u3 = u2;
    uint32_t ptj1 = u3;
    uint32_t u4 = load32_le(sm + (j + (uint32_t)2U) * (uint32_t)4U);
    uint32_t u5 = u4;
    uint32_t ptj2 = u5;
    uint32_t u6 = load32_le(sm + (j + (uint32_t)3U) * (uint32_t)4U);
    uint32_t u7 = u6;
    uint32_t ptj3 = u7;
    uint32_t u8 = load32_le(sm + (j + (uint32_t)4U) * (uint32_t)4U);
    uint32_t u9 = u8;
    uint32_t ptj4 = u9;
    uint32_t u10 = load32_le(sm + (j + (uint32_t)5U) * (uint32_t)4U);
    uint32_t u11 = u10;
    uint32_t ptj5 = u11;
    uint32_t u12 = load32_le(sm + (j + (uint32_t)6U) * (uint32_t)4U);
    uint32_t u13 = u12;
    uint32_t ptj6 = u13;
    uint32_t u14 = load32_le(sm + (j + (uint32_t)7U) * (uint32_t)4U);
    uint32_t u15 = u14;
    uint32_t ptj7 = u15;
    uint32_t u16 = load32_le(sm + (j + (uint32_t)8U) * (uint32_t)4U);
    uint32_t u17 = u16;
    uint32_t ptj8 = u17;
    uint32_t u18 = load32_le(sm + (j + (uint32_t)9U) * (uint32_t)4U);
    uint32_t u19 = u18;
    uint32_t ptj9 = u19;
    uint32_t u20 = load32_le(sm + (j + (uint32_t)10U) * (uint32_t)4U);
    uint32_t u21 = u20;
    uint32_t ptj10 = u21;
    uint32_t u22 = load32_le(sm + (j + (uint32_t)11U) * (uint32_t)4U);
    uint32_t u23 = u22;
    uint32_t ptj11 = u23;
    uint32_t u24 = load32_le(sm + (j + (uint32_t)12U) * (uint32_t)4U);
    uint32_t u25 = u24;
    uint32_t ptj12 = u25;
    uint32_t u26 = load32_le(sm + (j + (uint32_t)13U) * (uint32_t)4U);
    uint32_t u27 = u26;
    uint32_t ptj13 = u27;
    uint32_t u28 = load32_le(sm + (j + (uint32_t)14U) * (uint32_t)4U);
    uint32_t u29 = u28;
    uint32_t ptj14 = u29;
    uint32_t u30 = load32_le(sm + (j + (uint32_t)15U) * (uint32_t)4U);
    uint32_t u31 = u30;
    uint32_t ptj15 = u31;
    uint32_t u32 = load32_le(sm + (j + (uint32_t)16U) * (uint32_t)4U);
    uint32_t u33 = u32;
    uint32_t ptj16 = u33;
    uint32_t u34 = load32_le(sm + (j + (uint32_t)17U) * (uint32_t)4U);
    uint32_t u35 = u34;
    uint32_t ptj17 = u35;
    uint32_t u36 = load32_le(sm + (j + (uint32_t)18U) * (uint32_t)4U);
    uint32_t u37 = u36;
    uint32_t ptj18 = u37;
    uint32_t u38 = load32_le(sm + (j + (uint32_t)19U) * (uint32_t)4U);
    uint32_t u39 = u38;
    uint32_t ptj19 = u39;
    uint32_t u = load32_le(sm + (j + (uint32_t)20U) * (uint32_t)4U);
    uint32_t u40 = u;
    uint32_t ptj20 = u40;
    uint32_t i = i0 * (uint32_t)32U;
    int32_t
    x0 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj0 << (uint32_t)11U), (uint32_t)11U);
    int32_t x2 = x0;
    z[i + (uint32_t)0U] = x2;
    int32_t
    x00 =
      (int32_t)(ptj0 >> (uint32_t)21U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj1 << (uint32_t)22U), (uint32_t)11U);
    int32_t x20 = x00;
    z[i + (uint32_t)1U] = x20;
    int32_t
    x01 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj1 << (uint32_t)1U), (uint32_t)11U);
    int32_t x21 = x01;
    z[i + (uint32_t)2U] = x21;
    int32_t
    x02 =
      (int32_t)(ptj1 >> (uint32_t)31U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj2 << (uint32_t)12U), (uint32_t)11U);
    int32_t x22 = x02;
    z[i + (uint32_t)3U] = x22;
    int32_t
    x03 =
      (int32_t)(ptj2 >> (uint32_t)20U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj3 << (uint32_t)23U), (uint32_t)11U);
    int32_t x23 = x03;
    z[i + (uint32_t)4U] = x23;
    int32_t
    x04 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj3 << (uint32_t)2U), (uint32_t)11U);
    int32_t x24 = x04;
    z[i + (uint32_t)5U] = x24;
    int32_t
    x05 =
      (int32_t)(ptj3 >> (uint32_t)30U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj4 << (uint32_t)13U), (uint32_t)11U);
    int32_t x25 = x05;
    z[i + (uint32_t)6U] = x25;
    int32_t
    x06 =
      (int32_t)(ptj4 >> (uint32_t)19U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj5 << (uint32_t)24U), (uint32_t)11U);
    int32_t x26 = x06;
    z[i + (uint32_t)7U] = x26;
    int32_t
    x07 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj5 << (uint32_t)3U), (uint32_t)11U);
    int32_t x27 = x07;
    z[i + (uint32_t)8U] = x27;
    int32_t
    x08 =
      (int32_t)(ptj5 >> (uint32_t)29U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj6 << (uint32_t)14U), (uint32_t)11U);
    int32_t x28 = x08;
    z[i + (uint32_t)9U] = x28;
    int32_t
    x09 =
      (int32_t)(ptj6 >> (uint32_t)18U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj7 << (uint32_t)25U), (uint32_t)11U);
    int32_t x29 = x09;
    z[i + (uint32_t)10U] = x29;
    int32_t
    x010 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj7 << (uint32_t)4U), (uint32_t)11U);
    int32_t x210 = x010;
    z[i + (uint32_t)11U] = x210;
    int32_t
    x011 =
      (int32_t)(ptj7 >> (uint32_t)28U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj8 << (uint32_t)15U), (uint32_t)11U);
    int32_t x211 = x011;
    z[i + (uint32_t)12U] = x211;
    int32_t
    x012 =
      (int32_t)(ptj8 >> (uint32_t)17U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj9 << (uint32_t)26U), (uint32_t)11U);
    int32_t x212 = x012;
    z[i + (uint32_t)13U] = x212;
    int32_t
    x013 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj9 << (uint32_t)5U), (uint32_t)11U);
    int32_t x213 = x013;
    z[i + (uint32_t)14U] = x213;
    int32_t
    x014 =
      (int32_t)(ptj9 >> (uint32_t)27U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj10 << (uint32_t)16U), (uint32_t)11U);
    int32_t x214 = x014;
    z[i + (uint32_t)15U] = x214;
    int32_t
    x015 =
      (int32_t)(ptj10 >> (uint32_t)16U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj11 << (uint32_t)27U), (uint32_t)11U);
    int32_t x215 = x015;
    z[i + (uint32_t)16U] = x215;
    int32_t
    x016 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj11 << (uint32_t)6U), (uint32_t)11U);
    int32_t x216 = x016;
    z[i + (uint32_t)17U] = x216;
    int32_t
    x017 =
      (int32_t)(ptj11 >> (uint32_t)26U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj12 << (uint32_t)17U), (uint32_t)11U);
    int32_t x217 = x017;
    z[i + (uint32_t)18U] = x217;
    int32_t
    x018 =
      (int32_t)(ptj12 >> (uint32_t)15U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj13 << (uint32_t)28U), (uint32_t)11U);
    int32_t x218 = x018;
    z[i + (uint32_t)19U] = x218;
    int32_t
    x019 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj13 << (uint32_t)7U), (uint32_t)11U);
    int32_t x219 = x019;
    z[i + (uint32_t)20U] = x219;
    int32_t
    x020 =
      (int32_t)(ptj13 >> (uint32_t)25U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj14 << (uint32_t)18U), (uint32_t)11U);
    int32_t x220 = x020;
    z[i + (uint32_t)21U] = x220;
    int32_t
    x021 =
      (int32_t)(ptj14 >> (uint32_t)14U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj15 << (uint32_t)29U), (uint32_t)11U);
    int32_t x221 = x021;
    z[i + (uint32_t)22U] = x221;
    int32_t
    x022 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj15 << (uint32_t)8U), (uint32_t)11U);
    int32_t x222 = x022;
    z[i + (uint32_t)23U] = x222;
    int32_t
    x023 =
      (int32_t)(ptj15 >> (uint32_t)24U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj16 << (uint32_t)19U), (uint32_t)11U);
    int32_t x223 = x023;
    z[i + (uint32_t)24U] = x223;
    int32_t
    x024 =
      (int32_t)(ptj16 >> (uint32_t)13U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj17 << (uint32_t)30U), (uint32_t)11U);
    int32_t x224 = x024;
    z[i + (uint32_t)25U] = x224;
    int32_t
    x025 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj17 << (uint32_t)9U), (uint32_t)11U);
    int32_t x225 = x025;
    z[i + (uint32_t)26U] = x225;
    int32_t
    x026 =
      (int32_t)(ptj17 >> (uint32_t)23U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj18 << (uint32_t)20U), (uint32_t)11U);
    int32_t x226 = x026;
    z[i + (uint32_t)27U] = x226;
    int32_t
    x027 =
      (int32_t)(ptj18 >> (uint32_t)12U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj19 << (uint32_t)31U), (uint32_t)11U);
    int32_t x227 = x027;
    z[i + (uint32_t)28U] = x227;
    int32_t
    x028 = FStar_Int32_shift_arithmetic_right((int32_t)(ptj19 << (uint32_t)10U), (uint32_t)11U);
    int32_t x228 = x028;
    z[i + (uint32_t)29U] = x228;
    int32_t
    x029 =
      (int32_t)(ptj19 >> (uint32_t)22U)
      | FStar_Int32_shift_arithmetic_right((int32_t)(ptj20 << (uint32_t)21U), (uint32_t)11U);
    int32_t x229 = x029;
    z[i + (uint32_t)30U] = x229;
    int32_t x030 = FStar_Int32_shift_arithmetic_right((int32_t)ptj20, (uint32_t)11U);
    int32_t x230 = x030;
    z[i + (uint32_t)31U] = x230;
  }
  memcpy(c,
    sm + Hacl_Impl_QTesla_Params_params_n * Hacl_Impl_QTesla_Params_params_d / (uint32_t)8U,
    Hacl_Impl_QTesla_Params_crypto_c_bytes
    *
      sizeof (sm
      + Hacl_Impl_QTesla_Params_params_n * Hacl_Impl_QTesla_Params_params_d / (uint32_t)8U)[0U]);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Heuristic_Pack_decode_sig */

/* SNIPPET_START: Hacl_Impl_QTesla_Pack_encode_sk */

static void
Hacl_Impl_QTesla_Pack_encode_sk(uint8_t *sk, int32_t *s, int32_t *e, uint8_t *seeds)
{
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t i = i0 * (uint32_t)4U;
    uint32_t j = (uint32_t)0U + i0 * (uint32_t)5U;
    int32_t si0 = s[i + (uint32_t)0U];
    int32_t si1 = s[i + (uint32_t)1U];
    int32_t si2 = s[i + (uint32_t)2U];
    int32_t si3 = s[i + (uint32_t)3U];
    sk[j + (uint32_t)0U] = (uint8_t)si0;
    sk[j + (uint32_t)1U] =
      (uint8_t)((FStar_Int32_shift_arithmetic_right(si0, (uint32_t)8U) & (int32_t)0x03)
      | (int32_t)((uint32_t)si1 << (uint32_t)2U));
    sk[j + (uint32_t)2U] =
      (uint8_t)((FStar_Int32_shift_arithmetic_right(si1, (uint32_t)6U) & (int32_t)0x0F)
      | (int32_t)((uint32_t)si2 << (uint32_t)4U));
    sk[j + (uint32_t)3U] =
      (uint8_t)((FStar_Int32_shift_arithmetic_right(si2, (uint32_t)4U) & (int32_t)0x3F)
      | (int32_t)((uint32_t)si3 << (uint32_t)6U));
    sk[j + (uint32_t)4U] = (uint8_t)FStar_Int32_shift_arithmetic_right(si3, (uint32_t)2U);
  }
  uint32_t j = (uint32_t)0U + Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U * (uint32_t)5U;
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t i = i0 * (uint32_t)4U;
    uint32_t j1 = j + i0 * (uint32_t)5U;
    int32_t si0 = e[i + (uint32_t)0U];
    int32_t si1 = e[i + (uint32_t)1U];
    int32_t si2 = e[i + (uint32_t)2U];
    int32_t si3 = e[i + (uint32_t)3U];
    sk[j1 + (uint32_t)0U] = (uint8_t)si0;
    sk[j1 + (uint32_t)1U] =
      (uint8_t)((FStar_Int32_shift_arithmetic_right(si0, (uint32_t)8U) & (int32_t)0x03)
      | (int32_t)((uint32_t)si1 << (uint32_t)2U));
    sk[j1 + (uint32_t)2U] =
      (uint8_t)((FStar_Int32_shift_arithmetic_right(si1, (uint32_t)6U) & (int32_t)0x0F)
      | (int32_t)((uint32_t)si2 << (uint32_t)4U));
    sk[j1 + (uint32_t)3U] =
      (uint8_t)((FStar_Int32_shift_arithmetic_right(si2, (uint32_t)4U) & (int32_t)0x3F)
      | (int32_t)((uint32_t)si3 << (uint32_t)6U));
    sk[j1 + (uint32_t)4U] = (uint8_t)FStar_Int32_shift_arithmetic_right(si3, (uint32_t)2U);
  }
  uint32_t uu____0 = j + Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U * (uint32_t)5U;
  memcpy(sk
    +
      (uint32_t)2U
      * Hacl_Impl_QTesla_Params_params_s_bits
      * Hacl_Impl_QTesla_Params_params_n
      / (uint32_t)8U,
    seeds,
    (uint32_t)2U * Hacl_Impl_QTesla_Params_crypto_seedbytes * sizeof seeds[0U]);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Pack_encode_sk */

/* SNIPPET_START: Hacl_Impl_QTesla_Pack_decode_sk */

static void
Hacl_Impl_QTesla_Pack_decode_sk(uint8_t *seeds, int16_t *s, int16_t *e, uint8_t *sk)
{
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t i = i0 * (uint32_t)4U;
    uint32_t j = (uint32_t)0U + i0 * (uint32_t)5U;
    uint8_t skj0 = sk[j + (uint32_t)0U];
    uint8_t skj1 = sk[j + (uint32_t)1U];
    uint8_t skj2 = sk[j + (uint32_t)2U];
    uint8_t skj3 = sk[j + (uint32_t)3U];
    uint8_t skj4 = sk[j + (uint32_t)4U];
    s[i + (uint32_t)0U] =
      (int16_t)skj0
      |
        (int16_t)FStar_Int32_shift_arithmetic_right((int32_t)((uint32_t)(int32_t)skj1
          << (uint32_t)30U),
          (uint32_t)22U);
    s[i + (uint32_t)1U] =
      (int16_t)(skj1 >> (uint32_t)2U)
      |
        (int16_t)FStar_Int32_shift_arithmetic_right((int32_t)((uint32_t)(int32_t)skj2
          << (uint32_t)28U),
          (uint32_t)22U);
    s[i + (uint32_t)2U] =
      (int16_t)(skj2 >> (uint32_t)4U)
      |
        (int16_t)FStar_Int32_shift_arithmetic_right((int32_t)((uint32_t)(int32_t)skj3
          << (uint32_t)26U),
          (uint32_t)22U);
    s[i + (uint32_t)3U] =
      (int16_t)(skj3 >> (uint32_t)6U)
      | (int16_t)((uint16_t)(int16_t)(int8_t)skj4 << (uint32_t)2U);
  }
  uint32_t j = (uint32_t)0U + Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U * (uint32_t)5U;
  for
  (uint32_t
    i0 = (uint32_t)0U;
    i0
    < Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U;
    i0 = i0 + (uint32_t)1U)
  {
    uint32_t i = i0 * (uint32_t)4U;
    uint32_t j1 = j + i0 * (uint32_t)5U;
    uint8_t skj0 = sk[j1 + (uint32_t)0U];
    uint8_t skj1 = sk[j1 + (uint32_t)1U];
    uint8_t skj2 = sk[j1 + (uint32_t)2U];
    uint8_t skj3 = sk[j1 + (uint32_t)3U];
    uint8_t skj4 = sk[j1 + (uint32_t)4U];
    e[i + (uint32_t)0U] =
      (int16_t)skj0
      |
        (int16_t)FStar_Int32_shift_arithmetic_right((int32_t)((uint32_t)(int32_t)skj1
          << (uint32_t)30U),
          (uint32_t)22U);
    e[i + (uint32_t)1U] =
      (int16_t)(skj1 >> (uint32_t)2U)
      |
        (int16_t)FStar_Int32_shift_arithmetic_right((int32_t)((uint32_t)(int32_t)skj2
          << (uint32_t)28U),
          (uint32_t)22U);
    e[i + (uint32_t)2U] =
      (int16_t)(skj2 >> (uint32_t)4U)
      |
        (int16_t)FStar_Int32_shift_arithmetic_right((int32_t)((uint32_t)(int32_t)skj3
          << (uint32_t)26U),
          (uint32_t)22U);
    e[i + (uint32_t)3U] =
      (int16_t)(skj3 >> (uint32_t)6U)
      | (int16_t)((uint16_t)(int16_t)(int8_t)skj4 << (uint32_t)2U);
  }
  uint32_t uu____0 = j + Hacl_Impl_QTesla_Params_params_n / (uint32_t)4U * (uint32_t)5U;
  memcpy(seeds,
    sk
    +
      (uint32_t)2U
      * Hacl_Impl_QTesla_Params_params_s_bits
      * Hacl_Impl_QTesla_Params_params_n
      / (uint32_t)8U,
    (uint32_t)2U
    * Hacl_Impl_QTesla_Params_crypto_seedbytes
    *
      sizeof (sk
      +
        (uint32_t)2U
        * Hacl_Impl_QTesla_Params_params_s_bits
        * Hacl_Impl_QTesla_Params_params_n
        / (uint32_t)8U)[0U]);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Pack_decode_sk */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__RADIX */

static uint32_t Hacl_Impl_QTesla_Gauss__RADIX = (uint32_t)64U;

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__RADIX */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__RADIX32 */

static uint32_t Hacl_Impl_QTesla_Gauss__RADIX32 = (uint32_t)32U;

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__RADIX32 */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__CDT_ROWS */

static uint32_t Hacl_Impl_QTesla_Gauss__CDT_ROWS = (uint32_t)209U;

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__CDT_ROWS */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__CDT_COLS */

static uint32_t Hacl_Impl_QTesla_Gauss__CDT_COLS = (uint32_t)1U;

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__CDT_COLS */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__CHUNK_SIZE */

static uint32_t Hacl_Impl_QTesla_Gauss__CHUNK_SIZE = (uint32_t)512U;

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__CHUNK_SIZE */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__DFIELD */

static int64_t Hacl_Impl_QTesla_Gauss__DFIELD = (int64_t)(uint64_t)9223372036854775807U;

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__DFIELD */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__PRODIFF */

static void
Hacl_Impl_QTesla_Gauss__PRODIFF(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v,
  uint32_t k
)
{
  int64_t minuend = diff[0U] + (a_v[k] & Hacl_Impl_QTesla_Gauss__DFIELD);
  int64_t shifted = minuend - (a_u[k] & Hacl_Impl_QTesla_Gauss__DFIELD);
  diff[0U] =
    FStar_Int64_shift_arithmetic_right(shifted,
      Hacl_Impl_QTesla_Gauss__RADIX - (uint32_t)1U);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__PRODIFF */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__PROSWAP */

static void
Hacl_Impl_QTesla_Gauss__PROSWAP(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *swap1,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v,
  uint32_t k
)
{
  swap1[0U] = (a_u[k] ^ a_v[k]) & diff[0U];
  a_u[k] = a_u[k] ^ swap1[0U];
  a_v[k] = a_v[k] ^ swap1[0U];
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__PROSWAP */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__PROSWAPG */

static void
Hacl_Impl_QTesla_Gauss__PROSWAPG(int32_t *swap1, int64_t *diff, int32_t *g_u, int32_t *g_v)
{
  int64_t diffVal = diff[0U];
  swap1[0U] = (g_u[0U] ^ g_v[0U]) & (int32_t)diffVal;
  g_u[0U] = g_u[0U] ^ swap1[0U];
  g_v[0U] = g_v[0U] ^ swap1[0U];
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__PROSWAPG */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINMAX0 */

static void
Hacl_Impl_QTesla_Gauss__MINMAX0(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *swap1,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v
)
{
  Hacl_Impl_QTesla_Gauss__PRODIFF(n_u, n_v, diff, a_u, a_v, (uint32_t)0U);
  Hacl_Impl_QTesla_Gauss__PROSWAP(n_u, n_v, swap1, diff, a_u, a_v, (uint32_t)0U);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINMAX0 */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINMAX1 */

static void
Hacl_Impl_QTesla_Gauss__MINMAX1(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *swap1,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v
)
{
  if (Hacl_Impl_QTesla_Gauss__CDT_COLS > (uint32_t)1U)
  {
    Hacl_Impl_QTesla_Gauss__PRODIFF(n_u, n_v, diff, a_u, a_v, (uint32_t)1U);
    Hacl_Impl_QTesla_Gauss__MINMAX0(n_u, n_v, swap1, diff, a_u, a_v);
    Hacl_Impl_QTesla_Gauss__PROSWAP(n_u, n_v, swap1, diff, a_u, a_v, (uint32_t)1U);
    return;
  }
  Hacl_Impl_QTesla_Gauss__MINMAX0(n_u, n_v, swap1, diff, a_u, a_v);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINMAX1 */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINMAX2 */

static void
Hacl_Impl_QTesla_Gauss__MINMAX2(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *swap1,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v
)
{
  if (Hacl_Impl_QTesla_Gauss__CDT_COLS > (uint32_t)2U)
  {
    Hacl_Impl_QTesla_Gauss__PRODIFF(n_u, n_v, diff, a_u, a_v, (uint32_t)2U);
    Hacl_Impl_QTesla_Gauss__MINMAX1(n_u, n_v, swap1, diff, a_u, a_v);
    Hacl_Impl_QTesla_Gauss__PROSWAP(n_u, n_v, swap1, diff, a_u, a_v, (uint32_t)2U);
    return;
  }
  Hacl_Impl_QTesla_Gauss__MINMAX1(n_u, n_v, swap1, diff, a_u, a_v);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINMAX2 */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINMAX3 */

static void
Hacl_Impl_QTesla_Gauss__MINMAX3(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *swap1,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v
)
{
  if (Hacl_Impl_QTesla_Gauss__CDT_COLS > (uint32_t)3U)
  {
    Hacl_Impl_QTesla_Gauss__PRODIFF(n_u, n_v, diff, a_u, a_v, (uint32_t)3U);
    Hacl_Impl_QTesla_Gauss__MINMAX2(n_u, n_v, swap1, diff, a_u, a_v);
    Hacl_Impl_QTesla_Gauss__PROSWAP(n_u, n_v, swap1, diff, a_u, a_v, (uint32_t)3U);
    return;
  }
  Hacl_Impl_QTesla_Gauss__MINMAX2(n_u, n_v, swap1, diff, a_u, a_v);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINMAX3 */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINMAX4 */

static void
Hacl_Impl_QTesla_Gauss__MINMAX4(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *swap1,
  int64_t *diff,
  int64_t *a_u,
  int64_t *a_v
)
{
  if (Hacl_Impl_QTesla_Gauss__CDT_COLS > (uint32_t)4U)
  {
    Hacl_Impl_QTesla_Gauss__PRODIFF(n_u, n_v, diff, a_u, a_v, (uint32_t)4U);
    Hacl_Impl_QTesla_Gauss__MINMAX3(n_u, n_v, swap1, diff, a_u, a_v);
    Hacl_Impl_QTesla_Gauss__PROSWAP(n_u, n_v, swap1, diff, a_u, a_v, (uint32_t)4U);
    return;
  }
  Hacl_Impl_QTesla_Gauss__MINMAX3(n_u, n_v, swap1, diff, a_u, a_v);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINMAX4 */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINIMAX */

static void
Hacl_Impl_QTesla_Gauss__MINIMAX(
  uint32_t n_u,
  uint32_t n_v,
  int64_t *a_u,
  int64_t *a_v,
  int32_t *g_u,
  int32_t *g_v
)
{
  int64_t diff = (int64_t)0;
  int64_t swapa = (int64_t)0;
  int32_t swapg = (int32_t)0;
  Hacl_Impl_QTesla_Gauss__MINMAX4(n_u, n_v, &swapa, &diff, a_u, a_v);
  Hacl_Impl_QTesla_Gauss__PROSWAPG(&swapg, &diff, g_u, g_v);
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINIMAX */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss_knuthMergeExchangeKG */

static void Hacl_Impl_QTesla_Gauss_knuthMergeExchangeKG(uint32_t n1, int64_t *a, int32_t *g)
{
  uint32_t t = (uint32_t)1U;
  while (t < n1 - t)
  {
    t = t + t;
  }
  uint32_t pBuf = t;
  while (pBuf > (uint32_t)0U)
  {
    uint32_t p = pBuf;
    int64_t *ap = a + p * Hacl_Impl_QTesla_Gauss__CDT_COLS;
    uint32_t a_idx = (uint32_t)0U;
    uint32_t ap_idx = (uint32_t)0U;
    int32_t *gp = g + p;
    for (uint32_t i = (uint32_t)0U; i < n1 - p; i = i + (uint32_t)1U)
    {
      if ((i & p) == (uint32_t)0U)
      {
        uint32_t a_idxval = a_idx;
        int64_t *a_i = a + a_idxval;
        uint32_t ap_idxval = ap_idx;
        int64_t *ap_i = ap + ap_idxval;
        Hacl_Impl_QTesla_Gauss__MINIMAX(n1 - a_idxval,
          n1 - p - ap_idxval,
          a_i,
          ap_i,
          g + i,
          gp + i);
      }
      a_idx = a_idx + Hacl_Impl_QTesla_Gauss__CDT_COLS;
      ap_idx = ap_idx + Hacl_Impl_QTesla_Gauss__CDT_COLS;
    }
    uint32_t uu____0 = t;
    uint32_t uu____1 = pBuf;
    int64_t *ap1 = a + uu____1 * Hacl_Impl_QTesla_Gauss__CDT_COLS;
    int32_t *gp1 = g + uu____1;
    uint32_t qBuf = uu____0;
    while (qBuf > uu____1)
    {
      uint32_t q = qBuf;
      uint32_t ap_idx1 = (uint32_t)0U;
      uint32_t aq_idx = q * Hacl_Impl_QTesla_Gauss__CDT_COLS;
      int32_t *gq = g + q;
      for (uint32_t i = (uint32_t)0U; i < n1 - q; i = i + (uint32_t)1U)
      {
        if ((i & uu____1) == (uint32_t)0U)
        {
          uint32_t ap_idxval = ap_idx1;
          int64_t *ap_i = ap1 + ap_idxval;
          uint32_t aq_idxval = aq_idx;
          int64_t *aq_i = a + aq_idxval;
          Hacl_Impl_QTesla_Gauss__MINIMAX(n1 - uu____1 - ap_idxval,
            n1 - aq_idxval,
            ap_i,
            aq_i,
            gp1 + i,
            gq + i);
        }
        ap_idx1 = ap_idx1 + Hacl_Impl_QTesla_Gauss__CDT_COLS;
        aq_idx = aq_idx + Hacl_Impl_QTesla_Gauss__CDT_COLS;
      }
      qBuf = q >> (uint32_t)1U;
    }
    pBuf = p >> (uint32_t)1U;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss_knuthMergeExchangeKG */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss__MINMAXG */

static void Hacl_Impl_QTesla_Gauss__MINMAXG(int32_t *a_u, int32_t *a_v)
{
  int32_t
  diff =
    FStar_Int32_shift_arithmetic_right((a_v[0U] & (int32_t)0x7FFFFFFF)
      - (a_u[0U] & (int32_t)0x7FFFFFFF),
      Hacl_Impl_QTesla_Gauss__RADIX32 - (uint32_t)1U);
  int32_t swap1 = (a_u[0U] ^ a_v[0U]) & diff;
  a_u[0U] = a_u[0U] ^ swap1;
  a_v[0U] = a_v[0U] ^ swap1;
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss__MINMAXG */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss_knuthMergeExchangeG */

static void Hacl_Impl_QTesla_Gauss_knuthMergeExchangeG(uint32_t n1, int32_t *a)
{
  uint32_t t;
  uint32_t pBuf;
  if (!(n1 <= (uint32_t)1U))
  {
    t = (uint32_t)1U;
    while (t < n1 - t)
    {
      t = t + t;
    }
    pBuf = t;
    while (pBuf > (uint32_t)0U)
    {
      uint32_t p = pBuf;
      int32_t *ap = a + p;
      for (uint32_t i = (uint32_t)0U; i < n1 - p; i = i + (uint32_t)1U)
      {
        if ((i & p) == (uint32_t)0U)
        {
          Hacl_Impl_QTesla_Gauss__MINMAXG(a + i, ap + i);
        }
      }
      uint32_t qBuf = t;
      while (qBuf > p)
      {
        uint32_t q = qBuf;
        int32_t *aq = a + q;
        for (uint32_t i = (uint32_t)0U; i < n1 - q; i = i + (uint32_t)1U)
        {
          if ((i & p) == (uint32_t)0U)
          {
            Hacl_Impl_QTesla_Gauss__MINMAXG(ap + i, aq + i);
          }
        }
        qBuf = q >> (uint32_t)1U;
      }
      pBuf = p >> (uint32_t)1U;
    }
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss_knuthMergeExchangeG */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss_cSHAKE_sampk */

static void Hacl_Impl_QTesla_Gauss_cSHAKE_sampk(int64_t *sampk, uint16_t nonce, uint8_t *seed)
{
  KRML_CHECK_SIZE(sizeof (uint8_t),
    ((uint32_t)512U + (uint32_t)209U) * (uint32_t)1U * (uint32_t)8U);
  uint8_t sampk_binary[((uint32_t)512U + (uint32_t)209U) * (uint32_t)1U * (uint32_t)8U];
  memset(sampk_binary,
    0U,
    ((uint32_t)512U + (uint32_t)209U) * (uint32_t)1U * (uint32_t)8U * sizeof sampk_binary[0U]);
  Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
    seed,
    nonce,
    (Hacl_Impl_QTesla_Gauss__CHUNK_SIZE + Hacl_Impl_QTesla_Gauss__CDT_ROWS)
    * Hacl_Impl_QTesla_Gauss__CDT_COLS
    * (uint32_t)8U,
    sampk_binary);
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < Hacl_Impl_QTesla_Gauss__CHUNK_SIZE * Hacl_Impl_QTesla_Gauss__CDT_COLS;
    i = i + (uint32_t)1U)
  {
    uint64_t u = load64_le(sampk_binary + i * (uint32_t)8U);
    uint64_t uintval = u;
    sampk[i] = (int64_t)uintval;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss_cSHAKE_sampk */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss_kmxGauss */

static void Hacl_Impl_QTesla_Gauss_kmxGauss(int32_t *z, uint8_t *seed, uint32_t nonce)
{
  int64_t
  cdt_v[209U] =
    {
      (int64_t)0x0000000000000000, (int64_t)0x023A1B3F94933202, (int64_t)0x06AD3C4C19410B24,
      (int64_t)0x0B1D1E95803CBB73, (int64_t)0x0F879D85E7AB7F6F, (int64_t)0x13EA9C5C52732915,
      (int64_t)0x18440933FFD2011B, (int64_t)0x1C91DFF191E15D07, (int64_t)0x20D22D0F2017900D,
      (int64_t)0x25031040C1E626EF, (int64_t)0x2922BEEBA163019D, (int64_t)0x2D2F866A3C5122D3,
      (int64_t)0x3127CE192059EF64, (int64_t)0x350A1928231CB01A, (int64_t)0x38D5082CD4FCC414,
      (int64_t)0x3C875A73B33ADA6B, (int64_t)0x401FEF0E67CD47D3, (int64_t)0x439DC59E3077B59C,
      (int64_t)0x46FFFEDA4FC0A316, (int64_t)0x4A45DCD32E9CAA91, (int64_t)0x4D6EC2F3922E5C24,
      (int64_t)0x507A35C1FB354670, (int64_t)0x5367DA64EA5F1C63, (int64_t)0x563775ED5B93E26E,
      (int64_t)0x58E8EC6B50CB95F8, (int64_t)0x5B7C3FD0B999197D, (int64_t)0x5DF18EA7664D810E,
      (int64_t)0x6049129F03B5CD6D, (int64_t)0x62831EF856A48427, (int64_t)0x64A01ED314BA206F,
      (int64_t)0x66A09363CA89DAA3, (int64_t)0x688512173EF213F5, (int64_t)0x6A4E42A8B137E138,
      (int64_t)0x6BFCDD302C5B888A, (int64_t)0x6D91A82DF797EAB8, (int64_t)0x6F0D7697EBA6A51D,
      (int64_t)0x707125ED27F05CF1, (int64_t)0x71BD9C544C184D8D, (int64_t)0x72F3C6C7FB380322,
      (int64_t)0x74149755088E5CC6, (int64_t)0x7521036D434271D4, (int64_t)0x761A02516A02B0CE,
      (int64_t)0x77008B9461817A43, (int64_t)0x77D595B95BC6A0FE, (int64_t)0x789A14EE338BB727,
      (int64_t)0x794EF9E2D7C53213, (int64_t)0x79F530BE414FE24D, (int64_t)0x7A8DA03110886732,
      (int64_t)0x7B1928A59B3AA79E, (int64_t)0x7B98A38CE58D06AE, (int64_t)0x7C0CE2C7BAD3164A,
      (int64_t)0x7C76B02ADDE64EF2, (int64_t)0x7CD6CD1D13EE98F2, (int64_t)0x7D2DF24DA06E2473,
      (int64_t)0x7D7CCF81A5CD98B9, (int64_t)0x7DC40B76C24FB5D4, (int64_t)0x7E0443D92DE22661,
      (int64_t)0x7E3E0D4B91401720, (int64_t)0x7E71F37EC9C1DE8D, (int64_t)0x7EA07957CE6B9051,
      (int64_t)0x7ECA1921F1AF6404, (int64_t)0x7EEF44CBC73DA35B, (int64_t)0x7F10662D0574233D,
      (int64_t)0x7F2DDF53CDDCD427, (int64_t)0x7F480AD7DF028A76, (int64_t)0x7F5F3C324B0F66B2,
      (int64_t)0x7F73C018698C18A7, (int64_t)0x7F85DCD8D69F8939, (int64_t)0x7F95D2B96ED3DA10,
      (int64_t)0x7FA3DC55532D71BB, (int64_t)0x7FB02EFA1DDDC61E, (int64_t)0x7FBAFB038BAE76E4,
      (int64_t)0x7FC46C34F918B3E3, (int64_t)0x7FCCAA102B95464C, (int64_t)0x7FD3D828F7D49092,
      (int64_t)0x7FDA16756C11CF83, (int64_t)0x7FDF819A3A7BFE69, (int64_t)0x7FE4333332A5FEBD,
      (int64_t)0x7FE84217AA0DE2B3, (int64_t)0x7FEBC29AC3100A8B, (int64_t)0x7FEEC6C78F0D514E,
      (int64_t)0x7FF15E9914396F2A, (int64_t)0x7FF3982E4982FB97, (int64_t)0x7FF57FFA236862D1,
      (int64_t)0x7FF720EFD36F4850, (int64_t)0x7FF884AB61732BC7, (int64_t)0x7FF9B396CA3B383C,
      (int64_t)0x7FFAB50BD1DD3633, (int64_t)0x7FFB8F72BA84114B, (int64_t)0x7FFC485E115A3388,
      (int64_t)0x7FFCE4A3C3B92B98, (int64_t)0x7FFD6873AE755E4A, (int64_t)0x7FFDD76BD840FDA1,
      (int64_t)0x7FFE34AA86CE6870, (int64_t)0x7FFE82DE5CA6A885, (int64_t)0x7FFEC454ABAA26DF,
      (int64_t)0x7FFEFB0625FADB89, (int64_t)0x7FFF28A214B1160F, (int64_t)0x7FFF4E983945429D,
      (int64_t)0x7FFF6E217C168A6A, (int64_t)0x7FFF884787F2B986, (int64_t)0x7FFF9DEB70088602,
      (int64_t)0x7FFFAFCB7B419E48, (int64_t)0x7FFFBE882DABB8F8, (int64_t)0x7FFFCAA8A65BDA07,
      (int64_t)0x7FFFD49E66188754, (int64_t)0x7FFFDCC891191605, (int64_t)0x7FFFE376BC4B0583,
      (int64_t)0x7FFFE8EB54D33209, (int64_t)0x7FFFED5DAEE78F4E, (int64_t)0x7FFFF0FBC7A6933D,
      (int64_t)0x7FFFF3EBC43A9213, (int64_t)0x7FFFF64D375FC4CC, (int64_t)0x7FFFF83A354A0431,
      (int64_t)0x7FFFF9C83CE9BB0D, (int64_t)0x7FFFFB08FCAC61A6, (int64_t)0x7FFFFC0AF80A1A6F,
      (int64_t)0x7FFFFCDA127DDE76, (int64_t)0x7FFFFD8003E62E56, (int64_t)0x7FFFFE04B9BF9C5B,
      (int64_t)0x7FFFFE6EA82EF9BD, (int64_t)0x7FFFFEC30D64CD46, (int64_t)0x7FFFFF0629856684,
      (int64_t)0x7FFFFF3B6CEEE3F1, (int64_t)0x7FFFFF659E6F7BA6, (int64_t)0x7FFFFF86FAC1036A,
      (int64_t)0x7FFFFFA14E69EDE9, (int64_t)0x7FFFFFB60AF6ACB7, (int64_t)0x7FFFFFC65857AECF,
      (int64_t)0x7FFFFFD3230F314F, (int64_t)0x7FFFFFDD27BE0A17, (int64_t)0x7FFFFFE4FC86CDFF,
      (int64_t)0x7FFFFFEB18AA9E4C, (int64_t)0x7FFFFFEFDAB1FD73, (int64_t)0x7FFFFFF38D65D499,
      (int64_t)0x7FFFFFF66BD0EB8C, (int64_t)0x7FFFFFF8A4782371, (int64_t)0x7FFFFFFA5BEF7C27,
      (int64_t)0x7FFFFFFBAEEB0B4C, (int64_t)0x7FFFFFFCB3E55903, (int64_t)0x7FFFFFFD7C6FE192,
      (int64_t)0x7FFFFFFE163E99E3, (int64_t)0x7FFFFFFE8BFC2558, (int64_t)0x7FFFFFFEE5F1CE80,
      (int64_t)0x7FFFFFFF2A8C31FD, (int64_t)0x7FFFFFFF5EC3CD18, (int64_t)0x7FFFFFFF866F376B,
      (int64_t)0x7FFFFFFFA483A906, (int64_t)0x7FFFFFFFBB4780C4, (int64_t)0x7FFFFFFFCC79BEB2,
      (int64_t)0x7FFFFFFFD970CBE1, (int64_t)0x7FFFFFFFE3326D21, (int64_t)0x7FFFFFFFEA865AB8,
      (int64_t)0x7FFFFFFFF004A7C8, (int64_t)0x7FFFFFFFF420E4F9, (int64_t)0x7FFFFFFFF732B791,
      (int64_t)0x7FFFFFFFF97C764F, (int64_t)0x7FFFFFFFFB303DDD, (int64_t)0x7FFFFFFFFC73D5A3,
      (int64_t)0x7FFFFFFFFD63AA57, (int64_t)0x7FFFFFFFFE15140D, (int64_t)0x7FFFFFFFFE981196,
      (int64_t)0x7FFFFFFFFEF89992, (int64_t)0x7FFFFFFFFF3F9A0C, (int64_t)0x7FFFFFFFFF73BA0B,
      (int64_t)0x7FFFFFFFFF99EBBB, (int64_t)0x7FFFFFFFFFB5DAA0, (int64_t)0x7FFFFFFFFFCA3E7B,
      (int64_t)0x7FFFFFFFFFD91985, (int64_t)0x7FFFFFFFFFE3E70A, (int64_t)0x7FFFFFFFFFEBBE45,
      (int64_t)0x7FFFFFFFFFF16C5C, (int64_t)0x7FFFFFFFFFF587BE, (int64_t)0x7FFFFFFFFFF87E7F,
      (int64_t)0x7FFFFFFFFFFAA108, (int64_t)0x7FFFFFFFFFFC29F5, (int64_t)0x7FFFFFFFFFFD43E8,
      (int64_t)0x7FFFFFFFFFFE0DD7, (int64_t)0x7FFFFFFFFFFE9E31, (int64_t)0x7FFFFFFFFFFF0530,
      (int64_t)0x7FFFFFFFFFFF4E88, (int64_t)0x7FFFFFFFFFFF82AA, (int64_t)0x7FFFFFFFFFFFA7A6,
      (int64_t)0x7FFFFFFFFFFFC1D6, (int64_t)0x7FFFFFFFFFFFD458, (int64_t)0x7FFFFFFFFFFFE166,
      (int64_t)0x7FFFFFFFFFFFEA97, (int64_t)0x7FFFFFFFFFFFF10C, (int64_t)0x7FFFFFFFFFFFF594,
      (int64_t)0x7FFFFFFFFFFFF8C0, (int64_t)0x7FFFFFFFFFFFFAF7, (int64_t)0x7FFFFFFFFFFFFC83,
      (int64_t)0x7FFFFFFFFFFFFD96, (int64_t)0x7FFFFFFFFFFFFE56, (int64_t)0x7FFFFFFFFFFFFEDA,
      (int64_t)0x7FFFFFFFFFFFFF36, (int64_t)0x7FFFFFFFFFFFFF75, (int64_t)0x7FFFFFFFFFFFFFA1,
      (int64_t)0x7FFFFFFFFFFFFFBF, (int64_t)0x7FFFFFFFFFFFFFD4, (int64_t)0x7FFFFFFFFFFFFFE2,
      (int64_t)0x7FFFFFFFFFFFFFEC, (int64_t)0x7FFFFFFFFFFFFFF2, (int64_t)0x7FFFFFFFFFFFFFF7,
      (int64_t)0x7FFFFFFFFFFFFFFA, (int64_t)0x7FFFFFFFFFFFFFFC, (int64_t)0x7FFFFFFFFFFFFFFD,
      (int64_t)0x7FFFFFFFFFFFFFFE, (int64_t)0x7FFFFFFFFFFFFFFF
    };
  KRML_CHECK_SIZE(sizeof (int64_t), ((uint32_t)512U + (uint32_t)209U) * (uint32_t)1U);
  int64_t sampk[((uint32_t)512U + (uint32_t)209U) * (uint32_t)1U];
  memset(sampk, 0U, ((uint32_t)512U + (uint32_t)209U) * (uint32_t)1U * sizeof sampk[0U]);
  KRML_CHECK_SIZE(sizeof (int32_t), (uint32_t)512U + (uint32_t)209U);
  int32_t sampg[(uint32_t)512U + (uint32_t)209U];
  memset(sampg, 0U, ((uint32_t)512U + (uint32_t)209U) * sizeof sampg[0U]);
  Hacl_Impl_QTesla_Gauss_cSHAKE_sampk(sampk, (uint16_t)nonce, seed);
  memcpy(sampk + Hacl_Impl_QTesla_Gauss__CHUNK_SIZE * Hacl_Impl_QTesla_Gauss__CDT_COLS,
    cdt_v,
    Hacl_Impl_QTesla_Gauss__CDT_ROWS * Hacl_Impl_QTesla_Gauss__CDT_COLS * sizeof cdt_v[0U]);
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Gauss__CHUNK_SIZE; i = i + (uint32_t)1U)
  {
    sampg[i] = (int32_t)i << (uint32_t)16U;
  }
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Gauss__CDT_ROWS; i = i + (uint32_t)1U)
  {
    sampg[Hacl_Impl_QTesla_Gauss__CHUNK_SIZE + i] = (int32_t)(uint32_t)0xFFFF0000U ^ (int32_t)i;
  }
  Hacl_Impl_QTesla_Gauss_knuthMergeExchangeKG(Hacl_Impl_QTesla_Gauss__CHUNK_SIZE
    + Hacl_Impl_QTesla_Gauss__CDT_ROWS,
    sampk,
    sampg);
  int32_t prev_inx = (int32_t)0;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < Hacl_Impl_QTesla_Gauss__CHUNK_SIZE + Hacl_Impl_QTesla_Gauss__CDT_ROWS;
    i = i + (uint32_t)1U)
  {
    int32_t curr_inx = sampg[i] & (int32_t)0xFFFF;
    int32_t uu____0 = prev_inx;
    int32_t uu____1 = curr_inx ^ prev_inx;
    prev_inx =
      uu____0
      ^
        (uu____1
        &
          FStar_Int32_shift_arithmetic_right(prev_inx - curr_inx,
            Hacl_Impl_QTesla_Gauss__RADIX32 - (uint32_t)1U));
    int64_t
    neg =
      FStar_Int64_shift_arithmetic_right(sampk[i * Hacl_Impl_QTesla_Gauss__CDT_COLS],
        Hacl_Impl_QTesla_Gauss__RADIX - (uint32_t)1U);
    int32_t neg1 = (int32_t)neg;
    sampg[i] =
      sampg[i]
      | (((neg1 & (int32_t)-1 * prev_inx) ^ (~neg1 & prev_inx)) & (int32_t)0xFFFF);
  }
  Hacl_Impl_QTesla_Gauss_knuthMergeExchangeG(Hacl_Impl_QTesla_Gauss__CHUNK_SIZE
    + Hacl_Impl_QTesla_Gauss__CDT_ROWS,
    sampg);
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Gauss__CHUNK_SIZE; i = i + (uint32_t)1U)
  {
    int32_t
    result =
      FStar_Int32_shift_arithmetic_right(sampg[i]
        << (Hacl_Impl_QTesla_Gauss__RADIX32 - (uint32_t)16U),
        Hacl_Impl_QTesla_Gauss__RADIX32 - (uint32_t)16U);
    z[i] = result;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss_kmxGauss */

/* SNIPPET_START: Hacl_Impl_QTesla_Gauss_sample_gauss_poly */

static void Hacl_Impl_QTesla_Gauss_sample_gauss_poly(int32_t *z, uint8_t *seed, uint32_t nonce)
{
  uint32_t dmsp = nonce << (uint32_t)8U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < Hacl_Impl_QTesla_Params_params_n / Hacl_Impl_QTesla_Gauss__CHUNK_SIZE;
    i = i + (uint32_t)1U)
  {
    uint32_t chunk = i * Hacl_Impl_QTesla_Gauss__CHUNK_SIZE;
    Hacl_Impl_QTesla_Gauss_kmxGauss(z + chunk, seed, dmsp);
    dmsp = dmsp + (uint32_t)1U;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_Gauss_sample_gauss_poly */

/* SNIPPET_START: Hacl_Impl_QTesla__RADIX32 */

static uint32_t Hacl_Impl_QTesla__RADIX32 = (uint32_t)32U;

/* SNIPPET_END: Hacl_Impl_QTesla__RADIX32 */

/* SNIPPET_START: Hacl_Impl_QTesla_abs_ */

int32_t Hacl_Impl_QTesla_abs_(int32_t value)
{
  int32_t mask = FStar_Int32_shift_arithmetic_right(value, (uint32_t)31U);
  return (value ^ mask) - mask;
}

/* SNIPPET_END: Hacl_Impl_QTesla_abs_ */

/* SNIPPET_START: Hacl_Impl_QTesla_check_ES */

bool Hacl_Impl_QTesla_check_ES(int32_t *p, uint32_t bound)
{
  uint32_t sum = (uint32_t)0U;
  uint32_t limit = Hacl_Impl_QTesla_Params_params_n;
  int32_t list[512U] = { 0 };
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t pj = p[i];
    int32_t abspj = Hacl_Impl_QTesla_abs_(pj);
    list[i] = abspj;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < Hacl_Impl_QTesla_Params_params_h; i0 = i0 + (uint32_t)1U)
  {
    uint32_t loopMax = limit - (uint32_t)1U;
    for (uint32_t i = (uint32_t)0U; i < loopMax; i = i + (uint32_t)1U)
    {
      int32_t a = list[i + (uint32_t)1U] - list[i];
      int32_t
      mask = FStar_Int32_shift_arithmetic_right(a, Hacl_Impl_QTesla__RADIX32 - (uint32_t)1U);
      int32_t temp = (list[i + (uint32_t)1U] & mask) | (list[i] & ~mask);
      list[i + (uint32_t)1U] = (list[i] & mask) | (list[i + (uint32_t)1U] & ~mask);
      list[i] = temp;
    }
    uint32_t listIndex = limit - (uint32_t)1U;
    int32_t listAmt = list[listIndex];
    sum = sum + (uint32_t)listAmt;
    limit = limit - (uint32_t)1U;
  }
  uint32_t sumAmt = sum;
  return sumAmt > bound;
}

/* SNIPPET_END: Hacl_Impl_QTesla_check_ES */

/* SNIPPET_START: Hacl_Impl_QTesla_poly_uniform */

void Hacl_Impl_QTesla_poly_uniform(int32_t *a, uint8_t *seed)
{
  uint32_t pos = (uint32_t)0U;
  uint32_t i = (uint32_t)0U;
  uint32_t nblocks = Hacl_Impl_QTesla_Params_params_genA;
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)3192U + (uint32_t)1U);
  uint8_t buf1[(uint32_t)3192U + (uint32_t)1U];
  memset(buf1, 0U, ((uint32_t)3192U + (uint32_t)1U) * sizeof buf1[0U]);
  uint16_t dmsp = (uint16_t)0U;
  Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
    seed,
    dmsp,
    (uint32_t)168U * Hacl_Impl_QTesla_Params_params_genA,
    buf1);
  dmsp = dmsp + (uint16_t)1U;
  while (i < Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_params_n)
  {
    uint32_t nbytes1 = (Hacl_Impl_QTesla_Params_params_q_log + (uint32_t)7U) / (uint32_t)8U;
    if (pos > (uint32_t)168U * nblocks - (uint32_t)4U * nbytes1)
    {
      nblocks = (uint32_t)1U;
      uint32_t bufSize = (uint32_t)168U * nblocks;
      uint8_t *subbuff = buf1;
      Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
        seed,
        dmsp,
        bufSize,
        subbuff);
      dmsp = dmsp + (uint16_t)1U;
      pos = (uint32_t)0U;
    }
    uint32_t pos0 = pos;
    uint32_t mask0 = ((uint32_t)1U << Hacl_Impl_QTesla_Params_params_q_log) - (uint32_t)1U;
    uint32_t u0 = load32_le(buf1 + pos0);
    uint32_t bufPosAsUint = u0;
    uint32_t val1 = bufPosAsUint & mask0;
    pos = pos + nbytes1;
    uint32_t pos01 = pos;
    uint32_t mask1 = ((uint32_t)1U << Hacl_Impl_QTesla_Params_params_q_log) - (uint32_t)1U;
    uint32_t u1 = load32_le(buf1 + pos01);
    uint32_t bufPosAsUint0 = u1;
    uint32_t val2 = bufPosAsUint0 & mask1;
    pos = pos + nbytes1;
    uint32_t pos02 = pos;
    uint32_t mask2 = ((uint32_t)1U << Hacl_Impl_QTesla_Params_params_q_log) - (uint32_t)1U;
    uint32_t u2 = load32_le(buf1 + pos02);
    uint32_t bufPosAsUint1 = u2;
    uint32_t val3 = bufPosAsUint1 & mask2;
    pos = pos + nbytes1;
    uint32_t pos03 = pos;
    uint32_t mask = ((uint32_t)1U << Hacl_Impl_QTesla_Params_params_q_log) - (uint32_t)1U;
    uint32_t u = load32_le(buf1 + pos03);
    uint32_t bufPosAsUint2 = u;
    uint32_t val4 = bufPosAsUint2 & mask;
    pos = pos + nbytes1;
    uint32_t params_q1 = (uint32_t)Hacl_Impl_QTesla_Params_params_q;
    uint32_t i10 = i;
    if
    (val1 < params_q1 && i10 < Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_params_n)
    {
      a[i10] =
        Hacl_Impl_QTesla_Globals_reduce((int64_t)val1 * Hacl_Impl_QTesla_Params_params_r2_invn);
      i = i10 + (uint32_t)1U;
    }
    uint32_t params_q10 = (uint32_t)Hacl_Impl_QTesla_Params_params_q;
    uint32_t i11 = i;
    if
    (
      val2
      < params_q10
      && i11 < Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_params_n
    )
    {
      a[i11] =
        Hacl_Impl_QTesla_Globals_reduce((int64_t)val2 * Hacl_Impl_QTesla_Params_params_r2_invn);
      i = i11 + (uint32_t)1U;
    }
    uint32_t params_q11 = (uint32_t)Hacl_Impl_QTesla_Params_params_q;
    uint32_t i12 = i;
    if
    (
      val3
      < params_q11
      && i12 < Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_params_n
    )
    {
      a[i12] =
        Hacl_Impl_QTesla_Globals_reduce((int64_t)val3 * Hacl_Impl_QTesla_Params_params_r2_invn);
      i = i12 + (uint32_t)1U;
    }
    uint32_t params_q12 = (uint32_t)Hacl_Impl_QTesla_Params_params_q;
    uint32_t i1 = i;
    if
    (val4 < params_q12 && i1 < Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_params_n)
    {
      a[i1] =
        Hacl_Impl_QTesla_Globals_reduce((int64_t)val4 * Hacl_Impl_QTesla_Params_params_r2_invn);
      i = i1 + (uint32_t)1U;
    }
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_poly_uniform */

/* SNIPPET_START: Hacl_Impl_QTesla_qtesla_keygen */

int32_t Hacl_Impl_QTesla_qtesla_keygen(uint8_t *pk, uint8_t *sk)
{
  uint8_t randomness[32U] = { 0U };
  bool
  uu____0 =
    Lib_RandomBuffer_System_randombytes(randomness,
      Hacl_Impl_QTesla_Params_crypto_randombytes);
  KRML_CHECK_SIZE(sizeof (uint8_t), ((uint32_t)1U + (uint32_t)3U) * (uint32_t)32U);
  uint8_t randomness_extended[((uint32_t)1U + (uint32_t)3U) * (uint32_t)32U];
  memset(randomness_extended,
    0U,
    ((uint32_t)1U + (uint32_t)3U) * (uint32_t)32U * sizeof randomness_extended[0U]);
  int32_t e[512U] = { 0 };
  int32_t s[512U] = { 0 };
  int32_t s_ntt[512U] = { 0 };
  int32_t a[512U] = { 0 };
  int32_t t[512U] = { 0 };
  uint32_t nonce = (uint32_t)0U;
  Hacl_SHA3_shake128_hacl(Hacl_Impl_QTesla_Params_crypto_randombytes,
    randomness,
    (Hacl_Impl_QTesla_Params_params_k + (uint32_t)3U) * Hacl_Impl_QTesla_Params_crypto_seedbytes,
    randomness_extended);
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_k; i = i + (uint32_t)1U)
  {
    while (true)
    {
      int32_t *ek = e + i * Hacl_Impl_QTesla_Params_params_n;
      uint8_t *subbuffer = randomness_extended + i * Hacl_Impl_QTesla_Params_crypto_seedbytes;
      uint32_t nonce0 = nonce;
      nonce = nonce0 + (uint32_t)1U;
      uint32_t nonce1 = nonce;
      Hacl_Impl_QTesla_Gauss_sample_gauss_poly(ek, subbuffer, nonce1);
      bool res = !Hacl_Impl_QTesla_check_ES(ek, Hacl_Impl_QTesla_Params_params_Le);
      if (res)
      {
        break;
      }
    }
  }
  while (true)
  {
    uint8_t
    *subbuffer =
      randomness_extended
      + Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_crypto_seedbytes;
    uint32_t nonce0 = nonce;
    nonce = nonce0 + (uint32_t)1U;
    uint32_t nonce1 = nonce;
    Hacl_Impl_QTesla_Gauss_sample_gauss_poly(s, subbuffer, nonce1);
    bool res = !Hacl_Impl_QTesla_check_ES(s, Hacl_Impl_QTesla_Params_params_Ls);
    if (res)
    {
      break;
    }
  }
  uint8_t
  *rndsubbuffer =
    randomness_extended
    + (Hacl_Impl_QTesla_Params_params_k + (uint32_t)1U) * Hacl_Impl_QTesla_Params_crypto_seedbytes;
  Hacl_Impl_QTesla_poly_uniform(a, rndsubbuffer);
  Hacl_Impl_QTesla_Poly_poly_ntt(s_ntt, s);
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_k; i = i + (uint32_t)1U)
  {
    int32_t *tk = t + i * Hacl_Impl_QTesla_Params_params_n;
    int32_t *ak = a + i * Hacl_Impl_QTesla_Params_params_n;
    int32_t *ek = e + i * Hacl_Impl_QTesla_Params_params_n;
    Hacl_Impl_QTesla_Poly_poly_mul(tk, ak, s_ntt);
    Hacl_Impl_QTesla_Heuristic_Poly_poly_add_correct(tk, tk, ek);
  }
  Hacl_Impl_QTesla_Pack_encode_sk(sk, s, e, rndsubbuffer);
  Hacl_Impl_QTesla_Heuristic_Pack_encode_pk(pk, t, rndsubbuffer);
  int32_t r = (int32_t)0;
  return r;
}

/* SNIPPET_END: Hacl_Impl_QTesla_qtesla_keygen */

/* SNIPPET_START: Hacl_Impl_QTesla_nblocks_shake */

static uint32_t Hacl_Impl_QTesla_nblocks_shake = (uint32_t)56U;

/* SNIPPET_END: Hacl_Impl_QTesla_nblocks_shake */

/* SNIPPET_START: Hacl_Impl_QTesla_bplus1bytes */

static uint32_t Hacl_Impl_QTesla_bplus1bytes = (uint32_t)3U;

/* SNIPPET_END: Hacl_Impl_QTesla_bplus1bytes */

/* SNIPPET_START: Hacl_Impl_QTesla_sample_y */

void Hacl_Impl_QTesla_sample_y(int32_t *y, uint8_t *seed, uint32_t nonce)
{
  uint32_t i = (uint32_t)0U;
  uint32_t pos = (uint32_t)0U;
  uint32_t nblocks = Hacl_Impl_QTesla_Params_params_n;
  uint8_t buf1[1537U] = { 0U };
  uint32_t nbytes = Hacl_Impl_QTesla_bplus1bytes;
  uint16_t dmsp = (uint16_t)(nonce << (uint32_t)8U);
  Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
    seed,
    dmsp,
    Hacl_Impl_QTesla_Params_params_n * nbytes,
    buf1);
  dmsp = dmsp + (uint16_t)1U;
  while (i < Hacl_Impl_QTesla_Params_params_n)
  {
    uint32_t nbytes1 = Hacl_Impl_QTesla_bplus1bytes;
    uint32_t nBlocksVal = nblocks;
    if (pos >= nBlocksVal * nbytes1)
    {
      nblocks = Hacl_Impl_QTesla_nblocks_shake;
      Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
        seed,
        dmsp,
        (uint32_t)168U,
        buf1);
      dmsp = dmsp + (uint16_t)1U;
      pos = (uint32_t)0U;
    }
    uint32_t pos0 = pos;
    uint8_t *subbuff = buf1 + pos0;
    uint32_t u = load32_le(subbuff);
    uint32_t bufPosAsU32 = u;
    int32_t bufPosAsElem = (int32_t)bufPosAsU32;
    uint32_t i0 = i;
    y[i0] = bufPosAsElem & (((int32_t)1 << (uint32_t)21U) - (int32_t)1);
    y[i0] = y[i0] - Hacl_Impl_QTesla_Params_params_B;
    if (y[i0] != (int32_t)1 << (uint32_t)20U)
    {
      i = i0 + (uint32_t)1U;
    }
    pos = pos + nbytes1;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_sample_y */

/* SNIPPET_START: Hacl_Impl_QTesla_hash_H */

void Hacl_Impl_QTesla_hash_H(uint8_t *c_bin, int32_t *v_, uint8_t *hm)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)512U + (uint32_t)64U);
  uint8_t t[(uint32_t)512U + (uint32_t)64U];
  memset(t, 0U, ((uint32_t)512U + (uint32_t)64U) * sizeof t[0U]);
  for (uint32_t i0 = (uint32_t)0U; i0 < Hacl_Impl_QTesla_Params_params_k; i0 = i0 + (uint32_t)1U)
  {
    for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
    {
      int32_t params_q1 = Hacl_Impl_QTesla_Params_params_q;
      int32_t vindex = v_[i0 * Hacl_Impl_QTesla_Params_params_n + i];
      int32_t temp = vindex;
      int32_t
      mask =
        FStar_Int32_shift_arithmetic_right(params_q1 / (int32_t)2 - temp,
          Hacl_Impl_QTesla__RADIX32 - (uint32_t)1U);
      int32_t temp1 = ((temp - params_q1) & mask) | (temp & ~mask);
      int32_t cL = temp1 & (((int32_t)1 << Hacl_Impl_QTesla_Params_params_d) - (int32_t)1);
      int32_t
      mask1 =
        FStar_Int32_shift_arithmetic_right(((int32_t)1
          << (Hacl_Impl_QTesla_Params_params_d - (uint32_t)1U))
          - cL,
          Hacl_Impl_QTesla__RADIX32 - (uint32_t)1U);
      int32_t
      cL1 = ((cL - ((int32_t)1 << Hacl_Impl_QTesla_Params_params_d)) & mask1) | (cL & ~mask1);
      t[i0 * Hacl_Impl_QTesla_Params_params_n + i] =
        (uint8_t)FStar_Int32_shift_arithmetic_right(temp1 - cL1, Hacl_Impl_QTesla_Params_params_d);
    }
  }
  memcpy(t + Hacl_Impl_QTesla_Params_params_k * Hacl_Impl_QTesla_Params_params_n,
    hm,
    Hacl_Impl_QTesla_Params_crypto_hmbytes * sizeof hm[0U]);
  Hacl_SHA3_shake128_hacl(Hacl_Impl_QTesla_Params_params_k
    * Hacl_Impl_QTesla_Params_params_n
    + Hacl_Impl_QTesla_Params_crypto_hmbytes,
    t,
    Hacl_Impl_QTesla_Params_crypto_c_bytes,
    c_bin);
}

/* SNIPPET_END: Hacl_Impl_QTesla_hash_H */

/* SNIPPET_START: Hacl_Impl_QTesla_encode_c */

void Hacl_Impl_QTesla_encode_c(uint32_t *pos_list, int16_t *sign_list, uint8_t *c_bin)
{
  int16_t c[512U] = { 0 };
  uint8_t r[168U] = { 0U };
  uint16_t dmsp = (uint16_t)0U;
  uint32_t cnt = (uint32_t)0U;
  uint32_t i = (uint32_t)0U;
  Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
    c_bin,
    dmsp,
    (uint32_t)168U,
    r);
  uint16_t dmspVal = dmsp;
  dmsp = dmspVal + (uint16_t)1U;
  while (i < Hacl_Impl_QTesla_Params_params_h)
  {
    uint32_t iVal = i;
    if (cnt > (uint32_t)168U - (uint32_t)3U)
    {
      Hacl_Impl_QTesla_Constants_cshake128_qtesla(Hacl_Impl_QTesla_Params_crypto_randombytes,
        c_bin,
        dmsp,
        (uint32_t)168U,
        r);
      dmsp = dmsp + (uint16_t)1U;
      cnt = (uint32_t)0U;
    }
    uint32_t cntVal = cnt;
    uint8_t rCntVal = r[cntVal];
    uint8_t rCntVal1 = r[cntVal + (uint32_t)1U];
    uint32_t pos = (uint32_t)rCntVal << (uint32_t)8U | (uint32_t)rCntVal1;
    uint32_t pos1 = pos & (Hacl_Impl_QTesla_Params_params_n - (uint32_t)1U);
    if (c[pos1] == (int16_t)0)
    {
      uint8_t rCntVal2 = r[cntVal + (uint32_t)2U];
      if ((rCntVal2 & (uint8_t)1U) == (uint8_t)1U)
      {
        c[pos1] = (int16_t)-1;
      }
      else
      {
        c[pos1] = (int16_t)1;
      }
      pos_list[iVal] = pos1;
      sign_list[iVal] = c[pos1];
      i = iVal + (uint32_t)1U;
    }
    cnt = cntVal + (uint32_t)3U;
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_encode_c */

/* SNIPPET_START: Hacl_Impl_QTesla_sparse_mul */

void
Hacl_Impl_QTesla_sparse_mul(int32_t *prod, int16_t *s, uint32_t *pos_list, int16_t *sign_list)
{
  int16_t *t = s;
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    prod[i] = (int32_t)0;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < Hacl_Impl_QTesla_Params_params_h; i0 = i0 + (uint32_t)1U)
  {
    uint32_t pos = pos_list[i0];
    for (uint32_t i = (uint32_t)0U; i < pos; i = i + (uint32_t)1U)
    {
      int16_t sign_list_i = sign_list[i0];
      int16_t tVal = t[i + Hacl_Impl_QTesla_Params_params_n - pos];
      prod[i] = prod[i] - (int32_t)(sign_list_i * tVal);
    }
    for (uint32_t i = pos; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
    {
      int16_t sign_list_i = sign_list[i0];
      int16_t tVal = t[i - pos];
      prod[i] = prod[i] + (int32_t)(sign_list_i * tVal);
    }
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_sparse_mul */

/* SNIPPET_START: Hacl_Impl_QTesla_sparse_mul32 */

void
Hacl_Impl_QTesla_sparse_mul32(
  int32_t *prod,
  int32_t *pk,
  uint32_t *pos_list,
  int16_t *sign_list
)
{
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    prod[i] = (int32_t)0;
  }
  for (uint32_t i0 = (uint32_t)0U; i0 < Hacl_Impl_QTesla_Params_params_h; i0 = i0 + (uint32_t)1U)
  {
    uint32_t pos = pos_list[i0];
    int16_t sign_list_i = sign_list[i0];
    for (uint32_t i = (uint32_t)0U; i < pos; i = i + (uint32_t)1U)
    {
      int32_t pkItem = pk[i + Hacl_Impl_QTesla_Params_params_n - pos];
      prod[i] = prod[i] - (int32_t)sign_list_i * pkItem;
    }
    for (uint32_t i = pos; i < Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
    {
      int32_t pkItem = pk[i - pos];
      prod[i] = prod[i] + (int32_t)sign_list_i * pkItem;
    }
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_sparse_mul32 */

/* SNIPPET_START: Hacl_Impl_QTesla_test_rejection */

bool Hacl_Impl_QTesla_test_rejection(int32_t *z)
{
  bool b = false;
  uint32_t i = (uint32_t)0U;
  for (; !b && i != Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t zi = z[i];
    int32_t zVal = zi;
    b =
      Hacl_Impl_QTesla_abs_(zVal)
      > Hacl_Impl_QTesla_Params_params_B - Hacl_Impl_QTesla_Params_params_U;
  }
  K___uint32_t_bool scrut = { .fst = i, .snd = b };
  return scrut.snd;
}

/* SNIPPET_END: Hacl_Impl_QTesla_test_rejection */

/* SNIPPET_START: Hacl_Impl_QTesla_test_correctness */

int32_t Hacl_Impl_QTesla_test_correctness(int32_t *v_)
{
  int32_t res = (int32_t)0;
  bool b = false;
  uint32_t i = (uint32_t)0U;
  for (; !b && i != Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t mask0 = Hacl_Impl_QTesla_Params_params_q / (int32_t)2 - v_[i];
    int32_t
    mask = FStar_Int32_shift_arithmetic_right(mask0, Hacl_Impl_QTesla__RADIX32 - (uint32_t)1U);
    int32_t val_ = ((v_[i] - Hacl_Impl_QTesla_Params_params_q) & mask) | (v_[i] & ~mask);
    int32_t val_1 = val_;
    uint32_t
    t0 =
      (uint32_t)~(Hacl_Impl_QTesla_abs_(val_1)
      - (Hacl_Impl_QTesla_Params_params_q / (int32_t)2 - Hacl_Impl_QTesla_Params_params_rejection))
      >> (Hacl_Impl_QTesla__RADIX32 - (uint32_t)1U);
    int32_t left = val_1;
    int32_t
    val__ =
      FStar_Int32_shift_arithmetic_right(val_1
        + ((int32_t)1 << (Hacl_Impl_QTesla_Params_params_d - (uint32_t)1U))
        - (int32_t)1,
        Hacl_Impl_QTesla_Params_params_d);
    int32_t val_2 = left - (int32_t)((uint32_t)val__ << Hacl_Impl_QTesla_Params_params_d);
    uint32_t
    t1 =
      (uint32_t)~(Hacl_Impl_QTesla_abs_(val_2)
      -
        (((int32_t)1 << (Hacl_Impl_QTesla_Params_params_d - (uint32_t)1U))
        - Hacl_Impl_QTesla_Params_params_rejection))
      >> (Hacl_Impl_QTesla__RADIX32 - (uint32_t)1U);
    bool r;
    if ((t0 | t1) == (uint32_t)1U)
    {
      res = (int32_t)1;
      r = true;
    }
    else
    {
      r = false;
    }
    b = r;
  }
  K___uint32_t_bool scrut = { .fst = i, .snd = b };
  return res;
}

/* SNIPPET_END: Hacl_Impl_QTesla_test_correctness */

/* SNIPPET_START: Hacl_Impl_QTesla_qtesla_sign */

void
Hacl_Impl_QTesla_qtesla_sign(
  uint32_t *smlen,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *sm,
  uint8_t *sk
)
{
  uint8_t randomness[32U] = { 0U };
  KRML_CHECK_SIZE(sizeof (uint8_t), (uint32_t)32U + (uint32_t)32U + (uint32_t)64U);
  uint8_t randomness_input[(uint32_t)32U + (uint32_t)32U + (uint32_t)64U];
  memset(randomness_input,
    0U,
    ((uint32_t)32U + (uint32_t)32U + (uint32_t)64U) * sizeof randomness_input[0U]);
  int32_t a[512U] = { 0 };
  uint8_t seeds[64U] = { 0U };
  int16_t s[512U] = { 0 };
  int16_t e[512U] = { 0 };
  uint32_t nonce = (uint32_t)0U;
  Hacl_Impl_QTesla_Pack_decode_sk(seeds, s, e, sk);
  uint8_t *subbuff = randomness_input + Hacl_Impl_QTesla_Params_crypto_randombytes;
  bool
  uu____0 =
    Lib_RandomBuffer_System_randombytes(subbuff,
      Hacl_Impl_QTesla_Params_crypto_randombytes);
  memcpy(randomness_input,
    seeds + Hacl_Impl_QTesla_Params_crypto_seedbytes,
    Hacl_Impl_QTesla_Params_crypto_seedbytes
    * sizeof (seeds + Hacl_Impl_QTesla_Params_crypto_seedbytes)[0U]);
  Hacl_SHA3_shake128_hacl(mlen,
    m,
    Hacl_Impl_QTesla_Params_crypto_hmbytes,
    randomness_input
    + Hacl_Impl_QTesla_Params_crypto_randombytes + Hacl_Impl_QTesla_Params_crypto_seedbytes);
  Hacl_SHA3_shake128_hacl(Hacl_Impl_QTesla_Params_crypto_randombytes
    + Hacl_Impl_QTesla_Params_crypto_seedbytes
    + Hacl_Impl_QTesla_Params_crypto_hmbytes,
    randomness_input,
    Hacl_Impl_QTesla_Params_crypto_seedbytes,
    randomness);
  Hacl_Impl_QTesla_poly_uniform(a, seeds);
  while (true)
  {
    uint8_t c[32U] = { 0U };
    int32_t z[512U] = { 0 };
    int32_t y[512U] = { 0 };
    int32_t v_[512U] = { 0 };
    int32_t rsp = (int32_t)0;
    uint32_t pos_list[30U] = { 0U };
    int16_t sign_list[30U] = { 0 };
    nonce = nonce + (uint32_t)1U;
    Hacl_Impl_QTesla_sample_y(y, randomness, nonce);
    int32_t y_ntt[512U] = { 0 };
    Hacl_Impl_QTesla_Poly_poly_ntt(y_ntt, y);
    for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_k; i = i + (uint32_t)1U)
    {
      Hacl_Impl_QTesla_Poly_poly_mul(v_ + i * Hacl_Impl_QTesla_Params_params_n,
        a + i * Hacl_Impl_QTesla_Params_params_n,
        y_ntt);
    }
    int32_t sc[512U] = { 0 };
    Hacl_Impl_QTesla_hash_H(c,
      v_,
      randomness_input
      + Hacl_Impl_QTesla_Params_crypto_randombytes + Hacl_Impl_QTesla_Params_crypto_seedbytes);
    Hacl_Impl_QTesla_encode_c(pos_list, sign_list, c);
    Hacl_Impl_QTesla_sparse_mul(sc, s, pos_list, sign_list);
    Hacl_Impl_QTesla_Heuristic_Poly_poly_add(z, y, sc);
    bool res;
    if (Hacl_Impl_QTesla_test_rejection(z))
    {
      res = false;
    }
    else
    {
      int32_t rsp1 = (int32_t)0;
      bool b = false;
      uint32_t i = (uint32_t)0U;
      for (; !b && i != Hacl_Impl_QTesla_Params_params_k; i = i + (uint32_t)1U)
      {
        int32_t ec[512U] = { 0 };
        int32_t *ec_k = ec + i * Hacl_Impl_QTesla_Params_params_n;
        int16_t *e_k = e + i * Hacl_Impl_QTesla_Params_params_n;
        Hacl_Impl_QTesla_sparse_mul(ec_k, e_k, pos_list, sign_list);
        Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_correct(v_ + i * Hacl_Impl_QTesla_Params_params_n,
          v_ + i * Hacl_Impl_QTesla_Params_params_n,
          ec_k);
        rsp1 = Hacl_Impl_QTesla_test_correctness(v_ + i * Hacl_Impl_QTesla_Params_params_n);
        int32_t rspVal = rsp1;
        b = rspVal != (int32_t)0;
      }
      K___uint32_t_bool scrut = { .fst = i, .snd = b };
      int32_t rspVal = rsp1;
      if (rspVal != (int32_t)0)
      {
        res = false;
      }
      else
      {
        for (uint32_t i0 = (uint32_t)0U; i0 < mlen; i0 = i0 + (uint32_t)1U)
        {
          uint32_t ix = Hacl_Impl_QTesla_Params_crypto_bytes + i0;
          sm[ix] = m[i0];
        }
        smlen[0U] = Hacl_Impl_QTesla_Params_crypto_bytes + mlen;
        Hacl_Impl_QTesla_Heuristic_Pack_encode_sig(sm, c, z);
        res = true;
      }
    }
    bool res0 = res;
    if (res0)
    {
      break;
    }
  }
}

/* SNIPPET_END: Hacl_Impl_QTesla_qtesla_sign */

/* SNIPPET_START: Hacl_Impl_QTesla_test_z */

int32_t Hacl_Impl_QTesla_test_z(int32_t *z)
{
  bool b = false;
  uint32_t i = (uint32_t)0U;
  for (; !b && i != Hacl_Impl_QTesla_Params_params_n; i = i + (uint32_t)1U)
  {
    int32_t zi = z[i];
    b =
      zi
      < (int32_t)-1 * (Hacl_Impl_QTesla_Params_params_B - Hacl_Impl_QTesla_Params_params_U)
      || zi > Hacl_Impl_QTesla_Params_params_B - Hacl_Impl_QTesla_Params_params_U;
  }
  K___uint32_t_bool scrut = { .fst = i, .snd = b };
  bool res = scrut.snd;
  if (res)
  {
    return (int32_t)1;
  }
  return (int32_t)0;
}

/* SNIPPET_END: Hacl_Impl_QTesla_test_z */

/* SNIPPET_START: Hacl_Impl_QTesla_qtesla_verify */

int32_t
Hacl_Impl_QTesla_qtesla_verify(
  uint32_t *mlen,
  uint32_t smlen,
  uint8_t *m,
  uint8_t *sm,
  uint8_t *pk
)
{
  if (smlen < Hacl_Impl_QTesla_Params_crypto_bytes)
  {
    return (int32_t)-1;
  }
  uint8_t c[32U] = { 0U };
  int32_t z[512U] = { 0 };
  Hacl_Impl_QTesla_Heuristic_Pack_decode_sig(c, z, sm);
  if (Hacl_Impl_QTesla_test_z(z) != (int32_t)0)
  {
    return (int32_t)-2;
  }
  uint8_t hm[64U] = { 0U };
  int32_t w[512U] = { 0 };
  uint8_t c_sig[32U] = { 0U };
  uint8_t seed[32U] = { 0U };
  uint32_t pos_list[30U] = { 0U };
  int16_t sign_list[30U] = { 0 };
  int32_t pk_t[512U] = { 0 };
  int32_t z_ntt[512U] = { 0 };
  int32_t tc[512U] = { 0 };
  int32_t a[512U] = { 0 };
  Hacl_Impl_QTesla_Heuristic_Pack_decode_pk(pk_t, seed, pk);
  Hacl_Impl_QTesla_poly_uniform(a, seed);
  Hacl_Impl_QTesla_encode_c(pos_list, sign_list, c);
  Hacl_Impl_QTesla_Poly_poly_ntt(z_ntt, z);
  for (uint32_t i = (uint32_t)0U; i < Hacl_Impl_QTesla_Params_params_k; i = i + (uint32_t)1U)
  {
    Hacl_Impl_QTesla_Poly_poly_mul(w + i * Hacl_Impl_QTesla_Params_params_n,
      a + i * Hacl_Impl_QTesla_Params_params_n,
      z_ntt);
    int32_t *tc_k = tc + i * Hacl_Impl_QTesla_Params_params_n;
    int32_t *pk_t_k = pk_t + i * Hacl_Impl_QTesla_Params_params_n;
    Hacl_Impl_QTesla_sparse_mul32(tc_k, pk_t_k, pos_list, sign_list);
    Hacl_Impl_QTesla_Heuristic_Poly_poly_sub_reduce(w + i * Hacl_Impl_QTesla_Params_params_n,
      w + i * Hacl_Impl_QTesla_Params_params_n,
      tc_k);
  }
  Hacl_SHA3_shake128_hacl(smlen - Hacl_Impl_QTesla_Params_crypto_bytes,
    sm + Hacl_Impl_QTesla_Params_crypto_bytes,
    Hacl_Impl_QTesla_Params_crypto_hmbytes,
    hm);
  Hacl_Impl_QTesla_hash_H(c_sig, w, hm);
  uint8_t res = (uint8_t)255U;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < Hacl_Impl_QTesla_Params_crypto_c_bytes;
    i = i + (uint32_t)1U)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(c[i], c_sig[i]);
    res = uu____0 & res;
  }
  uint8_t z1 = res;
  bool r = z1 == (uint8_t)255U;
  if (!r)
  {
    return (int32_t)-3;
  }
  mlen[0U] = smlen - Hacl_Impl_QTesla_Params_crypto_bytes;
  for
  (uint32_t
    i = (uint32_t)0U;
    i
    < smlen - Hacl_Impl_QTesla_Params_crypto_bytes;
    i = i + (uint32_t)1U)
  {
    m[i] = sm[Hacl_Impl_QTesla_Params_crypto_bytes + i];
  }
  return (int32_t)0;
}

/* SNIPPET_END: Hacl_Impl_QTesla_qtesla_verify */

/* SNIPPET_START: Hacl_Impl_QTesla_crypto_sign_keypair */

int32_t Hacl_Impl_QTesla_crypto_sign_keypair(uint8_t *pk, uint8_t *sk)
{
  return Hacl_Impl_QTesla_qtesla_keygen(pk, sk);
}

/* SNIPPET_END: Hacl_Impl_QTesla_crypto_sign_keypair */

/* SNIPPET_START: Hacl_Impl_QTesla_crypto_sign */

int32_t
Hacl_Impl_QTesla_crypto_sign(
  uint8_t *sm,
  uint64_t *smlen,
  uint8_t *m,
  uint64_t mlen,
  uint8_t *sk
)
{
  uint32_t smlen_sizet = (uint32_t)0U;
  Hacl_Impl_QTesla_qtesla_sign(&smlen_sizet, (uint32_t)mlen, m, sm, sk);
  uint32_t smlen_sizet1 = smlen_sizet;
  smlen[0U] = (uint64_t)smlen_sizet1;
  return (int32_t)0;
}

/* SNIPPET_END: Hacl_Impl_QTesla_crypto_sign */

/* SNIPPET_START: Hacl_Impl_QTesla_crypto_sign_open */

int32_t
Hacl_Impl_QTesla_crypto_sign_open(
  uint8_t *m,
  uint64_t *mlen,
  uint8_t *sm,
  uint64_t smlen,
  uint8_t *pk
)
{
  uint32_t smlen1 = (uint32_t)smlen;
  uint32_t mlen_sizet = (uint32_t)0U;
  int32_t res = Hacl_Impl_QTesla_qtesla_verify(&mlen_sizet, smlen1, m, sm, pk);
  uint32_t mlen_sizet1 = mlen_sizet;
  mlen[0U] = (uint64_t)mlen_sizet1;
  return res;
}

/* SNIPPET_END: Hacl_Impl_QTesla_crypto_sign_open */

