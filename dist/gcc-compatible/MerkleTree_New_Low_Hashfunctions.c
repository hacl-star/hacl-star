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


#include "MerkleTree_New_Low_Hashfunctions.h"

uint8_t
*LowStar_Regional_rg_alloc___uint8_t__uint32_t(
  LowStar_Regional_regional__uint32_t__uint8_t_ rg
)
{
  return rg.r_alloc(rg.state);
}

uint8_t *MerkleTree_New_Low_Hashfunctions_init_hash(uint32_t hsz)
{
  return
    LowStar_Regional_rg_alloc___uint8_t__uint32_t((
        (LowStar_Regional_regional__uint32_t__uint8_t_){
          .state = hsz,
          .dummy = MerkleTree_New_Low_Datastructures_hash_dummy,
          .r_alloc = MerkleTree_New_Low_Datastructures_hash_r_alloc,
          .r_free = MerkleTree_New_Low_Datastructures_hash_r_free
        }
      ));
}

void MerkleTree_New_Low_Hashfunctions_free_hash(uint32_t hsz, uint8_t *h1)
{
  LowStar_Regional_rg_free___uint8_t__uint32_t((
      (LowStar_Regional_regional__uint32_t__uint8_t_){
        .state = hsz,
        .dummy = MerkleTree_New_Low_Datastructures_hash_dummy,
        .r_alloc = MerkleTree_New_Low_Datastructures_hash_r_alloc,
        .r_free = MerkleTree_New_Low_Datastructures_hash_r_free
      }
    ),
    h1);
}

void
MerkleTree_New_Low_Hashfunctions_sha256_compress(uint8_t *src1, uint8_t *src2, uint8_t *dst)
{
  uint32_t hash_size = (uint32_t)32U;
  Spec_Hash_Definitions_hash_alg hash_alg = Spec_Hash_Definitions_SHA2_256;
  uint8_t cb[64U] = { 0U };
  memcpy(cb, src1, hash_size * sizeof (src1[0U]));
  memcpy(cb + (uint32_t)32U, src2, hash_size * sizeof (src2[0U]));
  uint32_t buf0[4U];
  uint32_t buf1[5U];
  uint32_t buf2[8U];
  uint32_t buf3[8U];
  uint64_t buf4[8U];
  uint64_t buf[8U];
  EverCrypt_Hash_state_s s;
  switch (hash_alg)
  {
    case Spec_Hash_Definitions_MD5:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i++)
        {
          buf0[i] = init;
        }
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_MD5_s, { .case_MD5_s = buf0 } });
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)5U; i++)
        {
          buf1[i] = init;
        }
        s = ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA1_s, { .case_SHA1_s = buf1 } });
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf2[i] = init;
        }
        s =
          (
            (EverCrypt_Hash_state_s){
              .tag = EverCrypt_Hash_SHA2_224_s,
              { .case_SHA2_224_s = buf2 }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        uint32_t init = (uint32_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf3[i] = init;
        }
        s =
          (
            (EverCrypt_Hash_state_s){
              .tag = EverCrypt_Hash_SHA2_256_s,
              { .case_SHA2_256_s = buf3 }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        uint64_t init = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf4[i] = init;
        }
        s =
          (
            (EverCrypt_Hash_state_s){
              .tag = EverCrypt_Hash_SHA2_384_s,
              { .case_SHA2_384_s = buf4 }
            }
          );
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        uint64_t init = (uint64_t)0U;
        for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
        {
          buf[i] = init;
        }
        s =
          ((EverCrypt_Hash_state_s){ .tag = EverCrypt_Hash_SHA2_512_s, { .case_SHA2_512_s = buf } });
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  EverCrypt_Hash_state_s st = s;
  EverCrypt_Hash_init(&st);
  EverCrypt_Hash_update(&st, cb);
  EverCrypt_Hash_finish(&st, dst);
}

