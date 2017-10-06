#include "RSA.h"

uint8_t RSA_zero_8 = (uint8_t )0;

uint32_t RSA_hLen = (uint32_t )32;

uint32_t RSA_sLen = (uint32_t )20;

bool RSA_uu___is_Mk_rsa_pubkey(RSA_rsa_pubkey projectee)
{
  return true;
}

uint64_t *RSA___proj__Mk_rsa_pubkey__item__n(RSA_rsa_pubkey projectee)
{
  RSA_rsa_pubkey scrut = projectee;
  uint64_t *n1 = scrut.n;
  return n1;
}

uint64_t *RSA___proj__Mk_rsa_pubkey__item__e(RSA_rsa_pubkey projectee)
{
  RSA_rsa_pubkey scrut = projectee;
  uint64_t *e = scrut.e;
  return e;
}

uint64_t *RSA_get_n(RSA_rsa_pubkey x)
{
  RSA_rsa_pubkey scrut = x;
  uint64_t *n1 = scrut.n;
  return n1;
}

uint64_t *RSA_get_e(RSA_rsa_pubkey x)
{
  RSA_rsa_pubkey scrut = x;
  uint64_t *e = scrut.e;
  return e;
}

bool RSA_uu___is_Mk_rsa_privkey(RSA_rsa_privkey projectee)
{
  return true;
}

RSA_rsa_pubkey RSA___proj__Mk_rsa_privkey__item__pkey(RSA_rsa_privkey projectee)
{
  RSA_rsa_privkey scrut = projectee;
  RSA_rsa_pubkey pkey = scrut.pkey;
  return pkey;
}

uint64_t *RSA___proj__Mk_rsa_privkey__item__d(RSA_rsa_privkey projectee)
{
  RSA_rsa_privkey scrut = projectee;
  uint64_t *d = scrut.d;
  return d;
}

RSA_rsa_pubkey RSA_get_pkey(RSA_rsa_privkey x)
{
  RSA_rsa_privkey scrut = x;
  RSA_rsa_pubkey pkey = scrut.pkey;
  return pkey;
}

uint64_t *RSA_get_d(RSA_rsa_privkey x)
{
  RSA_rsa_privkey scrut = x;
  uint64_t *d = scrut.d;
  return d;
}

uint32_t RSA_get_octets(uint32_t modBits)
{
  return (modBits + (uint32_t )7) / (uint32_t )8;
}

uint32_t RSA_get_length_em(uint32_t modBits)
{
  if ((modBits - (uint32_t )1) % (uint32_t )8 == (uint32_t )0)
    return RSA_get_octets(modBits) - (uint32_t )1;
  else
    return RSA_get_octets(modBits);
}

void RSA_hash_sha256(uint8_t *mHash, uint8_t *m, uint32_t len)
{
  SHA2_256_hash(mHash, m, len);
}

void
RSA_mgf(
  uint32_t mgfseed_len,
  uint8_t *mgfseed,
  uint32_t len,
  uint32_t counter,
  uint8_t *acc,
  uint8_t *res
)
{
  KRML_CHECK_SIZE(RSA_zero_8, (uint32_t )4);
  uint8_t c[4];
  for (uintmax_t _i = 0; _i < (uint32_t )4; ++_i)
    c[_i] = RSA_zero_8;
  c[0] = (uint8_t )(counter >> (uint32_t )24);
  c[1] = (uint8_t )(counter >> (uint32_t )16);
  c[2] = (uint8_t )(counter >> (uint32_t )8);
  c[3] = (uint8_t )counter;
  KRML_CHECK_SIZE(RSA_zero_8, mgfseed_len + (uint32_t )4);
  uint8_t tmp[mgfseed_len + (uint32_t )4];
  for (uintmax_t _i = 0; _i < mgfseed_len + (uint32_t )4; ++_i)
    tmp[_i] = RSA_zero_8;
  memcpy(tmp, mgfseed, mgfseed_len * sizeof mgfseed[0]);
  memcpy(tmp + mgfseed_len, c, (uint32_t )4 * sizeof c[0]);
  KRML_CHECK_SIZE(RSA_zero_8, RSA_hLen);
  uint8_t hash_tmp[RSA_hLen];
  for (uintmax_t _i = 0; _i < RSA_hLen; ++_i)
    hash_tmp[_i] = RSA_zero_8;
  RSA_hash_sha256(hash_tmp, tmp, mgfseed_len + (uint32_t )4);
  uint32_t counter1 = counter + (uint32_t )1;
  uint32_t acc_size = counter1 * RSA_hLen;
  KRML_CHECK_SIZE(RSA_zero_8, acc_size);
  uint8_t acc_tmp[acc_size];
  for (uintmax_t _i = 0; _i < acc_size; ++_i)
    acc_tmp[_i] = RSA_zero_8;
  memcpy(acc_tmp, acc, (acc_size - RSA_hLen) * sizeof acc[0]);
  memcpy(acc_tmp + acc_size - RSA_hLen, hash_tmp, RSA_hLen * sizeof hash_tmp[0]);
  if (acc_size < len)
    RSA_mgf(mgfseed_len, mgfseed, len, counter1, acc_tmp, res);
  else
    memcpy(res, acc_tmp, len * sizeof acc_tmp[0]);
}

void RSA_xordb(uint8_t *b1, uint8_t *b2, uint32_t len)
{
  if (len > (uint32_t )0)
  {
    uint32_t len1 = len - (uint32_t )1;
    uint8_t uu____337 = b1[len1];
    uint8_t uu____338 = b2[len1];
    uint8_t uu____336 = uu____337 ^ uu____338;
    b1[len1] = uu____336;
    RSA_xordb(b1, b2, len1);
  }
}

void RSA_pss_encode(uint32_t modBits, uint8_t *msg, uint32_t len, uint8_t *salt, uint8_t *em)
{
  KRML_CHECK_SIZE(RSA_zero_8, RSA_hLen);
  uint8_t mHash[RSA_hLen];
  for (uintmax_t _i = 0; _i < RSA_hLen; ++_i)
    mHash[_i] = RSA_zero_8;
  RSA_hash_sha256(mHash, msg, len);
  uint32_t emBits = modBits - (uint32_t )1;
  uint32_t emLen = RSA_get_length_em(modBits);
  uint32_t m1_size = (uint32_t )8 + RSA_hLen + RSA_sLen;
  KRML_CHECK_SIZE(RSA_zero_8, m1_size);
  uint8_t m1[m1_size];
  for (uintmax_t _i = 0; _i < m1_size; ++_i)
    m1[_i] = RSA_zero_8;
  memcpy(m1 + (uint32_t )8, mHash, RSA_hLen * sizeof mHash[0]);
  memcpy(m1 + (uint32_t )8 + RSA_hLen, salt, RSA_sLen * sizeof salt[0]);
  KRML_CHECK_SIZE(RSA_zero_8, RSA_hLen);
  uint8_t m1Hash[RSA_hLen];
  for (uintmax_t _i = 0; _i < RSA_hLen; ++_i)
    m1Hash[_i] = RSA_zero_8;
  RSA_hash_sha256(m1Hash, m1, m1_size);
  uint32_t db_size = emLen - RSA_hLen - (uint32_t )1;
  KRML_CHECK_SIZE(RSA_zero_8, db_size);
  uint8_t db[db_size];
  for (uintmax_t _i = 0; _i < db_size; ++_i)
    db[_i] = RSA_zero_8;
  uint32_t ind_1 = emLen - RSA_sLen - RSA_hLen - (uint32_t )2;
  db[ind_1] = (uint8_t )1;
  memcpy(db + ind_1 + (uint32_t )1, salt, RSA_sLen * sizeof salt[0]);
  KRML_CHECK_SIZE(RSA_zero_8, db_size);
  uint8_t dbMask[db_size];
  for (uintmax_t _i = 0; _i < db_size; ++_i)
    dbMask[_i] = RSA_zero_8;
  KRML_CHECK_SIZE(RSA_zero_8, (uint32_t )0);
  uint8_t acc[0];
  RSA_mgf(RSA_hLen, m1Hash, db_size, (uint32_t )0, acc, dbMask);
  RSA_xordb(db, dbMask, db_size);
  uint32_t zeroL = (uint32_t )8 * emLen - emBits;
  uint8_t uu____488 = db[0];
  uint8_t uu____487 = uu____488 & (uint8_t )0xff >> zeroL;
  db[0] = uu____487;
  memcpy(em, db, db_size * sizeof db[0]);
  memcpy(em + db_size, m1Hash, RSA_hLen * sizeof m1Hash[0]);
  em[emLen - (uint32_t )1] = (uint8_t )0xbc;
}

bool RSA_pss_verify(uint32_t modBits, uint8_t *em, uint8_t *msg, uint32_t len)
{
  uint32_t emLen = RSA_get_length_em(modBits);
  uint32_t m1_size = (uint32_t )8 + RSA_hLen + RSA_sLen;
  uint32_t pad_size = emLen - RSA_sLen - RSA_hLen - (uint32_t )1;
  uint32_t db_size = emLen - RSA_hLen - (uint32_t )1;
  KRML_CHECK_SIZE(RSA_zero_8, RSA_hLen);
  uint8_t mHash[RSA_hLen];
  for (uintmax_t _i = 0; _i < RSA_hLen; ++_i)
    mHash[_i] = RSA_zero_8;
  KRML_CHECK_SIZE(RSA_zero_8, RSA_hLen);
  uint8_t m1Hash_[RSA_hLen];
  for (uintmax_t _i = 0; _i < RSA_hLen; ++_i)
    m1Hash_[_i] = RSA_zero_8;
  KRML_CHECK_SIZE(RSA_zero_8, m1_size);
  uint8_t m1[m1_size];
  for (uintmax_t _i = 0; _i < m1_size; ++_i)
    m1[_i] = RSA_zero_8;
  KRML_CHECK_SIZE(RSA_zero_8, pad_size);
  uint8_t pad2[pad_size];
  for (uintmax_t _i = 0; _i < pad_size; ++_i)
    pad2[_i] = RSA_zero_8;
  KRML_CHECK_SIZE(RSA_zero_8, db_size);
  uint8_t dbMask[db_size];
  for (uintmax_t _i = 0; _i < db_size; ++_i)
    dbMask[_i] = RSA_zero_8;
  RSA_hash_sha256(mHash, msg, len);
  uint8_t uu____625 = em[emLen - (uint32_t )1];
  bool uu____624 = uu____625 == (uint8_t )0xbc;
  bool uu____623 = !uu____624;
  uint8_t acc[0];
  bool res;
  if (uu____623)
    res = false;
  else
  {
    uint8_t *maskedDB = em;
    uint8_t *m1Hash = em + db_size;
    uint32_t zeroL = (uint32_t )8 * emLen - (modBits - (uint32_t )1);
    uint8_t uu____639 = maskedDB[0];
    uint8_t tmp = uu____639 & (uint8_t )0xff << (uint32_t )8 - zeroL;
    bool ite0;
    if (!(tmp == (uint8_t )0x00))
      ite0 = false;
    else
    {
      KRML_CHECK_SIZE(RSA_zero_8, (uint32_t )0);
      for (uintmax_t _i = 0; _i < (uint32_t )0; ++_i)
        acc[_i] = RSA_zero_8;
      RSA_mgf(RSA_hLen, m1Hash, db_size, (uint32_t )0, acc, dbMask);
      RSA_xordb(maskedDB, dbMask, db_size);
      uint8_t uu____661 = maskedDB[0];
      uint8_t uu____660 = uu____661 & (uint8_t )0xff >> zeroL;
      maskedDB[0] = uu____660;
      pad2[pad_size - (uint32_t )1] = (uint8_t )0x01;
      uint8_t *pad1 = maskedDB;
      bool uu____677 = FStar_Buffer_eqb(pad1, pad2, pad_size);
      bool uu____676 = !uu____677;
      bool ite;
      if (uu____676)
        ite = false;
      else
      {
        uint8_t *salt = maskedDB + pad_size;
        memcpy(m1 + (uint32_t )8, mHash, RSA_hLen * sizeof mHash[0]);
        memcpy(m1 + (uint32_t )8 + RSA_hLen, salt, RSA_sLen * sizeof salt[0]);
        RSA_hash_sha256(m1Hash_, m1, m1_size);
        ite = FStar_Buffer_eqb(m1Hash, m1Hash_, RSA_hLen);
      }
      ite0 = ite;
    }
    res = ite0;
  }
  return res;
}

void
RSA_rsa_sign(
  uint32_t modBits,
  uint32_t skeyBits,
  uint32_t msgLen,
  uint8_t *msg,
  RSA_rsa_privkey skey,
  uint8_t *salt,
  uint8_t *sgnt
)
{
  uint32_t k1 = RSA_get_octets(modBits);
  uint64_t *d = RSA_get_d(skey);
  RSA_rsa_pubkey uu____797 = RSA_get_pkey(skey);
  uint64_t *n1 = RSA_get_n(uu____797);
  uint32_t emLen = RSA_get_length_em(modBits);
  KRML_CHECK_SIZE(RSA_zero_8, emLen);
  uint8_t em[emLen];
  for (uintmax_t _i = 0; _i < emLen; ++_i)
    em[_i] = RSA_zero_8;
  RSA_pss_encode(modBits, msg, msgLen, salt, em);
  uint32_t mLen = Convert_get_size_nat(emLen);
  KRML_CHECK_SIZE((uint64_t )0, mLen);
  uint64_t m[mLen];
  memset(m, 0, mLen * sizeof m[0]);
  Convert_text_to_nat(em, emLen, m);
  uint32_t sLen1 = Convert_get_size_nat(k1);
  KRML_CHECK_SIZE((uint64_t )0, sLen1);
  uint64_t s[sLen1];
  memset(s, 0, sLen1 * sizeof s[0]);
  Exponentiation_mod_exp(modBits, mLen, skeyBits, sLen1, n1, m, d, s);
  Convert_nat_to_text(s, k1, sgnt);
}

bool
RSA_rsa_verify(
  uint32_t modBits,
  uint32_t msgLen,
  uint32_t pkeyBits,
  uint8_t *sgnt,
  RSA_rsa_pubkey pkey,
  uint8_t *msg
)
{
  uint64_t *e = RSA_get_e(pkey);
  uint64_t *n1 = RSA_get_n(pkey);
  uint32_t k1 = RSA_get_octets(modBits);
  uint32_t sLen1 = Convert_get_size_nat(k1);
  KRML_CHECK_SIZE((uint64_t )0, sLen1);
  uint64_t s[sLen1];
  memset(s, 0, sLen1 * sizeof s[0]);
  Convert_text_to_nat(sgnt, k1, s);
  uint32_t emLen = RSA_get_length_em(modBits);
  uint32_t mLen = Convert_get_size_nat(emLen);
  KRML_CHECK_SIZE((uint64_t )0, mLen);
  uint64_t m[mLen];
  memset(m, 0, mLen * sizeof m[0]);
  Exponentiation_mod_exp(modBits, sLen1, pkeyBits, mLen, n1, s, e, m);
  KRML_CHECK_SIZE(RSA_zero_8, emLen);
  uint8_t em[emLen];
  for (uintmax_t _i = 0; _i < emLen; ++_i)
    em[_i] = RSA_zero_8;
  Convert_nat_to_text(m, emLen, em);
  bool res = RSA_pss_verify(modBits, em, msg, msgLen);
  return res;
}

