#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <EverCrypt_AEAD.h>
#ifdef HAVE_VALE
#include <EverCrypt_Vale.h>
#endif
#include <EverCrypt_Chacha20Poly1305.h>
}

#ifdef HAVE_OPENSSL
#include <openssl/evp.h>
#endif

#ifdef HAVE_BCRYPT
#include <windows.h>
#include <bcrypt.h>

#ifndef NT_SUCCESS
#define NT_SUCCESS(Status) (((NTSTATUS)(Status)) >= 0)
#endif
#endif

#ifdef HAVE_JC
#include <jc.h>
#endif

class AEADBenchmark : public Benchmark
{
  protected:
    size_t key_sz, msg_len, ad_len = 128;
    uint8_t *tag;
    uint8_t iv[16]; // 12 used; old vale likes to have 16 anyways.
    uint8_t *key;
    uint8_t *plain;
    uint8_t *cipher;
    uint8_t *ad = 0;
    std::string algorithm;

  public:
    static std::string column_headers() { return "\"Provider\", \"Algorithm\", \"Size [b]\"" + Benchmark::column_headers() + ", \"Avg Cycles/Byte\""; }

    AEADBenchmark(size_t key_sz_bits, size_t tag_len, size_t msg_len) : Benchmark()
    {
      if (key_sz_bits != 128 && key_sz_bits != 192 && key_sz_bits != 256)
        throw std::logic_error("Need key_sz in {128, 192, 256}");

      if (msg_len == 0)
        throw std::logic_error("Need msg_len > 0");

      this->key_sz = key_sz_bits/8;
      this->msg_len = msg_len;

      key = new uint8_t[key_sz];
      plain = new uint8_t[msg_len];
      cipher = new uint8_t[msg_len];
      tag = new uint8_t[tag_len];
      ad = new uint8_t[ad_len];

      randomize(ad, ad_len);
    }

    void set_name(const std::string & provider, const std::string & algorithm)
    {
      Benchmark::set_name(provider);
      this->algorithm = algorithm;
    }

    virtual ~AEADBenchmark()
    {
      delete[](ad);
      delete[](tag);
      delete[](cipher);
      delete[](plain);
      delete[](key);
    }

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      randomize((char*)key, key_sz);
      randomize((char*)plain, msg_len);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << "\"" << name << "\""
        << "," << "\"" << algorithm << "\""
        << "," << msg_len;
      Benchmark::report(rs, s);
      rs << "," << (ctotal/(double)msg_len)/(double)s.samples << "\n";
    }
};

class NilBenchmark : public AEADBenchmark {
public:
  NilBenchmark(const std::string &provider, const std::string &algorithm) :
    AEADBenchmark(128, 0, 32)
  {
    set_name(provider, algorithm);
  }
  ~NilBenchmark () {}
  virtual void bench_func() {}
  virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << "\"" << name << "\""
        << "," << "\"" << algorithm << "\""
        << "," << msg_len;
      rs << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0
        << "," << 0.0;
      rs << "," << 0.0 << "\n";
    }
};

void type2name_evercrypt(AEADBenchmark & b, int type)
{
  switch (type) {
      case Spec_Agile_AEAD_AES128_GCM: b.set_name("EverCrypt", "AES128\\nGCM"); break;
      case Spec_Agile_AEAD_AES256_GCM: b.set_name("EverCrypt", "AES256\\nGCM"); break;
      case Spec_Agile_AEAD_CHACHA20_POLY1305: b.set_name("EverCrypt", "Chacha20\\nPoly1305"); break;
      case Spec_Agile_AEAD_AES128_CCM: b.set_name("EverCrypt", "AES128\\nCCM"); break;
      case Spec_Agile_AEAD_AES256_CCM: b.set_name("EverCrypt", "AES256\\nCCM"); break;
      case Spec_Agile_AEAD_AES128_CCM8: b.set_name("EverCrypt", "AES128\\nCCM8"); break;
      case Spec_Agile_AEAD_AES256_CCM8: b.set_name("EverCrypt", "AES256\\nCCM8"); break;
      default: throw std::logic_error("Unknown AEAD algorithm");
    }
}

template<uint8_t type, size_t key_size_bits, size_t tag_len>
class EverCryptAEADEncrypt : public AEADBenchmark
{
  protected:
    EverCrypt_AEAD_state_s *state;

  public:
    EverCryptAEADEncrypt(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      { type2name_evercrypt(*this, type); }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      if (EverCrypt_AEAD_create_in(type, &state, (uint8_t*)key) != EverCrypt_Error_Success)
        throw std::logic_error("AEAD context creation failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (
      #endif
        EverCrypt_AEAD_encrypt(state, (uint8_t*)iv, 12, (uint8_t*)ad, ad_len, (uint8_t*)plain, msg_len, (uint8_t*)cipher, (uint8_t*)tag)
      #ifdef _DEBUG
        != EverCrypt_Error_Success) throw std::logic_error("AEAD encryption failed")
      #endif
      ;
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      EverCrypt_AEAD_free(state);
      AEADBenchmark::bench_cleanup(s);
    }
    virtual ~EverCryptAEADEncrypt() { }
};

template<uint8_t type, size_t key_size_bits, size_t tag_len>
class EverCryptAEADDecrypt : public AEADBenchmark
{
  protected:
    EverCrypt_AEAD_state_s *state;

  public:
    EverCryptAEADDecrypt(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      { type2name_evercrypt(*this, type); }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      if (EverCrypt_AEAD_create_in(type, &state, (uint8_t*)key) != EverCrypt_Error_Success)
        throw std::logic_error("AEAD context creation failed");

      EverCrypt_AEAD_encrypt(state, (uint8_t*)iv, 12, (uint8_t*)ad, ad_len, (uint8_t*)plain, msg_len, (uint8_t*)cipher, (uint8_t*)tag);
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (
      #endif
        EverCrypt_AEAD_decrypt(state, (uint8_t*)iv, 12, (uint8_t*)ad, ad_len, (uint8_t*)cipher, msg_len, (uint8_t*)tag, (uint8_t*)plain)
      #ifdef _DEBUG
        != EverCrypt_Error_Success) throw std::logic_error("AEAD decryption failed")
      #endif
      ;
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      EverCrypt_AEAD_free(state);
      AEADBenchmark::bench_cleanup(s);
    }
    virtual ~EverCryptAEADDecrypt() { }
};

#ifdef HAVE_VALE
template<size_t key_size_bits, size_t tag_len>
class OldValeEncrypt : public AEADBenchmark
{
  protected:
    gcm_args args;

  public:
    OldValeEncrypt(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      {
        switch(key_size_bits) {
          case 128: set_name("Vale (old)", "AES128\\nGCM"); break;
          case 256: set_name("Vale (old)", "AES256\\nGCM"); break;
          default: throw std::logic_error("Unknown algorithm");
        }
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      args.plain = (uint8_t*)plain;
      args.plain_len = msg_len;
      args.aad = (uint8_t*)ad;
      args.aad_len = ad_len;
      args.iv = (uint8_t*)iv;
      args.cipher = (uint8_t*)cipher;
      args.tag = (uint8_t*)tag;

      args.expanded_key = new uint8_t[15 * (128/8)];
      switch(key_size_bits) {
        case 128: old_aes128_key_expansion((uint8_t*)key, args.expanded_key); break;
        case 256: old_aes256_key_expansion((uint8_t*)key, args.expanded_key); break;
      }
    }
    virtual void bench_func()
    {
      switch(key_size_bits) {
      case 128: old_gcm128_encrypt(&args);
      case 256: old_gcm256_encrypt(&args);
      }
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      delete[](args.expanded_key);
      AEADBenchmark::bench_cleanup(s);
    }
    virtual ~OldValeEncrypt() {}
};

template<size_t key_size_bits, size_t tag_len>
class OldValeDecrypt : public AEADBenchmark
{
  protected:
    gcm_args args;

  public:
    OldValeDecrypt(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      {
        switch(key_size_bits) {
          case 128: set_name("Vale (old)", "AES128\\nGCM"); break;
          case 256: set_name("Vale (old)", "AES256\\nGCM"); break;
          default: throw std::logic_error("Unknown algorithm");
        }
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      args.plain = (uint8_t*)plain;
      args.plain_len = msg_len;
      args.aad = (uint8_t*)ad;
      args.aad_len = ad_len;
      args.iv = (uint8_t*)iv;
      args.cipher = (uint8_t*)cipher;
      args.tag = (uint8_t*)tag;
      args.expanded_key = new uint8_t[15 * (128/8)];
      switch(key_size_bits) {
        case 128: old_aes128_key_expansion((uint8_t*)key, args.expanded_key); old_gcm128_encrypt(&args); break;
        case 256: old_aes256_key_expansion((uint8_t*)key, args.expanded_key); old_gcm256_encrypt(&args); break;
      }
      std::swap(args.cipher, args.plain);
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      switch(key_size_bits) {
      case 128: if (old_gcm128_decrypt(&args) != 0) throw std::logic_error("Vale decryption failed"); break;
      case 256: if (old_gcm256_decrypt(&args) != 0) throw std::logic_error("Vale decryption failed"); break;
      }
      #else
      switch(key_size_bits) {
      case 128: old_gcm128_decrypt(&args); break;
      case 256: old_gcm256_decrypt(&args); break;
      }
      #endif
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      delete[](args.expanded_key);
      AEADBenchmark::bench_cleanup(s);
    }
    virtual ~OldValeDecrypt() {}
};
#endif

#ifdef HAVE_OPENSSL
// See https://github.com/openssl/openssl/blob/master/demos/evp/aesgcm.c

static void openssl_type2name(AEADBenchmark & b, int type, size_t key_size_bits, size_t tag_len)
{
  switch (type) {
    case 0:
      switch(key_size_bits) {
        case 128: b.set_name("OpenSSL", "AES128\\nGCM"); break;
        case 256: b.set_name("OpenSSL", "AES256\\nGCM"); break;
        default: throw std::logic_error("Unknown algorithm");
      }
      break;
    case 1: b.set_name("OpenSSL", "Chacha20\\nPoly1305"); break;
    default: throw std::logic_error("Unknown algorithm");
  }
}

template<int type, size_t key_size_bits, size_t tag_len>
class OpenSSLEncrypt : public AEADBenchmark
{
  protected:
    static const EVP_CIPHER *evp_cipher;
    EVP_CIPHER_CTX *ctx;
    int outlen;

  public:
    OpenSSLEncrypt(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      {
        openssl_type2name(*this, type, key_size_bits, tag_len);
        ctx = EVP_CIPHER_CTX_new();
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      EVP_EncryptInit_ex(ctx, evp_cipher, NULL, NULL, NULL);
      if ((EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_IVLEN, 12, NULL) <= 0) ||
          (EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv)  <= 0))
          throw std::logic_error("OpenSSL encryption initialization failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if ((ad_len > 0 && EVP_EncryptUpdate(ctx, NULL, &outlen, ad, ad_len) <= 0) ||
          (EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len) <= 0) ||
          (EVP_EncryptFinal_ex(ctx, cipher, &outlen) <= 0))
          throw std::logic_error("OpenSSL encryption failed");
      #else
      if (ad_len > 0) EVP_EncryptUpdate(ctx, NULL, &outlen, ad, ad_len);
      EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len);
      EVP_EncryptFinal_ex(ctx, cipher, &outlen);
      #endif
    }
    virtual ~OpenSSLEncrypt() { EVP_CIPHER_CTX_free(ctx); }
};

template<> const EVP_CIPHER *OpenSSLEncrypt<0, 128, 16>::evp_cipher = EVP_aes_128_gcm();
template<> const EVP_CIPHER *OpenSSLEncrypt<0, 256, 16>::evp_cipher = EVP_aes_256_gcm();
template<> const EVP_CIPHER *OpenSSLEncrypt<1, 256, 16>::evp_cipher = EVP_chacha20_poly1305();

template<size_t type, size_t key_size_bits, size_t tag_len>
class OpenSSLDecrypt : public AEADBenchmark
{
  protected:
    static const EVP_CIPHER *evp_cipher;
    EVP_CIPHER_CTX *ctx;
    int outlen;

  public:
    OpenSSLDecrypt(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      {
        openssl_type2name(*this, type, key_size_bits, tag_len);
        ctx = EVP_CIPHER_CTX_new();
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      EVP_DecryptInit_ex(ctx, evp_cipher, NULL, NULL, NULL);
      if ((EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_IVLEN, 12, NULL) <= 0) ||
          (EVP_EncryptInit_ex(ctx, NULL, NULL, key, iv) <= 0) ||
          (ad_len > 0 && EVP_EncryptUpdate(ctx, NULL, &outlen, ad, ad_len) <= 0) ||
          (EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len) <= 0) ||
          (EVP_EncryptFinal_ex(ctx, cipher, &outlen) <= 0) ||
          (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, 16, tag) <= 0) ||
          (EVP_DecryptInit_ex(ctx, NULL, NULL, key, iv) <= 0))
          throw std::logic_error("OpenSSL decryption initialization failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (((ad_len > 0) && EVP_DecryptUpdate(ctx, NULL, &outlen, ad, ad_len) <= 0) ||
          EVP_DecryptUpdate(ctx, plain, &outlen, cipher, msg_len)  <= 0 ||
          EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, tag_len, (void *)tag)  <= 0 ||
          EVP_DecryptFinal_ex(ctx, plain, &outlen) <= 0)
          throw std::logic_error("OpenSSL tag validation failed")
      #else
      if (ad_len > 0) EVP_DecryptUpdate(ctx, NULL, &outlen, ad, ad_len);
      EVP_DecryptUpdate(ctx, plain, &outlen, cipher, msg_len);
      EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, tag_len, (void *)tag);
      EVP_DecryptFinal_ex(ctx, plain, &outlen);
      #endif
      ;
    }
    virtual ~OpenSSLDecrypt() { EVP_CIPHER_CTX_free(ctx); }
};

template<> const EVP_CIPHER *OpenSSLDecrypt<0, 128, 16>::evp_cipher = EVP_aes_128_gcm();
template<> const EVP_CIPHER *OpenSSLDecrypt<0, 256, 16>::evp_cipher = EVP_aes_256_gcm();
template<> const EVP_CIPHER *OpenSSLDecrypt<1, 256, 16>::evp_cipher = EVP_chacha20_poly1305();
#endif

#ifdef HAVE_BCRYPT
static void bcrypt_type2name(AEADBenchmark & b, size_t key_size_bits, size_t tag_len)
{
  switch(key_size_bits) {
    case 128: b.set_name("BCrypt", "AES128\\nGCM"); break;
    case 256: b.set_name("BCrypt", "AES256\\nGCM"); break;
    default: throw std::logic_error("Unknown algorithm");
  }
}

#ifndef BCRYPT_AES_GCM_ALG_HANDLE
#define BCRYPT_AES_GCM_ALG_HANDLE ((BCRYPT_ALG_HANDLE) 0x000001e1)
#endif

template<size_t key_size_bits, size_t tag_len>
class BCryptEncryptBM : public AEADBenchmark
{
  protected:
    BCRYPT_ALG_HANDLE hAlg = NULL;
    BCRYPT_KEY_HANDLE hKey = NULL;
    BCRYPT_AUTHENTICATED_CIPHER_MODE_INFO Info;
    ULONG outlen;

  public:
    BCryptEncryptBM(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      {
        bcrypt_type2name(*this, key_size_bits, tag_len);
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      if(!NT_SUCCESS(BCryptGenerateSymmetricKey(BCRYPT_AES_GCM_ALG_HANDLE, &hKey, NULL, 0, key, key_size_bits/8, 0)))
        throw std::logic_error("BCrypt key setup failed");

      BCRYPT_INIT_AUTH_MODE_INFO(Info);
      Info.pbAuthData = (PUCHAR) ad;
      Info.cbAuthData = ad_len;
      Info.pbTag = tag;
      Info.cbTag = 16;
      Info.pbNonce = iv;
      Info.cbNonce = 12;
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (!NT_SUCCESS(
      #endif
        BCryptEncrypt(hKey, plain, msg_len, &Info, iv, 12, cipher, msg_len, &outlen, 0)
      #ifdef _DEBUG
        )) throw std::logic_error("BCrypt encryption failed")
      #endif
      ;
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
      { BCryptDestroyKey(hKey); }
    virtual ~BCryptEncryptBM() { }
};

template<size_t key_size_bits, size_t tag_len>
class BCryptDecryptBM : public AEADBenchmark
{
  protected:
    BCRYPT_ALG_HANDLE hAlg = NULL;
    BCRYPT_KEY_HANDLE hKey = NULL;
    BCRYPT_AUTHENTICATED_CIPHER_MODE_INFO Info;
    ULONG outlen;

  public:
    BCryptDecryptBM(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
      {
        bcrypt_type2name(*this, key_size_bits, tag_len);
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
      if(!NT_SUCCESS(BCryptGenerateSymmetricKey(BCRYPT_AES_GCM_ALG_HANDLE, &hKey, NULL, 0, key, key_size_bits/8, 0)))
        throw std::logic_error("BCrypt key setup failed");

      BCRYPT_INIT_AUTH_MODE_INFO(Info);
      Info.pbAuthData = (PUCHAR) ad;
      Info.cbAuthData = ad_len;
      Info.pbTag = tag;
      Info.cbTag = 16;
      Info.pbNonce = iv;
      Info.cbNonce = 12;

      if (!NT_SUCCESS(BCryptEncrypt(hKey, plain, msg_len, &Info, iv, 12, cipher, msg_len, &outlen, 0)))
        throw std::logic_error("BCrypt encryption failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (!NT_SUCCESS(
      #endif
        BCryptDecrypt(hKey, cipher, msg_len, &Info, iv, 12, plain, msg_len, &outlen, 0)
      #ifdef _DEBUG
        )) throw std::logic_error("BCrypt decryption failed")
      #endif
        ;
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
      { BCryptDestroyKey(hKey); }
    virtual ~BCryptDecryptBM() {}
};

#endif

#include <iomanip>
void showbuf(const uint8_t *buf, size_t len)
{
  for (size_t i = 0; i < len; i++)
    std::cout << std::hex << std::setfill('0') << std::setw(2) << (unsigned)buf[i];
  std::cout << std::endl;
}

#ifdef WIN32
#undef HAVE_JC
#endif

static uint32_t
Hacl_Impl_Chacha20_chacha20_constants[4U] =
  { (uint32_t)0x61707865U, (uint32_t)0x3320646eU, (uint32_t)0x79622d32U, (uint32_t)0x6b206574U };

#ifdef HAVE_JC
template<size_t key_size_bits, size_t tag_len>
class JCChacha20Poly1305EncryptBM : public AEADBenchmark
{
  protected:
  public:
    JCChacha20Poly1305EncryptBM(size_t msg_len) :
      AEADBenchmark(key_size_bits, tag_len, msg_len)
    {
        set_name("libjc", "Chacha20\\nPoly1305");
    }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_setup(s);
    }
    virtual void bench_func()
    {
      auto check_eq = [this](const uint8_t *x, const uint8_t *y, uint32_t sz) {
        for (size_t i = 0; i < sz; i++)
          if (x[i] != y[i]) {
            print_buffer(x, sz);
            print_buffer(y, sz);
            throw std::logic_error("mismatch");
          }
      };

      static uint8_t iv_zero[12] = { 0 };

      // See https://tools.ietf.org/html/rfc8439#section-2.8.1

      // pad16(x):
      //    if (len(x) % 16)==0
      //       then return NULL
      //       else return copies(0, 16-(len(x)%16))
      //    end

      // poly1305_key_gen(key,nonce):
      //    counter = 0
      //    block = chacha20_block(key,counter,nonce)
      //    return block[0..31]
      //    end

      // chacha20_aead_encrypt(aad, key, iv, constant, plaintext):
      //    nonce = constant | iv
      std::vector<uint8_t> nonce;
      for (size_t i = 0; i < 32; i++)
        nonce.push_back(((uint8_t*)Hacl_Impl_Chacha20_chacha20_constants)[i]);
      for (size_t i = 0; i < 12; i++)
        nonce.push_back(iv[i]);
      //    otk = poly1305_key_gen(key, nonce)
      uint32_t ec_ctx[4] = { 0 };
      uint8_t block[64];
      libjc_avx2_chacha20_avx2((uint64_t*)block, (uint64_t*)nonce.data(), 64, (uint64_t*)key, (uint64_t*)iv_zero, 0);

      #if 0
      uint8_t ec_block[64];
      Hacl_Impl_Chacha20_chacha20_encrypt(64, ec_block, nonce.data(), key, iv_zero, 0);
      check_eq(block, ec_block, 64);
      // uint8_t ec_dk_block[64];
      // Hacl_Impl_Chacha20Poly1305_Poly_derive_key(key, iv, ec_dk_block);
      // check_eq(block, ec_dk_block, 64);
      #endif
      uint8_t *otk = block; // 64 but we use only 32

      //    ciphertext = chacha20_encrypt(key, 1, nonce, plaintext)
      uint8_t ciphertext[msg_len];
      libjc_avx2_chacha20_avx2((uint64_t*)ciphertext, (uint64_t*)plain, msg_len, (uint64_t*)key, (uint64_t*)nonce.data(), 1);
      #if 0
      uint8_t ec_ciphertext[msg_len];
      Hacl_Impl_Chacha20_chacha20_encrypt(msg_len, ec_ciphertext, plain, key, nonce.data(), 1);
      check_eq(ciphertext, ec_ciphertext, msg_len);
      #endif

      std::vector<uint8_t> mac_data;
      //    mac_data = aad | pad16(aad)
      //    mac_data |= ciphertext | pad16(ciphertext)
      //    mac_data |= num_to_8_le_bytes(aad.length)
      //    mac_data |= num_to_8_le_bytes(ciphertext.length)
      for (size_t i = 0; i < ad_len; i++)
        mac_data.push_back(ad[i]);
      for (size_t pad = ad_len; pad % 16 != 0; pad++)
        mac_data.push_back(0);
      for (size_t i = 0; i < msg_len; i++)
        mac_data.push_back(ciphertext[i]);
      for (size_t pad = msg_len; pad % 16 != 0; pad++)
        mac_data.push_back(0);
      uint64_t ad_len64 = ad_len;
      uint8_t *ad_len8 = (uint8_t*)&ad_len64;
      for (size_t i = 0; i < 8; i++)
        mac_data.push_back(ad_len8[i]);
      uint64_t msg_len64 = msg_len;
      uint8_t *msg_len8 = (uint8_t*)&msg_len64;
      for (size_t i = 0; i < 8; i++)
        mac_data.push_back(msg_len8[i]);

      //    tag = poly1305_mac(mac_data, otk)
      uint8_t tag[tag_len];
      libjc_avx2_poly1305_avx2((uint64_t*)tag, (uint64_t*)mac_data.data(), mac_data.size(), (uint64_t*)otk);
      #ifdef _DEBUG
      uint8_t ec_tag[tag_len];
      Hacl_Poly1305_128_poly1305_mac(ec_tag, mac_data.size(), mac_data.data(), otk);
      check_eq(tag, ec_tag, tag_len);
      #endif

      #if 0 // def _DEBUG
      EverCrypt_AEAD_state_s *state;
      EverCrypt_Error_error_code ec;
      ec = EverCrypt_AEAD_create_in(Spec_Agile_AEAD_CHACHA20_POLY1305, &state, (uint8_t*)key);
      if (ec != EverCrypt_Error_Success)
        throw std::logic_error("AEAD context creation failed");
      ec = EverCrypt_AEAD_encrypt(state,
                                  (uint8_t*)iv, 12,
                                  (uint8_t*)ad, ad_len,
                                  (uint8_t*)plain, msg_len,
                                  (uint8_t*)ec_ciphertext,
                                  (uint8_t*)ec_tag);
      if (ec != EverCrypt_Error_Success)
        throw std::logic_error("AEAD encryption failed");
      EverCrypt_AEAD_free(state);
      check_eq(ciphertext, ec_ciphertext, msg_len);
      check_eq(tag, ec_tag, tag_len);
      #endif
      //    return (ciphertext, tag)
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      AEADBenchmark::bench_cleanup(s);
    }
    virtual ~JCChacha20Poly1305EncryptBM() {}
};
#endif

static std::string filter(const std::string & data_filename, const std::string & keyword)
{
  return "< grep -e \"^\\\"" + keyword + "\" -e \"^\\\"Provider\" " + data_filename;
}

void bench_aead_encrypt(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 64, 128, 256, 512, 1024, 1056, 2048, 4096, 8192, 16384, 32768, 65536 };

  Benchmark::PlotSpec plot_specs_cycles;
  Benchmark::PlotSpec plot_specs_bytes;

  for (size_t ds: data_sizes)
  {
    std::stringstream dsstr;
    dsstr << ds;

    std::stringstream data_filename;
    data_filename << "bench_aead_encrypt_" << ds << ".csv";

    if (plot_specs_cycles.empty())
    {
      plot_specs_cycles.push_back(std::make_pair(data_filename.str(), "using 'Avg':xticlabels(strcol('Provider').\"\\n\".strcol('Algorithm')) title '" + dsstr.str() + " b'"));
      plot_specs_bytes.push_back(std::make_pair(data_filename.str(), "using 'Avg Cycles/Byte':xticlabels(strcol('Provider').\"\\n\".strcol('Algorithm')) title '" + dsstr.str() + " b'"));
    }
    else
    {
      plot_specs_cycles.push_back(std::make_pair(data_filename.str(), "using 'Avg' title '" + dsstr.str() + " b'"));
      plot_specs_bytes.push_back(std::make_pair(data_filename.str(), "using 'Avg Cycles/Byte' title '" + dsstr.str() + " b'"));
    }

    std::list<Benchmark*> todo = {
      new EverCryptAEADEncrypt<Spec_Agile_AEAD_AES128_GCM, 128, 16>(ds),
      new EverCryptAEADEncrypt<Spec_Agile_AEAD_AES256_GCM, 256, 16>(ds),
      new EverCryptAEADEncrypt<Spec_Agile_AEAD_CHACHA20_POLY1305, 256, 16>(ds),
      // new EverCryptAEADEncrypt<Spec_Agile_AEAD_AES128_CCM, 128, 16>(ds), // unsupported?
      // new EverCryptAEADEncrypt<Spec_Agile_AEAD_AES256_CCM, 256, 16>(ds), // unsupported?
      // new EverCryptAEADEncrypt<Spec_Agile_AEAD_AES128_CCM8, 128, 8>(ds), // unsupported?
      // new EverCryptAEADEncrypt<Spec_Agile_AEAD_AES256_CCM8, 256, 8>(ds), // unsupported?

      // #ifdef HAVE_VALE
      // new OldValeEncrypt<128, 16>(ds),
      // new OldValeEncrypt<256, 16>(ds),
      // #endif

      #ifdef HAVE_OPENSSL
      new OpenSSLEncrypt<0, 128, 16>(ds),
      new OpenSSLEncrypt<0, 256, 16>(ds),
      new OpenSSLEncrypt<1, 256, 16>(ds),
      #endif

      #ifdef HAVE_BCRYPT
      new BCryptEncryptBM<128, 16>(ds),
      new BCryptEncryptBM<256, 16>(ds),
      new NilBenchmark("BCrypt", "Chacha20\\nPoly1305"),
      #endif

      #ifdef HAVE_JC
      new NilBenchmark("libjc", "AES128\\nGCM"),
      new NilBenchmark("libjc", "AES256\\nGCM"),
      new JCChacha20Poly1305EncryptBM<256, 16>(ds),
      #endif
      };

      Benchmark::run_batch(s, AEADBenchmark::column_headers(), data_filename.str(), todo);

      Benchmark::PlotSpec plot_specs_ds_cycles;
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "EverCrypt"), "EverCrypt", "Avg", "strcol('Algorithm')", 0, false);
      #ifdef HAVE_OPENSSL
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "OpenSSL"), "OpenSSL", "Avg", "strcol('Algorithm')", 0, false);
      #endif
      #ifdef HAVE_BCRYPT
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "BCrypt"), "BCrypt", "Avg", "strcol('Algorithm')", 0, false);
      #endif
      #ifdef HAVE_JC
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "libjc"), "libjc", "Avg", "strcol('Algorithm')", 0, false);
      #endif
      Benchmark::add_label_offsets(plot_specs_ds_cycles);

      std::stringstream extras;
      extras << "set key top left inside\n";
      extras << "set style histogram clustered gap 3 title\n";
      extras << "set style data histograms\n";
      extras << "set bmargin 5\n";
      extras << "set xrange [-0.5:2.5]\n";

      Benchmark::make_plot(s,
                      "svg",
                      "AEAD Encryption performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/encryption]",
                      plot_specs_ds_cycles,
                      "bench_aead_all_encrypt_" + dsstr.str() + "_cycles.svg",
                      extras.str());

      Benchmark::PlotSpec plot_specs_ds_bytes;
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "EverCrypt"), "EverCrypt", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #ifdef HAVE_OPENSSL
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "OpenSSL"), "OpenSSL", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #endif
      #ifdef HAVE_BCRYPT
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "BCrypt"), "BCrypt", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #endif
      #ifdef HAVE_JC
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "libjc"), "libjc", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #endif
      Benchmark::add_label_offsets(plot_specs_ds_bytes);

      Benchmark::make_plot(s,
                      "svg",
                      "AEAD Encryption performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/byte]",
                      plot_specs_ds_bytes,
                      "bench_aead_all_encrypt_" + dsstr.str() + "_bytes.svg",
                      extras.str());

      Benchmark::PlotSpec plot_specs_ds_candlesticks;
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "EverCrypt"), "EverCrypt", "strcol('Algorithm')"),
      #ifdef HAVE_OPENSSL
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "OpenSSL"), "OpenSSL", "strcol('Algorithm')"),
      #endif
      #ifdef HAVE_BCRYPT
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "BCrypt"), "BCrypt", "strcol('Algorithm')"),
      #endif
      #ifdef HAVE_JC
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "libjc"), "libjc", "strcol('Algorithm')"),
      #endif

      extras << "set boxwidth .25\n";
      extras << "set style fill empty\n";

      Benchmark::make_plot(s,
                      "svg",
                      "AEAD Encryption performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/encryption]",
                      plot_specs_ds_candlesticks,
                      "bench_aead_all_encrypt_" + dsstr.str() + "_candlesticks.svg",
                      extras.str());
  }

  std::stringstream extras;
  extras << "set key top left inside\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                       "svg",
                       "AEAD Encryption Performance",
                       "",
                       "Avg. performance [CPU cycles/encryption]",
                       plot_specs_cycles,
                       "bench_aead_all_encrypt_cycles.svg",
                       extras.str());

  Benchmark::make_plot(s,
                       "svg",
                       "AEAD Encryption Performance",
                       "",
                       "Avg. performance [CPU cycles/byte]",
                       plot_specs_bytes,
                       "bench_aead_all_encrypt_bytes.svg",
                       extras.str());
}

void bench_aead_decrypt(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 64, 128, 256, 512, 1024, 1056, 2048, 4096, 8192, 16384, 32768, 65536 };

  Benchmark::PlotSpec plot_specs_cycles;
  Benchmark::PlotSpec plot_specs_bytes;

  for (size_t ds: data_sizes)
  {
    std::stringstream dsstr;
    dsstr << ds;

    std::stringstream data_filename;
    data_filename << "bench_aead_decrypt_" << ds << ".csv";

    if (plot_specs_cycles.empty())
    {
      plot_specs_cycles.push_back(std::make_pair(data_filename.str(), "using 'Avg':xticlabels(strcol('Provider').\"\\n\".strcol('Algorithm')) title '" + dsstr.str() + " b'"));
      plot_specs_bytes.push_back(std::make_pair(data_filename.str(), "using 'Avg Cycles/Byte':xticlabels(strcol('Provider').\"\\n\".strcol('Algorithm')) title '" + dsstr.str() + " b'"));
    }
    else
    {
      plot_specs_cycles.push_back(std::make_pair(data_filename.str(), "using 'Avg' title '" + dsstr.str() + " b'"));
      plot_specs_bytes.push_back(std::make_pair(data_filename.str(), "using 'Avg Cycles/Byte' title '" + dsstr.str() + " b'"));
    }

    std::list<Benchmark*> todo = {
      new EverCryptAEADDecrypt<Spec_Agile_AEAD_AES128_GCM, 128, 16>(ds),
      new EverCryptAEADDecrypt<Spec_Agile_AEAD_AES256_GCM, 256, 16>(ds),
      new EverCryptAEADDecrypt<Spec_Agile_AEAD_CHACHA20_POLY1305, 256, 16>(ds),
      // new EverCryptAEADDecrypt<Spec_Agile_AEAD_AES128_CCM, 128, 16>(ds), // unsupported?
      // new EverCryptAEADDecrypt<Spec_Agile_AEAD_AES256_CCM, 256, 16>(ds), // unsupported?
      // new EverCryptAEADDecrypt<Spec_Agile_AEAD_AES128_CCM8, 128, 8>(ds), // unsupported?
      // new EverCryptAEADDecrypt<Spec_Agile_AEAD_AES256_CCM8, 256, 8>(ds), // unsupported?

      // #ifdef HAVE_VALE
      // new OldValeDecrypt<128, 16>(ds),
      // new OldValeDecrypt<256, 16>(ds),
      // #endif

      #ifdef HAVE_OPENSSL
      new OpenSSLDecrypt<0, 128, 16>(ds),
      new OpenSSLDecrypt<0, 256, 16>(ds),
      new OpenSSLDecrypt<1, 256, 16>(ds),
      #endif

      #ifdef HAVE_BCRYPT
      new BCryptDecryptBM<128, 16>(ds),
      new BCryptDecryptBM<256, 16>(ds),
      #endif
      };

      Benchmark::run_batch(s, AEADBenchmark::column_headers(), data_filename.str(), todo);

      Benchmark::PlotSpec plot_specs_ds_cycles;
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "EverCrypt"), "EverCrypt", "Avg", "strcol('Algorithm')", 0, false);
      #ifdef HAVE_OPENSSL
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "OpenSSL"), "OpenSSL", "Avg", "strcol('Algorithm')", 0, false);
      #endif
      #ifdef HAVE_BCRYPT
      plot_specs_ds_cycles += Benchmark::histogram_line(filter(data_filename.str(), "BCrypt"), "BCrypt", "Avg", "strcol('Algorithm')", 0, false);
      #endif
      Benchmark::add_label_offsets(plot_specs_ds_cycles);

      std::stringstream extras;
      extras << "set key top left inside\n";
      extras << "set style histogram clustered gap 3 title\n";
      extras << "set style data histograms\n";
      extras << "set bmargin 5\n";
      extras << "set xrange [-0.5:2.5]\n";

      Benchmark::make_plot(s,
                      "svg",
                      "AEAD Decryption performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/decryption]",
                      plot_specs_ds_cycles,
                      "bench_aead_all_decrypt_" + dsstr.str() + "_cycles.svg",
                      extras.str());

      Benchmark::PlotSpec plot_specs_ds_bytes;
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "EverCrypt"), "EverCrypt", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #ifdef HAVE_OPENSSL
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "OpenSSL"), "OpenSSL", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #endif
      #ifdef HAVE_BCRYPT
      plot_specs_ds_bytes += Benchmark::histogram_line(filter(data_filename.str(), "BCrypt"), "BCrypt", "Avg Cycles/Byte", "strcol('Algorithm')", 2, false);
      #endif
      Benchmark::add_label_offsets(plot_specs_ds_bytes);

      Benchmark::make_plot(s,
                      "svg",
                      "AEAD Decryption performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/byte]",
                      plot_specs_ds_bytes,
                      "bench_aead_all_decrypt_" + dsstr.str() + "_bytes.svg",
                      extras.str());

      Benchmark::PlotSpec plot_specs_ds_candlesticks;
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "EverCrypt"), "EverCrypt", "strcol('Algorithm')"),
      #ifdef HAVE_OPENSSL
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "OpenSSL"), "OpenSSL", "strcol('Algorithm')"),
      #endif
      #ifdef HAVE_BCRYPT
      plot_specs_ds_candlesticks += Benchmark::candlestick_line(filter(data_filename.str(), "BCrypt"), "BCrypt", "strcol('Algorithm')"),
      #endif

      extras << "set boxwidth .25\n";
      extras << "set style fill empty\n";

      Benchmark::make_plot(s,
                      "svg",
                      "AEAD Decryption performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/decryption]",
                      plot_specs_ds_candlesticks,
                      "bench_aead_all_decrypt_" + dsstr.str() + "_candlesticks.svg",
                      extras.str());
  }

  std::stringstream extras;
  extras << "set key top left inside\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                       "svg",
                       "AEAD Decryption Performance",
                       "",
                       "Avg. performance [CPU cycles/decryption]",
                       plot_specs_cycles,
                       "bench_aead_all_decrypt_cycles.svg",
                       extras.str());

  Benchmark::make_plot(s,
                       "svg",
                       "AEAD Decryption Performance",
                       "",
                       "Avg. performance [CPU cycles/byte]",
                       plot_specs_bytes,
                       "bench_aead_all_decrypt_bytes.svg",
                       extras.str());
}

void bench_aead(const BenchmarkSettings & s)
{
  bench_aead_encrypt(s);
  // bench_aead_decrypt(s);
}
