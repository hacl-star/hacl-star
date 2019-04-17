#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>
#include <set>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <EverCrypt_AEAD.h>
}

class AEADBenchmark : public Benchmark
{
  protected:
    cycles cbegin, cend, cdiff, ctotal = 0, cmax = 0, cmin = -1;
    size_t tbegin, tend, tdiff, ttotal = 0;
    size_t toverall;

    size_t key_sz, input_sz;
    unsigned char tag[16], iv[12];
    unsigned char *key;
    unsigned char *plain;
    unsigned char *cipher;

  public:
    static constexpr auto header = "Algorithm, Size [b], CPU Time (incl) [sec], CPU Time (excl) [sec], Avg Cycles/Hash, Min Cycles/Hash, Max Cycles/Hash, Avg Cycles/Byte";

    AEADBenchmark(std::ostream & rs, size_t key_sz_bits, size_t input_sz, std::string const & prefix) : Benchmark()
    {
      if (key_sz_bits != 128 && key_sz_bits != 192 && key_sz_bits != 256)
        throw std::logic_error("Need key_sz in {128, 192, 256}");

      if (input_sz == 0)
        throw std::logic_error("Need input_sz > 0");

      this->key_sz = key_sz_bits/8;
      this->input_sz = input_sz;

      key = new unsigned char[key_sz];
      plain = new unsigned char[input_sz];
      cipher = new unsigned char[input_sz];

      b_randomize((char*)key, key_sz);
      b_randomize((char*)plain, input_sz);

      std::stringstream s;
      s << prefix << " ";
      // s << (type==0 ? "MD5" : (type==1 ? "SHA1" : (type == 2 ? "SHA2\\_" : "Unknown")));
      name = s.str();
    }

    virtual ~AEADBenchmark()
    {
      delete(key);
      delete(plain);
      delete(cipher);
    }

    virtual void b_func() = 0;

    virtual void run()
    {
      srand(seed);
      toverall = clock();

      for (int i = 0; i < samples; i++)
      {
        tbegin = clock();
        cbegin = b_cpucycles_begin();
        b_func();
        cend = b_cpucycles_end();
        tend = clock();
        cdiff = cend-cbegin;
        tdiff = difftime(tend, tbegin);
        ctotal += cdiff;
        ttotal += tdiff;
        if (cdiff < cmin) cmin = cdiff;
        if (cdiff > cmax) cmax = cdiff;
      }

      toverall = clock() - toverall;
    }

    virtual void report(std::ostream & rs)
    {
      rs << "\"" << name.c_str() << key_sz << "\""
        << "," << input_sz
        << "," << toverall/(double)CLOCKS_PER_SEC
        << "," << ttotal/(double)CLOCKS_PER_SEC
        << "," << ctotal/(double)samples
        << "," << cmin << cmax
        << "," << (ctotal/(double)input_sz)/(double)samples
        << "\n";
    }
};

template<int type, int key_sz_bits>
class EverCryptAEAD : public AEADBenchmark
{
  public:
    EverCryptAEAD(std::ostream & rs, size_t input_sz) :
      AEADBenchmark(rs, type /*EverCrypt_aead_keyLen(type)*/, input_sz, "EverCyrypt") {}
    virtual ~EverCryptAEAD() {}
    virtual void b_func() {
      // EverCrypt_AEAD_state_s *s = EverCrypt_aead_create(type, key);
      // EverCrypt_aead_encrypt(s, iv, "", 0, plain, N, cipher, tag);
      // EverCrypt_aead_free(s);
    }
};

int bench_aead(unsigned int seed, size_t num_samples)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192 };

  for (size_t ds: data_sizes)
  {
    std::stringstream filename;
    filename << "bench_aead_" << ds << ".csv";

    std::set<Benchmark*> todo = {
      // EverCryptAEAD<EverCrypt_AES128_GCM, 128>(ds);
      // EverCryptAEAD<EverCrypt_AES256_GCM, 256>(ds);
      // EverCryptAEAD<EverCrypt_CHACHA20_POLY1305, 128>(ds);
      // EverCryptAEAD<EverCrypt_AES128_CCM, 128>(ds);
      // EverCryptAEAD<EverCrypt_AES256_CCM, 256>(ds);
      // EverCryptAEAD<EverCrypt_AES128_CCM8, 128>(ds);
      // EverCryptAEAD<EverCrypt_AES256_CCM8, 256>(ds);

      #ifdef HAVE_OPENSSL
      #endif
      };

    b_run(seed, num_samples, AEADBenchmark::header, filename.str(), todo);
  }
}