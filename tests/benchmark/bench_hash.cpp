#include <vector>
#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <EverCrypt_Hash.h>
}

#ifdef HAVE_OPENSSL
#include <openssl/sha.h>
#include <openssl/md5.h>
#endif

class HashBenchmark : public Benchmark
{
  private:
    static constexpr auto header = "Algorithm, Size [b], CPU Time (incl) [sec], CPU Time (excl) [sec], Avg Cycles/Hash, Min Cycles/Hash, Max Cycles/Hash, Avg Cycles/Byte";

  protected:
    uint8_t *src, *dst;
    size_t src_sz;

  public:
    HashBenchmark(std::ostream & rs, size_t src_sz, int type, int N, std::string const & prefix) : Benchmark(rs), src(0), src_sz(src_sz)
    {
      if (src_sz == 0)
        throw std::logic_error("Need src_sz > 0");
      src = new uint8_t[src_sz];
      b_randomize((char*)src, src_sz);

      dst = new uint8_t[N/8];

      std::stringstream s;
      s << prefix << " ";
      s << (type==0 ? "MD5" : (type==1 ? "SHA1" : (type == 2 ? "SHA2\\_" : "Unknown")));
      if (type==2) s << N;
      name = s.str();
    }

    virtual ~HashBenchmark()
    {
      delete(src);
      src_sz = 0;
    }

    static void print_header(std::ostream & rs) { rs << header << "\n"; }

    virtual void b_func() = 0;

    virtual void run(unsigned int seed, size_t samples)
    {
      srand(seed);

      cycles cbegin, cend, cdiff, ctotal = 0, cmax = 0, cmin = -1;
      size_t tbegin, tend, tdiff, ttotal = 0;
      size_t toverall = clock();

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

      rs << "\"" << name.c_str() << "\""
        << "," << src_sz
        << "," << toverall/(double)CLOCKS_PER_SEC
        << "," << ttotal/(double)CLOCKS_PER_SEC
        << "," << ctotal/(double)samples
        << "," << cmin << cmax
        << "," << (ctotal/(double)src_sz)/(double)samples
        << "\n";
    }
};

template<int type, int N>
class HaclHash : public HashBenchmark
{
  static void (*fun)(uint8_t *input, uint32_t input_len, uint8_t *dst);
  public:
    HaclHash(std::ostream & rs, size_t src_sz) : HashBenchmark(rs, src_sz, type, N, "HaCl") {}
    virtual ~HaclHash() {}
    virtual void b_func() { fun(src, src_sz, dst); }
};

template<> void (*HaclHash<0, 128>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_MD5_hash;
template<> void (*HaclHash<1, 160>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA1_hash;
template<> void (*HaclHash<2, 224>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_224;
template<> void (*HaclHash<2, 256>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_256;
template<> void (*HaclHash<2, 384>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_384;
template<> void (*HaclHash<2, 512>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_512;
typedef HaclHash<0, 128> HaclMD5;
typedef HaclHash<1, 160> HaclSHA1;

template<int type, int N>
class EverCryptHash : public HashBenchmark
{
  const static int id;
  public:
    EverCryptHash(std::ostream & rs, size_t src_sz) : HashBenchmark(rs, src_sz, type, N, "EverCrypt") {}
    virtual ~EverCryptHash() {}
    virtual void b_func() { EverCrypt_Hash_hash(id, dst, src, src_sz); }
};

template<> const int EverCryptHash<0, 128>::id = Spec_Hash_Definitions_MD5;
template<> const int EverCryptHash<1, 160>::id = Spec_Hash_Definitions_SHA1;
template<> const int EverCryptHash<2, 224>::id = Spec_Hash_Definitions_SHA2_224;
template<> const int EverCryptHash<2, 256>::id = Spec_Hash_Definitions_SHA2_256;
template<> const int EverCryptHash<2, 384>::id = Spec_Hash_Definitions_SHA2_384;
template<> const int EverCryptHash<2, 512>::id = Spec_Hash_Definitions_SHA2_512;
typedef EverCryptHash<0, 128> EverCryptMD5;
typedef EverCryptHash<1, 160> EverCryptSHA1;

#ifdef HAVE_OPENSSL
template<int type, int N>
class OpenSSLHash : public HashBenchmark
{
  static unsigned char* (*fun)(const unsigned char *d, size_t n, unsigned char *md);

  public:
    OpenSSLHash(std::ostream & rs, size_t src_sz) : HashBenchmark(rs, src_sz, type, N, "OpenSSL") {}
    virtual ~OpenSSLHash() {}
    virtual void b_func() { fun((unsigned char*)src, src_sz, (unsigned char*)dst); }
};

template<> unsigned char* (*OpenSSLHash<0, 128>::fun)(const unsigned char *d, size_t n, unsigned char *md) = MD5;
template<> unsigned char* (*OpenSSLHash<1, 160>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA1;
template<> unsigned char* (*OpenSSLHash<2, 224>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA224;
template<> unsigned char* (*OpenSSLHash<2, 256>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA256;
template<> unsigned char* (*OpenSSLHash<2, 384>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA384;
template<> unsigned char* (*OpenSSLHash<2, 512>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA512;
typedef OpenSSLHash<0, 128> OpenSSLMD5;
typedef OpenSSLHash<1, 160> OpenSSLSHA1;
#endif

int bench_hash(unsigned int seed, size_t num_samples)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192 };



  for (size_t ds: data_sizes)
  {
    std::stringstream filename;
    filename << "bench_hash_" << ds << ".csv";
    std::cout << "-- " << filename.str() << "...\n";
    std::ofstream rs(filename.str(), std::ios::out | std::ios::trunc);

    Benchmark::print_config(rs);
    HashBenchmark::print_header(rs);

    std::vector<HashBenchmark*> todo = {
      new HaclMD5(rs, ds),
      new HaclSHA1(rs, ds),
      new HaclHash<2, 224>(rs, ds),
      new HaclHash<2, 256>(rs, ds),
      new HaclHash<2, 384>(rs, ds),
      new HaclHash<2, 512>(rs, ds),

      new EverCryptMD5(rs, ds),
      new EverCryptSHA1(rs, ds),
      new EverCryptHash<2, 224>(rs, ds),
      new EverCryptHash<2, 256>(rs, ds),
      new EverCryptHash<2, 384>(rs, ds),
      new EverCryptHash<2, 512>(rs, ds),

      #ifdef HAVE_OPENSSL
      new OpenSSLMD5(rs, ds),
      new OpenSSLSHA1(rs, ds),
      new OpenSSLHash<2, 224>(rs, ds),
      new OpenSSLHash<2, 256>(rs, ds),
      new OpenSSLHash<2, 384>(rs, ds),
      new OpenSSLHash<2, 512>(rs, ds),
      #endif
      };

    for (Benchmark* b: todo)
      b->run(seed, num_samples);
  }
}