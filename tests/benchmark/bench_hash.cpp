#include <vector>
#include <stdexcept>
#include <sstream>

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
    static constexpr auto header = "alg, size [b], cpu time incl [s], cpu time excl [s], avg cyc/hash, min cyc/hash, max cyc/hash, avg cyc/byte\n";
    static constexpr auto format = "%s, %zu, %f, %f, %.2f, %lu, %lu, %.2f\n";

  public:
    uint8_t *src;
    size_t src_sz;

    HashBenchmark(size_t src_sz) : src(0), src_sz(src_sz)
    {
      if (src_sz == 0)
        throw std::logic_error("Need src_sz > 0");
      src = new uint8_t[src_sz];
      b_randomize((char*)src, src_sz);
    }

    ~HashBenchmark()
    {
      delete(src);
      src_sz = 0;
    }

    static void print_header() { printf(header); }

    virtual void b_func() = 0;

    virtual void run(size_t samples)
    {
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

      printf(format,
        name.c_str(),
        src_sz,
        toverall/(double)CLOCKS_PER_SEC,
        ttotal/(double)CLOCKS_PER_SEC,
        ctotal/(double)samples,
        cmin, cmax,
        (ctotal/(double)src_sz)/(double)samples);
    }
};

template<int type, int N>
class EverCryptHash : public HashBenchmark
{
  uint8_t *dst;
  const static int id;

  public:
    EverCryptHash(size_t src_sz) : HashBenchmark(src_sz) {
      dst = new uint8_t[N/8];
      std::stringstream s;
      s << "EverCrypt " << EverCrypt_Hash_string_of_alg(id);
      name = s.str();
    }
    virtual ~EverCryptHash() {}
    virtual void b_func() { EverCrypt_Hash_hash(id, dst, src, src_sz); }
};

template<> const int EverCryptHash<0, 128>::id = Spec_Hash_Definitions_MD5;
template<> const int EverCryptHash<1, 160>::id = Spec_Hash_Definitions_SHA1;
template<> const int EverCryptHash<2, 224>::id = Spec_Hash_Definitions_SHA2_224;
template<> const int EverCryptHash<2, 256>::id = Spec_Hash_Definitions_SHA2_256;
template<> const int EverCryptHash<2, 384>::id = Spec_Hash_Definitions_SHA2_384;
template<> const int EverCryptHash<2, 512>::id = Spec_Hash_Definitions_SHA2_512;

#ifdef HAVE_OPENSSL
template<int type, int N>
class OpenSSLHash : public HashBenchmark
{
  uint8_t *dst;
  static unsigned char* (*fun)(const unsigned char *d, size_t n, unsigned char *md);

  public:
    OpenSSLHash(size_t src_sz) : HashBenchmark(src_sz) {
      dst = new uint8_t[N/8];
      std::stringstream s;
      s << "OpenSSL ";
      s << (type==0 ? "MD5" : type==1 ? "SHA1" : "SHA2_");
      if (type==2) s << N;
      name = s.str();}
    virtual ~OpenSSLHash() {}
    virtual void b_func() { fun((unsigned char*)src, src_sz, (unsigned char*)dst); }
};

template<> unsigned char* (*OpenSSLHash<0, 128>::fun)(const unsigned char *d, size_t n, unsigned char *md) = MD5;
template<> unsigned char* (*OpenSSLHash<1, 160>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA1;
template<> unsigned char* (*OpenSSLHash<2, 224>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA224;
template<> unsigned char* (*OpenSSLHash<2, 256>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA256;
template<> unsigned char* (*OpenSSLHash<2, 384>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA384;
template<> unsigned char* (*OpenSSLHash<2, 512>::fun)(const unsigned char *d, size_t n, unsigned char *md) = SHA512;
#endif

int bench_hash(size_t samples)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192 };

  HashBenchmark::print_header();

  for (size_t ds: data_sizes)
  {
    printf("-- Source size: %zu\n", ds);
    std::vector<HashBenchmark*> todo = {
      new EverCryptHash<0, 128>(ds),
      new EverCryptHash<1, 160>(ds),
      new EverCryptHash<2, 224>(ds),
      new EverCryptHash<2, 256>(ds),
      new EverCryptHash<2, 384>(ds),
      new EverCryptHash<2, 512>(ds),
      #ifdef HAVE_OPENSSL
      new OpenSSLHash<0, 128>(ds),
      new OpenSSLHash<1, 160>(ds),
      new OpenSSLHash<2, 224>(ds),
      new OpenSSLHash<2, 256>(ds),
      new OpenSSLHash<2, 384>(ds),
      new OpenSSLHash<2, 512>(ds),
      #endif
      };

    for (Benchmark* b: todo)
      b->run(samples);
  }
}