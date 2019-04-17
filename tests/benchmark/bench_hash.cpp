#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>
#include <set>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <EverCrypt_Hash.h>
#include <Hacl_Hash.h>
}

#ifdef HAVE_OPENSSL
#include <openssl/sha.h>
#include <openssl/md5.h>
#endif

class HashBenchmark : public Benchmark
{
  protected:
    cycles cbegin, cend, cdiff, ctotal = 0, cmax = 0, cmin = -1;
    size_t tbegin, tend, tdiff, ttotal = 0;
    size_t toverall;

    uint8_t *src, *dst;
    size_t src_sz;

  public:
    static constexpr auto header = "Algorithm, Size [b], CPU Time (incl) [sec], CPU Time (excl) [sec], Avg Cycles/Hash, Min Cycles/Hash, Max Cycles/Hash, Avg Cycles/Byte";

    HashBenchmark(size_t src_sz, int type, int N, std::string const & prefix) : Benchmark(), src(0), src_sz(src_sz)
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
      set_name(s.str());
    }

    virtual ~HashBenchmark()
    {
      delete(src);
      src_sz = 0;
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
      rs << "\"" << name.c_str() << "\""
        << "," << src_sz
        << "," << toverall/(double)CLOCKS_PER_SEC
        << "," << ttotal/(double)CLOCKS_PER_SEC
        << "," << ctotal/(double)samples
        << "," << cmin
        << "," << cmax
        << "," << (ctotal/(double)src_sz)/(double)samples
        << "\n";
    }
};

template<int type, int N>
class HaclHash : public HashBenchmark
{
  static void (*fun)(uint8_t *input, uint32_t input_len, uint8_t *dst);
  public:
    HaclHash(size_t src_sz) : HashBenchmark(src_sz, type, N, "HaCl") {}
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
    EverCryptHash(size_t src_sz) : HashBenchmark(src_sz, type, N, "EverCrypt") {}
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
    OpenSSLHash(size_t src_sz) : HashBenchmark(src_sz, type, N, "OpenSSL") {}
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
    std::set<Benchmark*> todo = {
      new HaclMD5(ds),
      new HaclSHA1(ds),
      new HaclHash<2, 224>(ds),
      new HaclHash<2, 256>(ds),
      new HaclHash<2, 384>(ds),
      new HaclHash<2, 512>(ds),

      new EverCryptMD5(ds),
      new EverCryptSHA1(ds),
      new EverCryptHash<2, 224>(ds),
      new EverCryptHash<2, 256>(ds),
      new EverCryptHash<2, 384>(ds),
      new EverCryptHash<2, 512>(ds),

      #ifdef HAVE_OPENSSL
      new OpenSSLMD5(ds),
      new OpenSSLSHA1(ds),
      new OpenSSLHash<2, 224>(ds),
      new OpenSSLHash<2, 256>(ds),
      new OpenSSLHash<2, 384>(ds),
      new OpenSSLHash<2, 512>(ds),
      #endif
    };

    std::stringstream num_benchmarks;
    num_benchmarks << todo.size();

    std::stringstream filename;
    filename << "bench_hash_" << ds << ".csv";

    b_run(seed, num_samples, HashBenchmark::header, filename.str(), todo);


    std::stringstream title;
    title << "Hash performance on " << ds << " bytes of data";

    std::stringstream plot_filename;
    plot_filename << "bench_hash_" << ds << ".svg";

    b_make_plot(seed, num_samples,
                "config",
                "svg",
                title.str(),
                "avg cycles/hash",
                filename.str(),
                plot_filename.str(),
                "",
                "   using 5:xticlabels(1) with boxes title columnheader, \
                 '' using ($0-1):5:xticlabels(1):(sprintf(\"%0.2f\", $5)) with labels font \"Courier,8\" rotate by 90 left");

    plot_filename.str("");
    plot_filename << "bench_hash_" << ds << "_candlesticks.svg";

    b_make_plot(seed, num_samples,
                "config",
                "svg",
                title.str(),
                "cycles/hash",
                filename.str(),
                plot_filename.str(),
                "set xrange[0:" + num_benchmarks.str() + "+1]",
                "using 0:5:6:7:5:xticlabels(1) with candlesticks whiskerbars .25");
  }
}