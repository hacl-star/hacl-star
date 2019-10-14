#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>

#include <benchmark.h>

extern "C" {
#include <EverCrypt_Hash.h>
#ifdef HAVE_HACL
#include <Hacl_Hash.h>
#include <Hacl_SHA3.h>
#endif
}

#ifdef HAVE_OPENSSL
#include <openssl/sha.h>
#include <openssl/md5.h>
#endif

#ifdef HAVE_BCRYPT
#include <windows.h>
#include <bcrypt.h>

#ifndef NT_SUCCESS
#define NT_SUCCESS(Status) (((NTSTATUS)(Status)) >= 0)
#endif
#endif

class HashBenchmark : public Benchmark
{
  protected:
    uint8_t *src, *dst;
    size_t src_sz;
    std::string alg_id;

  public:
    static std::string column_headers() { return "\"Provider\",\"Algorithm\",\"Size [b]\"" + Benchmark::column_headers() + ",\"Avg Cycles/Byte\""; }

    HashBenchmark(size_t src_sz, int type, int N, const std::string & prefix) : Benchmark(prefix), src(0), src_sz(src_sz)
    {
      if (src_sz == 0)
        throw std::logic_error("Need src_sz > 0");

      src = new uint8_t[src_sz];
      dst = new uint8_t[N/8];

      switch (type)
      {
        case 0: alg_id = "MD5"; break;
        case 1: alg_id = "SHA1"; break;
        case 2: {
          std::stringstream as;
          as << "SHA2-" << N;
          alg_id = as.str();
          break;
        }
        case 3: alg_id = "SHA3"; break;
        default: throw std::logic_error("unknown algorithm");
      }
    }

    virtual ~HashBenchmark()
    {
      delete[](src);
      delete[](dst);
      src_sz = 0;
    }

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Benchmark::bench_setup(s);
      randomize((char*)src, src_sz);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << "\"" << name << "\"" << "," << "\"" << alg_id << "\"" << "," << src_sz;
      Benchmark::report(rs, s);
      rs << "," << (ctotal/(double)src_sz)/(double)s.samples << "\n";
    }
};

template<int type, int N>
class HaclHash : public HashBenchmark
{
  static void (*fun)(uint8_t *input, uint32_t input_len, uint8_t *dst);
  public:
    HaclHash(size_t src_sz) : HashBenchmark(src_sz, type, N, "HaCl") {}
    virtual ~HaclHash() {}
    virtual void bench_func() { fun(src, src_sz, dst); }
};

template<> void (*HaclHash<0, 128>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_MD5_legacy_hash;
template<> void (*HaclHash<1, 160>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA1_legacy_hash;
template<> void (*HaclHash<2, 224>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_224;
template<> void (*HaclHash<2, 256>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_256;
template<> void (*HaclHash<2, 384>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_384;
template<> void (*HaclHash<2, 512>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = Hacl_Hash_SHA2_hash_512;
typedef HaclHash<0, 128> HaclMD5;
typedef HaclHash<1, 160> HaclSHA1;

template<> void (*HaclHash<3, 224>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = [](uint8_t *input, uint32_t input_len, uint8_t *dst) { Hacl_SHA3_sha3_224(input_len, input, dst); };
template<> void (*HaclHash<3, 256>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = [](uint8_t *input, uint32_t input_len, uint8_t *dst) { Hacl_SHA3_sha3_256(input_len, input, dst); };
template<> void (*HaclHash<3, 384>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = [](uint8_t *input, uint32_t input_len, uint8_t *dst) { Hacl_SHA3_sha3_384(input_len, input, dst); };
template<> void (*HaclHash<3, 512>::fun)(uint8_t *input, uint32_t input_len, uint8_t *dst) = [](uint8_t *input, uint32_t input_len, uint8_t *dst) { Hacl_SHA3_sha3_512(input_len, input, dst); };

template<int type, int N>
class EverCryptHash : public HashBenchmark
{
  const static int id;
  public:
    EverCryptHash(size_t src_sz) : HashBenchmark(src_sz, type, N, "EverCrypt") {}
    virtual ~EverCryptHash() {}
    virtual void bench_func() { EverCrypt_Hash_hash(id, dst, src, src_sz); }
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
    virtual void bench_func() { fun((unsigned char*)src, src_sz, (unsigned char*)dst); }
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

#ifdef HAVE_BCRYPT
template<int type, int N>
class BCryptHashBM : public HashBenchmark
{
  static unsigned char* (*fun)(const unsigned char *d, size_t n, unsigned char *md);
  BCRYPT_ALG_HANDLE hAlg = NULL;
  BCRYPT_HASH_HANDLE hHash = NULL;
  static LPCWSTR alg_id;
  DWORD cbHashObject = 0, cbHash = 0, cbData = 0;
  PBYTE pbHashObject = 0;

  public:
    BCryptHashBM(size_t src_sz) : HashBenchmark(src_sz, type, N, "BCrypt")
    {
      if (!NT_SUCCESS(BCryptOpenAlgorithmProvider(&hAlg, alg_id, NULL, BCRYPT_HASH_REUSABLE_FLAG)) ||
          !NT_SUCCESS(BCryptGetProperty(hAlg, BCRYPT_OBJECT_LENGTH, (PBYTE)&cbHashObject, sizeof(DWORD), &cbData, 0)) ||
          !NT_SUCCESS(BCryptGetProperty(hAlg, BCRYPT_HASH_LENGTH, (PBYTE)&cbHash, sizeof(DWORD),  &cbData, 0)))
        throw std::logic_error("BCrypt setup failed");
      pbHashObject = (PBYTE)HeapAlloc (GetProcessHeap (), 0, cbHashObject);
      if (cbHash != N/8 ||
          !NT_SUCCESS(BCryptCreateHash(hAlg, &hHash, pbHashObject, cbHashObject, NULL, 0, 0)))
        throw std::logic_error("BCrypt setup failed");
    }
    virtual void bench_func()
    {
      if (!NT_SUCCESS(BCryptHashData(hHash, src, src_sz, 0)) ||
          !NT_SUCCESS(BCryptFinishHash(hHash, dst, N/8, 0)))
        throw std::logic_error("BCrypt hash failed");
    }
    virtual ~BCryptHashBM()
    {
      BCryptDestroyHash(hHash);
      BCryptCloseAlgorithmProvider(hAlg, 0);
    }
};

template<> LPCWSTR BCryptHashBM<0, 128>::alg_id = BCRYPT_MD5_ALGORITHM;
template<> LPCWSTR BCryptHashBM<1, 160>::alg_id = BCRYPT_SHA1_ALGORITHM;
// No BCRYPT_SHA224_ALGORITHM
template<> LPCWSTR BCryptHashBM<2, 256>::alg_id = BCRYPT_SHA256_ALGORITHM;
template<> LPCWSTR BCryptHashBM<2, 384>::alg_id = BCRYPT_SHA384_ALGORITHM;
template<> LPCWSTR BCryptHashBM<2, 512>::alg_id = BCRYPT_SHA512_ALGORITHM;
typedef BCryptHashBM<0, 128> BCryptMD5;
typedef BCryptHashBM<1, 160> BCryptSHA1;
#endif

static std::string filter(const std::string & data_filename, const std::string & keyword)
{
  return "< grep -e \"\\\"" + keyword + "\" -e \"^\\\"Provider\" " + data_filename;
}

void bench_hash_plots(const BenchmarkSettings & s, const std::string & alg, const std::string & num_benchmarks, const std::string & data_filename)
{
  std::stringstream title;
  title << alg << " performance";

  Benchmark::Benchmark::PlotSpec plot_specs_cycles;
  plot_specs_cycles += Benchmark::histogram_line(filter(data_filename, "EverCrypt"), "EverCrypt", "Avg", "strcol('Size [b]')", 0, true);
  #ifdef HAVE_HACL
  plot_specs_cycles += Benchmark::histogram_line(filter(data_filename, "HaCl"), "HaCl", "Avg", "strcol('Size [b]')", 0, true);
  #endif
  #ifdef HAVE_OPENSSL
  plot_specs_cycles += Benchmark::histogram_line(filter(data_filename, "OpenSSL"), "OpenSSL", "Avg", "strcol('Size [b]')", 0, true);
  #endif
  #ifdef HAVE_BCRYPT
  plot_specs_cycles += Benchmark::histogram_line(filter(data_filename, "BCrypt"), "BCrypt", "Avg", "strcol('Size [b]')", 0, true);
  #endif
  Benchmark::add_label_offsets(plot_specs_cycles, 1.0);

  std::stringstream extras;
  extras << "set key top left inside\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                       "svg",
                       title.str(),
                       "Message length [bytes]",
                       "Avg. performance [CPU cycles/hash]",
                       plot_specs_cycles,
                       "bench_hash_" + alg + "_cyles.svg",
                       extras.str(),
                       {}, 0,
                       true);


  Benchmark::Benchmark::PlotSpec plot_specs_bytes;
  plot_specs_bytes += Benchmark::histogram_line(filter(data_filename, "EverCrypt"), "EverCrypt", "Avg Cycles/Byte", "strcol('Size [b]')", 2, true);
  #ifdef HAVE_HACL
  plot_specs_bytes += Benchmark::histogram_line(filter(data_filename, "HaCl"), "HaCl", "Avg Cycles/Byte", "strcol('Size [b]')", 2, true);
  #endif
  #ifdef HAVE_OPENSSL
  plot_specs_bytes += Benchmark::histogram_line(filter(data_filename, "OpenSSL"), "OpenSSL", "Avg Cycles/Byte", "strcol('Size [b]')", 2, true);
  #endif
  #ifdef HAVE_BCRYPT
  plot_specs_bytes += Benchmark::histogram_line(filter(data_filename, "BCrypt"), "BCrypt", "Avg Cycles/Byte", "strcol('Size [b]')", 2, true);
  #endif
  Benchmark::add_label_offsets(plot_specs_bytes, 1.0);

  extras << "set key top right inside\n";

  Benchmark::make_plot(s,
                       "svg",
                       title.str(),
                       "Message length [bytes]",
                       "Avg. performance [CPU cycles/byte]",
                       plot_specs_bytes,
                       "bench_hash_" + alg + "_bytes.svg",
                       extras.str(),
                       {}, 0,
                       true);


  Benchmark::Benchmark::PlotSpec plot_specs_cycles_candlesticks;
  plot_specs_cycles_candlesticks += Benchmark::candlestick_line(filter(data_filename, "EverCrypt"), "EverCrypt", "strcol('Size [b]')");
  #ifdef HAVE_HACL
  plot_specs_cycles_candlesticks += Benchmark::candlestick_line(filter(data_filename, "HaCl"), "HaCl", "strcol('Size [b]')");
  #endif
  #ifdef HAVE_OPENSSL
  plot_specs_cycles_candlesticks += Benchmark::candlestick_line(filter(data_filename, "OpenSSL"), "OpenSSL", "strcol('Size [b]')");
  #endif
  #ifdef HAVE_BCRYPT
  plot_specs_cycles_candlesticks += Benchmark::candlestick_line(filter(data_filename, "BCrypt"), "BCrypt", "strcol('Size [b]')");
  #endif

  extras << "set boxwidth 0.25\n";
  extras << "set style fill empty\n";
  extras << "set key top left inside\n";
  extras << "set xrange[-.5:6.5]";

  Benchmark::make_plot(s,
                       "svg",
                       title.str(),
                       "Message length [bytes]",
                       "Avg. performance [CPU cycles/hash]",
                       plot_specs_cycles_candlesticks,
                       "bench_hash_" + alg + "_candlesticks.svg",
                       extras.str(),
                       {}, 0,
                       true);
}

void bench_hash_alg(const BenchmarkSettings & s, const std::string & alg, std::list<Benchmark*> & todo)
{
  std::string data_filename = "bench_hash_" + alg + ".csv";
  std::string num_benchmarks = std::to_string(todo.size());

  Benchmark::run_batch(s, HashBenchmark::column_headers(), data_filename, todo);

  bench_hash_plots(s, alg, num_benchmarks, data_filename);
}

void mk_(size_t ds, const std::string & data_filename)
{

}

void bench_md5(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
     todo.push_back(new EverCryptMD5(ds));
     #ifdef HAVE_HACL
     todo.push_back(new HaclMD5(ds));
     #endif
     #ifdef HAVE_OPENSSL
     todo.push_back(new OpenSSLMD5(ds));
     #endif
     #ifdef HAVE_BCRYPT
     todo.push_back(new BCryptMD5(ds));
     #endif
  }

  bench_hash_alg(s, "MD5", todo);
}

void bench_sha1(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
     todo.push_back(new EverCryptSHA1(ds));
     #ifdef HAVE_HACL
     todo.push_back(new HaclSHA1(ds));
     #endif
     #ifdef HAVE_OPENSSL
     todo.push_back(new OpenSSLSHA1(ds));
     #endif
     #ifdef HAVE_BCRYPT
     todo.push_back(new BCryptSHA1(ds));
     #endif
  }

  bench_hash_alg(s, "SHA1", todo);
}

void bench_sha2_224(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    todo.push_back(new EverCryptHash<2, 224>(ds));
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<2, 224>(ds));
    #endif
    #ifdef HAVE_OPENSSL
    todo.push_back(new OpenSSLHash<2, 224>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA2_224", todo);
}

void bench_sha2_256(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    todo.push_back(new EverCryptHash<2, 256>(ds));
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<2, 256>(ds));
    #endif
    #ifdef HAVE_OPENSSL
    todo.push_back(new OpenSSLHash<2, 256>(ds));
    #endif
    #ifdef HAVE_BCRYPT
    todo.push_back(new BCryptHashBM<2, 256>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA2_256", todo);
}

void bench_sha2_384(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    todo.push_back(new EverCryptHash<2, 384>(ds));
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<2, 384>(ds));
    #endif
    #ifdef HAVE_OPENSSL
    todo.push_back(new OpenSSLHash<2, 384>(ds));
    #endif
    #ifdef HAVE_BCRYPT
    todo.push_back(new BCryptHashBM<2, 384>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA2_384", todo);
}

void bench_sha2_512(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    todo.push_back(new EverCryptHash<2, 512>(ds));
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<2, 512>(ds));
    #endif
    #ifdef HAVE_OPENSSL
    todo.push_back(new OpenSSLHash<2, 512>(ds));
    #endif
    #ifdef HAVE_BCRYPT
    todo.push_back(new BCryptHashBM<2, 512>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA2_512", todo);
}

void bench_sha2(const BenchmarkSettings & s)
{
  bench_sha2_224(s);
  bench_sha2_256(s);
  bench_sha2_384(s);
  bench_sha2_512(s);
}

void bench_sha3_224(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<3, 224>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA3_224", todo);
}

void bench_sha3_256(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<3, 256>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA3_256", todo);
}

void bench_sha3_384(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<3, 384>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA3_384", todo);
}

void bench_sha3_512(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  std::list<Benchmark*> todo;

  for (size_t ds: data_sizes)
  {
    #ifdef HAVE_HACL
    todo.push_back(new HaclHash<3, 512>(ds));
    #endif
  }

  bench_hash_alg(s, "SHA3-512", todo);
}

void bench_sha3(const BenchmarkSettings & s)
{
  bench_sha3_224(s);
  bench_sha3_256(s);
  bench_sha3_384(s);
  bench_sha3_512(s);
}

void bench_hash(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  bench_md5(s);
  bench_sha1(s);
  bench_sha2(s);

  int i = 0;
  for (size_t ds : data_sizes)
  {
    std::string dss = std::to_string(ds);

    Benchmark::Benchmark::PlotSpec plot_specs_cycles = {
      std::make_pair(filter("bench_hash_MD5.csv", "," + dss + ","),      "using 'Avg':xticlabels(strcol('Provider')) title 'MD5'"),
      std::make_pair(filter("bench_hash_SHA1.csv", "," + dss + ","),     "using 'Avg':xticlabels(strcol('Provider')) title 'SHA1'"),
      std::make_pair(filter("bench_hash_SHA2_224.csv", "," + dss + ","), "using 'Avg':xticlabels(strcol('Provider')) title 'SHA2-224'"),
      std::make_pair(filter("bench_hash_SHA2_256.csv", "," + dss + ","), "using 'Avg':xticlabels(strcol('Provider')) title 'SHA2-256'"),
      std::make_pair(filter("bench_hash_SHA2_384.csv", "," + dss + ","), "using 'Avg':xticlabels(strcol('Provider')) title 'SHA2-384'"),
      std::make_pair(filter("bench_hash_SHA2_512.csv", "," + dss + ","), "using 'Avg':xticlabels(strcol('Provider')) title 'SHA2-512'")
    };

    Benchmark::Benchmark::PlotSpec plot_specs_bytes = {
      std::make_pair(filter("bench_hash_MD5.csv", "," + dss + ","),      "using 'Avg Cycles/Byte':xticlabels(strcol('Provider')) title 'MD5'"),
      std::make_pair(filter("bench_hash_SHA1.csv", "," + dss + ","),     "using 'Avg Cycles/Byte':xticlabels(strcol('Provider')) title 'SHA1'"),
      std::make_pair(filter("bench_hash_SHA2_224.csv", "," + dss + ","), "using 'Avg Cycles/Byte':xticlabels(strcol('Provider')) title 'SHA2-224'"),
      std::make_pair(filter("bench_hash_SHA2_256.csv", "," + dss + ","), "using 'Avg Cycles/Byte':xticlabels(strcol('Provider')) title 'SHA2-256'"),
      std::make_pair(filter("bench_hash_SHA2_384.csv", "," + dss + ","), "using 'Avg Cycles/Byte':xticlabels(strcol('Provider')) title 'SHA2-384'"),
      std::make_pair(filter("bench_hash_SHA2_512.csv", "," + dss + ","), "using 'Avg Cycles/Byte':xticlabels(strcol('Provider')) title 'SHA2-512'")
    };

    std::string title = "Hash performance (message length " + std::to_string(ds) + " bytes)";

    std::stringstream extras;
    extras << "set xtics norotate\n";
    extras << "set key on\n";
    extras << "set style histogram clustered gap 3 title\n";
    extras << "set style data histograms\n";
    //extras << "set xrange [-.5:2.5]";

    Benchmark::make_plot(s,
                         "svg",
                         title,
                         "",
                         "Avg. performance [CPU cycles/hash]",
                         plot_specs_cycles,
                         "bench_hash_all_" + std::to_string(ds) + "_cycles.svg",
                         extras.str());

    Benchmark::make_plot(s,
                         "svg",
                         title,
                         "",
                         "Avg. performance [CPU cycles/byte]",
                         plot_specs_bytes,
                         "bench_hash_all_" + std::to_string(ds) + "_bytes.svg",
                         extras.str());


    std::vector<std::string> fils = { "MD5", "SHA1", "SHA2_224", "SHA2_256", "SHA2_384", "SHA2_512" };
    std::string data_filename = "bench_hash_all_" + std::to_string(ds) + ".csv";
    std::ofstream outf(data_filename, std::ios::out | std::ios::trunc);
    outf << "\"Provider\",\"Algorithm\",\"Size [b]\"" + Benchmark::column_headers() + ",\"Avg Cycles/Byte\"\n";
    outf.close();
    for (std::string fil : fils)
    {
      int r = system(("grep \"," + std::to_string(ds) + ",\" bench_hash_" + fil + ".csv >> bench_hash_all_" + std::to_string(ds) + ".csv").c_str());
      if (r != 0)
        throw std::logic_error("Plot generation failed");
    }

    extras.str("");
    extras << "set xtics norotate\n";
    extras << "set key top right\n";
    extras << "set style histogram clustered gap 2 title offset 0,-1.5\n";
    extras << "set style data histograms\n";

    Benchmark::Benchmark::PlotSpec plot_specs_bytes_by_alg;

    bool first = true;

    std::vector<std::string> algs = { "MD5", "SHA1", "SHA2-224", "SHA2-256", "SHA2-384", "SHA2-512" };
    size_t num_in_histo = 0;
    for (int i = 0; i < algs.size(); i++)
    {
      std::string alg = algs[i];
      std::string dfn = "bench_hash_" + fils[i] + ".csv";
      auto pss = {
        std::make_pair(filter(dfn, "EverCrypt\\\",\\\"" + alg + "\\\"," + dss + ","),
                       std::string("using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) ") + (first ? "title 'EverCrypt'" : "notitle") + " lt 1"),
        #ifdef HAVE_HACL
        std::make_pair(filter(dfn, "HaCl\\\",\\\"" + alg + "\\\"," + dss + ","),
                       std::string("using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) ") + (first ? "title 'HaCl'" : "notitle") + " lt 2"),
        #endif
        #ifdef HAVE_OPENSSL
        std::make_pair(filter(dfn, "OpenSSL\\\",\\\"" + alg + "\\\"," + dss + ","),
                       std::string("using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) ") + (first ? "title 'OpenSSL'" : "notitle") + " lt 3"),
        #endif
        #ifdef HAVE_BCRYPT
        std::make_pair(filter(dfn, "BCrypt\\\",\\\"" + alg + "\\\"," + dss + ","),
                       std::string("using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) ") + (first ? "title 'BCrypt'" : "notitle") + " lt 4"),
        #endif
      };
      plot_specs_bytes_by_alg += pss;
      num_in_histo = pss.size();
      first = false;
    }

    Benchmark::make_plot(s,
                         "svg",
                         title,
                         "",
                         "Avg. performance [CPU cycles/byte]",
                         plot_specs_bytes_by_alg,
                         "bench_hash_all_" + std::to_string(ds) + "_bytes_by_alg.svg",
                         extras.str(),
                         algs,
                         num_in_histo);

    i++;
    #ifdef HAVE_HACL
    i++;
    #endif
    #ifdef HAVE_OPENSSL
    i++;
    #endif
    #ifdef HAVE_BCRYPT
    i++;
    #endif
  }
}
