#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <Hacl_Poly1305_128.h>
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

class MACBenchmark : public Benchmark
{
  protected:
    const size_t key_sz = 32;
    size_t msg_len;

    uint8_t *key;
    uint8_t *msg;
    uint8_t *mac;
    std::string algorithm;

  public:
    static std::string column_headers() { return "\"Provider\", \"Algorithm\", \"Size [b]\"" + Benchmark::column_headers() + ", \"Avg Cycles/Byte\""; }

    MACBenchmark(size_t msg_len) : Benchmark(), msg_len(msg_len)
    {
      if (msg_len == 0)
        throw std::logic_error("Need msg_len > 0");

      key = new uint8_t[key_sz];
      msg = new uint8_t[msg_len];
      mac = new uint8_t[32];
    }

    void set_name(const std::string & provider, const std::string & algorithm)
    {
      Benchmark::set_name(provider);
      this->algorithm = algorithm;
    }

    virtual ~MACBenchmark()
    {
      delete[](mac);
      delete[](msg);
      delete[](key);
    }

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      randomize((char*)key, key_sz);
      randomize((char*)msg, msg_len);
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

class EverCryptPoly1305 : public MACBenchmark
{
  public:
    EverCryptPoly1305(size_t msg_len) :
      MACBenchmark(msg_len)
      { set_name("EverCrypt", "Poly1305"); }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      MACBenchmark::bench_setup(s);
    }
    virtual void bench_func()
    {
      Hacl_Poly1305_128_poly1305_mac(mac, msg_len, msg, key);
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      MACBenchmark::bench_cleanup(s);
    }
    virtual ~EverCryptPoly1305() { }
};


#ifdef HAVE_OPENSSL
// See https://github.com/openssl/openssl/blob/master/demos/evp/aesgcm.c

// class OpenSSLPoly1305 : public MACBenchmark
// {
//   protected:
//     EVP_MAC_CTX *ctx;
//     int outlen;

//   public:
//     OpenSSLPoly1305(size_t msg_len) :
//       MACBenchmark(msg_len)
//       {
//         set_name("OpenSSL", "Poly1305\\nPoly1305");
//         ctx = EVP_MAC_CTX_new();
//       }
//     virtual void bench_setup(const BenchmarkSettings & s)
//     {
//       MACBenchmark::bench_setup(s);
//       EVP_PKEY_POLY1305
//       if ((EVP_EncryptInit_ex(ctx, EVP_Poly1305(), NULL, key, iv)  <= 0))
//           throw std::logic_error("OpenSSL MAC initialization failed");
//     }
//     virtual void bench_func()
//     {
//       #ifdef _DEBUG
//       if ((EVP_EncryptUpdate(ctx, MAC, &outlen, msg, msg_len) <= 0) ||
//           (EVP_EncryptFinal_ex(ctx, MAC, &outlen) <= 0))
//           throw std::logic_error("OpenSSL encryption failed");
//       #else
//       EVP_EncryptUpdate(ctx, MAC, &outlen, msg, msg_len);
//       EVP_EncryptFinal_ex(ctx, MAC, &outlen);
//       #endif
//     }
//     virtual ~OpenSSLPoly1305() { EVP_MAC_CTX_free(ctx); }
// };

#endif

#ifdef HAVE_BCRYPT
// TODO
#endif


#ifdef HAVE_JC
enum JCInstructionSet { REF, AVX, AVX2 };

template<JCInstructionSet is>
class JCPoly1305 : public MACBenchmark
{
  protected:
    static void (*f)(uint64_t*, uint64_t*, uint64_t, uint64_t*);

  public:
    JCPoly1305(size_t msg_len) :
      MACBenchmark(msg_len)
    {
      set_name("libjc", "Poly1305");
    }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      MACBenchmark::bench_setup(s);
    }
    virtual void bench_func()
    {
      f((uint64_t*)mac, (uint64_t*)msg, msg_len, (uint64_t*)key);
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      MACBenchmark::bench_cleanup(s);
    }
    virtual ~JCPoly1305() { }
};

template<> void (*JCPoly1305<JCInstructionSet::REF>::f)(uint64_t*, uint64_t*, uint64_t, uint64_t*) = poly1305_ref3;
// cwinter: can't link both, avx and avx2, because of symbol name clashes
//template<> void (*JCPoly1305<JCInstructionSet::AVX>::f)(uint64_t*, uint64_t*, uint64_t, uint64_t*) = poly1305_avx;
template<> void (*JCPoly1305<JCInstructionSet::AVX2>::f)(uint64_t*, uint64_t*, uint64_t, uint64_t*) = poly1305_avx2;
#endif

static std::string filter(const std::string & data_filename, const std::string & keyword)
{
  return "< grep -e \"^\\\"" + keyword + "\" -e \"^\\\"Provider\" " + data_filename;
}

void bench_mac(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  Benchmark::PlotSpec plot_specs_cycles;
  Benchmark::PlotSpec plot_specs_bytes;

  for (size_t ds: data_sizes)
  {
    std::stringstream dsstr;
    dsstr << ds;

    std::stringstream data_filename;
    data_filename << "bench_mac_" << ds << ".csv";

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
      new EverCryptPoly1305(ds),

      #ifdef HAVE_OPENSSL
      //new OpenSSLPoly1305(ds),
      #endif

      #ifdef HAVE_BCRYPT
      #endif

      #ifdef HAVE_JC
      new JCPoly1305<JCInstructionSet::AVX2>(ds),
      #endif
      };

      Benchmark::run_batch(s, MACBenchmark::column_headers(), data_filename.str(), todo);

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
                      "MAC performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/encryption]",
                      plot_specs_ds_cycles,
                      "bench_mac_all_" + dsstr.str() + "_cycles.svg",
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
                      "MAC performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/byte]",
                      plot_specs_ds_bytes,
                      "bench_mac_all_" + dsstr.str() + "_bytes.svg",
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
                      "MAC performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/encryption]",
                      plot_specs_ds_candlesticks,
                      "bench_mac_all_" + dsstr.str() + "_candlesticks.svg",
                      extras.str());
  }

  std::stringstream extras;
  extras << "set key top left inside\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                       "svg",
                       "MAC Performance",
                       "",
                       "Avg. performance [CPU cycles/encryption]",
                       plot_specs_cycles,
                       "bench_mac_all_cycles.svg",
                       extras.str());

  Benchmark::make_plot(s,
                       "svg",
                       "MAC Performance",
                       "",
                       "Avg. performance [CPU cycles/byte]",
                       plot_specs_bytes,
                       "bench_mac_all_bytes.svg",
                       extras.str());
}
