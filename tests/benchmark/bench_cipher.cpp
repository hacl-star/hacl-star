#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <EverCrypt_Cipher.h>
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

class CipherBenchmark : public Benchmark
{
  protected:
    const size_t key_sz = 32;
    size_t msg_len, iv_len = 12;

    uint8_t *key;
    uint8_t *plain;
    uint8_t *cipher;
    uint8_t *iv;
    size_t ctr;
    std::string algorithm;

  public:
    static std::string column_headers() { return "\"Provider\", \"Algorithm\", \"Size [b]\"" + Benchmark::column_headers() + ", \"Avg Cycles/Byte\""; }

    CipherBenchmark(size_t msg_len) : Benchmark(), msg_len(msg_len)
    {
      if (msg_len == 0)
        throw std::logic_error("Need msg_len > 0");

      key = new uint8_t[key_sz];
      plain = new uint8_t[msg_len];
      cipher = new uint8_t[msg_len];
      iv = new uint8_t[iv_len];
      ctr = 0;
    }

    void set_name(const std::string & provider, const std::string & algorithm)
    {
      Benchmark::set_name(provider);
      this->algorithm = algorithm;
    }

    virtual ~CipherBenchmark()
    {
      delete[](iv);
      delete[](cipher);
      delete[](plain);
      delete[](key);
    }

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      randomize((char*)key, key_sz);
      randomize((char*)plain, msg_len);
      randomize((char*)iv, iv_len);
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


class EverCryptChaCha20 : public CipherBenchmark
{
  public:
    EverCryptChaCha20(size_t msg_len) :
      CipherBenchmark(msg_len)
      { set_name("EverCrypt", "Chacha20\\nPoly1305"); }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_setup(s);
    }
    virtual void bench_func()
    {
      EverCrypt_Cipher_chacha20(msg_len, cipher, plain, key, iv, ctr);
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_cleanup(s);
    }
    virtual ~EverCryptChaCha20() { }
};


#ifdef HAVE_OPENSSL
// See https://github.com/openssl/openssl/blob/master/demos/evp/aesgcm.c

class OpenSSLChaCha20 : public CipherBenchmark
{
  protected:
    EVP_CIPHER_CTX *ctx;
    int outlen;

  public:
    OpenSSLChaCha20(size_t msg_len) :
      CipherBenchmark(msg_len)
      {
        set_name("OpenSSL", "Chacha20\\nPoly1305");
        ctx = EVP_CIPHER_CTX_new();
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_setup(s);
      if ((EVP_EncryptInit_ex(ctx, EVP_chacha20(), NULL, key, iv)  <= 0))
          throw std::logic_error("OpenSSL cipher initialization failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if ((EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len) <= 0) ||
          (EVP_EncryptFinal_ex(ctx, cipher, &outlen) <= 0))
          throw std::logic_error("OpenSSL encryption failed");
      #else
      EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len);
      EVP_EncryptFinal_ex(ctx, cipher, &outlen);
      #endif
    }
    virtual ~OpenSSLChaCha20() { EVP_CIPHER_CTX_free(ctx); }
};

#endif

#ifdef HAVE_BCRYPT
// TODO
#endif


#ifdef HAVE_JC
class JCChaCha20 : public CipherBenchmark
{
  void (*f)(uint64_t*, uint64_t*, uint32_t, uint64_t*, uint64_t*, uint32_t) = nullptr;

  public:
    enum InstructionSet { JC_REF, /*  JC_AVX, */ JC_AVX2 };

    JCChaCha20(InstructionSet is, size_t msg_len) :
      CipherBenchmark(msg_len)
    {
        switch(is) {
          case JC_REF: set_name("libjc", "Chacha20 (ref)"); f = chacha20_ref; break;
          // case JC_AVX: set_name("libjc", "Chacha20"); f = chacha20_avx; break; // cwinter: can't link both, avx and avx2, because of symbol name clashes
          case JC_AVX2: set_name("libjc", "Chacha20"); f = chacha20_avx2; break;
        }
    }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_setup(s);
    }
    virtual void bench_func()
    {
      f((uint64_t*)cipher, (uint64_t*)plain, msg_len, (uint64_t*)key, (uint64_t*)iv, ctr);
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_cleanup(s);
    }
    virtual ~JCChaCha20() { }
};
#endif

static std::string filter(const std::string & data_filename, const std::string & keyword)
{
  return "< grep -e \"^\\\"" + keyword + "\" -e \"^\\\"Provider\" " + data_filename;
}

void bench_cipher(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  Benchmark::PlotSpec plot_specs_cycles;
  Benchmark::PlotSpec plot_specs_bytes;

  for (size_t ds: data_sizes)
  {
    std::stringstream dsstr;
    dsstr << ds;

    std::stringstream data_filename;
    data_filename << "bench_cipher_" << ds << ".csv";

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
      new EverCryptChaCha20(ds),

      #ifdef HAVE_OPENSSL
      new OpenSSLChaCha20(ds),
      #endif

      #ifdef HAVE_BCRYPT
      #endif

      #ifdef HAVE_JC
      new JCChaCha20(JCChaCha20::JC_AVX2, ds),
      #endif
      };

      Benchmark::run_batch(s, CipherBenchmark::column_headers(), data_filename.str(), todo);

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
                      "Cipher performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/encryption]",
                      plot_specs_ds_cycles,
                      "bench_cipher_all_" + dsstr.str() + "_cycles.svg",
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
                      "Cipher performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/byte]",
                      plot_specs_ds_bytes,
                      "bench_cipher_all_" + dsstr.str() + "_bytes.svg",
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
                      "Cipher performance (message length " + dsstr.str() + " bytes)",
                      "",
                      "Avg. performance [CPU cycles/encryption]",
                      plot_specs_ds_candlesticks,
                      "bench_cipher_all_" + dsstr.str() + "_candlesticks.svg",
                      extras.str());
  }

  std::stringstream extras;
  extras << "set key top left inside\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                       "svg",
                       "Cipher Performance",
                       "",
                       "Avg. performance [CPU cycles/encryption]",
                       plot_specs_cycles,
                       "bench_cipher_all_cycles.svg",
                       extras.str());

  Benchmark::make_plot(s,
                       "svg",
                       "Cipher Performance",
                       "",
                       "Avg. performance [CPU cycles/byte]",
                       plot_specs_bytes,
                       "bench_cipher_all_bytes.svg",
                       extras.str());
}
