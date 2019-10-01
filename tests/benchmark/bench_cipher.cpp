#include <stdexcept>
#include <sstream>
#include <iostream>
#include <fstream>

#include <time.h>
#include <benchmark.h>

extern "C" {
#include <EverCrypt_AutoConfig2.h>
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
    const size_t iv_len = 16;
    size_t msg_len;

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
      for (size_t i = 12; i < 16; i++)
        iv[i] = 0;
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
      { set_name("EverCrypt", "ChaCha20"); }
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

#ifdef WIN32
#undef HAVE_OPENSSL
#endif

#ifdef HAVE_OPENSSL
// See https://github.com/openssl/openssl/blob/master/demos/evp/aesgcm.c

class OpenSSLChaCha20 : public CipherBenchmark
{
  protected:
    EVP_CIPHER_CTX *ctx;
    int outlen;
    uint8_t openssl_iv[16];

  public:
    OpenSSLChaCha20(size_t msg_len) :
      CipherBenchmark(msg_len)
      {
        set_name("OpenSSL", "ChaCha20");
        ctx = EVP_CIPHER_CTX_new();
      }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_setup(s);
      for (size_t i = 4; i < iv_len; i++)
        openssl_iv[i] = iv[i-4];
      openssl_iv[0] = openssl_iv[1] = openssl_iv[2] = openssl_iv[3] = 0;
      if ((EVP_CipherInit_ex(ctx, EVP_chacha20(), NULL, key, openssl_iv, 1) <= 0))
          throw std::logic_error("OpenSSL cipher initialization failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if ((EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len) <= 0) ||
          (EVP_EncryptFinal(ctx, cipher, &outlen) <= 0))
          throw std::logic_error("OpenSSL encryption failed");

      uint8_t tmp[msg_len];
      EverCrypt_Cipher_chacha20(msg_len, tmp, plain, key, iv, 0);

      for (size_t i = 0; i < msg_len; i++)
        if (cipher[i] != tmp[i]) {
          std::cout << "EverCrypt: "; Benchmark::print_buffer(tmp, msg_len);
          std::cout << "OpenSSL  : "; Benchmark::print_buffer(cipher, msg_len);
          throw std::logic_error("Encryption mismatch");
        }
      #else
      EVP_EncryptUpdate(ctx, cipher, &outlen, plain, msg_len);
      EVP_EncryptFinal(ctx, cipher, &outlen);
      #endif
    }
    virtual ~OpenSSLChaCha20() { EVP_CIPHER_CTX_free(ctx); }
};

#endif

#ifdef HAVE_BCRYPT
#undef HAVE_BCRYPT // TODO
#endif

#ifdef WIN32
#undef HAVE_JC
#endif

#ifdef HAVE_JC
enum JCInstructionSet { REF, AVX, AVX2 };

template<JCInstructionSet is>
class JCChaCha20 : public CipherBenchmark
{
  static void (*f)(uint64_t*, uint64_t*, uint32_t, uint64_t*, uint64_t*, uint32_t);

  public:
    JCChaCha20(size_t msg_len) :
      CipherBenchmark(msg_len)
    {
      set_name("libjc", "ChaCha20");
    }
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_setup(s);
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      uint8_t tmp[msg_len];
      EverCrypt_Cipher_chacha20(msg_len, tmp, plain, key, iv, ctr);
      #endif

      f((uint64_t*)cipher, (uint64_t*)plain, msg_len, (uint64_t*)key, (uint64_t*)iv, ctr);

      #ifdef _DEBUG
      for (size_t i = 0; i < msg_len; i++)
        if (cipher[i] != tmp[i]) {
          std::cout << "EverCrypt: "; Benchmark::print_buffer(tmp, msg_len);
          std::cout << "libjc    : "; Benchmark::print_buffer(cipher, msg_len);
          throw std::logic_error("Encryption mismatch");
        }
      #endif
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      CipherBenchmark::bench_cleanup(s);
    }
    virtual ~JCChaCha20() { }
};

template<> void (*JCChaCha20<REF>::f)(uint64_t*, uint64_t*, uint32_t, uint64_t*, uint64_t*, uint32_t) = chacha20_ref;
#ifndef WIN32
template<> void (*JCChaCha20<AVX>::f)(uint64_t*, uint64_t*, uint32_t, uint64_t*, uint64_t*, uint32_t) = libjc_avx_chacha20_avx;
#endif
template<> void (*JCChaCha20<AVX2>::f)(uint64_t*, uint64_t*, uint32_t, uint64_t*, uint64_t*, uint32_t) = libjc_avx2_chacha20_avx2;
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
      new JCChaCha20<JCInstructionSet::AVX2>(ds),
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
      Benchmark::add_label_offsets(plot_specs_ds_cycles, 0.5, 8.0);

      std::stringstream extras;
      extras << "set key top left inside\n";
      extras << "set style histogram clustered gap 3 title\n";
      extras << "set style data histograms\n";
      extras << "set bmargin 5\n";
      extras << "set xrange [-0.5:0.5]\n";

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
      Benchmark::add_label_offsets(plot_specs_ds_bytes, 0.5, 8.0);

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
  extras << "set key top right inside\n";
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
