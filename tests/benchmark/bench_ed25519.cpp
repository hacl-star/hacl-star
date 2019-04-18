#include <string>
#include <sstream>

#include "benchmark.h"

#ifdef HAVE_HACL
extern "C" {
#include <Hacl_Ed25519.h>
}
#endif

#ifdef HAVE_OPENSSL
#include <openssl/evp.h>
#include <openssl/ec.h>
#endif

#define SIGNATURE_LENGTH 64

class DSABenchmark: public Benchmark
{
  protected:
      typedef __attribute__((aligned(32))) uint8_t X25519_KEY[32];
      X25519_KEY shared_secret, our_secret, our_public, their_secret, their_public;
      size_t msg_len;
      uint8_t *signature, *msg;

  public:
    static constexpr auto header = "Algorithm, Size [b], CPU Time (incl) [sec], CPU Time (excl) [sec], Avg Cycles/Op, Min Cycles/Op, Max Cycles/Op, Avg Cycles/Byte";

    DSABenchmark(size_t msg_len, std::string const & prefix) :
      Benchmark(prefix),
      msg_len(msg_len)
    {
      signature = new uint8_t[SIGNATURE_LENGTH];
      msg = new uint8_t[msg_len];
    }

    virtual ~DSABenchmark()
    {
      delete(msg);
      delete(signature);
    }

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      randomize(our_secret, 32);
      randomize(their_secret, 32);
      randomize(msg, msg_len);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s)
    {
      rs << "\"" << name.c_str() << "\""
        << "," << msg_len
        << "," << toverall/(double)CLOCKS_PER_SEC
        << "," << ttotal/(double)CLOCKS_PER_SEC
        << "," << ctotal/(double)s.samples
        << "," << cmin
        << "," << cmax
        << "," << (ctotal/(double)msg_len)/(double)s.samples
        << "\n";
    }
};

#ifdef HAVE_HACL
class HaclSign: public DSABenchmark
{
  public:
    HaclSign(size_t msg_len) : DSABenchmark(msg_len, "HaCl") {}
    virtual void bench_setup(const BenchmarkSettings & s) {}
    virtual void bench_func()
      { Hacl_Ed25519_sign(signature, our_secret, msg, msg_len); }
    virtual ~HaclSign() {}
};

#define EXPANDED_KEYS_SIZE 96

class HaclSignExpanded: public DSABenchmark
{
  protected:
    uint8_t expanded_keys[EXPANDED_KEYS_SIZE];

  public:
    HaclSignExpanded(size_t msg_len) : DSABenchmark(msg_len, "HaCl (expanded)") {}
    virtual void bench_setup(const BenchmarkSettings & s)
      { Hacl_Ed25519_expand_keys(expanded_keys, our_secret); }
    virtual void bench_func()
      { Hacl_Ed25519_sign_expanded(signature, expanded_keys, msg, msg_len); }
    virtual ~HaclSignExpanded() {}
};

class HaclVerify: public DSABenchmark
{
  public:
    HaclVerify(size_t msg_len) : DSABenchmark(msg_len, "HaCl (verify)") {}
    virtual void bench_setup(const BenchmarkSettings & s)
    {
        Hacl_Ed25519_secret_to_public(our_public, our_secret);
        Hacl_Ed25519_sign(signature, our_secret, msg, msg_len);
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (!
      #endif
        Hacl_Ed25519_verify(our_public, msg, msg_len, signature)
      #ifdef _DEBUG
      ) throw std::logic_error("Signature verification failed")
      #endif
      ;
    }
    virtual ~HaclVerify() {}
};
#endif

#ifdef HAVE_OPENSSL
class OpenSSLSign: public DSABenchmark
{
  protected:
    size_t sig_len = SIGNATURE_LENGTH;
    EVP_MD_CTX *mdctx;
    EVP_PKEY *ours = NULL;

  public:
    OpenSSLSign(size_t msg_len) : DSABenchmark(msg_len, "OpenSSL") {}
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      EVP_PKEY_CTX *pkctx = EVP_PKEY_CTX_new_id(EVP_PKEY_ED25519, NULL);
      EVP_PKEY_keygen_init(pkctx);
      EVP_PKEY_keygen(pkctx, &ours);
      EVP_PKEY_CTX_free(pkctx);

      mdctx = EVP_MD_CTX_new();
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (EVP_DigestSignInit(mdctx, NULL, NULL, NULL, ours) <= 0)
        throw std::logic_error("OpenSSL EVP_DigestSignInit failed");
      if (EVP_DigestSign(mdctx, signature, &sig_len, msg, msg_len) <= 0)
        throw std::logic_error("OpenSSL EVP_DigestSign failed");
      #else
      EVP_DigestSignInit(mdctx, NULL, NULL, NULL, ours);
      EVP_DigestSign(mdctx, signature, &sig_len, msg, msg_len);
      #endif
    }
    virtual ~OpenSSLSign()
      { EVP_MD_CTX_free(mdctx); }
};

class OpenSSLVerify: public DSABenchmark
{
  protected:
    size_t sig_len = SIGNATURE_LENGTH;
    EVP_MD_CTX *mdctx;
    EVP_PKEY *ours = NULL;

  public:
    OpenSSLVerify(size_t msg_len) : DSABenchmark(msg_len, "OpenSSL (verify)") {}
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      EVP_PKEY_CTX *pkctx = EVP_PKEY_CTX_new_id(EVP_PKEY_ED25519, NULL);
      EVP_PKEY_keygen_init(pkctx);
      EVP_PKEY_keygen(pkctx, &ours);
      EVP_PKEY_CTX_free(pkctx);

      mdctx = EVP_MD_CTX_new();

      if (EVP_DigestSignInit(mdctx, NULL, NULL, NULL, ours) <= 0)
        throw std::logic_error("OpenSSL EVP_DigestSignInit failed");
      if (EVP_DigestSign(mdctx, signature, &sig_len, msg, msg_len) <= 0)
        throw std::logic_error("OpenSSL EVP_DigestSign failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (EVP_DigestVerifyInit(mdctx, NULL, NULL, NULL, ours) <= 0)
        throw std::logic_error("OpenSSL EVP_DigestVerifyInit failed");
      if (EVP_DigestVerify(mdctx, signature, sig_len, msg, msg_len) <= 0)
        throw std::logic_error("OpenSSL EVP_DigestVerify failed");
      #else
      EVP_DigestVerifyInit(mdctx, NULL, NULL, NULL, ours);
      EVP_DigestVerify(mdctx, signature, sig_len, msg, msg_len);
      #endif
    }
    virtual ~OpenSSLVerify()
      { EVP_MD_CTX_free(mdctx); }
};
#endif

void bench_ed25519(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536 };

  for (size_t ds: data_sizes)
  {
    std::stringstream data_filename;
    data_filename << "bench_ed25519_" << ds << ".csv";

    std::list<Benchmark*> todo = {
      #ifdef HAVE_HACL
      new HaclSign(ds),
      new HaclSignExpanded(ds),
      new HaclVerify(ds),
      #endif

      #ifdef HAVE_OPENSSL
      new OpenSSLSign(ds),
      new OpenSSLVerify(ds),
      #endif
      };

    Benchmark::run_batch(s, DSABenchmark::header, data_filename.str(), todo);

    std::stringstream title;
    title << "Ed25519 performance (message size=" << ds << " bytes)";

    std::stringstream plot_filename;
    plot_filename << "bench_ed25519_" << ds << "_cycles.svg";

    Benchmark::plot_spec_t plot_spec_cycles =
      { std::make_pair(data_filename.str(), "using 5:xticlabels(1) with boxes title columnheader, '' using ($0-1):5:xticlabels(1):(sprintf(\"%0.0f\", $5)) with labels font \"Courier,8\" offset char 0,.5") };

    Benchmark::plot_spec_t plot_spec_bytes =
      { std::make_pair(data_filename.str(), "using 8:xticlabels(1) with boxes title columnheader, '' using ($0-1):8:xticlabels(1):(sprintf(\"%0.0f\", $5)) with labels font \"Courier,8\" offset char 0,.5") };

    Benchmark::make_plot(s,
                         "svg",
                         title.str(),
                         "",
                         "Avg. performance [CPU cycles/operation]",
                         plot_spec_cycles,
                         plot_filename.str(),
                         "");

    plot_filename.str("");
    plot_filename << "bench_ed25519_" << ds << "_bytes.svg";

    Benchmark::make_plot(s,
                         "svg",
                         title.str(),
                         "",
                         "Avg. performance [CPU cycles/byte]",
                         plot_spec_bytes,
                         plot_filename.str(),
                         "");
  }
}