#include <string>
#include <sstream>

#include "benchmark.h"

extern "C" {
#include <EverCrypt_Curve25519.h>
}

#ifdef HAVE_HACL
#include <Hacl_Curve25519.h>
#endif

#ifdef HAVE_OPENSSL
#include <openssl/evp.h>
#include <openssl/ec.h>
#endif

#ifdef HAVE_RFC7748
#include <rfc7748_precomputed.h>
#endif

class Curve25519Benchmark: public Benchmark
{
  protected:
    typedef __attribute__((aligned(32))) uint8_t X25519_KEY[32];
    X25519_KEY shared_secret, our_secret, their_public;

  public:
    static constexpr auto header = "Algorithm, CPU Time (incl) [sec], CPU Time (excl) [sec], Avg Cycles/Derivation, Min Cycles/Derivation, Max Cycles/Derivation";

    Curve25519Benchmark(std::string const & prefix) : Benchmark(prefix) {}

    virtual ~Curve25519Benchmark() {}

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Benchmark::bench_setup(s);
      randomize(our_secret, 32);
      randomize(their_public, 32);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s)
    {
      rs << "\"" << name.c_str() << "\""
        << "," << toverall/(double)CLOCKS_PER_SEC
        << "," << ttotal/(double)CLOCKS_PER_SEC
        << "," << ctotal/(double)s.samples
        << "," << cmin
        << "," << cmax
        << "\n";
    }
};

class EverCrypt: public Curve25519Benchmark
{
  public:
    EverCrypt() : Curve25519Benchmark("EverCrypt") {}
    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Curve25519Benchmark::bench_setup(s);
      EverCrypt_Curve25519_secret_to_public(their_public, our_secret);
    }
    virtual void bench_func()
      { EverCrypt_Curve25519_ecdh(shared_secret, our_secret, their_public); }
    virtual ~EverCrypt() {}
};

#ifdef HAVE_RFC7748
extern void x25519_shared_secret_x64(uint8_t* sec, uint8_t* priv, uint8_t* pub);

class RFC7748: public Curve25519Benchmark
{
  public:
    RFC7748() : Curve25519Benchmark("RFC 7748") {}
    virtual void bench_func()
      { X25519_Shared(shared_secret, our_secret, their_public); }
    virtual ~RFC7748() {}
};
#endif

#ifdef HAVE_HACL
class Hacl51: public Curve25519Benchmark
{
  public:
    Hacl51() : Curve25519Benchmark("HaCl (51)") {}
    virtual void bench_func()
      { Hacl_Curve25519_51_ecdh(shared_secret, our_secret, their_public); }
    virtual ~Hacl51() {}
};

class Hacl64: public Curve25519Benchmark
{
  public:
    Hacl64() : Curve25519Benchmark("Hacl (64)") {}
    virtual void bench_func()
      { Hacl_Curve25519_64_ecdh(shared_secret, our_secret, their_public); }
    virtual ~Hacl64() {}
};
#endif

#ifdef HAVE_OPENSSL
class OpenSSL: public Curve25519Benchmark
{
  protected:
    size_t skeylen;
    EVP_PKEY_CTX *ctx;
    EVP_PKEY *ours = NULL, *theirs = NULL;

  public:
    OpenSSL() : Curve25519Benchmark("OpenSSL") {}

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Curve25519Benchmark::bench_setup(s);

      ours = EVP_PKEY_new();
      EVP_PKEY_CTX *our_key_ctx = EVP_PKEY_CTX_new_id(NID_X25519, NULL);
      if (EVP_PKEY_keygen_init(our_key_ctx) <= 0) throw std::logic_error("failed");
      if (EVP_PKEY_keygen(our_key_ctx, &ours) <= 0) throw std::logic_error("failed");
	    EVP_PKEY_CTX_free(our_key_ctx);

      theirs = EVP_PKEY_new();
      EVP_PKEY_CTX *their_key_ctx = EVP_PKEY_CTX_new_id(NID_X25519, NULL);
      if (EVP_PKEY_keygen_init(their_key_ctx) <= 0) throw std::logic_error("failed");
      if (EVP_PKEY_keygen(their_key_ctx, &theirs) <= 0) throw std::logic_error("failed");
      EVP_PKEY_CTX_free(their_key_ctx);

      ctx = EVP_PKEY_CTX_new(ours, NULL);

      if (EVP_PKEY_derive_init(ctx) <= 0)
        throw std::logic_error("OpenSSL derive_init failed");
      if (EVP_PKEY_derive_set_peer(ctx, theirs) <= 0)
        throw std::logic_error("OpenSSL derive_set_peer failed");
    }
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (
      #endif
        EVP_PKEY_derive(ctx, shared_secret, &skeylen)
      #ifdef _DEBUG
        <= 0)
        throw std::logic_error("OpenSSL X25519 failed")
      #endif
      ;
    }
    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      EVP_PKEY_free(theirs);
      EVP_PKEY_free(ours);
      EVP_PKEY_CTX_free(ctx);

      Curve25519Benchmark::bench_cleanup(s);
    }
    virtual ~OpenSSL() {}
};
#endif

void bench_curve25519(const BenchmarkSettings & s)
{
  std::stringstream data_filename;
  data_filename << "bench_curve25519.csv";

  std::list<Benchmark*> todo = {
    new EverCrypt(),
    #ifdef HAVE_RFC7748
    new RFC7748(),
    #endif
    #ifdef HAVE_HACL
    new Hacl51(),
    new Hacl64(),
    #endif
    #ifdef HAVE_OPENSSL
    new OpenSSL()
    #endif
    };

  std::stringstream num_benchmarks;
  num_benchmarks << todo.size();

  Benchmark::run_batch(s, Curve25519Benchmark::header, data_filename.str(), todo);

  Benchmark::plot_spec_t plot_spec_cycles =
    { std::make_pair(data_filename.str(), "using 4:xticlabels(1) with boxes title columnheader, '' using ($0-1):4:xticlabels(1):(sprintf(\"%0.0f\", $5)) with labels font \"Courier,8\" offset char 0,.5") };

  Benchmark::plot_spec_t plot_spec_candlesticks =
    { std::make_pair(data_filename.str(), "using 0:4:5:6:4:xticlabels(1) with candlesticks whiskerbars .25") };

  Benchmark::make_plot(s,
                       "svg",
                       "Curve25519 performance",
                       "",
                       "Avg. performance [CPU cycles/derivation]",
                       plot_spec_cycles,
                       "bench_curve25519_cycles.svg",
                       "set xtics norotate");

  Benchmark::make_plot(s,
                       "svg",
                       "Curve25519 performance",
                       "",
                       "Avg. performance [CPU cycles/derivation]",
                       plot_spec_candlesticks,
                       "bench_curve25519_candlesticks.svg",
                       "set xrange[.5:" + num_benchmarks.str() + "+.5]");
}