#include <string>
#include <sstream>

#include "benchmark.h"

extern "C" {
#include <EverCrypt_Curve25519.h>
}

class Curve25519Benchmark: public Benchmark
{
  protected:
    typedef __attribute__((aligned(32))) uint8_t X25519_KEY[32];
    X25519_KEY shared_secret, our_secret, their_public;

  public:
    static std::string column_headers() { return "\"Algorithm\"" + Benchmark::column_headers(); }

    Curve25519Benchmark(std::string const & prefix) : Benchmark(prefix) {}

    virtual ~Curve25519Benchmark() {}

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Benchmark::bench_setup(s);
      randomize(our_secret, 32);
      randomize(their_public, 32);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << "\"" << name.c_str() << "\"";
      Benchmark::report(rs, s);
      rs << "\n";
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
#include <rfc7748_precomputed.h>
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
#include <Hacl_Curve25519.h>

class Hacl51: public Curve25519Benchmark
{
  public:
    Hacl51() : Curve25519Benchmark("HaCl\\n(Radix 51)") {}
    virtual void bench_func()
      { Hacl_Curve25519_51_ecdh(shared_secret, our_secret, their_public); }
    virtual ~Hacl51() {}
};

class Hacl64: public Curve25519Benchmark
{
  public:
    Hacl64() : Curve25519Benchmark("HaCl\\n(Radix 64)") {}
    virtual void bench_func()
      { Hacl_Curve25519_64_ecdh(shared_secret, our_secret, their_public); }
    virtual ~Hacl64() {}
};
#endif

#ifdef HAVE_OPENSSL
#include <openssl/evp.h>
#include <openssl/ec.h>

extern "C" {
extern int X25519(uint8_t out_shared_key[32], const uint8_t private_key[32], const uint8_t peer_public_value[32]);
}

class OpenSSL: public Curve25519Benchmark
{
  public:
    OpenSSL() : Curve25519Benchmark("OpenSSL") {}
    virtual void bench_func()
    {
      #ifdef _DEBUG
      if (
      #endif
        X25519(shared_secret, our_secret, their_public)
      #ifdef _DEBUG
        <= 0)
        throw std::logic_error("OpenSSL X25519 failed")
      #endif
      ;
    }
    virtual ~OpenSSL() {}
};

class OpenSSLEVP: public Curve25519Benchmark
{
  protected:
    size_t skeylen;
    EVP_PKEY_CTX *ctx;
    EVP_PKEY *ours = NULL, *theirs = NULL;

  public:
    OpenSSLEVP() : Curve25519Benchmark("OpenSSL\\n(EVP)") {}

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
    virtual ~OpenSSLEVP() {}
};
#endif


#ifdef HAVE_FIAT_CURVE25519
#include "fiat-curve25519.h"

class Fiat: public Curve25519Benchmark
{
  public:
    Fiat() : Curve25519Benchmark("Fiat") {}
    virtual void bench_func()
      { crypto_scalarmult(shared_secret, our_secret, their_public); }
};
#endif

void bench_curve25519(const BenchmarkSettings & s)
{
  std::string data_filename = "bench_curve25519.csv";

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
    new OpenSSL(),
    new OpenSSLEVP(),
    #endif
    #ifdef HAVE_FIAT_CURVE25519
    new Fiat()
    #endif
    };

  std::stringstream num_benchmarks;
  num_benchmarks << todo.size();

  Benchmark::run_batch(s, Curve25519Benchmark::column_headers(), data_filename, todo);

  std::stringstream extras;
  extras << "set style histogram clustered gap 1 title\n";
  extras << "set style data histograms\n";
  extras << "set xrange[-.5:" + num_benchmarks.str() + "-.5]\n";
  extras << "set bmargin 4\n";

  Benchmark::make_plot(s,
                       "svg",
                       "Curve25519 performance",
                       "",
                       "Avg. performance [CPU cycles/derivation]",
                       Benchmark::histogram_line(data_filename, "", "Avg", "strcol('Algorithm')", 0),
                       "bench_curve25519_cycles.svg",
                       extras.str());

  extras << "set boxwidth 0.25\n";
  extras << "set style fill empty\n";

  Benchmark::make_plot(s,
                       "svg",
                       "Curve25519 performance",
                       "",
                       "Avg. performance [CPU cycles/derivation]",
                       Benchmark::candlestick_line(data_filename, "", "strcol('Algorithm')"),
                       "bench_curve25519_candlesticks.svg",
                       extras.str());
}