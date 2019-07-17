#include <cstdlib>
#include <string>
#include <cstring>
#include <list>
#include <algorithm>

#include "benchmark.h"

#include "bench_hash.h"
#include "bench_aead.h"
#include "bench_curve25519.h"
#include "bench_ed25519.h"
#include "bench_merkle.h"
#include "bench_cipher.h"
#include "bench_mac.h"

BenchmarkSettings & parse_args(int argc, char const ** argv)
{
  static BenchmarkSettings r;

  std::list<std::string> arg_fams;

  for (int i = 1; i < argc; i++)
  {
    if (*argv[i] == '-')
    {
      /* option */
      if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0 ||
          strcmp(argv[i], "-?") == 0 || strcmp(argv[i], "/?") == 0)
      {
        std::cout << "Usage: " << argv[0] << " [-h] [--help] [-s seed] [-n samples] families ...\n";
        exit(1);
      }
      else if (strcmp(argv[i], "-s") == 0)
        r.seed = strtoul(argv[++i], NULL, 10);
      else if (strcmp(argv[i], "-n") == 0)
      {
        r.samples = strtoul(argv[++i], NULL, 10);
        if (r.samples == 0)
        {
          std::cout << "Error: need more than 0 samples.\n";
          exit(1);
        }
      }
    }
    else
      arg_fams.push_back(argv[i]);
  }

  if (arg_fams.empty())
  {
    // Add default queue of benchmarks
    r.families_to_run.push_back("hash");
    r.families_to_run.push_back("aead");
    r.families_to_run.push_back("curve25519");
    r.families_to_run.push_back("ed25519");
    r.families_to_run.push_back("merkle");
    r.families_to_run.push_back("cipher");
    r.families_to_run.push_back("mac");
  }
  else
  {
    if (std::find(arg_fams.begin(), arg_fams.end(), "hash") != arg_fams.end())
    {
      arg_fams.remove("md5");
      arg_fams.remove("sha1");
      arg_fams.remove("sha2");
      arg_fams.remove("sha2_224");
      arg_fams.remove("sha2_256");
      arg_fams.remove("sha2_384");
      arg_fams.remove("sha2_512");
    }

    for (std::string a : arg_fams)
      r.families_to_run.push_back(a);
  }

  return r;
}

#define ADD_BENCH(X) if (b == #X) { bench_##X(s); continue; }

int main(int argc, char const **argv)
{
  try
  {
    Benchmark::initialize();
    BenchmarkSettings & s = parse_args(argc, argv);

    std::cout << "Config: " << Benchmark::get_runtime_config() << "\n";

    while (!s.families_to_run.empty())
    {
      std::string b = s.families_to_run.front();
      s.families_to_run.pop_front();

      ADD_BENCH(md5);
      ADD_BENCH(sha1);
      ADD_BENCH(sha2);
      ADD_BENCH(sha3);
      ADD_BENCH(hash);

      ADD_BENCH(aead);

      ADD_BENCH(curve25519);

      ADD_BENCH(ed25519);

      ADD_BENCH(merkle);

      ADD_BENCH(cipher);
      ADD_BENCH(mac);

      std::cout << "Unsupported benchmark '" << b << "'.\n";
    }

    // CRYPTO_cleanup_all_ex_data();

    return 0;
  }
  catch (const std::exception & ex)
  {
    std::cout << "Exception: " << ex.what() << "\n";
  }
  catch (...)
  {
    std::cout << "Exception: caught unknown exception" << "\n";
  }

  return 1;
}