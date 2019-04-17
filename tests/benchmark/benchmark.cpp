#include <string>
#include <fstream>
#include <sstream>

extern "C" {
#include <EverCrypt_AutoConfig2.h>
}

#include "benchmark.h"
#include "benchmark_plot_templates.h"

void b_init()
{
  srand(0);
}

extern void b_randomize(char *buf, size_t buf_sz)
{
  for (int i = 0; i < buf_sz; i++)
    buf[i] = rand() % 8;
}

Benchmark::Benchmark() : seed(0), samples(1) {}

Benchmark::Benchmark(std::string & name) : seed(0), samples(1) { set_name(name); }

void Benchmark::set_name(const std::string & n)
{
  name = n;
  size_t pos = name.find('_', 0);
  while (pos != std::string::npos)
  {
    name.replace(pos, 1, "\\_");
    pos = name.find('_', pos + 2);
  }
}

std::string Benchmark::get_config()
{
  std::stringstream rs;
  rs <<        (EverCrypt_AutoConfig2_has_shaext() ? "+" : "-") << "SHAEXT";
  rs << " " << (EverCrypt_AutoConfig2_has_aesni() ? "+" : "-") << "AESNI";
  rs << " " << (EverCrypt_AutoConfig2_has_pclmulqdq() ? "+" : "-") << "PCLMULQDQ";
  rs << " " << (EverCrypt_AutoConfig2_has_avx() ? "+" : "-") << "AVX";
  rs << " " << (EverCrypt_AutoConfig2_has_avx2() ? "+" : "-") << "AVX2";
  rs << " " << (EverCrypt_AutoConfig2_has_bmi2() ? "+" : "-") << "BMI2";
  rs << " " << (EverCrypt_AutoConfig2_has_adx() ? "+" : "-") << "ADX";
  rs << " " << (EverCrypt_AutoConfig2_wants_hacl() ? "+" : "-") << "HACL";
  rs << " " << (EverCrypt_AutoConfig2_wants_vale() ? "+" : "-") << "VALE";
  return rs.str();
}

void Benchmark::set_config(int shaext, int aesni, int pclmulqdq, int avx, int avx2, int bmi2, int adx, int hacl, int vale)
{
  EverCrypt_AutoConfig2_init();
  if (shaext == 0) EverCrypt_AutoConfig2_disable_shaext();
  if (aesni == 0) EverCrypt_AutoConfig2_disable_aesni();
  if (pclmulqdq == 0) EverCrypt_AutoConfig2_disable_pclmulqdq();
  if (avx == 0) EverCrypt_AutoConfig2_disable_avx();
  if (avx2 == 0) EverCrypt_AutoConfig2_disable_avx2();

  // No way to disable these?
  // if (bmi2 == 0) EverCrypt_AutoConfig2_disable_bmi2();
  // if (adx == 0) EverCrypt_AutoConfig2_disable_adx();

  if (hacl == 0) EverCrypt_AutoConfig2_disable_hacl();
  if (vale == 0) EverCrypt_AutoConfig2_disable_vale();
}

static const char time_fmt[] = "%b %d %Y %H:%M:%S";

void b_run(unsigned int seed,
           size_t samples,
           const std::string & data_header,
           const std::string & data_filename,
           std::set<Benchmark*> & benchmarks)
{
  char time_buf[1024];
  time_t rawtime;
  struct tm * timeinfo;
  time (&rawtime);
  timeinfo = localtime (&rawtime);
  strftime(time_buf, sizeof(time_buf), time_fmt, timeinfo);

  std::cout << "-- " << data_filename << "...\n";
  std::ofstream rs(data_filename, std::ios::out | std::ios::trunc);

  rs << "// Config: " << Benchmark::get_config() << " seed=" << seed << "\n";
  rs << "// Date: " << "\n";
  rs << data_header << "\n";

  while (!benchmarks.empty())
  {
    auto fst = benchmarks.begin();
    Benchmark *b = *fst;
    benchmarks.erase(fst);

    b->set_seed(seed);
    b->set_samples(samples);
    b->run();
    b->report(rs);
    rs.flush();

    delete(b);
  }

  rs.close();
  benchmarks.clear();
}

extern void b_make_plot(unsigned int seed,
                        size_t samples,
                        const std::string & build_config,
                        const std::string & terminal,
                        const std::string & title,
                        const std::string & units,
                        const std::string & data_filename,
                        const std::string & plot_filename,
                        const std::string & plot_extras,
                        const std::string & plot_spec,
                        bool add_key)
{
  std::string gnuplot_filename = plot_filename;
  gnuplot_filename.replace(plot_filename.length()-3, 3, "plt");
  std::cout << "-- " << gnuplot_filename << "...\n";

  std::ofstream of(gnuplot_filename, std::ios::out | std::ios::trunc);
  of << "set terminal " << terminal << "\n";
  of << "set title \"" << title << "\"\n";
  of << "set label \"Date: \".strftime(\"" << time_fmt << "\", time(0)) at character .5, 1.5 font \"Courier,8\"\n";
  of << "set label \"Runtime config: " << Benchmark::get_config() << " SEED=" << seed << " SAMPLES=" << samples << "\" at character .5, 1.0 font \"Courier,8\"\n";
  of << "set label \"Build config: " << build_config << "\" at character .5, .5 font \"Courier,8\"\n";
  of << GNUPLOT_GLOBALS << "\n";
  of << "set key " << (add_key?"on":"off") << "\n";
  of << "set ylabel \"" << units << "\"" << "\n";
  of << "set output '"<< plot_filename << "'" << "\n";
  of << plot_extras << "\n";
  of << "plot '" << data_filename << "' " << plot_spec << "\n";
  of.close();

  std::cout << "-- " << plot_filename << "...\n";
  system((std::string("gnuplot ") + gnuplot_filename).c_str());
}
