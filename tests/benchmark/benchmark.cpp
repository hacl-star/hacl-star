#include <string>
#include <fstream>
#include <sstream>
#include <list>
#include <vector>
#include <algorithm>

#include <math.h>

extern "C" {
#include <EverCrypt_AutoConfig2.h>
}

#include "benchmark.h"

bool Benchmark::have_gnuplot = false;

void Benchmark::initialize()
{
  srand(0);

  Benchmark::set_runtime_config(1, 1, 1, 1, 1, 1, 1, 1, 1);

  have_gnuplot = false;
  #ifndef WIN32
    if (system("gnuplot --help > /dev/null 2>&1") == 0 &&
        system("grep --help > /dev/null 2>&1") == 0)
      have_gnuplot = true;
  #endif
}

void Benchmark::randomize(char *buf, size_t buf_sz)
{
  for (int i = 0; i < buf_sz; i++)
    buf[i] = rand() % 8;
}

Benchmark::Benchmark() {}

Benchmark::Benchmark(const std::string & name) { set_name(name); }

void Benchmark::escape(char c, std::string & str)
{
  size_t pos = str.find(c, 0);
  while (pos != std::string::npos)
  {
    str.replace(pos, 1, std::string("\\\\") + c);
    pos = str.find(c, pos + 3);
  }
}

std::string Benchmark::escape(const std::string & str)
{
  std::string r = str;
  escape('_', r);
  escape('"', r);
  return r;
}

void Benchmark::set_name(const std::string & n)
{
  name = escape(n);
}

std::string Benchmark::get_runtime_config()
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

std::string Benchmark::get_cpu_string()
{
  std::string r = "Unknown CPU.";
  #ifndef WIN32
    FILE* pipe = popen("grep \"model name\" /proc/cpuinfo -m 1", "r");
    if (pipe)
    {
      char buffer[1024];
      r = "";
      try
      {
        while (fgets(buffer, 1024, pipe) != NULL)
          r += buffer;
      }
      catch (...) {}
      pclose(pipe);
    }
  #endif

  return r;
}


std::pair<std::string, std::string> & Benchmark::get_build_config(bool escaped)
{
  static std::pair<std::string, std::string> r("", "");
  static std::pair<std::string, std::string> r_esc("", "");

  if (r.first == "" || r.second == "")
  {
    std::ifstream f("compile_commands.json");

    if (!f)
      r.first = r.second = "Unknown, no CMakeCache.txt";
    else
    {
      std::string previous, line;
      while (std::getline(f, line))
      {
        if (line.rfind("  \"file\":", 0) == 0 &&
            line.find("/EverCrypt_Error.c\"", 0) != std::string::npos)
        {
          size_t p = previous.find(":", 0);
          if (p != std::string::npos)
            r.first = std::string("EverCrypt: ") + previous.substr(p + 3, previous.length() - p - 5);
        }
        else if (line.rfind("  \"file\":", 0) == 0 &&
                 line.find("/prims.c\"", 0) != std::string::npos)
        {
          size_t p = previous.find(":", 0);
          if (p != std::string::npos)
            r.second = std::string("KreMLib: ") + previous.substr(p + 3, previous.length() - p - 5);
        }
        previous = line;
      }
    }

    r_esc.first = escape(r.first);
    r_esc.second = escape(r.second);
  }

  return escaped ? r_esc : r;
}

void Benchmark::set_runtime_config(int shaext, int aesni, int pclmulqdq, int avx, int avx2, int bmi2, int adx, int hacl, int vale)
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

void Benchmark::run(const BenchmarkSettings & s)
{
  pre(s);

  samples.reserve(s.samples);

  for (int i = 0; i < s.warmup_samples; i++)
  {
    bench_setup(s);
    bench_func();
    bench_cleanup(s);
  }

  ctotal = 0.0;
  texcl = Clock::duration::zero();

  for (int i = 0; i < s.samples; i++)
  {
    bench_setup(s);

    tbegin = Clock::now();
    cbegin = cpucycles_begin();
    bench_func();
    cend = cpucycles_end();
    tend = Clock::now();;
    cdiff = cend-cbegin;
    tdiff = tend - tbegin;
    ctotal += cdiff;
    texcl += tdiff;
    if (cdiff < cmin) cmin = cdiff;
    if (cdiff > cmax) cmax = cdiff;

    bench_cleanup(s);
    samples.push_back(cdiff);
  }

  post(s);

  std::sort(samples.begin(), samples.end());
}

void Benchmark::report(std::ostream & rs, const BenchmarkSettings & s) const
{
  double q25 = cmin, median = 0.0, q75 = cmax, avg = 0.0, stddev = 0.0;
  size_t n = samples.size();

  if (samples.size() > 4)
  {
    median = (n % 2 == 1 ? (double)samples[n/2] : (samples[n/2] + samples[(n+1)/2])/(double)2.0);
    avg = ctotal/(double)s.samples;
    q25 = (double)samples[n/4];
    q75 = (double)samples[(3*n)/4];
  }

  double sum_squares = 0.0;
  for (size_t i = 0; i < samples.size(); i++)
  {
    double q = samples[i] - avg;
    sum_squares += q*q;
  }
  stddev = sqrt(sum_squares/(double)(n-1));

  rs << "," << std::chrono::duration_cast<std::chrono::nanoseconds>(tincl).count()
    << "," << std::chrono::duration_cast<std::chrono::nanoseconds>(texcl).count()
    << "," << cmin
    << "," << q25
    << "," << avg
    << "," << median
    << "," << q75
    << "," << cmax
    << "," << stddev
    << "," << n
    << "," << (n/(std::chrono::duration_cast<std::chrono::nanoseconds>(texcl).count() / 1000000000.0));
}

static const char time_fmt[] = "%b %d %Y %H:%M:%S";

void Benchmark::run_batch(const BenchmarkSettings & s,
                          const std::string & data_header,
                          const std::string & data_filename,
                          std::list<Benchmark*> & benchmarks)
{
  char time_buf[1024];
  time_t rawtime;
  struct tm * timeinfo;
  time (&rawtime);
  timeinfo = localtime (&rawtime);
  strftime(time_buf, sizeof(time_buf), time_fmt, timeinfo);

  std::cout << "-- " << data_filename << "...\n";
  std::cout.flush();
  std::ofstream rs(data_filename, std::ios::out | std::ios::trunc);

  rs << "// Date: " << time_buf << "\n";
  rs << "// Config: " << Benchmark::get_runtime_config() << " seed=" << s.seed << " samples=" << s.samples << "\n";
  rs << "// " << Benchmark::get_build_config(false).first << "\n";
  rs << "// " << Benchmark::get_build_config(false).second << "\n";
  rs << "// " << Benchmark::get_cpu_string() << "\n";
  rs << data_header << "\n";

  while (!benchmarks.empty())
  {
    Benchmark *b = benchmarks.front();
    benchmarks.pop_front();

    b->run(s);
    b->report(rs, s);
    rs.flush();

    delete(b);
  }

  rs.close();
}

Benchmark::PlotSpec Benchmark::histogram_line(const std::string & data_filename, const std::string & title, const std::string & column, const std::string & xlabels, unsigned label_digits, bool label_rotate)
{
  std::string t = "title columnheader";
  if (title != "")
    t = "title '" + title + "'";
  return
    {
      std::make_pair(data_filename, "using '" + column + "':xticlabels(" + xlabels + ") " + t),
      std::make_pair("", "using 0:'" + column + "':xticlabels(" + xlabels + "):(sprintf(\"%0." + std::to_string(label_digits) +
                         "f\", column('" + column + "'))) with labels notitle " + (label_rotate?"rotate":"") +
                         " font \"Courier,8\"")
    };
}

void Benchmark::add_label_offsets(Benchmark::PlotSpec & ps, double label_offset_y, double scale)
{
  std::vector<double> x;
  x.resize(ps.size(), 0.0);

  if (ps.size() % 2 != 0)
    throw std::logic_error("Labels assumed at every other line.");

  switch (ps.size())
  {
  case 4: x[1] = -2.0 * scale; x[3] = +2.0 * scale; break;
  case 6: x[1] = -1.3 * scale; x[3] = +0.0; x[5] = +1.3 * scale; break;
  default: break;
  }

  for (size_t i = 1; i < ps.size(); i+=2)
  {
    ps[i].second += " offset char " + std::to_string(x[i]) + "," + std::to_string(label_offset_y);
  }
}

Benchmark::PlotSpec Benchmark::candlestick_line(const std::string & data_filename, const std::string & title, const std::string & xlabels)
{
  std::string t = "notitle";
  if (title != "")
    t = "title '" + title + "'";
  return
    {
      std::make_pair(data_filename, "using 0:'Q25':'Min':'Max':'Q75':xticlabels(" + xlabels + ") with candlesticks " + t + " whiskerbars .25"),
      // median line? // std::make_pair("", "using 0:'Med':'Med':'Med':'Med' with candlesticks lt -1 notitle")
    };
}

void make_plot_labels(std::ofstream & of, const BenchmarkSettings & s)
{
  of << "set label \"Date: \".strftime(\"" << time_fmt << "\", time(0)) at character .5, 1.1 font \"Courier,8\"\n";
  of << "set label \"Config: " << Benchmark::get_runtime_config() << " SEED=" << s.seed << " SAMPLES=" << s.samples << "\" at character .5, .65 font \"Courier,8\"\n";
  of << "set label \"" << Benchmark::get_build_config(true).first << "\" at character .5, .25 font \"Courier,1\"\n";
  of << "set label \"" << Benchmark::get_build_config(true).second << "\" at character .5, .35 font \"Courier,1\"\n";
}

void Benchmark::make_plot(const BenchmarkSettings & s,
                          const std::string & terminal,
                          const std::string & title,
                          const std::string & xtitle,
                          const std::string & ytitle,
                          const PlotSpec & plot_specs,
                          const std::string & plot_filename,
                          const std::string & plot_extras,
                          const std::vector<std::string> & sub_histo_titles,
                          size_t num_in_sub_histo,
                          bool add_key)
{
  int sub_histo = 0;
  std::vector<std::string>::const_iterator next_sht = sub_histo_titles.begin();
  std::string gnuplot_filename = plot_filename;
  gnuplot_filename.replace(plot_filename.length()-3, 3, "plt");
  std::cout << "-- " << gnuplot_filename << "...\n";
  std::cout.flush();

  std::ofstream of(gnuplot_filename, std::ios::out | std::ios::trunc);
  of << "set terminal " << terminal << "\n";
  of << "set title \"" << escape(title) << "\"\n";
  make_plot_labels(of, s);
  of << GNUPLOT_GLOBALS << "\n";
  of << "set key " << (add_key?"on":"off") << "\n";
  if (xtitle != "") of << "set xlabel \"" << xtitle << "\"" << "\n";
  if (ytitle != "") of << "set ylabel \"" << ytitle << "\"" << "\n";
  of << "set output '"<< plot_filename << "'" << "\n";
  of << plot_extras << "\n";
  of << "plot \\\n";
  for (size_t i = 0; i < plot_specs.size(); i++)
  {
    if (i != 0) of << ", \\\n";
    if (num_in_sub_histo != 0 && i % num_in_sub_histo == 0)
      of << "newhistogram '" << *next_sht++ << "' at " << sub_histo++ << ", \\\n";
    of << "'" << plot_specs[i].first << "' " << plot_specs[i].second;
  }
  of.close();

  if (have_gnuplot)
  {
    std::cout << "-- " << plot_filename << "...\n";
    std::cout.flush();
    int r = system((std::string("gnuplot ") + gnuplot_filename).c_str());
    if (r != 0)
      throw std::logic_error("Plot generation failed");
  }
}
