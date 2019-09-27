#include <sys/time.h>

#include <sstream>
#include <algorithm>

#include <benchmark.h>

extern "C" {
#include "MerkleTree.h"
}

class MerkleInsert : public Benchmark
{
  protected:
    size_t num_nodes = 0;
    merkle_tree *tree;
    std::vector<uint8_t*> hashes;

  public:
    static std::string column_headers() { return "\"Nodes\"" + Benchmark::column_headers(); }

    MerkleInsert(size_t num_nodes) : Benchmark(), num_nodes(num_nodes) { }

    virtual ~MerkleInsert() {}

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Benchmark::bench_setup(s);
      uint8_t *ih = init_hash();
      tree = mt_create(ih);
      free_hash(ih);

      hashes.resize(num_nodes, NULL);
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        hashes[i] = init_hash();
        for (size_t j = 0; j < 8; j++)
           *(hashes[i] + j) = rand() % 8;
      }
    }

    virtual void bench_func()
    {
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        #ifdef _DEBUG
        if (!mt_insert_pre(tree, hashes[i]))
          throw std::logic_error("precondition violation");
        #endif
        mt_insert(tree, hashes[i]);
      }

    }

    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      for (uint64_t i = 0; i < num_nodes; i++)
        free_hash(hashes[i]);
      mt_free(tree);
      Benchmark::bench_cleanup(s);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << num_nodes;
      Benchmark::report(rs, s);
      rs << "\n";
    }
};

class MerklePathExtraction : public Benchmark
{
  protected:
    size_t num_nodes = 0;
    merkle_tree *tree;
    std::vector<uint8_t*> hashes;
    std::vector<hash_vec*> paths;
    std::vector<uint8_t*> roots;

  public:
    static std::string column_headers() { return "\"Nodes\"" + Benchmark::column_headers(); }

    MerklePathExtraction(size_t num_nodes) : Benchmark(), num_nodes(num_nodes) { }

    virtual ~MerklePathExtraction() {}

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Benchmark::bench_setup(s);
      uint8_t *ih = init_hash();
      tree = mt_create(ih);
      free_hash(ih);

      hashes.resize(num_nodes, NULL);
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        uint8_t *hash = init_hash();
        hashes[i] = init_hash();
        for (size_t j = 0; j < 8; j++)
           *(hashes[i] + j) = rand() % 8;
        #ifdef _DEBUG
        if (!mt_insert_pre(tree, hashes[i]))
          throw std::logic_error("precondition violation");
        #endif
        mt_insert(tree, hash);
      }

      paths.resize(num_nodes);
      roots.resize(num_nodes);
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        roots[i] = init_hash();
        paths[i] = init_path();
      }
    }

    virtual void bench_func()
    {
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        #ifdef _DEBUG
        if (!mt_get_path_pre(tree, i, paths[i], roots[i]))
          throw std::logic_error("precondition violation");
        #endif
        mt_get_path(tree, i, paths[i], roots[i]);
      }
    }

    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        clear_path(paths[i]);
        free_path(paths[i]);
        free_hash(roots[i]);
        free_hash(hashes[i]);
      }
      mt_free(tree);
      Benchmark::bench_cleanup(s);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << num_nodes;
      Benchmark::report(rs, s);
      rs << "\n";
    }
};

class MerklePathVerification : public Benchmark
{
  protected:
    size_t num_nodes = 0;
    merkle_tree *tree;
    std::vector<uint8_t*> hashes;
    std::vector<hash_vec*> paths;
    std::vector<uint8_t*> roots;
    std::vector<uint32_t> js;

  public:
    static std::string column_headers() { return "\"Nodes\"" + Benchmark::column_headers(); }

    MerklePathVerification(size_t num_nodes) : Benchmark(), num_nodes(num_nodes) { }

    virtual ~MerklePathVerification() {}

    virtual void bench_setup(const BenchmarkSettings & s)
    {
      Benchmark::bench_setup(s);
      uint8_t *ih = init_hash();
      tree = mt_create(ih);
      free_hash(ih);

      hashes.resize(num_nodes, NULL);
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        uint8_t *hash = init_hash();
        hashes[i] = init_hash();
        for (size_t j = 0; j < 8; j++)
           *(hashes[i] + j) = rand() % 8;
        #ifdef _DEBUG
        if (!mt_insert_pre(tree, hashes[i]))
          throw std::logic_error("precondition violation");
        #endif
        mt_insert(tree, hash);
      }

      paths.resize(num_nodes);
      roots.resize(num_nodes);
      js.resize(num_nodes);
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        roots[i] = init_hash();
        paths[i] = init_path();

        #ifdef _DEBUG
        if (!mt_get_path_pre(tree, i, paths[i], roots[i]))
          throw std::logic_error("precondition violation");
        #endif
        js[i] = mt_get_path(tree, i, paths[i], roots[i]);
      }
    }

    virtual void bench_func()
    {
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        #ifdef _DEBUG
        if (!mt_verify(tree, i, js[i], paths[i], roots[i]))
          throw std::logic_error("precondition violation");
        bool ok =
        #endif
          mt_verify(tree, i, js[i], paths[i], roots[i]);
        #ifdef _DEBUG
        if (!ok)
          throw std::logic_error("postcondition violation");
        #endif
      }
    }

    virtual void bench_cleanup(const BenchmarkSettings & s)
    {
      for (uint64_t i = 0; i < num_nodes; i++)
      {
        clear_path(paths[i]);
        free_path(paths[i]);
        free_hash(roots[i]);
        free_hash(hashes[i]);
      }
      mt_free(tree);
      Benchmark::bench_cleanup(s);
    }

    virtual void report(std::ostream & rs, const BenchmarkSettings & s) const
    {
      rs << num_nodes;
      Benchmark::report(rs, s);
      rs << "\n";
    }
};

void bench_merkle_insert(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576 };
  std::string data_filename = "bench_merkle_insert.csv";

  std::list<Benchmark*> todo;
  for (size_t ds: data_sizes)
    todo.push_back(new MerkleInsert(ds));

  Benchmark::run_batch(s, MerkleInsert::column_headers(), data_filename, todo);

  std::stringstream extras;
  extras << "set boxwidth 0.8\n";
  extras << "set key off\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                  "svg",
                  "Merkle tree insertion performance",
                  "# tree nodes",
                  "Avg. performance [CPU cycles/insertion]",
                  Benchmark::histogram_line(data_filename, "", "Avg", "strcol('Nodes')", 0),
                  "bench_merkle_insert_cycles.svg",
                  extras.str());

  std::string X = "((" + std::to_string(s.samples) + " * column('Nodes'))/(column('CPUexcl')/1000000000))";
  std::string lbls = "sprintf(\"%dk\", column('Nodes')/1024)";
  Benchmark::PlotSpec plot_specs_timed = {
    std::make_pair(data_filename, "using " + X + ":xticlabels(" + lbls + ") with boxes"),
    std::make_pair("", "using 0:" + X + ":xticlabels(" + lbls + "):(sprintf(\"%0.0f\", " + X + ")) with labels font \"Courier,8\" offset char 0,.5 center notitle"),
  };

  Benchmark::make_plot(s,
                  "svg",
                  "Merkle tree insertion performance",
                  "# tree nodes",
                  "Avg. performance [insertion/sec]",
                  plot_specs_timed,
                  "bench_merkle_insert_timed.svg",
                  extras.str());
}

void bench_merkle_get_path(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576 };
  std::string data_filename = "bench_merkle_get_path.csv";

  std::list<Benchmark*> todo;
  for (size_t ds: data_sizes)
    todo.push_back(new MerklePathExtraction(ds));

  Benchmark::run_batch(s, MerklePathExtraction::column_headers(), data_filename, todo);

  std::stringstream extras;
  extras << "set boxwidth 0.8\n";
  extras << "set key off\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                  "svg",
                  "Merkle tree path extraction performance",
                  "# tree nodes",
                  "Avg. performance [CPU cycles/path]",
                  Benchmark::histogram_line(data_filename, "", "Avg", "strcol('Nodes')", 0),
                  "bench_merkle_get_path_cycles.svg",
                  extras.str());

  std::string X = "((" + std::to_string(s.samples) + " * column('Nodes'))/(column('CPUexcl')/1000000000))";
  std::string lbls = "sprintf(\"%dk\", column('Nodes')/1024)";
  Benchmark::PlotSpec plot_specs_timed = {
    std::make_pair(data_filename, "using " + X + ":xticlabels(" + lbls + ") with boxes"),
    std::make_pair("", "using 0:" + X + ":xticlabels(" + lbls + "):(sprintf(\"%0.0f\", " + X + ")) with labels font \"Courier,8\" offset char 0,.5 center notitle"),
  };

  Benchmark::make_plot(s,
                  "svg",
                  "Merkle tree path extraction performance",
                  "# tree nodes",
                  "Avg. performance [paths/sec]",
                  plot_specs_timed,
                  "bench_merkle_get_path_timed.svg",
                  extras.str());
}

void bench_merkle_verify(const BenchmarkSettings & s)
{
  size_t data_sizes[] = { 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576 };
  std::string data_filename = "bench_merkle_verify.csv";

  std::list<Benchmark*> todo;
  for (size_t ds: data_sizes)
    todo.push_back(new MerklePathVerification(ds));

  Benchmark::run_batch(s, MerklePathVerification::column_headers(), data_filename, todo);

  std::stringstream extras;
  extras << "set boxwidth 0.8\n";
  extras << "set key off\n";
  extras << "set style histogram clustered gap 3 title\n";
  extras << "set style data histograms\n";
  extras << "set bmargin 5\n";

  Benchmark::make_plot(s,
                  "svg",
                  "Merkle tree path verification performance",
                  "# tree nodes",
                  "Avg. performance [CPU cycles/verification]",
                  Benchmark::histogram_line(data_filename, "", "Avg", "strcol('Nodes')", 0),
                  "bench_merkle_verify_cycles.svg",
                  extras.str());

  std::string X = "((" + std::to_string(s.samples) + " * column('Nodes'))/(column('CPUexcl')/1000000000))";
  std::string lbls = "sprintf(\"%dk\", column('Nodes')/1024)";
  Benchmark::PlotSpec plot_specs_timed = {
    std::make_pair(data_filename, "using " + X + ":xticlabels(" + lbls + ") with boxes"),
    std::make_pair("", "using 0:" + X + ":xticlabels(" + lbls + "):(sprintf(\"%0.0f\", " + X + ")) with labels font \"Courier,8\" offset char 0,.5 center notitle"),
  };

  Benchmark::make_plot(s,
                  "svg",
                  "Merkle tree path verification performance",
                  "# tree nodes",
                  "Avg. performance [paths/sec]",
                  plot_specs_timed,
                  "bench_merkle_verify_timed.svg",
                  extras.str());
}

void bench_merkle(const BenchmarkSettings & s)
{
  // These amortize over a number of tree nodes, so shouldn't need many samples.
  BenchmarkSettings s_local = s;
  s_local.samples = std::max<size_t>(s.samples / 1000, 1ul);
  s_local.warmup_samples = 0;

  bench_merkle_insert(s_local);
  bench_merkle_get_path(s_local);
  bench_merkle_verify(s_local);
}