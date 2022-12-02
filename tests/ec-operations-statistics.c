#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

/**
   All the computations are done for the fixed-window method.
*/

#define scalar_unsigned 0
#define scalar_signed 1
#define scalar_wnaf 2

typedef uint8_t scalar_representation;

static inline bool is_unsigned(scalar_representation sr) {
  switch (sr) {
  case scalar_unsigned: {
    return true;
  }
  case scalar_signed: {
    return false;
  }
  case scalar_wnaf: {
    return false;
  }
  }
}

static inline char *str_scalar_repr(scalar_representation sr) {
  switch (sr) {
  case scalar_unsigned: {
    return "[unsigned]";
  }
  case scalar_signed: {
    return "[signed]";
  }
  case scalar_wnaf: {
    return "[wNAF]";
  }
  }
}

//-------------------------------------------

static inline void print_end_line(bool is_print) {
  if (is_print) {
    printf("-----------------------------------------------------------\n");
  }
}

static inline void print_header_for_number_of_ops(bool is_print,
                                                  bool is_ec_ops) {
  if (is_print) {
    print_end_line(true);
    char *mul_str = is_ec_ops ? "#point_add" : "#fmul";
    char *sqr_str = is_ec_ops ? "#point_double" : "#fsqr";
    char *mul_appr_str = is_ec_ops ? "~#point_add" : "~#fmul";

    printf("%-5s %-5s %-15s %-15s %-15s \n", "w", "w_g", mul_str, sqr_str,
           mul_appr_str);
    print_end_line(true);
  }
}

static inline void print_header_for_aggregated_table(bool is_ec_ops,
                                                     double ratio_ec,
                                                     double ratio_ff,
                                                     scalar_representation sr) {
  printf("\n\n");
  char *mul_str = is_ec_ops ? "point_add" : "fmul";
  char *sqr_str = is_ec_ops ? "point_double" : "fsqr";
  double ratio = is_ec_ops ? ratio_ec : ratio_ff;
  char *repr_str = str_scalar_repr(sr);

  printf("%s Aggregated table with ~#%s, where %s = %5.2f * %s \n", repr_str,
         mul_str, sqr_str, ratio, mul_str);
  print_end_line(true);
}

typedef struct {
  uint32_t padd_fmul;
  uint32_t padd_fsqr;
  uint32_t pdouble_fmul;
  uint32_t pdouble_fsqr;
  // ?todo: uint32_t pmixed_fmul;
  // ?todo: uint32_t pmixed_fsqr;
  double ratio_ff;
  double ratio_ec;
} cost_of_ec_ops;

typedef struct {
  uint32_t l;
  uint32_t l_g;
  bool is_precomp_g_const;
  scalar_representation scalar_repr;
} table_precomp_params;

typedef struct {
  uint32_t precomp_add;
  uint32_t precomp_double;
} number_of_ec_ops_table;

typedef struct {
  uint32_t main_add;
  uint32_t main_double;
  uint32_t rem_add;
  uint32_t extra_fmul; // needed for GLV when multiplying X coordinate by beta
  // ?todo: uint32_t main_mixed;
  // ?todo: uint32_t rem_mixed;
} number_of_ec_ops_main;

typedef struct {
  number_of_ec_ops_table precomp;
  number_of_ec_ops_main loop;
} number_of_ec_ops;

typedef struct {
  uint32_t total_add;
  uint32_t total_double;
  double total_appr_ec;
  uint32_t total_fmul;
  uint32_t total_fsqr;
  double total_appr_ff;
} total_number_of_ops;

typedef struct {
  bool is_print;
  bool is_print_precomp_g_large; // a large static precomputed table for a
                                 // base point G: [default] (w = w_g),
                                 // [large_precomp_g] (w <> w_g)
  bool is_ec_ops;                // print a total number of EC or FF operations
  bool is_glv; // [fw] for 1 ECSM, [double_fw] for 2 ECSM, [glv] for 4 ECSM
  scalar_representation scalar_repr; // [unsigned], [signed], [wnaf]
  // a static precomputed table for a base point G: [default], [precomp_g]
} print_total_number_of_ops;

static inline total_number_of_ops
print_number_of_point_ops(bool is_print, bool is_ec_ops, cost_of_ec_ops cs,
                          table_precomp_params tp, number_of_ec_ops ks) {

  uint32_t total_add =
      ks.precomp.precomp_add + ks.loop.main_add + ks.loop.rem_add;
  uint32_t total_double = ks.precomp.precomp_double + ks.loop.main_double;
  double total_appr_ec = total_add + total_double * cs.ratio_ec;

  uint32_t total_fmul = total_add * cs.padd_fmul +
                        total_double * cs.pdouble_fmul + ks.loop.extra_fmul;
  uint32_t total_fsqr =
      total_add * cs.padd_fsqr + total_double * cs.pdouble_fsqr;
  double total_appr_ff = total_fmul + total_fsqr * cs.ratio_ff;

  if (is_print) {
    uint32_t total_mul = is_ec_ops ? total_add : total_fmul;
    uint32_t total_sqr = is_ec_ops ? total_double : total_fsqr;
    double total_appr = is_ec_ops ? total_appr_ec : total_appr_ff;

    printf("%-5d %-5d %-15d %-15d %-15.2f \n", tp.l, tp.l_g, total_mul,
           total_sqr, total_appr);
  }

  total_number_of_ops res;
  res.total_add = total_add;
  res.total_double = total_double;
  res.total_fmul = total_fmul;
  res.total_fsqr = total_fsqr;
  res.total_appr_ec = total_appr_ec;
  res.total_appr_ff = total_appr_ff;
  return res;
}

/* a precomputed table for a signed representation: [0P; 1P; 2P; 3P; ..;
2^(w-1)] uint32_t table_len = (1ul << (w - 1ul)) + 1ul; table[0] =
point_at_infinity; table[1] = P; for (uint32_t i = 1; i < table_len / 2; i++) {
    table[2 * i] = table[i] + table[i];
    table[2 * i + 1] = table[2 * i] + P;
    }
  table[table_len - 1] = table[(table_len - 1) / 2] + table[(table_len - 1) / 2]

point_add_signed = point_add_unsigned / 2
point_double_signed = point_double_unsigned +/ 2 1
*/

/* a precomputed table for wNAF: [1P; 3P; 5P; 7P; ..; 2^(w-1)-1]
  uint32_t table_len = 1ul << (w - 2ul);
  tmp = 2P // 1 precomp_double
  table[0] = P
  for (uint32_t i = 1; i < table_len; i++)
    table[i] = table[i - 1] + tmp // (table_len - 1) precomp_add
*/

static inline number_of_ec_ops_table
count_number_of_ops_1_ecsm_precomp(table_precomp_params tp) {
  number_of_ec_ops_table res;
  if (tp.is_precomp_g_const) {
    res.precomp_double = 0U;
    res.precomp_add = 0U;
  } else {
    switch (tp.scalar_repr) {
    case scalar_unsigned: {
      uint32_t table_len = (1U << tp.l) - 2U;
      res.precomp_double = table_len / 2U;
      res.precomp_add = table_len / 2U;
      break;
    }
    case scalar_signed: {
      uint32_t table_len = (1U << (tp.l - 1U)) - 2U;
      res.precomp_double = table_len / 2U + 1U;
      res.precomp_add = table_len / 2U;
      break;
    }
    case scalar_wnaf: {
      uint32_t table_len = 1U << (tp.l - 2U);
      res.precomp_double = 1U;
      res.precomp_add = table_len - 1U;
      break;
    }
    }
  }
  return res;
}

static inline number_of_ec_ops_table
count_number_of_ops_2_ecsm_precomp(table_precomp_params tp) {
  number_of_ec_ops_table res;
  switch (tp.scalar_repr) {
  case scalar_unsigned: {
    uint32_t table_len = (1U << tp.l) - 2U;
    uint32_t table_len_g = (1U << tp.l_g) - 2U;
    if (tp.is_precomp_g_const) {
      res.precomp_double = table_len / 2U;
      res.precomp_add = table_len / 2U;
    } else {
      res.precomp_double = table_len / 2U + table_len_g / 2U;
      res.precomp_add = table_len / 2U + table_len_g / 2U;
    }
    break;
  }
  case scalar_signed: {
    uint32_t table_len = (1U << (tp.l - 1U)) - 2U;
    uint32_t table_len_g = (1U << (tp.l_g - 1U)) - 2U;
    if (tp.is_precomp_g_const) {
      res.precomp_double = table_len / 2U + 1U;
      res.precomp_add = table_len / 2U;
    } else {
      res.precomp_double = table_len / 2U + table_len_g / 2U + 2U;
      res.precomp_add = table_len / 2U + table_len_g / 2U;
    }
    break;
  }
  case scalar_wnaf: {
    uint32_t table_len = 1U << (tp.l - 2U);
    uint32_t table_len_g = 1U << (tp.l_g - 2U);
    if (tp.is_precomp_g_const) {
      res.precomp_double = 1U;
      res.precomp_add = table_len - 1U;
    } else {
      res.precomp_double = 2U;
      res.precomp_add = table_len + table_len_g - 2U;
    }
    break;
  }
  }
  return res;
}

static inline number_of_ec_ops_main
count_number_of_ops_1_ecsm_loop(table_precomp_params tp, uint32_t bBits) {
  number_of_ec_ops_main res;
  // init step
  res.rem_add = 0U; // we skip mul by `one`
  // main loop
  uint32_t n = bBits / tp.l;
  res.main_double = n * tp.l;
  res.main_add = n;
  res.extra_fmul = 0;
  return res;
}

static inline number_of_ec_ops_main
count_number_of_ops_2_ecsm_loop_l_eq(table_precomp_params tp, uint32_t bBits) {
  number_of_ec_ops_main res;
  // init step
  res.rem_add = (bBits % tp.l == 0U) ? 0U : 1U;
  // main loop
  uint32_t n = bBits / tp.l;
  res.main_double = n * tp.l;
  res.main_add = n + n;
  res.extra_fmul = 0;
  return res;
}

static inline number_of_ec_ops_main
count_number_of_ops_2_ecsm_loop_l_diff(table_precomp_params tp,
                                       uint32_t bBits) {
  number_of_ec_ops_main res;
  // init step
  res.rem_add = 0U;
  // main loop
  uint32_t rem_l = (bBits % tp.l == 0U) ? 0U : 1U;
  uint32_t rem_l_g = (bBits % tp.l_g == 0U) ? 0U : 1U;
  uint32_t n_l = bBits / tp.l + rem_l;
  uint32_t n_l_g = bBits / tp.l_g + rem_l_g;
  res.main_double = bBits;
  res.main_add = n_l + n_l_g;
  res.extra_fmul = 0;
  return res;
}

static inline number_of_ec_ops_main
count_number_of_ops_4_ecsm_loop_l_eq(table_precomp_params tp, uint32_t bBits) {
  number_of_ec_ops_main res;
  // init step
  res.rem_add = (bBits % tp.l == 0U) ? 0U : 3U;
  // main loop
  uint32_t n = bBits / tp.l;
  res.main_double = n * tp.l;
  res.main_add = n + n + n + n;

  uint32_t extra_fmul = (bBits % tp.l == 0U) ? 0U : 1U;
  if (tp.is_precomp_g_const) {
    res.extra_fmul = n + extra_fmul; // account for mul by beta
  } else {
    res.extra_fmul = n + extra_fmul + n + extra_fmul; // account for mul by beta
  }
  return res;
}

static inline number_of_ec_ops_main
count_number_of_ops_4_ecsm_loop_l_diff(table_precomp_params tp,
                                       uint32_t bBits) {
  number_of_ec_ops_main res;
  // init step
  res.rem_add = 0U;
  // main loop
  uint32_t rem_l = (bBits % tp.l == 0U) ? 0U : 1U;
  uint32_t rem_l_g = (bBits % tp.l_g == 0U) ? 0U : 1U;
  uint32_t n_l = bBits / tp.l + rem_l;
  uint32_t n_l_g = bBits / tp.l_g + rem_l_g;
  res.main_double = bBits;
  res.main_add = n_l + n_l + n_l_g + n_l_g;

  if (tp.is_precomp_g_const) {
    res.extra_fmul = n_l; // account for mul by beta
  } else {
    res.extra_fmul = n_l + n_l_g; // account for mul by beta
  }

  return res;
}

// 1 ECSM: [fw], [fw_precomp_g] + [wnaf]/[signed]/[unsigned]
static inline total_number_of_ops
count_number_of_ops_1_ecsm(bool is_print, bool is_ec_ops, cost_of_ec_ops cs,
                           table_precomp_params tp, uint32_t bBits) {

  bBits = is_unsigned(tp.scalar_repr) ? bBits : (bBits + 1);
  number_of_ec_ops res;
  res.precomp = count_number_of_ops_1_ecsm_precomp(tp);
  res.loop = count_number_of_ops_1_ecsm_loop(tp, bBits);
  return print_number_of_point_ops(is_print, is_ec_ops, cs, tp, res);
}

// 2 ECSM: [double_fw], [double_fw_precomp_g], [double_fw_precomp_g_large] +
// [wnaf]/[signed]/[unsigned]
static inline total_number_of_ops
count_number_of_ops_2_ecsm(bool is_print, bool is_ec_ops, cost_of_ec_ops cs,
                           table_precomp_params tp, uint32_t bBits) {

  bBits = is_unsigned(tp.scalar_repr) ? bBits : (bBits + 1);
  number_of_ec_ops res;
  res.precomp = count_number_of_ops_2_ecsm_precomp(tp);
  if (tp.l == tp.l_g) {
    res.loop = count_number_of_ops_2_ecsm_loop_l_eq(tp, bBits);
  } else {
    res.loop = count_number_of_ops_2_ecsm_loop_l_diff(tp, bBits);
  }

  return print_number_of_point_ops(is_print, is_ec_ops, cs, tp, res);
}

// 4 ECSM: [glv], [glv_precomp_g], [glv_precomp_g_large] +
// [wnaf]/[signed]/[unsigned]
static inline total_number_of_ops
count_number_of_ops_4_ecsm(bool is_print, bool is_ec_ops, cost_of_ec_ops cs,
                           table_precomp_params tp, uint32_t bBits_glv) {

  bBits_glv = is_unsigned(tp.scalar_repr) ? bBits_glv : (bBits_glv + 1);
  number_of_ec_ops res;
  res.precomp = count_number_of_ops_2_ecsm_precomp(tp);
  if (tp.l == tp.l_g) {
    res.loop = count_number_of_ops_4_ecsm_loop_l_eq(tp, bBits_glv);
  } else {
    res.loop = count_number_of_ops_4_ecsm_loop_l_diff(tp, bBits_glv);
  }

  return print_number_of_point_ops(is_print, is_ec_ops, cs, tp, res);
}

static inline total_number_of_ops
count_number_of_ops_n_ecsm(print_total_number_of_ops po, cost_of_ec_ops cs,
                           table_precomp_params tp, uint32_t bBits,
                           uint32_t n_ecsm) {

  if (n_ecsm == 1U) {
    return count_number_of_ops_1_ecsm(po.is_print, po.is_ec_ops, cs, tp, bBits);
  }

  if (n_ecsm == 2U) {
    return count_number_of_ops_2_ecsm(po.is_print, po.is_ec_ops, cs, tp, bBits);
  }

  if (n_ecsm == 4U) {
    return count_number_of_ops_4_ecsm(po.is_print, po.is_ec_ops, cs, tp, bBits);
  }

  printf("\n\n Invalid n_ecsm = %d!. Possible values are 1, 2, and 4. \n",
         n_ecsm);
}

#define N_MIN 3 // included
#define N_MAX 9 // excluded
#define N_LEN (N_MAX - N_MIN)
#define N_MAX_G 16
#define N_LEN_G (N_LEN * (N_MAX_G - N_MIN))

void print_minimum(bool is_print, double appr[N_LEN]) {
  double min = appr[0];
  int ind = 0;

  for (int i = 0; i < N_LEN; i++) {
    ind = (appr[i] < min) ? i : ind;
    min = (appr[i] < min) ? appr[i] : min;
  }

  if (is_print) {
    printf("\n Minimum is w = %d, ~#ops = %8.2f \n", N_MIN + ind, min);
  }
}

void print_minimum_l_g(bool is_print, double appr[N_LEN_G]) {
  uint32_t len = N_MAX_G - N_MIN;
  double min = appr[0];
  int ind_i = 0;
  int ind_j = 0;
  int ind = 0;

  for (int i = N_MIN; i < N_MAX; i++) {
    for (int j = i; j < N_MAX_G; j++) {
      ind = len * (i - N_MIN) + (j - N_MIN);
      ind_i = (appr[ind] < min) ? i : ind_i;
      ind_j = (appr[ind] < min) ? j : ind_j;
      min = (appr[ind] < min) ? appr[ind] : min;
    }
  }

  if (is_print) {
    printf("\n Minimum is w = %d, w_g = %d, ~#ops = %8.2f \n", ind_i, ind_j,
           min);
  }
}

void get_field_total_number_of_ops(bool is_ec_ops, bool is_diff_window_g,
                                   total_number_of_ops *no, double *res) {

  int n = is_diff_window_g ? N_LEN_G : N_LEN;
  if (is_ec_ops) {
    for (int i = 0; i < n; i++) {
      res[i] = no[i].total_appr_ec;
    }
  } else {
    for (int i = 0; i < n; i++) {
      res[i] = no[i].total_appr_ff;
    }
  }
}

void print_minimum_ec_or_ff(bool is_ec_ops, bool is_diff_window_g,
                            total_number_of_ops *res) {

  if (is_diff_window_g) {
    double appr[N_LEN_G] = {0};
    get_field_total_number_of_ops(is_ec_ops, is_diff_window_g, res, appr);
    print_minimum_l_g(true, appr);
  } else {
    double appr[N_LEN] = {0};
    get_field_total_number_of_ops(is_ec_ops, is_diff_window_g, res, appr);
    print_minimum(true, appr);
  }
}

// total_number_of_ops res[N_LEN_G]; if is_diff_window_g
// total_number_of_ops res[N_LEN]; otherwise
static inline void
print_count_number_of_ops_n_ecsm(print_total_number_of_ops po,
                                 cost_of_ec_ops cs, uint32_t bBits,
                                 bool is_precomp_g_const, bool is_diff_window_g,
                                 uint32_t n_ecsm, total_number_of_ops *res) {

  table_precomp_params tp;
  tp.is_precomp_g_const = is_precomp_g_const;
  tp.scalar_repr = po.scalar_repr;

  print_header_for_number_of_ops(po.is_print, po.is_ec_ops);

  if (is_diff_window_g) {
    uint32_t len = N_MAX_G - N_MIN;
    for (int i = N_MIN; i < N_MAX; i++) {
      for (int j = i; j < N_MAX_G; j++) {
        tp.l = i;
        tp.l_g = j;
        res[len * (i - N_MIN) + (j - N_MIN)] =
            count_number_of_ops_n_ecsm(po, cs, tp, bBits, n_ecsm);
      }
      print_end_line(po.is_print);
    }
  } else {
    for (int i = N_MIN; i < N_MAX; i++) {
      tp.l = i;
      tp.l_g = i;
      res[i - N_MIN] = count_number_of_ops_n_ecsm(po, cs, tp, bBits, n_ecsm);
    }
  }
  print_end_line(po.is_print);
  print_minimum_ec_or_ff(po.is_ec_ops, is_diff_window_g, res);
  print_end_line(po.is_print);
}

void print_statistics_glv(
    print_total_number_of_ops po, cost_of_ec_ops cs, uint32_t bBits_glv,
    total_number_of_ops res_glv[N_LEN],
    total_number_of_ops res_glv_precomp_g[N_LEN],
    total_number_of_ops res_glv_precomp_g_large[N_LEN_G]) {

  char *repr_str = str_scalar_repr(po.scalar_repr);
  bool is_precomp_g_const;
  bool is_diff_window_g;

  printf("\n[glv] %s precomp_table_g is computed in 4 ECSM \n", repr_str);
  is_precomp_g_const = false;
  is_diff_window_g = false; // ==> N_LEN
  print_count_number_of_ops_n_ecsm(po, cs, bBits_glv, is_precomp_g_const,
                                   is_diff_window_g, 4, res_glv);

  printf("\n[glv_precomp_g] %s precomp_table_g as constant in 4 ECSM \n",
         repr_str);
  is_precomp_g_const = true;
  is_diff_window_g = false; // ==> N_LEN
  print_count_number_of_ops_n_ecsm(po, cs, bBits_glv, is_precomp_g_const,
                                   is_diff_window_g, 4, res_glv_precomp_g);

  if (po.is_print_precomp_g_large) {
    printf(
        "\n[glv_precomp_g_large] %s precomp_table_g as constant in 4 ECSM \n",
        repr_str);
    is_precomp_g_const = true;
    is_diff_window_g = true; // ==> N_LEN_G
    print_count_number_of_ops_n_ecsm(po, cs, bBits_glv, is_precomp_g_const,
                                     is_diff_window_g, 4,
                                     res_glv_precomp_g_large);
  }
}

void print_statistics(print_total_number_of_ops po, cost_of_ec_ops cs,
                      uint32_t bBits, uint32_t bBits_glv) {

  char *repr_str = str_scalar_repr(po.scalar_repr);
  bool is_precomp_g_const;
  bool is_diff_window_g;

  total_number_of_ops res_main[N_LEN];
  total_number_of_ops res_precomp_g[N_LEN];
  total_number_of_ops res_precomp_g_large[N_LEN_G];

  printf("\n[double_fw] %s precomp_table_g is computed in 2 ECSM \n", repr_str);
  is_precomp_g_const = false;
  is_diff_window_g = false; // ==> N_LEN
  print_count_number_of_ops_n_ecsm(po, cs, bBits, is_precomp_g_const,
                                   is_diff_window_g, 2, res_main);

  printf("\n[precomp_g] %s precomp_table_g as constant in 2 ECSM\n", repr_str);
  is_precomp_g_const = true;
  is_diff_window_g = false; // ==> N_LEN
  print_count_number_of_ops_n_ecsm(po, cs, bBits, is_precomp_g_const,
                                   is_diff_window_g, 2, res_precomp_g);

  if (po.is_print_precomp_g_large) {
    printf("\n[precomp_g_large] %s precomp_table_g as constant in 2 ECSM\n",
           repr_str);
    is_precomp_g_const = true;
    is_diff_window_g = true; // ==> N_LEN_G
    print_count_number_of_ops_n_ecsm(po, cs, bBits, is_precomp_g_const,
                                     is_diff_window_g, 2, res_precomp_g_large);
  }

  double appr_main[N_LEN] = {0};
  double appr_precomp_g[N_LEN] = {0};
  get_field_total_number_of_ops(po.is_ec_ops, false, res_main, appr_main);
  get_field_total_number_of_ops(po.is_ec_ops, false, res_precomp_g,
                                appr_precomp_g);

  if (po.is_glv) {
    total_number_of_ops res_glv[N_LEN];
    total_number_of_ops res_glv_precomp_g[N_LEN];
    total_number_of_ops res_glv_precomp_g_large[N_LEN_G];

    print_statistics_glv(po, cs, bBits_glv, res_glv, res_glv_precomp_g,
                         res_glv_precomp_g_large);

    double appr_glv[N_LEN] = {0};
    double appr_glv_precomp_g[N_LEN] = {0};
    get_field_total_number_of_ops(po.is_ec_ops, false, res_glv, appr_glv);
    get_field_total_number_of_ops(po.is_ec_ops, false, res_glv_precomp_g,
                                  appr_glv_precomp_g);

    print_header_for_aggregated_table(po.is_ec_ops, cs.ratio_ec, cs.ratio_ff,
                                      po.scalar_repr);
    printf("%-5s %-10s %-10s %-10s %-10s \n", "w", "double_fw", "precomp_g",
           "glv", "glv_precomp_g");
    print_end_line(true);
    for (int i = N_MIN; i < N_MAX; i++) {
      printf("%-5d %-10.2f %-10.2f %-10.2f %-10.2f\n", i, appr_main[i - N_MIN],
             appr_precomp_g[i - N_MIN], appr_glv[i - N_MIN],
             appr_glv_precomp_g[i - N_MIN]);
    }
    print_end_line(true);
  } else {
    print_header_for_aggregated_table(po.is_ec_ops, cs.ratio_ec, cs.ratio_ff,
                                      po.scalar_repr);
    printf("%-5s %-10s %-15s \n", "w", "double_fw", "precomp_g");
    print_end_line(true);
    for (int i = N_MIN; i < N_MAX; i++) {
      printf("%-5d %-15.2f %-15.2f \n", i, appr_main[i - N_MIN],
             appr_precomp_g[i - N_MIN]);
    }
    print_end_line(true);
  }
}

// for 1 ECSM
void print_statistics_1(print_total_number_of_ops po, cost_of_ec_ops cs,
                        uint32_t bBits) {

  char *repr_str = str_scalar_repr(po.scalar_repr);
  bool is_precomp_g_const;
  bool is_diff_window_g = false; // 1 ECSM

  total_number_of_ops res_main[N_LEN];
  total_number_of_ops res_precomp_g[N_LEN];

  printf("\n[fw] %s precomp_table_g is computed in 1 ECSM \n", repr_str);
  is_precomp_g_const = false;
  print_count_number_of_ops_n_ecsm(po, cs, bBits, is_precomp_g_const,
                                   is_diff_window_g, 1, res_main);

  printf("\n[precomp_g] %s precomp_table_g as constant in 1 ECSM\n", repr_str);
  is_precomp_g_const = true;
  print_count_number_of_ops_n_ecsm(po, cs, bBits, is_precomp_g_const,
                                   is_diff_window_g, 1, res_precomp_g);

  double appr_main[N_LEN] = {0};
  double appr_precomp_g[N_LEN] = {0};
  get_field_total_number_of_ops(po.is_ec_ops, false, res_main, appr_main);
  get_field_total_number_of_ops(po.is_ec_ops, false, res_precomp_g,
                                appr_precomp_g);

  print_header_for_aggregated_table(po.is_ec_ops, cs.ratio_ec, cs.ratio_ff,
                                    po.scalar_repr);
  printf("%-5s %-10s %-15s \n", "w", "fw", "precomp_g");
  print_end_line(true);
  for (int i = N_MIN; i < N_MAX; i++) {
    printf("%-5d %-15.2f %-15.2f \n", i, appr_main[i - N_MIN],
           appr_precomp_g[i - N_MIN]);
  }
  print_end_line(true);
}

/*
secp256k1_point_add: 825 cycles
 secp256k1_point_double: 516 cycles
 secp256k1_fmul: 67 cycles
 secp256k1_fsqr: 58 cycles
 fsqr = 0.85 * fmul
 point_double = 0.62 * point_add

 ed25519_point_add: 462 cycles
 ed25519_point_double: 388 cycles
 ed25519_fmul: 59 cycles
 ed25519_fsqr: 49 cycles
 fsqr = 0.83 * fmul
 point_double = 0.83 * point_add
*/
int main() {
  uint32_t bBits_secp256k1 = 256U;
  uint32_t bBits_glv_secp256k1 = 128U; // w/o wNAF

  print_total_number_of_ops print_secp256k1;
  print_secp256k1.is_print = false;
  print_secp256k1.is_print_precomp_g_large = true;
  print_secp256k1.is_ec_ops = false;
  print_secp256k1.is_glv = true;
  print_secp256k1.scalar_repr = scalar_unsigned;

  cost_of_ec_ops cs_secp256k1;
  cs_secp256k1.padd_fmul = 12U;
  cs_secp256k1.padd_fsqr = 0U;
  cs_secp256k1.pdouble_fmul = 6U;
  cs_secp256k1.pdouble_fsqr = 2U;
  cs_secp256k1.ratio_ec = 0.66;
  cs_secp256k1.ratio_ff = 0.85;

  printf("\n\n[projective] secp256k1-ecdsa-verify:\n");
  // [double_fw], [double_fw_precomp_g], [double_fw_precomp_g_large]
  // [glv], [glv_precomp_g], [glv_precomp_g_large]
  print_statistics(print_secp256k1, cs_secp256k1, bBits_secp256k1,
                   bBits_glv_secp256k1);

  // we're using four_fw with four precomputed tables now
  // printf("\n\n[projective] secp256k1-ecdsa-sign:\n");
  // [fw], [fw_precomp_g]
  // print_statistics_1(print_secp256k1, cs_secp256k1, bBits_secp256k1);

  printf("\n\n");
  print_end_line(true);
  print_end_line(true);

  // TODO: account for making a precomputed table with Z = 1
  /* printf("\n\n [jacobian-mixed] secp256k1-ecdsa-verify:\n"); */
  /* cost_of_ec_ops cs_secp256k1_jac_mixed; */
  /* cs_secp256k1_jac_mixed.ratio_ff = 0.85; */
  /* cs_secp256k1_jac_mixed.ratio_ec = 0.6; // for mixed */
  /* cs_secp256k1_jac_mixed.padd_fmul = 8U; // for mixed */
  /* cs_secp256k1_jac_mixed.padd_fsqr = 3U; // for mixed */
  /* cs_secp256k1_jac_mixed.pdouble_fmul = 3U; */
  /* cs_secp256k1_jac_mixed.pdouble_fsqr = 4U; */

  /* // [double_fw], [double_fw_precomp_g], [double_fw_precomp_g_large] */
  /* // [glv], [glv_precomp_g], [glv_precomp_g_large] */
  /* print_statistics(print_secp256k1, cs_secp256k1_jac_mixed, bBits_secp256k1,
   */
  /*                  bBits_glv_secp256k1); */

  /* printf("\n\n"); */
  /* print_end_line(true); */
  /* print_end_line(true); */

  /*
  printf("\n\n [jacobian] secp256k1-ecdsa-verify:\n");
  cost_of_ec_ops cs_secp256k1_jac;
  cs_secp256k1_jac.ratio_ff = 0.85;
  cs_secp256k1_jac.ratio_ec = 0.42;
  cs_secp256k1_jac.padd_fmul = 12U;
  cs_secp256k1_jac.padd_fsqr = 4U;
  cs_secp256k1_jac.pdouble_fmul = 3U;
  cs_secp256k1_jac.pdouble_fsqr = 4U;

  // [double_fw], [double_fw_precomp_g], [double_fw_precomp_g_large]
  // [glv], [glv_precomp_g], [glv_precomp_g_large]
  print_statistics(print_secp256k1, cs_secp256k1_jac, bBits_secp256k1,
                   bBits_glv_secp256k1);
  */

  // For ed25519, it's better to set `is_ec_ops_secp256k1 = true`,
  // as we don't compare different point addition and doubling formulas
  print_total_number_of_ops print_ed25519;
  print_ed25519.is_print = false;
  print_ed25519.is_print_precomp_g_large = true;
  print_ed25519.is_ec_ops = true;
  print_ed25519.is_glv = false;
  print_ed25519.scalar_repr = scalar_unsigned;

  uint32_t bBits_ed25519 = 256U;
  uint32_t bBits_glv_ed25519 = 0U;

  cost_of_ec_ops cs_ed25519;
  cs_ed25519.padd_fmul = 9U; // 8M + 1D
  cs_ed25519.padd_fsqr = 0U;
  cs_ed25519.pdouble_fmul = 4U;
  cs_ed25519.pdouble_fsqr = 4U;
  cs_ed25519.ratio_ff = 0.83;
  cs_ed25519.ratio_ec = 0.83;

  printf("\n\nHACL ed25519-verify:\n");
  // [double_fw], [double_fw_precomp_g], [double_fw_precomp_g_large]
  print_statistics(print_ed25519, cs_ed25519, bBits_ed25519, bBits_glv_ed25519);

  // we're using four_fw with four precomputed tables now
  // printf("\n\nHACL ed25519-sign:\n");
  // [fw], [fw_precomp_g]
  // print_statistics_1(print_ed25519, cs_ed25519, bBits_ed25519);

  return EXIT_SUCCESS;
}
