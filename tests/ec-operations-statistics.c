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

// TODO: add the cost of `point_add` and `point double` in `fmul` and `fsqr`
// to compare formulas given in
// - projective coordinates
// - jacobian coordinates
// - mixed coordinates
// TODO: account for wNAF
// - it changes #point_add and _double for a precomputed table
static inline void print_end_line(bool is_print) {
  if (is_print) {
    printf("-----------------------------------------------------------\n");
  }
}

static inline void print_header_for_number_of_ops(bool is_print,
                                                  bool is_ec_ops) {
  if (is_print) {
    print_end_line(true);
    if (is_ec_ops) {
      printf("%-5s %-5s %-15s %-15s %-15s \n", "w", "w_g", "#point_add",
             "#point_double", "~#point_add");
    } else {
      printf("%-5s %-5s %-15s %-15s %-15s \n", "w", "w_g", "#fmul", "#fsqr",
             "~#fmul");
    }
    print_end_line(true);
  }
}

static inline void print_header_for_aggregated_table(bool is_ec_ops,
                                                     uint32_t ratio_ec,
                                                     uint32_t ratio_ff) {
  printf("\n\n");
  if (is_ec_ops) {
    printf("Aggregated table with ~#point_add, where point_double = %d / 5 * "
           "point_add \n",
           ratio_ec);
  } else {
    printf("Aggregated table with ~#fmul, where fsqr = %d / 5 * fmul \n",
           ratio_ff);
  }
  print_end_line(true);
}

typedef struct {
  uint32_t padd_fmul;
  uint32_t padd_fsqr;
  uint32_t pdouble_fmul;
  uint32_t pdouble_fsqr;
  // todo: uint32_t pmixed_fmul;
  // todo: uint32_t pmixed_fsqr;
} cost_of_ec_ops;

typedef struct {
  uint32_t precomp_add;
  uint32_t precomp_double;
  uint32_t main_add;
  uint32_t main_double;
  uint32_t rem_add;
  // todo: uint32_t main_mixed;
  // todo: uint32_t rem_mixed;
  // todo: uint32_t extra_fmul; e.g., for GLV or precomp
  // todo: uint32_t extra_fsqr; e.g., for GLV or precomp
} number_of_ec_ops;

typedef struct {
  uint32_t l;
  uint32_t l_g;
  bool is_precomp_g_const;
  // todo: bool is_wnaf;
} table_precomp_params;

static inline uint32_t
print_number_of_point_ops(bool is_print, bool is_ec_ops, uint32_t ratio_ec,
                          uint32_t ratio_ff, cost_of_ec_ops cs,
                          table_precomp_params tp, number_of_ec_ops ks) {

  uint32_t total_add = ks.precomp_add + ks.main_add + ks.rem_add;
  uint32_t total_double = ks.precomp_double + ks.main_double;
  uint32_t total_appr_ec = total_add + (total_double * ratio_ec / 5U);

  uint32_t total_fmul =
      total_add * cs.padd_fmul + total_double * cs.pdouble_fmul;
  uint32_t total_fsqr =
      total_add * cs.padd_fsqr + total_double * cs.pdouble_fsqr;
  uint32_t total_appr_ff = total_fmul + (total_fsqr * ratio_ff / 5U);

  uint32_t res = is_ec_ops ? total_appr_ec : total_appr_ff;

  if (is_print) {
    if (is_ec_ops) {
      printf("%-5d %-5d %-15d %-15d %-15d \n", tp.l, tp.l_g, total_add,
             total_double, total_appr_ec);
    } else {
      printf("%-5d %-5d %-15d %-15d %-15d \n", tp.l, tp.l_g, total_fmul,
             total_fsqr, total_appr_ff);
    }
  }
  return res;
}

// 1 ECSM: [main], [precomp_g]
uint32_t count_number_of_ops_1_ecsm(bool is_print, bool is_ec_ops,
                                    uint32_t ratio_ec, uint32_t ratio_ff,
                                    cost_of_ec_ops cs, table_precomp_params tp,
                                    uint32_t bBits) {
  number_of_ec_ops res;
  if (tp.is_precomp_g_const) {
    res.precomp_double = 0U;
    res.precomp_add = 0U;
  } else {
    uint32_t table_len = (1U << tp.l) - 2U;
    res.precomp_double = table_len / 2U;
    res.precomp_add = table_len / 2U;
  }
  // init step
  res.rem_add = 0U; // we skip mul by `one`
  // main loop
  uint32_t n = bBits / tp.l;
  res.main_double = n * tp.l;
  res.main_add = n;

  return print_number_of_point_ops(is_print, is_ec_ops, ratio_ec, ratio_ff, cs,
                                   tp, res);
}

// 2 ECSM: [main], [precomp_g], [precomp_g_large]
uint32_t count_number_of_ops_2_ecsm(bool is_print, bool is_ec_ops,
                                    uint32_t ratio_ec, uint32_t ratio_ff,
                                    cost_of_ec_ops cs, table_precomp_params tp,
                                    uint32_t bBits) {

  number_of_ec_ops res;
  uint32_t table_len = (1U << tp.l) - 2U;
  uint32_t table_len_g = (1U << tp.l_g) - 2U;
  if (tp.is_precomp_g_const) {
    res.precomp_double = table_len / 2U;
    res.precomp_add = table_len / 2U;
  } else {
    res.precomp_double = table_len / 2U + table_len_g / 2U;
    res.precomp_add = table_len / 2U + table_len_g / 2U;
  }
  // init step
  uint32_t rem_l = bBits % tp.l;
  uint32_t rem_l_g = bBits % tp.l_g;
  res.rem_add = (rem_l != 0U && rem_l_g != 0U) ? 1U : 0U;
  // main loop
  uint32_t min_rem = (rem_l < rem_l_g) ? rem_l : rem_l_g;
  res.main_double = bBits - min_rem;
  res.main_add = bBits / tp.l + bBits / tp.l_g;

  return print_number_of_point_ops(is_print, is_ec_ops, ratio_ec, ratio_ff, cs,
                                   tp, res);
}

// 4ECSM: [glv], [glv_precomp_g], [glv_precomp_g_large]
uint32_t count_number_of_ops_4_ecsm(bool is_print, bool is_ec_ops,
                                    uint32_t ratio_ec, uint32_t ratio_ff,
                                    cost_of_ec_ops cs, table_precomp_params tp,
                                    uint32_t bBits_glv) {

  number_of_ec_ops res;
  uint32_t table_len = (1U << tp.l) - 2U;
  uint32_t table_len_g = (1U << tp.l_g) - 2U;
  if (tp.is_precomp_g_const) {
    res.precomp_double = table_len / 2U;
    res.precomp_add = table_len / 2U;
  } else {
    res.precomp_double = table_len / 2U + table_len_g / 2U;
    res.precomp_add = table_len / 2U + table_len_g / 2U;
  }
  // init step
  uint32_t rem_l = bBits_glv % tp.l;
  uint32_t rem_l_g = bBits_glv % tp.l_g;
  res.rem_add = (rem_l == 0U && rem_l_g == 0U)
                    ? 0U
                    : ((rem_l != 0U && rem_l_g != 0U) ? 3U : 1U);
  // main loop
  uint32_t min_rem = (rem_l < rem_l_g) ? rem_l : rem_l_g;
  res.main_double = bBits_glv - min_rem;
  res.main_add = bBits_glv / tp.l + bBits_glv / tp.l + bBits_glv / tp.l_g +
                 bBits_glv / tp.l_g; // four scalars + acc

  // TODO: account for mul by beta = (n + n) M
  return print_number_of_point_ops(is_print, is_ec_ops, ratio_ec, ratio_ff, cs,
                                   tp, res);
}

#define N_MIN 3 // included
#define N_MAX 9 // excluded
#define N_LEN (N_MAX - N_MIN)
#define N_MAX_G 16
#define N_LEN_G (N_LEN * (N_MAX_G - N_MIN))

void print_minimum(bool is_print, uint32_t appr[N_LEN]) {
  uint32_t min = appr[0];
  int ind = 0;

  for (int i = 0; i < N_LEN; i++) {
    ind = (appr[i] < min) ? i : ind;
    min = (appr[i] < min) ? appr[i] : min;
  }

  if (is_print) {
    printf("\n Minimum is w = %d, ~#ops = %d \n", N_MIN + ind, min);
  }
}

void print_minimum_l_g(bool is_print, uint32_t appr[N_LEN_G]) {
  uint32_t len = N_MAX_G - N_MIN;
  uint32_t min = appr[0];
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
    printf("\n Minimum is w = %d, w_g = %d, ~#ops = %d \n", ind_i, ind_j, min);
  }
}

void print_statistics_glv(bool is_print, bool is_ec_ops, uint32_t ratio_ec,
                          uint32_t ratio_ff, cost_of_ec_ops cs,
                          uint32_t bBits_glv, uint32_t glv_appr[N_LEN],
                          uint32_t glv_precomp_g_appr[N_LEN]) {

  table_precomp_params tp;

  printf("\n[glv] precomp_table_g is computed in 4 ECSM \n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    tp.l = i;
    tp.l_g = i;
    tp.is_precomp_g_const = false;
    glv_appr[i - N_MIN] = count_number_of_ops_4_ecsm(
        is_print, is_ec_ops, ratio_ec, ratio_ff, cs, tp, bBits_glv);
  }
  print_end_line(is_print);
  print_minimum(true, glv_appr);
  print_end_line(is_print);

  printf("\n[glv_precomp_g] precomp_table_g as constant in 4 ECSM \n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    tp.l = i;
    tp.l_g = i;
    tp.is_precomp_g_const = true;
    glv_precomp_g_appr[i - N_MIN] = count_number_of_ops_4_ecsm(
        is_print, is_ec_ops, ratio_ec, ratio_ff, cs, tp, bBits_glv);
  }
  print_end_line(is_print);
  print_minimum(true, glv_precomp_g_appr);
  print_end_line(is_print);
}

void print_statistics(bool is_print, bool is_ec_ops, uint32_t ratio_ec,
                      uint32_t ratio_ff, cost_of_ec_ops cs, uint32_t bBits,
                      bool is_glv, uint32_t bBits_glv) {

  table_precomp_params tp;
  uint32_t main_appr[N_LEN] = {0};
  printf("\n[main] precomp_table_g is computed in 2 ECSM \n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    tp.l = i;
    tp.l_g = i;
    tp.is_precomp_g_const = false;
    main_appr[i - N_MIN] = count_number_of_ops_2_ecsm(
        is_print, is_ec_ops, ratio_ec, ratio_ff, cs, tp, bBits);
  }
  print_end_line(is_print);
  print_minimum(true, main_appr);
  print_end_line(is_print);

  uint32_t precomp_g_appr[N_LEN] = {0};
  printf("\n[precomp_g] precomp_table_g as constant in 2 ECSM\n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    tp.l = i;
    tp.l_g = i;
    tp.is_precomp_g_const = true;
    precomp_g_appr[i - N_MIN] = count_number_of_ops_2_ecsm(
        is_print, is_ec_ops, ratio_ec, ratio_ff, cs, tp, bBits);
  }
  print_end_line(is_print);
  print_minimum(true, precomp_g_appr);
  print_end_line(is_print);

  if (is_glv) {
    uint32_t glv_appr[N_LEN] = {0};
    uint32_t glv_precomp_g_appr[N_LEN] = {0};
    print_statistics_glv(is_print, is_ec_ops, ratio_ec, ratio_ff, cs, bBits_glv,
                         glv_appr, glv_precomp_g_appr);

    print_header_for_aggregated_table(is_ec_ops, ratio_ec, ratio_ff);
    printf("%-5s %-10s %-10s %-10s %-10s \n", "w", "main", "precomp_g", "glv",
           "glv_precomp_g");
    print_end_line(true);
    for (int i = N_MIN; i < N_MAX; i++) {
      printf("%-5d %-10d %-10d %-10d %-10d\n", i, main_appr[i - N_MIN],
             precomp_g_appr[i - N_MIN], glv_appr[i - N_MIN],
             glv_precomp_g_appr[i - N_MIN]);
    }
    print_end_line(true);
  } else {
    print_header_for_aggregated_table(is_ec_ops, ratio_ec, ratio_ff);
    printf("%-5s %-10s %-15s \n", "w", "main", "precomp_g");
    print_end_line(true);
    for (int i = N_MIN; i < N_MAX; i++) {
      printf("%-5d %-15d %-15d \n", i, main_appr[i - N_MIN],
             precomp_g_appr[i - N_MIN]);
    }
    print_end_line(true);
  }
}

// for 1 ECSM
void print_statistics_1(bool is_print, bool is_ec_ops, uint32_t ratio_ec,
                        uint32_t ratio_ff, cost_of_ec_ops cs, uint32_t bBits) {
  table_precomp_params tp;
  uint32_t main_appr[N_LEN] = {0};
  printf("\n[main] precomp_table_g is computed in 1 ECSM \n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    tp.l = i;
    tp.l_g = i;
    tp.is_precomp_g_const = false;
    main_appr[i - N_MIN] = count_number_of_ops_1_ecsm(
        is_print, is_ec_ops, ratio_ec, ratio_ff, cs, tp, bBits);
  }
  print_end_line(is_print);

  uint32_t precomp_g_appr[N_LEN] = {0};
  printf("\n[precomp_g] precomp_table_g as constant in 1 ECSM\n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    tp.l = i;
    tp.l_g = i;
    tp.is_precomp_g_const = true;
    precomp_g_appr[i - N_MIN] = count_number_of_ops_1_ecsm(
        is_print, is_ec_ops, ratio_ec, ratio_ff, cs, tp, bBits);
  }
  print_end_line(is_print);

  print_header_for_aggregated_table(is_ec_ops, ratio_ec, ratio_ff);
  printf("%-5s %-10s %-15s \n", "w", "main", "precomp_g");
  print_end_line(true);
  for (int i = N_MIN; i < N_MAX; i++) {
    printf("%-5d %-15d %-15d \n", i, main_appr[i - N_MIN],
           precomp_g_appr[i - N_MIN]);
  }
  print_end_line(true);
}

void print_statistics_l_g(bool is_print, bool is_ec_ops, uint32_t ratio_ec,
                          uint32_t ratio_ff, cost_of_ec_ops cs, uint32_t bBits,
                          bool is_glv, uint32_t bBits_glv) {
  table_precomp_params tp;
  uint32_t len = N_MAX_G - N_MIN;
  uint32_t precomp_g_large_appr[N_LEN_G] = {0};

  printf("\n[precomp_g_large] precomp_table_g as constant in 2 ECSM\n");

  print_header_for_number_of_ops(is_print, is_ec_ops);
  for (int i = N_MIN; i < N_MAX; i++) {
    for (int j = i; j < N_MAX_G; j++) {
      tp.l = i;
      tp.l_g = j;
      tp.is_precomp_g_const = true;
      precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)] =
          count_number_of_ops_2_ecsm(is_print, is_ec_ops, ratio_ec, ratio_ff,
                                     cs, tp, bBits);
    }
    print_end_line(is_print);
  }
  print_end_line(is_print);
  print_minimum_l_g(true, precomp_g_large_appr);
  print_end_line(is_print);

  if (is_glv) {
    uint32_t glv_precomp_g_large_appr[N_LEN_G] = {0};
    printf(
        "\n\n[glv_precomp_g_large] precomp_table_g as constant in 4 ECSM \n");

    print_header_for_number_of_ops(is_print, is_ec_ops);
    for (int i = N_MIN; i < N_MAX; i++) {
      for (int j = i; j < N_MAX_G; j++) {
        tp.l = i;
        tp.l_g = j;
        tp.is_precomp_g_const = true;
        glv_precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)] =
            count_number_of_ops_4_ecsm(is_print, is_ec_ops, ratio_ec, ratio_ff,
                                       cs, tp, bBits_glv);
      }
      print_end_line(is_print);
    }
    print_end_line(is_print);
    print_minimum_l_g(true, glv_precomp_g_large_appr);
    print_end_line(is_print);

    print_header_for_aggregated_table(is_ec_ops, ratio_ec, ratio_ff);
    printf("%-5s %-5s %-10s %-10s \n", "w", "w_g", "precomp_g_large",
           "glv_precomp_g_large");
    print_end_line(true);
    for (int i = N_MIN; i < N_MAX; i++) {
      for (int j = i; j < N_MAX_G; j++) {
        printf("%-5d %-5d %-10d %-10d \n", i, j,
               precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)],
               glv_precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)]);
      }
      print_end_line(true);
    }
    print_end_line(true);
  } else {
    print_header_for_aggregated_table(is_ec_ops, ratio_ec, ratio_ff);
    printf("%-5s %-5s %-10s \n", "w", "w_g", "precomp_g_large");
    print_end_line(true);
    for (int i = N_MIN; i < N_MAX; i++) {
      for (int j = i; j < N_MAX_G; j++) {
        printf("%-5d %-5d %-10d \n", i, j,
               precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)]);
      }
      print_end_line(true);
    }
    print_end_line(true);
  }
}

int main() {

  // for secp256k1, point_double = 0.6 * point_add in projective coordinates
  bool is_print_secp256k1 = false;
  bool is_ec_ops_secp256k1 = true;
  uint32_t ratio_ec_secp256k1 = 3;
  uint32_t ratio_ff_secp256k1 = 3; // TODO: check
  uint32_t bBits_secp256k1 = 256U;
  bool is_glv_secp256k1 = true;
  uint32_t bBits_glv_secp256k1 = 128U; // w/o wNAF

  cost_of_ec_ops cs_secp256k1;
  cs_secp256k1.padd_fmul = 12U;
  cs_secp256k1.padd_fsqr = 0U;
  cs_secp256k1.pdouble_fmul = 6U;
  cs_secp256k1.pdouble_fsqr = 2U;

  printf("\n\nHACL secp256k1-ecdsa-verify:\n");
  // [main], [precomp_g], [glv], [glv_precomp_g]
  print_statistics(is_print_secp256k1, is_ec_ops_secp256k1, ratio_ec_secp256k1,
                   ratio_ff_secp256k1, cs_secp256k1, bBits_secp256k1,
                   is_glv_secp256k1, bBits_glv_secp256k1);

  // [precomp_g_large], [glv_precomp_g_large]
  print_statistics_l_g(is_print_secp256k1, is_ec_ops_secp256k1,
                       ratio_ec_secp256k1, ratio_ff_secp256k1, cs_secp256k1,
                       bBits_secp256k1, is_glv_secp256k1, bBits_glv_secp256k1);

  printf("\n\nHACL secp256k1-ecdsa-sign:\n");
  // [main], [precomp_g]
  print_statistics_1(is_print_secp256k1, is_ec_ops_secp256k1,
                     ratio_ec_secp256k1, ratio_ff_secp256k1, cs_secp256k1,
                     bBits_secp256k1);

  // for ed25519, point_double = 0.8 * point_add
  bool is_print_ed25519 = false;
  bool is_ec_ops_ed25519 = true;
  uint32_t ratio_ec_ed25519 = 4;
  uint32_t ratio_ff_ed25519 = 3; // TODO: check
  uint32_t bBits_ed25519 = 256U;
  bool is_glv_ed25519 = false;
  uint32_t bBits_glv_ed25519 = 0U;

  cost_of_ec_ops cs_ed25519;
  cs_ed25519.padd_fmul = 9U; // 9M + 1D
  cs_ed25519.padd_fsqr = 0U;
  cs_ed25519.pdouble_fmul = 4U;
  cs_ed25519.pdouble_fsqr = 4U;

  printf("\n\nHACL ed25519-verify:\n");
  // [main], [precomp_g]
  print_statistics(is_print_ed25519, is_ec_ops_ed25519, ratio_ec_ed25519,
                   ratio_ff_ed25519, cs_ed25519, bBits_ed25519, is_glv_ed25519,
                   bBits_glv_ed25519);

  // [precomp_g_large]
  print_statistics_l_g(is_print_ed25519, is_ec_ops_ed25519, ratio_ec_ed25519,
                       ratio_ff_ed25519, cs_ed25519, bBits_ed25519,
                       is_glv_ed25519, bBits_glv_ed25519);

  printf("\n\nHACL ed25519-sign:\n");
  // [main], [precomp_g]
  print_statistics_1(is_print_ed25519, is_ec_ops_ed25519, ratio_ec_ed25519,
                     ratio_ff_ed25519, cs_ed25519, bBits_ed25519);

  return EXIT_SUCCESS;
}
