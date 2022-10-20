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

static inline void print_header_for_number_of_point_ops(bool is_print) {
  if (is_print) {
    print_end_line(true);
    printf("%-5s %-5s %-15s %-15s %-15s \n", "w", "w_g", "#point_add",
           "#point_double", "~#point_add");
    print_end_line(true);
  }
}

typedef struct {
  uint32_t precomp_add;
  uint32_t precomp_double;
  uint32_t main_add;
  uint32_t main_double;
  uint32_t rem_add;
} number_of_ec_ops;

static inline uint32_t print_number_of_point_ops(bool is_print, uint32_t ratio,
                                                 uint32_t l, uint32_t l_g,
                                                 number_of_ec_ops ks) {

  uint32_t total_add = ks.precomp_add + ks.main_add + ks.rem_add;
  uint32_t total_double = ks.precomp_double + ks.main_double;

  uint32_t total_appr = total_add + (total_double * ratio / 5U);

  if (is_print) {
    printf("%-5d %-5d %-15d %-15d %-15d \n", l, l_g, total_add, total_double,
           total_appr);
    /* printf(" w = %d \n", l);
       printf(" w_g = %d \n", l_g);
       printf(" total_add = %d \n", total_add);
       printf(" total_double = %d \n", total_double);
       printf(" total_appr = %d \n", total_appr);
       printf("\n"); */
  }
  return total_appr;
}

// [main] precomp_table_g is computed in 1 ECSM
uint32_t main_count_number_of_point_ops_1(bool is_print, uint32_t ratio,
                                          uint32_t l, uint32_t bBits) {
  number_of_ec_ops res;
  // 1 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = table_len / 2U;
  res.precomp_add = table_len / 2U;
  // init step
  res.rem_add = 0U; // we skip mul by `one`
  // main loop
  uint32_t n = bBits / l;
  res.main_double = n * l;
  res.main_add = n;

  return print_number_of_point_ops(is_print, ratio, l, l, res);
}

// [precomp_g] precomp_table_g as constant in 1 ECSM
uint32_t precomp_g_count_number_of_point_ops_1(bool is_print, uint32_t ratio,
                                               uint32_t l, uint32_t bBits) {

  number_of_ec_ops res;
  // no need for a precomp table
  res.precomp_double = 0U;
  res.precomp_add = 0U;
  // init step
  res.rem_add = 0U; // we skip mul by `one`
  // main loop
  uint32_t n = bBits / l;
  res.main_double = n * l;
  res.main_add = n;

  return print_number_of_point_ops(is_print, ratio, l, l, res);
}

// [main] precomp_table_g is computed in 2 ECSM
uint32_t main_count_number_of_point_ops(bool is_print, uint32_t ratio,
                                        uint32_t l, uint32_t bBits) {

  number_of_ec_ops res;
  // 2 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = (table_len / 2U) * 2U;
  res.precomp_add = (table_len / 2U) * 2U;
  // init step
  res.rem_add = (bBits % l == 0U) ? 0U : 1U;
  // main loop
  uint32_t n = bBits / l;
  res.main_double = n * l;
  res.main_add = n + n;

  return print_number_of_point_ops(is_print, ratio, l, l, res);
}

// [precomp_g] precomp_table_g as constant in 2 ECSM
uint32_t precomp_g_count_number_of_point_ops(bool is_print, uint32_t ratio,
                                             uint32_t l, uint32_t bBits) {

  number_of_ec_ops res;
  // 1 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = table_len / 2U;
  res.precomp_add = table_len / 2U;
  // init step
  res.rem_add = (bBits % l == 0U) ? 0U : 1U;
  // main loop
  uint32_t n = bBits / l;
  res.main_double = n * l;
  res.main_add = n + n;

  return print_number_of_point_ops(is_print, ratio, l, l, res);
}

// [precomp_g_large] precomp_table_g as constant in 2 ECSM
uint32_t precomp_g_large_count_number_of_point_ops(bool is_print,
                                                   uint32_t ratio, uint32_t l,
                                                   uint32_t l_g,
                                                   uint32_t bBits) {
  number_of_ec_ops res;
  // 1 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = table_len / 2U;
  res.precomp_add = table_len / 2U;
  // init step
  uint32_t rem_l = bBits % l;
  uint32_t rem_l_g = bBits % l_g;
  res.rem_add = (rem_l != 0U && rem_l_g != 0U) ? 1U : 0U;
  // main loop
  uint32_t min_rem = (rem_l < rem_l_g) ? rem_l : rem_l_g;
  res.main_double = bBits - min_rem;
  res.main_add = bBits / l + bBits / l_g;

  return print_number_of_point_ops(is_print, ratio, l, l_g, res);
}

// [glv] precomp_table_g is computed in 4 ECSM
uint32_t glv_count_number_of_point_ops(bool is_print, uint32_t ratio,
                                       uint32_t l, uint32_t bBits_glv) {

  number_of_ec_ops res;
  // 2 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = (table_len / 2U) * 2U;
  res.precomp_add = (table_len / 2U) * 2U;
  // init step
  res.rem_add = (bBits_glv % l != 0U) ? 3U : 0U;
  // main loop
  uint32_t n = bBits_glv / l;
  res.main_double = n * l;
  res.main_add = n + n + n + n; // four scalars + acc

  return print_number_of_point_ops(is_print, ratio, l, l, res);
}

// [glv_precomp_g] precomp_table_g as constant in 4 ECSM
uint32_t glv_precomp_g_count_number_of_point_ops(bool is_print, uint32_t ratio,
                                                 uint32_t l,
                                                 uint32_t bBits_glv) {

  number_of_ec_ops res;
  // 1 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = table_len / 2U;
  res.precomp_add = table_len / 2U;
  // init step
  res.rem_add = (bBits_glv % l != 0U) ? 3U : 0U;
  // main loop
  uint32_t n = bBits_glv / l;
  res.main_double = n * l;
  res.main_add = n + n + n + n; // four scalars + acc

  // TODO: account for mul by beta = (n + n) M
  return print_number_of_point_ops(is_print, ratio, l, l, res);
}

// [glv_precomp_g_large] precomp_table_g as constant in 4 ECSM
uint32_t glv_precomp_g_large_count_number_of_point_ops(bool is_print,
                                                       uint32_t ratio,
                                                       uint32_t l, uint32_t l_g,
                                                       uint32_t bBits_glv) {
  number_of_ec_ops res;
  // 1 precomp_table
  uint32_t table_len = (1U << l) - 2U;
  res.precomp_double = table_len / 2U;
  res.precomp_add = table_len / 2U;
  // init step
  uint32_t rem_l = bBits_glv % l;
  uint32_t rem_l_g = bBits_glv % l_g;
  res.rem_add = (rem_l == 0U && rem_l_g == 0U)
                    ? 0U
                    : ((rem_l != 0U && rem_l_g != 0U) ? 3U : 1U);
  // main loop
  uint32_t min_rem = (rem_l < rem_l_g) ? rem_l : rem_l_g;
  res.main_double = bBits_glv - min_rem;
  res.main_add = bBits_glv / l + bBits_glv / l + bBits_glv / l_g +
                 bBits_glv / l_g; // four scalars + acc

  // TODO: account for mul by beta = (n + n) M
  return print_number_of_point_ops(is_print, ratio, l, l_g, res);
}

#define N_MIN 3 // included
#define N_MAX 9 // excluded
#define N_LEN (N_MAX - N_MIN)
#define N_MAX_G 16
#define N_LEN_G (N_LEN * (N_MAX_G - N_MIN))

void print_statistics_glv(bool is_print, uint32_t ratio, uint32_t bBits_glv,
                          uint32_t glv_appr[N_LEN],
                          uint32_t glv_precomp_g_appr[N_LEN]) {

  printf("\n\n[glv] precomp_table_g is computed in 4 ECSM \n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    glv_appr[i - N_MIN] =
        glv_count_number_of_point_ops(is_print, ratio, i, bBits_glv);
  }
  print_end_line(is_print);

  printf("\n\n[glv_precomp_g] precomp_table_g as constant in 4 ECSM \n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    glv_precomp_g_appr[i - N_MIN] =
        glv_precomp_g_count_number_of_point_ops(is_print, ratio, i, bBits_glv);
  }
  print_end_line(is_print);
}

void print_statistics(uint32_t ratio, bool is_glv, bool is_print,
                      uint32_t bBits, uint32_t bBits_glv) {
  uint32_t main_appr[N_LEN] = {0};
  printf("\n[main] precomp_table_g is computed in 2 ECSM \n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    main_appr[i - N_MIN] =
        main_count_number_of_point_ops(is_print, ratio, i, bBits);
  }
  print_end_line(is_print);

  uint32_t precomp_g_appr[N_LEN] = {0};
  printf("\n\n[precomp_g] precomp_table_g as constant in 2 ECSM\n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    precomp_g_appr[i - N_MIN] =
        precomp_g_count_number_of_point_ops(is_print, ratio, i, bBits);
  }
  print_end_line(is_print);

  if (is_glv) {
    uint32_t glv_appr[N_LEN] = {0};
    uint32_t glv_precomp_g_appr[N_LEN] = {0};
    print_statistics_glv(is_print, ratio, bBits_glv, glv_appr,
                         glv_precomp_g_appr);

    printf("\n\n");
    printf("Aggregated table with ~#point_add, where point_double = %d / 5 * "
           "point_add \n",
           ratio);
    print_end_line(true);
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
    printf("\n\n");
    printf("Aggregated table with ~#point_add, where point_double = %d / 5 * "
           "point_add \n",
           ratio);
    print_end_line(true);
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
void print_statistics_1(uint32_t ratio, bool is_print, uint32_t bBits) {
  uint32_t main_appr[N_LEN] = {0};
  printf("\n[main] precomp_table_g is computed in 1 ECSM \n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    main_appr[i - N_MIN] =
        main_count_number_of_point_ops_1(is_print, ratio, i, bBits);
  }
  print_end_line(is_print);

  uint32_t precomp_g_appr[N_LEN] = {0};
  printf("\n\n[precomp_g] precomp_table_g as constant in 1 ECSM\n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    precomp_g_appr[i - N_MIN] =
        precomp_g_count_number_of_point_ops_1(is_print, ratio, i, bBits);
  }
  print_end_line(is_print);

  printf("\n\n");
  printf("Aggregated table with ~#point_add, where point_double = %d / 5 * "
         "point_add \n",
         ratio);
  print_end_line(true);
  printf("%-5s %-10s %-15s \n", "w", "main", "precomp_g");
  print_end_line(true);
  for (int i = N_MIN; i < N_MAX; i++) {
    printf("%-5d %-15d %-15d \n", i, main_appr[i - N_MIN],
           precomp_g_appr[i - N_MIN]);
  }
  print_end_line(true);
}

void print_statistics_l_g(uint32_t ratio, bool is_glv, bool is_print,
                          uint32_t bBits, uint32_t bBits_glv) {

  uint32_t len = N_MAX_G - N_MIN;
  uint32_t precomp_g_large_appr[N_LEN_G] = {0};

  printf("\n\n[precomp_g_large] precomp_table_g as constant in 2 ECSM\n");

  print_header_for_number_of_point_ops(is_print);
  for (int i = N_MIN; i < N_MAX; i++) {
    for (int j = i; j < N_MAX_G; j++) {
      precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)] =
          precomp_g_large_count_number_of_point_ops(is_print, ratio, i, j,
                                                    bBits);
    }
    print_end_line(is_print);
  }
  print_end_line(is_print);

  if (is_glv) {
    uint32_t glv_precomp_g_large_appr[N_LEN_G] = {0};
    printf(
        "\n\n[glv_precomp_g_large] precomp_table_g as constant in 4 ECSM \n");

    print_header_for_number_of_point_ops(is_print);
    for (int i = N_MIN; i < N_MAX; i++) {
      for (int j = i; j < N_MAX_G; j++) {
        glv_precomp_g_large_appr[len * (i - N_MIN) + (j - N_MIN)] =
            glv_precomp_g_large_count_number_of_point_ops(is_print, ratio, i, j,
                                                          bBits_glv);
      }
      print_end_line(is_print);
    }
    print_end_line(is_print);

    printf("\n\n");
    printf("Aggregated table with ~#point_add, where point_double = %d / 5 * "
           "point_add \n",
           ratio);
    print_end_line(true);
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
    printf("\n\n");
    printf("Aggregated table with ~#point_add, where point_double = %d / 5 * "
           "point_add \n",
           ratio);
    print_end_line(true);
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
  bool is_glv;
  bool is_print;
  uint32_t ratio;
  uint32_t bBits;
  uint32_t bBits_glv;

  // for secp256k1, point_double = 0.6 * point_add in projective coordinates
  ratio = 3;
  is_glv = true;
  is_print = false;
  bBits = 256U;
  bBits_glv = 128U; // w/o wNAF
  printf("\n\nHACL secp256k1-ecdsa-verify:\n");
  print_statistics(ratio, is_glv, is_print, bBits, bBits_glv);

  // for secp256k1, point_double = 0.6 * point_add in projective coordinates
  ratio = 3;
  is_glv = true;
  is_print = false;
  bBits = 256U;
  bBits_glv = 128U; // w/o wNAF
  printf("\n\nHACL secp256k1-ecdsa-verify:\n");
  print_statistics_l_g(ratio, is_glv, is_print, bBits, bBits_glv);

  // for secp256k1, point_double = 0.6 * point_add in projective coordinates
  ratio = 3;
  is_print = false;
  bBits = 256U;
  printf("\n\nHACL secp256k1-ecdsa-sign:\n");
  print_statistics_1(ratio, is_print, bBits);

  // for ed25519, point_double = 0.8 * point_add
  ratio = 4;
  is_glv = false;
  is_print = false;
  bBits = 256U;
  printf("\n\nHACL ed25519-verify:\n");
  print_statistics(ratio, is_glv, is_print, bBits, 0U);

  // for ed25519, point_double = 0.8 * point_add
  ratio = 4;
  is_glv = false;
  is_print = false;
  bBits = 256U;
  printf("\n\nHACL ed25519-verify:\n");
  print_statistics_l_g(ratio, is_glv, is_print, bBits, 0U);

  // for ed25519, point_double = 0.8 * point_add
  ratio = 4;
  is_print = false;
  bBits = 256U;
  printf("\n\nHACL ed25519-sign:\n");
  print_statistics_1(ratio, is_print, bBits);

  return EXIT_SUCCESS;
}
