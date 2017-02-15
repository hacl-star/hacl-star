/** dude, is my code constant time?
 *
 * This file measures the execution time of a given function many times with
 * different inputs and performs a Welch's t-test to determine if the function
 * runs in constant time or not. This is essentially leakage detection, and
 * not a timing attack.
 *
 * Notes:
 * 
 *  - the execution time distribution tends to be skewed towards large
 *    timings, leading to a fat right tail. Most executions take little time,
 *    some of them take a lot. We try to speed up the test process by
 *    throwing away those measurements with large cycle count. (For example,
 *    those measurements could correspond to the execution being interrupted
 *    by the OS.) Setting a threshold value for this is not obvious; we just
 *    keep the x% percent fastest timings, and repeat for several values of x.
 * 
 *  - the previous observation is highly heuristic. We also keep the uncropped 
 *    measurement time and do a t-test on that.
 *
 *  - we also test for unequal variances (second order test), but this is
 *    probably redundant since we're doing as well a t-test on cropped
 *    measurements (non-linear transform)
 *
 *  - as long as any of the different test fails, the code will be deemed
 *    variable time.
 *
 */

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include "cpucycles.h"
#include "ttest.h"
#include "random.h"
#include "fixture.h"
#include "percentile.h"

#define number_tests                                                           \
  (1 /* first order uncropped */ + number_percentiles /* cropped */ +          \
   1 /* second order uncropped */)
#define enough_measurements 10000 // pretty arbitrary
#define number_percentiles 100

static t_ctx *t[number_tests];
static int64_t percentiles[number_percentiles] = {0};

// threshold values for Welch's t-test
#define t_threshold_bananas 500 // test failed, with overwhelming probability
#define t_threshold_moderate                                                   \
  10 // test failed. Pankaj likes 4.5 but let's be more lenient

static void __attribute__((noreturn)) die(void) { exit(111); }

// fill percentiles.
// the exponential tendency is mean to approximately match
// the measurements distribution.
static void prepare_percentiles(int64_t *ticks) {
  for (size_t i = 0; i < number_percentiles; i++) {
    percentiles[i] = percentile(
        ticks, 1 - (pow(0.5, 10 * (double)(i + 1) / number_percentiles)),
        number_measurements);
  }
}

static void measure(int64_t *ticks, uint8_t *input_data) {
  for (size_t i = 0; i < number_measurements; i++) {
    ticks[i] = cpucycles();
    do_one_computation(input_data + i * chunk_size);
  }
  ticks[number_measurements] = cpucycles();
}

static void differentiate(int64_t *exec_times, int64_t *ticks) {
  for (size_t i = 0; i < number_measurements; i++) {
    exec_times[i] = ticks[i + 1] - ticks[i];
  }
}

static void update_statistics(int64_t *exec_times, uint8_t *classes) {
  // XXX we could throw away the first 1e4 and the last 1e4 measurements,
  // to minimize measurement noise. test if this actually improves anything.
  for (size_t i = 0; i < number_measurements; i++) {
    int64_t difference = exec_times[i];

    if (difference < 0) {
      continue; // the cpu cycle counter overflowed
    }

    // do a t-test on the execution time
    t_push(t[0], difference, classes[i]);

    // do a t-test on cropped execution times, for several cropping thresholds.
    for (size_t crop_index = 0; crop_index < number_percentiles; crop_index++) {
      if (difference < percentiles[crop_index]) {
        t_push(t[crop_index + 1], difference, classes[i]);
      }
    }

    // do a second-order test (only if we have more than 10000 measurements).
    // Centered product pre-processing.
    if (t[0]->n[0] > 10000) {
      double centered = (double)difference - t[0]->mean[classes[i]];
      t_push(t[1 + number_percentiles], centered * centered, classes[i]);
    }
  }
}

static void wrap_report(t_ctx *x) {
  if (x->n[0] > enough_measurements) {
    double tval = t_compute(x);
    //printf("got t=%4.2f\n", tval);
  } else {
    //printf(" (not enough measurements %f)\n", x->n[0]);
  }
}

// which t-test yields max t value?
static int max_test(void) {
  int ret = 0;
  double max = 0;
  for (size_t i = 0; i < number_tests; i++) {
    if (t[i]->n[0] > enough_measurements) {
      double x = fabs(t_compute(t[i]));
      if (max < x) {
        max = x;
        ret = i;
      }
    }
  }
  return ret;
}

static void report(void) {

  #if 0
  printf("number traces\n");
  for (size_t i = 0; i < number_tests; i++) {
    //printf("traces %zu %f\n", i, t[i]->n[0] +  t[i]->n[1]);
  }
  printf("\n\n");

  printf("first order\n");
  wrap_report(t[0]);

  printf("cropped\n");
  for (size_t i = 0; i < number_percentiles; i++) {
    wrap_report(t[i + 1]);
  }

  printf("second order\n");
  wrap_report(t[1 + number_percentiles]);
  #endif

  int mt = max_test();
  double max_t = fabs(t_compute(t[mt]));
  double number_traces_max_t = t[mt]->n[0] +  t[mt]->n[1];
  double max_tau = max_t / number_traces_max_t;

  printf("meas: %7.2lf M, ", (number_traces_max_t / 1e6));
  if (number_traces_max_t < enough_measurements) {
    printf("not enough measurements (%.0f still to go).\n", enough_measurements-number_traces_max_t);
    return;
  }

  /*
   * max_t: the t statistic value
   * max_tau: a t value normalized by number of measurements.
   *          this way we can compare max_tau taken with different
   *          number of measurements. This is sort of "distance
   *          between distributions", independent of number of
   *          measurements.
   * (5/tau)^2: how many measurements we would need to barely
   *            detect the leak, if present. "barely detect the
   *            leak" = have a t value greater than 5.
   */          
  printf("max t: %+7.2f, max tau: %.2e, (5/tau)^2: %.2e.",
    max_t,
    max_tau,
    (double)(5*5)/(double)(max_tau*max_tau));

  if (max_t > t_threshold_bananas) {
    printf(" Definitely not constant time.\n");
    exit(0);
  }
  if (max_t > t_threshold_moderate) {
    printf(" Probably not constant time.\n");
  }
  if (max_t < t_threshold_moderate) {
    printf(" For the moment, maybe constant time.\n");
  }
}

static void doit(void) {
  // XXX move these callocs to parent
  int64_t *ticks = calloc(number_measurements + 1, sizeof(int64_t));
  int64_t *exec_times = calloc(number_measurements, sizeof(int64_t));
  uint8_t *classes = calloc(number_measurements, sizeof(uint8_t));
  uint8_t *input_data =
      calloc(number_measurements * chunk_size, sizeof(uint8_t));

  if (!ticks || !exec_times || !classes || !input_data) {
    die();
  }

  prepare_inputs(input_data, classes);
  measure(ticks, input_data);
  differentiate(exec_times, ticks); // inplace

  // we compute the percentiles only if they are not filled yet
  if (percentiles[number_percentiles - 1] == 0) {
    prepare_percentiles(exec_times);
  }
  update_statistics(exec_times, classes);
  report();

  free(ticks);
  free(exec_times);
  free(classes);
  free(input_data);
}

int main(int argc, char **argv) {
  (void)argc;
  (void)argv;

  init_dut();
  for (int i = 0; i < number_tests; i++) {
    t[i] = malloc(sizeof(t_ctx));
    t_init(t[i]);
  }

  for (;;) {
    doit();
  }
}
