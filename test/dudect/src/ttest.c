/**
 * Online Welch's t-test.
 *
 * Tests whether two populations have same mean.
 * This is basically Student's t-test for unequal
 * variances and unequal sample sizes.
 *
 * see https://en.wikipedia.org/wiki/Welch%27s_t-test
 *
 */

#include <math.h>
#include <stdint.h>
#include <assert.h>
#include <stdio.h>
#include "ttest.h"
#include <stdlib.h>

void t_push(t_ctx *ctx, double x, uint8_t class) {
  assert(class == 0 || class == 1);
  ctx->n[class]++;
  // Welford method for computing online variance
  // in a numerically stable way.
  // see Knuth Vol 2
  double delta = x - ctx->mean[class];
  ctx->mean[class] = ctx->mean[class] + delta / ctx->n[class];
  ctx->m2[class] = ctx->m2[class] + delta * (x - ctx->mean[class]);
}

double t_compute(t_ctx *ctx) {
  double var[2] = {0.0, 0.0};
  var[0] = ctx->m2[0] / (ctx->n[0] - 1);
  var[1] = ctx->m2[1] / (ctx->n[1] - 1);
  double num = (ctx->mean[0] - ctx->mean[1]);
  double den = sqrt(var[0] / ctx->n[0] + var[1] / ctx->n[1]);
  double t_value = num / den;
  return t_value;
}

void t_init(t_ctx *ctx) {
  for (int class = 0; class < 2; class ++) {
    ctx->mean[class] = 0.0;
    ctx->m2[class] = 0.0;
    ctx->n[class] = 0.0;
  }
  return;
}

#if 0
static void run_test(void) {
  t_ctx *ctx = malloc(sizeof(t_ctx));
  if (!ctx)
    return;
  t_init(ctx);
  for (int rep = 0; rep < 10000; rep++) {
    double sign = (rep % 2) ? -1 : 1;
    t_push(ctx, sign * rep, rep % 2);
  }

  double t = t_compute(ctx);
  printf("test t=%4.2f\n", t);
  return;
}

int main(int argc, char **argv) { run_test(); }
#endif
