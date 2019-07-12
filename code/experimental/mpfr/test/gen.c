#include <stdio.h>
#include <stdlib.h>
#include <mpfr.h>

#define MAXLEN 100
#define min(a, b) (((a) < (b)) ? (a) : (b))

int main(void)
{
  FILE * fp, * out;
  char * line = NULL;
  char b[MAXLEN], c[MAXLEN], rnd[MAXLEN], r[MAXLEN];
    size_t len = 0;
    ssize_t read;
    mpfr_t fb, fc, fr;
    mpfr_prec_t p;
    int inex;
    mpfr_init(fb); mpfr_init(fc); mpfr_init(fr);

    fp = fopen("test/add1sp_tests", "r");
    out = fopen("test/add1sp1_testdata", "w");

    while ((read = getline(&line, &len, fp)) != -1) {
      if(line[0] == 'S' || read == 1) continue;
      sscanf(line, "%ld %s %s %s %s %d", &p, b, c, rnd, r, &inex);
      // if(rnd[8] != 'N') continue;
      mpfr_set_prec(fb, p); mpfr_set_prec(fc, p); mpfr_set_prec(fr, p);
      mpfr_set_str(fb, b, 16, MPFR_RNDN);
      mpfr_set_str(fc, c, 16, MPFR_RNDN);
      mpfr_set_str(fr, r, 16, MPFR_RNDN);
      mpfr_exp_t emin = min(min(fb -> _mpfr_exp, fc -> _mpfr_exp), fr -> _mpfr_exp);
      fprintf(out, "%d %lu %ld %lu %ld %s %ld %lu %ld %d\n",
	      fb -> _mpfr_sign,
	      fb -> _mpfr_d[0], fb -> _mpfr_exp - emin,
	      fc -> _mpfr_d[0], fc -> _mpfr_exp - emin,
	      rnd, p,
	      fr -> _mpfr_d[0], fr -> _mpfr_exp - emin,
	      inex);
    }

    fclose(fp);
}
