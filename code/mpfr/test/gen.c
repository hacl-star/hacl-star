#include <stdio.h>
#include <stdlib.h>
#include <mpfr.h>

#define MAXLEN 200

int main(int argc, char* argv[])
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

    fp = fopen(argv[1], "r");
    out = fopen(argv[2], "w");

    while ((read = getline(&line, &len, fp)) != -1) {
      if(line[0] == 'S' || read == 1) continue;
      sscanf(line, "%ld %s %s %s %s %d", &p, b, c, rnd, r, &inex);
      if(rnd[8] == 'F') continue;
      mpfr_set_prec(fb, p); mpfr_set_prec(fc, p); mpfr_set_prec(fr, p);
      mpfr_set_str(fb, b, 16, MPFR_RNDN);
      mpfr_set_str(fc, c, 16, MPFR_RNDN);
      mpfr_set_str(fr, r, 16, MPFR_RNDN);
      mpfr_exp_t emin = 0;
      fprintf(out, "%d %lu %ld %d %lu %ld %s %ld %d %lu %ld %d\n",
	      fb -> _mpfr_sign, fb -> _mpfr_d[0], fb -> _mpfr_exp,
	      fc -> _mpfr_sign, fc -> _mpfr_d[0], fc -> _mpfr_exp,
	      rnd, p,
	      fr -> _mpfr_sign, fr -> _mpfr_d[0],
	      (fr -> _mpfr_exp > -9223372036854775805 ?
	              fr -> _mpfr_exp :
	              fr -> _mpfr_exp + 9223372036854775807 - 2147483647),
	      inex);
    }

    fclose(fp);
}
