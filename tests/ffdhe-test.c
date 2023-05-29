#include <fcntl.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "Hacl_FFDHE.h"

#include "ffdhe_vectors.h"
#include "test_helpers.h"

bool
print_test(Spec_FFDHE_ffdhe_alg a,
           uint8_t* sk1,
           uint8_t* pk1,
           uint8_t* sk2,
           uint8_t* pk2,
           uint8_t* exp)
{
  uint32_t len = Hacl_FFDHE_ffdhe_len(a);
  uint8_t pk_c1[len];
  uint8_t pk_c2[len];
  uint8_t ss1[len];
  uint8_t ss2[len];
  memset(pk_c1, 0U, len * sizeof(uint8_t));
  memset(pk_c2, 0U, len * sizeof(uint8_t));
  memset(ss1, 0U, len * sizeof(uint8_t));
  memset(ss2, 0U, len * sizeof(uint8_t));

  Hacl_FFDHE_ffdhe_secret_to_public(a, sk1, pk_c1);
  Hacl_FFDHE_ffdhe_secret_to_public(a, sk2, pk_c2);
  Hacl_FFDHE_ffdhe_shared_secret(a, sk1, pk2, ss1);
  Hacl_FFDHE_ffdhe_shared_secret(a, sk2, pk1, ss2);

  bool ok = true;
  printf("FFDHE pk1 =? pk_c1: ");
  // ok &= compare_and_print(len,pk_c1,pk1);
  ok &= compare(len, pk_c1, pk1);

  printf("FFDHE pk2 =? pk_c2: ");
  // ok &= compare_and_print(len,pk_c2,pk2);
  ok &= compare(len, pk_c2, pk2);

  printf("FFDHE ss1 =? ss2: ");
  ok &= compare(len, ss1, ss2);

  printf("FFDHE ss1 =? exp:\n");
  ok &= compare_and_print(len, ss1, exp);

  return ok;
}

int
main()
{
  bool ok = true;
  for (int i = 0; i < sizeof(vectors) / sizeof(ffdhe_test_vector); ++i) {
    ok &= print_test(vectors[i].alg,
                     vectors[i].sk1,
                     vectors[i].pk1,
                     vectors[i].sk2,
                     vectors[i].pk2,
                     vectors[i].ss);
  }

  if (ok)
    return EXIT_SUCCESS;
  else
    return EXIT_FAILURE;
}
