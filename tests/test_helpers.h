// This header contains test helpers to avoid ridiculous copy-paste between
// various test files. Keep everything in there static inline.

#pragma "once"

static inline bool compare_and_print(size_t len, uint8_t* comp, uint8_t* exp) {
  printf("computed:");
  for (size_t i = 0; i < len; i++)
    printf("%02x",comp[i]);
  printf("\n");
  printf("expected:");
  for (size_t i = 0; i < len; i++)
    printf("%02x",exp[i]);
  printf("\n");
  bool ok = true;
  for (size_t i = 0; i < len; i++)
    ok = ok & (exp[i] == comp[i]);
  if (ok)
    printf("Success!\n");
  else
    printf("**FAILED**\n");
  return ok;
}
