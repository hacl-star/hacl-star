#ifndef FUZZ_H
#define FUZZ_H

#include "asmopt_internal.h"

#if defined(__cplusplus)
extern "C" {
#endif

typedef void (*impl_fuzz)(const void *impl, const unsigned char *in, const size_t *random_sizes, unsigned char *out);

typedef enum {
	FUZZ_DONE,
	FUZZ_ARRAY,
	FUZZ_RANDOM_LENGTH_ARRAY0,
	FUZZ_RANDOM_LENGTH_ARRAY1,
	FUZZ_RANDOM_LENGTH_ARRAY2,
	FUZZ_RANDOM_LENGTH_ARRAY3
} fuzz_type_t;

typedef struct fuzz_variable_t {
	const char *desc;
	fuzz_type_t type;
	size_t size;
} fuzz_variable_t;

void fuzz_init(void);
void fuzz_init_deterministic(void);
void fuzz_get_bytes(void *out, size_t len);
void fuzz_print_bytes(const char *desc, const unsigned char *bytes, const unsigned char *base, size_t len);
void fuzz(const void *impls, size_t impl_size, const fuzz_variable_t *input_variables, const fuzz_variable_t *output_variables, impl_fuzz fuzz_fn);

#if defined(__cplusplus)
}
#endif

#endif /* FUZZ_H */
