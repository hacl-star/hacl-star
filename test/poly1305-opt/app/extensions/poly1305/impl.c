#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "cpuid.h"
#include "poly1305.h"

typedef struct poly1305_state_internal_t {
	unsigned char opaque[192]; /* largest state required (AVX2) */
	size_t leftover, block_size;
	unsigned char buffer[64]; /* largest blocksize (AVX2) */
} poly1305_state_internal;

typedef struct poly1305_impl_t {
	unsigned long cpu_flags;
	const char *desc;

	size_t (*block_size)(void);
	void (*init_ext)(void *state, const poly1305_key *key, size_t bytes_hint);
	void (*blocks)(void *state, const unsigned char *in, size_t inlen);
	void (*finish_ext)(void *state, const unsigned char *in, size_t remaining, unsigned char *mac);
	void (*auth)(unsigned char *mac, const unsigned char *in, size_t inlen, const poly1305_key *key);
} poly1305_impl_t;

#define POLY1305_DECLARE(ext) \
	size_t poly1305_block_size_##ext(void); \
	void poly1305_init_ext_##ext(void *state, const poly1305_key *key, size_t bytes_hint); \
	void poly1305_blocks_##ext(void *state, const unsigned char *in, size_t inlen); \
	void poly1305_finish_ext_##ext(void *state, const unsigned char *in, size_t remaining, unsigned char *mac); \
	void poly1305_auth_##ext(unsigned char *mac, const unsigned char *m, size_t inlen, const poly1305_key *key);

#define POLY1305_IMPL(cpuflags, desc, ext) \
	{(cpuflags), desc, poly1305_block_size_##ext, poly1305_init_ext_##ext, poly1305_blocks_##ext, poly1305_finish_ext_##ext, poly1305_auth_##ext}

#if defined(ARCH_X86)
	/* 32 bit only implementations */
	#if defined(CPU_32BITS)
	#endif

	/* 64 bit only implementations */
	#if defined(CPU_64BITS)
	#endif

	/* both 32 and 64 bits */
	POLY1305_DECLARE(x86)
	#define POLY1305_X86 POLY1305_IMPL(CPUID_X86, "x86", x86)

	#if defined(HAVE_SSE2)
		POLY1305_DECLARE(sse2)
		#define POLY1305_SSE2 POLY1305_IMPL(CPUID_SSE2, "sse2", sse2)
	#endif

	#if defined(HAVE_AVX)
		POLY1305_DECLARE(avx)
		#define POLY1305_AVX POLY1305_IMPL(CPUID_AVX, "avx", avx)
	#endif

	#if defined(HAVE_AVX2)
		POLY1305_DECLARE(avx2)
		#define POLY1305_AVX2 POLY1305_IMPL(CPUID_AVX2, "avx2", avx2)
	#endif
#endif

#if defined(ARCH_ARM)
	#if defined(HAVE_ARMv6)
		POLY1305_DECLARE(armv6)
		#define POLY1305_ARMv6 POLY1305_IMPL(CPUID_ARMv6, "armv6", armv6)
	#endif

	#if defined(HAVE_NEON)
		POLY1305_DECLARE(neon)
		#define POLY1305_NEON POLY1305_IMPL(CPUID_NEON, "neon", neon)
	#endif
#endif

/* the "always runs" version */
#if defined(HAVE_INT64) && defined(HAVE_INT128)
	#define POLY1305_GENERIC POLY1305_IMPL(CPUID_GENERIC, "generic/64", ref)
	#include "poly1305/poly1305_ref-64.inc"
#elif defined(HAVE_INT32) && defined(HAVE_INT64)
	#define POLY1305_GENERIC POLY1305_IMPL(CPUID_GENERIC, "generic/32", ref)
	#include "poly1305/poly1305_ref-32.inc"
#else
	#define POLY1305_GENERIC POLY1305_IMPL(CPUID_GENERIC, "generic/8", ref)
	#include "poly1305/poly1305_ref-8.inc"
#endif

/* list implemenations from most optimized to least, with generic as the last entry */
static const poly1305_impl_t poly1305_list[] = {
	/* x86 */
	#if defined(POLY1305_AVX2)
		POLY1305_AVX2,
	#endif
	#if defined(POLY1305_AVX)
		POLY1305_AVX,
	#endif
	#if defined(POLY1305_SSE2)
		POLY1305_SSE2,
	#endif
	#if defined(POLY1305_X86)
		POLY1305_X86,
	#endif

	/* arm */
	#if defined(POLY1305_NEON)
		POLY1305_NEON,
	#endif
	#if defined(POLY1305_ARMv6)
		POLY1305_ARMv6,
	#endif

	POLY1305_GENERIC
};

POLY1305_DECLARE(bootup)

static const poly1305_impl_t poly1305_bootup_impl = POLY1305_IMPL(CPUID_GENERIC, "bootup", bootup);
static const poly1305_impl_t *poly1305_opt = &poly1305_bootup_impl;

/* is the pointer aligned on a word boundary? */
static int
poly1305_is_aligned(const void *p) {
	return ((size_t)p & (sizeof(size_t) - 1)) == 0;
}

/* processes inlen bytes (full blocks only), handling input alignment */
static void
poly1305_consume(poly1305_state_internal *state, const unsigned char *in, size_t inlen) {
	int in_aligned;

	/* it's ok to call with 0 bytes */
	if (!inlen)
		return;

	/* if everything is aligned, handle directly */
	in_aligned = poly1305_is_aligned(in);
	if (in_aligned) {
		poly1305_opt->blocks(state->opaque, in, inlen);
		return;
	}

	/* copy the unaligned data to an aligned buffer and process in chunks */
	while (inlen) {
		unsigned char buffer[1024];
		const size_t bytes = (inlen > sizeof(buffer)) ? sizeof(buffer) : inlen;
		memcpy(buffer, in, bytes);
		poly1305_opt->blocks(state->opaque, buffer, bytes);
		in += bytes;
		inlen -= bytes;
	}
}


LIB_PUBLIC void
poly1305_init(poly1305_state *S, const poly1305_key *key) {
	poly1305_state_internal *state = (poly1305_state_internal *)S;
	poly1305_opt->init_ext(state->opaque, key, 0);
	state->leftover = 0;
	state->block_size = poly1305_opt->block_size();
}

LIB_PUBLIC void
poly1305_init_ext(poly1305_state *S, const poly1305_key *key, size_t bytes_hint) {
	poly1305_state_internal *state = (poly1305_state_internal *)S;
	poly1305_opt->init_ext(state->opaque, key, bytes_hint);
	state->leftover = 0;
	state->block_size = poly1305_opt->block_size();
}

LIB_PUBLIC void
poly1305_update(poly1305_state *S, const unsigned char *in, size_t inlen) {
	poly1305_state_internal *state = (poly1305_state_internal *)S;

	/* handle leftover */
	if (state->leftover) {
		size_t want = (state->block_size - state->leftover);
		if (want > inlen)
			want = inlen;
		memcpy(state->buffer + state->leftover, in, want);
		inlen -= want;
		in += want;
		state->leftover += want;
		if (state->leftover < state->block_size)
			return;
		poly1305_opt->blocks(state->opaque, state->buffer, state->block_size);
		state->leftover = 0;
	}

	/* process full blocks */
	if (inlen >= state->block_size) {
		size_t want = (inlen & ~(state->block_size - 1));
		poly1305_consume(state, in, want);
		in += want;
		inlen -= want;
	}

	/* store leftover */
	if (inlen) {
		memcpy(state->buffer + state->leftover, in, inlen);
		state->leftover += inlen;
	}
}

LIB_PUBLIC void
poly1305_finish(poly1305_state *S, unsigned char *mac) {
	poly1305_state_internal *state = (poly1305_state_internal *)S;
	poly1305_opt->finish_ext(state->opaque, state->buffer, state->leftover, mac);
}

LIB_PUBLIC void
poly1305_auth(unsigned char *mac, const unsigned char *in, size_t inlen, const poly1305_key *key) {
	poly1305_opt->auth(mac, in, inlen, key);
}

/* does an incremental mac as well as a one pass and verifies they all match */
static int
poly1305_auth_test(unsigned char *mac, const unsigned char *in, size_t inlen, const poly1305_key *key) {
	poly1305_state st;
	unsigned char mac2[16];
	size_t block_size = poly1305_opt->block_size();

	/* one pass */
	poly1305_auth(mac, in, inlen, key);

	/* incremental one pass */
	poly1305_init_ext(&st, key, inlen);
	poly1305_update(&st, in, inlen);
	poly1305_finish(&st, mac2);

	/* make sure they match */
	if (memcmp(mac, mac2, 16) != 0) {
		memset(mac, 0, 16);
		return 1;
	}

	/* incremental multi-pass. SSE2/AVX/AVX2 can support up to a 64 byte block size, so try all possible block sizes (64, 32, 16) */
	poly1305_init(&st, key);

	/* do the native block size first to prime the state */
	if (inlen >= block_size) { poly1305_update(&st, in, block_size); in += block_size; inlen -= block_size; }

	/* try 64 down to 16 */
	if    (inlen >= 64) { poly1305_update(&st, in, 64); in += 64; inlen -= 64; }
	if    (inlen >= 32) { poly1305_update(&st, in, 32); in += 32; inlen -= 32; }
	if    (inlen >= 16) { poly1305_update(&st, in, 16); in += 16; inlen -= 16; }
	if    (inlen >   0) { poly1305_update(&st, in, inlen);                    }
	poly1305_finish(&st, mac2);

	/* make sure they match */
	if (memcmp(mac, mac2, 16) != 0) {
		memset(mac, 0, 16);
		return 1;
	}

	return 0;
}

static int
poly1305_test_impl(const void *impl) {
	/* example from nacl */
	static const poly1305_key nacl_key = {{
		0xee,0xa6,0xa7,0x25,0x1c,0x1e,0x72,0x91,
		0x6d,0x11,0xc2,0xcb,0x21,0x4d,0x3c,0x25,
		0x25,0x39,0x12,0x1d,0x8e,0x23,0x4e,0x65,
		0x2d,0x65,0x1f,0xa4,0xc8,0xcf,0xf8,0x80,
	}};

	static const unsigned char nacl_msg[131] = {
		0x8e,0x99,0x3b,0x9f,0x48,0x68,0x12,0x73,
		0xc2,0x96,0x50,0xba,0x32,0xfc,0x76,0xce,
		0x48,0x33,0x2e,0xa7,0x16,0x4d,0x96,0xa4,
		0x47,0x6f,0xb8,0xc5,0x31,0xa1,0x18,0x6a,
		0xc0,0xdf,0xc1,0x7c,0x98,0xdc,0xe8,0x7b,
		0x4d,0xa7,0xf0,0x11,0xec,0x48,0xc9,0x72,
		0x71,0xd2,0xc2,0x0f,0x9b,0x92,0x8f,0xe2,
		0x27,0x0d,0x6f,0xb8,0x63,0xd5,0x17,0x38,
		0xb4,0x8e,0xee,0xe3,0x14,0xa7,0xcc,0x8a,
		0xb9,0x32,0x16,0x45,0x48,0xe5,0x26,0xae,
		0x90,0x22,0x43,0x68,0x51,0x7a,0xcf,0xea,
		0xbd,0x6b,0xb3,0x73,0x2b,0xc0,0xe9,0xda,
		0x99,0x83,0x2b,0x61,0xca,0x01,0xb6,0xde,
		0x56,0x24,0x4a,0x9e,0x88,0xd5,0xf9,0xb3,
		0x79,0x73,0xf6,0x22,0xa4,0x3d,0x14,0xa6,
		0x59,0x9b,0x1f,0x65,0x4c,0xb4,0x5a,0x74,
		0xe3,0x55,0xa5
	};

	static const unsigned char nacl_mac[16] = {
		0xf3,0xff,0xc7,0x70,0x3f,0x94,0x00,0xe5,
		0x2a,0x7d,0xfb,0x4b,0x3d,0x33,0x05,0xd9
	};

	/* generates a final value of (2^130 - 2) == 3 */
	static const poly1305_key wrap_key = {{
		0x02,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
		0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
		0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
		0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	}};

	static const unsigned char wrap_msg[16] = {
		0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
		0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff
	};

	static const unsigned char wrap_mac[16] = {
		0x03,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
		0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
	};

	/*
		auth the auths of [msg:,key:0,0..,pad:ff,ff...], [msg:1,key:1,1..,pad:ff,ff...], 
		[msg:2,2,key:2,2..,pad:ff,ff...] with the following key
	*/
	static const poly1305_key total_key = {{
		0x01,0x02,0x03,0x04,0x05,0x06,0x07,
		0xff,0xfe,0xfd,0xfc,0xfb,0xfa,0xf9,
		0xff,0xff,0xff,0xff,0xff,0xff,0xff,
		0xff,0xff,0xff,0xff,0xff,0xff,0xff
	}};

	static const unsigned char total_mac[16] = {
		0xc6,0x9d,0xc3,0xb9,0x75,0xee,0x5f,0x6b,
		0x28,0x99,0x57,0x94,0x41,0x27,0xd7,0x5e,
	};

	poly1305_state state_total;
	poly1305_key key;
	unsigned char msg[256];
	unsigned char mac[16];
	size_t i, j;
	int result = 0;

	poly1305_opt = (poly1305_impl_t *)impl;

	result |= poly1305_auth_test(mac, nacl_msg, sizeof(nacl_msg), &nacl_key);
	result |= memcmp(nacl_mac, mac, sizeof(nacl_mac));

	result |= poly1305_auth_test(mac, wrap_msg, sizeof(wrap_msg), &wrap_key);
	result |= memcmp(wrap_mac, mac, sizeof(wrap_mac));

	poly1305_init(&state_total, &total_key);
	for (i = 0; i < 256; i++) {
		/* set key and message to 'i,i,i..', pad to 'ff,ff,ff..' */
		for (j = 0; j < 16; j++) key.b[j] = i;
		for (j = 0; j < 16; j++) key.b[j+16] = 0xff;
		for (j = 0; j < i; j++) msg[j] = i;
		result |= poly1305_auth_test(mac, msg, i, &key);
		poly1305_update(&state_total, mac, 16);
	}
	poly1305_finish(&state_total, mac);
	result |= memcmp(total_mac, mac, sizeof(total_mac));

	return result;
}

LIB_PUBLIC int
poly1305_startup(void) {
	const void *opt = LOCAL_PREFIX(cpu_select)(poly1305_list, sizeof(poly1305_impl_t), poly1305_test_impl);
	if (opt) {
		poly1305_opt = (const poly1305_impl_t *)opt;
		return 0;
	} else {
		return 1;
	}
}

size_t
poly1305_block_size_bootup(void) {
	size_t ret = 0;
	if (poly1305_startup() == 0) {
		ret = poly1305_opt->block_size();
	} else {
		fprintf(stderr, "poly1305 failed to startup\n");
		exit(1);
	}
	return ret;
}

void
poly1305_init_ext_bootup(void *state, const poly1305_key *key, size_t bytes_hint) {
	if (poly1305_startup() == 0) {
		poly1305_opt->init_ext(state, key, bytes_hint);
	} else {
		fprintf(stderr, "poly1305 failed to startup\n");
		exit(1);
	}
}

void
poly1305_blocks_bootup(void *state, const unsigned char *in, size_t inlen) {
	if (poly1305_startup() == 0) {
		poly1305_opt->blocks(state, in, inlen);
	} else {
		fprintf(stderr, "poly1305 failed to startup\n");
		exit(1);
	}
}

void
poly1305_finish_ext_bootup(void *state, const unsigned char *in, size_t remaining, unsigned char *mac) {
	if (poly1305_startup() == 0) {
		poly1305_opt->finish_ext(state, in, remaining, mac);
	} else {
		fprintf(stderr, "poly1305 failed to startup\n");
		exit(1);
	}
}

void
poly1305_auth_bootup(unsigned char *mac, const unsigned char *in, size_t inlen, const poly1305_key *key) {
	if (poly1305_startup() == 0) {
		poly1305_opt->auth(mac, in, inlen, key);
	} else {
		fprintf(stderr, "poly1305 failed to startup\n");
		exit(1);
	}
}

#if defined(UTILITIES)

#include <stdio.h>
#include <string.h>
#include "fuzz.h"
#include "bench.h"

static const fuzz_variable_t fuzz_inputs[] = {
	{"key", FUZZ_ARRAY, 32},
	{"input", FUZZ_RANDOM_LENGTH_ARRAY0, 256},
	{0, FUZZ_DONE, 0}
};

static const fuzz_variable_t fuzz_outputs[] = {
	{"auth", FUZZ_ARRAY, 16},
	{0, FUZZ_DONE, 0}
};


/* process the input with the given implementation and write it to the output */
static void
poly1305_fuzz_impl(const void *impl, const unsigned char *in, const size_t *random_sizes, unsigned char *out) {
	const poly1305_key *k = (const poly1305_key *)in;
	const unsigned char *m = in + 32;
	size_t bytes = random_sizes[0];
	poly1305_opt = (const poly1305_impl_t *)impl;
	poly1305_auth_test(out, m, bytes, k);
}

/* run the fuzzer on poly1305 */
void
poly1305_fuzz(void) {
	fuzz_init();
	fuzz(poly1305_list, sizeof(poly1305_impl_t), fuzz_inputs, fuzz_outputs, poly1305_fuzz_impl);
}



static unsigned char *bench_arr = NULL;
static unsigned char bench_mac[16];
static poly1305_key bench_key = {{0}};
static size_t bench_len = 0;

static void
poly1305_bench_impl(const void *impl) {
	poly1305_opt = (const poly1305_impl_t *)impl;
	poly1305_auth(bench_mac, bench_arr, bench_len, &bench_key);
}

void
poly1305_bench(void) {
	static const size_t lengths[] = {1, 64, 128, 576, 8192, 0};
	size_t i;
	bench_arr = bench_get_buffer();
	memset(bench_arr, 0xff, 8192);
	memset(&bench_key, 0xff, sizeof(bench_key));
	for (i = 0; lengths[i]; i++) {
		bench_len = lengths[i];
		bench(poly1305_list, sizeof(poly1305_impl_t), poly1305_test_impl, poly1305_bench_impl, bench_len, "byte");
	}

}

#endif /* defined(UTILITIES) */
