#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "cpuid.h"
#include "chacha.h"

enum chacha_constants {
	CHACHA_BLOCKBYTES = 64,
};

typedef struct chacha_state_internal_t {
	unsigned char s[48];
	size_t rounds;
	size_t leftover;
	unsigned char buffer[CHACHA_BLOCKBYTES];
} chacha_state_internal;

static void * (* volatile secure_memset)(void *, int, size_t) = memset;

typedef struct chacha_impl_t {
	unsigned long cpu_flags;
	const char *desc;

	void (*chacha)(const chacha_key *key, const chacha_iv *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds);
	void (*xchacha)(const chacha_key *key, const chacha_iv24 *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds);
	void (*chacha_blocks)(chacha_state_internal *state, const unsigned char *in, unsigned char *out, size_t bytes);
	void (*hchacha)(const unsigned char key[32], const unsigned char iv[16], unsigned char out[32], size_t rounds);
} chacha_impl_t;

#define CHACHA_DECLARE(ext) \
	void chacha_##ext(const chacha_key *key, const chacha_iv *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds); \
	void xchacha_##ext(const chacha_key *key, const chacha_iv24 *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds); \
	void chacha_blocks_##ext(chacha_state_internal *state, const unsigned char *in, unsigned char *out, size_t bytes); \
	void hchacha_##ext(const unsigned char key[32], const unsigned char iv[16], unsigned char out[32], size_t rounds);

#define CHACHA_IMPL(cpuflags, desc, ext) \
	{(cpuflags), desc, chacha_##ext, xchacha_##ext, chacha_blocks_##ext, hchacha_##ext}

#if defined(ARCH_X86)
	/* 32 bit only implementations */
	#if defined(CPU_32BITS)
	#endif

	/* 64 bit only implementations */
	#if defined(CPU_64BITS)
	#endif

	/* both 32 & 64 bit implementations */
	#if defined(HAVE_AVX2)
		CHACHA_DECLARE(avx2)
		#define CHACHA_AVX2 CHACHA_IMPL(CPUID_AVX2, "avx2", avx2)
	#endif

	#if defined(HAVE_XOP)
		CHACHA_DECLARE(xop)
		#define CHACHA_XOP CHACHA_IMPL(CPUID_XOP, "xop", xop)
	#endif

	#if defined(HAVE_AVX)
		CHACHA_DECLARE(avx)
		#define CHACHA_AVX CHACHA_IMPL(CPUID_AVX, "avx", avx)
	#endif

	#if defined(HAVE_SSSE3)
		CHACHA_DECLARE(ssse3)
		#define CHACHA_SSSE3 CHACHA_IMPL(CPUID_SSSE3, "ssse3", ssse3)
	#endif

	#if defined(HAVE_SSE2)
		CHACHA_DECLARE(sse2)
		#define CHACHA_SSE2 CHACHA_IMPL(CPUID_SSE2, "sse2", sse2)
	#endif

	CHACHA_DECLARE(x86)
	#define CHACHA_X86 CHACHA_IMPL(CPUID_X86, "x86", x86)
#endif

#if defined(ARCH_ARM)
	#if defined(HAVE_ARMv6)
		CHACHA_DECLARE(armv6)
		#define CHACHA_ARMv6 CHACHA_IMPL(CPUID_ARMv6, "armv6", armv6)
	#endif

	#if defined(HAVE_NEON)
		CHACHA_DECLARE(neon)
		#define CHACHA_NEON CHACHA_IMPL(CPUID_NEON, "neon", neon)
	#endif
#endif

/* the "always runs" version */
#define CHACHA_GENERIC CHACHA_IMPL(CPUID_GENERIC, "generic", ref)
#include "chacha/chacha_ref.inc"

/* list implemenations from most optimized to least, with generic as the last entry */
static const chacha_impl_t chacha_list[] = {
	/* x86 */
	#if defined(CHACHA_AVX2)
		CHACHA_AVX2,
	#endif
	#if defined(CHACHA_XOP)
		CHACHA_XOP,
	#endif
	#if defined(CHACHA_AVX)
		CHACHA_AVX,
	#endif
	#if defined(CHACHA_SSSE3)
		CHACHA_SSSE3,
	#endif
	#if defined(CHACHA_SSE2)
		CHACHA_SSE2,
	#endif
	#if defined(CHACHA_X86)
		CHACHA_X86,
	#endif

	/* arm */
	#if defined(CHACHA_NEON)
		CHACHA_NEON,
	#endif
	#if defined(CHACHA_ARMv6)
		CHACHA_ARMv6,
	#endif

	CHACHA_GENERIC
};

CHACHA_DECLARE(bootup)

static const chacha_impl_t chacha_bootup_impl = {
	CPUID_GENERIC,
	NULL,
	chacha_bootup,
	xchacha_bootup,
	chacha_blocks_bootup,
	hchacha_bootup
};

static const chacha_impl_t *chacha_opt = &chacha_bootup_impl;

/* is the pointer aligned on a word boundary? */
static int
chacha_is_aligned(const void *p) {
	return ((size_t)p & (sizeof(size_t) - 1)) == 0;
}

/* initialize the state */
LIB_PUBLIC void
chacha_init(chacha_state *S, const chacha_key *key, const chacha_iv *iv, size_t rounds) {
	chacha_state_internal *state = (chacha_state_internal *)S;
	memcpy(state->s + 0, key, 32);
	memset(state->s + 32, 0, 8);
	memcpy(state->s + 40, iv, 8);
	state->rounds = rounds;
	state->leftover = 0;
}

/* processes inlen bytes (can do partial blocks), handling input/ouput alignment */
static void
chacha_consume(chacha_state_internal *state, const unsigned char *in, unsigned char *out, size_t inlen) {
	unsigned char buffer[16 * CHACHA_BLOCKBYTES];
	int in_aligned, out_aligned;

	/* it's ok to call with 0 bytes */
	if (!inlen)
		return;

	/* if everything is aligned, handle directly */
	in_aligned = chacha_is_aligned(in);
	out_aligned = chacha_is_aligned(out);
	if (in_aligned && out_aligned) {
		chacha_opt->chacha_blocks(state, in, out, inlen);
		return;
	}

	/* copy the unaligned data to an aligned buffer and process in chunks */
	while (inlen) {
		const size_t bytes = (inlen > sizeof(buffer)) ? sizeof(buffer) : inlen;
		const unsigned char *src = in;
		unsigned char *dst = (out_aligned) ? out : buffer;
		if (!in_aligned) {
			memcpy(buffer, in, bytes);
			src = buffer;
		}
		chacha_opt->chacha_blocks(state, src, dst, bytes);
		if (!out_aligned)
			memcpy(out, buffer, bytes);
		if (in) in += bytes;
		out += bytes;
		inlen -= bytes;
	}
}


/* hchacha */
LIB_PUBLIC void
hchacha(const unsigned char key[32], const unsigned char iv[16], unsigned char out[32], size_t rounds) {
	chacha_opt->hchacha(key, iv, out, rounds);
}


/* update, returns number of bytes written to out */
LIB_PUBLIC size_t
chacha_update(chacha_state *S, const unsigned char *in, unsigned char *out, size_t inlen) {
	chacha_state_internal *state = (chacha_state_internal *)S;
	unsigned char *out_start = out;
	size_t bytes;

	/* enough for at least one block? */
	if ((state->leftover + inlen) >= CHACHA_BLOCKBYTES) {
		/* handle the previous data */
		if (state->leftover) {
			bytes = (CHACHA_BLOCKBYTES - state->leftover);
			if (in) {
				memcpy(state->buffer + state->leftover, in, bytes);
				in += bytes;
			}
			chacha_consume(state, (in) ? state->buffer : NULL, out, CHACHA_BLOCKBYTES);
			inlen -= bytes;
			out += CHACHA_BLOCKBYTES;
			state->leftover = 0;
		}

		/* handle the direct data */
		bytes = (inlen & ~(CHACHA_BLOCKBYTES - 1));
		if (bytes) {
			chacha_consume(state, in, out, bytes);
			inlen -= bytes;
			if (in) in += bytes;
			out += bytes;
		}
	}

	/* handle leftover data */
	if (inlen) {
		if (in) memcpy(state->buffer + state->leftover, in, inlen);
		else memset(state->buffer + state->leftover, 0, inlen);
		state->leftover += inlen;
	}

	return out - out_start;
}

/* sets the counter to 0xffffffff so it should carry on the next call */
static void
chacha_set_test_counter(chacha_state *S) {
	chacha_state_internal *state = (chacha_state_internal *)S;
	state->s[32] = 0xff;
	state->s[33] = 0xff;
	state->s[34] = 0xff;
	state->s[35] = 0xff;
	state->s[36] = 0;
	state->s[37] = 0;
	state->s[38] = 0;
	state->s[39] = 0;
}

/* finalize, write out any leftover data */
LIB_PUBLIC size_t
chacha_final(chacha_state *S, unsigned char *out) {
	chacha_state_internal *state = (chacha_state_internal *)S;
	size_t leftover = state->leftover;
	if (leftover) {
		if (chacha_is_aligned(out)) {
			chacha_opt->chacha_blocks(state, state->buffer, out, leftover);
		} else {
			chacha_opt->chacha_blocks(state, state->buffer, state->buffer, leftover);
			memcpy(out, state->buffer, leftover);
		}
	}
	secure_memset(S, 0, sizeof(chacha_state));
	return leftover;
}

/* one-shot, input/output assumed to be word aligned */
LIB_PUBLIC void
chacha(const chacha_key *key, const chacha_iv *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds) {
	chacha_opt->chacha(key, iv, in, out, inlen, rounds);
}

/*
	xchacha, chacha with a 192 bit nonce
*/

LIB_PUBLIC void
xchacha_init(chacha_state *S, const chacha_key *key, const chacha_iv24 *iv, size_t rounds) {
	chacha_key subkey;
	hchacha(key->b, iv->b, subkey.b, rounds);
	chacha_init(S, &subkey, (chacha_iv *)(iv->b + 16), rounds);
}

/* one-shot, input/output assumed to be word aligned */
LIB_PUBLIC void
xchacha(const chacha_key *key, const chacha_iv24 *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds) {
	chacha_opt->xchacha(key, iv, in, out, inlen, rounds);
}


/*
	chacha/8 test
	key [32,33,34,..63]
	iv [128,129,130,131,132,133,134,135]
	ctr [0x00000000ffffffff]
*/

static size_t chacha_test_rounds = 8;

/* 2048 bytes, enough to trigger the 'fast path' on all implementations */
#define CHACHA_TEST_LEN 2048

/* first block of the test sequence */
static const unsigned char expected_chacha_first[CHACHA_BLOCKBYTES] = {
	0xe7,0x01,0x10,0x8e,0x9a,0x2f,0x24,0xc6,0xcd,0xbb,0x77,0x7e,0x4f,0xcf,0x10,0xae,
	0xd9,0x49,0x5a,0xa6,0x02,0x86,0x9d,0xf9,0x3b,0xb5,0xe2,0xc7,0xe6,0xbd,0xf7,0xf5,
	0x7c,0x9e,0x65,0x91,0x8b,0x95,0x43,0xb8,0xd3,0xcc,0x2f,0x97,0xb8,0xab,0x58,0xd2,
	0xe9,0x94,0x8a,0x4c,0xc6,0xb7,0x78,0x30,0xc2,0x1a,0xbf,0xb7,0xc8,0x8c,0xcd,0xf7,
};

/* xor of all the blocks from the test sequence */
static const unsigned char expected_chacha[CHACHA_BLOCKBYTES] = {
	0xb3,0x1c,0xfa,0xcc,0x9a,0x8e,0xa9,0x82,0x19,0x61,0x3f,0x91,0x04,0x72,0x8f,0x66,
	0x6e,0x3f,0x15,0x6d,0xfd,0x20,0x1c,0x40,0x69,0x36,0x8a,0xc2,0x25,0xd9,0x2d,0xcb,
	0x99,0xdd,0x71,0x46,0x33,0x70,0x15,0x05,0x68,0x29,0x65,0x01,0x15,0x24,0x6d,0x20,
	0xe2,0x63,0xea,0x73,0x60,0x0c,0x94,0xc6,0x7c,0x22,0xf0,0xf7,0x9e,0xa4,0xf8,0x34,
};

/*
	hchacha/8 test
	key [192,193,194,..223]
	iv [16,17,18,..31]
*/

static const unsigned char expected_hchacha[32] = {
	0xe6,0x19,0x0f,0x48,0xf1,0xc0,0x2a,0x68,0xb8,0xf2,0x2e,0xf8,0xbc,0xfd,0x41,0x06,
	0x7b,0xa9,0x36,0xf3,0x63,0x2f,0x5c,0x6d,0x40,0x39,0x24,0xb3,0x74,0x68,0xcb,0xdd,
};

/*
	oneshot chacha+xchacha/8 test
	key [192,193,194,..223]
	iv [16,17,18,..31]
*/

/* xor of all the blocks from the one-shot test sequence */
static const unsigned char expected_chacha_oneshot[CHACHA_BLOCKBYTES] = {
	0x21,0x5b,0x81,0x79,0x74,0xef,0x98,0x89,0xc6,0x40,0x47,0x53,0x42,0x01,0x24,0x88,
	0x21,0xa3,0xb6,0xc8,0x43,0x62,0x0b,0x00,0x19,0xd0,0xd5,0xee,0x6c,0x21,0xf8,0x51,
	0xa8,0xb3,0x45,0x56,0x72,0xc1,0x85,0x0e,0xe1,0x43,0xbe,0xd6,0xa6,0x8b,0x3d,0xdc,
	0x3d,0xf7,0x64,0xfd,0x80,0x0c,0xd9,0x58,0xf8,0x06,0x40,0xf4,0xc2,0x14,0xba,0x84,
};

/* xor of all the blocks from the one-shot test sequence */
static const unsigned char expected_xchacha_oneshot[CHACHA_BLOCKBYTES] = {
	0x01,0xd1,0x84,0x26,0x1b,0x7d,0x44,0x4d,0x3a,0x8f,0xef,0x3f,0x1e,0x11,0xb5,0xa0,
	0x07,0x04,0x46,0x4c,0xfb,0x6b,0xd0,0x30,0x42,0x3d,0xfa,0x56,0x71,0x33,0x96,0xdb,
	0xef,0x0f,0x09,0xc1,0xde,0x41,0xc5,0xa8,0xba,0x37,0x59,0x3f,0x43,0xc3,0xf8,0xc4,
	0xce,0xd5,0xf0,0x51,0x5f,0x2c,0x5e,0xcf,0xe2,0x5e,0x68,0x95,0x7a,0x5c,0x02,0xea,
};


/* initialize state, set the counter right below the 32 bit boundary */
static void
chacha_test_init_state(chacha_state *st, chacha_key *key, chacha_iv *iv) {
	chacha_init(st, key, iv, chacha_test_rounds);
	chacha_set_test_counter(st);
}

/* return a chacha_state * aligned to (sizeof(size_t) - 1) mod 64 */
static chacha_state *
chacha_test_misalign_state(void *p) {
	unsigned char *st = (unsigned char *)p;
	while (((size_t)st & 63) != (sizeof(size_t) - 1))
		st++;
	return (chacha_state *)p;
}

/* test 1..64 byte generation, will use slow single-block codepath, also partial block generation. out must have at least 64 bytes of space */
static int
chacha_test_oneblock(chacha_key *key, chacha_iv *iv, const unsigned char *in, unsigned char *out) {
	unsigned char buffer[sizeof(chacha_state) + 63];
	chacha_state *st = chacha_test_misalign_state(buffer);
	size_t i, j;
	unsigned char *p;
	int res = 0;

	for (i = 1; i <= CHACHA_BLOCKBYTES; i++) {
		memset(out, 0, i);
		p = out;
		chacha_test_init_state(st, key, iv);
		p += chacha_update(st, in, p, i);
		res |= (chacha_final(st, p) != (i & (CHACHA_BLOCKBYTES - 1))) ? 1 : 0;
		/* undo input buffer if needed */
		if (in) {
			for (j = 0; j < i; j++)
				out[j] ^= in[j];
		}
		res |= memcmp(expected_chacha_first, out, i);
	}
	return res;
}

/* xor all the blocks together in to one block, xor'ing the blocks with input if needed */
static void
chacha_test_compact_array(unsigned char *dst, const unsigned char *src, size_t srclen, const unsigned char *in) {
	size_t blocks = srclen / CHACHA_BLOCKBYTES;
	size_t i, j;
	memset(dst, 0, CHACHA_BLOCKBYTES);
	for (i = 0; i < blocks; i++) {
		if (in) {
			for (j = 0; j < CHACHA_BLOCKBYTES; j++)
				dst[j] ^= src[(i * CHACHA_BLOCKBYTES) + j] ^ in[(i * CHACHA_BLOCKBYTES) + j];
		} else {
			for (j = 0; j < CHACHA_BLOCKBYTES; j++)
				dst[j] ^= src[(i * CHACHA_BLOCKBYTES) + j];
		}
	}
}

/* test CHACHA_TEST_LEN byte generation, will trigger efficient multi-block codepath. out must have at least CHACHA_TEST_LEN bytes of space */
static int
chacha_test_multiblock(chacha_key *key, chacha_iv *iv, const unsigned char *in, unsigned char *out) {
	unsigned char buffer[sizeof(chacha_state) + 63];
	chacha_state *st = chacha_test_misalign_state(buffer);
	unsigned char final[CHACHA_BLOCKBYTES];
	unsigned char *p = out;
	int res = 0;

	memset(out, 0, CHACHA_TEST_LEN);
	chacha_test_init_state(st, key, iv);
	p += chacha_update(st, in, p, CHACHA_TEST_LEN);
	res |= (chacha_final(st, p) != (CHACHA_TEST_LEN & (CHACHA_BLOCKBYTES - 1))) ? 1 : 0;
	chacha_test_compact_array(final, out, CHACHA_TEST_LEN, in);
	res |= memcmp(expected_chacha, final, sizeof(expected_chacha));
	return res;
}



/* incremental, test CHACHA_TEST_LEN byte generation, will trigger single/multi-block codepath. out must have at least CHACHA_TEST_LEN bytes of space */
static int
chacha_test_multiblock_incremental(chacha_key *key, chacha_iv *iv, const unsigned char *in, unsigned char *out) {
	unsigned char buffer[sizeof(chacha_state) + 63];
	chacha_state *st = chacha_test_misalign_state(buffer);
	unsigned char final[CHACHA_BLOCKBYTES];
	size_t i, inc;
	unsigned char *p;
	int res = 0;

	for (inc = 1; inc < CHACHA_TEST_LEN; inc += 61) {
		p = out;
		memset(out, 0, CHACHA_TEST_LEN);
		chacha_test_init_state(st, key, iv);
		for(i = 0; i <= CHACHA_TEST_LEN; i += inc)
			p += chacha_update(st, (in) ? (in + i) : NULL, p, ((i + inc) > CHACHA_TEST_LEN) ? (CHACHA_TEST_LEN - i) : inc);
		res |= (chacha_final(st, p) != (CHACHA_TEST_LEN & (CHACHA_BLOCKBYTES - 1))) ? 1 : 0;
		chacha_test_compact_array(final, out, CHACHA_TEST_LEN, in);
		res |= memcmp(expected_chacha, final, sizeof(expected_chacha));
	}

	return res;
}

/* input_buffer is either NULL, or a buffer with at least (CHACHA_TEST_LEN+1) bytes which is initialized to {0} */
static int
chacha_test_impl(const unsigned char *input_buffer, unsigned char *output_buffer) {
	chacha_key key;
	chacha_iv iv;
	chacha_iv24 x_iv;
	unsigned char h_key[32];
	unsigned char h_iv[16];
	unsigned char final[CHACHA_BLOCKBYTES];
	unsigned char final_hchacha[32];
	size_t i;
	int res = 0;

	/*
		key [32,33,34,..63], iv [128,129,130,131,132,133,134,135]
	*/
	for (i = 0; i < sizeof(key); i++) key.b[i] = (unsigned char)(i + 32);
	for (i = 0; i < sizeof(iv); i++) iv.b[i] = (unsigned char)(i + 128);


	/* single block */
	res |= chacha_test_oneblock(&key, &iv, input_buffer, output_buffer);

	/* multi block */
	res |= chacha_test_multiblock(&key, &iv, input_buffer, output_buffer);

	/* incremental */
	res |= chacha_test_multiblock_incremental(&key, &iv, input_buffer, output_buffer);

	/*
		hchacha
		key [192,193,194,..223], iv [16,17,18,..31]
	*/
	for (i = 0; i < sizeof(h_key); i++) h_key[i] = (unsigned char)(i + 192);
	for (i = 0; i < sizeof(h_iv); i++) h_iv[i] = (unsigned char)(i + 16);

	memset(final_hchacha, 0, sizeof(final_hchacha));
	hchacha(h_key, h_iv, final_hchacha, chacha_test_rounds);
	res |= memcmp(expected_hchacha, final_hchacha, sizeof(expected_hchacha));

	/*
		one-shot, buffers must be aligned
		key [192,193,194,..223], iv [16,17,18,..31]
	*/

	if (chacha_is_aligned(input_buffer) && chacha_is_aligned(output_buffer)) {
		for (i = 0; i < sizeof(key); i++) key.b[i] = (unsigned char)(i + 192);
		for (i = 0; i < sizeof(iv); i++) iv.b[i] = (unsigned char)(i + 16);
		for (i = 0; i < sizeof(x_iv); i++) x_iv.b[i] = (unsigned char)(i + 16);

		memset(output_buffer, 0, CHACHA_TEST_LEN);
		chacha(&key, &iv, input_buffer, output_buffer, CHACHA_TEST_LEN, chacha_test_rounds);
		chacha_test_compact_array(final, output_buffer, CHACHA_TEST_LEN, input_buffer);
		res |= memcmp(expected_chacha_oneshot, final, sizeof(expected_chacha_oneshot));

		memset(output_buffer, 0, CHACHA_TEST_LEN);
		xchacha(&key, &x_iv, input_buffer, output_buffer, CHACHA_TEST_LEN, chacha_test_rounds);
		chacha_test_compact_array(final, output_buffer, CHACHA_TEST_LEN, input_buffer);
		res |= memcmp(expected_xchacha_oneshot, final, sizeof(expected_xchacha_oneshot));
	}

	return res;
}

/* somethign random and non-block-repeating to make sure the implementation is actually xor'ing the input data */
static void
chacha_make_test_data(unsigned char *buffer) {
	size_t i, h;

	h = 0;
	for (i = 0; i < CHACHA_TEST_LEN; i++) {
		h += h + i + 0x55;
		h ^= (h >> 3);
		buffer[i] = (unsigned char)h;
	}
}

static int
chacha_test_full_impl(const void *impl) {
	unsigned char buffer[2][CHACHA_TEST_LEN + (sizeof(size_t) * 2)];
	unsigned char *in = buffer[0], *out = buffer[1];
	int res = 0;

	chacha_opt = (chacha_impl_t *)impl;

	/* make sure the buffers are actually word aligned */
	while (!chacha_is_aligned(in)) in++;
	while (!chacha_is_aligned(out)) out++;

	/* test against aligned input buffer, aligned/unaligned output buffers */
	chacha_make_test_data(in);
	res |= chacha_test_impl(in, out);
	res |= chacha_test_impl(NULL, out);
	res |= chacha_test_impl(in, out + 1);
	res |= chacha_test_impl(NULL, out + 1);

	/* unaligned bufferput buffer, aligned/unaligned output buffers */
	chacha_make_test_data(in + 1);
	res |= chacha_test_impl(in + 1, out);
	res |= chacha_test_impl(in + 1, out + 1);

	return res;
}

LIB_PUBLIC int
chacha_startup(void) {
	const void *opt = LOCAL_PREFIX(cpu_select)(chacha_list, sizeof(chacha_impl_t), chacha_test_full_impl);
	if (opt) {
		chacha_opt = (const chacha_impl_t *)opt;
		return 0;
	} else {
		return 1;
	}
}


void
chacha_bootup(const chacha_key *key, const chacha_iv *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds) {
	if (chacha_startup() == 0) {
		chacha_opt->chacha(key, iv, in, out, inlen, rounds);
	} else {
		fprintf(stderr, "chacha failed to startup\n");
		exit(1);
	}
}

void
xchacha_bootup(const chacha_key *key, const chacha_iv24 *iv, const unsigned char *in, unsigned char *out, size_t inlen, size_t rounds) {
	if (chacha_startup() == 0) {
		chacha_opt->xchacha(key, iv, in, out, inlen, rounds);
	} else {
		fprintf(stderr, "chacha failed to startup\n");
		exit(1);
	}
}

void
chacha_blocks_bootup(chacha_state_internal *state, const unsigned char *in, unsigned char *out, size_t bytes) {
	if (chacha_startup() == 0) {
		chacha_opt->chacha_blocks(state, in, out, bytes);
	} else {
		fprintf(stderr, "chacha failed to startup\n");
		exit(1);
	}
}

void
hchacha_bootup(const unsigned char key[32], const unsigned char iv[16], unsigned char out[32], size_t rounds) {
	if (chacha_startup() == 0) {
		chacha_opt->hchacha(key, iv, out, rounds);
	} else {
		fprintf(stderr, "chacha failed to startup\n");
		exit(1);
	}
}

#if defined(UTILITIES)

#include <stdio.h>
#include <string.h>
#include "fuzz.h"
#include "bench.h"

static const fuzz_variable_t fuzz_inputs[] = {
	{"hchacha_key", FUZZ_ARRAY, 32},
	{"hchacha_iv", FUZZ_ARRAY, 16},
	{"chacha_key", FUZZ_ARRAY, 32},
	{"chacha_iv", FUZZ_ARRAY, 8},
	{"input", FUZZ_RANDOM_LENGTH_ARRAY0, 2048},
	{0, FUZZ_DONE, 0}
};

static const fuzz_variable_t fuzz_outputs[] = {
	{"hchacha_output", FUZZ_ARRAY, 32},
	{"chacha_output_oneshot", FUZZ_RANDOM_LENGTH_ARRAY0, 2048},
	{"chacha_output_incremental", FUZZ_RANDOM_LENGTH_ARRAY0, 2048},
	{0, FUZZ_DONE, 0}
};


/* process the input with the given implementation and write it to the output */
static void
chacha_fuzz_impl(const void *impl, const unsigned char *in, const size_t *random_sizes, unsigned char *out) {
	static const size_t rounds = 8;

	const unsigned char *fuzz_hchacha_key = in;
	const unsigned char *fuzz_hchacha_iv = in + 32;
	const unsigned char *fuzz_chacha_key = in + 48;
	const unsigned char *fuzz_chacha_iv = in + 80;
	const unsigned char *fuzz_chacha_input = in + 88;

	unsigned char *fuzz_hchacha_output = out;
	unsigned char *fuzz_chacha_output_oneshot = out + 32;
	unsigned char *fuzz_chacha_output_incremental = out + 32 + random_sizes[0];

	chacha_state st;

	/* set the current implementation to impl */
	chacha_opt = (const chacha_impl_t *)impl;

	/* hchacha */
	hchacha(fuzz_hchacha_key, fuzz_hchacha_iv, fuzz_hchacha_output, rounds);

	/* chacha one shot */
	chacha((const chacha_key *)fuzz_chacha_key, (const chacha_iv *)fuzz_chacha_iv, fuzz_chacha_input, fuzz_chacha_output_oneshot, random_sizes[0], rounds);

	/* chacha incremental, CAN HAVE UNALIGNED INPUT/OUTPUT, which is why we don't align anything */
	chacha_init(&st, (const chacha_key *)fuzz_chacha_key, (const chacha_iv *)fuzz_chacha_iv, rounds);
	fuzz_chacha_output_incremental += chacha_update(&st, fuzz_chacha_input, fuzz_chacha_output_incremental, random_sizes[0]);
	chacha_final(&st, fuzz_chacha_output_incremental);
}

/* run the fuzzer on chacha */
void
chacha_fuzz(void) {
	fuzz_init();
	fuzz(chacha_list, sizeof(chacha_impl_t), fuzz_inputs, fuzz_outputs, chacha_fuzz_impl);
}



static unsigned char *bench_arr = NULL;
static const chacha_key bench_key = {{1}};
static const chacha_iv bench_iv = {{2}};
static const unsigned char hbench_key[32] = {1};
static const unsigned char hbench_iv[16] = {2};
static size_t bench_len = 0;
static size_t bench_rounds = 8;

static void
chacha_bench_impl(const void *impl) {
	const chacha_impl_t *chacha_impl = (const chacha_impl_t *)impl;
	chacha_impl->chacha(&bench_key, &bench_iv, bench_arr, bench_arr, bench_len, bench_rounds);
}

static void
hchacha_bench_impl(const void *impl) {
	const chacha_impl_t *chacha_impl = (const chacha_impl_t *)impl;
	chacha_impl->hchacha(hbench_key, hbench_iv, bench_arr, bench_rounds);
}

void
chacha_bench(void) {
	static const size_t rounds[] = {8, 12, 20, 0};
	static const size_t lengths[] = {1, 64, 576, 8192, 0};
	size_t i, j;
	bench_arr = bench_get_buffer();

	printf("ChaCha\n");
	for (i = 0; rounds[i]; i++) {
		bench_rounds = rounds[i];
		printf("\n---- %u rounds ----\n", (unsigned int)bench_rounds);
		for (j = 0; lengths[j]; j++) {
			bench_len = lengths[j];
			memset(bench_arr, 0xc5, bench_len);
			bench(chacha_list, sizeof(chacha_impl_t), chacha_test_full_impl, chacha_bench_impl, bench_len, "byte");
		}
	}

	printf("HChaCha\n");
	for (i = 0; rounds[i]; i++) {
		bench_rounds = rounds[i];
		printf("\n---- %u rounds ----\n", (unsigned int)bench_rounds);
		bench(chacha_list, sizeof(chacha_impl_t), chacha_test_full_impl, hchacha_bench_impl, 1, "call");
	}
}

#endif /* defined(UTILITIES) */
