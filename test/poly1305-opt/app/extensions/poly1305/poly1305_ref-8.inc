/*
	poly1305 implementation using 8 bit * 8 bit = 16 bit multiplication and 32 bit addition

	based on the public domain reference version in supercop by djb
*/

enum {
	POLY1305_BLOCK_SIZE = 16
};

typedef struct poly1305_state_ref_t {
	unsigned char r[17];
	unsigned char h[17];
	unsigned char pad[17];
	unsigned char final;
} poly1305_state_ref_t;

static size_t
poly1305_block_size_ref(void) {
	return POLY1305_BLOCK_SIZE;
}

static void
poly1305_init_ext_ref(void *state, const poly1305_key *key, size_t bytes_hint) {
	poly1305_state_ref_t *st = (poly1305_state_ref_t *)state;
	size_t i;

	/* bytes_hint not used */
	(void)bytes_hint;

	/* r &= 0xffffffc0ffffffc0ffffffc0fffffff */
	for (i = 0; i < 16; i++) st->r[i] = key->b[i];
	st->r[3] &= 0x0f;
	st->r[4] &= 0xfc;
	st->r[7] &= 0x0f;
	st->r[8] &= 0xfc;
	st->r[11] &= 0x0f;
	st->r[12] &= 0xfc;
	st->r[15] &= 0x0f;
	st->r[16] = 0;

	/* h = 0 */
	for (i = 0; i < 17; i++) st->h[i] = 0;

	/* save pad for later */
	for (i = 0; i < 16; i++) st->pad[i] = key->b[i + 16];
	st->pad[16] = 0;

	st->final = 0;
}

static void
poly1305_add(unsigned char h[17], const unsigned char c[17]) {
	unsigned short u = 0;
	size_t i;
	for (i = 0; i < 17; i++) {
		u += (unsigned short)h[i] + (unsigned short)c[i];
		h[i] = (unsigned char)u & 0xff;
		u >>= 8;
	}
}

static void
poly1305_partial_reduce(unsigned char h[17], unsigned long hr[17]) {
	unsigned long u;
	size_t i;
	u = 0;
	for (i = 0; i < 16; i++) {
		u += hr[i];
		h[i] = (unsigned char)u & 0xff;
		u >>= 8;
	}
	u += hr[16];
	h[16] = (unsigned char)u & 0x03;
	u >>= 2;
	u += (u << 2); /* u *= 5; */
	for (i = 0; i < 16; i++) {
		u += h[i];
		h[i] = (unsigned char)u & 0xff;
		u >>= 8;
	}
	h[16] += (unsigned char)u;
}

static void
poly1305_full_reduce(unsigned char h[17]) {
	static const unsigned char minusp[17] = {
		0x05,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
		0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
		0xfc
	};
	unsigned char horig[17], negative;
	size_t i;

	/* compute h + -p */
	for (i = 0; i < 17; i++) horig[i] = h[i];
	poly1305_add(h, minusp);

	/* select h if h < p, or h + -p if h >= p */
	negative = -(h[16] >> 7);
	for (i = 0; i < 17; i++)
		h[i] ^= negative & (horig[i] ^ h[i]);
}


static void
poly1305_blocks_ref(void *state, const unsigned char *in, size_t inlen) {
	poly1305_state_ref_t *st = (poly1305_state_ref_t *)state;
	const unsigned char hibit = st->final ? 0 : 1; /* 1 << 128 */

	while (inlen >= POLY1305_BLOCK_SIZE) {
		unsigned long hr[17], u;
		unsigned char c[17];
		size_t i, j;

		/* h += m */
		for (i = 0; i < 16; i++)
			c[i] = in[i];
		c[16] = hibit;
		poly1305_add(st->h, c);

		/* h *= r */
		for (i = 0; i < 17; i++) {
			u = 0;
			for (j = 0; j <= i ; j++) {
				u += (unsigned short)st->h[j] * st->r[i - j];
			}
			for (j = i + 1; j < 17; j++) {
				unsigned long v = (unsigned short)st->h[j] * st->r[i + 17 - j];
				v = ((v << 8) + (v << 6)); /* v *= (5 << 6); */
				u += v;
			}
			hr[i] = u;
		}

		/* (partial) h %= p */
		poly1305_partial_reduce(st->h, hr);

		in += POLY1305_BLOCK_SIZE;
		inlen -= POLY1305_BLOCK_SIZE;
	}
}

static void
poly1305_finish_ext_ref(void *state, const unsigned char *in, size_t remaining, unsigned char mac[16]) {
	poly1305_state_ref_t *st = (poly1305_state_ref_t *)state;
	size_t i;

	/* process the remaining block */
	if (remaining) {
		unsigned char final[POLY1305_BLOCK_SIZE] = {0};
		size_t i;
		for (i = 0; i < remaining; i++)
			final[i] = in[i];
		final[remaining] = 1;
		st->final = 1;
		poly1305_blocks_ref(st, final, POLY1305_BLOCK_SIZE);
	}

	/* fully reduce h */
	poly1305_full_reduce(st->h);

	/* h = (h + pad) % (1 << 128) */
	poly1305_add(st->h, st->pad);
	for (i = 0; i < 16; i++) mac[i] = st->h[i];

	/* zero out the state */
	for (i = 0; i < 17; i++) st->r[i] = 0;
	for (i = 0; i < 17; i++) st->h[i] = 0;
	for (i = 0; i < 17; i++) st->pad[i] = 0;
}

static void
poly1305_auth_ref(unsigned char mac[16], const unsigned char *in, size_t inlen, const poly1305_key *key) {
	poly1305_state_ref_t st;
	size_t blocks;
	poly1305_init_ext_ref(&st, key, inlen);
	blocks = (inlen & ~(POLY1305_BLOCK_SIZE - 1));
	if (blocks) {
		poly1305_blocks_ref(&st, in, blocks);
		in += blocks;
		inlen -= blocks;
	}
	poly1305_finish_ext_ref(&st, in, inlen, mac);
}

