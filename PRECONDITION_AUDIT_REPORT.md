# HACL* Precondition Audit Report

**Date:** 2026-03-27
**Scope:** All public C functions in `dist/gcc-compatible/` headers, traced back to
F\* source code in `code/` to identify preconditions.
**Focus:** Undocumented preconditions that could cause undefined behavior, crashes,
or memory corruption when violated by callers.

---

## Executive Summary

An audit of all public C header files in HACL\*'s `dist/gcc-compatible/` directory
was performed, comparing each function's C documentation against the preconditions
present in the verified F\* source code. The F\* type system enforces buffer sizes,
value ranges, and disjointness constraints that are **erased during extraction to C**,
leaving raw `uint8_t *` pointers and `uint32_t` parameters with no compile-time
enforcement. If the C headers do not document these constraints, callers can easily
violate them, causing undefined behavior.

**Key statistics:**
- **~200 public C functions** audited across 40+ headers
- **1 documentation bug** found (RSAPSS buffer size)
- **1 copy-paste bug** in documentation (Blake2s output_len limit)
- **14 headers with zero documentation** on any function
- **~100 functions** with critical undocumented buffer size preconditions

The most dangerous findings are cases where a public function has a non-obvious
precondition (buffer size, minimum length, value range) that is enforced only by
F\* types and not documented in the C header. A caller following only the C API
could easily trigger out-of-bounds reads/writes.

---

## CRITICAL Findings

These are preconditions whose violation causes **immediate undefined behavior**
(out-of-bounds reads/writes, integer underflow leading to massive allocations)
and that are **not documented** in the C headers.

### CRITICAL-1: Chacha20 — zero documentation for key/nonce sizes

**Files:** `Hacl_Chacha20.h`, `Hacl_Chacha20_Vec32.h`, `Hacl_Chacha20_Vec128.h`, `Hacl_Chacha20_Vec256.h`

The header contains bare function signatures with no comments at all:

```c
void Hacl_Chacha20_chacha20_encrypt(
  uint32_t len, uint8_t *out, uint8_t *text,
  uint8_t *key, uint8_t *n, uint32_t ctr);
```

**Undocumented preconditions from F\* (all cause out-of-bounds access if violated):**
- `key` must point to exactly **32 bytes**
- `n` (nonce) must point to exactly **12 bytes**
- `out` and `text` must each be at least `len` bytes
- `text` and `out` must be either identical or fully disjoint (no partial overlap)

Same applies to `chacha20_decrypt`. A caller who does not know Chacha20 internals
has no way to determine these sizes from the C header alone.

### CRITICAL-2: Salsa20 — zero documentation, inconsistent nonce sizes within one header

**File:** `Hacl_Salsa20.h`

All four functions have zero documentation. The nonce sizes differ between functions
**in the same header** and are not documented anywhere:

| Function | Nonce size | Output size |
|---|---|---|
| `salsa20_encrypt` / `salsa20_decrypt` | **8 bytes** | `len` bytes |
| `salsa20_key_block0` | **8 bytes** | **64 bytes** |
| `hsalsa20` | **16 bytes** | **32 bytes** |

A caller who sizes their nonce buffer for `salsa20_encrypt` (8 bytes) and then
passes it to `hsalsa20` (which reads 16 bytes) triggers an **8-byte out-of-bounds
read**. All functions require a 32-byte key; this is also undocumented.

### CRITICAL-3: Poly1305 — zero documentation for output/key sizes

**Files:** `Hacl_MAC_Poly1305.h`, `Hacl_MAC_Poly1305_Simd128.h`, `Hacl_MAC_Poly1305_Simd256.h`

```c
void Hacl_MAC_Poly1305_mac(
  uint8_t *output, uint8_t *input, uint32_t input_len, uint8_t *key);
```

No documentation. Undocumented preconditions:
- `output` must be exactly **16 bytes** (unconditional write)
- `key` must be exactly **32 bytes** (unconditional read)
- `output` must not overlap `input` or `key`

The streaming API (`malloc`, `reset`, `update`, `digest`, `free`) is also
entirely undocumented:
- `malloc(key)`: `key` must be 32 bytes; return can be NULL
- `digest(state, output)`: `output` must be 16 bytes
- Lifecycle ordering (malloc -> update* -> digest -> free) not stated

### CRITICAL-4: HPKE — zero documentation on all functions; `ctlen > 16` not checked

**Files:** All 15 `Hacl_HPKE_*.h` headers (Curve51, Curve64, P256 variants)

Every HPKE header contains bare function signatures with no comments:

```c
uint32_t Hacl_HPKE_Curve51_CP32_SHA256_openBase(
  uint8_t *pkE, uint8_t *skR, uint32_t infolen, uint8_t *info,
  uint32_t aadlen, uint8_t *aad, uint32_t ctlen, uint8_t *ct, uint8_t *o_pt);
```

**Undocumented preconditions (all cause UB if violated):**
- `openBase`: **`ctlen` must be strictly greater than 16**. The implementation
  computes `ctlen - 16` as `uint32_t`; if `ctlen <= 16`, this underflows to
  ~4 billion, causing a massive out-of-bounds read/write.
- `sealBase`: `o_ct` must be `plainlen + 16` bytes (for ciphertext + tag)
- `skE`/`skR` must be 32 bytes (for Curve25519 variants)
- `pkR`/`pkE` must be 32 bytes (for Curve25519 variants)
- `infolen` has an upper bound depending on the hash algorithm
- `aadlen` and `plainlen` must not exceed AEAD max length

### CRITICAL-5: FFDHE — zero documentation; secret key must be > 1

**File:** `Hacl_FFDHE.h`

All six functions have zero documentation:

```c
void Hacl_FFDHE_ffdhe_secret_to_public(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk);
uint64_t Hacl_FFDHE_ffdhe_shared_secret(
  Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk, uint8_t *ss);
```

**Undocumented preconditions:**
- `sk`, `pk`, and `ss` must each be `ffdhe_len(a)` bytes (256, 384, 512, 768, or
  1024 bytes depending on the algorithm). A caller has no way to know the required
  buffer sizes without calling `ffdhe_len` first, and this is not documented.
- **`sk` must represent a number strictly greater than 1** (big-endian). This is a
  precondition in the F\* source (`1 < nat_from_bytes_be sk`). Passing sk = 0 or
  sk = 1 could produce incorrect cryptographic output.
- `sk` and `pk` must be disjoint from each other and from `ss`.

### CRITICAL-6: FrodoKEM — zero documentation on all functions

**Files:** `Hacl_Frodo640.h`, `Hacl_Frodo976.h`, `Hacl_Frodo1344.h`

All three KEM functions (`crypto_kem_keypair`, `crypto_kem_enc`, `crypto_kem_dec`)
have zero documentation. The required buffer sizes are determined by exported
constants (`crypto_publickeybytes`, `crypto_secretkeybytes`, `crypto_ciphertextbytes`,
`crypto_bytes`) but the headers never state which parameter maps to which constant.

### CRITICAL-7: HKDF — output length limit `len <= 255 * HashLen` undocumented

**Files:** `Hacl_HKDF.h`, `Hacl_HKDF_Blake2b_256.h`, `Hacl_HKDF_Blake2s_128.h`

All HKDF-Expand functions have parameter descriptions but **never document the
RFC 5869 output length limit**:
- SHA-256: `len <= 8160` (255 * 32)
- SHA-384: `len <= 12240` (255 * 48)
- SHA-512: `len <= 16320` (255 * 64)

This is a hard precondition in F\*. Violating it causes the function to read/write
beyond the allocated output buffer.

Also undocumented: `prklen >= hash_length(a)` (PRK must be at least as long as the
hash output).

### CRITICAL-8: NaCl/HPKE `open` functions — minimum ciphertext length undocumented

**Files:** `Hacl_NaCl.h` (for `open_easy` variants), all `Hacl_HPKE_*.h`

The NaCl `crypto_secretbox_open_easy` and `crypto_box_open_easy` functions document
that `m` is `clen - 16` bytes but **never state that `clen >= 16` is required**.
Since `clen` is `uint32_t`, `clen - 16` underflows if `clen < 16`.

The header says:
```
@param m Pointer to `clen` - 16 (tag length) bytes
```
...but does not say: "clen must be at least 16."

### CRITICAL-9: HMAC-DRBG — all NIST SP 800-90A security bounds undocumented

**File:** `Hacl_HMAC_DRBG.h`

None of the DRBG length constraints are documented in C:
- `entropy_input_len`: must be between `min_length(a)` (16 for SHA1, 32 for SHA2)
  and `max_length` (65536)
- `nonce_len`: must be between `min_length(a)/2` and `max_length`
- `personalization_string_len`: must be <= 65536
- `additional_input_len`: must be <= 65536
- `n` (output length for `generate`): must be <= 65536

The `generate` function returns `bool` (false = reseed required), but this is not
documented. The exported constants (`reseed_interval`, `max_output_length`, etc.)
exist but have no documentation explaining their meaning or values.

---

## HIGH Findings

These are preconditions that are partially documented or whose violation has
significant consequences but may be mitigated by type system limits.

### HIGH-1: RSAPSS — documentation bug in `eb`/`db` buffer sizes

**File:** `Hacl_RSAPSS.h`, lines 110, 124, 150, 186

The C header documents `eb` as:
```
@param eb Pointer to `ceil(modBits / 8)` bytes
```

The F\* source specifies `eb: lbuffer uint8 (blocks eBits 8ul)`, which is
**`ceil(eBits / 8)`** bytes, not `ceil(modBits / 8)`.

Same error for `db`: documented as `ceil(modBits / 8)` but should be `ceil(dBits / 8)`.

**Impact:** If `eBits < modBits` (common: RSA-2048 with e=65537 has eBits=17,
modBits=2048), a caller following the documentation would allocate a 256-byte buffer
for `eb` when only 3 bytes are needed. The function reads `ceil(eBits/8)` bytes, so
the oversized buffer is harmless. However, if `eBits > modBits` (unlikely but
possible), the caller would allocate too few bytes, causing an out-of-bounds read.

**Affected functions:**
- `Hacl_RSAPSS_new_rsapss_load_pkey` (eb)
- `Hacl_RSAPSS_new_rsapss_load_skey` (eb, db)
- `Hacl_RSAPSS_rsapss_skey_sign` (eb, db)
- `Hacl_RSAPSS_rsapss_pkey_verify` (eb)

Also undocumented: `modBits > 1`, `eBits > 0`, `dBits > 0`.

### HIGH-2: Chacha20Poly1305 AEAD — disjointness constraints incomplete

**File:** `Hacl_AEAD_Chacha20Poly1305.h`

The encrypt function documents buffer sizes well and notes that in-place
encryption is allowed (`input` and `output` can be the same pointer). However,
it does NOT document:
- `output` and `tag` must be **strictly disjoint** (not just different starts —
  they cannot overlap at all)
- `key` and `nonce` must not overlap with `output` or `tag`
- `data` (AAD) must not overlap with `output`

The `eq_or_disjoint` semantics are also incomplete: the header says "input and
output can point to the same memory" but does not warn that partial overlap
(e.g., `output = input + 1`) is undefined behavior.

### HIGH-3: EverCrypt AEAD — `iv_len > 0` and `ad_len <= 2^31` undocumented

**File:** `EverCrypt_AEAD.h`

`EverCrypt_AEAD_encrypt` and `decrypt` are partially documented (buffer sizes,
NULL handling, return codes) but omit:
- `iv_len > 0` (must be positive; 0 causes UB)
- For CHACHA20_POLY1305: `iv_len == 12` exactly
- `ad_len <= 2^31`
- Maximum plaintext/ciphertext length per algorithm
- All disjointness constraints between buffers

The `encrypt_expand_*` family (8 functions) and `decrypt_expand_*` family
(8 functions) are almost entirely undocumented.

### HIGH-4: EverCrypt HMAC, Chacha20Poly1305, Poly1305, Ed25519 — completely undocumented

**Files:**
- `EverCrypt_HMAC.h` — `EverCrypt_HMAC_compute` has no documentation at all.
  Output buffer size (hash-length-dependent), supported algorithms, key
  constraints — all missing.
- `EverCrypt_Chacha20Poly1305.h` — `aead_encrypt` and `aead_decrypt` have no
  documentation. Key (32), nonce (12), tag (16) sizes all missing.
- `EverCrypt_Poly1305.h` — `mac` has no documentation. Output (16) and key (32)
  sizes missing.
- `EverCrypt_Ed25519.h` — all 5 functions (`secret_to_public`, `expand_keys`,
  `sign_expanded`, `sign`, `verify`) have no documentation. The 96-byte
  `expanded_keys` buffer requirement is particularly non-obvious.

### HIGH-5: Streaming HMAC — entire API undocumented

**File:** `Hacl_Streaming_HMAC.h`

All 7 public functions (`malloc_`, `reset`, `update`, `digest`, `free`, `copy`,
`get_impl`) have zero documentation. Missing:
- Valid `impl` values (0-13)
- Key length constraints (`keysized` per algorithm)
- Output buffer size for `digest` (hash-length-dependent)
- Lifecycle ordering (malloc -> reset -> update* -> digest -> free)
- Error code meanings

### HIGH-6: EverCrypt AutoConfig2 — prerequisite for all agile APIs, undocumented

**File:** `EverCrypt_AutoConfig2.h`

`EverCrypt_AutoConfig2_init()` must be called before using any agile EverCrypt
API. This is never documented in the AutoConfig header or any of the EverCrypt
headers that depend on it. All 26 functions (init, recall, 11 feature queries,
11 feature disablers, has_vec128, has_vec256) have no documentation.

---

## MEDIUM Findings

### MEDIUM-1: Curve25519 — `ecdh` return value semantics undocumented

**Files:** `Hacl_Curve25519_51.h`, `Hacl_Curve25519_64.h`, `EverCrypt_Curve25519.h`

The `ecdh` function returns `bool` but the C headers do not explain what it means.
From F\*: `false` means the shared secret is all zeros (indicating the peer supplied
a low-order point). This is security-critical information.

Buffer sizes (32 bytes each) are documented. Disjointness (`out` must not overlap
`priv` or `pub`) is not documented.

### MEDIUM-2: HMAC — `data_len + block_length < 2^32` overflow constraint

**File:** `Hacl_HMAC.h`

All 11 HMAC compute functions document output buffer sizes and key behavior well.
However, the F\* precondition `data_len + block_length(a) < 2^32` is never
documented. Since `data_len` is `uint32_t`, this can only overflow when
`data_len > 2^32 - block_length - 1` (e.g., `data_len > 2^32 - 65` for SHA-256).
In practice nearly unreachable, but formally required.

### MEDIUM-3: Blake2 — salt/personal buffer sizes undocumented; `hash_with_key` bug

**Files:** `Hacl_Hash_Blake2b.h`, `Hacl_Hash_Blake2s.h`

Blake2 documentation is generally excellent. However:
- **Documentation bug in Blake2s**: `hash_with_key` says `output_len` must be
  `1 <= output_len <= 64` but Blake2s maximum output is **32** bytes, not 64.
  This is a copy-paste from Blake2b.
- Salt buffer sizes (Blake2b: 16 bytes, Blake2s: 8 bytes) and personalization
  buffer sizes (same) are not documented per-function, though macros
  `HACL_HASH_BLAKE2B_SALT_BYTES` etc. are defined.
- `digest_length >= 1` is not documented (0-length digest is invalid).
- `update` says "0 = success, 1 = max length exceeded" but does not state what
  the max length is (Blake2b: 2^128-1, Blake2s: 2^64-1).

### MEDIUM-4: SHA-3 streaming API — entirely undocumented

**File:** `Hacl_Hash_SHA3.h`

The streaming API (malloc, free, copy, reset, update, digest, squeeze) has zero
documentation. The one-shot functions (sha3_224/256/384/512, shake128/256) also
have no documentation for buffer size requirements.

Exception: the low-level `shake128_absorb_nblocks`, `shake128_absorb_final`,
`shake128_squeeze_nblocks` functions ARE well documented.

### MEDIUM-5: SHA-2 — 224/384 variants systematically missing docs

**File:** `Hacl_Hash_SHA2.h`

The SHA2-256 and SHA2-512 streaming functions have good documentation (including
max input length limits). The SHA2-224 and SHA2-384 variants have **no comments
at all**, despite being functionally identical (except for output size and IV).

### MEDIUM-6: P256/K256 — disjointness constraints systematically missing

**Files:** `Hacl_P256.h`, `Hacl_K256_ECDSA.h`

Both headers have good documentation for buffer sizes, key validity ranges, and
return value semantics. The systematic gap is **disjointness constraints**:
- Signing functions: `signature` must not overlap `msg`, `private_key`, or `nonce`
- DH functions: `shared_secret` must not overlap `their_pubkey` or `private_key`
- Key conversion functions: input and output must not overlap

These are required by F\* but never stated in C headers. In contrast, the Ed25519
header (`Hacl_Ed25519.h`) explicitly documents "Must not overlap the memory
location of X" for all functions — this is the model to follow.

### MEDIUM-7: EverCrypt Hash — `free` references wrong function name

**File:** `EverCrypt_Hash.h`

The `free` function's comment says "Free a state previously allocated with
`create_in`" but the allocation function is named `malloc`. This is a documentation
inconsistency that could confuse callers looking for `create_in`.

---

## LOW Findings

### LOW-1: Internal functions leaked into public headers

Several headers expose KaRaMeL-generated discriminator functions that should be
internal:
- `EverCrypt_AEAD_uu___is_Ek` in `EverCrypt_AEAD.h`
- `EverCrypt_DRBG_uu___is_SHA1_s` (and SHA2 variants) in `EverCrypt_DRBG.h`
- `Hacl_HMAC_DRBG_uu___is_State` in `Hacl_HMAC_DRBG.h`
- `Hacl_Hash_SHA3_absorb_inner_32` in `Hacl_Hash_SHA3.h`

These should be documented as "internal — do not call directly" or ideally not
exposed in the header at all.

### LOW-2: DRBG reseed counter overflow

**Files:** `EverCrypt_DRBG.h`, `Hacl_HMAC_DRBG.h`

The `uint32_t` reseed counter is incremented without overflow check. Practically
unreachable (requires 4 billion `generate` calls without reseeding, but the
reseed interval check at 1024 would force reseeding long before that).

### LOW-3: HMAC `keysized` constraint on key length

The `keysized` F\* precondition requires `key_len < max_input_length(a)` and
`key_len + block_length(a) < 2^32`. The C headers correctly document "can be any
length; hashed if > block_length" but do not state the theoretical upper bound.
In practice, `uint32_t key_len` limits this to < 4GB, well within bounds.

---

## Documentation Quality by Header

### Well-Documented Headers (model to follow)

| Header | Notes |
|---|---|
| `Hacl_Ed25519.h` | All preconditions documented, including disjointness. Uses `@@Comment` F\* annotations. |
| `Hacl_EC_Ed25519.h` | Excellent: buffer sizes, disjointness/equality, coordinate systems, endianness. |
| `Hacl_EC_K256.h` | Excellent: same quality as EC_Ed25519. |
| `Hacl_P256.h` | Good: buffer sizes, key validity, return semantics. Only missing disjointness. |
| `Hacl_K256_ECDSA.h` | Good: same quality as P256. Low-S normalization behavior documented. |
| `Hacl_Hash_Blake2b.h` | Good: detailed parameter constraints. Minor gaps (salt/personal sizes). |
| `Hacl_Bignum32.h` | Excellent: complete preconditions including `a < n`, odd modulus, primality. |
| `Hacl_Bignum64.h` | Good: same quality as Bignum32. |
| `EverCrypt_Hash.h` | Good: max input lengths, error codes, lifecycle. |

### Partially-Documented Headers (need improvement)

| Header | Notes |
|---|---|
| `Hacl_AEAD_Chacha20Poly1305.h` | Buffer sizes documented; disjointness incomplete. |
| `Hacl_HMAC.h` | Output sizes and key behavior documented; overflow constraints missing. |
| `Hacl_HKDF.h` | Parameter descriptions present; RFC 5869 limits missing. |
| `Hacl_NaCl.h` | Buffer sizes documented; `clen >= 16` and disjointness missing. |
| `Hacl_Hash_SHA2.h` | 256/512 documented; 224/384 missing. |
| `Hacl_Curve25519_51.h` | Buffer sizes documented; return semantics and disjointness missing. |
| `EverCrypt_AEAD.h` | Core encrypt/decrypt partially documented; expand variants undocumented. |
| `EverCrypt_DRBG.h` | Create/instantiate/generate documented; length limits missing. |
| `Hacl_RSAPSS.h` | Well-structured docs but has buffer size bug and missing `modBits > 1`. |
| `Hacl_HMAC_DRBG.h` | Supported algorithms documented; all NIST bounds missing. |

### Undocumented Headers (zero comments on functions)

| Header | Function Count | Impact |
|---|---|---|
| `Hacl_Chacha20.h` | 2 | CRITICAL — key/nonce sizes invisible |
| `Hacl_Chacha20_Vec32.h` | 2 | CRITICAL |
| `Hacl_Chacha20_Vec128.h` | 2 | CRITICAL |
| `Hacl_Chacha20_Vec256.h` | 2 | CRITICAL |
| `Hacl_Salsa20.h` | 4 | CRITICAL — nonce size varies per function |
| `Hacl_MAC_Poly1305.h` | 6 | CRITICAL — output/key sizes invisible |
| `Hacl_MAC_Poly1305_Simd128.h` | 6 | CRITICAL |
| `Hacl_MAC_Poly1305_Simd256.h` | 6 | CRITICAL |
| All 15 `Hacl_HPKE_*.h` | 4 each (60 total) | CRITICAL — ctlen > 16 not checked |
| `Hacl_FFDHE.h` | 6 | CRITICAL — buffer sizes depend on algorithm |
| `Hacl_Frodo640.h` | 3 | CRITICAL — buffer sizes from constants |
| `Hacl_Frodo976.h` | 3 | CRITICAL |
| `Hacl_Frodo1344.h` | 3 | CRITICAL |
| `EverCrypt_HMAC.h` | 2 | HIGH — output size algorithm-dependent |
| `EverCrypt_Chacha20Poly1305.h` | 2 | HIGH — key/nonce/tag sizes missing |
| `EverCrypt_Poly1305.h` | 1 | HIGH — output/key sizes missing |
| `EverCrypt_Ed25519.h` | 5 | HIGH — buffer sizes missing |
| `EverCrypt_AutoConfig2.h` | 26 | HIGH — init() prerequisite undocumented |
| `Hacl_Streaming_HMAC.h` | 10 | HIGH — entire lifecycle undocumented |
| `Hacl_Hash_SHA3.h` (streaming) | ~12 | MEDIUM — streaming API undocumented |

---

## Recommendations

### Immediate (addresses CRITICAL findings)

1. **Add `@@Comment` annotations** to the F\* interface files (`.fsti`) for all
   undocumented headers. The Ed25519 module demonstrates how this generates
   high-quality C header documentation automatically. Priority:
   - `Hacl.Chacha20.fst` (key=32, nonce=12)
   - `Hacl.Salsa20.fst` (key=32, nonce=8/16, output=32/64)
   - `Hacl.Impl.Poly1305.fsti` (output=16, key=32)
   - All HPKE `.fsti` files (especially `ctlen > 16` for `openBase`)
   - `Hacl.FFDHE.fst` (buffer sizes from `ffdhe_len`, sk > 1)
   - `Hacl.Frodo*.fst` (buffer sizes from exported constants)

2. **Add `ctlen > 16` / `clen >= 16` guards** or at minimum document the
   constraint in:
   - All 15 HPKE `openBase` functions
   - NaCl `crypto_secretbox_open_easy` and `crypto_box_open_easy` variants

3. **Fix the RSAPSS documentation bug**: Change `ceil(modBits / 8)` to
   `ceil(eBits / 8)` for the `eb` parameter and `ceil(dBits / 8)` for `db`
   in `new_rsapss_load_pkey`, `new_rsapss_load_skey`, `rsapss_skey_sign`,
   and `rsapss_pkey_verify`.

4. **Fix the Blake2s documentation bug**: Change `1 <= output_len <= 64` to
   `1 <= output_len <= 32` in `Hacl_Hash_Blake2s_hash_with_key`.

### Short-term (addresses HIGH findings)

5. **Document HKDF output length limits** (`len <= 255 * HashLen`) in all
   `expand` functions.

6. **Document HMAC-DRBG bounds** (min/max entropy, nonce, personalization,
   output, additional_input lengths).

7. **Document `EverCrypt_AutoConfig2_init()`** as a prerequisite for all agile
   EverCrypt APIs.

8. **Add documentation to EverCrypt wrappers** (HMAC, Chacha20Poly1305, Poly1305,
   Ed25519) — these are agile convenience APIs that many users will reach for first.

### Longer-term (systematic improvement)

9. **Adopt the `@@Comment` pattern** from Ed25519/P256/K256/Bignum across all
   modules. This ensures documentation is generated from the verified F\* source
   and stays in sync with preconditions.

10. **Add disjointness documentation** systematically. The Ed25519 pattern
    ("Must not overlap the memory location of X") should be applied to all
    functions that have `disjoint` preconditions in F\*.

11. **Mark internal functions** (KaRaMeL discriminators like `uu___is_*`,
    internal helpers like `absorb_inner_32`) with a comment: "Internal — not
    intended for direct use by application code."
