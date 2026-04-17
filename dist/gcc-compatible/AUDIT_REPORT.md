# HACL* C Code Audit Report — Memory Safety & Undefined Behavior

**Date:** 2026-03-17
**Scope:** 85 `.c` files in `dist/gcc-compatible/`, machine-generated from verified F\* via KaRaMeL.

**Key context:** The F\* source is formally verified for memory safety, but the verification model assumes (1) allocation never fails and (2) C's strict NULL-pointer rules for `memcpy` don't apply. Most findings stem from these model gaps, not logic errors.

---

## HIGH Severity

### 1. NULL dereference after failed `CALLOC` — multiple files

`KRML_HOST_CALLOC` return values are used without NULL checks, then immediately dereferenced (via `memcpy`, assignment, or arithmetic). If allocation fails, this is immediate undefined behavior.

| File | Function | Unchecked alloc |
|------|----------|-----------------|
| `EverCrypt_AEAD.c:82` | `create_in_chacha20_poly1305` | `ek` (32B), then `memcpy(ek, k, 32)` |
| `EverCrypt_AEAD.c:107` | `create_in_aes128_gcm` | `ek` (480B) |
| `EverCrypt_AEAD.c:140` | `create_in_aes256_gcm` | `ek` (544B) |
| `EverCrypt_DRBG.c:135-204` | `create_in` (all 4 hash variants) | `k` and `v` buffers |
| `Hacl_HMAC_DRBG.c:91-164` | `create_in` (all 4 hash variants) | `k` and `v` buffers |
| `Hacl_GenericField32.c:80` | `field_init` | `r2` and `n1` |
| `Hacl_GenericField64.c:80` | `field_init` | `r2` and `n1` |
| `Hacl_Bignum256.c:1067` | `mont_ctx_init` | `r2` and `n1` |
| `Hacl_Bignum256_32.c:1100` | `mont_ctx_init` | `r2` and `n1` |
| `Hacl_Bignum4096.c:1022` | `mont_ctx_init` | `r2` and `n1` |
| `Hacl_Bignum4096_32.c:1012` | `mont_ctx_init` | `r2` and `n1` |
| `Hacl_Bignum32.c:486` | `mont_ctx_init` | `r2` and `n1` |
| `Hacl_Bignum64.c:411` | `mont_ctx_init` | `r2` and `n1` |

### 2. Memory leaks + false `Success` on allocation failure — `EverCrypt_AEAD.c`

In all three `create_in_*` functions, if `KRML_HOST_MALLOC` for the state struct `p` returns NULL:
- The already-allocated `ek` buffer is **leaked** (never freed)
- `dst[0U] = NULL` is written
- The function returns `EverCrypt_Error_Success`

The caller has no way to detect the failure.

**Example (`create_in_chacha20_poly1305`, lines 82–91):**
```c
uint8_t *ek = (uint8_t *)KRML_HOST_CALLOC(32U, sizeof (uint8_t));  // no NULL check
EverCrypt_AEAD_state_s
*p = (EverCrypt_AEAD_state_s *)KRML_HOST_MALLOC(sizeof (EverCrypt_AEAD_state_s));
if (p != NULL) { p[0U] = ...; }
memcpy(ek, k, 32U * sizeof (uint8_t));  // ek could be NULL
dst[0U] = p;  // p could be NULL, ek leaked
return EverCrypt_Error_Success;  // always returns Success!
```

### 3. Memory leaks on outer allocation failure — DRBG, Bignum, GenericField

In `EverCrypt_DRBG_create_in`, `Hacl_Bignum*_mont_ctx_init`, and `Hacl_GenericField*_field_init`: if the final outer `KRML_HOST_MALLOC` fails and returns NULL, all previously allocated inner buffers (`k`, `v`, `ctr`, `r2`, `n1`) are leaked.

**Example (`EverCrypt_DRBG_create_in`, lines 135–217):**
```c
uint8_t *k = (uint8_t *)KRML_HOST_CALLOC(20U, sizeof (uint8_t));   // no NULL check
uint8_t *v = (uint8_t *)KRML_HOST_CALLOC(20U, sizeof (uint8_t));   // no NULL check
uint32_t *ctr = (uint32_t *)KRML_HOST_MALLOC(sizeof (uint32_t));
// ...
*buf = (EverCrypt_DRBG_state_s *)KRML_HOST_MALLOC(sizeof (EverCrypt_DRBG_state_s));
if (buf != NULL) { buf[0U] = st; }
return buf;  // if NULL, k/v/ctr are all leaked
```

---

## MEDIUM Severity

### 4. `memcpy` with NULL pointer when length is 0 — HMAC, DRBG, HPKE

Per C11 7.1.4p1, `memcpy(dst, NULL, 0)` is undefined behavior even when the count is 0. This is reachable in:

- **`Hacl_HMAC.c` / `EverCrypt_HMAC.c`**: all `compute_*` functions when `key_len = 0` and `key = NULL`
  ```c
  if (key_len <= 64U)
  {
    memcpy(nkey, key, key_len * sizeof (uint8_t));  // key can be NULL when key_len is 0
  }
  ```
- **`Hacl_HMAC_DRBG.c`**: `instantiate`/`reseed` when optional parameters (e.g., `personalization_string`) are NULL with length 0
  ```c
  memcpy(seed_material + entropy_input_len + nonce_len,
    personalization_string,                              // can be NULL
    personalization_string_len * sizeof (uint8_t));      // can be 0
  ```

### 5. Massive stack allocations in FrodoKEM — likely stack overflow

These arrays are allocated on the stack and exceed default stack limits (typically 1–8 MB) on most platforms, especially in threaded contexts.

| File | Array | Size |
|------|-------|------|
| `Hacl_Frodo1344.c:64` | `uint16_t a_matrix[1806336]` | **~3.6 MB** |
| `Hacl_Frodo976.c:64` | `uint16_t a_matrix[952576]` | **~1.9 MB** |
| `Hacl_Frodo640.c:64` | `uint16_t a_matrix[409600]` | **~800 KB** |

Total stack usage in Frodo1344's `crypto_kem_keypair` is approximately 3.7 MB in a single frame (`a_matrix` + `s_matrix` + `e_matrix` + `r` + `b_matrix`). The same issue appears in `crypto_kem_enc` and `crypto_kem_dec`.

### 6. Zero-length VLAs (C11 undefined behavior) — `Hacl_HMAC_DRBG.c`

If all length parameters are 0, `uint8_t seed_material[0]` is declared, which is UB per C11 6.7.6.2p5. Occurs in `Hacl_HMAC_DRBG_instantiate` at lines 197, 253, 309, 365.

```c
KRML_CHECK_SIZE(sizeof (uint8_t), entropy_input_len + nonce_len + personalization_string_len);
uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];  // can be 0
```

### 7. Unsigned underflow in HPKE `openBase` — all 15 `Hacl_HPKE_*.c` files

```c
uint8_t *tag = ct + ctlen - 16U;
Hacl_AEAD_Chacha20Poly1305_decrypt(o_pt, cipher, ctlen - 16U, ...);
```

If `ctlen < 16`, `ctlen - 16U` wraps to ~4 billion (unsigned), causing massive out-of-bounds reads. No check for `ctlen >= 16` exists. Affects all 15 HPKE variant files:
- `Hacl_HPKE_Curve51_CP{32,128,256}_SHA{256,512}.c`
- `Hacl_HPKE_Curve64_CP{32,128,256}_SHA{256,512}.c`
- `Hacl_HPKE_P256_CP{32,128,256}_SHA256.c`

### 8. VLAs from unchecked parameters — `Hacl_RSAPSS.c`

In `rsapss_skey_sign` (line 793) and `rsapss_pkey_verify` (line 839), VLA sizes are computed from `modBits`/`eBits`/`dBits`:

```c
uint64_t skey[2U * ((modBits - 1U) / 64U + 1U) + (eBits - 1U) / 64U + 1U + (dBits - 1U) / 64U + 1U];
```

If any parameter is 0, `modBits - 1U` wraps to `UINT32_MAX`, creating a catastrophic stack allocation. The higher-level `new_rsapss_load_pkey`/`new_rsapss_load_skey` functions validate inputs, but the lower-level sign/verify functions do not.

### 9. VLAs from caller-controlled sizes — `EverCrypt_DRBG.c`, `Hacl_HMAC_DRBG.c`

Throughout `instantiate`, `reseed`, and `generate` functions, VLAs are sized by caller-provided parameters:

```c
uint8_t seed_material[entropy_input_len + nonce_len + personalization_string_len];
uint8_t input0[input_len];  // input_len = hash_len + 1 + entropy_input_len + ...
```

While `KRML_CHECK_SIZE` is called before each VLA, it typically aborts rather than returning an error. With `max_personalization_string_length = 65536`, VLAs can reach ~100 KB, risking stack overflow. The same pattern exists in `EverCrypt_HKDF.c` where `text[tlen + infolen + 1U]` is allocated with caller-controlled `infolen`.

---

## LOW Severity

### 10. Error codes silently discarded — `EverCrypt_AEAD.c`

The `_no_check` variants of `encrypt_expand`/`decrypt_expand` for AES-GCM compute an error code `r` (potentially `InvalidIVLength` when `iv_len == 0`) but always return `EverCrypt_Error_Success`:

```c
r = EverCrypt_Error_Success;
KRML_MAYBE_UNUSED_VAR(r);
return EverCrypt_Error_Success;  // r is never propagated
```

Affected locations: lines 643–646, 787–790.

### 11. System RNG failure silently ignored — `Hacl_Frodo_KEM.c:34-38`

```c
void randombytes_(uint32_t len, uint8_t *res)
{
  bool b = Lib_RandomBuffer_System_randombytes(res, len);
  KRML_MAYBE_UNUSED_VAR(b);
}
```

If the system RNG fails, FrodoKEM proceeds with uninitialized/zero "randomness", silently breaking all security guarantees.

### 12. Dead NULL checks on stack pointers — `EverCrypt_AEAD.c`

Multiple `encrypt_expand`/`decrypt_expand` functions check `if (s == NULL)` where `s = &p` (a stack variable), which can never be NULL. Unreachable dead code at lines 548–554, 692–698, 835–841, 976–982, 1576–1580, 1726–1730, 1876–1879, 2023–2026.

### 13. Reseed counter overflow — `EverCrypt_DRBG.c`, `Hacl_HMAC_DRBG.c`

`uint32_t` counter incremented without overflow check:
```c
uint32_t old_ctr = ctr[0U];
ctr[0U] = old_ctr + 1U;
```

Practically unreachable — requires 4 billion `generate` calls without reseeding, and the reseed interval check (1024) would force reseeding long before that.

### 14. Pointer arithmetic past buffer end in SHA3 — `Hacl_Hash_SHA3.c:298-300`

```c
uint32_t rem = 0U % len;          // rem = 0 always
uint8_t *b01 = input + input_len; // one-past-end pointer
memcpy(bl0, b01 + 0U - rem, rem * sizeof (uint8_t));  // memcpy with size 0
```

Per C11 7.1.4p1, passing a one-past-end pointer to `memcpy` with size 0 is technically UB, though this is a KaRaMeL code generation artifact and harmless in practice.

### 15. `Hacl_RSAPSS.c:137` — `mgf_hash` underflow when `maskLen = 0`

```c
uint32_t n = (maskLen - 1U) / hLen + 1U;
```

If `maskLen = 0`, wraps to `(UINT32_MAX) / hLen + 1`. Protected by caller preconditions but not by the function itself.

---

## Clean Areas (No Issues Found)

- **Integer/shift undefined behavior:** The entire codebase uses exclusively unsigned types for arithmetic. All shift amounts are within type widths. No signed overflow, division by zero, or unsequenced modifications. KaRaMeL generates very clean integer code.
- **Use-after-free:** None found. Free functions consistently extract inner pointers before freeing outer structs.
- **Double-free:** None found.
- **Mismatched alloc/free:** None. `KRML_HOST_CALLOC`/`MALLOC` consistently paired with `KRML_HOST_FREE`; `KRML_ALIGNED_MALLOC` with `KRML_ALIGNED_FREE`.
- **Pure algorithm files** (Chacha20, Poly1305, SHA2, SHA3, Blake2, Curve25519, Ed25519, P256, K256): Stack-only with fixed-size arrays. No dynamic allocation, no memory safety issues.
- **`EverCrypt_Hash.c`:** Correctly handles allocation failures with proper cleanup — a model for how the other files should work.

---

## Recommendations

1. **Add NULL checks after every `KRML_HOST_CALLOC`/`KRML_HOST_MALLOC`** and free earlier allocations on failure. `EverCrypt_Hash.c` already does this correctly and can serve as a template.
2. **Add `ctlen >= 16` guard** in all HPKE `openBase` functions before the subtraction.
3. **Move FrodoKEM large matrices to heap allocation** to avoid stack overflow.
4. **Guard `memcpy` calls** with `if (len > 0)` when the pointer may be NULL (or use a wrapper macro).
5. **Propagate error codes** in `EverCrypt_AEAD.c` `_no_check` variants instead of discarding them.
6. **Check and propagate RNG failure** in `Hacl_Frodo_KEM.c`.
7. **Add input validation** in lower-level `Hacl_RSAPSS` sign/verify functions to prevent VLA underflow when `modBits`/`eBits`/`dBits` are 0.
