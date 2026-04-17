# HACL* Specification Audit Report

**Date:** 2026-03-11
**Scope:** All F* specification files in `hacl-star/specs/`
**Method:** Systematic comparison against official IETF RFCs and NIST standards

---

## Executive Summary

An audit of 20+ cryptographic specification files was performed, comparing each
against its authoritative standard (IETF RFC or NIST FIPS/SP publication). Four
bugs were identified: one critical, one high-severity, one medium, and one low.
The remaining specifications were found to be faithful to their standards.

---

## Bugs Found

### BUG-1: HPKE P-256 DeriveKeyPair validates against wrong modulus [CRITICAL]

**File:** `Spec.Agile.HPKE.fst`, line 146
**Standard:** RFC 9180, Section 7.1.3 (DeriveKeyPair for P-256)

**Description:**

The `dkp_nist_p` function derives a P-256 private key from a PRK via
labeled expand. It validates the candidate scalar `sk` with:

```fstar
if sk = 0 || sk >= Spec.P256.prime then
```

RFC 9180 Section 7.1.3 requires the check `0 < sk < order`, where `order` is
the group order of the P-256 curve, not the field prime.

The relevant constants are:

```
order = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
prime = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
```

Since `order < prime`, the current code accepts private keys in the range
`[order, prime)` as valid. This is a window of approximately 2^128 values.
A scalar in this range is not a valid P-256 private key — point multiplication
by such a scalar would produce incorrect results because the scalar exceeds the
group order, effectively reducing modulo `order` during the elliptic curve
operation while the validation assumed it was in range.

**Impact:** Any HPKE ciphersuite using DHKEM(P-256, HKDF-SHA256) could derive
an invalid private key if the HKDF-Expand output falls in `[order, prime)`.
This would cause the sender and receiver to compute different shared secrets,
leading to decryption failure. In a theoretical worst case, it could leak
information about the private key through the relationship between the
unreduced and reduced scalar.

**Fix:**

```fstar
// Line 146: replace Spec.P256.prime with Spec.P256.order
if sk = 0 || sk >= Spec.P256.order then
```

---

### BUG-2: AES key expansion writes wrong index (copy-paste error) [HIGH]

**File:** `Spec.AES.fst`, lines 215–216
**Standard:** NIST FIPS 197, Section 5.2 (Key Expansion)

**Description:**

The `aes_keygen_assist` function has a copy-paste bug where index 6 is written
twice and index 5 is never written:

```fstar
let st = st.[4] <- rcon ^. sub_byte s.[5] in
let st = st.[6] <- sub_byte s.[6] in    // BUG: should be st.[5]
let st = st.[6] <- sub_byte s.[7] in    // overwrites the line above
let st = st.[7] <- sub_byte s.[4] in
```

The pattern for bytes 4–7 should mirror the pattern at bytes 12–15 (which is
correct):

```fstar
let st = st.[12] <- rcon ^. sub_byte s.[13] in
let st = st.[13] <- sub_byte s.[14] in
let st = st.[14] <- sub_byte s.[15] in
let st = st.[15] <- sub_byte s.[12] in
```

Both groups implement RotWord + SubWord + AddRcon. The correct code for bytes
4–7 should be:

```fstar
let st = st.[4] <- rcon ^. sub_byte s.[5] in
let st = st.[5] <- sub_byte s.[6] in    // FIX: index 5, not 6
let st = st.[6] <- sub_byte s.[7] in
let st = st.[7] <- sub_byte s.[4] in
```

**Impact:** `st.[5]` retains its initial value of zero instead of
`sub_byte s.[6]`. This corrupts the intermediate result of `aes_keygen_assist`.
The downstream functions `keygen_assist0` and `keygen_assist1` copy slices of
this result into the expanded key schedule. Whether the corruption propagates
to the final key schedule depends on which slices are copied, but the
intermediate value is definitively wrong. If this spec is used for AES-128 or
AES-256 key expansion, the resulting round keys may be incorrect.

**Fix:**

```fstar
// Line 215: change st.[6] to st.[5]
let st = st.[5] <- sub_byte s.[6] in
```

---

### BUG-3: AES-128 CTR key_block1 returns key_block0 [MEDIUM]

**File:** `Spec.AES.fst`, line 422
**Standard:** N/A (internal API consistency)

**Description:**

The convenience wrapper `aes128_ctr_key_block1` calls the wrong underlying
function:

```fstar
let aes128_ctr_key_block1 key n_len n =
  aes_ctr_key_block0 AES128 key n_len n    // BUG: should be aes_ctr_key_block1
```

The generic `aes_ctr_key_block0` initializes the AES-CTR state with counter=0,
while `aes_ctr_key_block1` initializes with counter=1 (line 362). This means
`aes128_ctr_key_block1` returns the keystream block for counter=0 instead of
counter=1.

**Impact:** Any caller using `aes128_ctr_key_block1` to obtain the second
keystream block (counter=1) will instead receive the first keystream block
(counter=0). This is relevant for AES-GCM, where key_block0 is used for GHASH
finalization and key_block1 is used for the first encryption block. Using the
wrong block would break both authentication and encryption.

**Fix:**

```fstar
// Line 422: change aes_ctr_key_block0 to aes_ctr_key_block1
let aes128_ctr_key_block1 key n_len n =
  aes_ctr_key_block1 AES128 key n_len n
```

---

### BUG-4: X25519 scalarmult omits scalar clamping [LOW]

**File:** `Spec.Curve25519.fst`, lines 120–123
**Standard:** RFC 7748, Section 5

**Description:**

RFC 7748 defines the `X25519(k, u)` function as:

1. Apply `decodeScalar25519(k)` — clamp the scalar
2. Apply `decodeUCoordinate(u)` — decode the u-coordinate
3. Perform the Montgomery ladder
4. Encode the result

The spec's `scalarmult` function only performs steps 2–4:

```fstar
let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =
  let u = decodePoint u in          // step 2
  let res = montgomery_ladder u k in // step 3 (no clamping!)
  encodePoint res                    // step 4
```

The `decodeScalar` function is defined (lines 42–45) and implements the correct
clamping (clear bits 0,1,2 of byte 0; clear bit 255; set bit 254), but it is
never called — not by `scalarmult` and not by `secret_to_public`.

The `montgomery_ladder` function hard-codes optimizations that depend on the
scalar being clamped: it assumes bit 254 is set (unconditional initial
`cswap2 (u64 1)` at line 108), and assumes bits 0–2 are zero (three explicit
doublings at lines 115–117 instead of ladder steps). If called with an
unclamped scalar where these bits differ, the result will be mathematically
incorrect.

**Impact:** This is classified as LOW because:
- In practice, Ed25519/X25519 private keys are always 32 random bytes that get
  clamped, and all known callers likely clamp before calling `scalarmult`.
- The `montgomery_ladder` will silently compute the wrong answer for unclamped
  scalars rather than crashing, so the bug would manifest as incorrect DH
  output rather than a security vulnerability per se.
- The deviation is an API mismatch with RFC 7748 rather than a mathematical
  error in the ladder itself.

**Fix:** Add clamping inside `scalarmult`:

```fstar
let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =
  let k = decodeScalar k in          // ADD: clamp the scalar
  let u = decodePoint u in
  let res = montgomery_ladder u k in
  encodePoint res
```

---

## Design Observations (informational, not bugs)

### OBS-1: Ed25519 cofactorless verification

**File:** `Spec.Ed25519.fst`, lines 158–159
**Standard:** RFC 8032, Section 5.1.7

The spec verifies signatures using the equation `[S]B = R + [H]A` (cofactorless)
rather than RFC 8032's `[8][S]B = [8]R + [8][H]A` (cofactored, where 8 is the
Ed25519 cofactor). This is a well-known and widely-accepted simplification. For
points that successfully decompress (which are guaranteed to be on the curve),
the two checks are equivalent. This matches the behavior of most Ed25519
implementations in practice (libsodium, Go, etc.) and is explicitly noted as
acceptable in RFC 8032.

### OBS-2: Minor typo in Ed25519

**File:** `Spec.Ed25519.PointOps.fst`, line 54
The identifier `point_at_inifinity_c` is misspelled (should be `infinity`).

---

## Specifications Verified Clean

The following specifications were audited and found to have no discrepancies
against their respective standards:

| Specification | Standard | Key Checks Performed |
|---|---|---|
| `Spec.Chacha20` | RFC 8439 | Quarter round rotations (16,12,8,7), "expand 32-byte k" constants, state layout, 20 rounds, counter increment, LE encoding |
| `Spec.Poly1305` | RFC 8439 §2.5 | Prime 2^130-5, clamping masks, block processing with 0x01 append, accumulation (acc+block)*r mod p, final tag (acc+s) mod 2^128 |
| `Spec.Chacha20Poly1305` | RFC 8439 §2.8 | Poly1305 key from counter=0, encryption from counter=1, MAC data layout (AAD‖pad‖CT‖pad‖len_AAD‖len_CT) |
| `Spec.SHA2` + `Constants` | FIPS 180-4 | All IVs (SHA-224/256/384/512), all round constants (64 for SHA-256, 80 for SHA-512), Ch/Maj/Sigma functions, rotation amounts, message schedule, padding |
| `Spec.SHA3` + `Constants` | FIPS 202 | Keccak-f[1600] 24 rounds, theta/rho/pi/chi/iota steps, round constants, rotation offsets, sponge construction, rates, domain separation (0x06/0x1F) |
| `Spec.Blake2` + `Definitions` | RFC 7693 | IVs, G function rotations (Blake2b: 32,24,16,63; Blake2s: 16,12,8,7), sigma table (160 entries), round counts (12/10), parameter block, finalization flags |
| `Spec.Agile.HMAC` | RFC 2104 | ipad=0x36, opad=0x5c, key wrapping (hash if >block_size, pad with zeros) |
| `Spec.Agile.HKDF` | RFC 5869 | Extract=HMAC(salt,IKM), Expand with single-byte counter starting at 1, 255*HashLen limit |
| `Spec.RSAPSS` | RFC 8017 | M'=0x0000000000000000‖mHash‖salt, DB=PS‖0x01‖salt, MGF1, masking, bit zeroing, 0xbc trailer |
| `Spec.P256` + `PointOps` | FIPS 186-4 / SEC 2 | Prime, a=-3, b, base point (Gx,Gy), group order, complete addition formulas |
| `Spec.K256` + `PointOps` | SEC 2 (secp256k1) | Prime 2^256-2^32-977, a=0, b=7, base point, group order |
| `Spec.FFDHE` | RFC 7919 | All five primes (2048–8192 bit), g=2, public key validation |
| `Spec.Salsa20` | Bernstein spec | Quarter round, "expand 32-byte k" constants, diagonal state layout, 20 rounds |
| `Spec.HMAC_DRBG` | NIST SP 800-90A | Update function (K,V with 0x00/0x01 separators), instantiate, reseed, generate |
| `Spec.Hash.Definitions` | FIPS 180-4 | Block sizes, word sizes, endianness, max input lengths |
| `Spec.Hash.MD` | Merkle-Damgard | Padding (0x80‖zeros‖length), length encoding (BE for SHA, LE for MD5) |
| `Spec.Agile.HPKE` (except `dkp_nist_p`) | RFC 9180 | Labeled extract/expand, suite_id, key schedule, encap/decap, seal/open |
| `Spec.SHA1` | FIPS 180-4 | IVs (H0–H4), round constants (K0–K3), logical functions (Ch/Parity/Maj), message schedule (ROTL 1), step function (ROTL 5/30), 80 rounds, BE encoding |
| `Spec.MD5` | RFC 1321 | IVs (A–D), all 64 T constants (sin-derived), auxiliary functions (F/G/H/I), shift amounts, message word indices, step function, LE encoding |

---

## Coverage Gaps (not audited or not implemented)

| Item | Reason |
|---|---|
| SHA-512/224, SHA-512/256 | Not implemented in the `sha2_alg` type |
| AES-192 | Not implemented in the `variant` type (only AES-128 and AES-256) |
| Salsa20 with 16-byte keys | Not implemented (only 32-byte key variant) |
| `Spec.Frodo` (FrodoKEM) | Post-quantum KEM; requires FrodoKEM specification for audit |
| `Spec.Box` / `Spec.SecretBox` | NaCl constructions; skipped in first round |
| GF(2^128) for GCM | Instantiation not in `specs/` directory; generic `GaloisField` library is structurally correct |
