module Hacl.FFDHE

open Lib.IntTypes

module S = Spec.FFDHE
module DH = Hacl.Impl.FFDHE
module BD = Hacl.Bignum.Definitions
module BE = Hacl.Bignum.Exponentiation

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let t_limbs = U64

inline_for_extraction noextract
let ke (a:S.ffdhe_alg) =
  BE.mk_runtime_exp #t_limbs (BD.blocks (DH.ffdhe_len a) (size (numbytes t_limbs)))

private
[@CInline]
let ffdhe_precomp_p (a:S.ffdhe_alg) : DH.ffdhe_precomp_p_st t_limbs a (DH.ffdhe_len a) (ke a) =
  DH.ffdhe_precomp_p a (DH.ffdhe_len a) (ke a)

private
[@CInline]
let ffdhe_check_pk (a:S.ffdhe_alg) : DH.ffdhe_check_pk_st t_limbs a (DH.ffdhe_len a) =
  DH.ffdhe_check_pk #t_limbs a (DH.ffdhe_len a)

private
[@CInline]
let ffdhe_compute_exp (a:S.ffdhe_alg) : DH.ffdhe_compute_exp_st t_limbs a (DH.ffdhe_len a) (ke a) =
  DH.ffdhe_compute_exp a (DH.ffdhe_len a) (ke a)


[@@ Comment "Return the byte length of FFDHE parameters for the given algorithm.

@param a The FFDHE algorithm (FFDHE2048=256, FFDHE3072=384, FFDHE4096=512, FFDHE6144=768, FFDHE8192=1024 bytes)."]
let ffdhe_len (a:S.ffdhe_alg) : DH.size_pos = DH.ffdhe_len a


[@@ Comment "Allocate and precompute Montgomery context for the FFDHE prime.

The caller must `free()` the returned pointer when done.

@param a The FFDHE algorithm.
@return A pointer to the precomputed context, or NULL on allocation failure."]
val new_ffdhe_precomp_p: a:S.ffdhe_alg ->
  DH.new_ffdhe_precomp_p_st t_limbs a (ffdhe_len a) (ke a)
let new_ffdhe_precomp_p a =
  DH.new_ffdhe_precomp_p a (DH.ffdhe_len a) (ke a) (ffdhe_precomp_p a)


[@@ Comment "INTERNAL. Compute a public key from a secret key using a precomputed context.

This is a low-level function intended for internal use.

The secret key `sk` must represent a value strictly greater than 1 (big-endian).
Both `sk` and `pk` must point to `ffdhe_len(a)` bytes of memory.

@param a The FFDHE algorithm.
@param p_r2_n Precomputed Montgomery context from `new_ffdhe_precomp_p`.
@param sk Pointer to `ffdhe_len(a)` bytes where the secret key is read from.
@param pk Pointer to `ffdhe_len(a)` bytes where the public key is written to."]
val ffdhe_secret_to_public_precomp: a:S.ffdhe_alg ->
  DH.ffdhe_secret_to_public_precomp_st t_limbs a (DH.ffdhe_len a) (ke a)
let ffdhe_secret_to_public_precomp a p_r2_n sk pk =
  let len = DH.ffdhe_len a in
  DH.ffdhe_secret_to_public_precomp a len (ke a) (ffdhe_compute_exp a) p_r2_n sk pk


[@@ Comment "Compute a public key from a secret key.

The secret key `sk` must represent a value strictly greater than 1 (big-endian).
Both `sk` and `pk` must point to `ffdhe_len(a)` bytes of memory and must not overlap.

@param a The FFDHE algorithm.
@param sk Pointer to `ffdhe_len(a)` bytes where the secret key is read from.
@param pk Pointer to `ffdhe_len(a)` bytes where the public key is written to."]
val ffdhe_secret_to_public: a:S.ffdhe_alg ->
  DH.ffdhe_secret_to_public_st t_limbs a (DH.ffdhe_len a) (ke a)
let ffdhe_secret_to_public a sk pk =
  let len = DH.ffdhe_len a in
  DH.ffdhe_secret_to_public a len (ke a) (ffdhe_secret_to_public_precomp a) (ffdhe_precomp_p a) sk pk


[@@ Comment "INTERNAL. Compute a shared secret using a precomputed context.

This is a low-level function intended for internal use.

The secret key `sk` must represent a value strictly greater than 1 (big-endian).
The public key `pk` is validated internally (1 < pk < p-1).
All of `sk`, `pk`, and `ss` must point to `ffdhe_len(a)` bytes and must not overlap.

Returns `ones` on success (valid peer public key) or `0` on failure.

@param a The FFDHE algorithm.
@param p_r2_n Precomputed Montgomery context from `new_ffdhe_precomp_p`.
@param sk Pointer to `ffdhe_len(a)` bytes where the secret key is read from.
@param pk Pointer to `ffdhe_len(a)` bytes where the peer's public key is read from.
@param ss Pointer to `ffdhe_len(a)` bytes where the shared secret is written to."]
val ffdhe_shared_secret_precomp: a:S.ffdhe_alg ->
  DH.ffdhe_shared_secret_precomp_st t_limbs a (DH.ffdhe_len a) (ke a)
let ffdhe_shared_secret_precomp a p_r2_n sk pk ss =
  let len = DH.ffdhe_len a in
  DH.ffdhe_shared_secret_precomp a len (ke a) (ffdhe_check_pk a) (ffdhe_compute_exp a) p_r2_n sk pk ss


[@@ Comment "Compute the FFDHE shared secret from a secret key and the peer's public key.

The secret key `sk` must represent a value strictly greater than 1 (big-endian).
The public key `pk` is validated internally (1 < pk < p-1).
All of `sk`, `pk`, and `ss` must point to `ffdhe_len(a)` bytes and must not overlap.

Returns `ones` on success (valid peer public key) or `0` on failure (invalid public key).

@param a The FFDHE algorithm.
@param sk Pointer to `ffdhe_len(a)` bytes where the secret key is read from.
@param pk Pointer to `ffdhe_len(a)` bytes where the peer's public key is read from.
@param ss Pointer to `ffdhe_len(a)` bytes where the shared secret is written to."]
val ffdhe_shared_secret: a:S.ffdhe_alg ->
  DH.ffdhe_shared_secret_st t_limbs a (DH.ffdhe_len a) (ke a)
let ffdhe_shared_secret a sk pk ss =
  let len = DH.ffdhe_len a in
  DH.ffdhe_shared_secret a len (ke a) (ffdhe_shared_secret_precomp a) (ffdhe_precomp_p a) sk pk ss
