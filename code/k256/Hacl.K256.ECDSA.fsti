module Hacl.K256.ECDSA

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

module S = Spec.K256
module BSeq = Lib.ByteSequence

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
let lbytes len = lbuffer uint8 len

///  ECDSA without low-S normalization

[@@ CPrologue
"/*******************************************************************************
  Verified C library for ECDSA signing and verification on the secp256k1 curve.

  For the comments on low-S normalization (or canonical lowest S value), see:
    • https://en.bitcoin.it/wiki/BIP_0062
    • https://yondon.blog/2019/01/01/how-not-to-use-ecdsa/
    • https://eklitzke.org/bitcoin-transaction-malleability

  For example, bitcoin-core/secp256k1 *always* performs low-S normalization.

*******************************************************************************/\n";

Comment "Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve"]
val ecdsa_sign_hashed_msg (signature:lbytes 64ul)
  (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


[@@ Comment "Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_sign_hashed_msg`.

  The function DOESN'T perform low-S normalization, see `secp256k1_ecdsa_sign_sha256` if needed."]
val ecdsa_sign_sha256 (signature:lbytes 64ul)
  (msg_len:size_t) (msg:lbytes msg_len) (private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


[@@ Comment "Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_hashed_msg` if needed.

  The function also checks whether `public key` is valid."]
val ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))


[@@ Comment "Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `ecdsa_verify_hashed_msg`.

  The function ACCEPTS non low-S normalized signatures, see `secp256k1_ecdsa_verify_sha256` if needed."]
val ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 signature))


///  Low-S normalization used in bitcoin-core/secp256k1

[@@ Comment "Compute canonical lowest S value for `signature` (R || S).

  The function returns `true` for successful normalization of S and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64]."]
val secp256k1_ecdsa_signature_normalize: signature: lbytes 64ul -> Stack bool
  (requires fun h -> live h signature)
  (ensures  fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_signature_normalize (as_seq h0 signature) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


[@@ Comment "Check whether `signature` (R || S) is in canonical form.

  The function returns `true` if S is low-S normalized and `false` otherwise.

  The argument `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64]."]
val secp256k1_ecdsa_is_signature_normalized: signature: lbytes 64ul -> Stack bool
  (requires fun h -> live h signature)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_is_signature_normalized (as_seq h0 signature))


[@@ Comment "Create an ECDSA signature.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The arguments `msgHash`, `private_key`, and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed.

  The function also checks whether `private_key` and `nonce` are valid:
    • 0 < `private_key` < the order of the curve
    • 0 < `nonce` < the order of the curve"]
val secp256k1_ecdsa_sign_hashed_msg (signature:lbytes 64ul)
  (msgHash private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msgHash /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_sign_hashed_msg (as_seq h0 msgHash) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


[@@ Comment "Create an ECDSA signature using SHA2-256.

  The function returns `true` for successful creation of an ECDSA signature and `false` otherwise.

  The outparam `signature` (R || S) points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `private_key` and `nonce` point to 32 bytes of valid memory, i.e., uint8_t[32].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_sign_hashed_msg`.

  The function ALWAYS performs low-S normalization, see `ecdsa_sign_hashed_msg` if needed."]
val secp256k1_ecdsa_sign_sha256 (signature:lbytes 64ul)
  (msg_len:size_t) (msg:lbytes msg_len) (private_key nonce:lbytes 32ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h private_key /\ live h nonce /\ live h signature /\
    disjoint signature msg /\ disjoint signature private_key /\ disjoint signature nonce)
  (ensures fun h0 b h1 -> modifies (loc signature) h0 h1 /\
    (let sgnt = S.secp256k1_ecdsa_sign_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 private_key) (as_seq h0 nonce) in
    (b <==> Some? sgnt) /\ (b ==> (as_seq h1 signature == Some?.v sgnt))))


[@@ Comment "Verify an ECDSA signature.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msgHash` points to 32 bytes of valid memory, i.e., uint8_t[32].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_hashed_msg` if needed.

  The function also checks whether `public_key` is valid"]
val secp256k1_ecdsa_verify_hashed_msg (msgHash:lbytes 32ul) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msgHash /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_verify_hashed_msg (as_seq h0 msgHash) (as_seq h0 public_key) (as_seq h0 signature))


[@@ Comment "Verify an ECDSA signature using SHA2-256.

  The function returns `true` if the signature is valid and `false` otherwise.

  The argument `msg` points to `msg_len` bytes of valid memory, i.e., uint8_t[msg_len].
  The arguments `public_key` (x || y) and `signature` (R || S) point to 64 bytes of valid memory, i.e., uint8_t[64].

  The function first hashes a message `msg` with SHA2-256 and then calls `secp256k1_ecdsa_verify_hashed_msg`.

  The function DOESN'T accept non low-S normalized signatures, see `ecdsa_verify_sha256` if needed."]
val secp256k1_ecdsa_verify_sha256 (msg_len:size_t) (msg:lbytes msg_len) (public_key signature:lbytes 64ul) : Stack bool
  (requires fun h ->
    live h msg /\ live h public_key /\ live h signature)
  (ensures fun h0 b h1 -> modifies0 h0 h1 /\
    b == S.secp256k1_ecdsa_verify_sha256 (v msg_len) (as_seq h0 msg) (as_seq h0 public_key) (as_seq h0 signature))


[@@ CPrologue
"/*******************************************************************************
  Parsing and Serializing public keys.

  A public key is a point (x, y) on the secp256k1 curve.

  The point can be represented in the following three ways.
    • raw          = [ x || y ], 64 bytes
    • uncompressed = [ 0x04 || x || y ], 65 bytes
    • compressed   = [ (0x02 for even `y` and 0x03 for odd `y`) || x ], 33 bytes

*******************************************************************************/\n";

 Comment "Convert a public key from uncompressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].

  The function DOESN'T check whether (x, y) is valid point."]
val public_key_uncompressed_to_raw: pk_raw:lbytes 64ul -> pk:lbytes 65ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))


[@@ Comment "Convert a public key from raw to its uncompressed form.

  The outparam `pk` points to 65 bytes of valid memory, i.e., uint8_t[65].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point."]
val public_key_uncompressed_from_raw: pk:lbytes 65ul -> pk_raw:lbytes 64ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


[@@ Comment "Convert a public key from compressed to its raw form.

  The function returns `true` for successful conversion of a public key and `false` otherwise.

  The outparam `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].

  The function also checks whether (x, y) is valid point."]
val public_key_compressed_to_raw: pk_raw:lbytes 64ul -> pk:lbytes 33ul -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))


[@@ Comment "Convert a public key from raw to its compressed form.

  The outparam `pk` points to 33 bytes of valid memory, i.e., uint8_t[33].
  The argument `pk_raw` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The function DOESN'T check whether (x, y) is valid point."]
val public_key_compressed_from_raw: pk:lbytes 33ul -> pk_raw:lbytes 64ul -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))


[@@ CPrologue "
/******************/
/* Key validation */
/******************/";

Comment "Public key validation.

  The function returns `true` if a public key is valid and `false` otherwise.

  The argument `public_key` points to 64 bytes of valid memory, i.e., uint8_t[64].

  The public key (x || y) is valid (with respect to SP 800-56A):
    • the public key is not the “point at infinity”, represented as O.
    • the affine x and y coordinates of the point represented by the public key are
      in the range [0, p – 1] where p is the prime defining the finite field.
    • y^2 = x^3 + ax + b where a and b are the coefficients of the curve equation.
  The last extract is taken from: https://neilmadden.blog/2017/05/17/so-how-do-you-validate-nist-ecdh-public-keys/"]
val is_public_key_valid: public_key:lbytes 64ul -> Stack bool
  (requires fun h -> live h public_key)
  (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
    b <==> S.validate_public_key (as_seq h0 public_key))


[@@ Comment "Private key validation.

  The function returns `true` if a private key is valid and `false` otherwise.

  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve"]
val is_private_key_valid: private_key:lbuffer uint8 32ul -> Stack bool
  (requires fun h -> live h private_key)
  (ensures  fun h0 r h1 -> modifies0 h0 h1 /\
    (let s = BSeq.nat_from_bytes_be (as_seq h0 private_key) in
    r <==> (0 < s && s < S.q)))


[@@ CPrologue "
/******************/
/* ECDH agreement */
/******************/";

Comment "Compute the public key from the private key.

  The function returns `true` if a private key is valid and `false` otherwise.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The private key is valid:
    • 0 < `private_key` < the order of the curve."]
val secret_to_public: public_key:lbytes 64ul -> private_key:lbytes 32ul -> Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\
    disjoint public_key private_key)
  (ensures fun h0 b h1 -> modifies (loc public_key) h0 h1 /\
    (let public_key_s = S.secret_to_public (as_seq h0 private_key) in
    (b <==> Some? public_key_s) /\ (b ==> (as_seq h1 public_key == Some?.v public_key_s))))


[@@ Comment "Execute the diffie-hellmann key exchange.

  The function returns `true` for successful creation of an ECDH shared secret and
  `false` otherwise.

  The outparam `shared_secret` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `their_pubkey` points to 64 bytes of valid memory, i.e., uint8_t[64].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t[32].

  The function also checks whether `private_key` and `their_pubkey` are valid."]
val ecdh:
    shared_secret:lbuffer uint8 64ul
  -> their_pubkey:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (let ss = S.ecdh (as_seq h0 their_pubkey) (as_seq h0 private_key) in
    (r <==> Some? ss) /\ (r ==> (as_seq h1 shared_secret == Some?.v ss))))
