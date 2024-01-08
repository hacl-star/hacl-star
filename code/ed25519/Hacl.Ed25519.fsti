module Hacl.Ed25519

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

[@@ CPrologue
"/********************************************************************************
  Verified C library for EdDSA signing and verification on the edwards25519 curve.
********************************************************************************/\n";

Comment "Compute the public key from the private key.

  @param[out] public_key Points to 32 bytes of valid memory, i.e., `uint8_t[32]`. Must not overlap the memory location of `private_key`.
  @param[in] private_key Points to 32 bytes of valid memory containing the private key, i.e., `uint8_t[32]`."]
val secret_to_public:
    public_key:lbuffer uint8 32ul
  -> private_key:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h public_key /\ live h private_key /\ disjoint public_key private_key)
    (ensures  fun h0 _ h1 -> modifies (loc public_key) h0 h1 /\
      as_seq h1 public_key == Spec.Ed25519.secret_to_public (as_seq h0 private_key))


[@@ Comment "Compute the expanded keys for an Ed25519 signature.

  @param[out] expanded_keys Points to 96 bytes of valid memory, i.e., `uint8_t[96]`. Must not overlap the memory location of `private_key`.
  @param[in] private_key Points to 32 bytes of valid memory containing the private key, i.e., `uint8_t[32]`.

  If one needs to sign several messages under the same private key, it is more efficient
  to call `expand_keys` only once and `sign_expanded` multiple times, for each message."]
val expand_keys:
    expanded_keys:lbuffer uint8 96ul
  -> private_key:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h expanded_keys /\ live h private_key /\ disjoint expanded_keys private_key)
    (ensures  fun h0 _ h1 -> modifies (loc expanded_keys) h0 h1 /\
     (let public_key, s, prefix = Spec.Ed25519.expand_keys (as_seq h0 private_key) in
      as_seq h1 (gsub expanded_keys 0ul 32ul) == public_key /\
      as_seq h1 (gsub expanded_keys 32ul 32ul) == s /\
      as_seq h1 (gsub expanded_keys 64ul 32ul) == prefix))


[@@ Comment "Create an Ed25519 signature with the (precomputed) expanded keys.

  @param[out] signature Points to 64 bytes of valid memory, i.e., `uint8_t[64]`. Must not overlap the memory locations of `expanded_keys` nor `msg`.
  @param[in] expanded_keys Points to 96 bytes of valid memory, i.e., `uint8_t[96]`, containing the expanded keys obtained by invoking `expand_keys`.
  @param[in] msg_len Length of `msg`.
  @param[in] msg Points to `msg_len` bytes of valid memory containing the message, i.e., `uint8_t[msg_len]`.

  If one needs to sign several messages under the same private key, it is more efficient
  to call `expand_keys` only once and `sign_expanded` multiple times, for each message."]
val sign_expanded:
    signature:lbuffer uint8 64ul
  -> expanded_keys:lbuffer uint8 96ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h expanded_keys /\
      disjoint signature msg /\ disjoint signature expanded_keys)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub expanded_keys 0ul 32ul))
        (as_seq h0 (gsub expanded_keys 32ul 32ul))
        (as_seq h0 (gsub expanded_keys 64ul 32ul))
        (as_seq h0 msg))


[@@ Comment "Create an Ed25519 signature.

  @param[out] signature Points to 64 bytes of valid memory, i.e., `uint8_t[64]`. Must not overlap the memory locations of `private_key` nor `msg`.
  @param[in] private_key Points to 32 bytes of valid memory containing the private key, i.e., `uint8_t[32]`.
  @param[in] msg_len Length of `msg`.
  @param[in] msg Points to `msg_len` bytes of valid memory containing the message, i.e., `uint8_t[msg_len]`.

  The function first calls `expand_keys` and then invokes `sign_expanded`.

  If one needs to sign several messages under the same private key, it is more efficient
  to call `expand_keys` only once and `sign_expanded` multiple times, for each message."]
val sign:
    signature:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h private_key /\
      disjoint signature msg /\ disjoint signature private_key)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 private_key) (as_seq h0 msg))


[@@ Comment "Verify an Ed25519 signature.

  @param public_key Points to 32 bytes of valid memory containing the public key, i.e., `uint8_t[32]`.
  @param msg_len Length of `msg`.
  @param msg Points to `msg_len` bytes of valid memory containing the message, i.e., `uint8_t[msg_len]`.
  @param signature Points to 64 bytes of valid memory containing the signature, i.e., `uint8_t[64]`.

  @return Returns `true` if the signature is valid and `false` otherwise."]
val verify:
    public_key:lbuffer uint8 32ul
  -> msg_len:size_t
  -> msg:lbuffer uint8 msg_len
  -> signature:lbuffer uint8 64ul ->
  Stack bool
    (requires fun h -> live h public_key /\ live h msg /\ live h signature)
    (ensures  fun h0 b h1 -> modifies0 h0 h1 /\
      b == Spec.Ed25519.verify (as_seq h0 public_key) (as_seq h0 msg) (as_seq h0 signature))
