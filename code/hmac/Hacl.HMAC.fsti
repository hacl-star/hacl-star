module Hacl.HMAC

/// A generic, meta-programmed HMAC module. This one provides one concrete
/// instantiation, namely HMAC-SHA2-256 instantiated with the HACL*
/// implementation. In the future, this module may provide more implementations
/// of HMAC, using optimized HACL versions of SHA2-256. For more algorithms, and
/// for an assembly-optimized HMAC version that may call into Vale, see
/// EverCrypt.HMAC.

module B = LowStar.Buffer
module D = Hacl.Hash.Definitions

open Spec.Agile.HMAC
open Spec.Hash.Definitions
open FStar.HyperStack.ST
open Lib.IntTypes

open EverCrypt.Helpers

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

let key_and_data_fits (a: hash_alg): Lemma
  (ensures (block_length a + pow2 32 <= max_input_length a))
=
  let open FStar.Integers in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

inline_for_extraction noextract
let compute_st (a: hash_alg) =
  tag: B.buffer uint8 {B.length tag == hash_length a} ->
  key: B.buffer uint8{ keysized a (B.length key) /\ B.disjoint key tag } ->
  keylen: UInt32.t{ UInt32.v keylen = B.length key } ->
  data: B.buffer uint8{ B.length data + block_length a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = B.length data } ->
  Stack unit
  (requires fun h0 -> B.live h0 tag /\ B.live h0 key /\ B.live h0 data)
  (ensures fun h0 _ h1 ->
    key_and_data_fits a;
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\
    B.as_seq h1 tag == hmac a (B.as_seq h0 key) (B.as_seq h0 data))

inline_for_extraction noextract
val mk_compute:
  i: D.impl ->
  hash: D.hash_st (D.get_alg i) ->
  alloca: D.alloca_st i ->
  init: D.init_st i ->
  update_multi: D.update_multi_st i ->
  update_last: D.update_last_st i ->
  finish: D.finish_st i ->
  compute_st (D.get_alg i)

val legacy_compute_sha1: compute_st SHA1

val compute_sha2_256: compute_st SHA2_256

val compute_sha2_384: compute_st SHA2_384

val compute_sha2_512: compute_st SHA2_512

val compute_blake2s_32: compute_st Blake2S

val compute_blake2b_32: compute_st Blake2B
