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

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

open EverCrypt.Helpers

let key_and_data_fits (a: hash_alg): Lemma
  (ensures (block_length a + pow2 32 <= max_input_length a))
=
  let open FStar.Integers in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

inline_for_extraction
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
  a: hash_alg ->
  hash: D.hash_st a ->
  alloca: D.alloca_st a ->
  init: D.init_st a ->
  update_multi: D.update_multi_st a ->
  update_last: D.update_last_st a ->
  finish: D.finish_st a ->
  compute_st a

val compute_sha2_256: compute_st SHA2_256
