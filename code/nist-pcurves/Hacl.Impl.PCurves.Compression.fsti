module Hacl.Impl.PCurves.Compression

open FStar.Mul
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.PCurves

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val uncompressed_to_raw: {| cp:S.curve_params |} -> pk:lbuffer uint8 (1ul +. 2ul *. size cp.bytes) ->
                         pk_raw:lbuffer uint8 (2ul *. size cp.bytes) -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_uncompressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_uncompressed_to_raw (as_seq h0 pk)))))


inline_for_extraction noextract
val compressed_to_raw: {| cp:S.curve_params |} -> pk:lbuffer uint8 (1ul +. size cp.bytes) ->
                       pk_raw:lbuffer uint8 (2ul *. size cp.bytes) -> Stack bool
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 b h1 -> modifies (loc pk_raw) h0 h1 /\
    (b <==> Some? (S.pk_compressed_to_raw (as_seq h0 pk))) /\
    (b ==> (as_seq h1 pk_raw == Some?.v (S.pk_compressed_to_raw (as_seq h0 pk)))))


inline_for_extraction noextract
val raw_to_uncompressed: {| cp:S.curve_params |} -> pk_raw:lbuffer uint8 (2ul *. size cp.bytes) ->
                         pk:lbuffer uint8 (1ul +. 2ul *. size cp.bytes) -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_uncompressed_from_raw (as_seq h0 pk_raw))


inline_for_extraction noextract
val raw_to_compressed: {| cp:S.curve_params |} -> pk_raw:lbuffer uint8 (2ul *. size cp.bytes) ->
                       pk:lbuffer uint8 (1ul +. size cp.bytes) -> Stack unit
  (requires fun h -> live h pk /\ live h pk_raw /\ disjoint pk pk_raw)
  (ensures  fun h0 _ h1 -> modifies (loc pk) h0 h1 /\
    as_seq h1 pk == S.pk_compressed_from_raw (as_seq h0 pk_raw))
