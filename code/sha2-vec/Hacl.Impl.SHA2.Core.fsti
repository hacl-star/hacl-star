module Hacl.Impl.SHA2.Core

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Spec.SHA2.Vec

module SpecVec = Hacl.Spec.SHA2.Vec

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

unfold
let state_t (a:sha2_alg) (m:m_spec) =
  lbuffer (element_t a m) 8ul

inline_for_extraction noextract
let init_vec_t (a:sha2_alg) (m:m_spec) = hash:state_t a m ->
  Stack unit
  (requires fun h -> live h hash)
  (ensures  fun h0 _ h1 -> modifies1 hash h0 h1 /\
    as_seq h1 hash == SpecVec.init a m)

inline_for_extraction noextract
val init: #a:sha2_alg -> #m:m_spec -> init_vec_t a m


inline_for_extraction noextract
let update_vec_t (a:sha2_alg) (m:m_spec) =
    b:multibuf (lanes a m) (block_len a)
  -> hash:state_t a m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h hash)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == SpecVec.update (as_seq_multi h0 b) (as_seq h0 hash))

inline_for_extraction noextract
val update: #a:sha2_alg -> #m:m_spec -> update_vec_t a m


inline_for_extraction noextract
let update_last_vec_t (a:sha2_alg) (m:m_spec) =
    upd:update_vec_t a m
  -> totlen:len_t a
  -> len:size_t{v len < block_length a}
  -> b:multibuf (lanes a m) len
  -> hash:state_t a m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h hash /\ disjoint_multi b hash)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == SpecVec.update_last totlen (v len) (as_seq_multi h0 b) (as_seq h0 hash))

inline_for_extraction noextract
val update_last: #a:sha2_alg -> #m:m_spec -> update_last_vec_t a m


noextract
let preserves_disjoint_multi #lanes #len #len' (b:multibuf lanes len) (r:multibuf lanes len') =
    (forall a l (x:lbuffer a l). disjoint_multi b x ==> disjoint_multi r x)

inline_for_extraction noextract
let get_multiblock_t (a:sha2_alg) (m:m_spec) =
    len:size_t
  -> b:multibuf (lanes a m) len
  -> i:size_t{v i < v len / block_length a} ->
  Stack (multibuf (lanes a m) (block_len a))
  (requires fun h -> live_multi h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\ live_multi h1 r /\ preserves_disjoint_multi b r /\
    as_seq_multi h1 r == SpecVec.get_multiblock_spec (v len) (as_seq_multi h0 b) (v i))

inline_for_extraction noextract
val get_multiblock: #a:sha2_alg -> #m:m_spec -> get_multiblock_t a m


inline_for_extraction noextract
let get_multilast_t (a:sha2_alg) (m:m_spec) =
    len:size_t
  -> b:multibuf (lanes a m) len ->
  Stack (multibuf (lanes a m) (len %. block_len a))
  (requires fun h -> live_multi h b)
  (ensures  fun h0 r h1 -> h0 == h1 /\ live_multi h1 r /\ preserves_disjoint_multi b r /\
    as_seq_multi h1 r == SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h0 b))

inline_for_extraction noextract
val get_multilast: #a:sha2_alg -> #m:m_spec -> get_multilast_t a m


inline_for_extraction noextract
let update_nblocks_vec_t (a:sha2_alg) (m:m_spec) =
    upd:update_vec_t a m
  -> len:size_t
  -> b:multibuf (lanes a m) len
  -> st:state_t a m ->
  Stack unit
  (requires fun h0 -> live_multi h0 b /\ live h0 st /\ disjoint_multi b st)
  (ensures  fun h0 _ h1 -> modifies (loc st) h0 h1 /\
    as_seq h1 st == SpecVec.update_nblocks #a #m (v len) (as_seq_multi h0 b) (as_seq h0 st))

inline_for_extraction noextract
val update_nblocks: #a:sha2_alg -> #m:m_spec -> update_nblocks_vec_t a m


inline_for_extraction noextract
let finish_vec_t (a:sha2_alg) (m:m_spec) =
    st:state_t a m
  -> h:multibuf (lanes a m) (hash_len a) ->
  Stack unit
  (requires fun h0 -> live_multi h0 h /\ internally_disjoint h /\ live h0 st /\ disjoint_multi h st)
  (ensures  fun h0 _ h1 -> modifies (loc_multi h |+| loc st) h0 h1 /\
    as_seq_multi h1 h == SpecVec.finish #a #m (as_seq h0 st))

inline_for_extraction noextract
val finish: #a:sha2_alg -> #m:m_spec -> finish_vec_t a m


inline_for_extraction noextract
let hash_vec_t (a:sha2_alg) (m:m_spec) =
    upd:update_vec_t a m
  -> h:multibuf (lanes a m) (hash_len a)
  -> len:size_t
  -> b:multibuf (lanes a m) len ->
  Stack unit
  (requires fun h0 -> live_multi h0 b /\ live_multi h0 h /\ internally_disjoint h)
  (ensures  fun h0 _ h1 -> modifies_multi h h0 h1 /\
    as_seq_multi h1 h == SpecVec.hash #a #m (v len) (as_seq_multi h0 b))

inline_for_extraction noextract
val hash: #a:sha2_alg -> #m:m_spec -> hash_vec_t a m
