module Hacl.Impl.SHA3.Vec

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.IntTypes
open Lib.NTuple

open Lib.MultiBuffer

open Lib.Buffer

open Hacl.Spec.SHA3.Vec.Common
open Spec.Hash.Definitions

module V = Hacl.Spec.SHA3.Vec

inline_for_extraction noextract
let state_t (m:m_spec) = lbuffer (element_t m) 25ul

inline_for_extraction noextract
val absorb_inner_nblocks: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.absorb_inner_nblocks #a #m (v rateInBytes) (v len) (as_seq_multi h0 b) (as_seq h0 s))

inline_for_extraction noextract
val absorb_final: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> delimitedSuffix:byte_t
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s ==
      V.absorb_final #a #m (as_seq h0 s) (v rateInBytes) (v len) (as_seq_multi h0 b) delimitedSuffix)

inline_for_extraction noextract
val absorb: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> delimitedSuffix:byte_t
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.absorb #a #m (as_seq h0 s) (v rateInBytes) (v len) (as_seq_multi h0 b) delimitedSuffix)

inline_for_extraction noextract
val squeeze_nblocks:# a:keccak_alg -> #m:m_spec{is_supported m}
  -> s:state_t m
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
    (requires fun h -> live_multi h b /\ live h s /\ internally_disjoint b /\
      disjoint_multi b s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s |+| loc_multi b) h0 h1 /\
      (let s', b' = 
        V.squeeze_nblocks #a #m (v rateInBytes) (v outputByteLen) (as_seq h0 s, as_seq_multi h0 b) in
        as_seq h1 s == s' /\
        as_seq_multi h1 b == b'))

inline_for_extraction noextract
val squeeze_last:# a:keccak_alg -> #m:m_spec{is_supported m}
  -> s:state_t m
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
    (requires fun h -> live_multi h b /\ live h s /\ internally_disjoint b /\
      disjoint_multi b s)
    (ensures  fun h0 _ h1 ->
      modifies_multi b h0 h1 /\
      as_seq_multi h1 b == V.squeeze_last #a #m (as_seq h0 s) (v rateInBytes) (v outputByteLen) (as_seq_multi h0 b))

inline_for_extraction noextract
val squeeze:# a:keccak_alg -> #m:m_spec{is_supported m}
  -> s:state_t m
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
    (requires fun h -> live_multi h b /\ live h s /\ internally_disjoint b /\
      disjoint_multi b s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s |+| loc_multi b) h0 h1 /\
      as_seq_multi h1 b == V.squeeze #a #m (as_seq h0 s) (v rateInBytes) (v outputByteLen) (as_seq_multi h0 b))

inline_for_extraction noextract
val keccak:# a:keccak_alg -> #m:m_spec{is_supported m}
  -> rate:size_t{v rate % 8 == 0 /\ v rate / 8 > 0 /\ v rate <= 1600}
  -> inputByteLen:size_t
  -> input:multibuf (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_t
  -> output:multibuf (lanes m) outputByteLen ->
  Stack unit
    (requires fun h -> live_multi h input /\ live_multi h output /\
      internally_disjoint output /\ disjoint_multi_multi input output)
    (ensures  fun h0 _ h1 ->
      modifies_multi output h0 h1 /\
      as_seq_multi h1 output ==
        V.keccak #a #m (v rate) (v inputByteLen) (as_seq_multi h0 input) delimitedSuffix (v outputByteLen) (as_seq_multi h0 output))
