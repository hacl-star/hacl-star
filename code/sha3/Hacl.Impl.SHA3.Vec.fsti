module Hacl.Impl.SHA3.Vec

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.MultiBuffer

open LowStar.Buffer
open Lib.Buffer

open Hacl.Spec.SHA3.Vec.Common
open Spec.Hash.Definitions

module LSeq = Lib.Sequence
module V = Hacl.Spec.SHA3.Vec

inline_for_extraction noextract
let state_t (m:m_spec) = lbuffer (element_t m) 25ul

inline_for_extraction noextract
let ws_t (m:m_spec) = lbuffer (element_t m) 32ul

inline_for_extraction noextract
let index_t = n:size_t{v n < 5}

inline_for_extraction noextract
val get:
    m:m_spec
  -> s:state_t m
  -> x:index_t
  -> y:index_t
  -> Stack (element_t m)
    (requires fun h -> live h s)
    (ensures  fun h0 r h1 ->
      modifies loc_none h0 h1 /\
      r == V.get m (as_seq h0 s) (v x) (v y))

inline_for_extraction noextract
val set:
    m:m_spec
  -> s:state_t m
  -> x:index_t
  -> y:index_t
  -> v:element_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.set m (as_seq h0 s) (size_v x) (size_v y) v)

inline_for_extraction noextract
val state_theta0:
    m:m_spec
  -> s:state_t m
  -> _C:lbuffer (element_t m) 5ul
  -> Stack unit
    (requires fun h -> live h s /\ live h _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc _C) h0 h1 /\
      as_seq h1 _C == V.state_theta0 m (as_seq h0 s) (as_seq h0 _C))

inline_for_extraction noextract
val state_theta_inner_s:
    m:m_spec
  -> _C:lbuffer (element_t m) 5ul
  -> x:index_t
  -> s:state_t m
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_theta_inner_s m (as_seq h0 _C) (v x) (as_seq h0 s))

inline_for_extraction noextract
val state_theta1:
    m:m_spec
  -> s:state_t m
  -> _C:lbuffer (element_t m) 5ul
  -> Stack unit
    (requires fun h0 -> live h0 s /\ live h0 _C /\ disjoint _C s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_theta1 m (as_seq h0 _C) (as_seq h0 s))

inline_for_extraction noextract
val state_theta:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_theta m (as_seq h0 s))

inline_for_extraction noextract
val state_pi_rho_inner:
    m:m_spec
  -> i:size_t{v i < 24}
  -> current:lbuffer (element_t m) 1ul
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s /\ live h current /\ disjoint current s)
    (ensures  fun h0 _ h1 ->
      modifies (loc_union (loc s) (loc current)) h0 h1 /\
      (let c', s' = V.state_pi_rho_inner m (v i) (bget h0 current 0, as_seq h0 s) in
      bget h1 current 0 == c' /\
      as_seq h1 s == s'))

inline_for_extraction noextract
val state_pi_rho:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_pi_rho m (as_seq h0 s))

inline_for_extraction noextract
val state_chi_inner:
    m:m_spec
  -> st:state_t m
  -> y:index_t
  -> Stack unit
    (requires fun h0 -> live h0 st)
    (ensures  fun h0 _ h1 ->
      modifies (loc st) h0 h1 /\
      as_seq h1 st == V.state_chi_inner m (v y) (as_seq h0 st))

inline_for_extraction noextract
val state_chi:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_chi m (as_seq h0 s))

inline_for_extraction noextract
val state_iota:
    m:m_spec
  -> s:state_t m
  -> round:size_t{v round < 24}
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_iota m (as_seq h0 s) (v round))

inline_for_extraction noextract
val state_permute:
    m:m_spec
  -> s:state_t m
  -> Stack unit
    (requires fun h -> live h s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s) h0 h1 /\
      as_seq h1 s == V.state_permute m (as_seq h0 s))

inline_for_extraction noextract
val set_wsi: #a:keccak_alg -> #m:m_spec
  -> ws:ws_t m
  -> i:size_t{v i < 32}
  -> b:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b /\ live h ws /\ disjoint b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == LSeq.upd (as_seq h0 ws) (v i) (V.load_elementi #a #m (as_seq h0 b) (v bi)))

inline_for_extraction noextract
val set_wsi_1_4: #a:keccak_alg -> #m:m_spec{lanes m == 1}
  -> ws:ws_t m
  -> i:size_t{v i < 32 /\ v (i +! 3ul) < 32}
  -> b:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m) /\ v (bi +! 3ul) < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b /\ live h ws /\ disjoint b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    (let ws1 = as_seq h1 ws in
     let ws0 = as_seq h0 ws in
     ws1.[v i + 0] == V.load_elementi #a #m (as_seq h0 b) (v bi + 0) /\
     ws1.[v i + 1] == V.load_elementi #a #m (as_seq h0 b) (v bi + 1) /\
     ws1.[v i + 2] == V.load_elementi #a #m (as_seq h0 b) (v bi + 2) /\
     ws1.[v i + 3] == V.load_elementi #a #m (as_seq h0 b) (v bi + 3) /\
     (forall (j: nat). j < v i ==> ws1.[j] == ws0.[j]) /\
     (forall (j: nat). j >= v i + 4 /\ j < 32 ==> ws1.[j] == ws0.[j])))

inline_for_extraction noextract
val load_blocks1: #a:keccak_alg -> #m:m_spec{lanes m == 1}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 b))

inline_for_extraction noextract
val set_wsi_4_4: #a:keccak_alg -> #m:m_spec{lanes m == 4}
  -> ws:ws_t m
  -> i:size_t{v i < 32 /\ v (i +! 3ul) < 32}
  -> b0:lbuffer uint8 256ul
  -> b1:lbuffer uint8 256ul
  -> b2:lbuffer uint8 256ul
  -> b3:lbuffer uint8 256ul
  -> bi:size_t{v bi < 32 / (lanes m)} ->
  Stack unit
  (requires fun h -> live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\
    live h ws /\ disjoint b0 ws /\ disjoint b1 ws /\ disjoint b2 ws /\ disjoint b3 ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    (let ws1 = as_seq h1 ws in
     let ws0 = as_seq h0 ws in
     ws1.[v i + 0] == V.load_elementi #a #m (as_seq h0 b0) (v bi) /\
     ws1.[v i + 1] == V.load_elementi #a #m (as_seq h0 b1) (v bi) /\
     ws1.[v i + 2] == V.load_elementi #a #m (as_seq h0 b2) (v bi) /\
     ws1.[v i + 3] == V.load_elementi #a #m (as_seq h0 b3) (v bi) /\
     (forall (j: nat). j < v i ==> ws1.[j] == ws0.[j]) /\
     (forall (j: nat). j >= v i + 4 /\ j < 32 ==> ws1.[j] == ws0.[j])))

inline_for_extraction noextract
val load_blocks4: #a:keccak_alg -> #m:m_spec{lanes m == 4}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 b))

inline_for_extraction noextract
val load_blocks: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_blocks #a #m (as_seq_multi h0 b))

inline_for_extraction noextract
val transpose_ws4:
    #m:m_spec{lanes m == 4}
  -> ws:ws_t m
  -> Stack unit
    (requires fun h -> live h ws)
    (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
      as_seq h1 ws == V.transpose_ws (as_seq h0 ws))

inline_for_extraction noextract
val transpose_ws: #m:m_spec{is_supported m} -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live h ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.transpose_ws (as_seq h0 ws))

inline_for_extraction noextract
val load_ws: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> b:multibuf (lanes m) 256ul
  -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.load_ws #a #m (as_seq_multi h0 b))

inline_for_extraction noextract
val loadState: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s /\
    (forall l. l < lanes m ==> (forall i. (i >= v rateInBytes /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.loadState #a #m (v rateInBytes) (as_seq_multi h0 b) (as_seq h0 s))

inline_for_extraction noextract
val transpose_s_ws4:
    #m:m_spec{lanes m == 4}
  -> ws:ws_t m
  -> Stack unit
    (requires fun h -> live h ws)
    (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
      as_seq h1 ws == V.transpose_s_ws (as_seq h0 ws))

inline_for_extraction noextract
val transpose_s_ws: #m:m_spec{is_supported m} -> ws:ws_t m ->
  Stack unit
  (requires fun h -> live h ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == V.transpose_s_ws (as_seq h0 ws))

inline_for_extraction noextract
val storeState: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> s:state_t m
  -> hbuf:lbuffer uint8 (size (lanes m) *! 32ul *! 8ul) ->
  Stack unit
  (requires fun h -> live h hbuf /\ live h s /\ disjoint hbuf s /\
    as_seq h hbuf == LSeq.create (lanes m * 32 * word_length a) (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc hbuf) h0 h1 /\
    as_seq h1 hbuf == V.storeState #a #m (as_seq h0 s))

inline_for_extraction noextract
val next_blocks:
  rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> nextBlock:lbuffer uint8 256ul ->
  Stack unit
  (requires fun h -> live h nextBlock /\
    as_seq h nextBlock == LSeq.create 256 (u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc nextBlock) h0 h1 /\
    as_seq h1 nextBlock == V.next_blocks (v rateInBytes) (as_seq h0 nextBlock))

inline_for_extraction noextract
val next_block1: #m:m_spec{lanes m == 1}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val next_block4: #m:m_spec{lanes m == 4}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\ 
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val next_block: #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\ 
    as_seq_multi h b == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b == V.next_block #m (v rateInBytes) (as_seq_multi h0 b))

inline_for_extraction noextract
val alloc_multi1: m:m_spec{lanes m == 1} ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

inline_for_extraction noextract
val alloc_multi4: m:m_spec{lanes m == 4} ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\ internally_disjoint b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

inline_for_extraction noextract
val alloc_multi: m:m_spec{is_supported m} ->
  StackInline (multibuf (lanes m) 256ul)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live_multi h1 b /\ internally_disjoint b /\
    stack_allocated_multi b h0 h1 (Seq.create 256 (u8 0)) /\
    as_seq_multi h1 b == next_block_seq_zero m)

inline_for_extraction noextract
val absorb_next: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live h s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.absorb_next #a #m (v rateInBytes) (as_seq h0 s))

inline_for_extraction noextract
val load_last_blocks:
  rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> lastBlock:lbuffer uint8 256ul ->
  Stack unit
  (requires fun h -> live h lastBlock /\ (forall i. (i >= v rem /\ i < 256) ==>
    Seq.index (as_seq h lastBlock) i == u8 0))
  (ensures  fun h0 _ h1 -> modifies (loc lastBlock) h0 h1 /\
    as_seq h1 lastBlock ==
      V.load_last_blocks (v rateInBytes) (v rem) delimitedSuffix (as_seq h0 lastBlock))

inline_for_extraction noextract
val load_last_block1: #m:m_spec{lanes m == 1}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b ==
      V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

inline_for_extraction noextract
val load_last_block4: #m:m_spec{lanes m == 4}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b ==
      V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

inline_for_extraction noextract
val load_last_block: #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ internally_disjoint b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\
    as_seq_multi h1 b ==
      V.load_last_block #m (v rateInBytes) (v rem) delimitedSuffix (as_seq_multi h0 b))

inline_for_extraction noextract
val absorb_last: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> rem:size_t{v rem < v rateInBytes}
  -> delimitedSuffix:byte_t
  -> b:multibuf (lanes m) 256ul
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s /\ internally_disjoint b /\
    (forall l. l < lanes m ==> (forall i. (i >= v rem /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b) h0 h1 /\
    as_seq h1 s == V.absorb_last #a #m delimitedSuffix (v rateInBytes) (v rem) (as_seq_multi h0 b) (as_seq h0 s))

inline_for_extraction noextract
val absorb_inner: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> b:multibuf (lanes m) 256ul
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s /\
    (forall l. l < lanes m ==> (forall i. (i >= v rateInBytes /\ i < 256) ==>
      Seq.index (as_seq_multi h b).(|l|) i == u8 0)))
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.absorb_inner #a #m (v rateInBytes) (as_seq_multi h0 b) (as_seq h0 s))

inline_for_extraction noextract
let get_multiblock_t (m:m_spec{is_supported m}) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> i:size_t{v i < v len / v rateInBytes}
  -> b':multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\
    internally_disjoint b' /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b' h0 h1 /\
    as_seq_multi h1 b' == V.get_multiblock_spec (v rateInBytes) (v len) (as_seq_multi h0 b) (v i))

inline_for_extraction noextract
val get_multiblock_1: #m:m_spec{lanes m == 1} -> get_multiblock_t m

inline_for_extraction noextract
val get_multiblock_4: #m:m_spec{lanes m == 4} -> get_multiblock_t m

inline_for_extraction noextract
val get_multiblock: #m:m_spec{is_supported m} -> get_multiblock_t m

inline_for_extraction noextract
let get_multilast_t (m:m_spec{is_supported m}) =
    rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> b':multibuf (lanes m) 256ul ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\
    internally_disjoint b' /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies_multi b' h0 h1 /\
    as_seq_multi h1 b' == V.get_multilast_spec (v rateInBytes) (v len) (as_seq_multi h0 b))

inline_for_extraction noextract
val get_multilast_1: #m:m_spec{lanes m == 1} -> get_multilast_t m

inline_for_extraction noextract
val get_multilast_4: #m:m_spec{lanes m == 4} -> get_multilast_t m

inline_for_extraction noextract
val get_multilast: #m:m_spec{is_supported m} -> get_multilast_t m

inline_for_extraction noextract
val absorb_inner_block: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> i:size_t{v i < v len / v rateInBytes}
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    as_seq h1 s == V.absorb_inner_block #a #m (v rateInBytes) (v len) (as_seq_multi h0 b) (v i) (as_seq h0 s))

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
val absorb_final_get: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> len:size_t
  -> b:multibuf (lanes m) len
  -> b':multibuf (lanes m) 256ul
  -> delimitedSuffix:byte_t
  -> s:state_t m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live_multi h b' /\ live h s /\
    internally_disjoint b' /\ disjoint_multi b' s /\ disjoint_multi_multi b b' /\
    as_seq_multi h b' == next_block_seq_zero m)
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b') h0 h1 /\
    as_seq h1 s == V.absorb_final #a #m (as_seq h0 s) (v rateInBytes)
      (v len) (as_seq_multi h0 b) delimitedSuffix)

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
val update_output1:
  #m:m_spec{lanes m == 1}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output4:
  #m:m_spec{lanes m == 4}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output:
  #m:m_spec{is_supported m}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v i) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output_last1:
  #m:m_spec{lanes m == 1}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> outRem:size_t{v outRem == v outputByteLen % v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output_last4:
  #m:m_spec{lanes m == 4}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> outRem:size_t{v outRem == v outputByteLen % v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

inline_for_extraction noextract
val update_output_last:
  #m:m_spec{is_supported m}
  -> block:lbuffer uint8 (size (lanes m) *! 256ul)
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> outRem:size_t{v outRem == v outputByteLen % v rateInBytes}
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live h block /\ live_multi h b /\ internally_disjoint b /\
    disjoint_multi b block)
  (ensures  fun h0 _ h1 -> modifies_multi b h0 h1 /\ as_seq_multi h1 b ==
      V.update_b_last #m (as_seq h0 block) (v rateInBytes) (v outputByteLen) (v outRem) (as_seq_multi h0 b))

inline_for_extraction noextract
val squeeze_inner: #a:keccak_alg -> #m:m_spec{is_supported m}
  -> rateInBytes:size_t{v rateInBytes > 0 /\ v rateInBytes <= 200}
  -> outputByteLen:size_t
  -> i:size_t{v i < v outputByteLen / v rateInBytes}
  -> s:state_t m
  -> b:multibuf (lanes m) outputByteLen ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h s /\ internally_disjoint b /\
    disjoint_multi b s)
  (ensures  fun h0 _ h1 -> modifies (loc s |+| loc_multi b) h0 h1 /\
    (let s', b' = 
      V.squeeze_inner #a #m (v rateInBytes) (v outputByteLen) (v i) (as_seq h0 s, as_seq_multi h0 b) in
      as_seq h1 s == s' /\
      as_seq_multi h1 b == b'))

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
val keccak_get:# a:keccak_alg -> #m:m_spec{is_supported m}
  -> rate:size_t{v rate % 8 == 0 /\ v rate / 8 > 0 /\ v rate <= 1600}
  -> inputByteLen:size_t
  -> input:multibuf (lanes m) inputByteLen
  -> delimitedSuffix:byte_t
  -> outputByteLen:size_t
  -> output:multibuf (lanes m) outputByteLen
  -> s:state_t m ->
  Stack unit
    (requires fun h -> live_multi h input /\ live_multi h output /\ live h s /\
      internally_disjoint output /\ disjoint_multi_multi input output /\
      disjoint_multi input s /\ disjoint_multi output s)
    (ensures  fun h0 _ h1 ->
      modifies (loc s |+| loc_multi output) h0 h1 /\
      as_seq_multi h1 output ==
        V.squeeze #a #m (V.absorb #a #m (as_seq h0 s) (v rate / 8) (v inputByteLen) (as_seq_multi h0 input) delimitedSuffix)
          (v rate / 8) (v outputByteLen) (as_seq_multi h0 output))

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
