module Hacl.Impl.SHA2.Generic

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.IntVector
open Lib.MultiBuffer
open Lib.CreateN

open Spec.Hash.Definitions
open Hacl.Hash.Definitions
open Hacl.Spec.SHA2.Vec
open Hacl.Impl.SHA2.Core

module ST = FStar.HyperStack.ST
module NTup = Lib.NTuple
module Constants = Spec.SHA2.Constants
module Spec = Hacl.Spec.SHA2
module SpecVec = Hacl.Spec.SHA2.Vec
module VecTranspose = Lib.IntVector.Transpose
module LSeq = Lib.Sequence


#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

(** Top-level constant arrays for the SHA2 algorithms. *)

let h224 : x:glbuffer uint32 8ul{witnessed x Constants.h224 /\ recallable x} =
  createL_global Constants.h224_l
let h256 : x:glbuffer uint32 8ul{witnessed x Constants.h256 /\ recallable x} =
  createL_global Constants.h256_l
let h384 : x:glbuffer uint64 8ul{witnessed x Constants.h384 /\ recallable x} =
  createL_global Constants.h384_l
let h512 : x:glbuffer uint64 8ul{witnessed x Constants.h512 /\ recallable x} =
  createL_global Constants.h512_l


noextract inline_for_extraction
let index_h0 (a:sha2_alg) (i:size_t) : Stack (word a)
  (requires (fun _ -> size_v i < 8))
  (ensures (fun h0 r h1 ->
    h0 == h1 /\
    r == Seq.index (Spec.h0 a) (size_v i))) =
    match a with
    | SHA2_224 -> recall h224; recall_contents h224 Constants.h224; h224.(i)
    | SHA2_256 -> recall h256; recall_contents h256 Constants.h256; h256.(i)
    | SHA2_384 -> recall h384; recall_contents h384 Constants.h384; h384.(i)
    | SHA2_512 -> recall h512; recall_contents h512 Constants.h512; h512.(i)


let k224_256 : x:glbuffer uint32 64ul{witnessed x Constants.k224_256 /\ recallable x} =
  createL_global Constants.k224_256_l

let k384_512 : x:glbuffer uint64 80ul{witnessed x Constants.k384_512 /\ recallable x} =
  createL_global Constants.k384_512_l


noextract inline_for_extraction
let index_k0 (a:sha2_alg) (i:size_t) : Stack (word a)
  (requires (fun _ -> size_v i < Spec.size_k_w a))
  (ensures (fun h0 r h1 ->
    h0 == h1 /\
    r == Seq.index (Spec.k0 a) (size_v i))) =
  match a with
  | SHA2_224 | SHA2_256 ->
      recall_contents k224_256 Constants.k224_256;
      k224_256.(i)
  | SHA2_384 | SHA2_512 ->
      recall_contents k384_512 Constants.k384_512;
      k384_512.(i)


inline_for_extraction noextract
val shuffle_core: #a:sha2_alg -> #m:m_spec
  -> k_t:word a
  -> ws_t:element_t a m
  -> st:state_t a m ->
  Stack unit
  (requires fun h -> live h st)
  (ensures  fun h0 _ h1 ->
    modifies (loc st) h0 h1 /\
    as_seq h1 st == SpecVec.shuffle_core_spec k_t ws_t (as_seq h0 st))

let shuffle_core #a #m k_t ws_t st =
  let hp0 = ST.get() in
  let a0 = st.(0ul) in
  let b0 = st.(1ul) in
  let c0 = st.(2ul) in
  let d0 = st.(3ul) in
  let e0 = st.(4ul) in
  let f0 = st.(5ul) in
  let g0 = st.(6ul) in
  let h0 = st.(7ul) in
  let k_e_t = load_element a m k_t in
  let t1 = h0 +| (_Sigma1 e0) +| (_Ch e0 f0 g0) +| k_e_t +| ws_t in
  let t2 = (_Sigma0 a0) +| (_Maj a0 b0 c0) in
  let a1 = t1 +| t2 in
  let b1 = a0 in
  let c1 = b0 in
  let d1 = c0 in
  let e1 = d0 +| t1 in
  let f1 = e0 in
  let g1 = f0 in
  let h1 = g0 in
  create8_st st a1 b1 c1 d1 e1 f1 g1 h1


#push-options "--z3rlimit 300"
inline_for_extraction noextract
val ws_next: #a:sha2_alg -> #m:m_spec -> ws:ws_t a m ->
  Stack unit
  (requires fun h -> live h ws)
  (ensures  fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
    as_seq h1 ws == SpecVec.ws_next (as_seq h0 ws))

let ws_next #a #m ws =
  let h0 = ST.get() in
  loop1 h0 16ul ws
  (fun h -> ws_next_inner #a #m)
  (fun i ->
    Lib.LoopCombinators.unfold_repeati 16 (ws_next_inner #a #m) (as_seq h0 ws) (v i);
    let t16 = ws.(i) in
    let t15 = ws.((i+.1ul) %. 16ul) in
    let t7  = ws.((i+.9ul) %. 16ul) in
    let t2  = ws.((i+.14ul) %. 16ul) in
    let s1 = _sigma1 t2 in
    let s0 = _sigma0 t15 in
    ws.(i) <- (s1 +| t7 +| s0 +| t16))
#pop-options


inline_for_extraction noextract
val shuffle: #a:sha2_alg -> #m:m_spec -> ws:ws_t a m -> hash:state_t a m ->
  Stack unit
  (requires fun h -> live h hash /\ live h ws /\ disjoint hash ws)
  (ensures  fun h0 _ h1 -> modifies2 ws hash h0 h1 /\
    as_seq h1 hash == SpecVec.shuffle #a #m (as_seq h0 ws) (as_seq h0 hash))

let shuffle #a #m ws hash =
  let h0 = ST.get() in
  loop2 h0 (num_rounds16 a) ws hash
  (fun h -> shuffle_inner_loop #a #m)
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v (num_rounds16 a)) (shuffle_inner_loop #a #m) (as_seq h0 ws, as_seq h0 hash) (v i);
    let h1 = ST.get() in
    loop1 h1 16ul hash
    (fun h -> shuffle_inner #a #m (as_seq h1 ws) (v i))
    (fun j ->
      Lib.LoopCombinators.unfold_repeati 16 (shuffle_inner #a #m (as_seq h1 ws) (v i)) (as_seq h1 hash) (v j);
      let k_t = index_k0 a (16ul *. i +. j) in
      let ws_t = ws.(j) in
      shuffle_core k_t ws_t hash);
    if i <. num_rounds16 a -. 1ul then ws_next ws)


inline_for_extraction noextract
val alloc: a:sha2_alg -> m:m_spec ->
  StackInline (state_t a m)
  (requires fun h -> True)
  (ensures  fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Seq.create 8 (zero_element a m)))

let alloc a m = Lib.Buffer.create 8ul (zero_element a m)


inline_for_extraction noextract
let init_vec_t (a:sha2_alg) (m:m_spec) = hash:state_t a m ->
  Stack unit
  (requires fun h -> live h hash)
  (ensures  fun h0 _ h1 -> modifies1 hash h0 h1 /\
    as_seq h1 hash == SpecVec.init a m)


inline_for_extraction noextract
val init: #a:sha2_alg -> #m:m_spec -> init_vec_t a m
let init #a #m hash =
  let h0 = ST.get() in
  fill h0 8ul hash
  (fun h i -> load_element a m (Seq.index (Spec.h0 a) i))
  (fun i ->
    let hi = index_h0 a i in
    load_element a m hi);
  let h1 = ST.get() in
  LSeq.eq_intro (as_seq h1 hash) (LSeq.createi 8 (fun i -> load_element a m (Seq.index (Spec.h0 a) i)))


inline_for_extraction noextract
let update_vec_t (a:sha2_alg) (m:m_spec) =
    b:multibuf (lanes a m) (block_len a)
  -> hash:state_t a m ->
  Stack unit
  (requires fun h -> live_multi h b /\ live h hash)
  (ensures  fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
    as_seq h1 hash == SpecVec.update (as_seq_multi h0 b) (as_seq h0 hash))


#push-options "--z3rlimit 200"
inline_for_extraction noextract
val update: #a:sha2_alg -> #m:m_spec -> update_vec_t a m
let update #a #m b hash =
  let h0 = ST.get() in
  push_frame ();
  let h1 = ST.get() in
  let hash_old = create 8ul (zero_element a m) in
  let ws = create 16ul (zero_element a m) in
  assert (disjoint_multi b hash_old);
  assert (disjoint_multi b ws);
  assert (disjoint ws hash_old);
  assert (disjoint hash hash_old);
  assert (disjoint ws hash);
  copy hash_old hash;
  let h2 = ST.get() in
  assert (live_multi h2 b);
  NTup.(eq_intro (as_seq_multi h2 b) (as_seq_multi h0 b));
  load_ws b ws;
  let h3 = ST.get() in
  assert (modifies (loc ws |+| loc hash_old) h0 h3);
  assert (as_seq h3 ws == SpecVec.load_ws (as_seq_multi h2 b));
  shuffle ws hash;
  let h4 = ST.get() in
  assert (modifies (loc hash |+| (loc ws |+| loc hash_old)) h0 h4);
  assert (as_seq h4 hash == SpecVec.shuffle (as_seq h3 ws) (as_seq h0 hash));
  map2T 8ul hash (+|) hash hash_old;
  let h5 = ST.get() in
  assert (modifies (loc hash |+| (loc ws |+| loc hash_old)) h0 h5);
  reveal_opaque (`%SpecVec.update) (SpecVec.update #a #m);
  assert (as_seq h5 hash == SpecVec.update (as_seq_multi h0 b) (as_seq h0 hash));
  pop_frame()
#pop-options


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


#push-options "--z3rlimit 350"
inline_for_extraction noextract
val update_last: #a:sha2_alg -> #m:m_spec -> update_last_vec_t a m
let update_last #a #m upd totlen len b hash =
  let h0 = ST.get() in
  push_frame ();
  let h1 = ST.get() in
  let blocks = padded_blocks a len in
  let fin = blocks *! block_len a in
  let last = create (size (lanes a m) *! 2ul *! block_len a) (u8 0) in
  let totlen_buf = create (len_len a) (u8 0) in
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) totlen_buf total_len_bits;
  let h2 = ST.get () in
  NTup.eq_intro (as_seq_multi h2 b) (as_seq_multi h0 b);
  assert (as_seq h2 totlen_buf ==
          Lib.ByteSequence.uint_to_bytes_be #(len_int_type a) total_len_bits);
  let (last0,last1) = load_last #a #m totlen_buf len b fin last in
  let h3 = ST.get () in
  assert ((as_seq_multi h3 last0, as_seq_multi h3 last1) ==
          SpecVec.load_last #a #m (as_seq h2 totlen_buf) (v fin) (v len) (as_seq_multi h2 b));
  assert (disjoint_multi last1 hash);
  upd last0 hash;
  let h4 = ST.get() in
  assert (modifies (loc hash |+| loc last |+| loc totlen_buf) h1 h3);
  assert (as_seq h4 hash == SpecVec.update (as_seq_multi h3 last0) (as_seq h3 hash));
  NTup.eq_intro (as_seq_multi h4 last1) (as_seq_multi h3 last1);
  assert (v blocks > 1 ==> blocks >. 1ul);
  assert (blocks >. 1ul ==> v blocks > 1);
  assert (not (blocks >. 1ul) ==> not (v blocks > 1));
  if blocks >. 1ul then (
    upd last1 hash;
    let h5 = ST.get() in
    assert (as_seq h5 hash == SpecVec.update (as_seq_multi h4 last1) (as_seq h4 hash));
    assert (modifies (loc hash |+| loc last |+| loc totlen_buf) h1 h5);
    assert (as_seq h5 hash == SpecVec.update_last totlen (v len) (as_seq_multi h0 b) (as_seq h0 hash));
    pop_frame()
  ) else (
    let h6 = ST.get() in
    assert (h4 == h6);
    assert (modifies (loc hash |+| loc totlen_buf |+| loc last) h1 h6);
    assert (as_seq h6 hash == SpecVec.update_last totlen (v len) (as_seq_multi h0 b) (as_seq h0 hash));
    pop_frame())
#pop-options


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


#push-options "--z3rlimit 200"
inline_for_extraction noextract
val update_nblocks: #a:sha2_alg -> #m:m_spec -> update_nblocks_vec_t a m
let update_nblocks #a #m upd len b st =
  let blocks = len /. block_len a in
  let h0 = ST.get() in
  loop1 h0 blocks st
  (fun h -> SpecVec.update_block #a #m (v len) (as_seq_multi h0 b))
  (fun i ->
    Lib.LoopCombinators.unfold_repeati (v blocks) (SpecVec.update_block #a #m (v len) (as_seq_multi h0 b)) (as_seq h0 st) (v i);
    let h0' = ST.get() in
    let mb = get_multiblock len b i in
    upd mb st;
    let h1 = ST.get() in
    assert (modifies (loc st) h0 h1);
    NTup.eq_intro (as_seq_multi h0' b) (as_seq_multi h0 b);
    assert (as_seq h1 st == SpecVec.update_block #a #m (v len) (as_seq_multi h0 b) (v i) (as_seq h0' st)))
#pop-options


inline_for_extraction noextract
let finish_vec_t (a:sha2_alg) (m:m_spec) =
    st:state_t a m
  -> h:multibuf (lanes a m) (hash_len a) ->
  Stack unit
  (requires fun h0 -> live_multi h0 h /\ internally_disjoint h /\ live h0 st /\ disjoint_multi h st)
  (ensures  fun h0 _ h1 -> modifies (loc_multi h |+| loc st) h0 h1 /\
    as_seq_multi h1 h == SpecVec.finish #a #m (as_seq h0 st))


#push-options "--z3rlimit 100"
inline_for_extraction noextract
val finish: #a:sha2_alg -> #m:m_spec -> finish_vec_t a m
let finish #a #m st h =
  let h0 = ST.get() in
  push_frame();
  let hbuf = create (size (lanes a m) *. 8ul *. word_len a) (u8 0) in
  let h1 = ST.get() in
  store_state st hbuf;
  emit hbuf h;
  let h2 = ST.get() in
  assert (modifies (loc_multi h |+| loc st |+| loc hbuf) h1 h2);
  assert (as_seq_multi h2 h == SpecVec.finish #a #m (as_seq h0 st));
  pop_frame();
  let h3 = ST.get() in
  assert (modifies (loc_multi h |+| loc st) h0 h3);
  NTup.eq_intro (as_seq_multi h2 h) (as_seq_multi h3 h);
  assert (as_seq_multi h2 h == as_seq_multi h3 h);
  assert (as_seq_multi h3 h == SpecVec.finish #a #m (as_seq h0 st))
#pop-options


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


#push-options "--z3rlimit 500"
inline_for_extraction noextract
val hash: #a:sha2_alg -> #m:m_spec -> hash_vec_t a m
let hash #a #m upd h len b =
  let init_h0 = ST.get() in
  push_frame();
  let h0 = ST.get() in
  NTup.eq_intro (as_seq_multi h0 b) (as_seq_multi init_h0 b);
  let st = alloc a m in
  init #a #m st;
  let h1 = ST.get() in
  assert (modifies (loc st) h0 h1);
  assert (as_seq h1 st == SpecVec.init a m);
  NTup.eq_intro (as_seq_multi h1 b) (as_seq_multi h0 b);
  let rem = len %. block_len a in
  let len' : len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB len in
  update_nblocks #a #m upd len b st;
  let h2 = ST.get() in
  assert (modifies (loc st) h0 h2);
  assert (as_seq h2 st == SpecVec.update_nblocks (v len) (as_seq_multi h0 b) (as_seq h1 st));
  NTup.eq_intro (as_seq_multi h2 b) (as_seq_multi h0 b);
  let lb: multibuf (lanes a m) rem = get_multilast len b in
  let h3 = ST.get() in
  assert (h2 == h3);
  assert (as_seq_multi h3 lb == SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h2 b));
  assert (preserves_disjoint_multi b lb);
  assert (disjoint_multi lb st);
  update_last #a #m upd len' rem lb st;
  let h4 = ST.get() in
  assert (modifies (loc st) h0 h4);
  assert (as_seq h4 st == SpecVec.update_last len' (v rem) (as_seq_multi h3 lb) (as_seq h3 st));
  finish #a #m st h;
  let h5 = ST.get() in
  assert (modifies (loc_multi h |+| loc st) h0 h5);
  assert (as_seq_multi h5 h == SpecVec.finish #a #m (as_seq h4 st));
  assert (as_seq_multi h5 h == SpecVec.hash #a #m (v len) (as_seq_multi h0 b));
  pop_frame();
  let h6 = ST.get() in
  NTup.eq_intro (as_seq_multi h6 h) (as_seq_multi h5 h)
#pop-options
