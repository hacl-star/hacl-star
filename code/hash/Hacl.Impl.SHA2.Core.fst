module Hacl.Impl.SHA2.Core

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.IntVector
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Hash.Definitions

module ST = FStar.HyperStack.ST
module NTup = Lib.NTuple
module Constants = Spec.SHA2.Constants
module Spec = Hacl.Spec.SHA2
module SpecVec = Hacl.Spec.SHA2.Vec
open Hacl.Spec.SHA2.Vec

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

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
let index_h0 (a: sha2_alg) (i: size_t) : Stack (word a)
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

unfold let state_t (a:sha2_alg) (m:m_spec) =
  lbuffer (element_t a m) 8ul

unfold let block_t (a:sha2_alg) =
  lbuffer uint8 (block_len a)

inline_for_extraction
let ws_t (a:sha2_alg) (m:m_spec) =
  lbuffer (element_t a m) 16ul

inline_for_extraction
val shuffle_core: #a: sha2_alg -> #m:m_spec ->
  k_t: word a ->
  ws_t: element_t a m ->
  st: state_t a m ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 ->
      modifies (loc st) h0 h1 /\
      as_seq h1 st ==
      SpecVec.shuffle_core_spec k_t ws_t (as_seq h0 st)))

#push-options "--z3rlimit 400"
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
  st.(0ul) <- a1;
  st.(1ul) <- b1;
  st.(2ul) <- c1;
  st.(3ul) <- d1;
  st.(4ul) <- e1;
  st.(5ul) <- f1;
  st.(6ul) <- g1;
  st.(7ul) <- h1;
  let h1 = ST.get() in
  eq_intro (as_seq h1 st)
           (shuffle_core_spec k_t ws_t (as_seq hp0 st))
#pop-options

inline_for_extraction
val set_wsi (#a:sha2_alg) (#m:m_spec) (ws:ws_t a m) (i:size_t{v i < 16}) (b:lbuffer uint8 (block_len a)) (bi:size_t{v bi < 16 / (lanes a m)}):
            Stack unit
            (requires (fun h -> live h b /\ live h ws /\ disjoint b ws))
            (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1))
let set_wsi #a #m ws i b bi =
  [@inline_let]
  let l = lanes a m in
  ws.(i) <- vec_load_be (word_t a) l (sub b (bi *. size l *. word_len a) (size l *. word_len a))

inline_for_extraction
val load_blocks1 (#a: sha2_alg) (#m:m_spec{lanes a m == 1})
                 (b: multibuf (lanes a m) (block_len a)) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws))
    (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
                           as_seq h1 ws ==
                           SpecVec.load_blocks (as_seq_multi h0 b)))
let load_blocks1 #a #m b ws =
  let h0 = ST.get() in
  let b = b.(|0|) in
  set_wsi ws 0ul b 0ul;
  set_wsi ws 1ul b 1ul;
  set_wsi ws 2ul b 2ul;
  set_wsi ws 3ul b 3ul;
  set_wsi ws 4ul b 4ul;
  set_wsi ws 5ul b 5ul;
  set_wsi ws 6ul b 6ul;
  set_wsi ws 7ul b 7ul;
  set_wsi ws 8ul b 8ul;
  set_wsi ws 9ul b 9ul;
  set_wsi ws 10ul b 10ul;
  set_wsi ws 11ul b 11ul;
  set_wsi ws 12ul b 12ul;
  set_wsi ws 13ul b 13ul;
  set_wsi ws 14ul b 14ul;
  set_wsi ws 15ul b 15ul;
  admit()

inline_for_extraction
val load_blocks4 (#a: sha2_alg) (#m:m_spec{lanes a m == 4})
                 (b: multibuf (lanes a m) (block_len a)) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws))
    (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
                           as_seq h1 ws ==
                           SpecVec.load_blocks (as_seq_multi h0 b)))
let load_blocks4 #a #m b ws =
  let h0 = ST.get() in
  let (b0,(b1,(b2,b3))) = NTup.tup4 b in
  admit();
//  let b0 = b.(|0|) in
//  let b1 = b.(|1|) in
//  let b2 = b.(|2|) in
//  let b3 = b.(|3|) in
  set_wsi ws 0ul b0 0ul;
  set_wsi ws 1ul b1 0ul;
  set_wsi ws 2ul b2 0ul;
  set_wsi ws 3ul b3 0ul;
  set_wsi ws 4ul b0 1ul;
  set_wsi ws 5ul b1 1ul;
  set_wsi ws 6ul b2 1ul;
  set_wsi ws 7ul b3 1ul;
  set_wsi ws 8ul b0 2ul;
  set_wsi ws 9ul b1 2ul;
  set_wsi ws 10ul b2 2ul;
  set_wsi ws 11ul b3 2ul;
  set_wsi ws 12ul b0 3ul;
  set_wsi ws 13ul b1 3ul;
  set_wsi ws 14ul b2 3ul;
  set_wsi ws 15ul b3 3ul;
  admit()


inline_for_extraction
val load_blocks (#a: sha2_alg) (#m:m_spec)
                (b: multibuf (lanes a m) (block_len a)) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws))
    (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
                           as_seq h1 ws ==
                           SpecVec.load_blocks (as_seq_multi h0 b)))

let load_blocks #a #m b ws =
  match lanes a m with
  | 1 -> load_blocks1 b ws
  | 4 -> load_blocks4 b ws
  | _ -> admit()


inline_for_extraction
val transpose_ws4 (#a: sha2_alg) (#m:m_spec{lanes a m == 4}) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live h ws))
    (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
                           as_seq h1 ws ==
                           SpecVec.transpose_ws (as_seq h0 ws)))

let transpose_ws4 #a #m ws =
  let (ws0,ws1,ws2,ws3) = transpose4x4 (ws.(0ul),ws.(1ul),ws.(2ul),ws.(3ul)) in
  let (ws4,ws5,ws6,ws7) = transpose4x4 (ws.(4ul),ws.(5ul),ws.(6ul),ws.(7ul)) in
  let (ws8,ws9,ws10,ws11) = transpose4x4 (ws.(8ul),ws.(9ul),ws.(10ul),ws.(11ul)) in
  let (ws12,ws13,ws14,ws15) = transpose4x4 (ws.(12ul),ws.(13ul),ws.(14ul),ws.(15ul)) in
  ws.(0ul) <- ws0;
  ws.(1ul) <- ws1;
  ws.(2ul) <- ws2;
  ws.(3ul) <- ws3;
  ws.(4ul) <- ws4;
  ws.(5ul) <- ws5;
  ws.(6ul) <- ws6;
  ws.(7ul) <- ws7;
  ws.(8ul) <- ws8;
  ws.(9ul) <- ws9;
  ws.(10ul) <- ws10;
  ws.(11ul) <- ws11;
  ws.(12ul) <- ws12;
  ws.(13ul) <- ws13;
  ws.(14ul) <- ws14;
  ws.(15ul) <- ws15;
  admit()

inline_for_extraction
val transpose_ws (#a: sha2_alg) (#m:m_spec) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live h ws))
    (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1 /\
                           as_seq h1 ws ==
                           SpecVec.transpose_ws (as_seq h0 ws)))
let transpose_ws #a #m ws =
  match lanes a m with
  | 1 -> ()
  | 4 -> transpose_ws4 ws
  | _ -> admit()


inline_for_extraction
val load_ws (#a: sha2_alg) (#m:m_spec)
            (b: multibuf (lanes a m) (block_len a)) (ws: ws_t a m):
    Stack unit
    (requires (fun h ->
      live_multi h b /\ live h ws /\ disjoint_multi b ws))
    (ensures (fun h0 _ h1 ->
      modifies (loc ws) h0 h1 /\
      as_seq h1 ws == SpecVec.load_ws #a #m (as_seq_multi h0 b)))
let load_ws #a #m b ws =
    let h0 = ST.get() in
    load_blocks b ws;
    transpose_ws ws

#push-options "--z3rlimit 300"
inline_for_extraction
val ws_next (#a: sha2_alg) (#m:m_spec)
            (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live h ws))
    (ensures (fun h0 _ h1 ->
      modifies (loc ws) h0 h1 /\
      as_seq h1 ws == SpecVec.ws_next (as_seq h0 ws)))
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

inline_for_extraction
val shuffle: #a:sha2_alg -> #m:m_spec -> ws:ws_t a m -> hash:state_t a m ->
    Stack unit
    (requires (fun h ->
      live h hash /\ live h ws /\
      disjoint hash ws))
    (ensures (fun h0 _ h1 ->
      modifies2 ws hash h0 h1 /\
      as_seq h1 hash == SpecVec.shuffle #a #m (as_seq h0 ws) (as_seq h0 hash)))

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
      if i <. num_rounds16 a -. 1ul then
        ws_next ws)


(** Init *)
inline_for_extraction
val alloc: a:sha2_alg -> m:m_spec ->
    StackInline (state_t a m)
    (requires (fun h -> True))
    (ensures (fun h0 b h1 -> live h1 b /\ stack_allocated b h0 h1 (Seq.create 8 (zero_element a m))))
let alloc a m = Lib.Buffer.create 8ul (zero_element a m)

inline_for_extraction
val init: #a:sha2_alg -> #m:m_spec -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1 /\
                           as_seq h1 hash == SpecVec.init a m))
let init #a #m hash =
  let h0 = ST.get() in
  fill h0 8ul hash
  (fun h i -> load_element a m (Seq.index (Spec.h0 a) i))
  (fun i -> let hi = index_h0 a i in
          load_element a m hi);
  let h1 = ST.get() in
  eq_intro (as_seq h1 hash)
           (createi 8 (fun i -> load_element a m (Seq.index (Spec.h0 a) i)))

let update_t (a:sha2_alg) (m:m_spec) = b:multibuf (lanes a m) (block_len a) -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash))// /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
                           as_seq h1 hash == SpecVec.update (as_seq_multi h0 b) (as_seq h0 hash)))

#push-options "--z3rlimit 500"
inline_for_extraction
val update: #a:sha2_alg -> #m:m_spec -> update_t a m
let update #a #m b hash =
  admit();
  let init_h0 = ST.get() in
  push_frame ();
  let h0 = ST.get() in
  let hash_old = create 8ul (zero_element a m) in
  copy hash_old hash;
  let h1 = ST.get() in
  assert (as_seq h1 hash_old == as_seq h0 hash);
  let ws = create 16ul (zero_element a m) in
  let h2 = ST.get() in
  assert (disjoint_multi b hash_old);
  Lib.NTuple.(eq_intro (as_seq_multi h2 b) (as_seq_multi h0 b));
  assert (live_multi h2 b);
  assert (disjoint_multi b ws);
  assert (disjoint ws hash_old);
  assert (disjoint hash hash_old);
  assert (disjoint ws hash);
  load_ws b ws;
  let h3 = ST.get() in
  assert (as_seq h3 ws == Hacl.Spec.SHA2.Vec.load_ws (as_seq_multi h0 b));
  assert (modifies (loc ws) h2 h3);
  assert (modifies (loc ws |+| loc hash_old) h0 h3);
  shuffle ws hash;
  let h4 = ST.get() in
  assert (as_seq h4 hash_old == as_seq h1 hash_old);
  assert (as_seq h4 hash == Hacl.Spec.SHA2.Vec.shuffle (as_seq h3 ws) (as_seq h0 hash));
  assert (modifies (loc hash |+| (loc ws |+| loc hash_old)) h0 h4);
  map2T 8ul hash (+|) hash hash_old; 
  let h5 = ST.get() in
  assert (as_seq h5 hash == map2 (+|) (as_seq h4 hash) (as_seq h1 hash_old));
  assert (as_seq h5 hash == update (as_seq_multi h0 b) (as_seq h0 hash));
  assert (modifies (loc hash |+| (loc ws |+| loc hash_old)) h0 h5);
  pop_frame();
  let fin_h5 = ST.get() in
  assert (modifies (loc hash) init_h0 fin_h5)
#pop-options

inline_for_extraction
let padded_blocks (a:sha2_alg) (len:size_t{v len < block_length a}) =
  if (len +. len_len a +. 1ul <=. block_len a) then 1ul else 2ul


inline_for_extraction
val load_last1: #a:sha2_alg -> #m:m_spec{lanes a m = 1} ->
                  totlen_buf:lbuffer uint8 (len_len a) ->
                  len:size_t{v len < block_length a} ->
                  b:multibuf (lanes a m) len ->
                  fin:size_t{v fin == block_length a \/ v fin == 2 * block_length a} ->
                  last:lbuffer uint8 (2ul *. block_len a) ->
    Stack (multibuf (lanes a m) (block_len a) & multibuf (lanes a m) (block_len a))
    (requires (fun h -> live h totlen_buf /\ live_multi h b /\ live h last /\
                      disjoint_multi b last /\ disjoint last totlen_buf /\
                      as_seq h last == Lib.Sequence.create (2 * block_length a) (u8 0)))
    (ensures (fun h0 (l0,l1) h1 -> modifies (loc last) h0 h1 /\
                           live_multi h1 l0 /\ live_multi h1 l1 /\
                           (as_seq_multi h1 l0, as_seq_multi h1 l1) ==
                           load_last1 #a #m (as_seq h0 totlen_buf) (v fin) (v len) (as_seq_multi h0 b)))                           
#push-options "--max_ifuel 2 --max_fuel 2 --z3rlimit 200"
let load_last1 #a #m totlen_buf len b fin last =
  let b = b.(|0|) in
  admit();
  update_sub last 0ul len b;
  last.(len) <- u8 0x80;
  update_sub last (fin -. len_len a) (len_len a) totlen_buf;
  let last0 : multibuf (lanes a m) (block_len a) = sub last 0ul (block_len a) in
  let last1 : multibuf (lanes a m) (block_len a) = sub last (block_len a) (block_len a) in
  let h1 = ST.get() in
  (last0,last1)
#pop-options

inline_for_extraction
val load_last4: #a:sha2_alg -> #m:m_spec{lanes a m = 4} ->
                  totlen_buf:lbuffer uint8 (len_len a) ->
                  len:size_t{v len < block_length a} ->
                  b:multibuf (lanes a m) len ->
                  fin:size_t{v fin == block_length a \/ v fin == 2 * block_length a} ->
                  last:lbuffer uint8 (size (lanes a m) *. 2ul *. block_len a) ->
    Stack (multibuf (lanes a m) (block_len a) & multibuf (lanes a m) (block_len a))
    (requires (fun h -> live h totlen_buf /\ live_multi h b /\ live h last /\
                      disjoint_multi b last /\ disjoint last totlen_buf /\
                      as_seq h last == Lib.Sequence.create (lanes a m * 2 * block_length a) (u8 0)))
    (ensures (fun h0 (l0,l1) h1 -> modifies (loc last) h0 h1 /\
                           live_multi h1 l0 /\ live_multi h1 l1 /\
                           (as_seq_multi h1 l0, as_seq_multi h1 l1) ==
                           load_last4 #a #m (as_seq h0 totlen_buf) (v fin) (v len) (as_seq_multi h0 b)))

#push-options "--z3rlimit 300"
let load_last4 #a #m totlen_buf len b fin last =
  let (b0,(b1,(b2,b3))) = NTup.tup4 b in
  let last0 = sub last 0ul (2ul *. block_len a) in
  let last1 = sub last (2ul *. block_len a) (2ul *. block_len a) in
  let last2 = sub last (4ul *. block_len a) (2ul *. block_len a) in
  let last3 = sub last (6ul *. block_len a) (2ul *. block_len a) in
  admit();
  update_sub last0 0ul len b0;
  update_sub last1 0ul len b1;
  update_sub last2 0ul len b2;
  update_sub last3 0ul len b3;
  last0.(len) <- u8 0x80;
  last1.(len) <- u8 0x80;
  last2.(len) <- u8 0x80;
  last3.(len) <- u8 0x80;
  update_sub last0 (fin -. len_len a) (len_len a) totlen_buf;
  update_sub last1 (fin -. len_len a) (len_len a) totlen_buf;
  update_sub last2 (fin -. len_len a) (len_len a) totlen_buf;
  update_sub last3 (fin -. len_len a) (len_len a) totlen_buf;
  let l00 = sub last0 0ul (block_len a) in
  let l10 = sub last1 0ul (block_len a) in
  let l20 = sub last2 0ul (block_len a) in
  let l30 = sub last3 0ul (block_len a) in
  let l01 = sub last0 (block_len a) (block_len a) in
  let l11 = sub last1 (block_len a) (block_len a) in
  let l21 = sub last2 (block_len a) (block_len a) in
  let l31 = sub last3 (block_len a) (block_len a) in
  let mb0:multibuf 4 (block_len a) = (l00, (l10, (l20, l30))) in
  let mb1:multibuf 4 (block_len a) = (l01, (l11, (l21, l31))) in
  (mb0, mb1)  
#pop-options

inline_for_extraction
val load_last: #a:sha2_alg -> #m:m_spec ->
               totlen_buf:lbuffer uint8 (len_len a) ->
               len:size_t{v len < block_length a} ->
               b:multibuf (lanes a m) len ->
               fin:size_t{v fin == block_length a \/ v fin == 2 * block_length a} ->
               last:lbuffer uint8 (size (lanes a m) *. 2ul *. block_len a) ->
    Stack (multibuf (lanes a m) (block_len a) & multibuf (lanes a m) (block_len a))
    (requires (fun h -> live h totlen_buf /\ live_multi h b /\ live h last /\
                      disjoint_multi b last /\ disjoint last totlen_buf /\
                      as_seq h last == Lib.Sequence.create (lanes a m * 2 * block_length a) (u8 0)))
    (ensures (fun h0 (l0,l1) h1 -> modifies (loc last) h0 h1 /\
                           live_multi h1 l0 /\ live_multi h1 l1 /\
                           (as_seq_multi h1 l0, as_seq_multi h1 l1) ==
                           SpecVec.load_last #a #m (as_seq h0 totlen_buf) (v fin) (v len) (as_seq_multi h0 b)))

let load_last #a #m  totlen_buf len b fin last =
  match lanes a m with
  | 1 -> admit();load_last1 #a #m totlen_buf len b fin last
  | 4 -> load_last4 #a #m totlen_buf len b fin last
  | _ -> admit()
  
inline_for_extraction
val update_last: #a:sha2_alg -> #m:m_spec ->
                  upd: update_t a m ->
                  totlen:len_t a ->
                  len:size_t{v len < block_length a} ->
                  b:multibuf (lanes a m) len ->
                  hash:state_t a m ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
                           as_seq h1 hash ==
                           SpecVec.update_last totlen (v len) (as_seq_multi h0 b) (as_seq h0 hash)))

#push-options "--z3rlimit 300"
let update_last #a #m upd totlen len b hash =
  push_frame ();
  let last = create (size (lanes a m) *. 2ul *. block_len a) (u8 0) in
  let totlen_buf = create (len_len a) (u8 0) in
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in 
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) totlen_buf total_len_bits;
  let blocks = padded_blocks a len in
  let fin = blocks *. block_len a in
  let (last0,last1) = load_last #a #m totlen_buf len b fin last in
  upd last0 hash;
  if blocks >. 1ul then (
    upd last1 hash
  );
  admit();
  pop_frame()
#pop-options

inline_for_extraction
val transpose_state4 (#a: sha2_alg) (#m:m_spec{lanes a m == 4}) (st: state_t a m):
    Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
                           as_seq h1 st ==
                           SpecVec.transpose_state4 (as_seq h0 st)))

#push-options "--z3rlimit 200"
let transpose_state4 #a #m st =
  let h0 = ST.get() in
  let st0 = st.(0ul) in
  let st1 = st.(1ul) in
  let st2 = st.(2ul) in
  let st3 = st.(3ul) in
  let st4 = st.(4ul) in
  let st5 = st.(5ul) in
  let st6 = st.(6ul) in
  let st7 = st.(7ul) in
  let (st0',st1',st2',st3') = transpose4x4 (st0,st1,st2,st3) in
  let (st4',st5',st6',st7') = transpose4x4 (st4,st5,st6,st7) in
  st.(0ul) <- st0';
  st.(1ul) <- st4';
  st.(2ul) <- st1';
  st.(3ul) <- st5';
  st.(4ul) <- st2';
  st.(5ul) <- st6';
  st.(6ul) <- st3';
  st.(7ul) <- st7';
  let h1 = ST.get() in
  Lib.Sequence.eq_intro (as_seq h1 st) (create8 st0' st4' st1' st5' st2' st6' st3' st7');
  Lib.Sequence.eq_intro (as_seq h0 st) (create8 st0 st1 st2 st3 st4 st5 st6 st7);
  Lib.Sequence.eq_intro (create8 st0' st4' st1' st5' st2' st6' st3' st7')
                        (SpecVec.transpose_state4 (create8 st0 st1 st2 st3 st4 st5 st6 st7));
  admit();            
  ()
#pop-options  


inline_for_extraction
val transpose_state (#a: sha2_alg) (#m:m_spec) (st: state_t a m):
    Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> modifies (loc st) h0 h1 /\
                           as_seq h1 st ==
                           SpecVec.transpose_state (as_seq h0 st)))
let transpose_state #a #m st =
  match lanes a m with
  | 1 -> ()
  | 4 -> transpose_state4 st
  | _ -> admit()


inline_for_extraction
val store_state: #a:sha2_alg -> #m:m_spec->
                 st:state_t a m ->
                 hbuf:lbuffer uint8 (size (lanes a m) *. 8ul *. word_len a) ->
    Stack unit
    (requires (fun h -> live h hbuf /\ live h st /\ disjoint hbuf st))
    (ensures (fun h0 _ h1 -> modifies (loc st |+| loc hbuf) h0 h1 /\
                           as_seq h1 hbuf ==
                           SpecVec.store_state #a #m (as_seq h0 st)))
let store_state #a #m st hbuf =
  admit();
  transpose_state st;
  let h0 = ST.get() in
  loop1 h0 8ul hbuf
  (fun h -> SpecVec.store_state_inner #a #m (as_seq h0 st))
  (fun i ->  
    admit();
    Lib.LoopCombinators.unfold_repeati 8 (SpecVec.store_state_inner #a #m (as_seq h0 st))
                                         (as_seq h0 hbuf) (v i);
    vec_store_be (sub hbuf (size (lanes a m) *. i *. word_len a) (size (lanes a m) *. word_len a)) st.(i))

inline_for_extraction
val emit1: #a:sha2_alg -> #m:m_spec{lanes a m = 1} ->
             hbuf: lbuffer uint8 (8ul *. word_len a) ->
             result:lbuffer uint8 (hash_len a) ->
    Stack unit
    (requires (fun h -> live h result /\ live h hbuf /\ disjoint result hbuf))
    (ensures (fun h0 _ h1 -> modifies (loc result) h0 h1 /\
                           (as_seq h1 result <: multiseq 1 (hash_length a)) ==
                           SpecVec.emit1 #a #m (as_seq h0 hbuf)))
let emit1 #a #m hbuf result =
  copy result (sub hbuf 0ul (hash_len a))

inline_for_extraction
val emit4: #a:sha2_alg -> #m:m_spec{lanes a m = 4} ->
             hbuf: lbuffer uint8 (size (lanes a m) *. 8ul *. word_len a) ->
             result:multibuf (lanes a m) (hash_len a) ->
    Stack unit
    (requires (fun h -> live_multi h result /\ live h hbuf /\ disjoint_multi result hbuf))
    (ensures (fun h0 _ h1 -> modifies_multi result h0 h1 /\
                           as_seq_multi h1 result ==
                           SpecVec.emit4 #a #m (as_seq h0 hbuf)))
#push-options "--z3rlimit 200"
let emit4 #a #m hbuf result =
  let (b0,(b1,(b2,b3))) = NTup.tup4 result in
  copy b0 (sub hbuf 0ul (hash_len a));
  copy b1 (sub hbuf (8ul *. word_len a) (hash_len a));
  copy b2 (sub hbuf (16ul *. word_len a) (hash_len a));
  copy b3 (sub hbuf (24ul *. word_len a) (hash_len a));
  admit()
#pop-options


inline_for_extraction
val emit: #a:sha2_alg -> #m:m_spec ->
          hbuf: lbuffer uint8 (size (lanes a m) *. 8ul *. word_len a) ->
          result:multibuf (lanes a m) (hash_len a) ->
    Stack unit
    (requires (fun h -> live_multi h result /\ live h hbuf /\ disjoint_multi result hbuf))
    (ensures (fun h0 _ h1 -> modifies_multi result h0 h1 /\
                           as_seq_multi h1 result ==
                           SpecVec.emit #a #m (as_seq h0 hbuf)))
let emit #a #m hbuf result =
  admit();
  match lanes a m with
  | 1 -> emit1 #a #m hbuf result
  | 4 -> emit4 #a #m hbuf result
  | _ -> admit()

inline_for_extraction
val get_multiblock: #a:sha2_alg -> #m:m_spec ->
                    len:size_t -> b:multibuf (lanes a m) len ->
                    i:size_t{v i < v len / block_length a} ->
                    Stack (multibuf (lanes a m) (block_len a))
                    (requires (fun h -> live_multi h b))
                    (ensures (fun h0 r h1 -> h0 == h1 /\ live_multi h1 r /\
                                           as_seq_multi h1 r ==
                                           SpecVec.get_multiblock_spec (v len) (as_seq_multi h0 b) (v i)))

let get_multiblock #a #m len b i =
  admit();
  match lanes a m with
  | 1 -> sub (b <: lbuffer uint8 len) (i *. block_len a) (block_len a)
  | 4 -> let (b0,(b1,(b2,b3))) = NTup.tup4 b in
         let bl0 : lbuffer uint8 (block_len a) = sub (b0 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let bl1 : lbuffer uint8 (block_len a) = sub (b1 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let bl2 : lbuffer uint8 (block_len a) = sub (b2 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let bl3 : lbuffer uint8 (block_len a) = sub (b3 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         NTup.ntup4 (bl0, (bl1, (bl2, bl3)))
  | _ -> admit()


inline_for_extraction
val get_multilast: #a:sha2_alg -> #m:m_spec ->
                   len:size_t -> b:multibuf (lanes a m) len ->
                   Stack (multibuf (lanes a m) (len %. block_len a))
                   (requires (fun h -> live_multi h b))
                   (ensures (fun h0 r h1 -> h0 == h1 /\ live_multi h1 r /\
                            as_seq_multi h1 r ==
                            SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h0 b)))

#push-options "--z3rlimit 200"
let get_multilast #a #m len b =
  admit();
  let h0 = ST.get() in
  let rem = len %. block_len a in
  match lanes a m with
  | 1 -> sub (b <: lbuffer uint8 len) (len -. rem) rem
  | 4 -> let (b0,(b1,(b2,b3))) = NTup.tup4 b in
         let bl0 = sub (b0 <: lbuffer uint8 len) (len -! rem) rem in
         let bl1 = sub (b1 <: lbuffer uint8 len) (len -! rem) rem in
         let bl2 = sub (b2 <: lbuffer uint8 len) (len -! rem) rem in
         let bl3 = sub (b3 <: lbuffer uint8 len) (len -! rem) rem in
         let mb : multibuf 4 rem = NTup.ntup4 (bl0, (bl1, (bl2, bl3))) in
         assert (v (len -! rem) = v len - v rem);
         let h1 = ST.get() in
         assert (as_seq h1 bl0 == Lib.Sequence.sub (as_seq h0 b0) (v len - v rem) (v rem));
         assert (as_seq h1 bl1 == Lib.Sequence.sub (as_seq h0 b1) (v len - v rem) (v rem));
         assert (as_seq h1 bl2 == Lib.Sequence.sub (as_seq h0 b2) (v len - v rem) (v rem));
         assert (as_seq h1 bl3 == Lib.Sequence.sub (as_seq h0 b3) (v len - v rem) (v rem));
         assert (as_seq_multi h1 mb == (as_seq h1 bl0, (as_seq h1 bl1, (as_seq h1 bl2, as_seq h1 bl3))));
         assert (h0 == h1);
         assert (live_multi h1 mb);
         Lib.NTuple.eq_intro (as_seq_multi h1 mb) (SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h0 b));
         assert (Lib.NTuple.equal
                       (as_seq_multi h1 mb)
                       (SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h0 b)));
         Lib.NTuple.eq_elim (as_seq_multi h1 mb) (SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h0 b));
         assert ((as_seq_multi h1 mb) ==
                 (SpecVec.get_multilast_spec #a #m (v len) (as_seq_multi h0 b)));
         admit();
         mb
  | _ -> admit()
#pop-options

inline_for_extraction
val hash: #a:sha2_alg -> #m:m_spec -> upd:update_t a m ->
          h:multibuf (lanes a m) (hash_len a) ->
          len:size_t ->
          b:multibuf (lanes a m) len ->
    Stack unit
    (requires (fun h0 -> live_multi h0 b /\ live_multi h0 h))
    (ensures (fun h0 _ h1 -> modifies_multi h h0 h1 /\
                           as_seq_multi h1 h ==
                           SpecVec.hash #a #m (v len) (as_seq_multi h0 b)))
let hash #a #m upd h len b =
    push_frame();
    let st = alloc a m in
    init #a #m st;
    let h0 = ST.get() in
    loop_nospec #h0 (len /. block_len a) st
      (fun i -> 
        let mb: multibuf (lanes a m) (block_len a) = get_multiblock len b i in
        upd mb st); 
    let rem = len %. block_len a in
    let mb: multibuf (lanes a m) rem = get_multilast len b in
    let len' : len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB len in
    admit();
    update_last #a #m upd len' rem mb st;
    let hbuf = create (size (lanes a m) *. 8ul *. word_len a) (u8 0) in
    store_state st hbuf;
    emit hbuf h;
    pop_frame()

[@CInline]
val sha256_update1: b:multibuf (lanes SHA2_256 M32) (block_len SHA2_256) -> hash:state_t SHA2_256 M32 ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash))// /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies (loc hash) h0 h1 /\
                           as_seq h1 hash == Hacl.Spec.SHA2.Vec.update #SHA2_256 #M32 (as_seq_multi h0 b) (as_seq h0 hash)))
let sha256_update1 b hash = update #SHA2_256 #M32 b hash

let sha256 h len b = admit(); hash #SHA2_256 #M32 sha256_update1 h len (b <: lbuffer uint8 len)

[@CInline]
val sha256_update4: b:multibuf (lanes SHA2_256 M128) (block_len SHA2_256) ->
                    hash:state_t SHA2_256 M128 ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash))// /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1 /\
                           as_seq h1 hash == Hacl.Spec.SHA2.Vec.update #SHA2_256 #M128 (as_seq_multi h0 b) (as_seq h0 hash)))

let sha256_update4 b hash =
  update #SHA2_256 #M128 b hash

#push-options "--z3rlimit 200"
let sha256_4 r0 r1 r2 r3 len b0 b1 b2 b3 =
  let ib : multibuf 4 len = NTup.ntup4 (b0,(b1,(b2,b3))) in
  let rb : multibuf 4 (hash_len SHA2_256) = NTup.ntup4 (r0,(r1,(r2,r3))) in
  let h0 = ST.get() in
  admit();
  assert (live_multi h0 ib);
  hash #SHA2_256 #M128 sha256_update4 rb len ib
#pop-options


