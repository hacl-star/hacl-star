module Hacl.Impl.SHA2.Core

open FStar.Mul
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.IntVector
module NTup = Lib.NTuple
open Lib.MultiBuffer
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Spec.SHA2
friend Hacl.Spec.SHA2.Vec
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


(** Update *)
unfold let state_t (a:sha2_alg) (m:m_spec) =
  lbuffer (element_t a m) 8ul

unfold let block_t (a:sha2_alg) =
  lbuffer uint8 (block_len a)
(*  match a with
  | SHA2_224 | SHA2_256 -> lbuffer uint8 64ul
  | SHA2_384 | SHA2_512 -> lbuffer uint8 128ul
*)

noextract
let state_v (#a:sha2_alg) (#m:m_spec) (h:mem) (st:state_t a m) : GTot (lseq (words_state a) (lanes a m)) =
  let st_seq = as_seq h st in
  let st_seq_seq = Lib.Sequence.map vec_v st_seq in
  let res = createi #(words_state a) (lanes a m) (fun i -> map (fun x -> x.[i]) st_seq_seq) in
  res
  
inline_for_extraction
let ws_t (a:sha2_alg) (m:m_spec) =
  lbuffer (element_t a m) 16ul

noextract
let ws_v (#a:sha2_alg) (#m:m_spec) (h:mem) (st:ws_t a m) : GTot (lseq (lseq (word a) 16) (lanes a m)) =
  let st_seq = as_seq h st in
  let st_seq_seq = Lib.Sequence.map vec_v st_seq in
  let res = createi #(lseq (word a) 16) (lanes a m) (fun i -> map (fun x -> x.[i]) st_seq_seq) in
  res

inline_for_extraction
val shuffle_core: #a: sha2_alg -> #m:m_spec ->
  k_t: word a ->
  ws_t: element_t a m ->
  hash: state_t a m ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures (fun h0 _ h1 ->
      modifies (loc hash) h0 h1 /\
      state_v h1 hash ==
      map2 (Spec.shuffle_core_pre_ a k_t) (vec_v ws_t) (state_v h0 hash)))

let shuffle_core #a #m k_t ws_t hash =
  let a0 = hash.(0ul) in
  let b0 = hash.(1ul) in
  let c0 = hash.(2ul) in
  let d0 = hash.(3ul) in
  let e0 = hash.(4ul) in
  let f0 = hash.(5ul) in
  let g0 = hash.(6ul) in
  let h0 = hash.(7ul) in
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
  hash.(0ul) <- a1;
  hash.(1ul) <- b1;
  hash.(2ul) <- c1;
  hash.(3ul) <- d1;
  hash.(4ul) <- e1;
  hash.(5ul) <- f1;
  hash.(6ul) <- g1;
  hash.(7ul) <- h1;
  admit()


inline_for_extraction
let num_rounds16 (a:sha2_alg) : n:size_t{v n > 0 /\ 16 * v n == Spec.size_k_w a} =
  match a with
  | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 5ul

inline_for_extraction
val load_ws1 (#a: sha2_alg) (#m:m_spec{lanes a m = 1})
        (b: block_t a) (ws: ws_t a m):
    Stack unit
    (requires (fun h ->
      live h b /\ live h ws /\ disjoint b ws))
    (ensures (fun h0 _ h1 ->
      modifies (loc ws) h0 h1))
let load_ws1 #a #m b ws =
    let h0 = ST.get() in
    loop_nospec #h0 16ul ws (fun i ->
      ws.(i) <- Lib.IntVector.vec_load_be (word_t a) 1 (sub b (i *. word_len a) (word_len a)))

inline_for_extraction
val load_ws4 (#a: sha2_alg) (#m:m_spec{lanes a m = 4})
        (b0: block_t a) (b1: block_t a)  (b2: block_t a)  (b3: block_t a) (ws: ws_t a m):
    Stack unit
    (requires (fun h ->
      live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\ live h ws /\ disjoint b0 ws /\ disjoint b1 ws  /\ disjoint b2 ws /\ disjoint b3 ws))
    (ensures (fun h0 _ h1 ->
      modifies (loc ws) h0 h1))
let load_ws4 #a #m b0 b1 b2 b3 ws =
    admit();
    let h0 = ST.get() in
    loop_nospec #h0 4ul ws (fun i ->
      ws.(4ul *. i) <- Lib.IntVector.vec_load_be (word_t a) 4 (sub b0 (4ul *. i *. word_len a) (4ul *. word_len a)));
    let h0 = ST.get() in
    loop_nospec #h0 4ul ws (fun i ->
      ws.(4ul *. i +. 1ul) <- Lib.IntVector.vec_load_be (word_t a) 4 (sub b1 (4ul *. i *. word_len a) (4ul *. word_len a)));
    let h0 = ST.get() in
    loop_nospec #h0 4ul ws (fun i ->
      ws.(4ul *. i +. 2ul) <- Lib.IntVector.vec_load_be (word_t a) 4 (sub b2 (4ul *. i *. word_len a) (4ul *. word_len a)));
    let h0 = ST.get() in
    loop_nospec #h0 4ul ws (fun i ->
      ws.(4ul *. i +. 3ul) <- Lib.IntVector.vec_load_be (word_t a) 4 (sub b3 (4ul *. i *. word_len a) (4ul *. word_len a)));
    let h0 = ST.get() in
    loop_nospec #h0 4ul ws (fun i ->
      let ws0 = ws.(4ul*.i+.0ul) in
      let ws1 = ws.(4ul*.i+.1ul) in
      let ws2 = ws.(4ul*.i+.2ul) in
      let ws3 = ws.(4ul*.i+.3ul) in
      ws.(4ul*.i) <- vec_interleave_low ws0 ws1;
      ws.(4ul*.i+.1ul) <- vec_interleave_high ws0 ws1;
      ws.(4ul*.i+.2ul) <- vec_interleave_low ws2 ws3;
      ws.(4ul*.i+.3ul) <- vec_interleave_high ws2 ws3;
      let ws0 = ws.(4ul*.i+.0ul) in
      let ws1 = ws.(4ul*.i+.1ul) in
      let ws2 = ws.(4ul*.i+.2ul) in
      let ws3 = ws.(4ul*.i+.3ul) in
      ws.(4ul*.i) <- vec_interleave_low_n 2 ws0 ws2;
      ws.(4ul*.i+.1ul) <- vec_interleave_high_n 2 ws0 ws2;
      ws.(4ul*.i+.2ul) <- vec_interleave_low_n 2 ws1 ws3;
      ws.(4ul*.i+.3ul) <- vec_interleave_high_n 2 ws1 ws3)

unfold let multiblock (a:sha2_alg) (m:m_spec) =
   multibuf (lanes a m) (block_len a)

#push-options "--max_ifuel 2 --max_fuel 2 --z3rlimit 100"
inline_for_extraction
val load_ws (#a: sha2_alg) (#m:m_spec)
            (b: multiblock a m) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live_multi h b /\ live h ws /\ disjoint_multi b ws))
    (ensures (fun h0 _ h1 -> modifies (loc ws) h0 h1))
let load_ws #a #m b ws =
  match lanes a m with
  | 1 -> let b = b <: lbuffer uint8 (block_len a) in 
         load_ws1 b ws
  | 4 -> admit();
         assert (lanes a m == 4);
         let b : lbuffer uint8 (block_len a) &
                 (lbuffer uint8 (block_len a) &
                 (lbuffer uint8 (block_len a) &
                  lbuffer uint8 (block_len a) ))
                 = b <: NTup.ntuple (lbuffer uint8 (block_len a)) 4 in
         let (b0,(b1,(b2,b3))) = b in
//         let b0 = b.(|0|) in
//         let b1 = b.(|1|) in
//         let b2 = b.(|2|) in
//         let b3 = b.(|3|) in
         load_ws4 b0 b1 b2 b3 ws
  | _ -> admit()
#pop-options

inline_for_extraction
val ws_next (#a: sha2_alg) (#m:m_spec)
            (k:size_t{size_v k > 0 /\ size_v k < size_v (num_rounds16 a)}) (ws: ws_t a m):
    Stack unit
    (requires (fun h -> live h ws))
    (ensures (fun h0 _ h1 ->
      modifies (loc ws) h0 h1))
let ws_next #a #m k ws =
  let h0 = ST.get() in
  loop_nospec #h0 16ul ws (fun i ->
      let t16 = ws.(i) in
      let t15 = ws.((i+.1ul) %. 16ul) in
      let t7  = ws.((i+.9ul) %. 16ul) in
      let t2  = ws.((i+.14ul) %. 16ul) in
      let s1 = _sigma1 t2 in
      let s0 = _sigma0 t15 in
      ws.(i) <- (s1 +| t7 +| s0 +| t16))

inline_for_extraction
val shuffle: #a:sha2_alg -> #m:m_spec -> ws:ws_t a m -> hash:state_t a m ->
    Stack unit
    (requires (fun h ->
      live h hash /\ live h ws /\
      disjoint hash ws))
    (ensures (fun h0 _ h1 ->
      modifies2 ws hash h0 h1))

let shuffle #a #m ws hash =
  let h0 = ST.get() in
  loop_nospec2 #h0 (num_rounds16 a) ws hash
    (fun i ->
      let h1 = ST.get() in
      loop_nospec #h1 16ul hash
      (fun j ->
       let k_t = index_k0 a (16ul *. i +. j) in
       let ws_t = ws.(j) in
       shuffle_core k_t ws_t hash);
      if i <. num_rounds16 a -. 1ul then
        ws_next (i+.1ul) ws)


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
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))
let init #a #m hash =
  let h0 = ST.get() in
  loop_nospec #h0 8ul hash (fun i ->
    let hi = index_h0 a i in
    hash.(i) <- load_element a m hi)


let update_t (a:sha2_alg) (m:m_spec) = b:multiblock a m -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))


#push-options "--max_fuel 0 --max_ifuel 2 --z3rlimit 50"
inline_for_extraction
val update: #a:sha2_alg -> #m:m_spec -> update_t a m
let update #a #m b hash =
  push_frame ();
  let hash_old = create 8ul (zero_element a m) in
  copy hash_old hash;
  let ws = create 16ul (zero_element a m) in
  let h0 = ST.get() in
  assert (live_multi h0 b);
  assert (disjoint_multi b ws);
  load_ws b ws;
  shuffle ws hash;
  map2T 8ul hash (+|) hash hash_old; 
  pop_frame()
#pop-options

inline_for_extraction
let padded_blocks (a:sha2_alg) (len:size_t{v len < block_length a}) =
  if (len +. len_len a +. 1ul <=. block_len a) then 1ul else 2ul

inline_for_extraction
val update1_last: #a:sha2_alg -> #m:m_spec{lanes a m = 1} ->
                  upd: update_t a m ->
                  totlen:len_t a ->
                  len:size_t{v len < block_length a} ->
                  b:lbuffer uint8 len -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h b /\ live h hash /\ disjoint b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))
let update1_last #a #m upd totlen len b hash =
  push_frame ();
  let last = create (2ul *. block_len a) (u8 0) in
  copy (sub last 0ul len) b;
  last.(len) <- u8 0x80;
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in 
  let blocks = padded_blocks a len in
  let fin = blocks *. block_len a in
  let len_by = sub last (fin -. len_len a) (len_len a) in
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) len_by total_len_bits;
  let b0 = sub last 0ul (block_len a) in
  upd b0 hash;
  if blocks >. 1ul then (
    let b1 = sub last (block_len a) (block_len a) in
    upd b1 hash
  );
  pop_frame()

inline_for_extraction
val update4_last: #a:sha2_alg -> #m:m_spec{lanes a m = 4} ->
                  upd: update_t a m ->
                  totlen:len_t a ->
                  len:size_t{v len < block_length a} ->
                  b0:lbuffer uint8 len ->
                  b1:lbuffer uint8 len ->
                  b2:lbuffer uint8 len ->
                  b3:lbuffer uint8 len ->
                  hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\ live h hash /\ disjoint b0 hash /\ disjoint b1 hash /\ disjoint b2 hash /\ disjoint b3 hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))

#push-options "--z3rlimit 200"
let update4_last #a #m upd totlen len b0 b1 b2 b3 hash =
  push_frame ();
  admit();
  let last = create (8ul *. block_len a) (u8 0) in
  let last0 = sub last 0ul (2ul *. block_len a) in
  let last1 = sub last (2ul *. block_len a) (2ul *. block_len a) in
  let last2 = sub last (4ul *. block_len a) (2ul *. block_len a) in
  let last3 = sub last (6ul *. block_len a) (2ul *. block_len a) in
  copy (sub last0 0ul len) b0;
  copy (sub last1 0ul len) b1;
  copy (sub last2 0ul len) b2;
  copy (sub last3 0ul len) b3;
  last0.(len) <- u8 0x80;
  last1.(len) <- u8 0x80;
  last2.(len) <- u8 0x80;
  last3.(len) <- u8 0x80;
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in 
  let blocks = padded_blocks a len in
  let fin = blocks *. block_len a in
  let len_buf0 = sub last0 (fin -. len_len a) (len_len a) in
  let len_buf1 = sub last1 (fin -. len_len a) (len_len a) in
  let len_buf2 = sub last2 (fin -. len_len a) (len_len a) in
  let len_buf3 = sub last3 (fin -. len_len a) (len_len a) in
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) len_buf0 total_len_bits;
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) len_buf1 total_len_bits;
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) len_buf2 total_len_bits;
  Lib.ByteBuffer.uint_to_bytes_be #(len_int_type a) len_buf3 total_len_bits;
  let last00 = sub last0 0ul (block_len a) in
  let last10 = sub last1 0ul (block_len a) in
  let last20 = sub last2 0ul (block_len a) in
  let last30 = sub last3 0ul (block_len a) in
  let mb:multibuf 4 (block_len a) = (last00, (last10, (last20, last30))) in
  upd mb hash;
  if blocks >. 1ul then (
    let last01 = sub last0 (block_len a) (block_len a) in
    let last11 = sub last1 (block_len a) (block_len a) in
    let last21 = sub last2 (block_len a) (block_len a) in
    let last31 = sub last3 (block_len a) (block_len a) in
    let mb: multibuf 4 (block_len a) = (last01, (last11, (last21, last31))) in
    upd mb hash
  );
  pop_frame()
#pop-options

inline_for_extraction
val update_last: #a:sha2_alg -> #m:m_spec{lanes a m = 1} ->
                  upd: update_t a m ->
                  totlen:len_t a ->
                  len:size_t{v len < block_length a} ->
                  b:multibuf (lanes a m) len -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))

let update_last #a #m upd totlen len b hash =
  match lanes a m with
  | 1 -> update1_last upd totlen len b hash
  | 4 -> let (b0,(b1,(b2,b3))) = b <: multibuf 4 len in
         update4_last upd totlen len b0 b1 b2 b3 hash
  | _ -> admit()


inline_for_extraction
val finish1: #a:sha2_alg -> #m:m_spec{lanes a m = 1} ->
             b:lbuffer uint8 (hash_len a) -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h b /\ live h hash /\ disjoint b hash))
    (ensures (fun h0 _ h1 -> modifies1 b h0 h1))
let finish1 #a #m b hash =
  let h0 = ST.get() in
  loop_nospec #h0 (hash_word_len a) b (fun i ->
       vec_store_be (sub b (i *. word_len a) (word_len a)) hash.(i))

inline_for_extraction
val finish4: #a:sha2_alg -> #m:m_spec{lanes a m = 4} ->
             b0:lbuffer uint8 (hash_len a) ->
             b1:lbuffer uint8 (hash_len a) ->
             b2:lbuffer uint8 (hash_len a) ->
             b3:lbuffer uint8 (hash_len a) ->
             hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\ live h hash /\ disjoint b0 hash /\ disjoint b1 hash /\ disjoint b2 hash /\ disjoint b3 hash))
    (ensures (fun h0 _ h1 -> modifies (loc b0 |+| loc b1 |+| loc b2 |+| loc b3) h0 h1))
let finish4 #a #m b0 b1 b2 b3 hash =
  push_frame();
  admit();
  let hbuf = create (4ul *. 8ul *. word_len a) (u8 0) in 
  let h0 = ST.get() in
  loop_nospec #h0 8ul hbuf (fun i ->
       vec_store_be (sub hbuf (4ul *. i *. word_len a) (4ul *. word_len a)) hash.(i));
  let h0 = ST.get() in
  loop_nospec #h0 (hash_word_len a) b0 (fun i ->
       copy (sub b0 (i *. word_len a) (word_len a)) (sub hbuf (4ul*.i*.word_len a) (word_len a)));
  let h0 = ST.get() in
  loop_nospec #h0 (hash_word_len a) b1 (fun i ->
       copy (sub b1 (i *. word_len a) (word_len a)) (sub hbuf (4ul*.i*.word_len a+.word_len a) (word_len a)));
  let h0 = ST.get() in
  loop_nospec #h0 (hash_word_len a) b2 (fun i ->
       copy (sub b2 (i *. word_len a) (word_len a)) (sub hbuf (4ul*.i*.word_len a+.2ul*.word_len a) (word_len a)));
  let h0 = ST.get() in
  loop_nospec #h0 (hash_word_len a) b3 (fun i ->
       copy (sub b3 (i *. word_len a) (word_len a)) (sub hbuf (4ul*.i*.word_len a+.3ul*.word_len a) (word_len a)));
  pop_frame()

inline_for_extraction
val finish: #a:sha2_alg -> #m:m_spec ->
             b:multibuf (lanes a m) (hash_len a) ->
             hash:state_t a m ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies_multi b h0 h1))

#push-options "--z3rlimit 200"
let finish #a #m b hash =
  match lanes a m with
  | 1 -> finish1 #a #m b hash
  | 4 -> admit();
         let (b0,(b1,(b2,b3))) = b <: multibuf 4 (hash_len a) in
         finish4 b0 b1 b2 b3 hash
  | _ -> admit()

inline_for_extraction
val get_multiblock: #a:sha2_alg -> #m:m_spec ->
                    len:size_t -> b:multibuf (lanes a m) len ->
                    i:size_t{v i < v len / block_length a} ->
                    Stack (multiblock a m)
                    (requires (fun h -> live_multi h b))
                    (ensures (fun h0 _ h1 -> h0 == h1))

let get_multiblock #a #m len b i =
  match lanes a m with
  | 1 -> sub (b <: lbuffer uint8 len) (i *. block_len a) (block_len a)
  | 4 -> admit();
         let (b0,(b1,(b2,b3))) = b <: multibuf 4 len in
         let bl0 = sub (b0 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let bl1 = sub (b1 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let bl2 = sub (b2 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let bl3 = sub (b3 <: lbuffer uint8 len) (i *. block_len a) (block_len a) in
         let mb : multibuf 4 (block_len a) = (bl0, (bl1, (bl2, bl3))) in
         mb
  | _ -> admit()

inline_for_extraction
val get_multilast: #a:sha2_alg -> #m:m_spec ->
                   len:size_t -> b:multibuf (lanes a m) len ->
                   Stack (multibuf (lanes a m) (len %. block_len a))
                   (requires (fun h -> live_multi h b))
                   (ensures (fun h0 _ h1 -> h0 == h1))

let get_multilast #a #m len b =
  let rem = len %. block_len a in
  match lanes a m with
  | 1 -> sub (b <: lbuffer uint8 len) (len -. rem) rem
  | 4 -> admit();
         let (b0,(b1,(b2,b3))) = b <: multibuf 4 len in
         let bl0 = sub (b0 <: lbuffer uint8 len) (len -. rem) rem in
         let bl1 = sub (b1 <: lbuffer uint8 len) (len -. rem) rem in
         let bl2 = sub (b2 <: lbuffer uint8 len) (len -. rem) rem in
         let bl3 = sub (b3 <: lbuffer uint8 len) (len -. rem) rem in
         let mb : multibuf 4 rem = (bl0, (bl1, (bl2, bl3))) in
         mb
  | _ -> admit()

inline_for_extraction
val hash: #a:sha2_alg -> #m:m_spec -> upd:update_t a m ->
          h:multibuf (lanes a m) (hash_len a) ->
          len:size_t ->
          b:multibuf (lanes a m) len ->
    Stack unit
    (requires (fun h0 -> live_multi h0 b /\ live_multi h0 h /\ disjoint_multi_multi h b))
    (ensures (fun h0 _ h1 -> modifies_multi h h0 h1))
let hash #a #m upd h len b =
    push_frame();
    let st = alloc a m in
    init st;
    [@inline_let]
    let spec h i acc = acc in
    admit();
    let h0 = ST.get() in
    loop1 h0 (len /. block_len a) st spec
      (fun i -> 
        let mb: multibuf (lanes a m) (block_len a) = get_multiblock len b i in
        upd mb st); 
    let rem = len %. block_len a in
    let mb: multibuf (lanes a m) rem = get_multilast len b in
    update_last upd len rem mb st;
    finish h st;
    pop_frame()

[@CInline]
val sha256_update1: b:block_t SHA2_256 -> hash:state_t SHA2_256 M32 ->
    Stack unit
    (requires (fun h -> live h b /\ live h hash /\ disjoint b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))
let sha256_update1 b hash = update #SHA2_256 #M32 b hash

let sha256 h len b = hash #SHA2_256 #M32 sha256_update1 h len (b <: lbuffer uint8 len)

[@CInline]
val sha256_update4: b:multiblock SHA2_256 M128 ->
                    hash:state_t SHA2_256 M128 ->
    Stack unit
    (requires (fun h -> live_multi h b /\ live h hash /\ disjoint_multi b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))
let sha256_update4 b hash =
  update #SHA2_256 #M128 b hash

let sha256_4 r0 r1 r2 r3 len b0 b1 b2 b3 =
  admit();
  let ib:multibuf 4 len = (b0,(b1,(b2,b3))) in
  let rb:multibuf 4 (hash_len SHA2_256) = (r0,(r1,(r2,r3))) in
  hash #SHA2_256 #M128 sha256_update4 rb len ib

