module Hacl.Impl.SHA2.Core

open FStar.Mul
module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Sequence
open Lib.Buffer
open Lib.IntVector
open Spec.Hash.Definitions
open Hacl.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Spec.SHA2
friend Spec.SHA2
friend Spec.SHA2.Lemmas

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
type m_spec =
  | M32
  | M128
  | M256
  | M512

inline_for_extraction
let lanes (a:sha2_alg) (m:m_spec) : nat =
  match a,m with
  | SHA2_224,M128
  | SHA2_256,M128 -> 4
  | SHA2_224,M256
  | SHA2_256,M256 -> 8
  | SHA2_224,M512
  | SHA2_256,M512 -> 16
  | SHA2_384,M128
  | SHA2_512,M128 -> 2
  | SHA2_384,M256
  | SHA2_512,M256 -> 4
  | SHA2_384,M512
  | SHA2_512,M512 -> 8
  | _ -> 1

inline_for_extraction
let element_t (a:sha2_alg) (m:m_spec) = vec_t (word_t a) (lanes a m)
inline_for_extraction
val zero_element: a:sha2_alg -> m:m_spec -> element_t a m
let zero_element a m = vec_zero (word_t a) (lanes a m) 

inline_for_extraction
val load_element: a:sha2_alg -> m:m_spec -> word a -> element_t a m
let load_element a m x = vec_load x (lanes a m) 

inline_for_extraction
let ( +| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( +| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( +| ) #U64 #(lanes a m)

inline_for_extraction
let ( ^| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( ^| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( ^| ) #U64 #(lanes a m)

inline_for_extraction
let ( &| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( &| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( &| ) #U64 #(lanes a m)

inline_for_extraction
let ( ~| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( ~| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( ~| ) #U64 #(lanes a m)

inline_for_extraction
let ( >>>| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> rotval (word_t a) -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( >>>| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( >>>| ) #U64 #(lanes a m)

inline_for_extraction
let ( >>| ) (#a:sha2_alg) (#m:m_spec): element_t a m -> shiftval (word_t a) -> element_t a m =
  match a with
  | SHA2_224 | SHA2_256 -> ( >>| ) #U32 #(lanes a m)
  | SHA2_384 | SHA2_512 -> ( >>| ) #U64 #(lanes a m)

inline_for_extraction
val _Ch: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m -> element_t a m -> element_t a m
let _Ch #a #m x y z = (x &| y) ^| (~| x &| z) //TODO: Ch(e,f,g)=((f^g)&e)^g

inline_for_extraction
val _Maj: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m -> element_t a m -> element_t a m
let _Maj #a #m x y z = (x &| y) ^| ((x &| z) ^| (y &| z)) // TODO: Maj(a,b,c) = Ch(a^b,c,b)

inline_for_extraction
val _Sigma0: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _Sigma0 #a #m x = Spec.((x >>>| (op0 a).c0) ^| (x >>>| (op0 a).c1) ^| (x >>>| (op0 a).c2))

inline_for_extraction
val _Sigma1: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _Sigma1 #a #m x = Spec.((x >>>| (op0 a).c3) ^| (x >>>| (op0 a).c4) ^| (x >>>| (op0 a).c5))

inline_for_extraction
val _sigma0: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _sigma0 #a #m x = Spec.((x >>>| (op0 a).e0) ^| (x >>>| (op0 a).e1) ^| (x >>| (op0 a).e2))

inline_for_extraction
val _sigma1: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
inline_for_extraction
let _sigma1 #a #m x = Spec.((x >>>| (op0 a).e3) ^| (x >>>| (op0 a).e4) ^| (x >>| (op0 a).e5))

noextract
let _Ch_lemma #a #m x y z :
  Lemma (vec_v (_Ch #a #m x y z) ==
         Lib.Sequence.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i])) =
        eq_intro (vec_v (_Ch #a #m x y z))
        (Lib.Sequence.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))

noextract
let _Maj_lemma #a #m x y z :
  Lemma (vec_v (_Maj #a #m x y z) ==
         Lib.Sequence.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i])) =
        eq_intro (vec_v (_Maj #a #m x y z))
        (Lib.Sequence.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))

noextract
let _Sigma0_lemma #a #m x :
  Lemma (vec_v (_Sigma0 #a #m x) ==
         Lib.Sequence.map (Spec._Sigma0 a) (vec_v x)) =
        eq_intro (vec_v (_Sigma0 #a #m x)) (Lib.Sequence.map (Spec._Sigma0 a) (vec_v x))

noextract
let _Sigma1_lemma #a #m x :
  Lemma (vec_v (_Sigma1 #a #m x) ==
         Lib.Sequence.map (Spec._Sigma1 a) (vec_v x)) =
        eq_intro (vec_v (_Sigma1 #a #m x)) (Lib.Sequence.map (Spec._Sigma1 a) (vec_v x))

noextract
let _sigma0_lemma #a #m x :
  Lemma (vec_v (_sigma0 #a #m x) ==
         Lib.Sequence.map (Spec._sigma0 a) (vec_v x)) =
        eq_intro (vec_v (_sigma0 #a #m x)) (Lib.Sequence.map (Spec._sigma0 a) (vec_v x))

noextract
let _sigma1_lemma #a #m x :
  Lemma (vec_v (_sigma1 #a #m x) ==
         Lib.Sequence.map (Spec._sigma1 a) (vec_v x)) =
        eq_intro (vec_v (_sigma1 #a #m x)) (Lib.Sequence.map (Spec._sigma1 a) (vec_v x))


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


let update1_t (a:sha2_alg) (m:m_spec{lanes a m = 1}) = b:block_t a -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h b /\ live h hash /\ disjoint b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))

let update4_t (a:sha2_alg) (m:m_spec{lanes a m = 4}) = b0:block_t a -> b1:block_t a -> b2:block_t a -> b3:block_t a -> hash:state_t a m ->
    Stack unit
    (requires (fun h -> live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\ live h hash /\ disjoint b0 hash /\ disjoint b1 hash /\ disjoint b2 hash /\ disjoint b3 hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))

inline_for_extraction
val update1: #a:sha2_alg -> #m:m_spec{lanes a m = 1} -> update1_t a m
let update1 #a #m b hash =
  push_frame ();
  let hash_old = create 8ul (zero_element a m) in
  copy hash_old hash;
  let ws = create 16ul (zero_element a m) in
  load_ws1 b ws;
  shuffle ws hash;
  map2T 8ul hash (+|) hash hash_old; 
  pop_frame()

inline_for_extraction
val update4: #a:sha2_alg -> #m:m_spec{lanes a m = 4} -> update4_t a m
let update4 #a #m b0 b1 b2 b3 hash =
  push_frame ();
  let hash_old = create 8ul (zero_element a m) in
  copy hash_old hash;
  let ws = create 16ul (zero_element a m) in
  load_ws4 b0 b1 b2 b3 ws;
  shuffle ws hash;
  map2T 8ul hash (+|) hash hash_old; 
  pop_frame()

inline_for_extraction
let padded_blocks (a:sha2_alg) (len:size_t{v len < block_length a}) =
  if (len +. len_len a +. 1ul <=. block_len a) then 1ul else 2ul
  
inline_for_extraction
val update1_last: #a:sha2_alg -> #m:m_spec{lanes a m = 1} ->
                  upd: update1_t a m ->
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
                  upd: update4_t a m ->
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
  upd last00 last10 last20 last30 hash;
  if blocks >. 1ul then (
    let last01 = sub last0 (block_len a) (block_len a) in
    let last11 = sub last1 (block_len a) (block_len a) in
    let last21 = sub last2 (block_len a) (block_len a) in
    let last31 = sub last3 (block_len a) (block_len a) in
    upd last01 last11 last21 last31 hash
  );
  pop_frame()
#pop-options

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
val hash1: #a:sha2_alg -> upd:update1_t a M32 -> h:lbuffer uint8 (hash_len a) ->
           len:size_t -> b:buffer uint8{length b == v len} ->
    Stack unit
    (requires (fun h0 -> live h0 b /\ live h0 h /\ disjoint h b))
    (ensures (fun h0 _ h1 -> modifies (loc h) h0 h1))
let hash1 #a upd h len b =
    push_frame();
    let st = alloc a M32 in
    init st;
    [@inline_let]
    let spec_f block acc = acc in
    [@inline_let]
    let spec_l len block acc = acc in
    admit();
    loop_blocks #uint8 #(element_t a M32) #8ul (block_len a) len b spec_f spec_l
                upd (update1_last #a #M32 upd len) st;
    finish1 h st;
    pop_frame()

inline_for_extraction
val hash4: #a:sha2_alg -> #m:m_spec{lanes a m == 4} -> upd:update4_t a m ->
           r0:lbuffer uint8 (hash_len a) ->
           r1:lbuffer uint8 (hash_len a) ->
           r2:lbuffer uint8 (hash_len a) ->
           r3:lbuffer uint8 (hash_len a) ->
           len:size_t ->
           b0:lbuffer uint8 len ->
           b1:lbuffer uint8 len ->
           b2:lbuffer uint8 len ->
           b3:lbuffer uint8 len ->
    Stack unit
    (requires (fun h0 -> live h0 b0 /\ live h0 b1 /\ live h0 b2 /\ live h0 b3 /\
                       live h0 r0 /\ live h0 r1 /\ live h0 r2 /\ live h0 r3))
    (ensures (fun h0 _ h1 -> modifies (loc r0 |+| loc r1 |+| loc r2 |+| loc r3) h0 h1))
let hash4 #a #m upd r0 r1 r2 r3 len b0 b1 b2 b3 =
    push_frame();
    let st = alloc a m in
    init st;
    [@inline_let]
    let spec h i acc = acc in
    admit();
    let h0 = ST.get() in
    loop1 h0 (len /. block_len a) st spec
      (fun i -> 
        let bl0 = sub b0 (i*. block_len a) (block_len a) in
        let bl1 = sub b1 (i*. block_len a) (block_len a) in
        let bl2 = sub b2 (i*. block_len a) (block_len a) in
        let bl3 = sub b3 (i*. block_len a) (block_len a) in
        upd bl0 bl1 bl2 bl3 st); 
    let rem = len %. block_len a in
    let bl0 = sub b0 (len -. rem) rem in
    let bl1 = sub b1 (len -. rem) rem in
    let bl2 = sub b2 (len -. rem) rem in
    let bl3 = sub b3 (len -. rem) rem in
    update4_last upd len rem bl0 bl1 bl2 bl3 st;
    finish4 r0 r1 r2 r3 st;
    pop_frame()

[@CInline]
val sha256_update1: b:block_t SHA2_256 -> hash:state_t SHA2_256 M32 ->
    Stack unit
    (requires (fun h -> live h b /\ live h hash /\ disjoint b hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))
let sha256_update1 b hash = update1 #SHA2_256 #M32 b hash

let sha256 hash len b = hash1 #SHA2_256 sha256_update1 hash len b

[@CInline]
val sha256_update4: b0:block_t SHA2_256 ->
                    b1:block_t SHA2_256 ->
                    b2:block_t SHA2_256 ->
                    b3:block_t SHA2_256 ->
                    hash:state_t SHA2_256 M128 ->
    Stack unit
    (requires (fun h -> live h b0 /\ live h b1 /\ live h b2 /\ live h b3 /\ live h hash /\ disjoint b0 hash /\ disjoint b1 hash /\ disjoint b2 hash /\ disjoint b3 hash))
    (ensures (fun h0 _ h1 -> modifies1 hash h0 h1))
let sha256_update4 b0 b1 b2 b3 hash = update4 #SHA2_256 #M128 b0 b1 b2 b3 hash

let sha256_4 r0 r1 r2 r3 len b0 b1 b2 b3 = hash4 #SHA2_256 sha256_update4 r0 r1 r2 r3 len b0 b1 b2 b3

(*
noextract inline_for_extraction
  val alloca: a:sha2_alg -> alloca_st a
noextract inline_for_extraction
let alloca a () =
  [@ inline_let ]
  let l: list (word a) = Spec.(match a with
    | SHA2_224 -> Constants.h224_l
    | SHA2_256 -> Constants.h256_l
    | SHA2_384 -> Constants.h384_l
    | SHA2_512 -> Constants.h512_l) in
  B.alloca_of_list l
#set-options "--max_fuel 0"

inline_for_extraction noextract
let alloca_224: alloca_st SHA2_224 = alloca SHA2_224
inline_for_extraction noextract
let alloca_256: alloca_st SHA2_256 = alloca SHA2_256
inline_for_extraction noextract
let alloca_384: alloca_st SHA2_384 = alloca SHA2_384
inline_for_extraction noextract
let alloca_512: alloca_st SHA2_512 = alloca SHA2_512
*)
(** Init *)
(*
noextract inline_for_extraction
val init: a:sha2_alg -> init_st a
noextract inline_for_extraction
let init a s =
  let h0 = ST.get () in
  let inv h1 (i: nat): Type0 =
    i <= 8 /\
    M.(modifies (loc_buffer s) h0 h1) /\
    S.equal (S.slice (B.as_seq h1 s) 0 i) (S.slice (h a) 0 i)
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < 8) }):
    ST.Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures (fun h0 _ h1 -> U32.(inv h0 (v i) /\ inv h1 (v i + 1))))
  =
    s.(i) <- index_h a i;
    let h2 = ST.get () in
    assert (S.equal (S.slice (B.as_seq h2 s) 0 (U32.v i + 1))
      (S.append
        (S.slice (B.as_seq h2 s) 0 (U32.v i))
        (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1))))
  in
  C.Loops.for 0ul 8ul inv f
let init_224: init_st SHA2_224 = init SHA2_224
let init_256: init_st SHA2_256 = init SHA2_256
let init_384: init_st SHA2_384 = init SHA2_384
let init_512: init_st SHA2_512 = init SHA2_512
*)


      
      
  
#set-options "--max_fuel 0"
(*
inline_for_extraction
let words_state (a: sha2_alg) =
  b:B.buffer (word a) { B.length b = state_word_length a }

inline_for_extraction
val k0 (a: sha2_alg): ST.Stack (IB.ibuffer (word a))
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 ->
    B.length b = Spec.size_k_w a /\
    B.live h1 b /\
    M.(modifies loc_none h0 h1) /\
    B.as_seq h1 b == Spec.k0 a))
inline_for_extraction
let k0 a =
  match a with
  | SHA2_224 | SHA2_256 ->
      IB.recall_contents k224_256 (S.seq_of_list Constants.k224_256_l);
      k224_256
  | SHA2_384 | SHA2_512 ->
      IB.recall_contents k384_512 (S.seq_of_list Constants.k384_512_l);
      k384_512


inline_for_extraction
val shuffle_core (a: sha2_alg)
  (block: G.erased (block_b a))
  (hash: words_state a)
  (ws: ws_w a)
  (t: U32.t { U32.v t < Spec.size_k_w a }):
  ST.Stack unit
    (requires (fun h ->
      let block = G.reveal block in
      let b = block_words_be a h block in
      B.live h block /\ B.live h hash /\ B.live h ws /\
      B.disjoint block hash /\ B.disjoint block ws /\ B.disjoint hash ws /\
      B.as_seq h ws == S.init (Spec.size_k_w a) (SpecLemmas.ws a b)))
    (ensures (fun h0 _ h1 ->
      let block = G.reveal block in
      let b = block_words_be a h0 block in
      M.(modifies (loc_buffer hash) h0 h1) /\
      B.as_seq h1 hash == SpecLemmas.shuffle_core a b (B.as_seq h0 hash) (U32.v t)))

#set-options "--max_fuel 1 --z3rlimit 100"
inline_for_extraction
let shuffle_core a block hash ws t =
  let a0 = hash.(0ul) in
  let b0 = hash.(1ul) in
  let c0 = hash.(2ul) in
  let d0 = hash.(3ul) in
  let e0 = hash.(4ul) in
  let f0 = hash.(5ul) in
  let g0 = hash.(6ul) in
  let h0 = hash.(7ul) in

  let w = ws.(t) in

  let t1 = h0 +. (Spec._Sigma1 a e0) +. (Spec._Ch a e0 f0 g0) +. (k0 a).(t) +. w in
  let t2 = (Spec._Sigma0 a a0) +. (Spec._Maj a a0 b0 c0) in

  hash.(0ul) <- t1 +. t2;
  hash.(1ul) <- a0;
  hash.(2ul) <- b0;
  hash.(3ul) <- c0;
  hash.(4ul) <- d0 +. t1;
  hash.(5ul) <- e0;
  hash.(6ul) <- f0;
  hash.(7ul) <- g0;

  (**) reveal_opaque (`%SpecLemmas.shuffle_core) SpecLemmas.shuffle_core;
  (**) let h = ST.get () in
  (**) [@inline_let]
  (**) let l = [ t1 +. t2; a0; b0; c0; d0 +. t1; e0; f0; g0 ] in
  (**) assert_norm (List.Tot.length l = 8);
  (**) S.intro_of_list #(word a) (B.as_seq h hash) l

#reset-options "--max_fuel 2 --z3rlimit 500"
inline_for_extraction
val shuffle: a:sha2_alg -> block:G.erased (block_b a) -> hash:words_state a -> ws:ws_w a ->
  ST.Stack unit
    (requires (fun h ->
      let block = G.reveal block in
      let b = block_words_be a h block in
      B.live h block /\ B.live h hash /\ B.live h ws /\
      B.disjoint block hash /\ B.disjoint block ws /\ B.disjoint hash ws /\
      B.as_seq h ws == S.init (Spec.size_k_w a) (SpecLemmas.ws a b)))
    (ensures (fun h0 _ h1 ->
      let block = G.reveal block in
      let b = block_words_be a h0 block in
      M.(modifies (loc_buffer hash) h0 h1 /\
      B.as_seq h1 hash == Spec.shuffle a (B.as_seq h0 hash) b)))

inline_for_extraction
let size_k_w (a: sha2_alg) = U32.uint_to_t (Spec.size_k_w a)

inline_for_extraction
let shuffle a block hash ws =
  let h0 = ST.get () in
  let inv (h1: HS.mem) (i: nat) =
    let block = G.reveal block in
    let block = block_words_be a h0 block in
    M.(modifies (loc_buffer hash) h0 h1) /\
    i <= Spec.size_k_w a /\
    B.as_seq h1 hash ==
      Spec.Loops.repeat_range 0 i (SpecLemmas.shuffle_core a block) (B.as_seq h0 hash)
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < Spec.size_k_w a)}):
    ST.Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures (fun h0 _ h1 ->
        U32.(inv h0 (v i) /\ inv h1 (v i + 1))))
  =
    (**) let h1 = ST.get () in
    shuffle_core a block hash ws i;
    (**) let h2 = ST.get () in
    (**) let block = G.reveal block in
    (**) let block = block_words_be a h0 block in
    (**) let hash = B.as_seq h0 hash in
    (**) Spec.Loops.repeat_range_induction 0 (U32.v i + 1) (SpecLemmas.shuffle_core a block) hash
  in
  (**) Spec.Loops.repeat_range_base 0 (SpecLemmas.shuffle_core a (block_words_be a h0 (G.reveal block))) (B.as_seq h0 hash);
  C.Loops.for 0ul (size_k_w a) inv f;
  reveal_opaque (`%Spec.shuffle) Spec.shuffle;
  (**) let hash = B.as_seq h0 hash in
  (**) let block = G.reveal block in
  (**) let block = block_words_be a h0 block in
  SpecLemmas.shuffle_is_shuffle_pre a hash block

inline_for_extraction
let zero (a: sha2_alg): word a =
  match a with
  | SHA2_224 | SHA2_256 -> u32 0
  | SHA2_384 | SHA2_512 -> u64 0

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

noextract inline_for_extraction
val update: a:sha2_alg -> update_st a
noextract inline_for_extraction
let update a hash block =
  (**) ST.push_frame ();
  (**) let h0 = ST.get () in
  let hash1: words_state a = B.alloca (zero a) 8ul in
  let computed_ws: ws_w a = B.alloca (zero a) (U32.uint_to_t (Spec.size_k_w a)) in
  ws a block computed_ws;
  B.blit hash 0ul hash1 0ul 8ul;
  (**) let h1 = ST.get () in
  (**) assert (S.equal (B.as_seq h1 hash1) (B.as_seq h0 hash));
  (**) assert (S.equal (B.as_seq h1 hash) (B.as_seq h0 hash));
  shuffle a (G.hide block) hash1 computed_ws;
  (**) let h2 = ST.get () in
  (**) assert (let block_w = words_of_bytes a #block_word_length (B.as_seq h1 block) in
	       S.equal (B.as_seq h2 hash1) (Spec.shuffle a (B.as_seq h1 hash1) block_w));
  C.Loops.in_place_map2 hash hash1 8ul ( +. );
  (**) let h3 = ST.get () in
  (**) assert (S.equal (B.as_seq h3 hash) (Spec.update_pre a (B.as_seq h1 hash1) (B.as_seq h1 block)));
  ST.pop_frame();
  (**) reveal_opaque (`%Spec.update) Spec.update


let update_224: update_st SHA2_224 = update SHA2_224
let update_256: update_st SHA2_256 = update SHA2_256
let update_384: update_st SHA2_384 = update SHA2_384
let update_512: update_st SHA2_512 = update SHA2_512

let pad_224: pad_st SHA2_224 = Hacl.Hash.PadFinish.pad SHA2_224
let pad_256: pad_st SHA2_256 = Hacl.Hash.PadFinish.pad SHA2_256
let pad_384: pad_st SHA2_384 = Hacl.Hash.PadFinish.pad SHA2_384
let pad_512: pad_st SHA2_512 = Hacl.Hash.PadFinish.pad SHA2_512

let finish_224: finish_st SHA2_224 = Hacl.Hash.PadFinish.finish SHA2_224
let finish_256: finish_st SHA2_256 = Hacl.Hash.PadFinish.finish SHA2_256
let finish_384: finish_st SHA2_384 = Hacl.Hash.PadFinish.finish SHA2_384
let finish_512: finish_st SHA2_512 = Hacl.Hash.PadFinish.finish SHA2_512
