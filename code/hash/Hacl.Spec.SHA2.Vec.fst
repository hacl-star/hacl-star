module Hacl.Spec.SHA2.Vec

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.LoopCombinators
open Spec.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Spec.SHA2
friend Spec.SHA2
friend Spec.SHA2.Lemmas

noextract
type m_spec =
  | M32
  | M128
  | M256
  | M512

inline_for_extraction
let lanes_t = n:nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8 \/ n == 16}
inline_for_extraction let lanes (a:sha2_alg) (m:m_spec) : lanes_t =
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
        Lib.Sequence.eq_intro (vec_v (_Ch #a #m x y z))
        (Lib.Sequence.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))

noextract
let _Maj_lemma #a #m x y z :
  Lemma (vec_v (_Maj #a #m x y z) ==
         Lib.Sequence.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i])) =
        Lib.Sequence.eq_intro (vec_v (_Maj #a #m x y z))
        (Lib.Sequence.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))

noextract
let _Sigma0_lemma #a #m x :
  Lemma (vec_v (_Sigma0 #a #m x) ==
         Lib.Sequence.map (Spec._Sigma0 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_Sigma0 #a #m x)) (Lib.Sequence.map (Spec._Sigma0 a) (vec_v x))

noextract
let _Sigma1_lemma #a #m x :
  Lemma (vec_v (_Sigma1 #a #m x) ==
         Lib.Sequence.map (Spec._Sigma1 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_Sigma1 #a #m x)) (Lib.Sequence.map (Spec._Sigma1 a) (vec_v x))

noextract
let _sigma0_lemma #a #m x :
  Lemma (vec_v (_sigma0 #a #m x) ==
         Lib.Sequence.map (Spec._sigma0 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_sigma0 #a #m x)) (Lib.Sequence.map (Spec._sigma0 a) (vec_v x))

noextract
let _sigma1_lemma #a #m x :
  Lemma (vec_v (_sigma1 #a #m x) ==
         Lib.Sequence.map (Spec._sigma1 a) (vec_v x)) =
        Lib.Sequence.eq_intro (vec_v (_sigma1 #a #m x)) (Lib.Sequence.map (Spec._sigma1 a) (vec_v x))

noextract
let state_spec (a:sha2_alg) (m:m_spec) =
  lseq (element_t a m) 8

noextract
let block_spec (a:sha2_alg) =
  lseq uint8 (block_length a)
noextract
let ws_spec (a:sha2_alg) (m:m_spec) =
  lseq (element_t a m) 16

noextract
let state_spec_v (#a:sha2_alg) (#m:m_spec) (st:state_spec a m) : GTot (lseq (words_state a) (lanes a m)) =
  let st_seq_seq = Lib.Sequence.map vec_v st in
  let res = createi #(words_state a) (lanes a m) (fun i -> map (fun x -> x.[i]) st_seq_seq) in
  res

noextract
let ws_spec_v (#a:sha2_alg) (#m:m_spec) (st:ws_spec a m) : GTot (lseq (lseq (word a) 16) (lanes a m)) =
  let st_seq_seq = Lib.Sequence.map vec_v st in
  let res = createi #(lseq (word a) 16) (lanes a m) (fun i -> map (fun x -> x.[i]) st_seq_seq) in
  res

noextract
val shuffle_core_spec: #a: sha2_alg -> #m:m_spec ->
                       k_t: word a ->
                       ws_t: element_t a m ->
                       st: state_spec a m ->
                       state_spec a m
let shuffle_core_spec #a #m k_t ws_t st =
  let a0 = st.[0] in
  let b0 = st.[1] in
  let c0 = st.[2] in
  let d0 = st.[3] in
  let e0 = st.[4] in
  let f0 = st.[5] in
  let g0 = st.[6] in
  let h0 = st.[7] in
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
  create8 a1 b1 c1 d1 e1 f1 g1 h1


inline_for_extraction
let num_rounds16 (a:sha2_alg) : n:size_t{v n > 0 /\ 16 * v n == Spec.size_k_w a} =
  match a with
  | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 5ul

noextract
let multiseq (lanes:lanes_t) (len:size_nat) =
  ntuple (lseq uint8 len) lanes

inline_for_extraction
let tup4 #a (#l:lanes_t{l = 4}) (t:ntuple a l) : a & (a & (a & a)) =
  assert (ntuple a l == ntuple a 4);
  t <: ntuple a 4

inline_for_extraction
let from_tup4 #a (#l:lanes_t{l = 4}) (t:a & (a & (a & a))) : ntuple a l =
  assert (ntuple a l == ntuple a 4);
  t <: ntuple a 4

noextract
let multiblock_spec (a:sha2_alg) (m:m_spec) =
  multiseq (lanes a m) (block_length a)

#push-options "--z3rlimit 100"
noextract
let load_vecij (#a:sha2_alg) (#m:m_spec) (b:multiblock_spec a m) (i:nat{i < 16}) : element_t a m =
  let l = lanes a m in
  let idx_i = i % l in
  let idx_j = i / l in
  vec_from_bytes_be (word_t a) l (sub b.(|idx_i|) (idx_j * l * word_length a) (l * word_length a))
noextract
let load_blocks (#a:sha2_alg) (#m:m_spec) (b:multiblock_spec a m) : ws_spec a m =
  let l = lanes a m in
  createi 16 (load_vecij #a #m b)
#pop-options

noextract
let transpose_ws1 (#a:sha2_alg) (#m:m_spec{lanes a m == 1}) (ws:ws_spec a m) : ws_spec a m = ws

inline_for_extraction
let transpose4x4 #vt
                 (vs : (vec_t vt 4 & vec_t vt 4 & vec_t vt 4 & vec_t vt 4)) :
                       (vec_t vt 4 & vec_t vt 4 & vec_t vt 4 & vec_t vt 4) =
    let (v0,v1,v2,v3) = vs in
    let v0' = vec_interleave_low v0 v1 in
    let v1' = vec_interleave_high v0 v1 in
    let v2' = vec_interleave_low v2 v3 in
    let v3' = vec_interleave_high v2 v3 in
    let v0'' = vec_interleave_low_n 2 v0' v2' in
    let v1'' = vec_interleave_high_n 2 v0' v2' in
    let v2'' = vec_interleave_low_n 2 v1' v3' in
    let v3'' = vec_interleave_high_n 2 v1' v3' in
    (v0'',v1'',v2'',v3'')

noextract
let transpose_ws4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4}) (ws:ws_spec a m) : ws_spec a m =
    let (ws0,ws1,ws2,ws3) = transpose4x4 (ws.[0], ws.[1], ws.[2], ws.[3]) in
    let (ws4,ws5,ws6,ws7) = transpose4x4 (ws.[4], ws.[5], ws.[6], ws.[7]) in
    let (ws8,ws9,ws10,ws11) = transpose4x4 (ws.[8], ws.[9], ws.[10], ws.[11]) in
    let (ws12,ws13,ws14,ws15) = transpose4x4 (ws.[12], ws.[13], ws.[14], ws.[15]) in
    create16 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15
    
noextract
let transpose_ws (#a:sha2_alg) (#m:m_spec) (ws:ws_spec a m) : ws_spec a m =
  match lanes a m with
  | 1 -> transpose_ws1 #a #m ws
  | 4 -> transpose_ws4 #a #m ws
  | _ -> admit()


noextract
let load_ws (#a:sha2_alg) (#m:m_spec) (b:multiblock_spec a m) : ws_spec a m =
  let ws = load_blocks #a #m b in
  transpose_ws #a #m ws

noextract
let ws_next_inner (#a:sha2_alg) (#m:m_spec)
                  (i:size_nat{i < 16})
                  (ws:ws_spec a m) : ws_spec a m =
      let t16 = ws.[i] in
      let t15 = ws.[(i+1) % 16] in
      let t7  = ws.[(i+9) % 16] in
      let t2  = ws.[(i+14) % 16] in
      let s1 = _sigma1 t2 in
      let s0 = _sigma0 t15 in
      ws.[i] <- (s1 +| t7 +| s0 +| t16)
      
noextract
let ws_next (#a:sha2_alg) (#m:m_spec)
            (ws:ws_spec a m) : ws_spec a m =
    repeati 16 (ws_next_inner #a #m) ws

noextract
let shuffle_inner (#a:sha2_alg) (#m:m_spec) (ws:ws_spec a m) (i:size_nat{i < v (num_rounds16 a)}) (j:size_nat{j < 16}) (st:state_spec a m) : state_spec a m =
  let k_t = Seq.index (Spec.k0 a) (16 * i + j) in
  let ws_t = ws.[j] in
  shuffle_core_spec k_t ws_t st
  
noextract
let shuffle_inner_loop (#a:sha2_alg) (#m:m_spec) (i:size_nat{i < v (num_rounds16 a)})
                       (ws_st:ws_spec a m & state_spec a m) : ws_spec a m & state_spec a m =
  let (ws,st) = ws_st in
  let st' = repeati 16 (shuffle_inner ws i) st in
  let ws' = if i < v (num_rounds16 a) - 1 then ws_next ws else ws in
  (ws',st')

noextract
let shuffle (#a:sha2_alg) (#m:m_spec) (ws:ws_spec a m) (st:state_spec a m) : state_spec a m =
  let (ws,st) = repeati (v(num_rounds16 a)) (shuffle_inner_loop #a #m) (ws,st) in
  st

noextract
let init (a:sha2_alg) (m:m_spec) : state_spec a m =
  createi 8 (fun i -> load_element a m (Seq.index (Spec.h0 a) i))

noextract
let update (#a:sha2_alg) (#m:m_spec) (b:multiblock_spec a m) (st:state_spec a m): state_spec a m =
  let st_old = st in
  let ws = load_ws b in
  let st_new = shuffle ws st_old in
  map2 (+|) st_new st_old

noextract
let padded_blocks (a:sha2_alg) (len:size_nat{len < block_length a}) : n:nat{n <= 2} =
  if (len + len_length a + 1 <= block_length a) then 1 else 2
 
noextract
let load_last1 (#a:sha2_alg) (#m:m_spec{lanes a m == 1})
               (totlen_seq:lseq uint8 (len_length a))
               (fin:size_nat{fin == block_length a \/ fin == 2 * block_length a})
               (len:size_nat{len < block_length a}) (b:multiseq 1 len) :
               multiseq 1 (block_length a) & multiseq 1 (block_length a) =
    let last = create (2 * block_length a) (u8 0) in
    let last = update_sub last 0 len b in
    let last = last.[len] <- u8 0x80 in
    let last = update_sub last (fin - len_length a) (len_length a) totlen_seq in
    let b0 = sub last 0 (block_length a) in
    let b1 = sub last (block_length a) (block_length a) in
    (b0, b1)

#push-options "--z3rlimit 200"
noextract
let load_last4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4})
               (totlen_seq:lseq uint8 (len_length a))
               (fin:size_nat{fin == block_length a \/ fin == 2 * block_length a})
               (len:size_nat{len < block_length a}) (b:multiseq (lanes a m) len) :
               multiseq (lanes a m) (block_length a) & multiseq (lanes a m) (block_length a) =
    let last = create (4 * 2 * block_length a) (u8 0) in
    let last0 = sub last 0 (2 * block_length a) in
    let last1 = sub last (2 * block_length a) (2 * block_length a) in
    let last2 = sub last (4 * block_length a) (2 * block_length a) in
    let last3 = sub last (6 * block_length a) (2 * block_length a) in
    let last0 = update_sub last0 0 len b.(|0|) in
    let last1 = update_sub last1 0 len b.(|1|) in
    let last2 = update_sub last2 0 len b.(|2|) in
    let last3 = update_sub last3 0 len b.(|3|) in
    let last0 = last0.[len] <- u8 0x80 in
    let last1 = last1.[len] <- u8 0x80 in
    let last2 = last2.[len] <- u8 0x80 in
    let last3 = last3.[len] <- u8 0x80 in
    let last0 = update_sub last0 (fin - len_length a) (len_length a) totlen_seq in
    let last1 = update_sub last1 (fin - len_length a) (len_length a) totlen_seq in
    let last2 = update_sub last2 (fin - len_length a) (len_length a) totlen_seq in
    let last3 = update_sub last3 (fin - len_length a) (len_length a) totlen_seq in
    let l00 = sub last0 0 (block_length a) in
    let l10 = sub last1 0 (block_length a) in
    let l20 = sub last2 0 (block_length a) in
    let l30 = sub last3 0 (block_length a) in
    let l01 = sub last0 (block_length a) (block_length a) in
    let l11 = sub last1 (block_length a) (block_length a) in
    let l21 = sub last2 (block_length a) (block_length a) in
    let l31 = sub last3 (block_length a) (block_length a) in
    let mb0:multiseq 4 (block_length a) = (l00, (l10, (l20, l30))) in
    let mb1:multiseq 4 (block_length a) = (l01, (l11, (l21, l31))) in
    (from_tup4 mb0, from_tup4 mb1)
#pop-options

noextract
let load_last (#a:sha2_alg) (#m:m_spec) (totlen_seq:lseq uint8 (len_length a))
              (fin:nat{fin == block_length a \/ fin == 2 * block_length a})
              (len:size_nat{len < block_length a}) (b:multiseq (lanes a m) len) :
              multiseq (lanes a m) (block_length a) & multiseq (lanes a m) (block_length a) =
    match lanes a m with
    | 1 -> let (b0,b1) = load_last1 #a #m totlen_seq fin len b in
           (b0,b1)
    | 4 -> let (b0,b1) = load_last4 #a #m totlen_seq fin len b in
           (b0,b1)
    | _ -> admit()
    
noextract
let update_last (#a:sha2_alg) (#m:m_spec) (totlen:len_t a)
                (len:size_nat{len < block_length a})
                (b:multiseq (lanes a m) len) (st:state_spec a m): state_spec a m =
  let blocks = padded_blocks a len in
  let fin : size_nat = blocks * block_length a in
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in 
  let totlen_seq = Lib.ByteSequence.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let (b0,b1) = load_last #a #m totlen_seq fin len b in
  let st = update b0 st in
  if blocks > 1 then
    update b1 st
  else st

noextract
let transpose_hash4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4})
                    (st:state_spec a m) : state_spec a m =
    let st0 = st.[0] in
    let st1 = st.[1] in
    let st2 = st.[2] in
    let st3 = st.[3] in
    let st4 = st.[4] in
    let st5 = st.[5] in
    let st6 = st.[6] in
    let st7 = st.[7] in
    let (st0,st1,st2,st3) = transpose4x4 (st0,st1,st2,st3) in
    let (st4,st5,st6,st7) = transpose4x4 (st4,st5,st6,st7) in
    create8 st0 st1 st2 st3 st4 st5 st6 st7 

noextract
let transpose_hash (#a:sha2_alg) (#m:m_spec) (st:state_spec a m) : state_spec a m =
  match lanes a m with
  | 1 -> st
  | 4 -> transpose_hash4 #a #m st
  | _ -> admit()
  
noextract
let finish1 (#a:sha2_alg) (#m:m_spec{lanes a m == 1})
           (st:state_spec a m) : multiseq (lanes a m) (hash_length a) =
    let h = create (8 * word_length a) (u8 0) in
    let h = repeati 8 (fun i h -> 
                    update_sub h (i * word_length a) (word_length a)
                      (vec_to_bytes_be st.[i])) h in
    let hsub = sub h 0 (hash_length a) in
    hsub <: multiseq 1 (hash_length a)

#push-options "--z3rlimit 100"
noextract
let finish4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4})
           (st:state_spec a m) : multiseq 4 (hash_length a) =
    let st = transpose_hash4 st in
    let h = create (8 * 4 * word_length a) (u8 0) in
    let h = repeati 8 (fun i h -> 
                    update_sub h (i * 4 * word_length a) (4 * word_length a)
                      (vec_to_bytes_be st.[i])) h in
    let h0 = sub h 0 (8 * word_length a) in
    let h1 = sub h (8 * word_length a) (8 * word_length a) in
    let h2 = sub h (16 * word_length a) (8 * word_length a) in
    let h3 = sub h (24 * word_length a) (8 * word_length a) in
    let hsub0 : lseq uint8 (hash_length a) = sub h0 0 (hash_length a) in
    let hsub1 : lseq uint8 (hash_length a) = sub h1 0 (hash_length a) in
    let hsub2 : lseq uint8 (hash_length a) = sub h2 0 (hash_length a) in
    let hsub3 : lseq uint8 (hash_length a) = sub h3 0 (hash_length a) in
    let hsub : multiseq 4 (hash_length a) = (hsub0,(hsub1,(hsub2,hsub3))) in
    hsub <: multiseq 4 (hash_length a)
#pop-options

noextract
let finish (#a:sha2_alg) (#m:m_spec)
           (st:state_spec a m) : multiseq (lanes a m) (hash_length a) =
    match lanes a m with
    | 1 -> finish1 st
    | 4 -> finish4 st
    | _ -> admit()

#push-options "--z3rlimit 200 --max_ifuel 2 --max_fuel 2"
noextract
let get_multiblock_spec (#a:sha2_alg) (#m:m_spec)
                        (len:size_nat) (b:multiseq (lanes a m) len)
                        (i:size_nat{i < len / block_length a})
                        : multiseq (lanes a m) (block_length a) =
    match lanes a m with
    | 1 -> let r = sub #_ #len  (b <: multiseq 1 len) (i * block_length a) (block_length a) in
           r <: multiseq 1 (block_length a)
    | 4 -> let (b0,(b1,(b2,b3))) = tup4 b in
           let bl0 = sub (b0 <: lseq uint8 len) (i * block_length a) (block_length a) in
           let bl1 = sub (b1 <: lseq uint8 len) (i * block_length a) (block_length a) in
           let bl2 = sub (b2 <: lseq uint8 len) (i * block_length a) (block_length a) in
           let bl3 = sub (b3 <: lseq uint8 len) (i * block_length a) (block_length a) in
           let ms: multiseq 4 (block_length a) = (bl0,(bl1,(bl2,bl3))) in
           ms <: multiseq 4 (block_length a)
    | _ -> admit()

noextract
let get_multilast_spec (#a:sha2_alg) (#m:m_spec)
                        (len:size_nat) (b:multiseq (lanes a m) len)
                        : multiseq (lanes a m) (len % block_length a) =
    let rem = len % block_length a in
    match lanes a m with
    | 1 -> let r = sub #_ #len  (b <: multiseq 1 len) (len - rem) (rem) in
           r <: multiseq 1 rem
    | 4 -> let (b0,(b1,(b2,b3))) = tup4 b in
           let bl0 = sub (b0 <: lseq uint8 len) (len - rem) rem in
           let bl1 = sub (b1 <: lseq uint8 len) (len - rem) rem in
           let bl2 = sub (b2 <: lseq uint8 len) (len - rem) rem in
           let bl3 = sub (b3 <: lseq uint8 len) (len - rem) rem in
           let ms: multiseq 4 rem = (bl0,(bl1,(bl2,bl3))) in
           ms <: multiseq 4 rem
    | _ -> admit()
#pop-options                       

noextract
let hash (#a:sha2_alg) (#m:m_spec) (len:len_t a{len_v a len <= max_size_t}) (b:multiseq (lanes a m) (len_v a len)) =
    let ls = len_v a len in
    let st = init a m in
        let blocks = ls / block_length a in
    let rem = ls % block_length a in
    let st = repeati blocks (fun i st ->
      let mb = get_multiblock_spec ls b i in
      update mb st) st in
    let mb = get_multilast_spec #a #m ls b in
    let st = update_last len rem mb st in
    finish st

noextract
let sha256 (len:size_nat) (b:lseq uint8 len) =
  hash #SHA2_256 #M32 (mk_int #U64 #PUB len) b

noextract
let sha256_4 (len:size_nat) (b:multiseq 4 len) =
  hash #SHA2_256 #M128 (mk_int #U64 #PUB len) b

noextract
let sha512 (len:size_nat) (b:lseq uint8 len) =
  hash #SHA2_512 #M32 (mk_int #U128 #PUB len) b

noextract
  let sha512_4 (len:size_nat) (b:multiseq 4 len) =
  hash #SHA2_512 #M256 (mk_int #U128 #PUB len) b

