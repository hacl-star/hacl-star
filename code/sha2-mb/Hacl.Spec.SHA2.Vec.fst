module Hacl.Spec.SHA2.Vec

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.LoopCombinators

open Spec.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Hacl.Spec.SHA2
module LSeq = Lib.Sequence
module VecTranspose = Lib.IntVector.Transpose


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

noextract
type m_spec =
  | M32
  | M128
  | M256

inline_for_extraction
let lanes_t = n:nat{n == 1 \/ n == 2 \/ n == 4 \/ n == 8}

inline_for_extraction
let lanes (a:sha2_alg) (m:m_spec) : lanes_t =
  match a,m with
  | SHA2_224,M128
  | SHA2_256,M128 -> 4
  | SHA2_224,M256
  | SHA2_256,M256 -> 8
  | SHA2_384,M128
  | SHA2_512,M128 -> 2
  | SHA2_384,M256
  | SHA2_512,M256 -> 4
  | _ -> 1

noextract
let is_supported (a:sha2_alg) (m:m_spec) =
  lanes a m = 1 \/ lanes a m = 4 \/ lanes a m = 8

inline_for_extraction
let element_t (a:sha2_alg) (m:m_spec) = vec_t (word_t a) (lanes a m)

inline_for_extraction
val zero_element: a:sha2_alg -> m:m_spec -> element_t a m
let zero_element a m = vec_zero (word_t a) (lanes a m)

//TODO: remove when Spec.Hash.Definitions.word is fixed
inline_for_extraction
let word (a:hash_alg) = uint_t (word_t a) SEC

//TODO: remove when Spec.Hash.Definitions.word is fixed
inline_for_extraction
let words_state' a = m:Seq.seq (word a) {Seq.length m = state_word_length a}

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
let _Ch #a #m x y z = (x &| y) ^| (~| x &| z) //Alternative: Ch(e,f,g)=((f^g)&e)^g  - does not appear to make a perf diff


inline_for_extraction
val _Maj: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m -> element_t a m -> element_t a m
let _Maj #a #m x y z = (x &| y) ^| ((x &| z) ^| (y &| z)) // Alternative: Maj(a,b,c) = Ch(a^b,c,b) - does not appear to make a perf diff

inline_for_extraction
val _Sigma0: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
let _Sigma0 #a #m x = Spec.((x >>>| (op0 a).c0) ^| (x >>>| (op0 a).c1) ^| (x >>>| (op0 a).c2))

inline_for_extraction
val _Sigma1: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
let _Sigma1 #a #m x = Spec.((x >>>| (op0 a).c3) ^| (x >>>| (op0 a).c4) ^| (x >>>| (op0 a).c5))

inline_for_extraction
val _sigma0: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
let _sigma0 #a #m x = Spec.((x >>>| (op0 a).e0) ^| (x >>>| (op0 a).e1) ^| (x >>| (op0 a).e2))

inline_for_extraction
val _sigma1: #a:sha2_alg -> #m:m_spec -> element_t a m -> element_t a m
let _sigma1 #a #m x = Spec.((x >>>| (op0 a).e3) ^| (x >>>| (op0 a).e4) ^| (x >>| (op0 a).e5))

noextract
let state_spec (a:sha2_alg) (m:m_spec) = lseq (element_t a m) 8

noextract
let ws_spec (a:sha2_alg) (m:m_spec) = lseq (element_t a m) 16

noextract
let state_spec_v (#a:sha2_alg) (#m:m_spec) (st:state_spec a m) : lseq (words_state' a) (lanes a m) =
  createi #(words_state' a) (lanes a m) (fun i ->
    create8
      (vec_v st.[0]).[i] (vec_v st.[1]).[i] (vec_v st.[2]).[i] (vec_v st.[3]).[i]
      (vec_v st.[4]).[i] (vec_v st.[5]).[i] (vec_v st.[6]).[i] (vec_v st.[7]).[i])

noextract
let ws_spec_v (#a:sha2_alg) (#m:m_spec) (st:ws_spec a m) : lseq (lseq (word a) 16) (lanes a m) =
  createi #(lseq (word a) 16) (lanes a m) (fun i ->
    create16
      (vec_v st.[0]).[i] (vec_v st.[1]).[i] (vec_v st.[2]).[i] (vec_v st.[3]).[i]
      (vec_v st.[4]).[i] (vec_v st.[5]).[i] (vec_v st.[6]).[i] (vec_v st.[7]).[i]
      (vec_v st.[8]).[i] (vec_v st.[9]).[i] (vec_v st.[10]).[i] (vec_v st.[11]).[i]
      (vec_v st.[12]).[i] (vec_v st.[13]).[i] (vec_v st.[14]).[i] (vec_v st.[15]).[i])


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
let multiseq (lanes:lanes_t) (len:nat) =
  ntuple (Seq.lseq uint8 len) lanes

unfold let multiblock_spec (a:sha2_alg) (m:m_spec) =
  multiseq (lanes a m) (block_length a)

noextract
let load_elementi (#a:sha2_alg) (#m:m_spec) (b:lseq uint8 (block_length a)) (bi:nat{bi < 16 / lanes a m}) : element_t a m =
  let l = lanes a m in
  vec_from_bytes_be (word_t a) l (sub b (bi * l * word_length a) (l * word_length a))

noextract
let get_wsi (#a:sha2_alg) (#m:m_spec) (b:multiblock_spec a m) (i:nat{i < 16}) : element_t a m =
  let l = lanes a m in
  let idx_i = i % l in
  let idx_j = i / l in
  load_elementi #a #m b.(|idx_i|) idx_j

noextract
let load_blocks (#a:sha2_alg) (#m:m_spec) (b:multiblock_spec a m) : ws_spec a m =
  createi 16 (get_wsi #a #m b)

noextract
let transpose_ws1 (#a:sha2_alg) (#m:m_spec{lanes a m == 1}) (ws:ws_spec a m) : ws_spec a m = ws

noextract
let transpose_ws4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4}) (ws:ws_spec a m) : ws_spec a m =
    let (ws0,ws1,ws2,ws3) = VecTranspose.transpose4x4 (ws.[0], ws.[1], ws.[2], ws.[3]) in
    let (ws4,ws5,ws6,ws7) = VecTranspose.transpose4x4 (ws.[4], ws.[5], ws.[6], ws.[7]) in
    let (ws8,ws9,ws10,ws11) = VecTranspose.transpose4x4 (ws.[8], ws.[9], ws.[10], ws.[11]) in
    let (ws12,ws13,ws14,ws15) = VecTranspose.transpose4x4 (ws.[12], ws.[13], ws.[14], ws.[15]) in
    create16 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15

noextract
let transpose_ws8 (#a:sha2_alg) (#m:m_spec{lanes a m == 8}) (ws:ws_spec a m) : ws_spec a m =
    let (ws0,ws1,ws2,ws3,ws4,ws5,ws6,ws7) = VecTranspose.transpose8x8 (ws.[0], ws.[1], ws.[2], ws.[3], ws.[4], ws.[5], ws.[6], ws.[7]) in
    let (ws8,ws9,ws10,ws11,ws12,ws13,ws14,ws15) = VecTranspose.transpose8x8 (ws.[8], ws.[9], ws.[10], ws.[11], ws.[12], ws.[13], ws.[14], ws.[15]) in
    create16 ws0 ws1 ws2 ws3 ws4 ws5 ws6 ws7 ws8 ws9 ws10 ws11 ws12 ws13 ws14 ws15

noextract
let transpose_ws (#a:sha2_alg) (#m:m_spec{is_supported a m}) (ws:ws_spec a m) : ws_spec a m =
  match lanes a m with
  | 1 -> transpose_ws1 #a #m ws
  | 4 -> transpose_ws4 #a #m ws
  | 8 -> transpose_ws8 #a #m ws


noextract
let load_ws (#a:sha2_alg) (#m:m_spec{is_supported a m}) (b:multiblock_spec a m) : ws_spec a m =
  let ws = load_blocks #a #m b in
  transpose_ws #a #m ws

noextract
let ws_next_inner (#a:sha2_alg) (#m:m_spec)
                  (i:nat{i < 16})
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
let shuffle_inner (#a:sha2_alg) (#m:m_spec) (ws:ws_spec a m) (i:nat{i < v (num_rounds16 a)}) (j:nat{j < 16}) (st:state_spec a m) : state_spec a m =
  let k_t = Seq.index (Spec.k0 a) (16 * i + j) in
  let ws_t = ws.[j] in
  shuffle_core_spec k_t ws_t st

noextract
let shuffle_inner_loop (#a:sha2_alg) (#m:m_spec) (i:nat{i < v (num_rounds16 a)})
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

[@"opaque_to_smt"]
noextract
let update (#a:sha2_alg) (#m:m_spec{is_supported a m}) (b:multiblock_spec a m) (st:state_spec a m): state_spec a m =
  let st_old = st in
  let ws = load_ws b in
  let st_new = shuffle ws st_old in
  map2 (+|) st_new st_old

noextract
let padded_blocks (a:sha2_alg) (len:nat{len <= block_length a}) : n:nat{n <= 2} =
  if (len + len_length a + 1 <= block_length a) then 1 else 2

noextract
let load_last_blocks (#a:sha2_alg)
                     (totlen_seq:lseq uint8 (len_length a))
                     (fin:nat{fin == block_length a \/ fin == 2 * block_length a})
                     (len:nat{len <= block_length a})
                     (b:lseq uint8 len) :
                     lseq uint8 (block_length a) & lseq uint8 (block_length a) =
    let last = create (2 * block_length a) (u8 0) in
    let last = update_sub last 0 len b in
    let last = last.[len] <- u8 0x80 in
    let last = update_sub last (fin - len_length a) (len_length a) totlen_seq in
    let l0 : lseq uint8 (block_length a) = sub last 0 (block_length a) in
    let l1 : lseq uint8 (block_length a) = sub last (block_length a) (block_length a) in
    (l0, l1)

noextract
let load_last1 (#a:sha2_alg) (#m:m_spec{lanes a m == 1})
               (totlen_seq:lseq uint8 (len_length a))
               (fin:nat{fin == block_length a \/ fin == 2 * block_length a})
               (len:nat{len <= block_length a}) (b:multiseq (lanes a m) len) :
               multiseq (lanes a m) (block_length a) & multiseq (lanes a m) (block_length a) =
    let b = b.(|0|) in
    let (l0,l1) = load_last_blocks #a totlen_seq fin len b in
    let lb0 : multiseq (lanes a m) (block_length a) = ntup1 l0 in
    let lb1 : multiseq (lanes a m) (block_length a) = ntup1 l1 in
    (lb0, lb1)

#push-options "--z3rlimit 100"
noextract
let load_last4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4})
               (totlen_seq:lseq uint8 (len_length a))
               (fin:nat{fin == block_length a \/ fin == 2 * block_length a})
               (len:nat{len <= block_length a}) (b:multiseq (lanes a m) len) :
               multiseq (lanes a m) (block_length a) & multiseq (lanes a m) (block_length a) =
    let b0 = b.(|0|) in
    let b1 = b.(|1|) in
    let b2 = b.(|2|) in
    let b3 = b.(|3|) in
    let (l00,l01) = load_last_blocks #a totlen_seq fin len b0 in
    let (l10,l11) = load_last_blocks #a totlen_seq fin len b1 in
    let (l20,l21) = load_last_blocks #a totlen_seq fin len b2 in
    let (l30,l31) = load_last_blocks #a totlen_seq fin len b3 in
    let mb0 = ntup4 (l00, (l10, (l20, l30))) in
    let mb1 = ntup4 (l01, (l11, (l21, l31))) in
    (mb0, mb1)

noextract
let load_last8 (#a:sha2_alg) (#m:m_spec{lanes a m == 8})
               (totlen_seq:lseq uint8 (len_length a))
               (fin:nat{fin == block_length a \/ fin == 2 * block_length a})
               (len:nat{len <= block_length a}) (b:multiseq (lanes a m) len) :
               multiseq (lanes a m) (block_length a) & multiseq (lanes a m) (block_length a) =
    let b0 = b.(|0|) in
    let b1 = b.(|1|) in
    let b2 = b.(|2|) in
    let b3 = b.(|3|) in
    let b4 = b.(|4|) in
    let b5 = b.(|5|) in
    let b6 = b.(|6|) in
    let b7 = b.(|7|) in
    let (l00,l01) = load_last_blocks #a totlen_seq fin len b0 in
    let (l10,l11) = load_last_blocks #a totlen_seq fin len b1 in
    let (l20,l21) = load_last_blocks #a totlen_seq fin len b2 in
    let (l30,l31) = load_last_blocks #a totlen_seq fin len b3 in
    let (l40,l41) = load_last_blocks #a totlen_seq fin len b4 in
    let (l50,l51) = load_last_blocks #a totlen_seq fin len b5 in
    let (l60,l61) = load_last_blocks #a totlen_seq fin len b6 in
    let (l70,l71) = load_last_blocks #a totlen_seq fin len b7 in
    let mb0 = ntup8 (l00, (l10, (l20, (l30, (l40, (l50, (l60, l70))))))) in
    let mb1 = ntup8 (l01, (l11, (l21, (l31, (l41, (l51, (l61, l71))))))) in
    (mb0, mb1)
#pop-options

[@"opaque_to_smt"]
noextract
let load_last (#a:sha2_alg) (#m:m_spec{is_supported a m}) (totlen_seq:lseq uint8 (len_length a))
              (fin:nat{fin == block_length a \/ fin == 2 * block_length a})
              (len:nat{len <= block_length a}) (b:multiseq (lanes a m) len) :
              multiseq (lanes a m) (block_length a) & multiseq (lanes a m) (block_length a) =
    match lanes a m with
    | 1 -> load_last1 #a #m totlen_seq fin len b
    | 4 -> load_last4 #a #m totlen_seq fin len b
    | 8 -> load_last8 #a #m totlen_seq fin len b

noextract
let update_last (#a:sha2_alg) (#m:m_spec{is_supported a m}) (totlen:len_t a)
                (len:nat{len <= block_length a})
                (b:multiseq (lanes a m) len) (st:state_spec a m): state_spec a m =
  let blocks = padded_blocks a len in
  let fin : nat = blocks * block_length a in
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in
  let totlen_seq = Lib.ByteSequence.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let (b0,b1) = load_last #a #m totlen_seq fin len b in
  let st = update b0 st in
  if blocks > 1 then
    update b1 st
  else st

noextract
let transpose_state4 (#a:sha2_alg) (#m:m_spec{lanes a m == 4})
                    (st:state_spec a m) : state_spec a m =
    let st0 = st.[0] in
    let st1 = st.[1] in
    let st2 = st.[2] in
    let st3 = st.[3] in
    let st4 = st.[4] in
    let st5 = st.[5] in
    let st6 = st.[6] in
    let st7 = st.[7] in
    let (st0,st1,st2,st3) = VecTranspose.transpose4x4 (st0,st1,st2,st3) in
    let (st4,st5,st6,st7) = VecTranspose.transpose4x4 (st4,st5,st6,st7) in
    create8 st0 st4 st1 st5 st2 st6 st3 st7

noextract
let transpose_state8 (#a:sha2_alg) (#m:m_spec{lanes a m == 8})
                    (st:state_spec a m) : state_spec a m =
    let st0 = st.[0] in
    let st1 = st.[1] in
    let st2 = st.[2] in
    let st3 = st.[3] in
    let st4 = st.[4] in
    let st5 = st.[5] in
    let st6 = st.[6] in
    let st7 = st.[7] in
    let (st0,st1,st2,st3,st4,st5,st6,st7) = VecTranspose.transpose8x8 (st0,st1,st2,st3,st4,st5,st6,st7) in
    create8 st0 st1 st2 st3 st4 st5 st6 st7

noextract
let transpose_state (#a:sha2_alg) (#m:m_spec{is_supported a m}) (st:state_spec a m) : state_spec a m =
  match lanes a m with
  | 1 -> st
  | 4 -> transpose_state4 #a #m st
  | 8 -> transpose_state8 #a #m st

noextract
let store_state (#a:sha2_alg) (#m:m_spec{is_supported a m}) (st:state_spec a m) :
                lseq uint8 (lanes a m * 8 * word_length a) =
    let st = transpose_state st in
    Lib.IntVector.Serialize.vecs_to_bytes_be st

noextract
let emit (#a:sha2_alg) (#m:m_spec)
         (hseq:lseq uint8 (lanes a m * 8 * word_length a)):
         multiseq (lanes a m) (hash_length a) =
    Lib.NTuple.createi #(Seq.lseq uint8 (hash_length a)) (lanes a m)
      (fun i -> sub hseq (i * 8 * word_length a) (hash_length a))

noextract
let get_multiblock_spec (#a:sha2_alg) (#m:m_spec)
                        (len:Spec.len_lt_max_a_t a) (b:multiseq (lanes a m) len)
                        (i:nat{i < len / block_length a})
                        : multiseq (lanes a m) (block_length a) =

    Lib.NTuple.createi #(Seq.lseq uint8 (block_length a)) (lanes a m)
      (fun j -> Seq.slice b.(|j|) (i * block_length a) (i * block_length a + block_length a))

noextract
let get_multilast_spec (#a:sha2_alg) (#m:m_spec)
                        (len:Spec.len_lt_max_a_t a) (b:multiseq (lanes a m) len)
                        : multiseq (lanes a m) (len % block_length a) =
    let rem = len % block_length a in
    Lib.NTuple.createi #(Seq.lseq uint8 rem) (lanes a m)
      (fun j -> Seq.slice b.(|j|) (len - rem) len)

noextract
let update_block (#a:sha2_alg) (#m:m_spec{is_supported a m}) (len:Spec.len_lt_max_a_t a) (b:multiseq (lanes a m) len)
                 (i:nat{i < len / block_length a}) (st:state_spec a m) : state_spec a m =
  let mb = get_multiblock_spec len b i in
  update mb st

noextract
let update_nblocks (#a:sha2_alg) (#m:m_spec{is_supported a m}) (len:Spec.len_lt_max_a_t a) (b:multiseq (lanes a m) len) (st:state_spec a m) : state_spec a m =
    let blocks = len / block_length a in
    let st = repeati blocks (update_block #a #m len b) st in
    st

noextract
let finish (#a:sha2_alg) (#m:m_spec{is_supported a m}) (st:state_spec a m) :
         multiseq (lanes a m) (hash_length a) =
    let hseq = store_state st in
    emit hseq

noextract
let hash (#a:sha2_alg) (#m:m_spec{is_supported a m}) (len:Spec.len_lt_max_a_t a) (b:multiseq (lanes a m) len) =
    let len' : len_t a = Spec.mk_len_t a len in
    let st = init a m in
    let st = update_nblocks #a #m len b st in
    let rem = len % block_length a in
    let mb = get_multilast_spec #a #m len b in
    let st = update_last len' rem mb st in
    finish st

noextract
let sha256 (len:Spec.len_lt_max_a_t SHA2_256) (b:seq uint8{length b = len}) =
  hash #SHA2_256 #M32 len b

noextract
let sha256_4 (len:Spec.len_lt_max_a_t SHA2_256) (b:multiseq 4 len) =
  hash #SHA2_256 #M128 len b

noextract
let sha512 (len:Spec.len_lt_max_a_t SHA2_512) (b:seq uint8{length b = len}) =
  hash #SHA2_512 #M32 len b

noextract
let sha512_4 (len:Spec.len_lt_max_a_t SHA2_512) (b:multiseq 4 len) =
  hash #SHA2_512 #M256 len b
