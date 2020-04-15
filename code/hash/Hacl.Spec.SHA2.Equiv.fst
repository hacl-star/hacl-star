module Hacl.Spec.SHA2.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.IntVector.Serialize
open Lib.LoopCombinators

open Hacl.Spec.SHA2.Vec
open Spec.Hash.Definitions
module Spec = Hacl.Spec.SHA2
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence
module VecTranspose = Lib.IntVector.Transpose


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let _Ch_lemma #a #m x y z :
  Lemma (vec_v (_Ch #a #m x y z) ==
    LSeq.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))
  [SMTPat (_Ch x y z)]
 =
  LSeq.eq_intro (vec_v (_Ch #a #m x y z))
    (LSeq.createi (lanes a m) (fun i -> Spec._Ch a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))


let _Maj_lemma #a #m x y z :
  Lemma (vec_v (_Maj #a #m x y z) ==
    LSeq.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))
  [SMTPat (_Maj x y z)]
 =
  LSeq.eq_intro (vec_v (_Maj #a #m x y z))
    (LSeq.createi (lanes a m) (fun i -> Spec._Maj a (vec_v x).[i] (vec_v y).[i] (vec_v z).[i]))


let _Sigma0_lemma #a #m x :
  Lemma (vec_v (_Sigma0 #a #m x) == LSeq.map (Spec._Sigma0 a) (vec_v x))
  [SMTPat (_Sigma0 x)]
 =
  LSeq.eq_intro (vec_v (_Sigma0 #a #m x)) (LSeq.map (Spec._Sigma0 a) (vec_v x))

let _Sigma1_lemma #a #m x :
  Lemma (vec_v (_Sigma1 #a #m x) == LSeq.map (Spec._Sigma1 a) (vec_v x))
  [SMTPat (_Sigma1 x)]
 =
  LSeq.eq_intro (vec_v (_Sigma1 #a #m x)) (LSeq.map (Spec._Sigma1 a) (vec_v x))

let _sigma0_lemma #a #m x :
  Lemma (vec_v (_sigma0 #a #m x) == LSeq.map (Spec._sigma0 a) (vec_v x))
  [SMTPat (_sigma0 x)]
 =
  LSeq.eq_intro (vec_v (_sigma0 #a #m x)) (LSeq.map (Spec._sigma0 a) (vec_v x))

let _sigma1_lemma #a #m x :
  Lemma (vec_v (_sigma1 #a #m x) == LSeq.map (Spec._sigma1 a) (vec_v x))
  [SMTPat (_sigma1 x)]
 =
  LSeq.eq_intro (vec_v (_sigma1 #a #m x)) (LSeq.map (Spec._sigma1 a) (vec_v x))


val seq_of_list_is_create8: #a:Type -> x0:a -> x1:a -> x2:a -> x3:a -> x4:a -> x5:a -> x6:a -> x7:a ->
  Lemma (create8 x0 x1 x2 x3 x4 x5 x6 x7 == Seq.seq_of_list [x0; x1; x2; x3; x4; x5; x6; x7])

let seq_of_list_is_create8 #a x0 x1 x2 x3 x4 x5 x6 x7 =
  let rp = Seq.seq_of_list [x0; x1; x2; x3; x4; x5; x6; x7] in
  assert_norm (length rp == 8);
  let lp = create8 x0 x1 x2 x3 x4 x5 x6 x7 in

  let aux (i:nat{i < 8}) : Lemma (Seq.index lp i == Seq.index rp i) =
    assert_norm (Seq.index lp i == Seq.index rp i) in

  Classical.forall_intro aux;
  eq_intro rp lp


val shuffle_core_pre_create8: a:sha2_alg -> k_t:word a -> ws_t:word a -> hash:words_state a -> words_state a
let shuffle_core_pre_create8 a k_t ws_t hash =
  let a0 = Seq.index hash 0 in
  let b0 = Seq.index hash 1 in
  let c0 = Seq.index hash 2 in
  let d0 = Seq.index hash 3 in
  let e0 = Seq.index hash 4 in
  let f0 = Seq.index hash 5 in
  let g0 = Seq.index hash 6 in
  let h0 = Seq.index hash 7 in

  let t1 = h0 +. (Spec._Sigma1 a e0) +. (Spec._Ch a e0 f0 g0) +. k_t +. ws_t in
  let t2 = (Spec._Sigma0 a a0) +. (Spec._Maj a a0 b0 c0) in
  create8 (t1 +. t2) a0 b0 c0 (d0 +. t1) e0 f0 g0


val shuffle_core_pre_create8_lemma: a:sha2_alg -> k_t:word a -> ws_t:word a -> hash:words_state a ->
  Lemma (Spec.shuffle_core_pre a k_t ws_t hash == shuffle_core_pre_create8 a k_t ws_t hash)
let shuffle_core_pre_create8_lemma a k_t ws_t hash =
  let a0 = Seq.index hash 0 in
  let b0 = Seq.index hash 1 in
  let c0 = Seq.index hash 2 in
  let d0 = Seq.index hash 3 in
  let e0 = Seq.index hash 4 in
  let f0 = Seq.index hash 5 in
  let g0 = Seq.index hash 6 in
  let h0 = Seq.index hash 7 in

  let t1 = h0 +. (Spec._Sigma1 a e0) +. (Spec._Ch a e0 f0 g0) +. k_t +. ws_t in
  let t2 = (Spec._Sigma0 a a0) +. (Spec._Maj a a0 b0 c0) in
  seq_of_list_is_create8 (t1 +. t2) a0 b0 c0 (d0 +. t1) e0 f0 g0


val shuffle_core_spec_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> k_t:word a
  -> ws_t:element_t a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
   ((state_spec_v (shuffle_core_spec k_t ws_t st)).[l] ==
    Spec.shuffle_core_pre a k_t (vec_v ws_t).[l] (state_spec_v st).[l])

let shuffle_core_spec_lemma_l #a #m k_t ws_t st l =
  eq_intro #(word a) #(state_word_length a)
    (state_spec_v (shuffle_core_spec k_t ws_t st)).[l]
    (shuffle_core_pre_create8 a k_t (vec_v ws_t).[l] (state_spec_v st).[l]);
  shuffle_core_pre_create8_lemma a k_t (vec_v ws_t).[l] (state_spec_v st).[l]


#push-options "--z3rlimit 100"
val ws_next_inner_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> i:size_nat{i < 16}
  -> ws:ws_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((ws_spec_v (ws_next_inner i ws)).[l] == Spec.ws_next_inner a i (ws_spec_v ws).[l])

let ws_next_inner_lemma_l #a #m i ws l =
  eq_intro #(word a) #16
    (ws_spec_v (ws_next_inner i ws)).[l]
    (Spec.ws_next_inner a i (ws_spec_v ws).[l])
#pop-options

val ws_next_lemma_loop:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> l:nat{l < lanes a m}
  -> n:nat{n <= 16} ->
  Lemma
   ((ws_spec_v (repeati n (ws_next_inner #a #m) ws)).[l] ==
    repeati n (Spec.ws_next_inner a) (ws_spec_v ws).[l])

let rec ws_next_lemma_loop #a #m ws l n =
  let lp = repeati n (ws_next_inner #a #m) ws in
  let rp = repeati n (Spec.ws_next_inner a) (ws_spec_v ws).[l] in

  if n = 0 then begin
    eq_repeati0 n (ws_next_inner #a #m) ws;
    eq_repeati0 n (Spec.ws_next_inner a) (ws_spec_v ws).[l];
    ws_next_inner_lemma_l 0 ws l end
  else begin
    let lp0 = repeati (n - 1) (ws_next_inner #a #m) ws in
    let rp0 = repeati (n - 1) (Spec.ws_next_inner a) (ws_spec_v ws).[l] in
    ws_next_lemma_loop #a #m ws l (n - 1);
    //assert ((ws_spec_v lp0).[l] == rp0);
    unfold_repeati n (ws_next_inner #a #m) ws (n - 1);
    unfold_repeati n (Spec.ws_next_inner a) (ws_spec_v ws).[l] (n - 1);
    //assert (lp == ws_next_inner #a #m (n - 1) lp0);
    //assert (rp == Spec.ws_next_inner a (n - 1) rp0);
    ws_next_inner_lemma_l (n - 1) lp0 l;
    () end


val ws_next_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((ws_spec_v (ws_next #a #m ws)).[l] == Spec.ws_next a (ws_spec_v ws).[l])

let ws_next_lemma_l #a #m ws l = ws_next_lemma_loop #a #m ws l 16


val shuffle_inner_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> i:size_nat{i < Spec.num_rounds16 a}
  -> j:size_nat{j < 16}
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
    ((state_spec_v (shuffle_inner ws i j st)).[l] ==
     Spec.shuffle_inner a (ws_spec_v ws).[l] i j (state_spec_v st).[l])

let shuffle_inner_lemma_l #a #m ws i j st l =
  let k_t = Seq.index (Spec.k0 a) (16 * i + j) in
  let ws_t = ws.[j] in
  shuffle_core_spec_lemma_l k_t ws_t st l


val shuffle_inner_loop_lemma:
    #a:sha2_alg
  -> #m:m_spec
  -> i:size_nat{i < Spec.num_rounds16 a}
  -> ws0:ws_spec a m
  -> st0:state_spec a m
  -> l:nat{l < lanes a m}
  -> n:nat{n <= 16} ->
  Lemma
    ((state_spec_v (repeati n (shuffle_inner ws0 i) st0)).[l] ==
     repeati n (Spec.shuffle_inner a (ws_spec_v ws0).[l] i) (state_spec_v st0).[l])

let rec shuffle_inner_loop_lemma #a #m i ws0 st0 l n =
  let f_sc = Spec.shuffle_inner a (ws_spec_v ws0).[l] i in
  let lp = repeati n (shuffle_inner ws0 i) st0 in
  let rp = repeati n f_sc (state_spec_v st0).[l] in

  if n = 0 then begin
    eq_repeati0 n (shuffle_inner ws0 i) st0;
    eq_repeati0 n f_sc (state_spec_v st0).[l];
    shuffle_inner_lemma_l #a #m ws0 i n st0 l end
  else begin
    let lp0 = repeati (n - 1) (shuffle_inner ws0 i) st0 in
    let rp0 = repeati (n - 1) f_sc (state_spec_v st0).[l] in
    shuffle_inner_loop_lemma #a #m i ws0 st0 l (n - 1);
    assert ((state_spec_v lp0).[l] == rp0);
    unfold_repeati n (shuffle_inner ws0 i) st0 (n - 1);
    unfold_repeati n f_sc (state_spec_v st0).[l] (n - 1);
    shuffle_inner_lemma_l #a #m ws0 i (n - 1) lp0 l end


val shuffle_inner_loop_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> i:size_nat{i < Spec.num_rounds16 a}
  -> ws_st:tuple2 (ws_spec a m) (state_spec a m)
  -> l:nat{l < lanes a m} ->
  Lemma
  (let (ws1, st1) = shuffle_inner_loop i ws_st in
   let (ws0, st0) = ws_st in
   let (ws, st) = Spec.shuffle_inner_loop a i ((ws_spec_v ws0).[l], (state_spec_v st0).[l]) in
   (ws_spec_v ws1).[l] == ws /\ (state_spec_v st1).[l] == st)

let shuffle_inner_loop_lemma_l #a #m i (ws0, st0) l =
  shuffle_inner_loop_lemma #a #m i ws0 st0 l 16;
  ws_next_lemma_l ws0 l


val shuffle_loop_lemma:
    #a:sha2_alg
  -> #m:m_spec
  -> ws0:ws_spec a m
  -> st0:state_spec a m
  -> l:nat{l < lanes a m}
  -> n:nat{n <= Spec.num_rounds16 a} ->
  Lemma
   (let (ws_v, st_v) = repeati n (shuffle_inner_loop #a #m) (ws0, st0) in
    let (ws, st) = repeati n (Spec.shuffle_inner_loop a) ((ws_spec_v ws0).[l], (state_spec_v st0).[l]) in
    (ws_spec_v ws_v).[l] == ws /\ (state_spec_v st_v).[l] == st)

let rec shuffle_loop_lemma #a #m ws0 st0 l n =
  let (ws_v, st_v) = repeati n (shuffle_inner_loop #a #m) (ws0, st0) in
  let acc0 = ((ws_spec_v ws0).[l], (state_spec_v st0).[l]) in
  let (ws, st) = repeati n (Spec.shuffle_inner_loop a) acc0 in

  if n = 0 then begin
    eq_repeati0 n (shuffle_inner_loop #a #m) (ws0, st0);
    eq_repeati0 n (Spec.shuffle_inner_loop a) acc0;
    shuffle_inner_loop_lemma_l #a #m n (ws0, st0) l end
  else begin
    let (ws_v1, st_v1) = repeati (n - 1) (shuffle_inner_loop #a #m) (ws0, st0) in
    let (ws1, st1) = repeati (n - 1) (Spec.shuffle_inner_loop a) acc0 in
    shuffle_loop_lemma #a #m ws0 st0 l (n - 1);
    //assert ((ws_spec_v ws_v1).[l] == ws1 /\ (state_spec_v st_v1).[l] == st1);
    unfold_repeati n (shuffle_inner_loop #a #m) (ws0, st0) (n - 1);
    unfold_repeati n (Spec.shuffle_inner_loop a) acc0 (n - 1);
    shuffle_inner_loop_lemma_l #a #m (n - 1) (ws_v1, st_v1) l end


val shuffle_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (shuffle ws st)).[l] ==
    Spec.shuffle a (ws_spec_v ws).[l] (state_spec_v st).[l])

let shuffle_lemma_l #a #m ws st l =
  shuffle_loop_lemma #a #m ws st l (Spec.num_rounds16 a)


val init_lemma_l: a:sha2_alg -> m:m_spec -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (init a m)).[l] == Spec.init a)

let init_lemma_l a m l =
  eq_intro #(word a) #(state_word_length a)
    (state_spec_v (init a m)).[l] (Spec.init a)


val load_blocks_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma (let l = lanes a m in
    (vec_v (load_blocks b).[i]).[j] ==
    BSeq.uint_from_bytes_be (sub b.(|i % l|) ((i / l * l + j) * word_length a) (word_length a)))

let load_blocks_lemma_ij #a #m b j i =
  let l = lanes a m in
  let idx_i = i % l in
  let idx_j = i / l in

  let blocksize = word_length a in
  let blocksize_l = l * blocksize in
  let b_j = sub b.(|idx_i|) (idx_j * blocksize_l) blocksize_l in

  //assert ((load_blocks b).[i] == vec_from_bytes_be (word_t a) l b_j);
  assert (vec_v ((load_blocks b).[i]) == BSeq.uints_from_bytes_be b_j);
  BSeq.index_uints_from_bytes_be #(word_t a) #SEC #(lanes a m) b_j j;
  assert ((vec_v ((load_blocks b).[i])).[j] ==
    BSeq.uint_from_bytes_be (sub b_j (j * blocksize) blocksize));

  calc (==) {
    idx_j * blocksize_l + j * blocksize;
    (==) { Math.Lemmas.paren_mul_right idx_j l blocksize;
      Math.Lemmas.distributivity_add_left (idx_j * l) j blocksize }
    (idx_j * l + j) * blocksize;
  };

  Seq.Properties.slice_slice b.(|idx_i|)
    (idx_j * blocksize_l) (idx_j * blocksize_l + blocksize_l)
    (j * blocksize) (j * blocksize + blocksize);

  assert ((vec_v ((load_blocks b).[i])).[j] ==
    BSeq.uint_from_bytes_be (sub b.(|idx_i|) ((idx_j * l + j) * blocksize) blocksize))


#push-options "--max_ifuel 1"
val transpose_ws4_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 4}
  -> ws:ws_spec a m
  -> i:nat{i < 4} ->
  Lemma
   (sub (transpose_ws4 ws) (i * lanes a m) (lanes a m) ==
    VecTranspose.transpose4x4_lseq (sub ws (i * lanes a m) (lanes a m)))

let transpose_ws4_lemma #a #m ws i =
  eq_intro
    (sub (transpose_ws4 ws) (i * lanes a m) (lanes a m))
     (VecTranspose.transpose4x4_lseq (sub ws (i * lanes a m) (lanes a m)))
#pop-options


val transpose_ws4_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 4} // lanes a m * lanes a m = 16
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    (vec_v (transpose_ws4 ws).[i]).[j] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws4_lemma_ij #a #m ws j i =
  let l = lanes a m in
  let i_sub = i / l in
  let j_sub = i % l in
  assert (i_sub * l + j_sub == i);

  let vs = sub ws (i_sub * lanes a m) (lanes a m) in
  transpose_ws4_lemma #a #m ws i_sub;
  //assert ((transpose_ws4 ws).[i] == (sub (transpose_ws4 ws) (i_sub * l) l).[j_sub]);
  //assert ((transpose_ws4 ws).[i] == (transpose4x4_lseq vs).[j_sub]);
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v (VecTranspose.transpose4x4_lseq vs).[j_sub]).[j]);
  VecTranspose.transpose4x4_lemma vs;
  //assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v vs.[j]).[j_sub]);
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v ws.[i_sub * lanes a m + j]).[j_sub])


val transpose_ws_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec
  -> ws:ws_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma
   (let l = lanes a m in
    ((ws_spec_v (transpose_ws ws)).[j]).[i] == (vec_v ws.[i / l * l + j]).[i % l])

let transpose_ws_lemma_ij #a #m ws j i =
  assert (((ws_spec_v (transpose_ws ws)).[j]).[i] == (vec_v (transpose_ws ws).[i]).[j]);
  match lanes a m with
  | 1 -> ()
  | 4 -> transpose_ws4_lemma_ij #a #m ws j i
  | _ -> admit()


val load_blocks_lemma_ij_subst:
    #a:sha2_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 16} ->
  Lemma (let l = lanes a m in
    (vec_v (load_blocks b).[i / l * l + j]).[i % l] ==
    BSeq.uint_from_bytes_be (sub b.(|j|) (i * word_length a) (word_length a)))

let load_blocks_lemma_ij_subst #a #m b j i =
  let l = lanes a m in
  let i_new = i / l * l + j in
  let j_new = i % l in
  load_blocks_lemma_ij #a #m b j_new i_new;
  //assert (
    //(vec_v (load_blocks b).[i_new]).[j_new] ==
    //BSeq.uint_from_bytes_be (sub b.(|i_new % l|) ((i_new / l * l + j_new) * word_length a) (word_length a)));

  calc (==) {
    i_new % l;
    (==) { }
    (i / l * l + j) % l;
    (==) { Math.Lemmas.modulo_addition_lemma j l (i / l) }
    j % l;
    (==) { Math.Lemmas.small_mod j l }
    j;
    };

  calc (==) {
    i_new / l * l + j_new;
    (==) { }
    (i / l * l + j) / l * l + i % l;
    (==) { Math.Lemmas.division_addition_lemma j l (i / l) }
    (i / l + j / l) * l + i % l;
    (==) { Math.Lemmas.distributivity_add_left (i / l) (j / l) l }
    i / l * l + j / l * l + i % l;
    (==) { Math.Lemmas.euclidean_division_definition i l }
    i + j / l * l;
    (==) { Math.Lemmas.small_div j l }
    i;
    }


val load_ws_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> j:nat{j < lanes a m} ->
  Lemma
    ((ws_spec_v (load_ws b)).[j] ==
      BSeq.uints_from_bytes_be #(word_t a) #SEC b.(|j|))

let load_ws_lemma_l #a #m b j =
  let lp = (ws_spec_v (load_ws b)).[j] in
  let rp = BSeq.uints_from_bytes_be #(word_t a) #SEC #16 b.(|j|) in

  let aux (i:nat{i < 16}) : Lemma (lp.[i] == rp.[i]) =
    let l = lanes a m in
    BSeq.index_uints_from_bytes_be #(word_t a) #SEC #16 b.(|j|) i;
    assert (rp.[i] == BSeq.uint_from_bytes_be (sub b.(|j|) (i * word_length a) (word_length a)));

    assert (lp.[i] == ((ws_spec_v (transpose_ws (load_blocks b))).[j]).[i]);
    transpose_ws_lemma_ij (load_blocks b) j i;
    load_blocks_lemma_ij_subst #a #m b j i in

  Classical.forall_intro aux;
  eq_intro lp rp


val state_spec_v_map2_add:
    #a:sha2_alg
  -> #m:m_spec
  -> st1:state_spec a m
  -> st2:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (map2 (+|) st1 st2)).[l] ==
    map2 #_ #_ #_ #8 (+.) (state_spec_v st1).[l] (state_spec_v st2).[l])

let state_spec_v_map2_add #a #m st1 st2 l =
  eq_intro
    (state_spec_v (map2 (+|) st1 st2)).[l]
    (map2 #_ #_ #_ #8 (+.) (state_spec_v st1).[l] (state_spec_v st2).[l])


val update_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> b:multiblock_spec a m
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (update b st)).[l] ==
    Spec.update a b.(|l|) (state_spec_v st).[l])

let update_lemma_l #a #m b st l =
  reveal_opaque (`%update) (update #a #m);
  let ws = load_ws b in
  load_ws_lemma_l b l;

  let st1 = shuffle ws st in
  shuffle_lemma_l ws st l;

  let res = map2 (+|) st1 st in
  state_spec_v_map2_add #a #m st1 st l


val load_last_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> totlen_seq:lseq uint8 (len_length a)
  -> fin:nat{fin == block_length a \/ fin == 2 * block_length a}
  -> len:size_nat{len < block_length a}
  -> b:multiseq (lanes a m) len
  -> l:nat{l < lanes a m} ->
  Lemma
   (let (b0_v, b1_v) = load_last totlen_seq fin len b in
    let (b0, b1) = Spec.load_last a totlen_seq fin len b.(|l|) in
    b0_v.(|l|) == b0 /\ b1_v.(|l|) == b1)

let load_last_lemma_l #a #m totlen_seq fin len b l =
  reveal_opaque (`%load_last) (load_last #a #m);
  match lanes a m with
  | 1 -> ()
  | 4 -> ()
  | _ -> admit()


val update_last_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> totlen:len_t a
  -> len:size_nat{len < block_length a}
  -> b:multiseq (lanes a m) len
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((state_spec_v (update_last totlen len b st)).[l] ==
    Spec.update_last a totlen len b.(|l|) (state_spec_v st).[l])

let update_last_lemma_l #a #m totlen len b st0 l =
  let blocks = padded_blocks a len in
  let fin : size_nat = blocks * block_length a in
  let total_len_bits = secret (shift_left #(len_int_type a) totlen 3ul) in
  let totlen_seq = Lib.ByteSequence.uint_to_bytes_be #(len_int_type a) total_len_bits in
  let (b0,b1) = load_last #a #m totlen_seq fin len b in
  load_last_lemma_l #a #m totlen_seq fin len b l;
  let st = update b0 st0 in
  update_lemma_l b0 st0 l;
  update_lemma_l b1 st l


#push-options "--max_ifuel 1"
val transpose_state4_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 4}
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    (Seq.index (vec_v (transpose_state st).[ind / l])) (ind % l) ==
    (Seq.index (state_spec_v st).[j] (i / word_length a)))

let transpose_state4_lemma #a #m st j i =
  let r0 = VecTranspose.transpose4x4_lseq (sub st 0 4) in
  VecTranspose.transpose4x4_lemma (sub st 0 4);
  let r1 = VecTranspose.transpose4x4_lseq (sub st 4 4) in
  VecTranspose.transpose4x4_lemma (sub st 4 4)
#pop-options


val transpose_state_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   (let l = lanes a m in
    let ind = 8 * j + i / word_length a in
    (Seq.index (vec_v (transpose_state st).[ind / l])) (ind % l) ==
    (Seq.index (state_spec_v st).[j] (i / word_length a)))

let transpose_state_lemma_ij #a #m st j i =
  match lanes a m with
  | 1 -> ()
  | 4 -> transpose_state4_lemma #a #m st j i
  | _ -> admit()


val store_state_lemma_ij:
    #a:sha2_alg
  -> #m:m_spec
  -> st:state_spec a m
  -> j:nat{j < lanes a m}
  -> i:nat{i < 8 * word_length a} ->
  Lemma
   ((store_state st).[j * (8 * word_length a) + i] ==
    (BSeq.uint_to_bytes_be (Seq.index (state_spec_v st).[j] (i / word_length a))).[i % word_length a])

let store_state_lemma_ij #a #m st j i =
  let st1 = transpose_state st in
  let j_v = j * (8 * word_length a) + i in
  let blocksize_v = word_length a * lanes a m in

  calc (==) { // j_v % blocksize_v / word_length a
    (j * (8 * word_length a) + i) % blocksize_v / word_length a;
    (==) { Math.Lemmas.modulo_division_lemma (j * (8 * word_length a) + i) (word_length a) (lanes a m) }
    (j * (8 * word_length a) + i) / word_length a % lanes a m;
    (==) { Math.Lemmas.paren_mul_right j 8 (word_length a);
           Math.Lemmas.division_addition_lemma i (word_length a) (8 * j) }
    (8 * j + i / word_length a) % lanes a m;
    };

  calc (==) { // j_v / blocksize_v
    (j * (8 * word_length a) + i) / (word_length a * lanes a m);
    (==) { Math.Lemmas.division_multiplication_lemma (j * (8 * word_length a) + i) (word_length a) (lanes a m) }
    (j * (8 * word_length a) + i) / word_length a / lanes a m;
    (==) { Math.Lemmas.paren_mul_right j 8 (word_length a);
           Math.Lemmas.division_addition_lemma i (word_length a) (8 * j) }
    (8 * j + i / word_length a) / lanes a m;
    };

  calc (==) {
    Seq.index (store_state st) j_v;
    (==) { index_vecs_to_bytes_be #(word_t a) #(lanes a m) #8 st1 j_v }
    (BSeq.uints_to_bytes_be (vec_v st1.[j_v / blocksize_v])).[j_v % blocksize_v];
    (==) { BSeq.index_uints_to_bytes_be (vec_v st1.[j_v / blocksize_v]) (j_v % blocksize_v) }
    (BSeq.uint_to_bytes_be
      (Seq.index (vec_v st1.[j_v / blocksize_v]) (j_v % blocksize_v / word_length a))).[(j_v % blocksize_v) % word_length a];
    (==) { Math.Lemmas.modulo_modulo_lemma j_v (word_length a) (lanes a m) }
    (BSeq.uint_to_bytes_be
      (Seq.index (vec_v st1.[j_v / blocksize_v]) (j_v % blocksize_v / word_length a))).[j_v % word_length a];
    (==) { transpose_state_lemma_ij #a #m st j i }
    (BSeq.uint_to_bytes_be (Seq.index (state_spec_v st).[j] (i / word_length a))).[j_v % word_length a];
    (==) { Math.Lemmas.paren_mul_right j 8 (word_length a);
           Math.Lemmas.modulo_addition_lemma i (word_length a) (j * 8) }
    (BSeq.uint_to_bytes_be (Seq.index (state_spec_v st).[j] (i / word_length a))).[i % word_length a];
    }


val store_state_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
   (sub (store_state st) (l * (8 * word_length a)) (8 * word_length a) ==
    Spec.store_state a (state_spec_v st).[l])

let store_state_lemma_l #a #m st l =
  let st_l : words_state a = (state_spec_v st).[l] in
  let rp = Spec.store_state a st_l in
  let lp = store_state st in

  let aux (i:nat{i < 8 * word_length a}) : Lemma (lp.[l * (8 * word_length a) + i] == rp.[i]) =
    //assert (rp == BSeq.uints_to_bytes_be #(word_t a) #SEC #8 st_l);
    BSeq.index_uints_to_bytes_be #(word_t a) #SEC #8 st_l i;
    assert (rp.[i] == (BSeq.uint_to_bytes_be (Seq.index st_l (i / word_length a))).[i % word_length a]);
    store_state_lemma_ij #a #m st l i in

  Classical.forall_intro aux;
  eq_intro
    (sub (store_state st) (l * (8 * word_length a)) (8 * word_length a))
    (Spec.store_state a (state_spec_v st).[l])


// val emit_lemma_l:
//     #a:sha2_alg
//   -> #m:m_spec
//   -> hseq:lseq uint8 (lanes a m * 8 * word_length a)
//   -> l:nat{l < lanes a m} ->
//   Lemma ((emit hseq).(|l|) == Spec.emit a (sub hseq (l * (8 * word_length a)) (8 * word_length a)))

// let emit_lemma_l #a #m hseq l = ()


val finish_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma ((finish st).(|l|) == Spec.finish a (state_spec_v st).[l])

let finish_lemma_l #a #m st l =
  store_state_lemma_l #a #m st l


val update_block_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len
  -> i:nat{i < len / block_length a}
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
   ((state_spec_v (update_block len b i st)).[l] ==
    Spec.update_block a len b.(|l|) i (state_spec_v st).[l])

let update_block_lemma_l #a #m len b i st l =
  let mb = get_multiblock_spec len b i in
  update_lemma_l mb st l


val update_nblocks_loop_lemma:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len
  -> st:state_spec a m
  -> l:nat{l < lanes a m}
  -> n:nat{n <= len / block_length a } ->
  Lemma
   ((state_spec_v (repeati n (update_block #a #m len b) st)).[l] ==
    repeati n (Spec.update_block a len b.(|l|)) (state_spec_v st).[l])

let rec update_nblocks_loop_lemma #a #m len b st l n =
  let lp = repeati n (update_block #a #m len b) st in
  let f_sc = Spec.update_block a len b.(|l|) in
  let rp = repeati n f_sc (state_spec_v st).[l] in

  if n = 0 then begin
    eq_repeati0 n (update_block #a #m len b) st;
    eq_repeati0 n f_sc (state_spec_v st).[l] end
  else begin
    let lp1 = repeati (n - 1) (update_block #a #m len b) st in
    let rp1 = repeati (n - 1) f_sc (state_spec_v st).[l] in
    update_nblocks_loop_lemma #a #m len b st l (n - 1);
    assert ((state_spec_v lp1).[l] == rp1);
    unfold_repeati n (update_block #a #m len b) st (n - 1);
    unfold_repeati n f_sc (state_spec_v st).[l] (n - 1);
    update_block_lemma_l #a #m len b (n - 1) lp1 l end


val update_nblocks_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len
  -> st:state_spec a m
  -> l:nat{l < lanes a m} ->
  Lemma
   ((state_spec_v (update_nblocks len b st)).[l] ==
    Spec.update_nblocks a len b.(|l|) (state_spec_v st).[l])

let update_nblocks_lemma_l #a #m len b st l =
  let blocks = len / block_length a in
  update_nblocks_loop_lemma #a #m len b st l blocks


val hash_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len
  -> l:nat{l < lanes a m} ->
  Lemma ((hash #a #m len b).(|l|) == Spec.hash len b.(|l|))

let hash_lemma_l #a #m len b l =
  let len' : len_t a = Lib.IntTypes.cast #U32 #PUB (len_int_type a) PUB (size len) in
  let st0 = init a m in
  init_lemma_l a m l;
  let st1 = update_nblocks #a #m len b st0 in
  update_nblocks_lemma_l #a #m len b st0 l;
  let rem = len % block_length a in
  let mb = get_multilast_spec #a #m len b in
  let st = update_last len' rem mb st1 in
  update_last_lemma_l len' rem mb st1 l;
  finish_lemma_l st l


val hash_lemma:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len ->
  Lemma (forall (l:nat{l < lanes a m}).
    (hash #a #m len b).(|l|) == Spec.hash len b.(|l|))

let hash_lemma #a #m len b =
  Classical.forall_intro (hash_lemma_l #a #m len b)
