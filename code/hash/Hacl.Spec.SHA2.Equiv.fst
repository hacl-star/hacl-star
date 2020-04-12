module Hacl.Spec.SHA2.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.NTuple
open Lib.Sequence
open Lib.IntVector
open Lib.LoopCombinators

open Hacl.Spec.SHA2.Vec
open Spec.Hash.Definitions
module Constants = Spec.SHA2.Constants
module Spec = Hacl.Spec.SHA2
module LSeq = Lib.Sequence
module BSeq = Lib.ByteSequence


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


noextract
let transpose4x4_lseq (#t:v_inttype) (vs:lseq (vec_t t 4) 4) : lseq (vec_t t 4) 4 =
  let (v0,v1,v2,v3) = (vs.[0],vs.[1],vs.[2],vs.[3]) in
  let (v0'',v1'',v2'',v3'') = transpose4x4 (v0,v1,v2,v3) in
  create4 v0'' v1'' v2'' v3''

// this lemma is proven in code/chacha20/Hacl.Spec.Chacha20.Lemmas for t = U32
val transpose4x4_lemma: #t:v_inttype -> vs:lseq (vec_t t 4) 4 ->
  Lemma ((forall (i:nat{i < 4}) (j:nat{j < 4}).
    (vec_v (transpose4x4_lseq vs).[i]).[j] == (vec_v vs.[j]).[i]))
let transpose4x4_lemma #t vs = admit()


val transpose_ws4_lemma:
    #a:sha2_alg
  -> #m:m_spec{lanes a m == 4}
  -> ws:ws_spec a m
  -> i:nat{i < 4} ->
  Lemma
   (sub (transpose_ws4 ws) (i * lanes a m) (lanes a m) ==
    transpose4x4_lseq (sub ws (i * lanes a m) (lanes a m)))

let transpose_ws4_lemma #a #m ws i =
  eq_intro
    (sub (transpose_ws4 ws) (i * lanes a m) (lanes a m))
     (transpose4x4_lseq (sub ws (i * lanes a m) (lanes a m)))


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
  assert ((vec_v (transpose_ws4 ws).[i]).[j] == (vec_v (transpose4x4_lseq vs).[j_sub]).[j]);
  transpose4x4_lemma vs;
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
  let ws = load_ws b in
  load_ws_lemma_l b l;

  let st1 = shuffle ws st in
  shuffle_lemma_l ws st l;

  let res = map2 (+|) st1 st in
  state_spec_v_map2_add #a #m st1 st l


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

let update_last_lemma_l #a #m totlen len b st l = admit()


val hash_lemma_l:
    #a:sha2_alg
  -> #m:m_spec
  -> len:size_nat
  -> b:multiseq (lanes a m) len
  -> l:nat{l < lanes a m} ->
  Lemma ((hash #a #m len b).(|l|) == Spec.hash len b.(|l|))

let hash_lemma_l #a #m len b l = admit()
