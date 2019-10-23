module Hacl.CTR.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Hacl.CTR.Lemmas +Lib.Sequence +FStar.Seq +Math.Lemmas'"


let lemma_i_div_bs w bs i =
  let bs_v = w * bs in
  calc (==) {
    w * (i / bs_v) + i % (w * bs) / bs;
  (==) { Math.Lemmas.swap_mul w bs }
    w * (i / bs_v) + i % (bs * w) / bs;
  (==) { Math.Lemmas.modulo_division_lemma i bs w }
    w * (i / bs_v) + i / bs % w;
  (==) { Math.Lemmas.division_multiplication_lemma i bs w }
    w * ((i / bs) / w) + i / bs % w;
  (==) { Math.Lemmas.euclidean_division_definition (i / bs) w }
    i / bs;
  }


let lemma_len_div_bs_v w bs len i = admit()

let lemma_len_div_bs w bs len i = admit()

let lemma_mod_bs_v_bs a w bs =
  Math.Lemmas.modulo_modulo_lemma a bs w;
  Math.Lemmas.swap_mul w bs

let lemma_div_bs_v_le a w bs = admit()

let lemma_i_div_bs_lt w bs len i = admit()

let lemma_i_le_len_div_bs_mul_bs w bs len i = admit()

let lemma_i_mod_bs_lt w bs len i = admit()


val lemma_slice_slice_f_vec_f:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> bs:size_pos{w * bs <= max_size_t}
  -> inp:seq a{length inp == len}
  -> i:nat{i < len / (w * bs) * (w * bs) /\ i < len / bs * bs} ->
  Lemma
  (let bs_v = w * bs in
   let b_v = get_block_s #a #len bs_v inp i in
   let b = get_block_s #a #len bs inp i in
   Math.Lemmas.cancel_mul_div w bs;
   //assert (i % bs_v < bs_v / bs * bs);
   let b1 = get_block_s #a #bs_v bs b_v (i % bs_v) in
   b1 `Seq.equal` b)

let lemma_slice_slice_f_vec_f #a #len w bs inp i = admit()


val lemma_slice_slice_g_vec_f:
    #a:Type
 -> #len:nat
  -> w:size_pos
  -> bs:size_pos{w * bs <= max_size_t}
  -> inp:seq a{length inp == len}
  -> i:nat{len / (w * bs) * (w * bs) <= i /\ i < len / bs * bs /\
        i % (w * bs) < (len % (w * bs)) / bs * bs} ->
  Lemma
  (let bs_v = w * bs in
   let rem = len % bs_v in
   let b_v: lseq a rem = get_last_s #a #len bs_v inp in
   let b: lseq a bs = get_block_s #a #len bs inp i in
   let b1: lseq a bs = get_block_s #a #rem bs b_v (i % bs_v) in
   b1 `Seq.equal` b)

let lemma_slice_slice_g_vec_f #a #len w bs inp i = admit()


val lemma_slice_slice_g_vec_g:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> bs:size_pos{w * bs <= max_size_t}
  -> inp:seq a{length inp == len} ->
  Lemma
  (let bs_v = w * bs in
   let rem = len % bs_v in
   let b_v = get_last_s #a #len bs_v inp in
   let b = get_last_s #a #len bs inp in
   let b1 = get_last_s #a #rem bs b_v in
   b1 `Seq.equal` b)

let lemma_slice_slice_g_vec_g #a #len w bs inp =
  let bs_v = w * bs in
  let rem = len % bs_v in
  Seq.slice_slice inp (len - rem) len (rem - rem % bs) rem;
  Math.Lemmas.modulo_modulo_lemma len bs w;
  Math.Lemmas.swap_mul w bs;
  assert (len % bs == rem % bs)


val lemma_map_blocks_multi_vec_i_aux:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos
  -> blocksize_v:size_pos{blocksize_v = w * blocksize}
  -> inp:seq a{length inp == len}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> pre:squash (forall (i:nat{i < len / blocksize_v * blocksize_v}) (b_v:lseq a (w * blocksize)).
         map_blocks_vec_equiv_pre_f_v #a #len w blocksize blocksize_v f f_v i b_v)
  -> i:nat{i < len / blocksize_v * blocksize_v} ->
  Lemma
   (lemma_div_bs_v_le len w blocksize;
   (get_block #_ #len blocksize_v inp f_v i).[i % blocksize_v] ==
   (get_block #_ #len blocksize inp f i).[i % blocksize])

let lemma_map_blocks_multi_vec_i_aux #a #len w blocksize blocksize_v inp f f_v pre i =
  lemma_div_bs_v_le len w blocksize;
  assert (i < len / blocksize * blocksize);
  let b_v = get_block_s #a #len blocksize_v inp i in
  assert (map_blocks_vec_equiv_pre_f_v #a #len w blocksize blocksize_v f f_v i b_v);
  Math.Lemmas.multiple_division_lemma w blocksize;
  assert (i % blocksize_v < blocksize_v / blocksize * blocksize);
  let b = get_block_s #_ #blocksize_v blocksize b_v (i % blocksize_v) in
  assert ((f_v (i / blocksize_v) b_v).[i % blocksize_v] == (f (i / blocksize) b).[i % blocksize]);
  assert ((get_block #_ #len blocksize_v inp f_v i).[i % blocksize_v] == (f_v (i / blocksize_v) b_v).[i % blocksize_v]);
  lemma_slice_slice_f_vec_f #a #len w blocksize inp i;
  assert ((get_block #_ #len blocksize inp f i).[i % blocksize] == (f (i / blocksize) b).[i % blocksize]);
  ()


val lemma_map_blocks_multi_vec_i:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos
  -> blocksize_v:size_pos{blocksize_v == w * blocksize}
  -> inp:seq a{length inp == len /\ len % blocksize_v = 0 /\ len % blocksize = 0}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> pre:squash (forall (i:nat{i < len}) (b_v:lseq a (w * blocksize)).
         map_blocks_vec_equiv_pre_f_v #a #len w blocksize (w * blocksize) f f_v i b_v)
  -> i:nat{i < len} ->
  Lemma
   (Math.Lemmas.div_exact_r len (w * blocksize);
    let blocksize_v = w * blocksize in
    let nb_v = len / blocksize_v in
    let nb = len / blocksize in

    let v = map_blocks_multi blocksize_v nb_v nb_v inp f_v in
    let s = map_blocks_multi blocksize nb nb inp f in
    Seq.index v i == Seq.index s i)

let lemma_map_blocks_multi_vec_i #a #len w blocksize blocksize_v inp f f_v pre i =
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let nb = len / blocksize in
  index_map_blocks_multi blocksize nb nb inp f i;
  index_map_blocks_multi blocksize_v nb_v nb_v inp f_v i;
  let s = map_blocks_multi blocksize nb nb inp f in
  let vec = map_blocks_multi blocksize_v nb_v nb_v inp f_v in
  //assert (Seq.index s i == (get_block #_ #len blocksize inp f i).[i % blocksize]);
  //assert (Seq.index vec i == (get_block #_ #len blocksize_v inp f_v i).[i % blocksize_v]);
  lemma_map_blocks_multi_vec_i_aux #a #len w blocksize blocksize_v inp f f_v pre i


let lemma_map_blocks_multi_vec #a #len w blocksize inp f f_v =
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let nb = len / blocksize in

  let v = map_blocks_multi blocksize_v nb_v nb_v inp f_v in
  let s = map_blocks_multi blocksize nb nb inp f in
  Classical.forall_intro (lemma_map_blocks_multi_vec_i #a #len w blocksize blocksize_v inp f f_v ());
  Seq.lemma_eq_intro v s


val lemma_map_blocks_vec_g_v_f_i_aux:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos
  -> blocksize_v:size_pos{blocksize_v == w * blocksize}
  -> inp:seq a{length inp == len}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre:squash ((forall (i:nat{len / blocksize_v * blocksize_v <= i /\ i < len}) (b_v:lseq a (len % blocksize_v)).
      map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v))
  -> i:nat{len / blocksize_v * blocksize_v <= i /\ i < len / blocksize * blocksize /\
	 i % blocksize_v < (len % blocksize_v) / blocksize * blocksize} ->
  Lemma
  ((get_last #_ #len blocksize_v inp g_v i).[i % blocksize_v] ==
   (get_block #_ #len blocksize inp f i).[i % blocksize])

let lemma_map_blocks_vec_g_v_f_i_aux #a #len w blocksize blocksize_v inp f g g_v pre i =
  let b_v = get_last_s #_ #len blocksize_v inp in
  assert (map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v);

  let rem_v = len % blocksize_v in
  let rem = len % blocksize in
  lemma_mod_bs_v_bs len w blocksize;
  assert (rem_v % blocksize = rem);

  let j = i % blocksize_v in
  let gv_b = g_v (len / blocksize_v) rem_v b_v in
  assert ((get_last #_ #len blocksize_v inp g_v i).[i % blocksize_v] == (gv_b).[j]);

  assert (j < rem_v / blocksize * blocksize);
  let b1 = get_block_s #a #rem_v blocksize b_v j in
  lemma_i_div_bs_lt w blocksize len i;
  let f_b1 = f (i / blocksize) b1 in
  assert ((gv_b).[j] == f_b1.[i % blocksize]);

  lemma_slice_slice_g_vec_f #a #len w blocksize inp i;
  let b: lseq a blocksize = get_block_s #a #len blocksize inp i in
  assert (b1 `Seq.equal` b);
  let f_b = f (i / blocksize) b in
  assert (f_b1.[i % blocksize] == f_b.[i % blocksize])


val lemma_map_blocks_vec_g_v_g_i_aux:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos
  -> blocksize_v:size_pos{blocksize_v = w * blocksize}
  -> inp:seq a{length inp == len}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre:squash (forall (i:nat{len / blocksize_v * blocksize_v <= i /\ i < len}) (b_v:lseq a (len % blocksize_v)).
      map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v)
  -> i:nat{len / blocksize * blocksize <= i /\ i < len /\
         (len % blocksize_v) / blocksize * blocksize <= i % blocksize_v} ->
  Lemma
  (div_interval blocksize (len / blocksize) i;
   div_mul_l i len w blocksize;
   mod_interval_lt blocksize_v (i / blocksize_v) i len;
   (get_last #_ #len blocksize_v inp g_v i).[i % blocksize_v] ==
   (get_last #_ #len blocksize inp g i).[i % blocksize])

let lemma_map_blocks_vec_g_v_g_i_aux #a #len w blocksize blocksize_v inp f g g_v pre i =
  lemma_div_bs_v_le len w blocksize;
  assert (len / blocksize_v * blocksize_v <= i);
  let b_v = get_last_s #_ #len blocksize_v inp in
  assert (map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v);

  let rem_v = len % blocksize_v in
  let rem = len % blocksize in
  lemma_mod_bs_v_bs len w blocksize;
  assert (rem_v % blocksize = rem);

  let j = i % blocksize_v in
  let gv_b = g_v (len / blocksize_v) rem_v b_v in
  assert ((get_last #_ #len blocksize_v inp g_v i).[i % blocksize_v] == (gv_b).[j]);

  assert (rem_v / blocksize * blocksize <= j);
  let b : lseq a rem = get_last_s #a #rem_v blocksize b_v in
  let g_b : lseq a rem = g (len / blocksize) rem b in
  mod_div_lt blocksize_v i len;
  assert (i % blocksize_v < len % blocksize_v);
  lemma_i_mod_bs_lt w blocksize len i;
  assert ((gv_b).[j] == g_b.[i % blocksize]);

  lemma_slice_slice_g_vec_g #a #len w blocksize inp;
  assert ((get_last #_ #len blocksize inp g i).[i % blocksize] == g_b.[i % blocksize])


val lemma_map_blocks_vec_i:
    #a:Type
  -> #len:nat
  -> w:size_pos
  -> blocksize:size_pos
  -> blocksize_v:size_pos{blocksize_v == w * blocksize}
  -> inp:seq a{length inp == len}
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre1:squash (forall (i:nat{i < len / blocksize_v * blocksize_v}) (b_v:lseq a blocksize_v).
      map_blocks_vec_equiv_pre_f_v #a #len w blocksize blocksize_v f f_v i b_v)
  -> pre2:squash (forall (i:nat{len / blocksize_v * blocksize_v <= i /\ i < len}) (b_v:lseq a (len % blocksize_v)).
      map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v)
  -> i:nat{i < len} ->
  Lemma
   (let v = map_blocks blocksize_v inp f_v g_v in
    let s = map_blocks blocksize inp f g in
    Seq.index v i == Seq.index s i)

let lemma_map_blocks_vec_i #a #len w blocksize blocksize_v inp f g f_v g_v pre1 pre2 i =
  index_map_blocks blocksize inp f g i;
  index_map_blocks blocksize_v inp f_v g_v i;
  let s = map_blocks blocksize inp f g in
  let v = map_blocks (w * blocksize) inp f_v g_v in
  if i < (len / blocksize) * blocksize then begin
    div_mul_lt blocksize i (len / blocksize);
    if i < (len / blocksize_v) * blocksize_v then
      lemma_map_blocks_multi_vec_i_aux #a #len w blocksize blocksize_v inp f f_v pre1 i
    else begin
      assume (i % blocksize_v < (len % blocksize_v) / blocksize * blocksize);
      lemma_map_blocks_vec_g_v_f_i_aux #a #len w blocksize blocksize_v inp f g g_v pre2 i end end
  else begin
    div_interval blocksize (len / blocksize) i;
    div_mul_l i len w blocksize;
    mod_interval_lt blocksize_v (i / blocksize_v) i len;
    assume ((len % blocksize_v) / blocksize * blocksize <= i % blocksize_v);
    lemma_map_blocks_vec_g_v_g_i_aux #a #len w blocksize blocksize_v inp f g g_v pre2 i end


let lemma_map_blocks_vec #a #len w blocksize inp f g f_v g_v =
  let v = map_blocks (w * blocksize) inp f_v g_v in
  let s = map_blocks blocksize inp f g in
  Classical.forall_intro (lemma_map_blocks_vec_i #a #len w blocksize (w * blocksize) inp f g f_v g_v () ());
  Seq.lemma_eq_intro v s
