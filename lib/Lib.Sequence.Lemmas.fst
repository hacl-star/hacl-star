module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

// This is unnecessary because the same pragma is interleaved from the interface
#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 \
             --using_facts_from '-* +Prims +Lib.Sequence.Lemmas +Lib.Sequence +FStar.Seq'"

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

let lemma_mod_bs_v_bs a w bs =
  Math.Lemmas.modulo_modulo_lemma a bs w;
  Math.Lemmas.swap_mul w bs

let lemma_div_bs_v_le a w bs = lemma_i_div_bs w bs a


let lemma_i_div_bs_lt w bs len i =
  let bs_v = w * bs in
  lemma_i_div_bs w bs i;
  div_interval bs_v (len / bs_v) i;
  //assert (i / bs == w * (len / (w * bs)) + i % (w * bs) / bs)
  lemma_i_div_bs w bs len

let lemma_i_mod_bs_lt w bs len i =
  mod_div_lt bs (i % (w * bs)) (len % (w * bs));
  lemma_mod_bs_v_bs i w bs;
  lemma_mod_bs_v_bs len w bs

val lemma_len_div_bs: bs:pos -> len:nat -> i:nat{len / bs * bs <= i /\ i < len} ->
  Lemma (len / bs == i / bs)
let lemma_len_div_bs bs len i =
  div_interval bs (len / bs) i

val lemma_i_div_bs_mul_bs:
  bs:pos -> w:pos -> bs_v:pos{bs_v == w * bs} -> i:nat ->
  Lemma (i / bs * bs == bs_v * (i / bs_v) + i % bs_v / bs * bs)
let lemma_i_div_bs_mul_bs bs w bs_v i =
  lemma_i_div_bs w bs i;
  Math.Lemmas.distributivity_add_left (w * (i / bs_v)) (i % bs_v / bs) bs;
  assert (i / bs * bs == w * (i / bs_v) * bs + i % bs_v / bs * bs);
  Math.Lemmas.swap_mul w (i / bs_v);
  Math.Lemmas.paren_mul_left (i / bs_v) w bs;
  assert (i / bs * bs == bs_v * (i / bs_v) + i % bs_v / bs * bs)

val lemma_i_mod_bs_v:
  len:nat -> bs:pos -> w:pos -> bs_v:pos{bs_v == w * bs} -> i:nat{(len / bs_v) * bs_v <= i /\ i < len} ->
  Lemma (i % bs_v == i - len / bs * bs + len % bs_v / bs * bs)
let lemma_i_mod_bs_v len bs w bs_v i =
  lemma_i_div_bs_mul_bs bs w bs_v len;
  lemma_len_div_bs bs_v len i


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

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
   b1 == b)

let lemma_slice_slice_f_vec_f #a #len w bs inp i =
  let bs_v = w * bs in
  let j_v = i / bs_v in
  let j = i % bs_v / bs in

  let aux () : Lemma ((j_v + 1) * bs_v <= len) =
    div_mul_lt bs_v i (len / bs_v) in

  let aux1 () : Lemma ((j + 1) * bs <= bs_v) =
    Math.Lemmas.swap_mul w bs;
    Math.Lemmas.modulo_division_lemma i bs w;
    assert (j < w);
    Math.Lemmas.lemma_mult_le_right bs (j + 1) w in

  let aux2 () : Lemma (j_v * bs_v + j * bs == i / bs * bs) =
    Math.Lemmas.paren_mul_right (i / bs_v) w bs;
    Math.Lemmas.distributivity_add_left (i / bs_v * w) ((i % bs_v) / bs) bs;
    lemma_i_div_bs w bs i in

  let aux3 () : Lemma (j_v * bs_v + (j + 1) * bs == (i / bs + 1) * bs) =
    Math.Lemmas.distributivity_add_left j 1 bs;
    Math.Lemmas.distributivity_add_left (i / bs) 1 bs;
    aux2 () in

  aux ();
  aux1 ();
  Seq.slice_slice inp (j_v * bs_v) ((j_v + 1) * bs_v) (j * bs) ((j + 1) * bs);
  aux2 ();
  aux3 ()


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
   b1 == b)

let lemma_slice_slice_g_vec_f #a #len w bs inp i =
  let bs_v = w * bs in
  let rem = len % bs_v in
  let j = i % bs_v / bs in

  let aux1 () : Lemma (0 <= len - rem /\ len - rem <= len) =
    Math.Lemmas.euclidean_division_definition len bs_v;
    assert (len - rem = len / bs_v * bs_v);
    Math.Lemmas.nat_times_nat_is_nat (len / bs_v) bs_v;
    assert (len - rem >= 0);
    Math.Lemmas.multiply_fractions len bs_v;
    assert (len - rem <= len);
    () in

  let aux2 () : Lemma (len - rem + j * bs == i / bs * bs) =
    calc (==) {
      i / bs * bs;
      (==) { lemma_i_div_bs_mul_bs bs w bs_v i }
      i / bs_v * bs_v + j * bs;
      (==) { lemma_len_div_bs bs_v len i }
      len / bs_v * bs_v + j * bs;
      (==) { Math.Lemmas.euclidean_division_definition len bs_v }
      len - rem + j * bs;
    } in

  let aux3 () : Lemma (len - rem + (j + 1) * bs == (i / bs + 1) * bs) =
    Math.Lemmas.distributivity_add_left j 1 bs;
    aux2 ();
    //assert (len - rem + j * bs + bs == i / bs * bs + bs);
    Math.Lemmas.distributivity_add_left (i / bs) 1 bs;
    () in

  let aux4 () : Lemma ((j + 1) * bs <= rem) =
    calc (<=) {
      (j + 1) * bs;
      (==) { aux3 () }
      (i / bs + 1) * bs - len + rem;
      (<=) { div_mul_lt bs i (len / bs);
	Math.Lemmas.lemma_mult_le_right bs (i / bs + 1) (len / bs) }
      len / bs * bs - len + rem;
      (<=) { Math.Lemmas.multiply_fractions len bs }
      rem;
    } in

  aux1 ();
  aux4 ();
  Seq.slice_slice inp (len - rem) len (j * bs) ((j + 1) * bs);
  aux2 ();
  aux3 ()


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
   b1 == b)

let lemma_slice_slice_g_vec_g #a #len w bs inp =
  let bs_v = w * bs in
  let rem = len % bs_v in
  Seq.slice_slice inp (len - rem) len (rem - rem % bs) rem;
  lemma_mod_bs_v_bs len w bs;
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


val lemma_map_blocks_vec_g_v_f_i:
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

let lemma_map_blocks_vec_g_v_f_i #a #len w blocksize blocksize_v inp f g g_v pre i =
  let b_v = get_last_s #_ #len blocksize_v inp in
  assert (map_blocks_vec_equiv_pre_g_v #a #len w blocksize blocksize_v f g g_v i b_v);
  lemma_slice_slice_g_vec_f #a #len w blocksize inp i// ;


val lemma_map_blocks_vec_g_v_g_i:
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

let lemma_map_blocks_vec_g_v_g_i #a #len w blocksize blocksize_v inp f g g_v pre i =
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

let lemma_map_blocks_vec_i #a #len w bs bs_v inp f g f_v g_v pre1 pre2 i =
  let aux1 (i:nat{(len / bs_v) * bs_v <= i /\ i < (len / bs) * bs}) : Lemma (i % bs_v < (len % bs_v) / bs * bs) =
    Math.Lemmas.multiply_fractions len bs;
    assert ((len / bs_v) * bs_v <= i /\ i < len);
    lemma_i_mod_bs_v len bs w bs_v i;
    () in

  let aux2 (i:nat{(len / bs) * bs <= i /\ i < len}) : Lemma ((len % bs_v) / bs * bs <= i % bs_v) =
    lemma_div_bs_v_le len w bs;
    assert (len / bs_v * bs_v <= i /\ i < len);
    lemma_i_mod_bs_v len bs w bs_v i;
    () in

  index_map_blocks bs inp f g i;
  index_map_blocks bs_v inp f_v g_v i;
  let s = map_blocks bs inp f g in
  let v = map_blocks (w * bs) inp f_v g_v in
  if i < (len / bs) * bs then begin
    div_mul_lt bs i (len / bs);
    if i < (len / bs_v) * bs_v then
      lemma_map_blocks_multi_vec_i_aux #a #len w bs bs_v inp f f_v pre1 i
    else begin
      aux1 i;
      //assert (i % bs_v < (len % bs_v) / bs * bs);
      lemma_map_blocks_vec_g_v_f_i #a #len w bs bs_v inp f g g_v pre2 i end end
  else begin
    div_interval bs (len / bs) i;
    div_mul_l i len w bs;
    mod_interval_lt bs_v (i / bs_v) i len;
    aux2 i;
    //assert ((len % bs_v) / bs * bs <= i % bs_v);
    lemma_map_blocks_vec_g_v_g_i #a #len w bs bs_v inp f g g_v pre2 i end


let lemma_map_blocks_vec #a #len w blocksize inp f g f_v g_v =
  let v = map_blocks (w * blocksize) inp f_v g_v in
  let s = map_blocks blocksize inp f g in
  Classical.forall_intro (lemma_map_blocks_vec_i #a #len w blocksize (w * blocksize) inp f g f_v g_v () ());
  Seq.lemma_eq_intro v s


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


let rec repeati_extensionality #a n f g acc0 =
  if n = 0 then begin
    Loops.eq_repeati0 n f acc0;
    Loops.eq_repeati0 n g acc0 end
  else begin
    Loops.unfold_repeati n f acc0 (n-1);
    Loops.unfold_repeati n g acc0 (n-1);
    repeati_extensionality #a (n-1) f g acc0 end


let rec repeati_right_extensionality #a n lo_g hi_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n (Loops.fixed_a a) f acc0;
    Loops.eq_repeat_right lo_g (lo_g+n) (Loops.fixed_a a) g acc0 end
  else begin
    Loops.unfold_repeat_right 0 n (Loops.fixed_a a) f acc0 (n-1);
    Loops.unfold_repeat_right lo_g (lo_g+n) (Loops.fixed_a a) g acc0 (lo_g+n-1);
    repeati_right_extensionality #a (n-1) lo_g hi_g f g acc0 end


val aux_repeat_bf_s0:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> i:nat{i < len0 / blocksize}
  -> acc:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
    let repeat_bf_s0 = repeat_blocks_f blocksize (Seq.slice inp 0 len0) f (len0 / blocksize) in
    let repeat_bf_t = repeat_blocks_f blocksize inp f (len / blocksize) in
    repeat_bf_s0 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s0 #a #b blocksize len0 inp f i acc =
  let len = length inp in
  FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
  let repeat_bf_s0 = repeat_blocks_f blocksize (Seq.slice inp 0 len0) f (len0 / blocksize) in
  let repeat_bf_t = repeat_blocks_f blocksize inp f (len / blocksize) in

  let nb = len0 / blocksize in
  assert ((i + 1) * blocksize <= nb * blocksize);
  let block = Seq.slice inp (i * blocksize) (i * blocksize + blocksize) in
  assert (repeat_bf_s0 i acc == f block acc);
  assert (repeat_bf_t i acc == f block acc)


#restart-solver
val lemma_aux: blocksize:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize == 0)
  (ensures  len0 / blocksize + (len - len0) / blocksize == len / blocksize)

let lemma_aux bs len len0 =
  calc (==) {
    len0 / bs + (len - len0) / bs;
    == { FStar.Math.Lemmas.lemma_div_exact len0 bs }
    len0 / bs + (len - len0 / bs * bs) / bs;
    == { FStar.Math.Lemmas.lemma_div_plus len (- len0 / bs) bs }
    len0 / bs + len / bs - len0 / bs;
    == { }
    len / bs;
  }


val lemma_aux2: blocksize:pos -> len:nat -> len0:nat -> i:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize == 0 /\ i < (len - len0) / blocksize)
  (ensures  len0 + i * blocksize + blocksize <= len)

let lemma_aux2 blocksize len len0 i =
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_mult_le_right blocksize (i + 1) (len1 / blocksize);
  assert (len0 + (i + 1) * blocksize <= len0 + len1 / blocksize * blocksize);
  FStar.Math.Lemmas.multiply_fractions len blocksize;
  assert (len1 / blocksize * blocksize <= len1);
  assert (len0 + (i + 1) * blocksize <= len)


val lemma_aux3: blocksize:pos -> len:nat -> len0:nat -> i:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize == 0 /\ i < (len - len0) / blocksize)
  (ensures  (len0 / blocksize + i) * blocksize == len0 + i * blocksize)

let lemma_aux3 blocksize len len0 i =
  calc (==) {
    (len0 / blocksize + i) * blocksize;
    (==) { FStar.Math.Lemmas.distributivity_add_left (len0 / blocksize) i blocksize }
    len0 / blocksize * blocksize + i * blocksize;
    (==) { FStar.Math.Lemmas.lemma_div_exact len0 blocksize }
    len0 + i * blocksize;
  }


val aux_repeat_bf_s1:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> i:nat{i < (length inp - len0) / blocksize}
  -> acc:b ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
    FStar.Math.Lemmas.lemma_div_le len1 len blocksize;
    let t1 = Seq.slice inp len0 len in
    let repeat_bf_s1 = repeat_blocks_f blocksize t1 f (len1 / blocksize) in
    let repeat_bf_t = repeat_blocks_f blocksize inp f (len / blocksize) in
    lemma_aux blocksize len len0;
    repeat_bf_s1 i acc == repeat_bf_t (len0 / blocksize + i) acc)

let aux_repeat_bf_s1 #a #b blocksize len0 inp f i acc =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
  FStar.Math.Lemmas.lemma_div_le len1 len blocksize;
  let t1 = Seq.slice inp len0 len in
  let repeat_bf_s1 = repeat_blocks_f blocksize t1 f (len1 / blocksize) in
  let repeat_bf_t = repeat_blocks_f blocksize inp f (len / blocksize) in

  let i_start = len0 / blocksize in
  let nb = len1 / blocksize in
  lemma_aux blocksize len len0;
  assert (i_start + nb = len / blocksize);

  lemma_aux2 blocksize len len0 i;
  let block = Seq.slice inp ((len0 / blocksize + i) * blocksize) ((len0 / blocksize + i) * blocksize + blocksize) in
  lemma_aux3 blocksize len len0 i;
  assert (block == Seq.slice inp (len0 + i * blocksize) (len0 + i * blocksize + blocksize));
  assert (repeat_bf_t (len0 / blocksize + i) acc == f block acc);

  //FStar.Math.Lemmas.lemma_mult_le_right blocksize (i + 1) (len1 / blocksize);
  //assert (i * blocksize + blocksize <= len1);
  assert (repeat_bf_s1 i acc == f (Seq.slice t1 (i * blocksize) (i * blocksize + blocksize)) acc);
  //assert (len0 + (i + 1) * blocksize <= len);
  FStar.Seq.Properties.slice_slice inp len0 len (i * blocksize) (i * blocksize + blocksize);
  assert (repeat_bf_s1 i acc == f block acc)


val repeat_blocks_split12:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
    FStar.Math.Lemmas.lemma_div_le len1 len blocksize;
    let repeat_bf_s0 = repeat_blocks_f blocksize (Seq.slice inp 0 len0) f (len0 / blocksize) in
    let repeat_bf_s1 = repeat_blocks_f blocksize (Seq.slice inp len0 len) f (len1 / blocksize) in
    let repeat_bf_t = repeat_blocks_f blocksize inp f (len / blocksize) in

    let acc1 = Loops.repeati (len0 / blocksize) repeat_bf_s0 acc0 in
    Loops.repeati (len1 / blocksize) repeat_bf_s1 acc1 ==
      Loops.repeati (len / blocksize) repeat_bf_t acc0)

let repeat_blocks_split12 #a #b blocksize len0 inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
  FStar.Math.Lemmas.lemma_div_le len1 len blocksize;

  let repeat_bf_s0 = repeat_blocks_f blocksize (Seq.slice inp 0 len0) f (len0 / blocksize) in
  let repeat_bf_s1 = repeat_blocks_f blocksize (Seq.slice inp len0 len) f (len1 / blocksize) in
  let repeat_bf_t = repeat_blocks_f blocksize inp f (len / blocksize) in

  let acc1 = Loops.repeati (len0 / blocksize) repeat_bf_s0 acc0 in
  calc (==) {
      Loops.repeati (len0 / blocksize) repeat_bf_s0 acc0;
    == { FStar.Classical.forall_intro_2 (aux_repeat_bf_s0 #a #b blocksize len0 inp f);
	 repeati_extensionality (len0 / blocksize) repeat_bf_s0 repeat_bf_t acc0 }
      Loops.repeati (len0 / blocksize) repeat_bf_t acc0;
    == { Loops.repeati_def (len0 / blocksize) repeat_bf_t acc0 }
      Loops.repeat_right 0 (len0 / blocksize) (Loops.fixed_a b) repeat_bf_t acc0;
    };

  let i_start = len0 / blocksize in
  let nb = len1 / blocksize in
  lemma_aux blocksize len len0;
  assert (i_start + nb = len / blocksize);
  let acc3 = Loops.repeati (len1 / blocksize) repeat_bf_s1 acc1 in
  calc (==) {
      Loops.repeati (len1 / blocksize) repeat_bf_s1 acc1;
    == { Loops.repeati_def (len1 / blocksize) repeat_bf_s1 acc1 }
      Loops.repeat_right 0 nb (Loops.fixed_a b) repeat_bf_s1 acc1;
    == { FStar.Classical.forall_intro_2 (aux_repeat_bf_s1 #a #b blocksize len0 inp f);
	 repeati_right_extensionality nb i_start (nb+i_start) repeat_bf_s1 repeat_bf_t acc1 }
      Loops.repeat_right i_start (i_start+nb) (Loops.fixed_a b) repeat_bf_t acc1;
    == { }
      Loops.repeat_right (len0 / blocksize) (len / blocksize) (Loops.fixed_a b) repeat_bf_t acc1;
    == { Loops.repeat_right_plus 0 (len0 / blocksize) (len / blocksize) (Loops.fixed_a b) repeat_bf_t acc0 }
      Loops.repeat_right 0 (len / blocksize) (Loops.fixed_a b) repeat_bf_t acc0;
    == { Loops.repeati_def (len / blocksize) repeat_bf_t acc0 }
      Loops.repeati (len / blocksize) repeat_bf_t acc0;
    }


#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"

val lemma_aux4: blocksize:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % blocksize == 0)
  (ensures  len0 + (len - len0) / blocksize * blocksize == len / blocksize * blocksize)

let lemma_aux4 bs len len0 =
  calc (==) {
    len0 + (len - len0) / bs * bs;
    == { FStar.Math.Lemmas.lemma_div_exact len0 bs }
    len0 + (len - len0 / bs * bs) / bs * bs;
    == { FStar.Math.Lemmas.lemma_div_plus len (- len0 / bs) bs }
    len0 + (len / bs - len0 / bs) * bs;
    == { FStar.Math.Lemmas.distributivity_sub_left (len / bs) (len0 / bs) bs }
    len0 + len / bs * bs - len0 / bs * bs;
    == { FStar.Math.Lemmas.lemma_div_exact len0 bs }
    len0 + len / bs * bs - len0;
    == { }
    len / bs * bs;
    }


let repeat_blocks_multi_split #a #b blocksize len0 inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
  assert (len % blocksize == len1 % blocksize);
  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
  FStar.Math.Lemmas.lemma_div_le len1 len blocksize;
  let repeat_bf_s0 = repeat_blocks_f blocksize t0 f (len0 / blocksize) in
  let repeat_bf_s1 = repeat_blocks_f blocksize t1 f (len1 / blocksize) in
  let repeat_bf_t  = repeat_blocks_f blocksize inp f (len / blocksize) in

  let acc1 = repeat_blocks_multi blocksize t0 f acc0 in
  let acc2 = repeat_blocks_multi blocksize t1 f acc1 in

  calc (==) {
    repeat_blocks_multi blocksize t1 f acc1;
    (==) { lemma_repeat_blocks_multi blocksize t1 f acc1 }
    Loops.repeati (len1 / blocksize) repeat_bf_s1 acc1;
    (==) { lemma_repeat_blocks_multi blocksize t0 f acc0 }
    Loops.repeati (len1 / blocksize) repeat_bf_s1 (Loops.repeati (len0 / blocksize) repeat_bf_s0 acc0);
    (==) { repeat_blocks_split12 blocksize len0 inp f acc0 }
    Loops.repeati (len / blocksize) repeat_bf_t acc0;
    (==) { lemma_repeat_blocks_multi blocksize inp f acc0 }
    repeat_blocks_multi blocksize inp f acc0;
  };
  assert (repeat_blocks_multi blocksize t1 f acc1 == repeat_blocks_multi blocksize inp f acc0)


#set-options "--z3rlimit 150 --initial_ifuel 1 --max_ifuel 1"
#restart-solver
let repeat_blocks_split #a #b blocksize len0 inp f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
  assert (len % blocksize == len1 % blocksize);
  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  FStar.Math.Lemmas.lemma_div_le len0 len blocksize;
  FStar.Math.Lemmas.lemma_div_le len1 len blocksize;
  let repeat_bf_s0 = repeat_blocks_f blocksize t0 f (len0 / blocksize) in
  let repeat_bf_s1 = repeat_blocks_f blocksize t1 f (len1 / blocksize) in
  let repeat_bf_t  = repeat_blocks_f blocksize inp f (len / blocksize) in

  let acc1 = repeat_blocks_multi blocksize t0 f acc0 in
  let acc2 = repeat_blocks blocksize t1 f l acc1 in

  let acc3 = Loops.repeati (len1 / blocksize) repeat_bf_s1 acc1 in

  calc (==) {
    repeat_blocks blocksize t1 f l acc1;
    (==) { lemma_repeat_blocks blocksize t1 f l acc1 }
    l (len1 % blocksize) (Seq.slice t1 (len1 / blocksize * blocksize) len1) acc3;
    (==) { FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize) }
    l (len % blocksize) (Seq.slice (Seq.slice inp len0 len) (len1 / blocksize * blocksize) len1) acc3;
    (==) { lemma_aux4 blocksize len len0; FStar.Seq.Properties.slice_slice inp len0 len (len1 / blocksize * blocksize) len1 }
    l (len % blocksize) (Seq.slice inp (len / blocksize * blocksize) len) acc3;
    (==) { lemma_repeat_blocks_multi blocksize t0 f acc0 }
    l (len % blocksize) (Seq.slice inp (len / blocksize * blocksize) len)
      (Loops.repeati (len1 / blocksize) repeat_bf_s1 (Loops.repeati (len0 / blocksize) repeat_bf_s0 acc0));
    (==) { repeat_blocks_split12 blocksize len0 inp f acc0 }
    l (len % blocksize) (Seq.slice inp (len / blocksize * blocksize) len) (Loops.repeati (len / blocksize) repeat_bf_t acc0);
    (==) { lemma_repeat_blocks blocksize inp f l acc0 }
    repeat_blocks blocksize inp f l acc0;
  };
  assert (repeat_blocks blocksize t1 f l acc1 == repeat_blocks blocksize inp f l acc0)


let unfold_repeatw #a w n f acc =
  match w with
  | 1 ->
    Loops.unfold_repeati n f acc (n-1)
  | 2 ->
    Loops.unfold_repeati (2*n) f acc (2*n-2);
    Loops.unfold_repeati (2*n) f acc (2*n-1)
  | 4 ->
    Loops.unfold_repeati (4*n) f acc (4*n-4);
    Loops.unfold_repeati (4*n) f acc (4*n-3);
    Loops.unfold_repeati (4*n) f acc (4*n-2);
    Loops.unfold_repeati (4*n) f acc (4*n-1)


let rec lemma_repeati_vec #a #a_vec w n normalize_n f f_vec acc0_vec =
  if n = 0 then begin
    Loops.eq_repeati0 n f_vec acc0_vec;
    Loops.eq_repeati0 (w * n) f (normalize_n acc0_vec) end
  else begin
    let acc0 = normalize_n acc0_vec in
    lemma_repeati_vec #a #a_vec w (n-1) normalize_n f f_vec acc0_vec;
    let next_p = Loops.repeati (n-1) f_vec acc0_vec in
    let next_v = Loops.repeati (w*(n-1)) f acc0 in
    assert (normalize_n next_p == next_v);

    let res1 = Loops.repeati n f_vec acc0_vec in
    let res2 = Loops.repeati (w*n) f acc0 in
    Loops.unfold_repeati n f_vec acc0_vec (n-1);
    assert (res1 == f_vec (n-1) next_p);
    unfold_repeatw w n f acc0;
    assert (res2 == repeat_w w n f (n-1) next_v);
    assert (normalize_n res1 == res2)
  end


#reset-options "--z3refresh --z3rlimit 300 --max_fuel 0 --max_ifuel 0"

val lemma_repeat_blocks_multi_load_acc:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:lanes
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{w * blocksize <= length inp /\ length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> normalize_n:(b_vec -> b)
  -> load_acc:(lseq a (w * blocksize) -> b -> b_vec)
  -> acc0:b ->
  Lemma
  (requires
   (let len0 = w * blocksize in
    let t0 = Seq.slice inp 0 len0 in
    let repeat_bf_t0 = repeat_blocks_f blocksize t0 f w in
    normalize_n (load_acc t0 acc0) == repeat_w #b w 1 repeat_bf_t0 0 acc0))
  (ensures
   (let len0 = w * blocksize in
    let t0 = Seq.slice inp 0 len0 in
    normalize_n (load_acc t0 acc0) == repeat_blocks_multi #a #b blocksize t0 f acc0))

let lemma_repeat_blocks_multi_load_acc #a #b #b_vec w blocksize inp f normalize_n load_acc acc0 =
  let len0 = w * blocksize in
  let t0 = Seq.slice inp 0 len0 in
  let repeat_bf_t0 = repeat_blocks_f blocksize t0 f w in
  let acc1 = load_acc t0 acc0 in
  calc (==) {
    normalize_n acc1;
    (==) { }
    repeat_w #b w 1 repeat_bf_t0 0 acc0;
    (==) { unfold_repeatw #b w 1 repeat_bf_t0 acc0; Loops.eq_repeati0 1 repeat_bf_t0 acc0 }
    Loops.repeati w repeat_bf_t0 acc0;
    (==) { lemma_repeat_blocks_multi #a #b blocksize t0 f acc0 }
    repeat_blocks_multi #a #b blocksize t0 f acc0;
  };
  assert (normalize_n acc1 == repeat_blocks_multi #a #b blocksize t0 f acc0)


let lemma_aux1 w blocksize len =
  let sb = w * blocksize in
  let len1 = len - w * blocksize in
  FStar.Math.Lemmas.modulo_addition_lemma len sb (- 1);
  assert (len % sb == len1 % sb);

  calc (==) {
    len1 / blocksize;
    (==) { FStar.Math.Lemmas.lemma_div_exact len1 sb }
    (len1 / sb * sb) / blocksize;
    (==) { FStar.Math.Lemmas.paren_mul_right (len1 / sb) w sb }
    ((len1 / sb * w) * blocksize) / blocksize;
    (==) { FStar.Math.Lemmas.multiple_division_lemma (len1 / sb * w) blocksize }
    len1 / sb * w;
    (==) { FStar.Math.Lemmas.swap_mul (len1 / sb) w}
    w * (len1 / sb);
  };
  assert (len1 / blocksize == w * (len1 / sb))


#set-options "--z3rlimit 300 --z3seed 1"
let lemma_repeat_blocks_multi_vec #a #b #b_vec w blocksize inp f f_vec normalize_n load_acc acc0 =
  let len = length inp in
  let len0 = w * blocksize in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
  assert (len % len0 == len1 % len0);
  FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- w);
  assert (len % blocksize == len1 % blocksize);

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let nb_vec = len1 / (w * blocksize) in
  let nb = len1 / blocksize in
  lemma_aux1 w blocksize len;
  assert (nb == w * nb_vec);

  let repeat_bf_vec = repeat_blocks_f (w * blocksize) t1 f_vec nb_vec in
  let repeat_bf_t0 = repeat_blocks_f blocksize t0 f w in
  let repeat_bf_t1 = repeat_blocks_f blocksize t1 f nb in

  let acc1 = load_acc t0 acc0 in
  calc (==) {
    normalize_n (repeat_blocks_multi (w * blocksize) t1 f_vec acc1);
    (==) { lemma_repeat_blocks_multi (w * blocksize) t1 f_vec acc1 }
    normalize_n (Loops.repeati nb_vec repeat_bf_vec acc1);
    (==) { lemma_repeati_vec w nb_vec normalize_n repeat_bf_t1 repeat_bf_vec acc1 }
    Loops.repeati nb repeat_bf_t1 (normalize_n acc1);
    (==) { lemma_repeat_blocks_multi blocksize t1 f (normalize_n acc1) }
    repeat_blocks_multi blocksize t1 f (normalize_n acc1);
    (==) { lemma_repeat_blocks_multi_load_acc #a #b #b_vec w blocksize inp f normalize_n load_acc acc0 }
    repeat_blocks_multi blocksize t1 f (repeat_blocks_multi #a #b blocksize t0 f acc0);
    (==) { repeat_blocks_multi_split blocksize len0 inp f acc0 }
    repeat_blocks_multi blocksize inp f acc0;
  }
