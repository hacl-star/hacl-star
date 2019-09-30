module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

// This is unnecessary because the same pragma is interleaved from the interface
#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Lib.Sequence.Lemmas +Lib.Sequence +FStar.Seq'"

val lemma_map_blocks_vec_i:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a
  -> f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block (length inp) (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last (length inp) (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre:squash (forall (i:nat{i < length inp}). map_blocks_vec_equiv_pre w blocksize inp f g f_v g_v i)
  -> i:nat{i < length inp} ->
  Lemma (
    let s = map_blocks blocksize inp f g in
    let v = map_blocks (w * blocksize) inp f_v g_v in
    Seq.index v i == Seq.index s i
  )

let lemma_map_blocks_vec_i #a w blocksize inp f g f_v g_v pre i =
  let len = length inp in
  let blocksize_v = w * blocksize in
  index_map_blocks blocksize inp f g i;
  index_map_blocks blocksize_v inp f_v g_v i;
  let s = map_blocks blocksize inp f g in
  let v = map_blocks (w * blocksize) inp f_v g_v in
  if i < (len / blocksize) * blocksize then
    div_mul_lt blocksize i (len / blocksize)
  else
    begin
    div_interval blocksize (len / blocksize) i;
    div_mul_l i len w blocksize;
    mod_interval_lt blocksize_v (i / blocksize_v) i len
    end

let lemma_map_blocks_vec #a w blocksize inp f g f_v g_v =
  Classical.forall_intro (lemma_map_blocks_vec_i w blocksize inp f g f_v g_v ())


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
