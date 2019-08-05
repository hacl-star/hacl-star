module Lib.Loops.Lemmas

open FStar.Mul
open FStar.Calc

open Lib.IntTypes
open Lib.Sequence
open Lib.IntVector

module Loops = Lib.LoopCombinators

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
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> i:nat{i < len0 / size_block}
  -> acc:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.lemma_div_le len0 len size_block;
    let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice inp 0 len0) f (len0 / size_block) in
    let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in
    repeat_bf_s0 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s0 #a #b size_block len0 inp f i acc =
  let len = length inp in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice inp 0 len0) f (len0 / size_block) in
  let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

  let nb = len0 / size_block in
  assert ((i + 1) * size_block <= nb * size_block);
  let block = Seq.slice inp (i * size_block) (i * size_block + size_block) in
  assert (repeat_bf_s0 i acc == f block acc);
  assert (repeat_bf_t i acc == f block acc)


val lemma_aux: size_block:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % size_block == 0)
  (ensures  len0 / size_block + (len - len0) / size_block == len / size_block)

let lemma_aux sb len len0 =
  calc (==) {
    len0 / sb + (len - len0) / sb;
    == { assert (len0 == len0 / sb * sb) }
    len0 / sb + (len - len0 / sb * sb) / sb;
    == { FStar.Math.Lemmas.lemma_div_plus len (- len0 / sb) sb }
    len0 / sb + len / sb - len0 / sb;
    == { }
    len / sb;
  }


val lemma_aux2: size_block:pos -> len:nat -> len0:nat -> i:nat ->
  Lemma
  (requires len0 <= len /\ len0 % size_block == 0 /\ i < (len - len0) / size_block)
  (ensures  len0 + i * size_block + size_block <= len)

let lemma_aux2 size_block len len0 i =
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_mult_le_right size_block (i + 1) (len1 / size_block);
  assert (len0 + (i + 1) * size_block <= len0 + len1 / size_block * size_block);
  FStar.Math.Lemmas.multiply_fractions len size_block;
  assert (len1 / size_block * size_block <= len1);
  assert (len0 + (i + 1) * size_block <= len)


val lemma_aux3: size_block:pos -> len:nat -> len0:nat -> i:nat ->
  Lemma
  (requires len0 <= len /\ len0 % size_block == 0 /\ i < (len - len0) / size_block)
  (ensures  (len0 / size_block + i) * size_block == len0 + i * size_block)

let lemma_aux3 size_block len len0 i =
  calc (==) {
    (len0 / size_block + i) * size_block;
    (==) { FStar.Math.Lemmas.distributivity_add_left (len0 / size_block) i size_block }
    len0 / size_block * size_block + i * size_block;
    (==) { assert (len0 / size_block * size_block == len0) }
    len0 + i * size_block;
  }


val aux_repeat_bf_s1:
    #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> i:nat{i < (length inp - len0) / size_block}
  -> acc:b ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    FStar.Math.Lemmas.lemma_div_le len0 len size_block;
    FStar.Math.Lemmas.lemma_div_le len1 len size_block;
    let t1 = Seq.slice inp len0 len in
    let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
    let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in
    lemma_aux size_block len len0;
    repeat_bf_s1 i acc == repeat_bf_t (len0 / size_block + i) acc)

let aux_repeat_bf_s1 #a #b size_block len0 inp f i acc =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;
  let t1 = Seq.slice inp len0 len in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  lemma_aux size_block len len0;
  assert (i_start + nb = len / size_block);

  lemma_aux2 size_block len len0 i;
  let block = Seq.slice inp ((len0 / size_block + i) * size_block) ((len0 / size_block + i) * size_block + size_block) in
  lemma_aux3 size_block len len0 i;
  assert (block == Seq.slice inp (len0 + i * size_block) (len0 + i * size_block + size_block));
  assert (repeat_bf_t (len0 / size_block + i) acc == f block acc);

  //FStar.Math.Lemmas.lemma_mult_le_right size_block (i + 1) (len1 / size_block);
  //assert (i * size_block + size_block <= len1);
  assert (repeat_bf_s1 i acc == f (Seq.slice t1 (i * size_block) (i * size_block + size_block)) acc);
  //assert (len0 + (i + 1) * size_block <= len);
  FStar.Seq.Properties.slice_slice inp len0 len (i * size_block) (i * size_block + size_block);
  assert (repeat_bf_s1 i acc == f block acc)


val repeat_blocks_split12:
    #a:Type0
  -> #b:Type0
  -> size_block:size_pos
  -> len0:nat{len0 % size_block = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a size_block -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    FStar.Math.Lemmas.lemma_div_le len0 len size_block;
    FStar.Math.Lemmas.lemma_div_le len1 len size_block;
    let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice inp 0 len0) f (len0 / size_block) in
    let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice inp len0 len) f (len1 / size_block) in
    let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

    let acc1 = Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 in
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 ==
      Loops.repeati (len / size_block) repeat_bf_t acc0)

let repeat_blocks_split12 #a #b size_block len0 inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;

  let repeat_bf_s0 = repeat_blocks_f size_block (Seq.slice inp 0 len0) f (len0 / size_block) in
  let repeat_bf_s1 = repeat_blocks_f size_block (Seq.slice inp len0 len) f (len1 / size_block) in
  let repeat_bf_t = repeat_blocks_f size_block inp f (len / size_block) in

  let acc1 = Loops.repeati (len0 / size_block) repeat_bf_s0 acc0 in
  calc (==) {
      Loops.repeati (len0 / size_block) repeat_bf_s0 acc0;
    == { FStar.Classical.forall_intro_2 (aux_repeat_bf_s0 #a #b size_block len0 inp f);
	 repeati_extensionality (len0 / size_block) repeat_bf_s0 repeat_bf_t acc0 }
      Loops.repeati (len0 / size_block) repeat_bf_t acc0;
    == { Loops.repeati_def (len0 / size_block) repeat_bf_t acc0 }
      Loops.repeat_right 0 (len0 / size_block) (Loops.fixed_a b) repeat_bf_t acc0;
    };

  let i_start = len0 / size_block in
  let nb = len1 / size_block in
  lemma_aux size_block len len0;
  assert (i_start + nb = len / size_block);
  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in
  calc (==) {
      Loops.repeati (len1 / size_block) repeat_bf_s1 acc1;
    == { Loops.repeati_def (len1 / size_block) repeat_bf_s1 acc1 }
      Loops.repeat_right 0 nb (Loops.fixed_a b) repeat_bf_s1 acc1;
    == { FStar.Classical.forall_intro_2 (aux_repeat_bf_s1 #a #b size_block len0 inp f);
	 repeati_right_extensionality nb i_start (nb+i_start) repeat_bf_s1 repeat_bf_t acc1 }
      Loops.repeat_right i_start (i_start+nb) (Loops.fixed_a b) repeat_bf_t acc1;
    == { }
      Loops.repeat_right (len0 / size_block) (len / size_block) (Loops.fixed_a b) repeat_bf_t acc1;
    == { Loops.repeat_right_plus 0 (len0 / size_block) (len / size_block) (Loops.fixed_a b) repeat_bf_t acc0 }
      Loops.repeat_right 0 (len / size_block) (Loops.fixed_a b) repeat_bf_t acc0;
    == { Loops.repeati_def (len / size_block) repeat_bf_t acc0 }
      Loops.repeati (len / size_block) repeat_bf_t acc0;
    }


val lemma_aux4: size_block:pos -> len:nat -> len0:nat ->
  Lemma
  (requires len0 <= len /\ len0 % size_block == 0)
  (ensures  len0 + (len - len0) / size_block * size_block == len / size_block * size_block)

let lemma_aux4 sb len len0 =
  calc (==) {
    len0 + (len - len0) / sb * sb;
    == { }
    len0 + (len - len0 / sb * sb) / sb * sb;
    == { FStar.Math.Lemmas.lemma_div_plus len (- len0 / sb) sb }
    len0 + (len / sb - len0 / sb) * sb;
    == { FStar.Math.Lemmas.distributivity_sub_left (len / sb) (len0 / sb) sb }
    len0 + len / sb * sb - len0 / sb * sb;
    == { }
    len0 + len / sb * sb - len0;
    == { }
    len / sb * sb;
    }


let repeat_blocks_multi_split #a #b size_block len0 inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len size_block (- len0 / size_block);
  assert (len % size_block == len1 % size_block);
  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t  = repeat_blocks_f size_block inp f (len / size_block) in

  let acc1 = repeat_blocks_multi size_block t0 f acc0 in
  let acc2 = repeat_blocks_multi size_block t1 f acc1 in

  calc (==) {
    repeat_blocks_multi size_block t1 f acc1;
    (==) { lemma_repeat_blocks_multi size_block t1 f acc1 }
    Loops.repeati (len1 / size_block) repeat_bf_s1 acc1;
    (==) { lemma_repeat_blocks_multi size_block t0 f acc0 }
    Loops.repeati (len1 / size_block) repeat_bf_s1 (Loops.repeati (len0 / size_block) repeat_bf_s0 acc0);
    (==) { repeat_blocks_split12 size_block len0 inp f acc0 }
    Loops.repeati (len / size_block) repeat_bf_t acc0;
    (==) { lemma_repeat_blocks_multi size_block inp f acc0 }
    repeat_blocks_multi size_block inp f acc0;
  };
  assert (repeat_blocks_multi size_block t1 f acc1 == repeat_blocks_multi size_block inp f acc0)


let repeat_blocks_split #a #b size_block len0 inp f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len size_block (- len0 / size_block);
  assert (len % size_block == len1 % size_block);
  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  FStar.Math.Lemmas.lemma_div_le len0 len size_block;
  FStar.Math.Lemmas.lemma_div_le len1 len size_block;
  let repeat_bf_s0 = repeat_blocks_f size_block t0 f (len0 / size_block) in
  let repeat_bf_s1 = repeat_blocks_f size_block t1 f (len1 / size_block) in
  let repeat_bf_t  = repeat_blocks_f size_block inp f (len / size_block) in

  let acc1 = repeat_blocks_multi size_block t0 f acc0 in
  let acc2 = repeat_blocks size_block t1 f l acc1 in

  let acc3 = Loops.repeati (len1 / size_block) repeat_bf_s1 acc1 in

  calc (==) {
    repeat_blocks size_block t1 f l acc1;
    (==) { lemma_repeat_blocks size_block t1 f l acc1 }
    l (len1 % size_block) (Seq.slice t1 (len1 / size_block * size_block) len1) acc3;
    (==) { FStar.Math.Lemmas.modulo_addition_lemma len size_block (- len0 / size_block) }
    l (len % size_block) (Seq.slice (Seq.slice inp len0 len) (len1 / size_block * size_block) len1) acc3;
    (==) { lemma_aux4 size_block len len0; FStar.Seq.Properties.slice_slice inp len0 len (len1 / size_block * size_block) len1 }
    l (len % size_block) (Seq.slice inp (len / size_block * size_block) len) acc3;
    (==) { lemma_repeat_blocks_multi size_block t0 f acc0 }
    l (len % size_block) (Seq.slice inp (len / size_block * size_block) len)
      (Loops.repeati (len1 / size_block) repeat_bf_s1 (Loops.repeati (len0 / size_block) repeat_bf_s0 acc0));
    (==) { repeat_blocks_split12 size_block len0 inp f acc0 }
    l (len % size_block) (Seq.slice inp (len / size_block * size_block) len) (Loops.repeati (len / size_block) repeat_bf_t acc0);
    (==) { lemma_repeat_blocks size_block inp f l acc0 }
    repeat_blocks size_block inp f l acc0;
  };
  assert (repeat_blocks size_block t1 f l acc1 == repeat_blocks size_block inp f l acc0)


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


val lemma_repeat_blocks_multi_load_acc:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:lanes
  -> size_block:size_pos{w * size_block <= max_size_t}
  -> inp:seq a{w * size_block <= length inp /\ length inp % (w * size_block) = 0 /\ length inp % size_block = 0}
  -> f:(lseq a size_block -> b -> b)
  -> normalize_n:(b_vec -> b)
  -> load_acc:(lseq a (w * size_block) -> b -> b_vec)
  -> acc0:b ->
  Lemma
  (requires
   (let len0 = w * size_block in
    let t0 = Seq.slice inp 0 len0 in
    let repeat_bf_t0 = repeat_blocks_f size_block t0 f w in
    normalize_n (load_acc t0 acc0) == repeat_w #b w 1 repeat_bf_t0 0 acc0))
  (ensures
   (let len0 = w * size_block in
    let t0 = Seq.slice inp 0 len0 in
    normalize_n (load_acc t0 acc0) == repeat_blocks_multi #a #b size_block t0 f acc0))

let lemma_repeat_blocks_multi_load_acc #a #b #b_vec w size_block inp f normalize_n load_acc acc0 =
  let len0 = w * size_block in
  let t0 = Seq.slice inp 0 len0 in
  let repeat_bf_t0 = repeat_blocks_f size_block t0 f w in
  let acc1 = load_acc t0 acc0 in
  calc (==) {
    normalize_n acc1;
    (==) { }
    repeat_w #b w 1 repeat_bf_t0 0 acc0;
    (==) { unfold_repeatw #b w 1 repeat_bf_t0 acc0; Loops.eq_repeati0 1 repeat_bf_t0 acc0 }
    Loops.repeati w repeat_bf_t0 acc0;
    (==) { lemma_repeat_blocks_multi #a #b size_block t0 f acc0 }
    repeat_blocks_multi #a #b size_block t0 f acc0;
  };
  assert (normalize_n acc1 == repeat_blocks_multi #a #b size_block t0 f acc0)


#reset-options "--z3refresh --z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let lemma_aux1 w size_block len =
  let sb = w * size_block in
  let len1 = len - w * size_block in
  FStar.Math.Lemmas.modulo_addition_lemma len sb (- 1);
  assert (len % sb == len1 % sb);

  calc (==) {
    len1 / size_block;
    (==) { FStar.Math.Lemmas.lemma_div_exact len1 sb }
    (len1 / sb * sb) / size_block;
    (==) { FStar.Math.Lemmas.paren_mul_right (len1 / sb) w sb }
    ((len1 / sb * w) * size_block) / size_block;
    (==) { FStar.Math.Lemmas.multiple_division_lemma (len1 / sb * w) size_block }
    len1 / sb * w;
    (==) { FStar.Math.Lemmas.swap_mul (len1 / sb) w}
    w * (len1 / sb);
  };
  assert (len1 / size_block == w * (len1 / sb))


let lemma_repeat_blocks_multi_vec #a #b #b_vec w size_block inp f f_vec normalize_n load_acc acc0 =
  let len = length inp in
  let len0 = w * size_block in
  let len1 = len - len0 in
  FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
  assert (len % len0 == len1 % len0);
  //FStar.Math.Lemmas.modulo_addition_lemma len size_block (- w);
  //assert (len % size_block == len1 % size_block);

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let nb_vec = len1 / (w * size_block) in
  let nb = len1 / size_block in
  lemma_aux1 w size_block len;
  assert (nb == w * nb_vec);

  let repeat_bf_vec = repeat_blocks_f (w * size_block) t1 f_vec nb_vec in
  let repeat_bf_t0 = repeat_blocks_f size_block t0 f w in
  let repeat_bf_t1 = repeat_blocks_f size_block t1 f nb in

  let acc1 = load_acc t0 acc0 in
  calc (==) {
    normalize_n (repeat_blocks_multi (w * size_block) t1 f_vec acc1);
    (==) { lemma_repeat_blocks_multi (w * size_block) t1 f_vec acc1 }
    normalize_n (Loops.repeati nb_vec repeat_bf_vec acc1);
    (==) { lemma_repeati_vec w nb_vec normalize_n repeat_bf_t1 repeat_bf_vec acc1 }
    Loops.repeati nb repeat_bf_t1 (normalize_n acc1);
    (==) { lemma_repeat_blocks_multi size_block t1 f (normalize_n acc1) }
    repeat_blocks_multi size_block t1 f (normalize_n acc1);
    (==) { lemma_repeat_blocks_multi_load_acc #a #b #b_vec w size_block inp f normalize_n load_acc acc0 }
    repeat_blocks_multi size_block t1 f (repeat_blocks_multi #a #b size_block t0 f acc0);
    (==) { repeat_blocks_multi_split size_block len0 inp f acc0 }
    repeat_blocks_multi size_block inp f acc0;
  }
