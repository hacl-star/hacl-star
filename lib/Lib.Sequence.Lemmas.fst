module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


let rec repeati_extensionality #a n f g acc0 =
  if n = 0 then begin
    Loops.eq_repeati0 n f acc0;
    Loops.eq_repeati0 n g acc0 end
  else begin
    Loops.unfold_repeati n f acc0 (n-1);
    Loops.unfold_repeati n g acc0 (n-1);
    repeati_extensionality #a (n-1) f g acc0 end


let rec repeat_gen_right_extensionality n lo_g hi_g a_f a_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n a_f f acc0;
    Loops.eq_repeat_right lo_g (lo_g+n) a_g g acc0 end
  else begin
    Loops.unfold_repeat_right 0 n a_f f acc0 (n-1);
    Loops.unfold_repeat_right lo_g (lo_g+n) a_g g acc0 (lo_g+n-1);
    repeat_gen_right_extensionality (n-1) lo_g hi_g a_f a_g f g acc0 end


let rec lemma_repeat_gen_vec w n a a_vec normalize_v f f_v acc_v0 =
  let lp = Loops.repeat_right 0 n a_vec f_v acc_v0 in
  let rp = Loops.repeat_right 0 (w * n) a f (normalize_v 0 acc_v0) in
  if n = 0 then begin
    Loops.eq_repeat_right 0 n a_vec f_v acc_v0;
    Loops.eq_repeat_right 0 (w * n) a f (normalize_v 0 acc_v0);
    () end
  else begin
    lemma_repeat_gen_vec w (n - 1) a a_vec normalize_v f f_v acc_v0;
    let next_p = Loops.repeat_right 0 (n - 1) a_vec f_v acc_v0 in
    let next_v = Loops.repeat_right 0 (w * (n - 1)) a f (normalize_v 0 acc_v0) in
    assert (normalize_v (n - 1) next_p == next_v);
    Loops.unfold_repeat_right 0 n a_vec f_v acc_v0 (n - 1);
    assert (lp == f_v (n - 1) next_p);
    Loops.repeat_right_plus 0 (w * (n - 1)) (w * n) a f (normalize_v 0 acc_v0);
    assert (rp == Loops.repeat_right (w * (n - 1)) (w * n) a f next_v);
    assert (normalize_v n lp == Loops.repeat_right (w * (n - 1)) (w * n) a f next_v);
    () end


let repeati_right_extensionality #a n lo_g hi_g f g acc0 =
  repeat_gen_right_extensionality n lo_g hi_g (Loops.fixed_a a) (Loops.fixed_a a) f g acc0


let lemma_repeati_vec #a #a_vec w n normalize_v f f_v acc_v0 =
  lemma_repeat_gen_vec w n (Loops.fixed_a a) (Loops.fixed_a a_vec) (Loops.fixed_i normalize_v) f f_v acc_v0;
  Loops.repeati_def n f_v acc_v0;
  Loops.repeati_def (w * n) f (normalize_v acc_v0)


val repeat_gen_blocks_f:
    #inp_t:Type0
  -> blocksize:size_pos
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> inp:seq inp_t{length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{i < n}
  -> acc:a i ->
  a (i + 1)

let repeat_gen_blocks_f #inp_t blocksize n a inp f i acc =
  Math.Lemmas.lemma_mult_le_right blocksize (i + 1) n;
  let block = Seq.slice inp (i * blocksize) (i * blocksize + blocksize) in
  f i block acc


let repeat_gen_blocks_multi #inp_t blocksize n a inp f acc0 =
  Loops.repeat_gen n a (repeat_gen_blocks_f blocksize n a inp f) acc0


let repeat_gen_blocks #inp_t #c blocksize inp a f l acc0 =
  let len = length inp in
  let nb = len / blocksize in
  let rem = len % blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let last = Seq.slice inp (nb * blocksize) len in
  Math.Lemmas.cancel_mul_div nb blocksize;
  let acc = repeat_gen_blocks_multi #inp_t blocksize nb a blocks f acc0 in
  l nb rem last acc


let len0_div_bs blocksize len len0 =
  calc (==) {
    len0 / blocksize + (len - len0) / blocksize;
    == { Math.Lemmas.lemma_div_exact len0 blocksize }
    len0 / blocksize + (len - len0 / blocksize * blocksize) / blocksize;
    == { Math.Lemmas.lemma_div_plus len (- len0 / blocksize) blocksize }
    len0 / blocksize + len / blocksize + (- len0 / blocksize);
    == { }
    len / blocksize;
  }


////////////////////////
// Start of proof of repeat_gen_blocks_multi_split lemma
////////////////////////

val aux_repeat_bf_s0:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{i < len0 / blocksize}
  -> acc:a i ->
  Lemma
   (let len = length inp in
    Math.Lemmas.cancel_mul_div n blocksize;
    len0_div_bs blocksize len len0;
    let t0 = Seq.slice inp 0 len0 in
    let repeat_bf_s0 = repeat_gen_blocks_f blocksize (len0 / blocksize) a t0 f in
    let repeat_bf_t  = repeat_gen_blocks_f blocksize n a inp f in
    repeat_bf_s0 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s0 #inp_t blocksize len0 n a inp f i acc =
  let len = length inp in
  let n0 = len0 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n == n0 + (len - len0) / blocksize);
  let t0 = Seq.slice inp 0 len0 in
  let repeat_bf_s0 = repeat_gen_blocks_f blocksize (len0 / blocksize) a t0 f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize n a inp f in

  Math.Lemmas.lemma_mult_le_right blocksize (i + 1) n;
  let block = Seq.slice inp (i * blocksize) (i * blocksize + blocksize) in
  assert (repeat_bf_t i acc == f i block acc);

  Math.Lemmas.lemma_mult_le_right blocksize (i + 1) n0;
  Seq.slice_slice inp 0 len0 (i * blocksize) (i * blocksize + blocksize);
  assert (repeat_bf_s0 i acc == f i block acc)


val aux_repeat_bf_s1:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{i < (length inp - len0) / blocksize}
  -> acc:a (len0 / blocksize + i) ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    Math.Lemmas.cancel_mul_div n blocksize;
    len0_div_bs blocksize len len0;
    //assert (n == n0 + n1);

    let a1 = shift_a n n0 n1 a in
    let f1 = shift_f blocksize n n0 n1 a f in
    let t1 = Seq.slice inp len0 len in
    Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
    assert (len % blocksize == len1 % blocksize);
    Math.Lemmas.cancel_mul_mod n blocksize;

    let repeat_bf_s1 = repeat_gen_blocks_f blocksize n1 a1 t1 f1 in
    let repeat_bf_t  = repeat_gen_blocks_f blocksize n a inp f in
    repeat_bf_s1 i acc == repeat_bf_t (n0 + i) acc)

let aux_repeat_bf_s1 #inp_t blocksize len0 n a inp f i acc =
  let len = length inp in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n == n0 + n1);

  let a1 = shift_a n n0 n1 a in
  let f1 = shift_f blocksize n n0 n1 a f in
  let t1 = Seq.slice inp len0 len in
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  assert (len % blocksize == len1 % blocksize);
  Math.Lemmas.cancel_mul_mod n blocksize;

  let repeat_bf_s1 = repeat_gen_blocks_f blocksize n1 a1 t1 f1 in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize n a inp f in

  Math.Lemmas.lemma_mult_le_right blocksize (n0 + i + 1) n;
  let block = Seq.slice inp ((n0 + i) * blocksize) ((n0 + i) * blocksize + blocksize) in
  assert (repeat_bf_t (n0 + i) acc == f1 i block acc);

  calc (<=) {
    i * blocksize + blocksize;
    (<=) { Math.Lemmas.lemma_mult_le_right blocksize (i + 1) n1 }
    n1 * blocksize;
    (==) { Math.Lemmas.div_exact_r len1 blocksize }
    len1;
    };

  calc (==) {
    len0 + i * blocksize;
    (==) { Math.Lemmas.div_exact_r len0 blocksize }
    n0 * blocksize + i * blocksize;
    (==) { Math.Lemmas.distributivity_add_left n0 i blocksize }
    (n0 + i) * blocksize;
    };

  Seq.slice_slice inp len0 len (i * blocksize) (i * blocksize + blocksize);
  assert (repeat_bf_s1 i acc == f1 i block acc)


let repeat_gen_blocks_multi_split #inp_t blocksize len0 n a inp f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n0 + n1 == n);

  let a1 = shift_a n n0 n1 a in
  let f1 = shift_f blocksize n n0 n1 a f in

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  assert (len % blocksize == len1 % blocksize);
  Math.Lemmas.cancel_mul_mod n blocksize;

  let repeat_bf_s0 = repeat_gen_blocks_f blocksize n0 a t0 f in
  let repeat_bf_s1 = repeat_gen_blocks_f blocksize n1 a1 t1 f1 in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize n a inp f in

  let acc1 : a n0 = repeat_gen_blocks_multi blocksize n0 a t0 f acc0 in
  let acc2 = repeat_gen_blocks_multi blocksize n1 a1 t1 f1 acc1 in
  //assert (acc2 == Loops.repeat_gen n1 a1 repeat_bf_s1 (Loops.repeat_gen n0 a repeat_bf_s0 acc0));

  calc (==) {
    Loops.repeat_gen n0 a repeat_bf_s0 acc0;
    (==) { Loops.repeat_gen_def n0 a repeat_bf_s0 acc0 }
    Loops.repeat_right 0 n0 a repeat_bf_s0 acc0;
    (==) { Classical.forall_intro_2 (aux_repeat_bf_s0 #inp_t blocksize len0 n a inp f);
	   repeat_gen_right_extensionality n0 0 n0 a a repeat_bf_s0 repeat_bf_t acc0 }
    Loops.repeat_right 0 n0 a repeat_bf_t acc0;
    };

  calc (==) {
    Loops.repeat_gen n1 a1 repeat_bf_s1 acc1;
    (==) { Loops.repeat_gen_def n1 a1 repeat_bf_s1 acc1 }
    Loops.repeat_right 0 n1 a1 repeat_bf_s1 acc1;
    (==) { Classical.forall_intro_2 (aux_repeat_bf_s1 #inp_t blocksize len0 n a inp f);
	   repeat_gen_right_extensionality n1 n0 n a1 a repeat_bf_s1 repeat_bf_t acc1 }
    Loops.repeat_right n0 n a repeat_bf_t acc1;
    (==) { }
    Loops.repeat_right n0 n a repeat_bf_t (Loops.repeat_right 0 n0 a repeat_bf_t acc0);
    (==) { Loops.repeat_right_plus 0 n0 n a repeat_bf_t acc0 }
    Loops.repeat_right 0 n a repeat_bf_t acc0;
    (==) { Loops.repeat_gen_def n a repeat_bf_t acc0 }
    Loops.repeat_gen n a repeat_bf_t acc0;
    };
  assert (acc2 == repeat_gen_blocks_multi blocksize n a inp f acc0)

////////////////////////
// End of proof of repeat_gen_blocks_multi_split lemma
////////////////////////

val repeat_gen_multi_blocks_split_slice:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> inp:seq inp_t{len0 <= length inp / blocksize * blocksize}
  -> a:(i:nat{i <= length inp / blocksize} -> Type)
  -> f:(i:nat{i < length inp / blocksize} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a 0 ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n = len / blocksize in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    len0_div_bs blocksize len len0;

    let a1 = shift_a n n0 n1 a in
    let f1 = shift_f blocksize n n0 n1 a f in
    Math.Lemmas.lemma_mod_sub_distr (n * blocksize) len0 blocksize;
    Math.Lemmas.cancel_mul_mod n blocksize;
    //assert ((n * blocksize - len0) % blocksize == 0);

    let blocks = Seq.slice inp 0 (n * blocksize) in
    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 (n * blocksize) in
    let acc1 : a n0 = repeat_gen_blocks_multi blocksize n0 a t0 f acc0 in
    repeat_gen_blocks_multi blocksize n a blocks f acc0 ==
    repeat_gen_blocks_multi blocksize n1 a1 t1 f1 acc1)

let repeat_gen_multi_blocks_split_slice #inp_t blocksize len0 inp a f acc0 =
  let n = length inp / blocksize in
  let len = n * blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  assert (length inp / blocksize == len / blocksize);
  let blocks = Seq.slice inp 0 len in

  //let len1 = len - len0 in
  len0_div_bs blocksize len len0;
  len0_div_bs blocksize (length inp) len0;
  //assert (len1 / blocksize == (length inp - len0) / blocksize)
  repeat_gen_blocks_multi_split blocksize len0 n a blocks f acc0

#push-options "--z3rlimit 150"

let repeat_gen_blocks_split #inp_t #c blocksize len0 inp max a f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  len0_div_bs blocksize len len0;
  assert (n0 + n1 == n);

  let a1 = shift_a n n0 n1 a in
  let f1 = shift_f blocksize n n0 n1 a f in
  let l1 = shift_l blocksize max n n0 n1 a l in

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let acc : a n0 = repeat_gen_blocks_multi blocksize n0 a t0 f acc0 in
  let blocks1 = Seq.slice t1 0 (n1 * blocksize) in
  Math.Lemmas.cancel_mul_mod n1 blocksize;
  let acc1 = repeat_gen_blocks_multi #inp_t blocksize n1 a1 blocks1 f1 acc in
  let last1 = Seq.slice t1 (n1 * blocksize) len1 in
  let last = Seq.slice inp (n * blocksize) len in

  calc (==) {
    len0 + n1 * blocksize;
    (==) { }
    len0 + (n - n0) * blocksize;
    (==) { Math.Lemmas.distributivity_sub_left n n0 blocksize }
    len0 + n * blocksize - n0 * blocksize;
    (==) { Math.Lemmas.div_exact_r len0 blocksize }
    n * blocksize;
  };

  calc (==) {
    repeat_gen_blocks blocksize t1 a1 f1 l1 acc;
    (==) { }
    l n (len1 % blocksize) last1 acc1;
    (==) { Math.Lemmas.lemma_mod_sub_distr len len0 blocksize }
    l n (len % blocksize) last1 acc1;
    (==) { Seq.slice_slice inp len0 len (n1 * blocksize) len1 }
    l n (len % blocksize) last acc1;
    (==) { repeat_gen_multi_blocks_split_slice #inp_t blocksize len0 inp a f acc0 }
    repeat_gen_blocks blocksize inp a f l acc0;
    }
#pop-options


let lemma_repeat_gen_blocks_multi_vec #inp_t w blocksize n inp a a_vec f f_v normalize_v acc_v0 = admit()


val repeat_blocks_multi_is_repeat_gen:
    #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> inp:seq a{length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> acc0:b -> Lemma
  (let n = length inp / blocksize in
   Math.Lemmas.div_exact_r (length inp) blocksize;
   repeat_blocks_multi #a #b blocksize inp f acc0 ==
   repeat_gen_blocks_multi #a blocksize n (Loops.fixed_a b) inp (Loops.fixed_i f) acc0)

let repeat_blocks_multi_is_repeat_gen #a #b blocksize inp f acc0 =
  let len = length inp in
  let n = len / blocksize in
  Math.Lemmas.div_exact_r (length inp) blocksize;

  let f_rep = repeat_blocks_f blocksize inp f n in
  let f_gen = repeat_gen_blocks_f blocksize n (Loops.fixed_a b) inp (Loops.fixed_i f) in

  let lp = repeat_blocks_multi #a #b blocksize inp f acc0 in
  lemma_repeat_blocks_multi #a #b blocksize inp f acc0;
  //assert (lp == Loops.repeati n (repeat_blocks_f blocksize inp f n) acc0);
  Loops.repeati_def n (repeat_blocks_f blocksize inp f n) acc0;
  //assert (lp == Loops.repeat_right 0 n (Loops.fixed_a b) (repeat_blocks_f blocksize inp f n) acc0);

  let aux (i:nat{i < n}) (acc:b) : Lemma (f_rep i acc == f_gen i acc) = () in
  Classical.forall_intro_2 aux;
  repeat_gen_right_extensionality n 0 n (Loops.fixed_a b) (Loops.fixed_a b) f_rep f_gen acc0;
  Loops.repeat_gen_def n (Loops.fixed_a b) f_gen acc0


val map_blocks_multi_is_repeat_gen:
    #a:Type0
  -> blocksize:size_pos
  -> n:nat
  -> inp:seq a{length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq a blocksize -> lseq a blocksize) -> Lemma
  (let f_gen (i:nat{i < n}) (block:lseq a blocksize)
    (acc:map_blocks_a a blocksize n i) : map_blocks_a a blocksize n (i + 1) =
    Seq.append acc (f i block) in

   map_blocks_multi #a blocksize n n inp f ==
   repeat_gen_blocks_multi #a blocksize n (map_blocks_a a blocksize n) inp f_gen Seq.empty)

let map_blocks_multi_is_repeat_gen #a blocksize n inp f =
  let f_g (i:nat{i < n}) (block:lseq a blocksize)
    (acc:map_blocks_a a blocksize n i) : map_blocks_a a blocksize n (i + 1) =
    Seq.append acc (f i block) in

  let f_gen = repeat_gen_blocks_f blocksize n (map_blocks_a a blocksize n) inp f_g in
  let f_map = map_blocks_f #a blocksize n inp f in
  //let lp = map_blocks_multi #a blocksize n n inp f in
  lemma_map_blocks_multi #a blocksize n n inp f;
  Loops.repeat_gen_def n (map_blocks_a a blocksize n) f_map Seq.empty;
  Loops.repeat_gen_def n (map_blocks_a a blocksize n) f_gen Seq.empty;

  let aux (i:nat{i < n}) (acc:map_blocks_a a blocksize n i) : Lemma (f_map i acc == f_gen i acc) = () in
  Classical.forall_intro_2 aux;
  repeat_gen_right_extensionality n 0 n (map_blocks_a a blocksize n)
    (map_blocks_a a blocksize n) f_map f_gen Seq.empty


val map_blocks_is_repeat_gen:
    #a:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i == length inp / blocksize} -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma
  (let len = length inp in
   let nb = len / blocksize in
   let f_gen (i:nat{i < nb}) (block:lseq a blocksize)
    (acc:map_blocks_a a blocksize nb i) : map_blocks_a a blocksize nb (i + 1) =
    Seq.append acc (f i block) in

   let l_gen (i:nat{i == nb}) (rem:nat{rem == len % blocksize}) (last:lseq a rem)
     (acc:map_blocks_a a blocksize nb i) : s:seq a{length s == len} =
     if rem > 0 then Seq.append acc (l nb rem last) else acc in

   map_blocks #a blocksize inp f l ==
   repeat_gen_blocks #a blocksize inp (map_blocks_a a blocksize nb) f_gen l_gen Seq.empty)

let map_blocks_is_repeat_gen #a blocksize inp f l =
  let len = length inp in
  let nb = len / blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  lemma_map_blocks #a blocksize inp f l;
  Math.Lemmas.cancel_mul_div nb blocksize;
  map_blocks_multi_is_repeat_gen #a blocksize nb blocks f



(*)


////////////////////////
// Start of proof of lemma_repeat_blocks_multi_vec
////////////////////////

val len_div_bs_w: w:pos -> blocksize:pos -> len:nat -> Lemma
  (requires len % (w * blocksize) = 0 /\ len % blocksize = 0)
  (ensures  len / blocksize == len / (w * blocksize) * w)

let len_div_bs_w w blocksize len =
  let blocksize_v = w * blocksize in
  calc (==) {
    len / blocksize;
    (==) { Math.Lemmas.lemma_div_exact len blocksize_v }
    (len / blocksize_v * blocksize_v) / blocksize;
    (==) { Math.Lemmas.paren_mul_right (len / blocksize_v) w blocksize }
    ((len / blocksize_v * w) * blocksize) / blocksize;
    (==) { Math.Lemmas.multiple_division_lemma (len / blocksize_v * w) blocksize }
    len / blocksize_v * w;
  }


val slice_slice_lemma:
    #a:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a//{length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> i:nat{i < length inp / (w * blocksize)}
  -> j:nat{j < w} -> Lemma
  (requires
   (let blocksize_v = w * blocksize in
    let len = length inp in
    let nb_v = len / blocksize_v in
    (i + 1) * blocksize_v <= nb_v * blocksize_v /\
    j * blocksize + blocksize <= blocksize_v /\
    (w * i + j) * blocksize + blocksize <= len))
  (ensures
  (let blocksize_v = w * blocksize in
   let block = Seq.slice inp (i * blocksize_v) (i * blocksize_v + blocksize_v) in
   let b1 = Seq.slice block (j * blocksize) (j * blocksize + blocksize) in
   let b2 = Seq.slice inp ((w * i + j) * blocksize) ((w * i + j) * blocksize + blocksize) in
   b1 == b2))

let slice_slice_lemma #a w blocksize inp i j =
  let blocksize_v = w * blocksize in
  Seq.Properties.slice_slice inp (i * blocksize_v) (i * blocksize_v + blocksize_v) (j * blocksize) (j * blocksize + blocksize)


val repeat_blocks_multi_vec_step2:
    #a:Type0
  -> #b:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> i:nat{i < length inp / (w * blocksize)}
  -> j:nat{j < w}
  -> acc:b -> Lemma
  (let len = length inp in
   let blocksize_v = w * blocksize in
   let nb_v = len / blocksize_v in
   let nb = len / blocksize in
   len_div_bs_w w blocksize len;
   assert (nb == w * nb_v);

   let repeat_bf_s = repeat_blocks_f blocksize inp f nb in
   Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) nb_v;
   assert ((i + 1) * blocksize_v <= nb_v * blocksize_v);
   let block = Seq.slice inp (i * blocksize_v) (i * blocksize_v + blocksize_v) in
   Math.Lemmas.cancel_mul_mod w blocksize;
   let repeat_bf_s1 = repeat_blocks_f blocksize block f w in
   Math.Lemmas.lemma_mult_le_left w (i + 1) nb_v;
   repeat_bf_s1 j acc == repeat_bf_s (w * i + j) acc)

let repeat_blocks_multi_vec_step2 #a #b w blocksize inp f i j acc =
  let len = length inp in
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let nb = len / blocksize in
  len_div_bs_w w blocksize len;
  assert (nb == w * nb_v);

  Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) nb_v;
  assert ((i + 1) * blocksize_v <= nb_v * blocksize_v);

  Math.Lemmas.lemma_mult_le_right blocksize (j + 1) w;
  assert (j * blocksize + blocksize <= blocksize_v);

  assert ((w * i + j) * blocksize + blocksize <= len);
  slice_slice_lemma #a w blocksize inp i j


val repeat_blocks_multi_vec_step1:
    #a:Type0
  -> #b:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> i:nat{i < length inp / (w * blocksize)}
  -> acc:b -> Lemma
  (let len = length inp in
   let blocksize_v = w * blocksize in
   let nb_v = len / blocksize_v in
   let nb = len / blocksize in
   len_div_bs_w w blocksize len;
   assert (nb == w * nb_v);

   let repeat_bf_s = repeat_blocks_f blocksize inp f nb in
   Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) nb_v;
   assert ((i + 1) * blocksize_v <= nb_v * blocksize_v);
   let block = Seq.slice inp (i * blocksize_v) (i * blocksize_v + blocksize_v) in
   FStar.Math.Lemmas.cancel_mul_mod w blocksize;
   let repeat_bf_s1 = repeat_blocks_f blocksize block f w in
   assert (w * (i + 1) <= w * nb_v);
   let lp = Loops.repeat_right 0 w (Loops.fixed_a b) repeat_bf_s1 acc in
   let rp = Loops.repeat_right (w * i) (w * (i + 1)) (Loops.fixed_a b) repeat_bf_s acc in
   lp == rp)

let repeat_blocks_multi_vec_step1 #a #b w blocksize inp f i acc =
  let len = length inp in
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let nb = len / blocksize in
  len_div_bs_w w blocksize len;
  assert (nb == w * nb_v);

  let repeat_bf_s = repeat_blocks_f blocksize inp f nb in
  Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) nb_v;
  assert ((i + 1) * blocksize_v <= nb_v * blocksize_v);
  let block = Seq.slice inp (i * blocksize_v) (i * blocksize_v + blocksize_v) in
  FStar.Math.Lemmas.cancel_mul_mod w blocksize;
  let repeat_bf_s1 = repeat_blocks_f blocksize block f w in

  Classical.forall_intro_2 (repeat_blocks_multi_vec_step2 #a #b w blocksize inp f i);
  repeati_right_extensionality w (w * i) (w * (i + 1)) repeat_bf_s1 repeat_bf_s acc


val repeat_blocks_multi_vec_step:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> f_v:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_v:(b_vec -> b)
  -> pre:squash (forall (b_v:lseq a (w * blocksize)) (acc_v:b_vec).
      repeat_blocks_multi_vec_equiv_pre w blocksize (w * blocksize) f f_v normalize_v b_v acc_v)
  -> i:nat{i < length inp / (w * blocksize)}
  -> acc_v:b_vec -> Lemma
  (let len = length inp in
   let blocksize_v = w * blocksize in
   let nb_v = len / blocksize_v in
   let nb = len / blocksize in
   len_div_bs_w w blocksize len;
   assert (nb == w * nb_v);

   let repeat_bf_v = repeat_blocks_f blocksize_v inp f_v nb_v in
   let repeat_bf_s = repeat_blocks_f blocksize inp f nb in

   normalize_v (repeat_bf_v i acc_v) ==
   Loops.repeat_right (w * i) (w * (i + 1)) (Loops.fixed_a b) repeat_bf_s (normalize_v acc_v))

let repeat_blocks_multi_vec_step #a #b #b_vec w blocksize inp f f_v normalize_v pre i acc_v =
  let len = length inp in
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let nb = len / blocksize in
  len_div_bs_w w blocksize len;
  assert (nb == w * nb_v);

  let repeat_bf_v = repeat_blocks_f blocksize_v inp f_v nb_v in
  let repeat_bf_s = repeat_blocks_f blocksize inp f nb in

  Math.Lemmas.lemma_mult_le_right blocksize_v (i + 1) nb_v;
  assert ((i + 1) * blocksize_v <= nb_v * blocksize_v);
  let block = Seq.slice inp (i * blocksize_v) (i * blocksize_v + blocksize_v) in
  Math.Lemmas.cancel_mul_mod w blocksize;
  let repeat_bf_s1 = repeat_blocks_f blocksize block f w in
  let acc = normalize_v acc_v in

  assert (repeat_blocks_multi_vec_equiv_pre w blocksize blocksize_v f f_v normalize_v block acc_v);
  assert (normalize_v (repeat_bf_v i acc_v) == repeat_blocks_multi blocksize block f acc);
  lemma_repeat_blocks_multi blocksize block f acc;
  assert (normalize_v (repeat_bf_v i acc_v) == Loops.repeati w repeat_bf_s1 acc);
  Loops.repeati_def w repeat_bf_s1 acc;
  repeat_blocks_multi_vec_step1 #a #b w blocksize inp f i acc


let lemma_repeat_blocks_multi_vec #a #b #b_vec w blocksize inp f f_v normalize_v acc_v0 =
  let len = length inp in
  let blocksize_v = w * blocksize in
  let nb_v = len / blocksize_v in
  let nb = len / blocksize in
  len_div_bs_w w blocksize len;
  assert (nb == w * nb_v);

  let repeat_bf_v = repeat_blocks_f blocksize_v inp f_v nb_v in
  let repeat_bf_s = repeat_blocks_f blocksize inp f nb in

  calc (==) {
    normalize_v (repeat_blocks_multi blocksize_v inp f_v acc_v0);
    (==) { lemma_repeat_blocks_multi blocksize_v inp f_v acc_v0 }
    normalize_v (Loops.repeati nb_v repeat_bf_v acc_v0);
    (==) { Classical.forall_intro_2 (repeat_blocks_multi_vec_step w blocksize inp f f_v normalize_v ());
      lemma_repeati_vec w nb_v normalize_v repeat_bf_s repeat_bf_v acc_v0}
    Loops.repeati nb repeat_bf_s (normalize_v acc_v0);
    (==) { lemma_repeat_blocks_multi blocksize inp f (normalize_v acc_v0) }
    repeat_blocks_multi blocksize inp f (normalize_v acc_v0);
  }

////////////////////////
// End of proof of lemma_repeat_blocks_multi_vec
////////////////////////
