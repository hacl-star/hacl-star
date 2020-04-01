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


let repeati_right_extensionality #a n lo_g hi_g f g acc0 =
  repeat_gen_right_extensionality n lo_g hi_g (Loops.fixed_a a) (Loops.fixed_a a) f g acc0


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


let repeat_gen_blocks_multi_extensionality #inp_t blocksize n inp a_f a_g f g acc0 =
  let f_rep = repeat_gen_blocks_f #inp_t blocksize n a_f inp f in
  let g_rep = repeat_gen_blocks_f #inp_t blocksize n a_g inp g in
  repeat_gen_right_extensionality n 0 n a_f a_g f_rep g_rep acc0;
  Loops.repeat_gen_def n a_f f_rep acc0;
  Loops.repeat_gen_def n a_g g_rep acc0


let repeat_gen_blocks_extensionality #inp_t #c blocksize inp n a_f a_g f g l_f l_g acc0 =
  let len = length inp in
  let rem = len % blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  Math.Lemmas.cancel_mul_mod n blocksize;

  let blocks = Seq.slice inp 0 (n * blocksize) in
  //let last = Seq.slice inp (n * blocksize) len in
  //let acc_f = repeat_gen_blocks_multi #inp_t blocksize n a_f blocks f acc0 in
  //let acc_g = repeat_gen_blocks_multi #inp_t blocksize n a_g blocks g acc0 in
  repeat_gen_blocks_multi_extensionality #inp_t blocksize n blocks a_f a_g f g acc0


let repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize inp f acc0 =
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


let repeat_blocks_is_repeat_gen_blocks #a #b #c blocksize inp f l acc0 =
  let len = length inp in
  let nb = len / blocksize in
  let rem = len % blocksize in

  let blocks = Seq.slice inp 0 (nb * blocksize) in
  Math.Lemmas.cancel_mul_div nb blocksize;
  let f_rep_b = repeat_blocks_f blocksize blocks f nb in
  let f_rep = repeat_blocks_f blocksize inp f nb in

  let aux (i:nat{i < nb}) (acc:b) : Lemma (f_rep_b i acc == f_rep i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * blocksize) (i * blocksize) (i * blocksize + blocksize) in

  Classical.forall_intro_2 aux;
  repeati_extensionality nb f_rep f_rep_b acc0;
  lemma_repeat_blocks #a #b #c blocksize inp f l acc0;
  assert (Loops.repeati nb f_rep acc0 == Loops.repeati nb f_rep_b acc0);
  Math.Lemmas.cancel_mul_mod nb blocksize;
  lemma_repeat_blocks_multi blocksize blocks f acc0;
  repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize blocks f acc0


let map_blocks_multi_is_repeat_gen_blocks_multi #a blocksize n inp f =
  let f_g = repeat_gen_blocks_map_f blocksize n f in

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


let map_blocks_is_repeat_gen #a blocksize inp f l =
  let len = length inp in
  let nb = len / blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let bs = map_blocks_multi #a blocksize nb nb blocks f in
  lemma_map_blocks #a blocksize inp f l;
  Math.Lemmas.cancel_mul_div nb blocksize;
  map_blocks_multi_is_repeat_gen_blocks_multi #a blocksize nb blocks f


#set-options "--z3rlimit 100"

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


let repeat_blocks_multi_split #a #b blocksize len0 inp f acc0 =
  let len = length inp in
  let n = len / blocksize in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n == n0 + n1);

  repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize inp f acc0;
  repeat_gen_blocks_multi_split #a blocksize len0 n (Loops.fixed_a b) inp (Loops.fixed_i f) acc0;

  let a1 = shift_a n n0 n1 (Loops.fixed_a b) in
  let f1 = shift_f blocksize n n0 n1 (Loops.fixed_a b) (Loops.fixed_i f) in
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  //assert (len % blocksize == len1 % blocksize);
  Math.Lemmas.cancel_mul_mod n blocksize;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in
  let acc1 = repeat_gen_blocks_multi blocksize n0 (Loops.fixed_a b) t0 (Loops.fixed_i f) acc0 in
  repeat_gen_blocks_multi_extensionality blocksize n1 t1 (Loops.fixed_a b) a1 (Loops.fixed_i f) f1 acc1;
  repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize t0 f acc0;
  repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize t1 f acc1


let repeat_blocks_split #a #b #c blocksize len0 inp f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  len0_div_bs blocksize len len0;
  assert (n0 + n1 == n);
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;

  let a1 = shift_a n n0 n1 (Loops.fixed_a b) in
  let f1 = shift_f blocksize n n0 n1 (Loops.fixed_a b) (Loops.fixed_i f) in
  let l1 = shift_l blocksize n n n0 n1 (Loops.fixed_a b) (Loops.fixed_i l) in

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let acc1 = repeat_gen_blocks_multi blocksize n0 (Loops.fixed_a b) t0 (Loops.fixed_i f) acc0 in

  calc (==) {
    repeat_blocks blocksize inp f l acc0;
    (==) {  repeat_blocks_is_repeat_gen_blocks blocksize inp f l acc0 }
    repeat_gen_blocks blocksize inp (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    (==) { repeat_gen_blocks_split #a #c blocksize len0 inp n (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0 }
    repeat_gen_blocks blocksize t1 a1 f1 l1 acc1;
    (==) { repeat_gen_blocks_extensionality #a #c blocksize t1 n1
             (Loops.fixed_a b) a1 (Loops.fixed_i f) f1 (Loops.fixed_i l) l1 acc1 }
    repeat_gen_blocks blocksize t1 (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc1;
    (==) { repeat_blocks_is_repeat_gen_blocks #a #b #c blocksize t1 f l acc1 }
    repeat_blocks blocksize t1 f l acc1;
    (==) { Math.Lemmas.cancel_mul_div n0 blocksize;
           repeat_blocks_multi_is_repeat_gen_blocks_multi blocksize t0 f acc0 }
    repeat_blocks blocksize t1 f l (repeat_blocks_multi blocksize t0 f acc0);
  }
