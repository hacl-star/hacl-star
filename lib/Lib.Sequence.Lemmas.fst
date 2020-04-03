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


let rec repeat_right_extensionality n lo a_f a_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right lo (lo + n) a_f f acc0;
    Loops.eq_repeat_right lo (lo + n) a_g g acc0 end
  else begin
    Loops.unfold_repeat_right lo (lo + n) a_f f acc0 (lo + n - 1);
    Loops.unfold_repeat_right lo (lo + n) a_g g acc0 (lo + n - 1);
    repeat_right_extensionality (n - 1) lo a_f a_g f g acc0 end


let rec repeat_gen_right_extensionality n lo_g a_f a_g f g acc0 =
  if n = 0 then begin
    Loops.eq_repeat_right 0 n a_f f acc0;
    Loops.eq_repeat_right lo_g (lo_g+n) a_g g acc0 end
  else begin
    Loops.unfold_repeat_right 0 n a_f f acc0 (n-1);
    Loops.unfold_repeat_right lo_g (lo_g+n) a_g g acc0 (lo_g+n-1);
    repeat_gen_right_extensionality (n-1) lo_g a_f a_g f g acc0 end


let repeati_right_extensionality #a n lo_g f g acc0 =
  repeat_gen_right_extensionality n lo_g (Loops.fixed_a a) (Loops.fixed_a a) f g acc0


let repeat_gen_blocks_multi #inp_t blocksize mi hi n inp a f acc0 =
  Loops.repeat_right mi (mi + n) a (repeat_gen_blocks_f blocksize mi hi n inp a f) acc0


let lemma_repeat_gen_blocks_multi #inp_t blocksize mi hi n inp a f acc0 = ()


let repeat_gen_blocks #inp_t #c blocksize mi hi inp a f l acc0 =
  let len = length inp in
  let nb = len / blocksize in
  let rem = len % blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let last = Seq.slice inp (nb * blocksize) len in
  Math.Lemmas.cancel_mul_div nb blocksize;
  let acc = repeat_gen_blocks_multi #inp_t blocksize mi hi nb blocks a f acc0 in
  l (mi + nb) rem last acc


let lemma_repeat_gen_blocks #inp_t #c blocksize mi hi inp a f l acc0 = ()


let repeat_gen_blocks_multi_extensionality #inp_t blocksize mi hi_f hi_g n inp a_f a_g f g acc0 =
  let f_rep = repeat_gen_blocks_f blocksize mi hi_f n inp a_f f in
  let g_rep = repeat_gen_blocks_f blocksize mi hi_g n inp a_g g in
  repeat_right_extensionality n mi a_f a_g f_rep g_rep acc0


let repeat_gen_blocks_multi_extensionality_zero #inp_t blocksize mi hi_f hi_g n inp a_f a_g f g acc0 =
  let f_rep = repeat_gen_blocks_f blocksize mi hi_f n inp a_f f in
  let g_rep = repeat_gen_blocks_f blocksize 0 hi_g n inp a_g g in
  repeat_gen_right_extensionality n mi a_g a_f g_rep f_rep acc0


let len0_div_bs blocksize len len0 =
  let k = len0 / blocksize in
  calc (==) {
    k + (len - len0) / blocksize;
    == { Math.Lemmas.lemma_div_exact len0 blocksize }
    k + (len - k * blocksize) / blocksize;
    == { Math.Lemmas.division_sub_lemma len blocksize k }
    k + len / blocksize - k;
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
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{mi <= i /\ i < mi + len0 / blocksize /\ i < hi} // i < hi is needed to type-check the definition
  -> acc:a i ->
  Lemma
   (let len = length inp in
    let n0 = len0 / blocksize in
    Math.Lemmas.cancel_mul_div n blocksize;
    len0_div_bs blocksize len len0;

    let t0 = Seq.slice inp 0 len0 in
    let repeat_bf_s0 = repeat_gen_blocks_f blocksize mi hi n0 t0 a f in
    let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

    repeat_bf_s0 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s0 #inp_t blocksize len0 mi hi n inp a f i acc =
  let len = length inp in
  let n0 = len0 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n == n0 + (len - len0) / blocksize);

  let t0 = Seq.slice inp 0 len0 in
  let repeat_bf_s0 = repeat_gen_blocks_f blocksize mi hi n0 t0 a f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

  let i_b = i - mi in
  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n;
  let block = Seq.slice inp (i_b * blocksize) (i_b * blocksize + blocksize) in
  assert (repeat_bf_t i acc == f i block acc);

  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n0;
  Seq.slice_slice inp 0 len0 (i_b * blocksize) (i_b * blocksize + blocksize);
  assert (repeat_bf_s0 i acc == f i block acc)


val aux_repeat_bf_s1:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> mi:nat
  -> hi:nat
  -> n:nat{mi + n <= hi}
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> a:(i:nat{i <= hi} -> Type)
  -> f:(i:nat{i < hi} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> i:nat{mi + len0 / blocksize <= i /\ i < mi + n}
  -> acc:a i ->
  Lemma
   (let len = length inp in
    let len1 = len - len0 in
    let n0 = len0 / blocksize in
    let n1 = len1 / blocksize in
    Math.Lemmas.cancel_mul_div n blocksize;
    len0_div_bs blocksize len len0;
    //assert (n == n0 + n1);

    let t1 = Seq.slice inp len0 len in
    Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
    //assert (len % blocksize == len1 % blocksize);
    Math.Lemmas.cancel_mul_mod n blocksize;

    let repeat_bf_s1 = repeat_gen_blocks_f blocksize (mi + n0) hi n1 t1 a f in
    let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

    repeat_bf_s1 i acc == repeat_bf_t i acc)

let aux_repeat_bf_s1 #inp_t blocksize len0 mi hi n inp a f i acc =
  let len = length inp in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n == n0 + n1);

  let t1 = Seq.slice inp len0 len in
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  //assert (len % blocksize == len1 % blocksize);
  Math.Lemmas.cancel_mul_mod n blocksize;

  let repeat_bf_s1 = repeat_gen_blocks_f blocksize (mi + n0) hi n1 t1 a f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

  let i_b = i - mi in
  Math.Lemmas.lemma_mult_le_right blocksize (i_b + 1) n;
  let block = Seq.slice inp (i_b * blocksize) (i_b * blocksize + blocksize) in
  assert (repeat_bf_t i acc == f i block acc);

  let i_b1 = i - mi - n0 in

  calc (<=) {
    i_b1 * blocksize + blocksize;
    (<=) { Math.Lemmas.lemma_mult_le_right blocksize (i_b1 + 1) n1 }
    n1 * blocksize;
    (==) { Math.Lemmas.div_exact_r len1 blocksize }
    len1;
    };

  calc (==) {
    len0 + i_b1 * blocksize;
    (==) { Math.Lemmas.div_exact_r len0 blocksize }
    n0 * blocksize + i_b1 * blocksize;
    (==) { Math.Lemmas.distributivity_add_left n0 i_b1 blocksize }
    (n0 + i_b1) * blocksize;
    };

  Seq.slice_slice inp len0 len (i_b1 * blocksize) (i_b1 * blocksize + blocksize);
  assert (repeat_bf_s1 i acc == f i block acc)


let repeat_gen_blocks_multi_split #inp_t blocksize len0 mi hi n inp a f acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  Math.Lemmas.cancel_mul_div n blocksize;
  len0_div_bs blocksize len len0;
  //assert (n0 + n1 == n);

  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  //assert (len % blocksize == len1 % blocksize);
  Math.Lemmas.cancel_mul_mod n blocksize;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let repeat_bf_s0 = repeat_gen_blocks_f blocksize mi hi n0 t0 a f in
  let repeat_bf_s1 = repeat_gen_blocks_f blocksize (mi + n0) hi n1 t1 a f in
  let repeat_bf_t  = repeat_gen_blocks_f blocksize mi hi n inp a f in

  let acc1 : a (mi + n0) = repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0 in
  //let acc2 = repeat_gen_blocks_multi blocksize (mi + n0) hi n1 t1 a f acc1 in

  calc (==) {
    repeat_gen_blocks_multi blocksize mi hi n0 t0 a f acc0;
    (==) { }
    Loops.repeat_right mi (mi + n0) a repeat_bf_s0 acc0;
    (==) { Classical.forall_intro_2 (aux_repeat_bf_s0 #inp_t blocksize len0 mi hi n inp a f);
           repeat_right_extensionality n0 mi a a repeat_bf_s0 repeat_bf_t acc0 }
    Loops.repeat_right mi (mi + n0) a repeat_bf_t acc0;
    };

  calc (==) {
    repeat_gen_blocks_multi blocksize (mi + n0) hi n1 t1 a f acc1;
    (==) { }
    Loops.repeat_right (mi + n0) (mi + n) a repeat_bf_s1 acc1;
    (==) { Classical.forall_intro_2 (aux_repeat_bf_s1 #inp_t blocksize len0 mi hi n inp a f);
           repeat_right_extensionality n1 (mi + n0) a a repeat_bf_s1 repeat_bf_t acc1 }
    Loops.repeat_right (mi + n0) (mi + n) a repeat_bf_t acc1;
    (==) { Loops.repeat_right_plus mi (mi + n0) (mi + n) a repeat_bf_t acc0 }
    Loops.repeat_right mi (mi + n) a repeat_bf_t acc0;
    (==) { }
    repeat_gen_blocks_multi blocksize mi hi n inp a f acc0;
  }

////////////////////////
// End of proof of repeat_gen_blocks_multi_split lemma
////////////////////////

(*
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
    let acc1 : a n0 = repeat_gen_blocks_multi blocksize n0 t0 a f acc0 in
    repeat_gen_blocks_multi blocksize n blocks a f acc0 ==
    repeat_gen_blocks_multi blocksize n1 t1 a1 f1 acc1)

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
  repeat_gen_blocks_multi_split blocksize len0 n blocks a f acc0
*)

let repeat_gen_blocks_split #inp_t #c blocksize len0 hi mi inp a f l acc0 = admit()
  // let len = length inp in
  // let len1 = len - len0 in
  // let n = len / blocksize in
  // let n0 = len0 / blocksize in
  // let n1 = len1 / blocksize in
  // len0_div_bs blocksize len len0;
  // assert (n0 + n1 == n);

  // let a1 = shift_a n n0 n1 a in
  // let f1 = shift_f blocksize n n0 n1 a f in
  // let l1 = shift_l blocksize max n n0 n1 a l in

  // let t0 = Seq.slice inp 0 len0 in
  // let t1 = Seq.slice inp len0 len in

  // let acc : a n0 = repeat_gen_blocks_multi blocksize n0 t0 a f acc0 in
  // let blocks1 = Seq.slice t1 0 (n1 * blocksize) in
  // Math.Lemmas.cancel_mul_mod n1 blocksize;
  // let acc1 = repeat_gen_blocks_multi #inp_t blocksize n1 blocks1 a1 f1 acc in
  // let last1 = Seq.slice t1 (n1 * blocksize) len1 in
  // let last = Seq.slice inp (n * blocksize) len in

  // calc (==) {
  //   len0 + n1 * blocksize;
  //   (==) { }
  //   len0 + (n - n0) * blocksize;
  //   (==) { Math.Lemmas.distributivity_sub_left n n0 blocksize }
  //   len0 + n * blocksize - n0 * blocksize;
  //   (==) { Math.Lemmas.div_exact_r len0 blocksize }
  //   n * blocksize;
  // };

  // calc (==) {
  //   repeat_gen_blocks blocksize t1 a1 f1 l1 acc;
  //   (==) { }
  //   l n (len1 % blocksize) last1 acc1;
  //   (==) { Math.Lemmas.lemma_mod_sub_distr len len0 blocksize }
  //   l n (len % blocksize) last1 acc1;
  //   (==) { Seq.slice_slice inp len0 len (n1 * blocksize) len1 }
  //   l n (len % blocksize) last acc1;
  //   (==) { repeat_gen_multi_blocks_split_slice #inp_t blocksize len0 inp a f acc0 }
  //   repeat_gen_blocks blocksize inp a f l acc0;
  //   }

////////////////////////
// Start of repeat_blocks-related properties
////////////////////////

let repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize inp f acc0 =
  let len = length inp in
  let n = len / blocksize in
  Math.Lemmas.div_exact_r len blocksize;

  let f_rep = repeat_blocks_f blocksize inp f n in
  let f_gen = repeat_gen_blocks_f blocksize 0 n n inp (Loops.fixed_a b) (Loops.fixed_i f) in

  let aux (i:nat{i < n}) (acc:b) : Lemma (f_rep i acc == f_gen i acc) = () in

  calc (==) {
    repeat_blocks_multi #a #b blocksize inp f acc0;
    (==) { lemma_repeat_blocks_multi #a #b blocksize inp f acc0 }
    Loops.repeati n f_rep acc0;
    (==) { Loops.repeati_def n (repeat_blocks_f blocksize inp f n) acc0 }
    Loops.repeat_right 0 n (Loops.fixed_a b) f_rep acc0;
    (==) { Classical.forall_intro_2 aux;
           repeat_gen_right_extensionality n 0 (Loops.fixed_a b) (Loops.fixed_a b) f_rep f_gen acc0 }
    Loops.repeat_right 0 n (Loops.fixed_a b) f_gen acc0;
    }


let repeat_blocks_is_repeat_gen_blocks #a #b #c blocksize inp f l acc0 =
  let len = length inp in
  let nb = len / blocksize in
  //let rem = len % blocksize in

  let blocks = Seq.slice inp 0 (nb * blocksize) in
  Math.Lemmas.cancel_mul_div nb blocksize;
  Math.Lemmas.cancel_mul_mod nb blocksize;

  let f_rep_b = repeat_blocks_f blocksize blocks f nb in
  let f_rep = repeat_blocks_f blocksize inp f nb in

  let aux (i:nat{i < nb}) (acc:b) : Lemma (f_rep_b i acc == f_rep i acc) =
    Math.Lemmas.lemma_mult_le_right blocksize (i + 1) nb;
    Seq.Properties.slice_slice inp 0 (nb * blocksize) (i * blocksize) (i * blocksize + blocksize) in

  lemma_repeat_blocks #a #b #c blocksize inp f l acc0;
  calc (==) {
    Loops.repeati nb f_rep acc0;
    (==) { Classical.forall_intro_2 aux; repeati_extensionality nb f_rep f_rep_b acc0 }
    Loops.repeati nb f_rep_b acc0;
    (==) { lemma_repeat_blocks_multi blocksize blocks f acc0 }
    repeat_blocks_multi blocksize blocks f acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize blocks f acc0 }
    repeat_gen_blocks_multi blocksize 0 nb nb blocks (Loops.fixed_a b) (Loops.fixed_i f) acc0;
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
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
  //assert (len % blocksize == len1 % blocksize);
  Math.Lemmas.cancel_mul_mod n blocksize;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in
  let acc1 = repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0 in

  calc (==) {
    repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_gen_blocks_multi_extensionality blocksize 0 n n0 n0 t0
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) acc0 }
    repeat_gen_blocks_multi blocksize 0 n0 n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize t0 f acc0 }
    repeat_blocks_multi blocksize t0 f acc0;
    };

  calc (==) {
    repeat_blocks_multi blocksize inp f acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize inp f acc0 }
    repeat_gen_blocks_multi blocksize 0 n n inp (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_gen_blocks_multi_split #a blocksize len0 0 n n inp (Loops.fixed_a b) (Loops.fixed_i f) acc0 }
    repeat_gen_blocks_multi blocksize n0 n n1 t1 (Loops.fixed_a b) (Loops.fixed_i f) acc1;
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize n0 n n1 n1 t1
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) acc1 }
    repeat_gen_blocks_multi blocksize 0 n1 n1 t1 (Loops.fixed_a b) (Loops.fixed_i f) acc1;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize t1 f acc1 }
    repeat_blocks_multi blocksize t1 f acc1;
    }


let repeat_blocks_split #a #b #c blocksize len0 inp f l acc0 =
  let len = length inp in
  let len1 = len - len0 in
  let n = len / blocksize in
  let n0 = len0 / blocksize in
  let n1 = len1 / blocksize in
  len0_div_bs blocksize len len0;
  assert (n0 + n1 == n);
  Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;

  let t0 = Seq.slice inp 0 len0 in
  let t1 = Seq.slice inp len0 len in

  let acc1 = repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0 in
  let blocks = Seq.slice t1 0 (n1 * blocksize) in

  calc (==) {
    repeat_gen_blocks_multi blocksize 0 n n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_gen_blocks_multi_extensionality blocksize 0 n n0 n0 t0
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i f) acc0 }
    repeat_gen_blocks_multi blocksize 0 n0 n0 t0 (Loops.fixed_a b) (Loops.fixed_i f) acc0;
    (==) { repeat_blocks_multi_is_repeat_gen_blocks_multi #a #b blocksize t0 f acc0 }
    repeat_blocks_multi blocksize t0 f acc0;
    };

  calc (==) {
    repeat_blocks blocksize inp f l acc0;
    (==) {  repeat_blocks_is_repeat_gen_blocks blocksize inp f l acc0 }
    repeat_gen_blocks blocksize 0 n inp (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0;
    (==) { repeat_gen_blocks_split #a #c blocksize len0 n 0 inp (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc0 }
    repeat_gen_blocks blocksize n0 n t1 (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc1;
    (==) { repeat_gen_blocks_multi_extensionality_zero blocksize n0 n n1 n1 blocks
            (Loops.fixed_a b) (Loops.fixed_a b) (Loops.fixed_i f)  (Loops.fixed_i f) acc1 }
    repeat_gen_blocks blocksize 0 n1 t1 (Loops.fixed_a b) (Loops.fixed_i f) (Loops.fixed_i l) acc1;
    (==) { repeat_blocks_is_repeat_gen_blocks #a #b #c blocksize t1 f l acc1 }
    repeat_blocks blocksize t1 f l acc1;
    }

////////////////////////
// End of repeat_blocks-related properties
////////////////////////

let map_blocks_multi_acc #a blocksize mi hi n inp f acc0 =
  repeat_gen_blocks_multi #a blocksize mi hi n inp
    (map_blocks_a a blocksize hi)
    (repeat_gen_blocks_map_f blocksize hi f) acc0


let map_blocks_acc #a blocksize mi hi inp f l acc0 =
  repeat_gen_blocks #a blocksize mi hi inp
    (map_blocks_a a blocksize hi)
    (repeat_gen_blocks_map_f blocksize hi f)
    (repeat_gen_blocks_map_l blocksize mi hi (length inp) l) acc0


let map_blocks_multi_acc_is_repeat_gen_blocks_multi #a blocksize mi hi n inp f acc0 = ()

let map_blocks_acc_is_repeat_gen #a blocksize mi hi inp f l acc0 = ()


let map_blocks_multi_is_map_blocks_multi_acc #a blocksize n inp f =
  let f_g = repeat_gen_blocks_map_f blocksize n f in

  let a_f = map_blocks_a a blocksize n in
  let f_gen = repeat_gen_blocks_f blocksize 0 n n inp a_f f_g in
  let f_map = map_blocks_f #a blocksize n inp f in
  let acc0 : a_f 0 = Seq.empty #a in

  let aux (i:nat{i < n}) (acc:a_f i) : Lemma (f_map i acc == f_gen i acc) = () in

  calc (==) {
    map_blocks_multi #a blocksize n n inp f;
    (==) { lemma_map_blocks_multi #a blocksize n n inp f }
    Loops.repeat_gen n a_f f_map acc0;
    (==) { Loops.repeat_gen_def n a_f f_map acc0 }
    Loops.repeat_right 0 n a_f f_map acc0;
    (==) { Classical.forall_intro_2 aux;
           repeat_gen_right_extensionality n 0 a_f a_f f_map f_gen acc0 }
    Loops.repeat_right 0 n a_f f_gen acc0;
    (==) { }
    repeat_gen_blocks_multi #a blocksize 0 n n inp a_f f_g acc0;
    }


let map_blocks_is_map_blocks_acc #a blocksize inp f l =
  let len = length inp in
  let nb = len / blocksize in
  let blocks = Seq.slice inp 0 (nb * blocksize) in
  let bs = map_blocks_multi #a blocksize nb nb blocks f in
  lemma_map_blocks #a blocksize inp f l;
  Math.Lemmas.cancel_mul_div nb blocksize;
  map_blocks_multi_is_map_blocks_multi_acc #a blocksize nb blocks f
