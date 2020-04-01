module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val repeati_extensionality:
    #a:Type0
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a -> Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures  Loops.repeati n f acc0 == Loops.repeati n g acc0)


// Loops.repeat_gen n a_f f acc0 ==
// Loops.repeat_right lo_g (lo_g + n) a_g g acc0)
val repeat_gen_right_extensionality:
    n:nat
  -> lo_g:nat
  -> hi_g:nat{lo_g + n <= hi_g}
  -> a_f:(i:nat{i <= n} -> Type)
  -> a_g:(i:nat{lo_g <= i /\ i <= hi_g} -> Type)
  -> f:(i:nat{i < n} -> a_f i -> a_f (i + 1))
  -> g:(i:nat{lo_g <= i /\ i < hi_g} -> a_g i -> a_g (i + 1))
  -> acc0:a_f 0 -> Lemma
  (requires
    (forall (i:nat{i <= n}). a_f i == a_g (lo_g + i)) /\
    (forall (i:nat{i < n}) (acc:a_f i). f i acc == g (lo_g + i) acc))
  (ensures
    Loops.repeat_right 0 n a_f f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) a_g g acc0)


// Loops.repeati n a f acc0 ==
// Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0
val repeati_right_extensionality:
    #a:Type
  -> n:nat
  -> lo_g:nat
  -> hi_g:nat{lo_g + n <= hi_g}
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{lo_g <= i /\ i < hi_g} -> a -> a)
  -> acc0:a -> Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (lo_g + i) acc))
  (ensures
    Loops.repeat_right 0 n (Loops.fixed_a a) f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0)


val repeat_gen_blocks_multi:
    #inp_t:Type0
  -> blocksize:size_pos
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> inp:seq inp_t{length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a 0 ->
  a n


val repeat_gen_blocks:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> inp:seq inp_t
  -> a:(i:nat{i <= length inp / blocksize} -> Type)
  -> f:(i:nat{i < length inp / blocksize} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i == length inp / blocksize} -> len:size_nat{len == length inp % blocksize} -> lseq inp_t len -> a i -> c)
  -> acc0:a 0 ->
  c


val repeat_gen_blocks_multi_extensionality:
    #inp_t:Type0
  -> blocksize:size_pos
  -> n:nat
  -> inp:seq inp_t{length inp == n * blocksize}
  -> a_f:(i:nat{i <= n} -> Type)
  -> a_g:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < n} -> lseq inp_t blocksize -> a_f i -> a_f (i + 1))
  -> g:(i:nat{i < n} -> lseq inp_t blocksize -> a_g i -> a_g (i + 1))
  -> acc0:a_f 0 -> Lemma
  (requires
    (forall (i:nat{i <= n}). a_f i == a_g i) /\
    (forall (i:nat{i < n}) (block:lseq inp_t blocksize) (acc:a_f i). f i block acc == g i block acc))
  (ensures
    repeat_gen_blocks_multi #inp_t blocksize n a_f inp f acc0 ==
    repeat_gen_blocks_multi #inp_t blocksize n a_g inp g acc0)


val repeat_blocks_multi_is_repeat_gen_blocks_multi:
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


val repeat_blocks_is_repeat_gen_blocks:
    #a:Type0
  -> #b:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> c)
  -> acc0:b -> Lemma
  (repeat_blocks #a #b #c blocksize inp f l acc0 ==
   repeat_gen_blocks #a #c blocksize inp (Loops.fixed_a b)
     (Loops.fixed_i f) (Loops.fixed_i l) acc0)


let repeat_gen_blocks_map_f
  (#a:Type0)
  (blocksize:size_pos)
  (n:nat)
  (f:(i:nat{i < n} -> lseq a blocksize -> lseq a blocksize))
  (i:nat{i < n})
  (block:lseq a blocksize)
  (acc:map_blocks_a a blocksize n i) : map_blocks_a a blocksize n (i + 1)
 =
   Seq.append acc (f i block)


val map_blocks_multi_is_repeat_gen_blocks_multi:
    #a:Type0
  -> blocksize:size_pos
  -> n:nat
  -> inp:seq a{length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq a blocksize -> lseq a blocksize) -> Lemma
  (map_blocks_multi #a blocksize n n inp f ==
   repeat_gen_blocks_multi #a blocksize n
     (map_blocks_a a blocksize n) inp
     (repeat_gen_blocks_map_f blocksize n f)
     Seq.empty)


let repeat_gen_blocks_map_l
  (#a:Type0)
  (blocksize:size_pos)
  (len:nat)
  (l:(i:nat{i == len / blocksize} -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (i:nat{i == len / blocksize})
  (rem:nat{rem == len % blocksize})
  (block_l:lseq a rem)
  (acc:map_blocks_a a blocksize (len / blocksize) i) : s:seq a{length s == len }
 =
   if rem > 0 then Seq.append acc (l (len / blocksize) rem block_l) else acc


val map_blocks_is_repeat_gen:
    #a:Type0
  -> blocksize:size_pos
  -> inp:seq a
  -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> lseq a blocksize)
  -> l:(i:nat{i == length inp / blocksize} -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma
  (let nb = length inp / blocksize in

   map_blocks #a blocksize inp f l ==
   repeat_gen_blocks #a blocksize inp
     (map_blocks_a a blocksize nb)
     (repeat_gen_blocks_map_f blocksize nb f)
     (repeat_gen_blocks_map_l blocksize (length inp) l)
     Seq.empty)


val len0_div_bs: blocksize:pos -> len:nat -> len0:nat -> Lemma
  (requires len0 <= len /\ len0 % blocksize == 0)
  (ensures  len0 / blocksize + (len - len0) / blocksize == len / blocksize)


let shift_a (n:nat) (n0:nat) (n1:nat{n = n0 + n1}) (a:(i:nat{i <= n} -> Type)) (i:nat{i <= n1}) = a (n0 + i)

let shift_f (#inp_t:Type0) (blocksize:size_pos) (n:nat) (n0:nat) (n1:nat{n = n0 + n1}) (a:(i:nat{i <= n} -> Type))
  (f:(i:nat{i < n} -> lseq inp_t blocksize -> a i -> a (i + 1))) (i:nat{i < n1}) = f (n0 + i)

let shift_l (#inp_t:Type0) (#c:Type0) (blocksize:size_pos) (max:nat) (n:nat{n <= max}) (n0:nat) (n1:nat{n = n0 + n1})
  (a:(i:nat{i <= max} -> Type)) (l:(i:nat{i <= max} -> len:size_nat{len < blocksize} -> lseq inp_t len -> a i -> c)) (i:nat{i == n1}) = l n


val repeat_gen_blocks_multi_split:
    #inp_t:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> n:nat
  -> a:(i:nat{i <= n} -> Type)
  -> inp:seq inp_t{len0 <= length inp /\ length inp == n * blocksize}
  -> f:(i:nat{i < n} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> acc0:a 0 ->
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
    Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
    //assert (len % blocksize == len1 % blocksize);
    Math.Lemmas.cancel_mul_mod n blocksize;

    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    repeat_gen_blocks_multi blocksize n a inp f acc0 ==
    repeat_gen_blocks_multi blocksize n1 a1 t1 f1
      (repeat_gen_blocks_multi blocksize n0 a t0 f acc0))


val repeat_gen_blocks_split:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> inp:seq inp_t{len0 <= length inp}
  -> max:nat{length inp / blocksize <= max}
  -> a:(i:nat{i <= max} -> Type)
  -> f:(i:nat{i < max} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i <= max} -> len:size_nat{len < blocksize} -> lseq inp_t len -> a i -> c)
  -> acc0:a 0 ->
  Lemma
   (let len = length inp in
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

    repeat_gen_blocks blocksize inp a f l acc0 ==
    repeat_gen_blocks blocksize t1 a1 f1 l1 acc)


val repeat_blocks_multi_split:
     #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    Math.Lemmas.lemma_mod_sub_distr len len0 blocksize;
    //assert (len % blocksize == (len - len0) % blocksize);
    repeat_blocks_multi blocksize inp f acc0 ==
    repeat_blocks_multi blocksize (Seq.slice inp len0 len) f
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))
