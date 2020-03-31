module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"


val repeati_extensionality:
    #a:Type0
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a -> Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures  Loops.repeati n f acc0 == Loops.repeati n g acc0)


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


val lemma_repeat_gen_vec:
    w:pos
  -> n:nat
  -> a:(i:nat{i <= n * w} -> Type)
  -> a_vec:(i:nat{i <= n} -> Type)
  -> normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i))
  -> f:(i:nat{i < n * w} -> a i -> a (i + 1))
  -> f_v:(i:nat{i < n} -> a_vec i -> a_vec (i + 1))
  -> acc_v0:a_vec 0 ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_v:a_vec i).
   (assert (w * (i + 1) <= w * n);
    normalize_v (i + 1) (f_v i acc_v) ==
    Loops.repeat_right (w * i) (w * (i + 1)) a f (normalize_v i acc_v))))
  (ensures
    normalize_v n (Loops.repeat_right 0 n a_vec f_v acc_v0) ==
    Loops.repeat_right 0 (w * n) a f (normalize_v 0 acc_v0))


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


val lemma_repeati_vec:
    #a:Type0
  -> #a_vec:Type0
  -> w:pos
  -> n:nat
  -> normalize_v:(a_vec -> a)
  -> f:(i:nat{i < n * w} -> a -> a)
  -> f_v:(i:nat{i < n} -> a_vec -> a_vec)
  -> acc_v0:a_vec ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_v:a_vec).
   (assert (w * (i + 1) <= w * n);
    normalize_v (f_v i acc_v) ==
    Loops.repeat_right (w * i) (w * (i + 1)) (Loops.fixed_a a) f (normalize_v acc_v))))
  (ensures
    normalize_v (Loops.repeati n f_v acc_v0) ==
    Loops.repeati (w * n) f (normalize_v acc_v0))


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
    let n0 = len0 / blocksize in
    let n1 = (len - len0) / blocksize in
    Math.Lemmas.cancel_mul_div n blocksize;
    assert (n == len / blocksize);
    assume (n0 + n1 == n);

    Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
    assert (len % blocksize == (len - len0) % blocksize);
    let a1 (i:nat{i <= n1}) = a (n0 + i) in
    let f1 (i:nat{i < n1}) = f (n0 + i) in

    repeat_gen_blocks_multi blocksize n a inp f acc0 ==
    repeat_gen_blocks_multi blocksize n1 a1 (Seq.slice inp len0 len) f1
      (repeat_gen_blocks_multi blocksize n0 a (Seq.slice inp 0 len0) f acc0))


val repeat_gen_blocks_split:
    #inp_t:Type0
  -> #c:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize == 0}
  -> inp:seq inp_t{len0 <= length inp}
  -> a:(i:nat{i <= length inp / blocksize} -> Type)
  -> f:(i:nat{i < length inp / blocksize} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> l:(i:nat{i == length inp / blocksize} -> len:size_nat{len == length inp % blocksize} -> lseq inp_t len -> a i -> c)
  -> acc0:a 0 ->
  Lemma
   (let len = length inp in
    let n = len / blocksize in
    let n0 = len0 / blocksize in
    let n1 = (len - len0) / blocksize in
    assume (n0 + n1 == n);

    let a1 (i:nat{i <= n1}) = a (n0 + i) in
    let f1 (i:nat{i < n1}) = f (n0 + i) in
    let l1 (i:nat{i == n1}) = l n in
    let acc : a n0 = repeat_gen_blocks_multi blocksize n0 a (Seq.slice inp 0 len0) f acc0 in

    repeat_gen_blocks blocksize inp a f l acc0 ==
    repeat_gen_blocks blocksize (Seq.slice inp len0 len) a1 f1 l1 acc)


let repeat_gen_blocks_multi_vec_equiv_pre
  (#inp_t:Type0)
  (w:size_pos)
  (blocksize:size_pos{w * blocksize <= max_size_t})
  (n:nat)
  (a:(i:nat{i <= n * w} -> Type))
  (a_vec:(i:nat{i <= n} -> Type))
  (f:(i:nat{i < n * w} -> lseq inp_t blocksize -> a i -> a (i + 1)))
  (f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1)))
  (normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i)))
  (i:nat{i < n})
  (b_v:lseq inp_t (w * blocksize))
  (acc_v:a_vec i)
  : prop
=
  Math.Lemmas.lemma_mult_le_right w (i + 1) n;
  let ai (j:nat{j <= w}) = a (i * w + j) in
  let fi (j:nat{j < w}) = f (i * w + j) in
  Math.Lemmas.cancel_mul_mod w blocksize;
  Math.Lemmas.cancel_mul_div w blocksize;
  normalize_v (i + 1) (f_v i b_v acc_v) == repeat_gen_blocks_multi blocksize w ai b_v fi (normalize_v i acc_v)


val lemma_repeat_gen_blocks_multi_vec:
    #inp_t:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> inp:seq inp_t{length inp == n * (w * blocksize)}
  -> a:(i:nat{i <= n * w} -> Type)
  -> a_vec:(i:nat{i <= n} -> Type)
  -> f:(i:nat{i < n * w} -> lseq inp_t blocksize -> a i -> a (i + 1))
  -> f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1))
  -> normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i))
  -> acc_v0:a_vec 0 -> Lemma
  (requires
    (forall (i:nat{i < n}) (b_v:lseq inp_t (w * blocksize)) (acc_v:a_vec i).
      repeat_gen_blocks_multi_vec_equiv_pre w blocksize n a a_vec f f_v normalize_v i b_v acc_v))
  (ensures
    normalize_v n (repeat_gen_blocks_multi (w * blocksize) n a_vec inp f_v acc_v0) ==
    repeat_gen_blocks_multi blocksize (n * w) a inp f (normalize_v 0 acc_v0))


let repeat_blocks_multi_vec_equiv_pre
  (#a:Type0)
  (#b:Type0)
  (#b_vec:Type0)
  (w:size_pos)
  (blocksize:size_pos)
  (blocksize_v:size_pos{blocksize_v == w * blocksize})
  (f:(lseq a blocksize -> b -> b))
  (f_v:(lseq a blocksize_v -> b_vec -> b_vec))
  (normalize_v:(b_vec -> b))
  (b_v:lseq a blocksize_v)
  (acc_v:b_vec)
  : prop
=
  Math.Lemmas.cancel_mul_mod w blocksize;
  normalize_v (f_v b_v acc_v) == repeat_blocks_multi blocksize b_v f (normalize_v acc_v)


val lemma_repeat_blocks_multi_vec:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> f_v:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_v:(b_vec -> b)
  -> acc_v0:b_vec ->
  Lemma
  (requires
    (forall (b_v:lseq a (w * blocksize)) (acc_v:b_vec).
      repeat_blocks_multi_vec_equiv_pre w blocksize (w * blocksize) f f_v normalize_v b_v acc_v))
  (ensures
    normalize_v (repeat_blocks_multi #a #b_vec (w * blocksize) inp f_v acc_v0) ==
    repeat_blocks_multi #a #b blocksize inp f (normalize_v acc_v0))
