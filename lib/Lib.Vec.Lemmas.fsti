module Lib.Vec.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.Sequence.Lemmas

module Loops = Lib.LoopCombinators


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

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


let repeat_gen_blocks_multi_vec_equiv_pre
  (#inp_t:Type0)
  (w:size_pos)
  (blocksize:size_pos{w * blocksize <= max_size_t})
  (n:nat)
  (a:(i:nat{i <= w * n} -> Type))
  (a_vec:(i:nat{i <= n} -> Type))
  (f:(i:nat{i < w * n} -> lseq inp_t blocksize -> a i -> a (i + 1)))
  (f_v:(i:nat{i < n} -> lseq inp_t (w * blocksize) -> a_vec i -> a_vec (i + 1)))
  (normalize_v:(i:nat{i <= n} -> a_vec i -> a (w * i)))
  (i:nat{i < n})
  (b_v:lseq inp_t (w * blocksize))
  (acc_v:a_vec i)
  : prop
=
  Math.Lemmas.lemma_mult_le_right w (i + 1) n;
  Math.Lemmas.cancel_mul_mod w blocksize;
  Math.Lemmas.cancel_mul_div w blocksize;

  normalize_v (i + 1) (f_v i b_v acc_v) ==
  repeat_gen_blocks_multi blocksize (w * i) (w * n) w b_v a f (normalize_v i acc_v)


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
    normalize_v n (repeat_gen_blocks_multi (w * blocksize) 0 n n inp a_vec f_v acc_v0) ==
    repeat_gen_blocks_multi blocksize 0 (n * w) (n * w) inp a f (normalize_v 0 acc_v0))


let repeat_blocks_multi_vec_equiv_pre
  (#a:Type0)
  (#b:Type0)
  (#b_vec:Type0)
  (w:size_pos)
  (blocksize:size_pos{w * blocksize <= max_size_t})
  (f:(lseq a blocksize -> b -> b))
  (f_v:(lseq a (w * blocksize) -> b_vec -> b_vec))
  (normalize_v:(b_vec -> b))
  (b_v:lseq a (w * blocksize))
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
      repeat_blocks_multi_vec_equiv_pre w blocksize f f_v normalize_v b_v acc_v))
  (ensures
    normalize_v (repeat_blocks_multi #a #b_vec (w * blocksize) inp f_v acc_v0) ==
    repeat_blocks_multi #a #b blocksize inp f (normalize_v acc_v0))


let map_blocks_multi_vec_equiv_pre
  (#a:Type)
  (w:size_pos)
  (blocksize:size_pos{w * blocksize <= max_size_t})
  (n:nat)
  (f:(i:nat{i < w * n} -> lseq a blocksize -> lseq a blocksize))
  (f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize)))
  (i:nat{i < n})
  (b_v:lseq a (w * blocksize))
  (acc_v:map_blocks_a a (w * blocksize) n i)
  : prop
 =
  Math.Lemmas.cancel_mul_div w blocksize;
  Math.Lemmas.cancel_mul_mod w blocksize;

  repeat_gen_blocks_map_f #a (w * blocksize) n f_v i b_v acc_v `Seq.equal`
  map_blocks_multi_acc blocksize (w * i) (w * n) w b_v f acc_v

// It means the following
// Seq.append acc_v (f_v i b_v) ==
// map_blocks_multi_acc blocksize (w * i) (w * n) w b_v f acc_v


val lemma_map_blocks_multi_vec:
     #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> n:nat
  -> inp:seq a{length inp == blocksize * w * n}
  -> f:(i:nat{i < w * n} -> lseq a blocksize -> lseq a blocksize)
  -> f_v:(i:nat{i < n} -> lseq a (w * blocksize) -> lseq a (w * blocksize)) ->
  Lemma
  (requires
    (forall (i:nat{i < n}) (b_v:lseq a (w * blocksize)) (acc_v:map_blocks_a a (w * blocksize) n i).
      map_blocks_multi_vec_equiv_pre w blocksize n f f_v i b_v acc_v))
  (ensures
   (Math.Lemmas.cancel_mul_mod n (w * blocksize);
    //Math.Lemmas.cancel_mul_div n (w * blocksize);
    Math.Lemmas.cancel_mul_mod (w * n) blocksize;
    //Math.Lemmas.cancel_mul_div (w * n) blocksize;

    map_blocks_multi (w * blocksize) n n inp f_v ==
    map_blocks_multi blocksize (w * n) (w * n) inp f))
