module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0 \
              --using_facts_from '-* +Prims +Lib.Sequence.Lemmas +Lib.Sequence'"


///
/// Equivalence of (map_blocks blocksize) and (mapblocks (w * blocksize))
///

(*
   Conditions for (map_blocks blocksize len input f g)
   to be equivalent to (map_blocks (w * blocksize) len input f_v g_v)
*)
let map_blocks_vec_equiv_pre
  (#a:Type)
  (w:size_pos)
  (blocksize:size_pos{w * blocksize <= max_size_t})
  (inp:seq a)
  (f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize))
  (g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem))
  (f_v:(block (length inp) (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize)))
  (g_v:(last (length inp) (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem))
  (i:nat{i < length inp})
  : prop
=
  let len = length inp in
  let blocksize_v = w * blocksize in
  if i < (len / blocksize) * blocksize then
    begin
    if i < (len / blocksize_v) * blocksize_v then
      (get_block (w * blocksize) inp f_v i).[i % blocksize_v] ==
      (get_block blocksize inp f i).[i % blocksize]
    else
      begin
      (get_last (w * blocksize) inp g_v i).[i % blocksize_v] ==
      (get_block blocksize inp f i).[i % blocksize]
      end
    end
  else
    begin
    div_interval blocksize (len / blocksize) i;
    div_mul_l i len w blocksize;
    mod_interval_lt blocksize_v (i / blocksize_v) i len;
    (get_last (w * blocksize) inp g_v i).[i % blocksize_v] ==
    (get_last blocksize inp g i).[i % blocksize]
    end


val lemma_map_blocks_vec:
    #a:Type
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a
  -> f:(block (length inp) blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last (length inp) blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block (length inp) (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last (length inp) (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma
  (requires
    forall (i:nat{i < length inp}). map_blocks_vec_equiv_pre w blocksize inp f g f_v g_v i)
  (ensures
     map_blocks (w * blocksize) inp f_v g_v `Seq.equal`
     map_blocks blocksize inp f g)


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val repeati_extensionality:
    #a:Type0
  -> n:nat
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{i < n} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g i acc))
  (ensures  (Loops.repeati n f acc0 == Loops.repeati n g acc0))


val repeati_right_extensionality:
    #a:Type
  -> n:nat
  -> lo_g:nat
  -> hi_g:nat{lo_g + n <= hi_g}
  -> f:(i:nat{i < n} -> a -> a)
  -> g:(i:nat{lo_g <= i /\ i < hi_g} -> a -> a)
  -> acc0:a ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc:a). f i acc == g (lo_g + i) acc))
  (ensures (Loops.repeat_right 0 n (Loops.fixed_a a) f acc0 ==
    Loops.repeat_right lo_g (lo_g + n) (Loops.fixed_a a) g acc0))


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
    FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
    assert (len % blocksize == (len - len0) % blocksize);
    repeat_blocks_multi blocksize inp f acc0 ==
    repeat_blocks_multi blocksize (Seq.slice inp len0 len) f
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))


val repeat_blocks_split:
     #a:Type0
  -> #b:Type0
  -> blocksize:size_pos
  -> len0:nat{len0 % blocksize = 0}
  -> inp:seq a{len0 <= length inp}
  -> f:(lseq a blocksize -> b -> b)
  -> l:(len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> b)
  -> acc0:b ->
  Lemma
   (let len = length inp in
    FStar.Math.Lemmas.modulo_addition_lemma len blocksize (- len0 / blocksize);
    assert (len % blocksize == (len - len0) % blocksize);
    repeat_blocks blocksize inp f l acc0 ==
    repeat_blocks blocksize (Seq.slice inp len0 len) f l
      (repeat_blocks_multi blocksize (Seq.slice inp 0 len0) f acc0))

noextract
let lanes = w:size_pos{w == 1 \/ w == 2 \/ w == 4}


noextract
let repeat_w (#a:Type0) (w:lanes) (n:nat) (f:(i:nat{i < w * n} -> a -> a)) (i:nat{i < n}) (acc:a) : Tot a =
  match w with
  | 1 -> f i acc
  | 2 -> f (2*i+1) (f (2*i) acc)
  | 4 -> f (4*i+3) (f (4*i+2) (f (4*i+1) (f (4*i) acc)))


val unfold_repeatw:
    #a:Type0
  -> w:lanes
  -> n:pos
  -> f:(i:nat{i < w * n} -> a -> a)
  -> acc0:a ->
  Lemma (Loops.repeati (w*n) f acc0 == repeat_w w n f (n-1) (Loops.repeati (w*(n-1)) f acc0))


val lemma_repeati_vec:
    #a:Type0
  -> #a_vec:Type0
  -> w:lanes
  -> n:nat
  -> normalize_n:(a_vec -> a)
  -> f:(i:nat{i < n * w} -> a -> a)
  -> f_vec:(i:nat{i < n} -> a_vec -> a_vec)
  -> acc0_vec:a_vec ->
  Lemma
  (requires (forall (i:nat{i < n}) (acc_vec:a_vec). normalize_n (f_vec i acc_vec) == repeat_w w n f i (normalize_n acc_vec)))
  (ensures  (normalize_n (Loops.repeati n f_vec acc0_vec) == Loops.repeati (w * n) f (normalize_n acc0_vec)))


private
val lemma_aux1: w:pos -> blocksize:pos -> len:pos ->
  Lemma
  (requires (w * blocksize <= len /\ len % (w * blocksize) = 0 /\ len % blocksize = 0))
  (ensures  ((len - w * blocksize) / blocksize == w * ((len - w * blocksize) / (w * blocksize))))


#set-options "--initial_ifuel 1 --max_ifuel 1"

val lemma_repeat_blocks_multi_vec:
    #a:Type0
  -> #b:Type0
  -> #b_vec:Type0
  -> w:lanes
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> inp:seq a{w * blocksize <= length inp /\ length inp % (w * blocksize) = 0 /\ length inp % blocksize = 0}
  -> f:(lseq a blocksize -> b -> b)
  -> f_vec:(lseq a (w * blocksize) -> b_vec -> b_vec)
  -> normalize_n:(b_vec -> b)
  -> load_acc:(lseq a (w * blocksize) -> b -> b_vec)
  -> acc0:b ->
  Lemma
  (requires
   (let len = length inp in
    let len0 = w * blocksize in
    let len1 = len - len0 in
    FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
    assert (len % len0 == len1 % len0);
    let t0 = Seq.slice inp 0 len0 in
    let t1 = Seq.slice inp len0 len in

    let nb_vec = len1 / (w * blocksize) in
    let nb = len1 / blocksize in
    lemma_aux1 w blocksize len;
    assert (nb == w * nb_vec);
    let repeat_bf_vec = repeat_blocks_f (w * blocksize) t1 f_vec nb_vec in
    let repeat_bf_t0 = repeat_blocks_f blocksize t0 f w in
    let repeat_bf_t1 = repeat_blocks_f blocksize t1 f nb in

    normalize_n (load_acc t0 acc0) == repeat_w #b w 1 repeat_bf_t0 0 acc0 /\
    (forall (i:nat{i < nb_vec}) (acc_vec:b_vec).
      normalize_n (repeat_bf_vec i acc_vec) == repeat_w #b w nb_vec repeat_bf_t1 i (normalize_n acc_vec))))
  (ensures
   (let len = length inp in
    let len0 = w * blocksize in
    FStar.Math.Lemmas.modulo_addition_lemma len len0 (- 1);
    assert (len % len0 == (len - len0) % len0);

    let acc_vec = load_acc (Seq.slice inp 0 len0) acc0 in
    normalize_n (repeat_blocks_multi #a #b_vec (w * blocksize) (Seq.slice inp len0 len) f_vec acc_vec) ==
    repeat_blocks_multi #a #b blocksize inp f acc0))
