module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

// This is unnecessary because the same pragma is interleaved from the interface
#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0 \
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
