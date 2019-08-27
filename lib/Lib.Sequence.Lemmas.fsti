module Lib.Sequence.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence


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
