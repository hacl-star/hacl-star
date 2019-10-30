module Spec.Agile.Hash.Incremental

open Lib.LoopCombinators
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes
open FStar.Mul

let updaten (acc_t:Type0) (data_t:Type0) (blocksize:size_pos)
	    (text:seq data_t{length text % blocksize = 0})
	    (update1: (i:nat -> lseq data_t blocksize -> acc_t -> acc_t))
	    (st:acc_t & nat) : acc_t & nat = magic()
    (* let (acc,start) = st in *)
    (* let update1' (i:nat) = update1 (i + start) in *)
    (* let acc = repeati_blocks_multi blocksize text update1' acc in *)
    (* let stop = start + (length text / blocksize) in *)
    (* (acc,stop) *)

let sub_block (data_t:Type0) (blocksize:size_pos) = b:seq data_t{length b < blocksize}

let state (acc_t:Type0) (data_t:Type0) (blocksize:size_pos) =
  (acc_t & nat & sub_block data_t blocksize)

let compute_lengths (blocksize:size_pos) (len_prev:nat{len_prev < blocksize}) (len_next:nat) :
    (fst:nat{if fst > 0 then fst + len_prev = blocksize else True} &
     snd:nat{snd % blocksize = 0} &
     thd:nat{thd < blocksize}) =
    if len_prev + len_next < blocksize then (
      (|0,0,len_next|)
      )
    else if len_prev = 0 then (
      let thd = len_next % blocksize in
      let snd = (len_next / blocksize) * blocksize in
      Math.Lemmas.cancel_mul_mod (len_next / blocksize) blocksize;
      assert (snd % blocksize = 0);
      (|0,snd,thd|))
    else (
      let fst = blocksize - len_prev in
      let rem = len_next - fst in
      let thd = rem % blocksize in
      let snd = (rem / blocksize) * blocksize in
      Math.Lemmas.cancel_mul_mod (rem / blocksize) blocksize;
      assert (snd % blocksize = 0);
      (|fst,snd,thd|))

let split3 (data_t:Type0) (text:seq data_t) (fst:nat) (snd:nat) (thd:nat{fst + snd + thd <= length text}) :
    (s1:seq data_t{length s1 = fst} &
     s2:seq data_t{length s2 = snd} &
     s3:seq data_t{length s3 = thd}) =
    let f = Seq.slice text 0 fst in
    let s = Seq.slice text fst (fst + snd) in
    let t = Seq.slice text (fst + snd) (fst + snd + thd) in
    (|f,s,t|)

let update_any (acc_t:Type0) (data_t:Type0) (blocksize:size_pos)
	    (text:seq data_t)
	    (update1: (i:nat -> lseq data_t blocksize -> acc_t -> acc_t))
	    (st:state acc_t data_t blocksize) : state acc_t data_t blocksize =
    let (acc,n,pb) = st in
    let (|fst,snd,thd|) = compute_lengths blocksize (length pb) (length text) in
    let (|first,mid_blocks,last|) = split3 data_t text fst snd thd in
    let (acc,n,pb) =
      if fst = 0 then (acc,n,pb)
      else
	let first_block = Seq.append pb first in
	let acc = update1 n first_block acc in
	(acc,n+1,Seq.empty) in
    let (acc,n) = updaten acc_t data_t blocksize mid_blocks update1 (acc,n) in
    let pb = Seq.append pb last in
    (acc,n,pb)



assume val update_any_nested: acc_t:Type0 -> data_t:Type0 -> blocksize:size_pos -> text0:seq data_t -> text1:seq data_t ->
	    update1: (i:nat -> lseq data_t blocksize -> acc_t -> acc_t) -> st:state acc_t data_t blocksize ->
	    Lemma (update_any acc_t data_t blocksize text1 update1 (
		      update_any acc_t data_t blocksize text0 update1 st) ==
		   update_any acc_t data_t blocksize (Seq.append text0 text1) update1 st)

assume val update_any_updaten: acc_t:Type0 -> data_t:Type0 -> blocksize:size_pos -> text:seq data_t{length text % blocksize = 0} ->
	    update1: (i:nat -> lseq data_t blocksize -> acc_t -> acc_t) -> acc0:acc_t -> start:nat ->
	    Lemma (update_any acc_t data_t blocksize text update1 (acc0,start,Seq.empty) ==
		   (let (acc,n) = updaten acc_t data_t blocksize text update1 (acc0,start) in
		    (acc,n,Seq.empty)))


