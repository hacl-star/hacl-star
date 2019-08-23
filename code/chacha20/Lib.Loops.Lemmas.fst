module Lib.Loops.Lemmas

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence

///
/// Equivalence of (map_blocks blocksize) and (mapblocks (w * blocksize))
///

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --z3refresh \
              --using_facts_from '-* +Prims +Lib.Loops.Lemmas +Lib.Sequence'"


val div_interval: b:pos -> n:int -> i:int -> Lemma
  (requires n * b <= i /\ i < (n + 1) * b)
  (ensures  i / b = n)

let div_interval b n i =
  Math.Lemmas.lemma_div_le (n * b) i b;
  Math.Lemmas.cancel_mul_div n b


val mod_interval_lt: b:pos -> n:int -> i:int -> j:int -> Lemma
  (requires n * b <= i /\ i < j /\ j < (n + 1) * b)
  (ensures  i % b < j % b)

let mod_interval_lt b n i j =
  div_interval b n i;
  div_interval b n j


val div_mul_lt: b:pos -> a:int -> n:int -> Lemma
  (requires a < n * b)
  (ensures  a / b < n)

let div_mul_lt b a n = ()


val mod_div_lt: b:pos -> i:int -> j:int -> Lemma
  (requires (j / b) * b <= i /\ i < j)
  (ensures  i % b < j % b)

let mod_div_lt b i j =
  mod_interval_lt b (j / b) i j


val div_mul_l: a:int -> b:int -> c:pos -> d:pos -> Lemma
  (requires a / d = b / d)
  (ensures  a / (c * d) = b / (c * d))

let div_mul_l a b c d =
  calc (==) {
    a / (c * d);
    == { }
    a / (d * c);
    == { Math.Lemmas.division_multiplication_lemma a d c }
    (a / d) / c;
    == { }
    (b / d) / c;
    == { Math.Lemmas.division_multiplication_lemma b d c }
    b / (d * c);
    == { }
    b / (c * d);
  }

(* A full block index *)
let block (len:nat) (blocksize:size_pos) = i:nat{i < len / blocksize}


(* Index of last (incomplete) block *)
let last  (len:nat) (blocksize:size_pos) = i:nat{i = len / blocksize}


(* Computes the block of the i-th element of (map_blocks blocksize input f g) *)
val get_block:
    #a:Type
  -> #len:size_nat
  -> blocksize:size_pos
  -> input:lseq a len
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> i:nat{i < (len / blocksize) * blocksize} ->
  Tot (lseq a blocksize)

let get_block #a #len blocksize input f i =
  let j: block len blocksize = i / blocksize in
  let b: lseq a blocksize = slice input (j * blocksize) ((j + 1) * blocksize) in
  f j b


(* Computes the last block of (map_blocks blocksize input f g) *)
val get_last:
    #a:Type
  -> #len:size_nat
  -> blocksize:size_pos
  -> input:lseq a len
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem) ->
  Tot (lseq a (len % blocksize))

let get_last #a #len blocksize input g =
  let rem = len % blocksize in
  let b: lseq a rem = slice input (len - rem) len in
  g (len / blocksize) rem b


(* This is a more reasonable type for Lib.Sequence.map_blocks, using lseq *)
val map_blocks:
    #a:Type
  -> #len:size_nat
  -> blocksize:size_pos
  -> inp:lseq a len
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem) ->
  Tot (lseq a len)

let map_blocks #a #len blocksize inp f g =
  map_blocks blocksize inp f g


(* An specialization of Lib.Sequence.index_map_blocks *)
val lemma_map_blocks_i:
    #a:Type
  -> #len:size_nat
  -> blocksize:size_pos
  -> input:lseq a len
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len} ->
  Lemma (
    let output = map_blocks blocksize input f g in
    let j = i % blocksize in
    if i < (len / blocksize) * blocksize
    then
      let block_i = get_block blocksize input f i in
      div_mul_lt blocksize i (len / blocksize);
      output.[i] == block_i.[j]
    else
      let block_i = get_last blocksize input g in
      mod_div_lt blocksize i len;
      output.[i] == block_i.[j]
  )

let lemma_map_blocks_i #a #len blocksize input f g i =
  index_map_blocks blocksize input f g i;
   let output = map_blocks blocksize input f g in
  if i < (len / blocksize) * blocksize then
    begin
    let block_i = get_block blocksize input f i in
    div_mul_lt blocksize i (len / blocksize);
    assert (output.[i] == block_i.[i % blocksize])
    end
  else
    begin
    let block_i = get_last blocksize input g in
    mod_div_lt blocksize i len;
    assert (output.[i] == block_i.[i % blocksize])
    end


(*
   Conditions for (map_blocks blocksize len input f g)
   to be equivalent to (map_blocks (w * blocksize) len input f_v g_v)
*)
val map_blocks_vec_equiv_pre:
    #a:Type
  -> #len:size_nat
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> input:lseq a len
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> i:nat{i < len} ->
  prop

let map_blocks_vec_equiv_pre #a #len w blocksize input f g f_v g_v i =
  let blocksize_v = w * blocksize in
  if i < (len / blocksize) * blocksize then
    begin
    if i < (len / blocksize_v) * blocksize_v then
      (get_block (w * blocksize) input f_v i).[i % blocksize_v] ==
      (get_block blocksize input f i).[i % blocksize]
    else
      begin
      mod_div_lt blocksize_v i len;
      (get_last (w * blocksize) input g_v).[i % blocksize_v] ==
      (get_block blocksize input f i).[i % blocksize]
      end
    end
  else
    begin
    div_interval blocksize (len / blocksize) i;
    div_mul_l i len w blocksize;
    mod_interval_lt blocksize_v (i / blocksize_v) i len;
    let lp = get_last (w * blocksize) input g_v in
    let rp = get_last blocksize input g in
    lp.[i % blocksize_v] == rp.[i % blocksize]
    end


val lemma_map_blocks_vec_aux:
    #a:Type
  -> #len:size_nat
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> input:lseq a len
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem)
  -> pre:squash (forall (i:nat{i < len}). map_blocks_vec_equiv_pre w blocksize input f g f_v g_v i)
  -> i:nat{i < len} ->
  Lemma (
    let s = map_blocks blocksize input f g in
    let v = map_blocks (w * blocksize) input f_v g_v in
    v.[i] == s.[i]
  )

let lemma_map_blocks_vec_aux #a #len w blocksize input f g f_v g_v pre i =
  let blocksize_v = w * blocksize in
  lemma_map_blocks_i blocksize input f g i;
  lemma_map_blocks_i blocksize_v input f_v g_v i;
  let s = map_blocks blocksize input f g in
  let v = map_blocks (w * blocksize) input f_v g_v in
  if i < (len / blocksize) * blocksize then
    begin
    div_mul_lt blocksize i (len / blocksize);
    assert (v.[i] == s.[i])
    end
  else
    begin
    div_interval blocksize (len / blocksize) i;
    div_mul_l i len w blocksize;
    mod_interval_lt blocksize_v (i / blocksize_v) i len;
    assert (v.[i] == s.[i])
    end


val lemma_map_blocks_vec:
    #a:Type
  -> #len:size_nat
  -> w:size_pos
  -> blocksize:size_pos{w * blocksize <= max_size_t}
  -> input:lseq a len
  -> f:(block len blocksize -> lseq a blocksize -> lseq a blocksize)
  -> g:(last len blocksize -> rem:size_nat{rem < blocksize} -> lseq a rem -> lseq a rem)
  -> f_v:(block len (w * blocksize) -> lseq a (w * blocksize) -> lseq a (w * blocksize))
  -> g_v:(last len (w * blocksize) -> rem:size_nat{rem < w * blocksize} -> lseq a rem -> lseq a rem) ->
  Lemma
  (requires
    forall (i:nat{i < len}). map_blocks_vec_equiv_pre w blocksize input f g f_v g_v i)
  (ensures
     map_blocks (w * blocksize) input f_v g_v `equal`
     map_blocks blocksize input f g)

let lemma_map_blocks_vec #a #len w blocksize input f g f_v g_v =
  Classical.forall_intro (lemma_map_blocks_vec_aux w blocksize input f g f_v g_v ())
