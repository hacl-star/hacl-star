module Hacl.Spec.Poly1305.Equiv

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.IntVector

module Poly = Spec.Poly1305
module PolyVec = Hacl.Spec.Poly1305.Vec
open Hacl.Impl.Poly1305.Fields

#set-options "--z3rlimit 80 --max_fuel 1 --max_ifuel 1 --initial_ifuel 0"

let update1_aux_equiv
  (r:Poly.felem)
  (len:size_nat{len <= 16})
  (b:lbytes len)
  (acc:Poly.felem)
  : Lemma (Poly.update1 r len b acc == PolyVec.update1 r len b acc)
  =
  let e:nat = nat_from_bytes_le b in
  Math.Lemmas.pow2_le_compat 128 (8 * len);
  assert (pow2 (8 * len) <= pow2 128);
  assert_norm (pow2 128 + pow2 128 < Poly.prime);
  let n1 = PolyVec.pfadd (pow2 (8*len)) e in
  let n2 = Poly.to_felem (pow2 (8*len) + e) in
  assert (n1 == n2);
  assert (Poly.fmul (Poly.fadd n2 acc) r == PolyVec.pfmul (PolyVec.pfadd acc n1) r)  

val lemma_repeat_blocks_exact_size:
    #a:Type0
  -> #b:Type0
  -> bs:size_nat{bs > 0}
  -> inp:lseq a bs
  -> f:(lseq a bs -> b -> b)
  -> l:(len:size_nat{len == length inp % bs} -> s:lseq a len -> b -> b)
  -> init:b ->
  Lemma (repeat_blocks #a #b bs inp f l init == l 0 Seq.empty (f inp init))

let lemma_repeat_blocks_exact_size #a #b bs inp f l init = 
  lemma_repeat_blocks #a #b bs inp f l init;
  let final = repeat_blocks #a #b bs inp f l init in
  let len = bs in
  let nb = len / bs in
  let rem = len % bs in
  assert_norm (rem = 0);
  assert_norm (nb = 1);
  assert_norm (nb * bs = bs);  
  let acc = Lib.LoopCombinators.repeati nb (repeat_blocks_f bs inp f nb) init in
  Lib.LoopCombinators.unfold_repeati 1 (repeat_blocks_f bs inp f nb) init 0;
  Lib.LoopCombinators.eq_repeati0 1 (repeat_blocks_f bs inp f nb) init;
  Seq.slice_length inp;
  assert (Seq.slice inp 0 bs == inp);
  let last = Seq.slice inp (nb * bs) len in
  Seq.slice_is_empty inp len;
  assert (last == Seq.empty)

val lemma_repeat_blocks_small_size:
    #a:Type0
  -> #b:Type0
  -> bs:size_nat{bs > 0}
  -> inp:seq a
  -> f:(lseq a bs -> b -> b)
  -> l:(len:size_nat{len == length inp % bs} -> s:lseq a len -> b -> b)
  -> init:b ->
  Lemma 
    (requires Seq.length inp < bs)
    (ensures repeat_blocks #a #b bs inp f l init == l (Seq.length inp) inp init)

let lemma_repeat_blocks_small_size #a #b bs inp f l init =
  lemma_repeat_blocks #a #b bs inp f l init;
  let final = repeat_blocks #a #b bs inp f l init in
  let len = Seq.length inp in
  let nb = len / bs in
  let rem = len % bs in  
  FStar.Math.Lemmas.small_div len bs; // len / bs = 0
  FStar.Math.Lemmas.small_mod len bs; // len % bs = len
  assert_norm (nb * bs = 0);  
  let acc = Lib.LoopCombinators.repeati nb (repeat_blocks_f bs inp f nb) init in  
  Lib.LoopCombinators.eq_repeati0 0 (repeat_blocks_f bs inp f nb) init;
  assert (acc == init);
  let last = Seq.slice inp (nb * bs) len in
  Seq.slice_length inp;
  assert (last == inp)

// Running poly1305_update on one single block is equivalent to running update1
// This is only true if the block is non-empty. If it is empty, poly_update will leave acc invariant,
// while update1 would perform the computation ((1 + acc) * r) % prime
let update1_equiv 
  (r:PolyVec.elem (width M32)) 
  (len:size_nat{0 < len /\ len <= Poly.size_block}) 
  (b:lbytes len)
  (acc:PolyVec.elem (width M32))
  : Lemma (
    Poly.update1 (Seq.index r 0) len b (Seq.index acc 0) = PolyVec.poly_update b acc r)
  = 
  assert (PolyVec.poly_update b acc r == PolyVec.poly_update1 b (PolyVec.from_elem acc) (PolyVec.from_elem r));
  assert (PolyVec.from_elem acc = Seq.index acc 0);
  assert (PolyVec.from_elem r = Seq.index r 0);
  let r_f = Seq.index r 0 in
  let acc_f = Seq.index acc 0 in
  assert (PolyVec.poly_update b acc r == repeat_blocks 16 b (PolyVec.update1 r_f 16) (PolyVec.poly_update1_rem r_f) acc_f);
  lemma_repeat_blocks 16 b (PolyVec.update1 r_f 16) (PolyVec.poly_update1_rem r_f) acc_f;
  let f = PolyVec.update1 r_f 16 in
  let l = PolyVec.poly_update1_rem r_f in
  if len = 16 then (
    lemma_repeat_blocks_exact_size 16 b f l acc_f;
    update1_aux_equiv r_f len b acc_f
  ) else (
    lemma_repeat_blocks_small_size 16 b f l acc_f;
    update1_aux_equiv r_f len b acc_f
  )

let update1_rem_equiv
  (r:Poly.felem)
  (len:size_nat{len < 16})
  (b:lbytes len)
  (acc:Poly.felem)
  : Lemma (Poly.poly_update1_rem r len b acc == PolyVec.poly_update1_rem r len b acc)
  =
  if len = 0 then ()
  else update1_aux_equiv r len b acc

#set-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 1"

let poly_equiv
  (len:size_nat)
  (text:lbytes len)
  (acc:PolyVec.elem (width M32))
  (r:PolyVec.elem (width M32))
  : Lemma (Poly.poly text (Seq.index acc 0) (Seq.index r 0) == PolyVec.poly_update #1 text acc r)
  = 
  assert (PolyVec.poly_update text acc r == PolyVec.poly_update1 text (PolyVec.from_elem acc) (PolyVec.from_elem r));
  let r_f = Seq.index r 0 in
  let acc_f = Seq.index acc 0 in
  let f = Poly.update1 r_f 16 in
  let l = Poly.poly_update1_rem r_f in
  let f_v = PolyVec.update1 r_f 16 in
  let l_v = PolyVec.poly_update1_rem r_f in  
  assert (PolyVec.poly_update text acc r == repeat_blocks 16 text f_v l_v acc_f);
  assert (Poly.poly text acc_f r_f == repeat_blocks 16 text f l acc_f);
  lemma_repeat_blocks 16 text f l acc_f;
  lemma_repeat_blocks 16 text f_v l_v acc_f;
  let nb = len / 16 in
  let rem = len % 16 in
  let repeat_bf_p = repeat_blocks_f 16 text f nb in
  let repeat_bf_v = repeat_blocks_f 16 text f_v nb in  
  let acc_p = Lib.LoopCombinators.repeati nb repeat_bf_p acc_f in
  let acc_v = Lib.LoopCombinators.repeati nb repeat_bf_v acc_f in
  let aux_repeat_bf (i:nat{i < nb}) (acc:Poly.felem) : Lemma (repeat_bf_p i acc == repeat_bf_v i acc)
    = assert (repeat_bf_p i acc = repeat_blocks_f 16 text f nb i acc);
      assert ((i+1) * 16 <= nb * 16);    
      let block = Seq.slice text (i*16) (i*16+16) in
      FStar.Seq.lemma_len_slice text (i*16) (i*16+16);
      assert (repeat_bf_p i acc == f block acc);
      assert (repeat_bf_v i acc == f_v block acc);      
      update1_aux_equiv r_f 16 block acc
  in
  let rec aux (n:nat{n <= nb}) : Lemma
    (Lib.LoopCombinators.repeati n repeat_bf_p acc_f == Lib.LoopCombinators.repeati n repeat_bf_v acc_f) =
    if n = 0 then (
      Lib.LoopCombinators.eq_repeati0 nb repeat_bf_p acc_f;
      Lib.LoopCombinators.eq_repeati0 nb repeat_bf_v acc_f
    ) else (
      Lib.LoopCombinators.unfold_repeati nb repeat_bf_p acc_f (n-1);
      Lib.LoopCombinators.unfold_repeati nb repeat_bf_v acc_f (n-1);
      aux (n-1);
      let next_p = Lib.LoopCombinators.repeati (n-1) repeat_bf_p acc_f in
      let next_v = Lib.LoopCombinators.repeati (n-1) repeat_bf_v acc_f in
      assert (next_p == next_v);
      aux_repeat_bf (n-1) next_p;
      assert (repeat_bf_p (n-1) next_p == repeat_bf_v (n-1) next_v)
    )
  in aux nb;
  let last = Seq.slice text (nb * 16) len in
  FStar.Seq.lemma_len_slice text (nb * 16) len;
  FStar.Math.Lemmas.lemma_div_mod len 16;
  if rem = 0 then ()
  else update1_aux_equiv r_f rem last acc_p
  


