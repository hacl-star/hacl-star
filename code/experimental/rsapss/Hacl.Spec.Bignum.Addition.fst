module Hacl.Spec.Bignum.Addition

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.LoopCombinators

open Hacl.Spec.Bignum
open Hacl.Spec.Bignum.Base


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let generate_elem_a (t:Type0) (a:Type0) (max:nat) (i:nat{i <= max}) = a & s:seq t{length s == i}

val generate_elem_f:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> f:(i:nat{i < max} -> a -> a & t)
  -> i:nat{i < max}
  -> acc:generate_elem_a t a max i ->
  generate_elem_a t a max (i + 1)

let generate_elem_f #t #a max f i acc =
  let c, res = acc in
  let c', e = f i c in
  let res' = Seq.snoc res e in
  c', res'


val generate_elems:
    #t:Type0
  -> #a:Type0
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a & t)
  -> init:a ->
  Tot (a & s:seq t{length s == n})

let generate_elems #t #a max n f init =
  repeat_gen n (generate_elem_a t a max) (generate_elem_f max f) (init, Seq.empty)



val bn_sub_f:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_nat{i < aLen}
  -> c:carry ->
  carry & uint64

let bn_sub_f #aLen #bLen a b i c =
  subborrow_u64 c a.[i] (bval b i)


val bn_sub:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen ->
  tuple2 carry (lbignum aLen)

let bn_sub #aLen #bLen a b =
  generate_elems #uint64 #carry aLen aLen (bn_sub_f a b) (u64 0)



val bn_add_f:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen
  -> i:size_nat{i < aLen}
  -> c:carry ->
  carry & uint64

let bn_add_f #aLen #bLen a b i c =
  addcarry_u64 c a.[i] (bval b i)


val bn_add:
    #aLen:size_nat
  -> #bLen:size_nat{bLen <= aLen}
  -> a:lbignum aLen
  -> b:lbignum bLen ->
  carry & lbignum aLen

let bn_add #aLen #bLen a b =
  generate_elems #uint64 #carry aLen aLen (bn_add_f a b) (u64 0)
