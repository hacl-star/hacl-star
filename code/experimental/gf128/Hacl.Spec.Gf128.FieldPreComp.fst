module Hacl.Spec.Gf128.FieldPreComp

open FStar.Mul
open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence

open Hacl.Spec.GF128.Vec

module GF = Spec.GaloisField


#reset-options "--z3rlimit 50 --max_fuel 1"

type table = lseq uint64 256
type table1 = lseq uint64 128

inline_for_extraction noextract
let elem_s = lseq uint64 2

let to_elem (x:elem_s) : elem =
  nat_to_uint #U128 (v x.[0] + v x.[1] * pow2 64)

let from_elem (x:elem) : elem_s =
  create2 (to_u64 x) (to_u64 (x >>. 64ul))

val lemma_to_from_elem: x:elem ->
  Lemma (to_elem (from_elem x) == x)
let lemma_to_from_elem x = ()

val lemma_from_to_elem: x:elem_s ->
  Lemma (from_elem (to_elem x) == x)
let lemma_from_to_elem x =
  eq_intro (from_elem (to_elem x)) x


let fadd_s (x:elem_s) (y:elem_s) : elem_s =
  let r0 = x.[0] ^. y.[0] in
  let r1 = x.[1] ^. y.[1] in
  create2 r0 r1

val fadd_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (fadd_s x y) == GF.fadd (to_elem x) (to_elem y))
let fadd_lemma x y = admit()


let bit_mask64 (u:uint64) = u64 0 -. (u &. u64 1)

let fmul_be_s_f (x:uint64) (i:nat{i < 64}) (tmp_sh:elem_s & elem_s) : (elem_s & elem_s) =
  let (tmp, sh) = tmp_sh in
  let (s0, s1) = (sh.[0], sh.[1]) in
  let m = bit_mask64 (x >>. (63ul -. size i)) in
  let tmp = tmp.[0] <- tmp.[0] ^. (m &. s0) in
  let tmp = tmp.[1] <- tmp.[1] ^. (m &. s1) in
  let s = bit_mask64 s0 in
  let sh = sh.[0] <- (s0 >>. 1ul) |. (s1 <<. size 63) in
  let sh = sh.[1] <- (s1 >>. 1ul) ^. (s &. u64 0xE100000000000000) in
  (tmp, sh)


let fmul_be_s (x:elem_s) (y:elem_s) : elem_s =
  let zero2 = create 2 (u64 0) in
  let (tmp, sh) =
    Lib.LoopCombinators.repeati 64 (fmul_be_s_f x.[1]) (zero2, y) in
  let (tmp, sh) =
    Lib.LoopCombinators.repeati 64 (fmul_be_s_f x.[0]) (tmp, sh) in
  tmp

val fmul_be_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (fmul_be_s x y) == GF.fmul_be (to_elem x) (to_elem y))
let fmul_be_lemma x y = admit()

let precomp_s_f (i:nat{i < 128}) (pre_sh:table & elem_s) : (table & elem_s) =
  let (pre, sh) = pre_sh in
  let (s0, s1) = (sh.[0], sh.[1]) in
  let pre = pre.[i * 2] <- s0 in
  let pre = pre.[i * 2 + 1] <- s1 in
  let s = bit_mask64 s0 in
  let sh = sh.[0] <- (s0 >>. 1ul) |. (s1 <<. size 63) in
  let sh = sh.[1] <- (s1 >>. 1ul) ^. (s &. u64 0xE100000000000000) in
  (pre, sh)

let precomp_s (r:elem_s) : table =
  let pre = create 256 (u64 0) in
  let (pre, sh) =
    Lib.LoopCombinators.repeati 128 (precomp_s_f) (pre, r) in
  pre

let fmul_pre_s_f (x:uint64) (tab:table1) (i:nat{i < 64}) (tmp:elem_s) : elem_s =
  let m = bit_mask64 (x >>. (63ul -. size i)) in
  let tmp = tmp.[0] <- tmp.[0] ^. (m &. tab.[i * 2]) in
  let tmp = tmp.[1] <- tmp.[1] ^. (m &. tab.[i * 2 + 1]) in

  tmp


let fmul_pre_s (x:elem_s) (tab:table) : elem_s =
  let zero2 = create 2 (u64 0) in
  let tmp =
    Lib.LoopCombinators.repeati 64 (fmul_pre_s_f x.[1] (sub tab 0 128)) zero2 in
  let tmp =
    Lib.LoopCombinators.repeati 64 (fmul_pre_s_f x.[0] (sub tab 128 128)) tmp in
  tmp


val fmul_pre_lemma: x:elem_s -> y:elem_s -> Lemma
  (to_elem (fmul_pre_s x (precomp_s y)) == GF.fmul_be (to_elem x) (to_elem y))
let fmul_pre_lemma x y = admit()





(*
let fmul_be (#f:field) (x:felem f) (y:felem f) : felem f =
  let one = one #f in
  let zero = zero #f in

  let (tmp, sh) =
    repeati (bits f.t)
    (fun i (tmp, sh) ->
      let m = eq_mask #f.t ((x >>. size (bits f.t - 1 - i)) &. one) one in
      let tmp = tmp ^. (m &. sh) in
      let carry_mask = eq_mask #f.t (sh &. one) one in
      let sh = sh >>. size 1 in
      let sh = sh ^. (carry_mask &. f.irred) in
      (tmp, sh)) (zero,y) in
  tmp
*)
