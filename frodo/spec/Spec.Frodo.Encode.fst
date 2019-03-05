module Spec.Frodo.Encode

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
open FStar.Math.Lemmas

open Spec.Matrix
open Spec.Frodo.Lemmas
open Spec.Frodo.Params

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

(* The simplified version of the encode and decode functions *)
(* when params_nbar = 8 *)

val ec:
    b:size_nat{0 < b /\ b <= params_logq}
  -> k:uint16{uint_v k < pow2 b}
  -> r:uint16{uint_v r < pow2 params_logq /\ uint_v r == uint_v k * pow2 (params_logq - b)}
let ec b k =
  let res = k <<. size (params_logq - b) in
  assert (uint_v res = uint_v k * pow2 (params_logq - b) % modulus U16);
  assert (uint_v k * pow2 (params_logq - b) < pow2 b * pow2 (params_logq - b));
  pow2_plus b (params_logq - b);
  //assert (uint_v k * pow2 (params_logq - b) < pow2 params_logq);
  //assert (uint_v res < pow2 params_logq);
  pow2_le_compat 16 params_logq;
  //assert (pow2 params_logq <= modulus U16);
  small_modulo_lemma_2 (uint_v res) (modulus U16);
  res

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq' --smtencoding.nl_arith_repr wrapped"

val dc:
    b:size_nat{0 < b /\ b < params_logq}
  -> c:uint16
  -> r:uint16{uint_v r < pow2 b /\
             uint_v r = (uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b) % pow2 b}
let dc b c =
  let res1 = (c +. (u16 1 <<. size (params_logq - b - 1))) >>. size (params_logq - b) in
  //assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1) % modulus U16) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  lemma_mod_plus_distr_l (pow2 (params_logq - b - 1)) (uint_v c) (modulus U16);
  //assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  pow2_modulo_division_lemma_1 (uint_v c + pow2 (params_logq - b - 1)) (params_logq - b) 16;
  //assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b)) % modulus U16);
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) (16 - params_logq + b) 16;
  //assert (uint_v res1 = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b));
  let res = res1 &. ((u16 1 <<. size b) -. u16 1) in
  modulo_pow2_u16 res1 b;
  assert (uint_v res1 % pow2 b = uint_v (res1 &. ((u16 1 <<. size b) -. u16 1)));
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) b (16 - params_logq + b);
  res

val ec1:
    b:size_nat{0 < b /\ b <= 8}
  -> x:uint64
  -> k:size_nat{k < 8}
  -> res:uint16
    {let rk = uint_v x / pow2 (b * k) % pow2 b in
      pow2_lt_compat 16 b;
      res == ec b (u16 rk)}
let ec1 b x k =
  modulo_pow2_u64 (x >>. size (b * k)) b;
  let rk = (x >>. size (b * k)) &. ((u64 1 <<. size b) -. u64 1) in
  assert (uint_v rk == uint_v (x >>. size (b * k)) % pow2 b);
  assert (uint_v (x >>. size (b * k)) == uint_v x / pow2 (b * k));
  assert (uint_v rk == uint_v x / pow2 (b * k) % pow2 b);
  pow2_lt_compat 16 b;
  //uintv_extensionality (to_u16 rk) (u16 (uint_v x / pow2 (b * k) % pow2 b));
  ec b (to_u16 rk)

val frodo_key_encode0:
    b:size_nat{0 < b /\ b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> x:uint64
  -> i:size_nat{i < params_nbar}
  -> k:size_nat{k < 8}
  -> res:matrix params_nbar params_nbar
  -> matrix params_nbar params_nbar
let frodo_key_encode0 b a x i k res =
  res.(i, k) <- ec1 b x k

val frodo_key_encode1:
     b:size_nat{0 < b /\ b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> i:size_nat{i < params_nbar}
  -> uint64
let frodo_key_encode1 b a i =
  let v8 = Seq.create 8 (u8 0) in
  let v8 = update_sub v8 0 b (Seq.sub a (i * b) b) in
  uint_from_bytes_le #U64 v8

val frodo_key_encode2:
     b:size_nat{0 < b /\ b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> i:size_nat{i < params_nbar}
  -> res:matrix params_nbar params_nbar
  -> matrix params_nbar params_nbar
let frodo_key_encode2 b a i res =
  let x = frodo_key_encode1 b a i in
  Loops.repeati 8 (frodo_key_encode0 b a x i) res

val frodo_key_encode:
    b:size_nat{0 < b /\ b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> res:matrix params_nbar params_nbar
let frodo_key_encode b a =
  let res = create params_nbar params_nbar in
  Loops.repeati params_nbar (frodo_key_encode2 b a) res

val frodo_key_decode0:
    b:size_nat{0 < b /\ b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> k:size_nat{k < 8}
  -> templong:uint64
  -> uint64
let frodo_key_decode0 b a i k templong =
  templong |. to_u64 (dc b a.(i, k)) <<. size (b * k)

val frodo_key_decode1:
    b:size_nat{0 < b /\ b <= 8}
  -> i:size_nat{i < params_nbar}
  -> templong:uint64
  -> res:lbytes (params_nbar * params_nbar * b / 8)
  -> lbytes (params_nbar * params_nbar * b / 8)
let frodo_key_decode1 b i templong res =
  update_sub res (i * b) b (Seq.sub (uint_to_bytes_le templong) 0 b)

val decode_templong_t : i:size_nat{i <= 8} -> Type0
let decode_templong_t i = uint64

val frodo_key_decode2:
    b:size_nat{0 < b /\ b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> res:lbytes (params_nbar * params_nbar * b / 8)
  -> lbytes (params_nbar * params_nbar * b / 8)
let frodo_key_decode2 b a i res =
  let templong = Loops.repeat_gen 8 decode_templong_t (frodo_key_decode0 b a i) (u64 0) in
  frodo_key_decode1 b i templong res

val frodo_key_decode:
    b:size_nat{0 < b /\ b <= 8}
  -> a:matrix params_nbar params_nbar
  -> res:lbytes (params_nbar * params_nbar * b / 8)
let frodo_key_decode b a =
  let resLen = params_nbar * params_nbar * b / 8 in
  let res = Seq.create resLen (u8 0) in
  Loops.repeati params_nbar (frodo_key_decode2 b a) res
