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

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.* +FStar.Pervasives -Spec.* +Spec.Frodo +Spec.Frodo.Params'"

val ec:
    b: size_nat{b <= params_logq}
  -> k: uint16{uint_v k < pow2 b}
  -> r: uint16{uint_v r < pow2 params_logq /\ uint_v r = uint_v k * pow2 (params_logq - b)}
let ec b k =
  let res = k <<. u32 (params_logq - b) in
  assert (uint_v res = (uint_v k * pow2 (params_logq - b)) % modulus U16);
  assert (uint_v k * pow2 (params_logq - b) < pow2 b * pow2 (params_logq - b));
  pow2_plus b (params_logq - b);
  //assert (uint_v k * pow2 (params_logq - b) < pow2 params_logq);
  //assert (uint_v res < pow2 params_logq);
  pow2_le_compat 16 params_logq;
  //assert (pow2 params_logq <= modulus U16);
  small_modulo_lemma_2 (uint_v res) (modulus U16);
  res

val dc:
    b: size_nat{b < params_logq}
  -> c: uint16
  -> r: uint16{uint_v r < pow2 b /\
             uint_v r = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 b}
let dc b c =
  let res1 = (c +. (u16 1 <<. u32 (params_logq - b - 1))) >>. u32 (params_logq - b) in
  assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1) % modulus U16) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  lemma_mod_plus_distr_l (pow2 (params_logq - b - 1)) (uint_v c) (modulus U16);
  assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  pow2_modulo_division_lemma_1 (uint_v c + pow2 (params_logq - b - 1)) (params_logq - b) 16;
  assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b)) % modulus U16);
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) (16 - params_logq + b) 16;
  assert (uint_v res1 = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b));
  let res = res1 &. ((u16 1 <<. u32 b) -. u16 1) in
  modulo_pow2_u16 res1 b;
  //assert (uint_v res1 % pow2 b = uint_v (res1 &. ((u16 1 <<. u32 b) -. u16 1)));
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) b (16 - params_logq + b);
  //assert (uint_v res = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 b);
  res

val frodo_key_encode:
    b: size_nat{b <= 8}
  -> a: lbytes (params_nbar * params_nbar * b / 8)
  -> matrix params_nbar params_nbar
let frodo_key_encode b a =
  let res = create params_nbar params_nbar in
  let v8 = Seq.create 8 (u8 0) in
  repeati params_nbar
  (fun i res ->
    repeati (params_nbar / 8)
    (fun j res ->
      let v8 = update_sub v8 0 b (Seq.sub a ((i + j) * b) b) in
      let vij = uint_from_bytes_le v8 in
      repeati 8
      (fun k res ->
        let ak = (vij >>. u32 (b * k)) &. ((u64 1 <<. u32 b) -. u64 1) in
	modulo_pow2_u64 (vij >>. u32 (b * k)) b;
        res.(i, 8 * j + k) <- ec b (to_u16 ak)
      ) res
    ) res
  ) res

val frodo_key_decode:
    b: size_nat{b <= 8}
  -> a: matrix params_nbar params_nbar
  -> lbytes (params_nbar * params_nbar * b / 8)
let frodo_key_decode b a =
  let resLen = params_nbar * params_nbar * b / 8 in
  let res = Seq.create resLen (u8 0) in
  repeati params_nbar
  (fun i res ->
    repeati (params_nbar / 8)
    (fun j res ->
      let templong = repeati 8
      (fun k templong ->
        let aij = dc b a.(i, 8 * j + k) in
        templong |. (to_u64 aij <<. u32 (b*k))
      ) (u64 0) in
      update_sub res ((i + j) * b) b (Seq.sub (uint_to_bytes_le templong) 0 b)
    ) res
  ) res
