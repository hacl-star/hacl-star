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

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

val lemma_matrix_equality_nbar:
    a:matrix params_nbar params_nbar
  -> b:matrix params_nbar params_nbar
  -> Lemma
      (requires (forall (i:size_nat{i < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). a.(i, 8 * j + k) == b.(i, 8 * j + k)))
      (ensures a == b)
let lemma_matrix_equality_nbar a b =
  assert (forall (i:size_nat{i < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). b.(i, 8 * j + k) == b.[i * params_nbar + j * 8 + k]);
  assert (forall (i:size_nat{i < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). a.[i * params_nbar + 8 * j + k] == b.[i * params_nbar + j * 8 + k]);
  assert (forall (i:size_nat{i < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). a.[i * params_nbar + j * 8 + k] == b.[i * params_nbar + j * 8 + k]);
  assert (forall (l:size_nat{l < params_nbar * params_nbar}). let x = l % params_nbar in l == (l / params_nbar) * params_nbar + x / 8 * 8 + x % 8 /\
    l / params_nbar < params_nbar /\ l % params_nbar < params_nbar /\ x / 8 < params_nbar / 8 /\ x % 8 < 8);
  assert (forall (k:size_nat{k < params_nbar * params_nbar}). a.[k] == b.[k]);
  Lib.Sequence.eq_intro a b

val ec:
    b: size_nat{b <= params_logq}
  -> k: uint16{uint_v k < pow2 b}
  -> r: uint16{uint_v r < pow2 params_logq /\ uint_v r == uint_v k * pow2 (params_logq - b)}
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
  //assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1) % modulus U16) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  lemma_mod_plus_distr_l (pow2 (params_logq - b - 1)) (uint_v c) (modulus U16);
  //assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) % modulus U16) / pow2 (params_logq - b)) % modulus U16);
  pow2_modulo_division_lemma_1 (uint_v c + pow2 (params_logq - b - 1)) (params_logq - b) 16; 
  //assert (uint_v res1 = (((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b)) % modulus U16);
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) (16 - params_logq + b) 16;
  //assert (uint_v res1 = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 (16 - params_logq + b));
  let res = res1 &. ((u16 1 <<. u32 b) -. u16 1) in
  modulo_pow2_u16 res1 b;   
  //assert (uint_v res1 % pow2 b = uint_v (res1 &. ((u16 1 <<. u32 b) -. u16 1)));
  pow2_modulo_modulo_lemma_1 ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) b (16 - params_logq + b); 
  //assert (uint_v res = ((uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b)) % pow2 b);
  res

val ec1:
    b: size_nat{b <= 8}
  -> vij:uint64
  -> k:size_nat{k < 8}
  -> Pure uint16
    (requires True)
    (ensures fun res ->
      let rk = (uint_v vij / pow2 (b * k)) % pow2 b in
      pow2_lt_compat 16 b;
      res == ec b (u16 rk))
let ec1 b vij k =
  modulo_pow2_u64 (vij >>. u32 (b * k)) b;
  let rk = (vij >>. u32 (b * k)) &. ((u64 1 <<. u32 b) -. u64 1) in
  assert (uint_v rk == uint_v (vij >>. u32 (b * k)) % pow2 b);
  assert (uint_v (vij >>. u32 (b * k)) == uint_v vij / pow2 (b * k));
  assert (uint_v rk == (uint_v vij / pow2 (b * k)) % pow2 b);
  pow2_lt_compat 16 b;
  uintv_extensionality (to_u16 rk) (u16 ((uint_v vij / pow2 (b * k)) % pow2 b));
  ec b (to_u16 rk)

val frodo_key_encode1:
    b: size_nat{b <= 8}
  -> a: lbytes (params_nbar * params_nbar * b / 8)
  -> res0: matrix params_nbar params_nbar
  -> vij:uint64
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> Pure (matrix params_nbar params_nbar)
    (requires True)
    (ensures fun res ->
      (forall (i0:size_nat{i0 < params_nbar /\ i0 <> i}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). res0.(i0, 8 * j + k) == res.(i0, 8 * j + k)) /\
      (forall (k1:size_nat{k1 < 8}). res.(i, 8 * j + k1) == ec1 b vij k1))
let frodo_key_encode1 b a res0 vij i j =
  repeati_inductive 8
    (fun k res ->
      (forall (i0:size_nat{i0 < params_nbar /\ i0 <> i}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). res0.(i0, 8 * j + k) == res.(i0, 8 * j + k)) /\
      (forall (k1:size_nat{k1 < k}). res.(i, 8 * j + k1) == ec1 b vij k1))
    (fun k res ->
      res.(i, 8 * j + k) <- ec1 b vij k
    ) res0

val frodo_key_encode_inner:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> k:size_nat{k < 8}
  -> v8:lbytes 8{forall (l:size_nat{b <= l /\ l < 8}). v8.[l] == u8 0}
  -> GTot uint16
let frodo_key_encode_inner b a i j k v8 =
  let v8 = update_sub v8 0 b (Seq.sub a ((i + j) * b) b) in
  let vij = uint_from_bytes_le v8 in
  ec1 b vij k

val frodo_key_encode2:
    b: size_nat{b <= 8}
  -> a: lbytes (params_nbar * params_nbar * b / 8)
  -> res0: matrix params_nbar params_nbar
  -> v8:lbytes 8{forall (k:size_nat{b <= k /\ k < 8}). v8.[k] == u8 0}
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> Pure (matrix params_nbar params_nbar)
    (requires True)
    (ensures fun res ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). res0.(i0, 8 * j + k) == res.(i0, 8 * j + k)) /\
      (forall (k1:size_nat{k1 < 8}). res.(i, 8 * j + k1) == frodo_key_encode_inner b a i j k1 v8))
let frodo_key_encode2 b a res0 v8 i j =
  let vij = uint_from_bytes_le (update_sub v8 0 b (Seq.sub a ((i + j) * b) b)) in
  frodo_key_encode1 b a res0 vij i j

val frodo_key_encode:
    b: size_nat{b <= 8}
  -> a: lbytes (params_nbar * params_nbar * b / 8)
  -> res:matrix params_nbar params_nbar{forall (i0:size_nat{i0 < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}).
      res.(i0, 8 * j + k) == frodo_key_encode_inner b a i0 j k (Seq.create 8 (u8 0))}
let frodo_key_encode b a =
  let res = create params_nbar params_nbar in
  let v8 = Seq.create 8 (u8 0) in
  let n2 = params_nbar / 8 in

  repeati_inductive params_nbar
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}) (k:size_nat{k < 8}). res.(i0, 8 * j + k) == frodo_key_encode_inner b a i0 j k v8)
  (fun i res ->
    repeati_inductive n2
    (fun j res0 ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}) (k:size_nat{k < 8}). res0.(i0, 8 * j + k) == res.(i0, 8 * j + k)) /\
      (forall (j0:size_nat{j0 < j}) (k:size_nat{k < 8}). res0.(i, 8 * j0 + k) == frodo_key_encode_inner b a i j0 k v8))
    (fun j res0 ->
      frodo_key_encode2 b a res0 v8 i j
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
