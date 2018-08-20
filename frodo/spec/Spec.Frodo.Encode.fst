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

(* The simplified version of the encode and decode functions *)
(* when params_nbar = 8 *)

val lemma_matrix_equality_nbar:
    a:matrix params_nbar params_nbar
  -> b:matrix params_nbar params_nbar
  -> Lemma
      (requires forall (i:size_nat{i < params_nbar}) (k:size_nat{k < 8}). a.(i, k) == b.(i, k))
      (ensures a == b)
let lemma_matrix_equality_nbar a b =
  assert (forall (i:size_nat{i < params_nbar}) (k:size_nat{k < 8}). b.(i, k) == b.[i * params_nbar + k]);
  assert (forall (i:size_nat{i < params_nbar}) (k:size_nat{k < 8}). a.[i * params_nbar + k] == b.[i * params_nbar + k]);
  assert (forall (l:size_nat{l < params_nbar * params_nbar}). l == (l / params_nbar) * params_nbar + l % params_nbar /\
    l / params_nbar < params_nbar /\ l % params_nbar < params_nbar);
  assert (forall (k:size_nat{k < params_nbar * params_nbar}). a.[k] == b.[k]);
  Lib.Sequence.eq_intro a b

val ec:
    b:size_nat{b <= params_logq}
  -> k:uint16{uint_v k < pow2 b}
  -> r:uint16{uint_v r < pow2 params_logq /\ uint_v r == uint_v k * pow2 (params_logq - b)}
let ec b k =
  let res = k <<. u32 (params_logq - b) in
  assert (uint_v res = uint_v k * pow2 (params_logq - b) % modulus U16);
  assert (uint_v k * pow2 (params_logq - b) < pow2 b * pow2 (params_logq - b));
  pow2_plus b (params_logq - b);
  //assert (uint_v k * pow2 (params_logq - b) < pow2 params_logq);
  //assert (uint_v res < pow2 params_logq);
  pow2_le_compat 16 params_logq;
  //assert (pow2 params_logq <= modulus U16);
  small_modulo_lemma_2 (uint_v res) (modulus U16);
  res

val dc:
    b:size_nat{b < params_logq}
  -> c:uint16
  -> r:uint16{uint_v r < pow2 b /\
             uint_v r = (uint_v c + pow2 (params_logq - b - 1)) / pow2 (params_logq - b) % pow2 b}
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
    b:size_nat{b <= 8}
  -> x:uint64
  -> k:size_nat{k < 8}
  -> res:uint16
    {let rk = uint_v x / pow2 (b * k) % pow2 b in
      pow2_lt_compat 16 b;
      res == ec b (u16 rk)}
let ec1 b x k =
  modulo_pow2_u64 (x >>. u32 (b * k)) b;
  let rk = (x >>. u32 (b * k)) &. ((u64 1 <<. u32 b) -. u64 1) in
  assert (uint_v rk == uint_v (x >>. u32 (b * k)) % pow2 b);
  assert (uint_v (x >>. u32 (b * k)) == uint_v x / pow2 (b * k));
  assert (uint_v rk == uint_v x / pow2 (b * k) % pow2 b);
  pow2_lt_compat 16 b;
  uintv_extensionality (to_u16 rk) (u16 (uint_v x / pow2 (b * k) % pow2 b));
  ec b (to_u16 rk)

val frodo_key_encode_fc:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> i:size_nat{i < params_nbar}
  -> k:size_nat{k < 8}
  -> GTot uint16
let frodo_key_encode_fc b a i k =
  let v8 = Seq.create 8 (u8 0) in
  let v8 = update_sub v8 0 b (Seq.sub a (i * b) b) in
  let x = uint_from_bytes_le v8 in
  ec1 b x k

val frodo_key_encode1:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> res0:matrix params_nbar params_nbar
  -> x:uint64
  -> i:size_nat{i < params_nbar}
  -> res:matrix params_nbar params_nbar
    {(forall (i0:size_nat{i0 < params_nbar /\ i0 <> i}) (k:size_nat{k < 8}). res0.(i0, k) == res.(i0, k)) /\
     (forall (k:size_nat{k < 8}). res.(i, k) == ec1 b x k)}
let frodo_key_encode1 b a res0 x i =
  repeati_inductive 8
    (fun k res ->
      (forall (i0:size_nat{i0 < params_nbar /\ i0 <> i}) (k:size_nat{k < 8}). res0.(i0, k) == res.(i0, k)) /\
      (forall (k1:size_nat{k1 < k}). res.(i, k1) == ec1 b x k1))
    (fun k res ->
      res.(i, k) <- ec1 b x k
    ) res0

val frodo_key_encode2:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> res0:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> res:matrix params_nbar params_nbar
    {(forall (i0:size_nat{i0 < i}) (k:size_nat{k < 8}). res0.(i0, k) == res.(i0, k)) /\
     (forall (k:size_nat{k < 8}). res.(i, k) == frodo_key_encode_fc b a i k)}
let frodo_key_encode2 b a res0 i =
  let v8 = Seq.create 8 (u8 0) in
  let x = uint_from_bytes_le (update_sub v8 0 b (Seq.sub a (i * b) b)) in
  frodo_key_encode1 b a res0 x i

val frodo_key_encode:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> res:matrix params_nbar params_nbar
    {forall (i:size_nat{i < params_nbar}) (k:size_nat{k < 8}).
     res.(i, k) == frodo_key_encode_fc b a i k}
let frodo_key_encode b a =
  let res = create params_nbar params_nbar in

  repeati_inductive params_nbar
  (fun i res ->
    (forall (i0:size_nat{i0 < i}) (k:size_nat{k < 8}).
     res.(i0, k) == frodo_key_encode_fc b a i0 k))
  (fun i res ->
      frodo_key_encode2 b a res i
  ) res

val fold_logor_:
    f:(j:size_nat{j < 8} -> GTot uint64)
  -> i:size_nat{i <= 8}
  -> GTot uint64
let rec fold_logor_ f i =
  if i = 0 then u64 0
  else fold_logor_ f (i - 1) |. f (i - 1)

#set-options "--max_fuel 1"

val decode_fc:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> k:size_nat{k <= 8}
  -> GTot uint64
let decode_fc b a i k =
  let f (k:size_nat{k < 8}) =
    to_u64 (dc b a.(i, k)) <<. u32 (b * k) in
  fold_logor_ f k

val frodo_key_decode1:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> res:uint64{res == decode_fc b a i 8}
let frodo_key_decode1 b a i =
  repeati_inductive 8
    (fun k templong -> templong == decode_fc b a i k)
    (fun k templong ->
      templong |. to_u64 (dc b a.(i, k)) <<. u32 (b * k)
    ) (u64 0)

#set-options "--max_fuel 0"

val frodo_key_decode_fc:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> k:size_nat{k < b}
  -> GTot uint8
let frodo_key_decode_fc b a i k =
  u8 (uint_v (frodo_key_decode1 b a i) / pow2 (8 * k) % pow2 8)

//TODO: prove in Lib.Bytesequence
assume val lemma_uint_to_bytes_le:
    #t:m_inttype
  -> u:uint_t t
  -> Lemma
    (forall (i:nat{i < numbytes t}).
      index (uint_to_bytes_le #t u) i == u8 (uint_v u / pow2 (8 * i) % pow2 8))

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from 'Prims FStar.Pervasives Spec.Frodo.Encode Lib.Sequence Lib.IntTypes Spec.Frodo.Params'"

val frodo_key_decode2:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> res0:lbytes (params_nbar * params_nbar * b / 8)
  -> res:lbytes (params_nbar * params_nbar * b / 8)
    {(forall (k:size_nat{k < b}). res.[i * b + k] == frodo_key_decode_fc b a i k) /\
     (forall (i0:size_nat{i0 < i}) (k:size_nat{k < b}). res.[i0 * b + k] == res0.[i0 * b + k])}
let frodo_key_decode2 b a i res0 =
  let templong = frodo_key_decode1 b a i in
  lemma_uint_to_bytes_le #U64 templong;
  let tmp = Seq.sub (uint_to_bytes_le templong) 0 b in
  let res = update_sub res0 (i * b) b tmp in
  assert (forall k. res.[i * b + k] == tmp.[k]);
  res

val frodo_key_decode:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> res:lbytes (params_nbar * params_nbar * b / 8)
    {forall (i:size_nat{i < params_nbar}) (k:size_nat{k < b}).
     res.[i * b + k] == frodo_key_decode_fc b a i k}
let frodo_key_decode b a =
  let resLen = params_nbar * params_nbar * b / 8 in
  let res = Seq.create resLen (u8 0) in
  repeati_inductive params_nbar
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (k:size_nat{k < b}).
    res.[i0 * b + k] == frodo_key_decode_fc b a i0 k)
  (fun i res ->
      // Don't remove. Not a useless let
      let res = frodo_key_decode2 b a i res in
      res
  ) res
