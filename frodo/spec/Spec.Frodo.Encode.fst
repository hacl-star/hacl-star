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
    b:size_nat{b <= params_logq}
  -> k:uint16{uint_v k < pow2 b}
  -> r:uint16{uint_v r < pow2 params_logq /\ uint_v r == uint_v k * pow2 (params_logq - b)}
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
    b:size_nat{b < params_logq}
  -> c:uint16
  -> r:uint16{uint_v r < pow2 b /\
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
    b:size_nat{b <= 8}
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
  -> GTot uint16
let frodo_key_encode_inner b a i j k =
  let v8 = Seq.create 8 (u8 0) in
  let v8 = update_sub v8 0 b (Seq.sub a ((i + j) * b) b) in
  let vij = uint_from_bytes_le v8 in
  ec1 b vij k

val frodo_key_encode2:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> res0:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> Pure (matrix params_nbar params_nbar)
    (requires True)
    (ensures fun res ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}). res0.(i0, 8 * j + k) == res.(i0, 8 * j + k)) /\
      (forall (k1:size_nat{k1 < 8}). res.(i, 8 * j + k1) == frodo_key_encode_inner b a i j k1))
let frodo_key_encode2 b a res0 i j =
  let v8 = Seq.create 8 (u8 0) in
  let vij = uint_from_bytes_le (update_sub v8 0 b (Seq.sub a ((i + j) * b) b)) in
  frodo_key_encode1 b a res0 vij i j

val frodo_key_encode:
    b:size_nat{b <= 8}
  -> a:lbytes (params_nbar * params_nbar * b / 8)
  -> res:matrix params_nbar params_nbar{forall (i0:size_nat{i0 < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < 8}).
    res.(i0, 8 * j + k) == frodo_key_encode_inner b a i0 j k}
let frodo_key_encode b a =
  let res = create params_nbar params_nbar in
  let n2 = params_nbar / 8 in

  repeati_inductive params_nbar
  (fun i res ->
    (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}) (k:size_nat{k < 8}). res.(i0, 8 * j + k) == frodo_key_encode_inner b a i0 j k))
  (fun i res ->
    repeati_inductive n2
    (fun j res0 ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}) (k:size_nat{k < 8}). res0.(i0, 8 * j + k) == res.(i0, 8 * j + k)) /\
      (forall (j0:size_nat{j0 < j}) (k:size_nat{k < 8}). res0.(i, 8 * j0 + k) == frodo_key_encode_inner b a i j0 k))
    (fun j res0 ->
      frodo_key_encode2 b a res0 i j
    ) res
  ) res


val fold_logor_:
    f:(j:size_nat{j < 8} -> GTot uint64)
  -> i:size_nat{i <= 8}
  -> GTot uint64
let rec fold_logor_ f i =
  if i = 0 then u64 0
  else fold_logor_ f (i - 1) |. f (i - 1)

#set-options "--max_fuel 1"

val fold_logor_extensionality:
    f:(i:size_nat{i < 8} -> GTot uint64)
  -> g:(i:size_nat{i < 8} -> GTot uint64)
  -> i:size_nat{i <= 8} -> Lemma
  (requires forall (i:size_nat{i < 8}). f i == g i)
  (ensures fold_logor_ f i == fold_logor_ g i)
let rec fold_logor_extensionality f g i =
  if i = 0 then ()
  else fold_logor_extensionality f g (i - 1)

val frodo_key_decode1:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> res:uint64{res == fold_logor_ (fun k -> to_u64 (dc b a.(i, 8 * j + k)) <<. u32 (b * k)) 8}
let frodo_key_decode1 b a i j =
  let f (k:size_nat{k < 8}) =
    to_u64 (dc b a.(i, 8 * j + k)) <<. u32 (b * k) in
  let f1 k = fold_logor_ f k in
  assume ((u64 0 |. f 0) == f1 1);
  let templong =
    repeati_inductive 8
    (fun k templong -> templong == f1 k)
    (fun k templong ->
      templong |. f k
    ) (u64 0) in
  fold_logor_extensionality f (fun k -> to_u64 (dc b a.(i, 8 * j + k)) <<. u32 (b * k)) 8;
  templong

val lemma_uint_to_bytes_le:
    #t:m_inttype
  -> u:uint_t t
  -> Lemma
    (forall (i:size_nat{i < numbytes t}). index (uint_to_bytes_le #t u) i == u8 (uint_v u / pow2 (8 * i) % pow2 8))
let lemma_uint_to_bytes_le #t u = admit()

val frodo_key_decode_fc:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> k:size_nat{k < b}
  -> GTot uint8
let frodo_key_decode_fc b a i j k =
  u8 (uint_v (frodo_key_decode1 b a i j) / pow2 (8 * k) % pow2 8)

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '*'"

(*
// TODO: may be a good idea to enrich the specification of Seq.sub as follows:

val sub: #a:Type -> #len:size_nat -> s1:lseq a len -> start:size_nat -> n:size_nat{start + n <= len} 
  -> s2:lseq a n{forall (k:size_nat{k < n}).{:pattern (s2.[k])} s2.[k] == s1.[start + k]}
let sub #a #len s start n = FStar.Seq.slice #a s start (start + n)
*)

val frodo_key_decode_inner:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> GTot (res:lbytes b{forall (k:size_nat{k < b}). res.[k] == frodo_key_decode_fc b a i j k})
let frodo_key_decode_inner b a i j =
  let templong = frodo_key_decode1 b a i j in
  let tmp = uint_to_bytes_le templong in
  lemma_uint_to_bytes_le #U64 templong;
  Seq.sub tmp 0 b

#reset-options "--z3rlimit 50 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --using_facts_from 'Prims +FStar.Pervasives +Spec.Frodo.Encode +Lib.Sequence +Lib.IntTypes +Spec.Frodo.Params'"

val frodo_key_decode2:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> i:size_nat{i < params_nbar}
  -> j:size_nat{j < params_nbar / 8}
  -> res0:lbytes (params_nbar * params_nbar * b / 8)
  -> res:lbytes (params_nbar * params_nbar * b / 8)
    {(forall (k:size_nat{k < b}). res.[(i + j) * b + k] == frodo_key_decode_fc b a i j k) /\
     (forall (i0:size_nat{i0 < i}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < b}). res.[(i0 + j) * b + k] == res0.[(i0 + j) * b + k])}
let frodo_key_decode2 b a i j res0 =
  let templong = frodo_key_decode1 b a i j in
  lemma_uint_to_bytes_le #U64 templong;
  let tmp = Seq.sub (uint_to_bytes_le templong) 0 b in
  let res = Seq.update_sub res0 ((i + j) * b) b tmp in
  admit(); //TODO: fix
  res

val frodo_key_decode:
    b:size_nat{b <= 8}
  -> a:matrix params_nbar params_nbar
  -> res:lbytes (params_nbar * params_nbar * b / 8)
    {forall (i:size_nat{i < params_nbar}) (j:size_nat{j < params_nbar / 8}) (k:size_nat{k < b}).
      res.[(i + j) * b + k] == frodo_key_decode_fc b a i j k}
let frodo_key_decode b a =
  let resLen = params_nbar * params_nbar * b / 8 in
  let res = Seq.create resLen (u8 0) in
  let n2 = params_nbar / 8 in

  repeati_inductive params_nbar
  (fun i res ->
    forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}) (k:size_nat{k < b}). res.[(i0 + j) * b + k] == frodo_key_decode_fc b a i0 j k)
  (fun i res ->
    repeati_inductive n2
    (fun j res0 ->
      (forall (i0:size_nat{i0 < i}) (j:size_nat{j < n2}) (k:size_nat{k < b}). res0.[(i0 + j) * b + k] == res.[(i0 + j) * b + k]) /\
      (forall (j0:size_nat{j0 < j}) (k:size_nat{k < b}). res0.[(i + j0) * b + k] == frodo_key_decode_fc b a i j0 k))
    (fun j res0 ->
      frodo_key_decode2 b a i j res0
    ) res
  ) res
