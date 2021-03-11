module Spec.Frodo.Encode

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Spec.Matrix
open Spec.Frodo.Lemmas

module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** The simplified version of the encode and decode functions when n = params_nbar = 8 *)

val ec:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b <= logq}
  -> k:uint16{v k < pow2 b}
  -> Pure uint16
    (requires True)
    (ensures fun r ->
      v r < pow2 logq /\ v r == v k * pow2 (logq - b))

let ec logq b k =
  let res = k <<. size (logq - b) in
  assert (v res = v k * pow2 (logq - b) % modulus U16);

  calc (<) {
    v k * pow2 (logq - b);
    (<) { Math.Lemmas.lemma_mult_lt_right (pow2 (logq - b)) (v k) (pow2 b) }
    pow2 b * pow2 (logq - b);
    (==) { Math.Lemmas.pow2_plus b (logq - b) }
    pow2 logq;
    };

  Math.Lemmas.pow2_le_compat 16 logq;
  Math.Lemmas.small_modulo_lemma_2 (v k * pow2 (logq - b)) (modulus U16);
  assert (v res = v k * pow2 (logq - b));
  res


val dc:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b < logq}
  -> c:uint16
  -> Pure uint16
    (requires True)
    (ensures  fun r ->
      v r < pow2 b /\ v r = (v c + pow2 (logq - b - 1)) / pow2 (logq - b) % pow2 b)

let dc logq b c =
  let res1 = (c +. (u16 1 <<. size (logq - b - 1))) >>. size (logq - b) in
  Math.Lemmas.pow2_lt_compat 16 (16 - logq + b);

  calc (==) {
    v res1;
    (==) { }
    (((v c + pow2 (logq - b - 1) % modulus U16) % modulus U16) / pow2 (logq - b)) % modulus U16;
    (==) { Math.Lemmas.lemma_mod_plus_distr_r (v c) (pow2 (logq - b - 1)) (modulus U16) }
    (((v c + pow2 (logq - b - 1)) % modulus U16) / pow2 (logq - b)) % modulus U16;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (v c + pow2 (logq - b - 1)) (logq - b) 16 }
    (((v c + pow2 (logq - b - 1)) / pow2 (logq - b)) % pow2 (16 - logq + b)) % modulus U16;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_2 ((v c + pow2 (logq - b - 1)) / pow2 (logq - b)) 16 (16 - logq + b) }
    ((v c + pow2 (logq - b - 1)) / pow2 (logq - b)) % pow2 (16 - logq + b);
    };

  let res = res1 &. ((u16 1 <<. size b) -. u16 1) in
  Math.Lemmas.pow2_lt_compat 16 b;

  calc (==) {
    v res;
    (==) { modulo_pow2_u16 res1 b }
    v res1 % pow2 b;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 ((v c + pow2 (logq - b - 1)) / pow2 (logq - b)) b (16 - logq + b) }
    ((v c + pow2 (logq - b - 1)) / pow2 (logq - b)) % pow2 b;
    };
  res


val ec1:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b <= logq /\ b <= 8}
  -> x:uint64
  -> k:size_nat{k < 8}
  -> Pure uint16
    (requires True)
    (ensures  fun res ->
      let rk = v x / pow2 (b * k) % pow2 b in
      Math.Lemmas.pow2_lt_compat 16 b;
      res == ec logq b (u16 rk))

let ec1 logq b x k =
  let rk = (x >>. size (b * k)) &. ((u64 1 <<. size b) -. u64 1) in
  Math.Lemmas.pow2_lt_compat 16 b;

  calc (==) {
    v rk;
    (==) { modulo_pow2_u64 (x >>. size (b * k)) b }
    v (x >>. size (b * k)) % pow2 b;
    (==) { }
    v x / pow2 (b * k) % pow2 b;
    };

  ec logq b (to_u16 rk)


val frodo_key_encode0:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b <= logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:lbytes (n * n * b / 8)
  -> x:uint64
  -> i:size_nat{i < n}
  -> k:size_nat{k < 8}
  -> res:matrix n n
  -> matrix n n

let frodo_key_encode0 logq b n a x i k res =
  res.(i, k) <- ec1 logq b x k


val frodo_key_encode1:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b <= logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:lbytes (n * n * b / 8)
  -> i:size_nat{i < n}
  -> uint64

let frodo_key_encode1 logq b n a i =
  let v8 = LSeq.create 8 (u8 0) in
  let v8 = update_sub v8 0 b (LSeq.sub a (i * b) b) in
  uint_from_bytes_le #U64 v8


val frodo_key_encode2:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b <= logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:lbytes (n * n * b / 8)
  -> i:size_nat{i < n}
  -> res:matrix n n
  -> matrix n n

let frodo_key_encode2 logq b n a i res =
  let x = frodo_key_encode1 logq b n a i in
  Loops.repeati 8 (frodo_key_encode0 logq b n a x i) res


val frodo_key_encode:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b <= logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:lbytes (n * n * b / 8)
  -> matrix n n

let frodo_key_encode logq b n a =
  let res = create n n in
  Loops.repeati n (frodo_key_encode2 logq b n a) res


val frodo_key_decode0:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b < logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:matrix n n
  -> i:size_nat{i < n}
  -> k:size_nat{k < 8}
  -> templong:uint64
  -> uint64

let frodo_key_decode0 logq b n a i k templong =
  templong |. to_u64 (dc logq b a.(i, k)) <<. size (b * k)


val frodo_key_decode1:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b < logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> i:size_nat{i < n}
  -> templong:uint64
  -> res:lbytes (n * n * b / 8)
  -> lbytes (n * n * b / 8)

let frodo_key_decode1 logq b n i templong res =
  update_sub res (i * b) b (LSeq.sub (uint_to_bytes_le templong) 0 b)


val decode_templong_t : i:size_nat{i <= 8} -> Type0
let decode_templong_t i = uint64

val frodo_key_decode2:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b < logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:matrix n n
  -> i:size_nat{i < n}
  -> res:lbytes (n * n * b / 8)
  -> lbytes (n * n * b / 8)

let frodo_key_decode2 logq b n a i res =
  let templong = Loops.repeat_gen 8 decode_templong_t (frodo_key_decode0 logq b n a i) (u64 0) in
  frodo_key_decode1 logq b n i templong res


val frodo_key_decode:
    logq:size_pos{logq <= 16}
  -> b:size_pos{b < logq /\ b <= 8}
  -> n:size_pos{n == 8}
  -> a:matrix n n
  -> lbytes (n * n * b / 8)

let frodo_key_decode logq b n a =
  let resLen = n * n * b / 8 in
  let res = LSeq.create resLen (u8 0) in
  Loops.repeati n (frodo_key_decode2 logq b n a) res
