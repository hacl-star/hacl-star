module Spec.SHA2.Core

open FStar.Mul
open FStar.Seq

open Spec.SHA2.Word
open Spec.SHA2.Specialization


(* val pow2_values: x:nat -> Lemma *)
(*   (requires True) *)
(*   (ensures (let p = pow2 x in *)
(*    match x with *)
(*    | 61 -> p=2305843009213693952 *)
(*    | 125 -> p=42535295865117307932921825928971026432 *)
(*    | _  -> True)) *)
(*   [SMTPat (pow2 x)] *)
(* let pow2_values x = *)
(*    match x with *)
(*    | 61 -> assert_norm (pow2 61 == 2305843009213693952) *)
(*    | 125 -> assert_norm (pow2 125 == 42535295865117307932921825928971026432) *)
(*    | _  -> () *)


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 25"


let (+%^) = word_add_mod


private val _Ch: x:word -> y:word -> z:word -> Tot word
let _Ch x y z = word_logxor (word_logand x y) (word_logand (word_lognot x) z)

private val _Maj: x:word -> y:word -> z:word -> Tot word
let _Maj x y z = word_logxor (word_logand x y) (word_logxor (word_logand x z) (word_logand y z))

private val _Sigma0: x:word -> Tot word
let _Sigma0 x = word_logxor (rotate_right x (index constants_Sigma0 0))
                            (word_logxor (rotate_right x (index constants_Sigma0 1))
                                         (rotate_right x (index constants_Sigma0 2)))

private val _Sigma1: x:word -> Tot word
let _Sigma1 x = word_logxor (rotate_right x (index constants_Sigma1 0))
                            (word_logxor (rotate_right x (index constants_Sigma1 1))
                                         (rotate_right x (index constants_Sigma1 2)))

private val _sigma0: x:word -> Tot word
let _sigma0 x = word_logxor (rotate_right x (index constants_sigma0 0))
                            (word_logxor (rotate_right x (index constants_sigma0 1))
                                         (word_shift_right x (index constants_sigma0 2)))

private val _sigma1: x:word -> Tot word
let _sigma1 x = word_logxor (rotate_right x (index constants_sigma1 0))
                            (word_logxor (rotate_right x (index constants_sigma1 1))
                                         (word_shift_right x (index constants_sigma1 2)))


private let rec ws (b:block_w) (t:counter{t < size_k_w}) : Tot word =
  if t < size_block_w then index b t
  else
    let t16 = ws b (t - 16) in
    let t15 = ws b (t - 15) in
    let t7  = ws b (t - 7) in
    let t2  = ws b (t - 2) in

    let s1 = _sigma1 t2 in
    let s0 = _sigma0 t15 in
    (s1 +%^ (t7 +%^ (s0 +%^ t16)))


private let shuffle_core (hash:hash_w) (block:block_w) (t:counter{t < size_k_w}) : Tot hash_w =
  let a = index hash 0 in
  let b = index hash 1 in
  let c = index hash 2 in
  let d = index hash 3 in
  let e = index hash 4 in
  let f = index hash 5 in
  let g = index hash 6 in
  let h = index hash 7 in

  (**) assert_norm(List.Tot.length k = size_k_w);
  let t1 = h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ (List.Tot.index k t) +%^ (ws block t) in
  let t2 = (_Sigma0 a) +%^ (_Maj a b c) in

  (**) cut(7 < Seq.length hash);
  let hash = upd hash 7 g in
  let hash = upd hash 6 f in
  let hash = upd hash 5 e in
  let hash = upd hash 4 (d +%^ t1) in
  let hash = upd hash 3 c in
  let hash = upd hash 2 b in
  let hash = upd hash 1 a in
  let hash = upd hash 0 (t1 +%^ t2) in
  hash


private let rec shuffle (hash:hash_w) (block:block_w) (t:counter{t <= size_k_w}) : Tot hash_w (decreases (size_k_w - t)) =
  if t < size_k_w then
    let hash = shuffle_core hash block t in
    shuffle hash block (t + 1)
  else hash


let update_compress (hash:hash_w) (block:bytes{length block = size_block}) : Tot hash_w =
  let b = words_from_be size_block_w block in
  let hash_1 = shuffle hash b 0 in
  Spec.Lib.map2 (fun x y -> x +%^ y) hash hash_1


let rec update_multi (hash:hash_w) (blocks:bytes{length blocks % size_block = 0}) : Tot hash_w (decreases (Seq.length blocks)) =
  if Seq.length blocks = 0 then hash
  else
    let (h,t) = Seq.split blocks size_block in
    update_multi (update_compress hash h) t


private let pad0_length (len:nat) : Tot (n:nat{(len + 1 + n + size_len_8) % size_block = 0}) =
  size_block - ((len + size_len_8 + 1) % size_block)


(* Pad the data up to the block length and encode the total length *)
let pad (len:nat{len < max_input_len_8}) : Tot (b:bytes{(length b + len) % size_block = 0}) =
  let firstbyte = Seq.create 1 0x80uy in
  let zeros = Seq.create (pad0_length len) 0uy in
  let encodedlen = Endianness.big_bytes size_len_ul_8 (len * 8) in
  firstbyte @| zeros @| encodedlen


let update_last (hash:hash_w) (prevlen:nat{prevlen % size_block = 0}) (input:bytes{(Seq.length input) + prevlen < max_input_len_8}) : Tot hash_w =
  let blocks = pad (prevlen + Seq.length input) in
  update_multi hash (input @| blocks)


let finish (hash:hash_w) : Tot bytes = words_to_be size_hash_w hash


let hash (input:bytes{Seq.length input < max_input_len_8}) : Tot (hash:bytes) =
  let n = Seq.length input / size_block in
  let (bs,l) = Seq.split input (n * size_block) in
  let hash = update_multi h_0 bs in
  let hash = update_last hash (n * size_block) l in
  finish hash


let hash' (input:bytes{Seq.length input < max_input_len_8}) : Tot (hash:bytes{length hash = 64}) =
  let blocks = pad (Seq.length input) in
  finish (update_multi h_0 (input @| blocks))
