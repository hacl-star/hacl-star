module Spec.SHA2

open FStar.Mul
open FStar.Seq
open FStar.UInt32

module Word = FStar.UInt32

val pow2_values: x:nat -> Lemma
  (requires True)
  (ensures (let p = pow2 x in
   match x with
   | 61 -> p=2305843009213693952
   | _  -> True))
  [SMTPat (pow2 x)]
let pow2_values x =
   match x with
   | 61 -> assert_norm (pow2 61 == 2305843009213693952)
   | _  -> ()


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 25"


//
// SHA-256
//

(* Define algorithm parameters *)
let size_hash_w = 8
let size_block_w = 16
let size_hash = 4 * size_hash_w
let size_block = 4 * size_block_w
let size_k_w = 64
let size_len_8 = 8
let size_len_ul_8 = 8ul
let max_input_len_8 = pow2 61

type bytes = m:seq UInt8.t
type word = Word.t
type hash_w = m:seq word {length m = size_hash_w}
type block_w = m:seq word {length m = size_block_w}
type blocks_w = m:seq block_w
type counter = UInt.uint_t 32

(* Define word based operators *)
let words_to_be = Spec.Lib.uint32s_to_be
let words_from_be = Spec.Lib.uint32s_from_be
let word_logxor = Word.logxor
let word_logand = Word.logand
let word_logor = Word.logor
let word_lognot = Word.lognot
let word_shift_right = Word.shift_right



private let rotate_right (a:word) (s:word {v s<32}) : Tot word =
  ((a >>^ s) |^ (a <<^ (32ul -^ s)))

(* [FIPS 180-4] section 4.1.2 *)
private val _Ch: x:word -> y:word -> z:word -> Tot word
let _Ch x y z = word_logxor (word_logand x y) (word_logand (word_lognot x) z)

private val _Maj: x:word -> y:word -> z:word -> Tot word
let _Maj x y z = word_logxor (word_logand x y) (word_logxor (word_logand x z) (word_logand y z))

private val _Sigma0: x:word -> Tot word
let _Sigma0 x = word_logxor (rotate_right x 2ul) (word_logxor (rotate_right x 13ul) (rotate_right x 22ul))

private val _Sigma1: x:word -> Tot word
let _Sigma1 x = word_logxor (rotate_right x 6ul) (word_logxor (rotate_right x 11ul) (rotate_right x 25ul))

private val _sigma0: x:word -> Tot word
let _sigma0 x = word_logxor (rotate_right x 7ul) (word_logxor (rotate_right x 18ul) (word_shift_right x 3ul))

private val _sigma1: x:word -> Tot word
let _sigma1 x = word_logxor (rotate_right x 17ul) (word_logxor (rotate_right x 19ul) (word_shift_right x 10ul))


(* [FIPS 180-4] section 4.2.2 *)
private let k = [
  0x428a2f98ul; 0x71374491ul; 0xb5c0fbcful; 0xe9b5dba5ul;
  0x3956c25bul; 0x59f111f1ul; 0x923f82a4ul; 0xab1c5ed5ul;
  0xd807aa98ul; 0x12835b01ul; 0x243185beul; 0x550c7dc3ul;
  0x72be5d74ul; 0x80deb1feul; 0x9bdc06a7ul; 0xc19bf174ul;
  0xe49b69c1ul; 0xefbe4786ul; 0x0fc19dc6ul; 0x240ca1ccul;
  0x2de92c6ful; 0x4a7484aaul; 0x5cb0a9dcul; 0x76f988daul;
  0x983e5152ul; 0xa831c66dul; 0xb00327c8ul; 0xbf597fc7ul;
  0xc6e00bf3ul; 0xd5a79147ul; 0x06ca6351ul; 0x14292967ul;
  0x27b70a85ul; 0x2e1b2138ul; 0x4d2c6dfcul; 0x53380d13ul;
  0x650a7354ul; 0x766a0abbul; 0x81c2c92eul; 0x92722c85ul;
  0xa2bfe8a1ul; 0xa81a664bul; 0xc24b8b70ul; 0xc76c51a3ul;
  0xd192e819ul; 0xd6990624ul; 0xf40e3585ul; 0x106aa070ul;
  0x19a4c116ul; 0x1e376c08ul; 0x2748774cul; 0x34b0bcb5ul;
  0x391c0cb3ul; 0x4ed8aa4aul; 0x5b9cca4ful; 0x682e6ff3ul;
  0x748f82eeul; 0x78a5636ful; 0x84c87814ul; 0x8cc70208ul;
  0x90befffaul; 0xa4506cebul; 0xbef9a3f7ul; 0xc67178f2ul]


private let h_0 = [
  0x6a09e667ul; 0xbb67ae85ul; 0x3c6ef372ul; 0xa54ff53aul;
  0x510e527ful; 0x9b05688cul; 0x1f83d9abul; 0x5be0cd19ul]


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


private let rec store_blocks (n:nat) (input:bytes{Seq.length input = n * size_block}) : Tot (b:blocks_w{Seq.length b = n}) (decreases n) =
  if n = 0 then Seq.createEmpty #block_w
  else
    let h = Seq.slice input 0 size_block in
    let t = Seq.slice input size_block (n * size_block) in
    let b_w = words_from_be size_block_w h in
    Seq.cons b_w  (store_blocks (n - 1) t)


private let pad_length (len:nat) : Tot (n:nat{(len + n) % size_block = 0}) =
  if (len % size_block) < (size_block - size_len_8 - 1) then size_block - (len % size_block)
  else (2 * size_block) - (len % size_block)


(* Pad the data up to the block length and encode the total length *)
let pad (prevlen:nat) (input:bytes{(Seq.length input) + prevlen < max_input_len_8})  : Tot (output:blocks_w) =

  (* Compute the padding length *)
  let padlen = (pad_length (Seq.length input)) - size_len_8 in

  (* Generate the padding (without the last size_len_8 bytes) *)
  (* Set the first bit of the padding to be a '1' *)
  let padding = Seq.create padlen 0uy in
  let padding = Seq.upd padding 0 0x80uy in

  (* Encode the data length (in bits) as a 64bit big endian integer *)
  let finallen = prevlen + Seq.length input in
  let encodedlen = Endianness.big_bytes size_len_ul_8 (finallen * 8) in

  (* Concatenate the data, padding and encoded length *)
  let output = Seq.append input padding in
  let output = Seq.append output encodedlen in
  let n = Seq.length output / size_block in
  store_blocks n output


let update_compress (hash:hash_w) (block:block_w) : Tot hash_w =
  let hash_1 = shuffle hash block 0 in
  Spec.Lib.map2 (fun x y -> x +%^ y) hash hash_1


(* let update_compress' (hash:hash_w) (block:block_w) : Tot hash_w = *)
  (* let a_0 = Seq.index hash 0 in *)
  (* let b_0 = Seq.index hash 1 in *)
  (* let c_0 = Seq.index hash 2 in *)
  (* let d_0 = Seq.index hash 3 in *)
  (* let e_0 = Seq.index hash 4 in *)
  (* let f_0 = Seq.index hash 5 in *)
  (* let g_0 = Seq.index hash 6 in *)
  (* let h_0 = Seq.index hash 7 in *)

  (* let hash_1 = shuffle hash block 0 in *)

  (* let a_1 = Seq.index hash_1 0 in *)
  (* let b_1 = Seq.index hash_1 1 in *)
  (* let c_1 = Seq.index hash_1 2 in *)
  (* let d_1 = Seq.index hash_1 3 in *)
  (* let e_1 = Seq.index hash_1 4 in *)
  (* let f_1 = Seq.index hash_1 5 in *)
  (* let g_1 = Seq.index hash_1 6 in *)
  (* let h_1 = Seq.index hash_1 7 in *)

  (* let hash = Seq.upd hash 0 (a_0 +%^ a_1) in *)
  (* let hash = Seq.upd hash 1 (b_0 +%^ b_1) in *)
  (* let hash = Seq.upd hash 2 (c_0 +%^ c_1) in *)
  (* let hash = Seq.upd hash 3 (d_0 +%^ d_1) in *)
  (* let hash = Seq.upd hash 4 (e_0 +%^ e_1) in *)
  (* let hash = Seq.upd hash 5 (f_0 +%^ f_1) in *)
  (* let hash = Seq.upd hash 6 (g_0 +%^ g_1) in *)
  (* let hash = Seq.upd hash 7 (h_0 +%^ h_1) in *)
  (* hash *)


let rec update_multi (n:nat) (hash:hash_w) (blocks:blocks_w{Seq.length blocks = n}) : Tot hash_w (decreases n) =
  if n = 0 then hash
  else
    let h = Seq.slice blocks 0 1 in
    let t = Seq.slice blocks 1 n in
    update_multi (n - 1) (update_compress hash (Seq.index h 0)) t


let update_last (hash:hash_w) (prevlen:nat) (input:bytes{(Seq.length input) + prevlen < max_input_len_8}) : Tot hash_w =
  let blocks = pad prevlen input in
  let n = Seq.length blocks in
  update_multi n hash blocks


(* let update_last' (hash:hash_w) (prevlen:nat) (input:bytes{(Seq.length input <= size_block) /\ (Seq.length input) + prevlen < max_input_len_8}) : Tot hash_w = *)

(*   (\* Compute the final length *\) *)
(*   let finallen = prevlen + Seq.length input in *)

(*   (\* Compute the padding length *\) *)
(*   let padlen = pad_length (Seq.length input) - size_len_8 in *)

(*   (\* Create the padding and set the first bit to 1 *\) *)
(*   let padding = Seq.create padlen 0uy in *)
(*   let padding = Seq.upd padding 0 0x80uy in *)

(*   (\* Encode the data length (in bits) as a 64bit big endian integer *\) *)
(*   let encodedlen = Endianness.big_bytes size_len_ul_8 (finallen * 8) in *)

(*   (\* Concatenate ever*\) *)
(*   let last = Seq.append input padding in *)
(*   let last = Seq.append last encodedlen in *)

(*   (\* Get the last block(s) *\) *)
(*   let n = Seq.length last / size_block in *)
(*   let blocks = store_blocks n last in *)

(*   (\* Compress one or two blocks depending on the input length *\) *)
(*   if Seq.length last <= 64 then *)
(*     update_compress hash (Seq.index blocks 0) *)
(*   else update_compress (update_compress hash (Seq.index blocks 0)) (Seq.index blocks 1) *)


let finish (hash:hash_w) : Tot bytes = words_to_be size_hash_w hash


let hash (input:bytes{Seq.length input < max_input_len_8}) : Tot (hash:bytes) =
  let n = Seq.length input / size_block in
  let input_blocks_8 = Seq.slice input 0 (n * size_block) in
  let input_blocks_w = store_blocks n input_blocks_8 in
  (**) assert_norm(List.Tot.length h_0 = size_hash_w);
  let hash = update_multi n (Seq.seq_of_list h_0) input_blocks_w in
  let input_last = Seq.slice input (n * size_block) (Seq.length input) in
  let hash = update_last hash (n * size_block) input_last in
  finish hash


let hash' (input:bytes{Seq.length input < max_input_len_8}) : Tot (hash:bytes) =
  let blocks = pad 0 input in
  let n = Seq.length blocks in
  (**) assert_norm(List.Tot.length h_0 = size_hash_w);
  finish (update_multi n (Seq.seq_of_list h_0) blocks)



//
// Test 1
//

unfold let test_plaintext_1 = [
      0x61uy; 0x62uy; 0x63uy;
]

unfold let test_expected_1 = [
      0xbauy; 0x78uy; 0x16uy; 0xbfuy; 0x8fuy; 0x01uy; 0xcfuy; 0xeauy;
      0x41uy; 0x41uy; 0x40uy; 0xdeuy; 0x5duy; 0xaeuy; 0x22uy; 0x23uy;
      0xb0uy; 0x03uy; 0x61uy; 0xa3uy; 0x96uy; 0x17uy; 0x7auy; 0x9cuy;
      0xb4uy; 0x10uy; 0xffuy; 0x61uy; 0xf2uy; 0x00uy; 0x15uy; 0xaduy
]


//
// Test 2
//

unfold let test_plaintext_2 = [
    0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy;
    0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy;
    0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
    0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
    0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
    0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
    0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy
    ]

unfold let test_expected_2 = [
      0x24uy; 0x8duy; 0x6auy; 0x61uy; 0xd2uy; 0x06uy; 0x38uy; 0xb8uy;
      0xe5uy; 0xc0uy; 0x26uy; 0x93uy; 0x0cuy; 0x3euy; 0x60uy; 0x39uy;
      0xa3uy; 0x3cuy; 0xe4uy; 0x59uy; 0x64uy; 0xffuy; 0x21uy; 0x67uy;
      0xf6uy; 0xecuy; 0xeduy; 0xd4uy; 0x19uy; 0xdbuy; 0x06uy; 0xc1uy
]


//
// Test 3
//

unfold let test_plaintext_3 = [
      0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy;
      0x62uy; 0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
      0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy;
      0x64uy; 0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
      0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy;
      0x66uy; 0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
      0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy;
      0x68uy; 0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
      0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy;
      0x6auy; 0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy;
      0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy;
      0x6cuy; 0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy;
      0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy;
      0x6euy; 0x6fuy; 0x70uy; 0x71uy; 0x72uy; 0x73uy; 0x74uy; 0x75uy
]

unfold let test_expected_3 = [
      0xcfuy; 0x5buy; 0x16uy; 0xa7uy; 0x78uy; 0xafuy; 0x83uy; 0x80uy;
      0x03uy; 0x6cuy; 0xe5uy; 0x9euy; 0x7buy; 0x04uy; 0x92uy; 0x37uy;
      0x0buy; 0x24uy; 0x9buy; 0x11uy; 0xe8uy; 0xf0uy; 0x7auy; 0x51uy;
      0xafuy; 0xacuy; 0x45uy; 0x03uy; 0x7auy; 0xfeuy; 0xe9uy; 0xd1uy

]


//
// Main
//

let test () =
  assert_norm(List.Tot.length test_plaintext_1 = 3);
  assert_norm(List.Tot.length test_expected_1 = 32);
  assert_norm(List.Tot.length test_plaintext_2 = 56);
  assert_norm(List.Tot.length test_expected_2 = 32);
  assert_norm(List.Tot.length test_plaintext_3 = 112);
  assert_norm(List.Tot.length test_expected_3 = 32);
  let test_plaintext_1 = createL test_plaintext_1 in
  let test_expected_1 = createL test_expected_1 in
  let test_plaintext_2 = createL test_plaintext_2 in
  let test_expected_2 = createL test_expected_2 in
  let test_plaintext_3 = createL test_plaintext_3 in
  let test_expected_3 = createL test_expected_3 in

  (hash test_plaintext_1 = test_expected_1) && (hash' test_plaintext_1 = test_expected_1) &&
  (hash test_plaintext_2 = test_expected_2) && (hash' test_plaintext_2 = test_expected_2) &&
  (hash test_plaintext_3 = test_expected_3) && (hash' test_plaintext_3 = test_expected_3)
