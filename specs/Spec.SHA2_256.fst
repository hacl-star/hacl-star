module Spec.SHA2_256

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32

open Spec.Loops
open Spec.Lib

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
let size_ws_w = size_k_w
let size_len_8 = 8
let size_len_ul_8 = 8ul
let max_input_len_8 = pow2 61

type bytes = m:seq UInt8.t
type word = Word.t
type hash_w = m:seq word {length m = size_hash_w}
type k_w = m:seq word {length m = size_k_w}
type ws_w = m:seq word {length m = size_ws_w}
type block_w = m:seq word {length m = size_block_w}
type blocks_w = m:seq block_w
type counter = nat

(* Define word based operators *)
let words_to_be = Spec.Lib.uint32s_to_be
let words_from_be = Spec.Lib.uint32s_from_be
let word_logxor = Word.logxor
let word_logand = Word.logand
let word_logor = Word.logor
let word_lognot = Word.lognot
let word_shift_right = Word.shift_right



let rotate_right (a:word) (s:word {0 < v s /\ v s<32}) : Tot word =
  ((a >>^ s) |^ (a <<^ (32ul -^ s)))

(* [FIPS 180-4] section 4.1.2 *)
val _Ch: x:word -> y:word -> z:word -> Tot word
let _Ch x y z = word_logxor (word_logand x y) (word_logand (word_lognot x) z)

val _Maj: x:word -> y:word -> z:word -> Tot word
let _Maj x y z = word_logxor (word_logand x y) (word_logxor (word_logand x z) (word_logand y z))

val _Sigma0: x:word -> Tot word
let _Sigma0 x = word_logxor (rotate_right x 2ul) (word_logxor (rotate_right x 13ul) (rotate_right x 22ul))

val _Sigma1: x:word -> Tot word
let _Sigma1 x = word_logxor (rotate_right x 6ul) (word_logxor (rotate_right x 11ul) (rotate_right x 25ul))

val _sigma0: x:word -> Tot word
let _sigma0 x = word_logxor (rotate_right x 7ul) (word_logxor (rotate_right x 18ul) (word_shift_right x 3ul))

val _sigma1: x:word -> Tot word
let _sigma1 x = word_logxor (rotate_right x 17ul) (word_logxor (rotate_right x 19ul) (word_shift_right x 10ul))


let k : k_w =
  Seq.Create.create_64
  0x428a2f98ul 0x71374491ul 0xb5c0fbcful 0xe9b5dba5ul
  0x3956c25bul 0x59f111f1ul 0x923f82a4ul 0xab1c5ed5ul
  0xd807aa98ul 0x12835b01ul 0x243185beul 0x550c7dc3ul
  0x72be5d74ul 0x80deb1feul 0x9bdc06a7ul 0xc19bf174ul
  0xe49b69c1ul 0xefbe4786ul 0x0fc19dc6ul 0x240ca1ccul
  0x2de92c6ful 0x4a7484aaul 0x5cb0a9dcul 0x76f988daul
  0x983e5152ul 0xa831c66dul 0xb00327c8ul 0xbf597fc7ul
  0xc6e00bf3ul 0xd5a79147ul 0x06ca6351ul 0x14292967ul
  0x27b70a85ul 0x2e1b2138ul 0x4d2c6dfcul 0x53380d13ul
  0x650a7354ul 0x766a0abbul 0x81c2c92eul 0x92722c85ul
  0xa2bfe8a1ul 0xa81a664bul 0xc24b8b70ul 0xc76c51a3ul
  0xd192e819ul 0xd6990624ul 0xf40e3585ul 0x106aa070ul
  0x19a4c116ul 0x1e376c08ul 0x2748774cul 0x34b0bcb5ul
  0x391c0cb3ul 0x4ed8aa4aul 0x5b9cca4ful 0x682e6ff3ul
  0x748f82eeul 0x78a5636ful 0x84c87814ul 0x8cc70208ul
  0x90befffaul 0xa4506cebul 0xbef9a3f7ul 0xc67178f2ul


let h_0 : hash_w =
  Seq.Create.create_8
  0x6a09e667ul 0xbb67ae85ul 0x3c6ef372ul 0xa54ff53aul
  0x510e527ful 0x9b05688cul 0x1f83d9abul 0x5be0cd19ul


let rec ws (b:block_w) (t:counter{t < size_k_w}) : Tot word =
  if t < size_block_w then b.[t]
  else
    let t16 = ws b (t - 16) in
    let t15 = ws b (t - 15) in
    let t7  = ws b (t - 7) in
    let t2  = ws b (t - 2) in

    let s1 = _sigma1 t2 in
    let s0 = _sigma0 t15 in
    (s1 +%^ (t7 +%^ (s0 +%^ t16)))


let shuffle_core (block:block_w) (hash:hash_w) (t:counter{t < size_k_w}) : Tot hash_w =
  let a = hash.[0] in
  let b = hash.[1] in
  let c = hash.[2] in
  let d = hash.[3] in
  let e = hash.[4] in
  let f = hash.[5] in
  let g = hash.[6] in
  let h = hash.[7] in

  (**) assert(Seq.length k = size_k_w);
  let t1 = h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ k.[t] +%^ ws block t in
  let t2 = (_Sigma0 a) +%^ (_Maj a b c) in

  (**) assert(t < Seq.length k);
  Seq.Create.create_8 (t1 +%^ t2) a b c (d +%^ t1) e f g


let shuffle (hash:hash_w) (block:block_w) : Tot hash_w =
  Spec.Loops.repeat_range_spec 0 size_ws_w (shuffle_core block) hash


let update (hash:hash_w) (block:bytes{length block = size_block}) : Tot hash_w =
  let b = words_from_be size_block_w block in
  let hash_1 = shuffle hash b in
  Spec.Lib.map2 (fun x y -> x +%^ y) hash hash_1


let rec update_multi (hash:hash_w) (blocks:bytes{length blocks % size_block = 0}) : Tot hash_w (decreases (Seq.length blocks)) =
  if Seq.length blocks = 0 then hash
  else
    let (block,rem) = Seq.split blocks size_block in
    let hash = update hash block in
    update_multi hash rem


let pad0_length (len:nat) : Tot (n:nat{(len + 1 + n + size_len_8) % size_block = 0}) =
  (size_block - (len + size_len_8 + 1)) % size_block


let pad (prevlen:nat{prevlen % size_block = 0}) (len:nat{prevlen + len < max_input_len_8}) : Tot (b:bytes{(length b + len) % size_block = 0}) =
  let tlen = prevlen + len in
  let firstbyte = Seq.create 1 0x80uy in
  let zeros = Seq.create (pad0_length len) 0uy in
  let encodedlen = Endianness.big_bytes size_len_ul_8 (tlen * 8) in
  firstbyte @| zeros @| encodedlen


let update_last (hash:hash_w) (prevlen:nat{prevlen % size_block = 0}) (input:bytes{(Seq.length input) + prevlen < max_input_len_8}) : Tot hash_w =
  let blocks = pad prevlen (Seq.length input) in
  update_multi hash (input @| blocks)


let finish (hashw:hash_w) : Tot (hash:bytes{length hash = size_hash}) = words_to_be size_hash_w hashw


let hash (input:bytes{Seq.length input < max_input_len_8}) : Tot (hash:bytes{length hash = size_hash}) =
  let n = Seq.length input / size_block in
  let (bs,l) = Seq.split input (n * size_block) in
  let hash = update_multi h_0 bs in
  let hash = update_last hash (n * size_block) l in
  finish hash


let hash' (input:bytes{Seq.length input < max_input_len_8}) : Tot (hash:bytes{length hash = size_hash}) =
  let blocks = pad 0 (Seq.length input) in
  finish (update_multi h_0 (input @| blocks))


#reset-options "--max_fuel 0 --z3rlimit 10"

let lemma_modulo (l:nat) (s:nat{s <> 0 /\ l >= s /\ l % s = 0}) : Lemma
  (ensures ((l - s) % s = 0)) =
Math.Lemmas.lemma_mod_plus (l - s) 1 s

#reset-options "--max_fuel 0 --z3rlimit 20"

val lemma_update_update_multi: (h0:hash_w) -> (blocks:bytes{Seq.length blocks >= size_block /\ Seq.length blocks % size_block = 0}) -> Lemma
  (ensures  (let (block,rem) = Seq.split blocks size_block in
             let h1 = update h0 block in
             let h2 = update_multi h1 rem in
             h2 == update_multi h0 blocks))

#reset-options "--max_fuel 1 --z3rlimit 100"

let lemma_update_update_multi h0 blocks =
  let (block,rem) = Seq.split blocks size_block in
  assert(size_block <> 0);
  assert(length blocks >= size_block);
  assert(length blocks % size_block = 0);
  lemma_modulo (length blocks) size_block;
  assert((length blocks - size_block) % size_block = 0);
  assert(Seq.length rem  % size_block = 0);
  let h1 = update h0 block in
  let h2 = update_multi h1 rem in
  Seq.lemma_eq_intro h2 (update_multi h0 blocks)


#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_update_multi_extend: (h0:hash_w) -> (block:bytes{Seq.length block = size_block}) -> (blocks:bytes{Seq.length blocks % size_block = 0}) -> Lemma
  (ensures (update_multi (update h0 block) blocks == update_multi h0 (block @| blocks)))

let lemma_update_multi_extend h0 block blocks =
  lemma_update_update_multi h0 (block @| blocks);
  let a,b = Seq.split (block @| blocks) size_block in
  Seq.lemma_eq_intro a block;
  Seq.lemma_eq_intro b blocks;
  Seq.lemma_eq_intro (update_multi (update h0 block) blocks) (update_multi h0 (block @| blocks))


#reset-options "--max_fuel 1 --z3rlimit 100 --using_facts_from FStar --using_facts_from Prims --using_facts_from Spec.SHA2_256"

let lemma_update_multi_empty (h:hash_w) (empty:bytes{Seq.length empty = 0}) : Lemma
  (ensures (update_multi h empty == h)) = ()

let update_multi_one (h:hash_w) (b:bytes{Seq.length b = size_block}) : Lemma
  (ensures (update_multi h b == update h b)) =
  let block, rem = Seq.split b size_block in
  assert (Seq.length rem == 0);
  lemma_update_multi_empty (update h b) rem

val update_multi_append:
  hash:hash_w ->
  blocks1:bytes{length blocks1 % size_block = 0} ->
  blocks2:bytes{length blocks2 % size_block = 0} ->
  Lemma
    (requires True)
    (ensures (update_multi (update_multi hash blocks1) blocks2 ==
              update_multi hash (blocks1 @| blocks2)))
    (decreases (length blocks1))
let rec update_multi_append hash blocks1 blocks2 =
  if Seq.length blocks1 = 0 then
    begin
    lemma_update_multi_empty hash blocks1;
    Seq.append_empty_l blocks1;
    Seq.lemma_eq_intro (blocks1 @| blocks2) blocks2
    end
  else
    begin
    (*
      update_multi (update_multi hash blocks1) blocks2
      == update_multi_def hash blocks1
      update_multi (update_multi (update hash b) blocks1') blocks2
      == update_multi_append (update hash b) blocks1' blocks2
      update_multi (update hash b) (blocks1' @| blocks2)
      == update_multi_def hash (blocks1 @| blocks2)
      update_multi hash (blocks1 @| blocks2)
    *)
    let b , blocks1' = Seq.split_eq blocks1 size_block in
    let b', blocks12 = Seq.split_eq (blocks1 @| blocks2) size_block in
    Seq.append_assoc b blocks1' blocks2;
    Seq.lemma_append_inj b (blocks1' @| blocks2) b' blocks12;
    update_multi_append (update hash b) blocks1' blocks2
    end

val update_update_multi_append:
  hash:hash_w ->
  blocks:bytes{length blocks % size_block = 0} ->
  b:bytes{length b = size_block} ->
  Lemma
    (update (update_multi hash blocks) b == update_multi hash (blocks @| b))
let update_update_multi_append hash blocks b =
  update_multi_append hash blocks b;
  update_multi_one (update_multi hash blocks) b

#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_hash_all_prepend_block: (block:bytes{Seq.length block = size_block}) -> (msg:bytes{Seq.length block + Seq.length msg < max_input_len_8}) -> Lemma
  (ensures (let n = Seq.length msg / size_block in
            let (msg_blocks,msg_last) = Seq.split msg (n * size_block) in
            let hash0 = update h_0 block in
            let hash1 = update_multi hash0 msg_blocks in
            let hash2 = update_last hash1 (size_block + (n * size_block)) msg_last in
            finish hash2 == hash (block @| msg)))

let lemma_hash_all_prepend_block block msg =
  let n = Seq.length msg / size_block in
  let (msg_blocks,msg_last) = Seq.split msg (n * size_block) in
  let hash1 = update h_0 block in
  let hash2 = update_multi hash1 msg_blocks in
  let hash3 = update_last hash2 (size_block + (n * size_block)) msg_last in
  let hash4 = finish hash3 in
  lemma_update_multi_extend h_0 block msg_blocks;
  lemma_eq_intro (block @| msg) (block @| msg_blocks @| msg_last);
  assert(hash2 == update_multi h_0 (block @| msg_blocks));
  let banana = block @| msg in
  let n' = Seq.length banana / size_block in
  let (msg_blocks',msg_last') = Seq.split banana (n' * size_block) in
  Math.Lemmas.distributivity_add_left n 1 size_block;
  assert(n' == n + 1);
  Seq.lemma_eq_intro (msg_last') (msg_last);
  Seq.lemma_eq_intro (msg_blocks') (block @| msg_blocks)


#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_hash_single_prepend_block: (block:bytes{Seq.length block = size_block}) -> (msg:bytes{Seq.length msg = size_hash}) -> Lemma
  (ensures ((* let n = Seq.length msg / size_block in *)
            (* let (msg_blocks,msg_last) = Seq.split msg (n * size_block) in *)
            let hash0 = update h_0 block in
            let hash1 = update_last hash0 (size_block) msg in
            finish hash1 == hash (block @| msg)))

let lemma_hash_single_prepend_block block msg =
  let n = Seq.length msg / size_block in
  assert_norm(n = 0);
  let (msg_blocks,msg_last) = Seq.split msg (n * size_block) in
  lemma_eq_intro msg_blocks createEmpty;
  lemma_eq_intro msg_last msg;
  let hash1 = update h_0 block in
  let hash2 = update_multi hash1 msg_blocks in // This is 0
  assert(Seq.length msg_blocks = 0);
  lemma_update_multi_empty hash1 msg_blocks;
  assert(update_multi hash1 msg_blocks == hash1);
  Seq.lemma_eq_intro (update h_0 block) (update_multi hash1 msg_blocks);
  assert(hash2 == update h_0 block);
  let hash3 = update_last hash2 (size_block + (n * size_block)) msg_last in
  let hash4 = finish hash3 in
  lemma_update_multi_extend h_0 block msg_blocks;
  lemma_eq_intro (block @| msg) (block @| msg_blocks @| msg_last);
  assert(hash2 == update_multi h_0 (block @| msg_blocks));
  let banana = block @| msg in
  let n' = Seq.length banana / size_block in
  let (msg_blocks',msg_last') = Seq.split banana (n' * size_block) in
  Math.Lemmas.distributivity_add_left n 1 size_block;
  assert(n' == n + 1);
  Seq.lemma_eq_intro (msg_last') (msg_last);
  Seq.lemma_eq_intro (msg_blocks') (block @| msg_blocks)



//
// Test 1
//

let test_plaintext1 = [
  0x61uy; 0x62uy; 0x63uy;
]

let test_expected1 = [
  0xbauy; 0x78uy; 0x16uy; 0xbfuy; 0x8fuy; 0x01uy; 0xcfuy; 0xeauy;
  0x41uy; 0x41uy; 0x40uy; 0xdeuy; 0x5duy; 0xaeuy; 0x22uy; 0x23uy;
  0xb0uy; 0x03uy; 0x61uy; 0xa3uy; 0x96uy; 0x17uy; 0x7auy; 0x9cuy;
  0xb4uy; 0x10uy; 0xffuy; 0x61uy; 0xf2uy; 0x00uy; 0x15uy; 0xaduy
]

//
// Test 2
//

let test_plaintext2 = []

let test_expected2 = [
  0xe3uy; 0xb0uy; 0xc4uy; 0x42uy; 0x98uy; 0xfcuy; 0x1cuy; 0x14uy;
  0x9auy; 0xfbuy; 0xf4uy; 0xc8uy; 0x99uy; 0x6fuy; 0xb9uy; 0x24uy;
  0x27uy; 0xaeuy; 0x41uy; 0xe4uy; 0x64uy; 0x9buy; 0x93uy; 0x4cuy;
  0xa4uy; 0x95uy; 0x99uy; 0x1buy; 0x78uy; 0x52uy; 0xb8uy; 0x55uy
]

//
// Test 3
//

let test_plaintext3 = [
  0x61uy; 0x62uy; 0x63uy; 0x64uy; 0x62uy; 0x63uy; 0x64uy; 0x65uy;
  0x63uy; 0x64uy; 0x65uy; 0x66uy; 0x64uy; 0x65uy; 0x66uy; 0x67uy;
  0x65uy; 0x66uy; 0x67uy; 0x68uy; 0x66uy; 0x67uy; 0x68uy; 0x69uy;
  0x67uy; 0x68uy; 0x69uy; 0x6auy; 0x68uy; 0x69uy; 0x6auy; 0x6buy;
  0x69uy; 0x6auy; 0x6buy; 0x6cuy; 0x6auy; 0x6buy; 0x6cuy; 0x6duy;
  0x6buy; 0x6cuy; 0x6duy; 0x6euy; 0x6cuy; 0x6duy; 0x6euy; 0x6fuy;
  0x6duy; 0x6euy; 0x6fuy; 0x70uy; 0x6euy; 0x6fuy; 0x70uy; 0x71uy
]

let test_expected3 = [
  0x24uy; 0x8duy; 0x6auy; 0x61uy; 0xd2uy; 0x06uy; 0x38uy; 0xb8uy;
  0xe5uy; 0xc0uy; 0x26uy; 0x93uy; 0x0cuy; 0x3euy; 0x60uy; 0x39uy;
  0xa3uy; 0x3cuy; 0xe4uy; 0x59uy; 0x64uy; 0xffuy; 0x21uy; 0x67uy;
  0xf6uy; 0xecuy; 0xeduy; 0xd4uy; 0x19uy; 0xdbuy; 0x06uy; 0xc1uy
]


//
// Test 4
//

let test_plaintext4 = [
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

let test_expected4 = [
  0xcfuy; 0x5buy; 0x16uy; 0xa7uy; 0x78uy; 0xafuy; 0x83uy; 0x80uy;
  0x03uy; 0x6cuy; 0xe5uy; 0x9euy; 0x7buy; 0x04uy; 0x92uy; 0x37uy;
  0x0buy; 0x24uy; 0x9buy; 0x11uy; 0xe8uy; 0xf0uy; 0x7auy; 0x51uy;
  0xafuy; 0xacuy; 0x45uy; 0x03uy; 0x7auy; 0xfeuy; 0xe9uy; 0xd1uy
]

//
// Test 5
//

let test_expected5 = [
  0xcduy; 0xc7uy; 0x6euy; 0x5cuy; 0x99uy; 0x14uy; 0xfbuy; 0x92uy;
  0x81uy; 0xa1uy; 0xc7uy; 0xe2uy; 0x84uy; 0xd7uy; 0x3euy; 0x67uy;
  0xf1uy; 0x80uy; 0x9auy; 0x48uy; 0xa4uy; 0x97uy; 0x20uy; 0x0euy;
  0x04uy; 0x6duy; 0x39uy; 0xccuy; 0xc7uy; 0x11uy; 0x2cuy; 0xd0uy
]


//
// Main
//

let test () =
  assert_norm(List.Tot.length test_plaintext1 = 3);
  assert_norm(List.Tot.length test_expected1 = 32);
//  assert_norm(List.Tot.length test_plaintext2 = 0);
  assert_norm(List.Tot.length test_expected2 = 32);
  assert_norm(List.Tot.length test_plaintext3 = 56);
  assert_norm(List.Tot.length test_expected3 = 32);
  assert_norm(List.Tot.length test_plaintext4 = 112);
  assert_norm(List.Tot.length test_expected4 = 32);
  assert_norm(List.Tot.length test_expected5 = 32);
  let test_plaintext1 = createL test_plaintext1 in
  let test_expected1 = createL test_expected1 in
  let test_plaintext2 = createL test_plaintext2 in
  let test_expected2 = createL test_expected2 in
  let test_plaintext3 = createL test_plaintext3 in
  let test_expected3 = createL test_expected3 in
  let test_plaintext4 = createL test_plaintext4 in
  let test_expected4 = createL test_expected4 in
//  let test_plaintext5 = create 1000000 0x61uy in
//  let test_expected5 = createL test_expected5 in

  (hash test_plaintext1 = test_expected1) && (hash' test_plaintext1 = test_expected1) &&
  (hash test_plaintext2 = test_expected2) && (hash' test_plaintext2 = test_expected2) &&
  (hash test_plaintext3 = test_expected3) && (hash' test_plaintext3 = test_expected3) &&
  (hash test_plaintext4 = test_expected4) && (hash' test_plaintext4 = test_expected4) // &&
//  (hash test_plaintext5 = test_expected5) && (hash' test_plaintext5 = test_expected5)
