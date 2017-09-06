module Spec.SHA2_512

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt64

open Spec.Loops
open Spec.Lib

module Word = FStar.UInt64


val pow2_values: x:nat -> Lemma
  (requires True)
  (ensures (let p = pow2 x in
   match x with
   | 61 -> p=2305843009213693952
   | 125 -> p=42535295865117307932921825928971026432
   | _  -> True))
  [SMTPat (pow2 x)]
let pow2_values x =
   match x with
   | 61 -> assert_norm (pow2 61 == 2305843009213693952)
   | 125 -> assert_norm (pow2 125 == 42535295865117307932921825928971026432)
   | _  -> ()



#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 25"


//
// SHA-512
//

(* Define algorithm parameters *)
let size_word = 8
let size_hash_w = 8
let size_block_w = 16
let size_hash = size_word * size_hash_w
let size_block = size_word * size_block_w
let size_k_w = 80
let size_ws_w = size_k_w
let size_len_8 = 16
let size_len_ul_8 = 16ul
let max_input_len_8 = pow2 125

type bytes = m:seq UInt8.t
type word = Word.t
type hash_w = m:seq word {length m = size_hash_w}
type k_w = m:seq word {length m = size_k_w}
type ws_w = m:seq word {length m = size_ws_w}
type block_w = m:seq word {length m = size_block_w}
type blocks_w = m:seq block_w
type counter = nat

(* Define word based operators *)
let words_to_be = Spec.Lib.uint64s_to_be
let words_from_be = Spec.Lib.uint64s_from_be
let word_logxor = Word.logxor
let word_logand = Word.logand
let word_logor = Word.logor
let word_lognot = Word.lognot
let word_shift_right = Word.shift_right
let word_add_mod = Word.add_mod



let rotate_right (a:word) (s:UInt32.t{0 < UInt32.v s /\ UInt32.v s < 64}) : Tot word =
  Word.((a >>^ s) |^ (a <<^ (UInt32.sub 64ul s)))

val _Ch: x:word -> y:word -> z:word -> Tot word
let _Ch x y z = word_logxor (word_logand x y) (word_logand (word_lognot x) z)

val _Maj: x:word -> y:word -> z:word -> Tot word
let _Maj x y z = word_logxor (word_logand x y) (word_logxor (word_logand x z) (word_logand y z))

val _Sigma0: x:word -> Tot word
let _Sigma0 x = word_logxor (rotate_right x 28ul) (word_logxor (rotate_right x 34ul) (rotate_right x 39ul))

val _Sigma1: x:word -> Tot word
let _Sigma1 x = word_logxor (rotate_right x 14ul) (word_logxor (rotate_right x 18ul) (rotate_right x 41ul))

val _sigma0: x:word -> Tot word
let _sigma0 x = word_logxor (rotate_right x 1ul) (word_logxor (rotate_right x 8ul) (word_shift_right x 7ul))

val _sigma1: x:word -> Tot word
let _sigma1 x = word_logxor (rotate_right x 19ul) (word_logxor (rotate_right x 61ul) (word_shift_right x 6ul))


let k : k_w =
  Seq.Create.create_80
  0x428a2f98d728ae22uL 0x7137449123ef65cduL 0xb5c0fbcfec4d3b2fuL 0xe9b5dba58189dbbcuL
  0x3956c25bf348b538uL 0x59f111f1b605d019uL 0x923f82a4af194f9buL 0xab1c5ed5da6d8118uL
  0xd807aa98a3030242uL 0x12835b0145706fbeuL 0x243185be4ee4b28cuL 0x550c7dc3d5ffb4e2uL
  0x72be5d74f27b896fuL 0x80deb1fe3b1696b1uL 0x9bdc06a725c71235uL 0xc19bf174cf692694uL
  0xe49b69c19ef14ad2uL 0xefbe4786384f25e3uL 0x0fc19dc68b8cd5b5uL 0x240ca1cc77ac9c65uL
  0x2de92c6f592b0275uL 0x4a7484aa6ea6e483uL 0x5cb0a9dcbd41fbd4uL 0x76f988da831153b5uL
  0x983e5152ee66dfabuL 0xa831c66d2db43210uL 0xb00327c898fb213fuL 0xbf597fc7beef0ee4uL
  0xc6e00bf33da88fc2uL 0xd5a79147930aa725uL 0x06ca6351e003826fuL 0x142929670a0e6e70uL
  0x27b70a8546d22ffcuL 0x2e1b21385c26c926uL 0x4d2c6dfc5ac42aeduL 0x53380d139d95b3dfuL
  0x650a73548baf63deuL 0x766a0abb3c77b2a8uL 0x81c2c92e47edaee6uL 0x92722c851482353buL
  0xa2bfe8a14cf10364uL 0xa81a664bbc423001uL 0xc24b8b70d0f89791uL 0xc76c51a30654be30uL
  0xd192e819d6ef5218uL 0xd69906245565a910uL 0xf40e35855771202auL 0x106aa07032bbd1b8uL
  0x19a4c116b8d2d0c8uL 0x1e376c085141ab53uL 0x2748774cdf8eeb99uL 0x34b0bcb5e19b48a8uL
  0x391c0cb3c5c95a63uL 0x4ed8aa4ae3418acbuL 0x5b9cca4f7763e373uL 0x682e6ff3d6b2b8a3uL
  0x748f82ee5defb2fcuL 0x78a5636f43172f60uL 0x84c87814a1f0ab72uL 0x8cc702081a6439ecuL
  0x90befffa23631e28uL 0xa4506cebde82bde9uL 0xbef9a3f7b2c67915uL 0xc67178f2e372532buL
  0xca273eceea26619cuL 0xd186b8c721c0c207uL 0xeada7dd6cde0eb1euL 0xf57d4f7fee6ed178uL
  0x06f067aa72176fbauL 0x0a637dc5a2c898a6uL 0x113f9804bef90daeuL 0x1b710b35131c471buL
  0x28db77f523047d84uL 0x32caab7b40c72493uL 0x3c9ebe0a15c9bebcuL 0x431d67c49c100d4cuL
  0x4cc5d4becb3e42b6uL 0x597f299cfc657e2auL 0x5fcb6fab3ad6faecuL 0x6c44198c4a475817uL


let h_0 : hash_w =
  Seq.Create.create_8
  0x6a09e667f3bcc908uL 0xbb67ae8584caa73buL 0x3c6ef372fe94f82buL 0xa54ff53a5f1d36f1uL
  0x510e527fade682d1uL 0x9b05688c2b3e6c1fuL 0x1f83d9abfb41bd6buL 0x5be0cd19137e2179uL


let rec ws (b:block_w) (t:counter{t < size_k_w}) : Tot word =
  if t < size_block_w then b.[t]
  else
    let t16 = ws b (t - 16) in
    let t15 = ws b (t - 15) in
    let t7  = ws b (t - 7) in
    let t2  = ws b (t - 2) in

    let s1 = _sigma1 t2 in
    let s0 = _sigma0 t15 in
    FStar.UInt64.(s1 +%^ (t7 +%^ (s0 +%^ t16)))


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
  let t1 = h +%^ (_Sigma1 e) +%^ (_Ch e f g) +%^ (Seq.index k t) +%^ ws block t in
  let t2 = ((_Sigma0 a) +%^ (_Maj a b c)) in

  (**) assert(t < Seq.length k);
  Seq.Create.create_8 (t1 +%^ t2) a b c (d +%^ t1) e f g


let shuffle (hash:hash_w) (block:block_w) : Tot hash_w =
  Spec.Loops.repeat_range_spec 0 size_ws_w (shuffle_core block) hash


let update (hash:hash_w) (block:bytes{length block = size_block}) : Tot hash_w =
  let b = words_from_be size_block_w block in
  let hash_1 = shuffle hash b in
  Spec.Loops.seq_map2 (fun x y -> x +%^ y) hash hash_1


let rec update_multi (hash:hash_w) (blocks:bytes{length blocks % size_block = 0}) : Tot hash_w (decreases (Seq.length blocks)) =
  if Seq.length blocks = 0 then hash
  else
    let (block,rem) = Seq.split blocks size_block in
    let hash = update hash block in
    update_multi hash rem


let pad0_length (len:nat) : Tot (n:nat{(len + 1 + n + size_len_8) % size_block = 0}) =
  (2 * size_block - (len + size_len_8 + 1)) % size_block


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
  let padding = pad 0 (Seq.length input) in
  finish (update_multi h_0 (input @| padding))


#reset-options "--max_fuel 0 --z3rlimit 10"

let lemma_update_multi_partial (h0:hash_w) (blocks:bytes{Seq.length blocks >= size_block /\ Seq.length blocks % size_block = 0}) : Lemma
  (ensures  (let (block,rem) = Seq.split blocks size_block in
             Seq.length blocks = Seq.length (block @| rem) /\
             update_multi h0 blocks == update_multi h0 (block @| rem))) =
  let (block,rem) = Seq.split blocks size_block in
  lemma_eq_intro blocks (block @| rem)


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


#reset-options "--max_fuel 1 --z3rlimit 100 --using_facts_from FStar --using_facts_from Prims --using_facts_from Spec.SHA2_512"

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


#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_eq_incremental: (h0:hash_w) -> (a:bytes{Seq.length a % size_block = 0}) -> (b:bytes{Seq.length b % size_block = 0}) -> (c:bytes{Seq.length c % size_block = 0 /\ c = a @| b}) -> (last:bytes{Seq.length c + Seq.length last < max_input_len_8}) -> Lemma
  (ensures  ((finish (update_last (update_multi h0 (a @| b)) (Seq.length a + Seq.length b) last))
            == finish (update_last (update_multi h0 c) (Seq.length c) last)))

let lemma_eq_incremental h0 a b c last = ()


(* #reset-options "--max_fuel 0 --z3rlimit 10" *)

(* val lemma_eq_incremental2: (h0:hash_w) -> (a:bytes{Seq.length a % size_block = 0}) -> (b:bytes{Seq.length b % size_block = 0}) -> (c:bytes{Seq.length c % size_block = 0 /\ c = a @| b}) -> (last:bytes{Seq.length c + Seq.length last < max_input_len_8}) -> Lemma *)
(*   (ensures  ((finish (update_last (update_multi h0 (a @| b)) (Seq.length a + Seq.length b) last)) *)
(*             == hash (a @| b @| last))) *)

(* let lemma_eq_incremental2 h0 a b c last = *)
(*   lemma_eq_intro (c @| last) (a @| b @| last); *)
(*   lemma_eq_incremental h0 a b (a @| b) last *)


#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_hash_def: (h0:hash_w) -> (input:bytes{Seq.length input < max_input_len_8}) -> Lemma
  (ensures  (let n = Seq.length input / size_block in
            let (blocks,last) = Seq.split input (n * size_block) in
            let hash1 = update_multi h_0 blocks in
            let hash2 = update_last hash1 (n * size_block) last in
            finish hash2 == hash input))

let lemma_hash_def h0 input = ()


#reset-options "--max_fuel 0 --z3rlimit 10"

val lemma_hash_def2: (h0:hash_w) -> (input:bytes{Seq.length input < max_input_len_8}) -> Lemma
  (ensures  (let n = Seq.length input / size_block in
            let (blocks,last) = Seq.split input (n * size_block) in
            let hash1 = update_multi h_0 blocks in
            let hash2 = update_last hash1 (n * size_block) last in
            finish hash2 == hash input /\ finish hash2 == hash (blocks @| last)))

let lemma_hash_def2 h0 input =
  let n = Seq.length input / size_block in
  let (blocks,last) = Seq.split input (n * size_block) in
  lemma_eq_intro input (blocks @| last);
  lemma_hash_def h0 (blocks @| last)

(* #reset-options "--max_fuel 0 --z3rlimit 10" *)

(* val lemma_hash_eq_incremental: (h0:hash_w) -> (block:bytes{Seq.length block = size_block}) -> (msg:bytes{Seq.length block + Seq.length msg < max_input_len_8}) -> Lemma *)
(*   (ensures (let n = Seq.length msg / size_block in *)
(*             let (msg_blocks, msg_last) = Seq.split msg (n * size_block) in *)
(*             (hash (block @| msg) == hash (block @| msg_blocks @| msg_last)))) *)

(* let lemma_hash_eq_incremental h0 block msg = *)
(*   let n = Seq.length msg / size_block in *)
(*   let (msg_blocks,msg_last) = Seq.split msg (n * size_block) in *)
(*   let hash1 = update h_0 block in *)
(*   let hash2 = update_multi hash1 msg_blocks in *)
(*   lemma_update_multi_extend h_0 block msg_blocks; *)
(*   lemma_eq_intro (block @| msg) (block @| msg_blocks @| msg_last) *)


#reset-options "--max_fuel 0 --z3rlimit 100"

val lemma_hash_prepend: (h0:hash_w) -> (block:bytes{Seq.length block = size_block}) -> (msg:bytes{Seq.length block + Seq.length msg < max_input_len_8}) -> Lemma
  (ensures (let n = Seq.length msg / size_block in
            let (msg_blocks,msg_last) = Seq.split msg (n * size_block) in
            let hash0 = update h_0 block in
            let hash1 = update_multi hash0 msg_blocks in
            let hash2 = update_last hash1 (size_block + (n * size_block)) msg_last in
            finish hash2 == hash (block @| msg)))

let lemma_hash_prepend h0 block msg =
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



//
// Test 1
//

let test_plaintext1 = [
  0x61uy; 0x62uy; 0x63uy;
]

let test_expected1 = [
  0xdduy; 0xafuy; 0x35uy; 0xa1uy; 0x93uy; 0x61uy; 0x7auy; 0xbauy;
  0xccuy; 0x41uy; 0x73uy; 0x49uy; 0xaeuy; 0x20uy; 0x41uy; 0x31uy;
  0x12uy; 0xe6uy; 0xfauy; 0x4euy; 0x89uy; 0xa9uy; 0x7euy; 0xa2uy;
  0x0auy; 0x9euy; 0xeeuy; 0xe6uy; 0x4buy; 0x55uy; 0xd3uy; 0x9auy;
  0x21uy; 0x92uy; 0x99uy; 0x2auy; 0x27uy; 0x4fuy; 0xc1uy; 0xa8uy;
  0x36uy; 0xbauy; 0x3cuy; 0x23uy; 0xa3uy; 0xfeuy; 0xebuy; 0xbduy;
  0x45uy; 0x4duy; 0x44uy; 0x23uy; 0x64uy; 0x3cuy; 0xe8uy; 0x0euy;
  0x2auy; 0x9auy; 0xc9uy; 0x4fuy; 0xa5uy; 0x4cuy; 0xa4uy; 0x9fuy
]


//
// Test 2
//

let test_plaintext2 = []

let test_expected2 = [
  0xcfuy; 0x83uy; 0xe1uy; 0x35uy; 0x7euy; 0xefuy; 0xb8uy; 0xbduy;
  0xf1uy; 0x54uy; 0x28uy; 0x50uy; 0xd6uy; 0x6duy; 0x80uy; 0x07uy;
  0xd6uy; 0x20uy; 0xe4uy; 0x05uy; 0x0buy; 0x57uy; 0x15uy; 0xdcuy;
  0x83uy; 0xf4uy; 0xa9uy; 0x21uy; 0xd3uy; 0x6cuy; 0xe9uy; 0xceuy;
  0x47uy; 0xd0uy; 0xd1uy; 0x3cuy; 0x5duy; 0x85uy; 0xf2uy; 0xb0uy;
  0xffuy; 0x83uy; 0x18uy; 0xd2uy; 0x87uy; 0x7euy; 0xecuy; 0x2fuy;
  0x63uy; 0xb9uy; 0x31uy; 0xbduy; 0x47uy; 0x41uy; 0x7auy; 0x81uy;
  0xa5uy; 0x38uy; 0x32uy; 0x7auy; 0xf9uy; 0x27uy; 0xdauy; 0x3euy
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
  0x20uy; 0x4auy; 0x8fuy; 0xc6uy; 0xdduy; 0xa8uy; 0x2fuy; 0x0auy;
  0x0cuy; 0xeduy; 0x7buy; 0xebuy; 0x8euy; 0x08uy; 0xa4uy; 0x16uy;
  0x57uy; 0xc1uy; 0x6euy; 0xf4uy; 0x68uy; 0xb2uy; 0x28uy; 0xa8uy;
  0x27uy; 0x9buy; 0xe3uy; 0x31uy; 0xa7uy; 0x03uy; 0xc3uy; 0x35uy;
  0x96uy; 0xfduy; 0x15uy; 0xc1uy; 0x3buy; 0x1buy; 0x07uy; 0xf9uy;
  0xaauy; 0x1duy; 0x3buy; 0xeauy; 0x57uy; 0x78uy; 0x9cuy; 0xa0uy;
  0x31uy; 0xaduy; 0x85uy; 0xc7uy; 0xa7uy; 0x1duy; 0xd7uy; 0x03uy;
  0x54uy; 0xecuy; 0x63uy; 0x12uy; 0x38uy; 0xcauy; 0x34uy; 0x45uy
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
  0x8euy; 0x95uy; 0x9buy; 0x75uy; 0xdauy; 0xe3uy; 0x13uy; 0xdauy;
  0x8cuy; 0xf4uy; 0xf7uy; 0x28uy; 0x14uy; 0xfcuy; 0x14uy; 0x3fuy;
  0x8fuy; 0x77uy; 0x79uy; 0xc6uy; 0xebuy; 0x9fuy; 0x7fuy; 0xa1uy;
  0x72uy; 0x99uy; 0xaeuy; 0xaduy; 0xb6uy; 0x88uy; 0x90uy; 0x18uy;
  0x50uy; 0x1duy; 0x28uy; 0x9euy; 0x49uy; 0x00uy; 0xf7uy; 0xe4uy;
  0x33uy; 0x1buy; 0x99uy; 0xdeuy; 0xc4uy; 0xb5uy; 0x43uy; 0x3auy;
  0xc7uy; 0xd3uy; 0x29uy; 0xeeuy; 0xb6uy; 0xdduy; 0x26uy; 0x54uy;
  0x5euy; 0x96uy; 0xe5uy; 0x5buy; 0x87uy; 0x4buy; 0xe9uy; 0x09uy
]


//
// Test 5
//

let test_expected5 = [
  0xe7uy; 0x18uy; 0x48uy; 0x3duy; 0x0cuy; 0xe7uy; 0x69uy; 0x64uy;
  0x4euy; 0x2euy; 0x42uy; 0xc7uy; 0xbcuy; 0x15uy; 0xb4uy; 0x63uy;
  0x8euy; 0x1fuy; 0x98uy; 0xb1uy; 0x3buy; 0x20uy; 0x44uy; 0x28uy;
  0x56uy; 0x32uy; 0xa8uy; 0x03uy; 0xafuy; 0xa9uy; 0x73uy; 0xebuy;
  0xdeuy; 0x0fuy; 0xf2uy; 0x44uy; 0x87uy; 0x7euy; 0xa6uy; 0x0auy;
  0x4cuy; 0xb0uy; 0x43uy; 0x2cuy; 0xe5uy; 0x77uy; 0xc3uy; 0x1buy;
  0xebuy; 0x00uy; 0x9cuy; 0x5cuy; 0x2cuy; 0x49uy; 0xaauy; 0x2euy;
  0x4euy; 0xaduy; 0xb2uy; 0x17uy; 0xaduy; 0x8cuy; 0xc0uy; 0x9buy
]




//
// Main
//

let test () =
  assert_norm(List.Tot.length test_plaintext1 = 3);
  assert_norm(List.Tot.length test_expected1 = 64);
//  assert_norm(List.Tot.length test_plaintext2 = 0);
  assert_norm(List.Tot.length test_expected2 = 64);
  assert_norm(List.Tot.length test_plaintext3 = 56);
  assert_norm(List.Tot.length test_expected3 = 64);
  assert_norm(List.Tot.length test_plaintext4 = 112);
  assert_norm(List.Tot.length test_expected4 = 64);
  assert_norm(List.Tot.length test_expected5 = 64);
  let test_plaintext1 = createL test_plaintext1 in
  let test_expected1 = createL test_expected1 in
  let test_plaintext2 = createL test_plaintext2 in
  let test_expected2 = createL test_expected2 in
  let test_plaintext3 = createL test_plaintext3 in
  let test_expected3 = createL test_expected3 in
  let test_plaintext4 = createL test_plaintext4 in
  let test_expected4 = createL test_expected4 in
  (* let test_plaintext5 = create 1000000 0x61uy in *)
  (* let test_expected5 = createL test_expected5 in *)

  (hash test_plaintext1 = test_expected1) && (hash' test_plaintext1 = test_expected1) &&
  (hash test_plaintext2 = test_expected2) && (hash' test_plaintext2 = test_expected2) &&
  (hash test_plaintext3 = test_expected3) && (hash' test_plaintext3 = test_expected3) &&
  (hash test_plaintext4 = test_expected4) && (hash' test_plaintext4 = test_expected4) // &&
  (* (hash test_plaintext5 = test_expected5) && (hash' test_plaintext5 = test_expected5) *)
