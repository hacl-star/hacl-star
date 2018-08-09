module Spec.SHA2Again

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module C = Spec.SHA2Again.Constants
module S = FStar.Seq

(* List the Hash algorithms *)
type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512

(* Defines the size of the word for each algorithm *)
inline_for_extraction
let size_word: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8

(* Number of words for intermediate hash *)
let size_hash_w = 8

(* Number of words for final hash *)
inline_for_extraction
let size_hash_final_w: hash_alg -> Tot nat = function
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8

(* Define the final hash length in bytes *)
let size_hash a =
  let open FStar.Mul in
  size_word a * size_hash_final_w a

(* Number of words for a block size *)
let size_block_w = 16

(* Define the size block in bytes *)
let size_block a =
  let open FStar.Mul in
  size_word a * size_block_w

(* Define the length of the constants *)
inline_for_extraction
let size_k_w: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 64
  | SHA2_384 | SHA2_512 -> 80

(* Define the length of scheduling block *)
let size_ws_w = size_k_w

(* Define the length of the encoded lenght in the padding *)
inline_for_extraction
let size_len_8: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 8
  | SHA2_384 | SHA2_512 -> 16

inline_for_extraction
let size_len_ul_8: a:hash_alg -> Tot (n:U32.t{U32.v n = size_len_8 a}) = function
  | SHA2_224 | SHA2_256 -> 8ul
  | SHA2_384 | SHA2_512 -> 16ul

(* Define the maximum input length in bytes *)
inline_for_extraction
let max_input8: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> pow2 61
  | SHA2_384 | SHA2_512 -> pow2 125

(* Definition of main types *)
type bytes = m:S.seq UInt8.t

inline_for_extraction
let word: hash_alg -> Tot Type0 = function
  | SHA2_224 | SHA2_256 -> U32.t
  | SHA2_384 | SHA2_512 -> U64.t

inline_for_extraction
let word_n: hash_alg -> Tot nat = function
  | SHA2_224 | SHA2_256 -> 32
  | SHA2_384 | SHA2_512 -> 64

let v' #a (x:word a) = match a with
  | SHA2_224 | SHA2_256 -> U32.v x
  | SHA2_384 | SHA2_512 -> U64.v x

let hash_w   a = m:S.seq (word a) {S.length m = size_hash_w}
let k_w      a = m:S.seq (word a) {S.length m = size_k_w a}
let ws_w     a = m:S.seq (word a) {S.length m = size_ws_w a}
let block_w  a = m:S.seq (word a) {S.length m = size_block_w}
let counter = nat

(* Define word based operators *)
let words_to_be: a:hash_alg -> Tot (len:nat -> s:S.seq (word a){S.length s = len} -> Tot (Spec.Lib.lbytes FStar.Mul.(size_word a * len))) = function
  | SHA2_224 | SHA2_256 -> Spec.Lib.uint32s_to_be
  | SHA2_384 | SHA2_512 -> Spec.Lib.uint64s_to_be

let words_from_be: a:hash_alg -> Tot (len:nat -> b:Spec.Lib.lbytes FStar.Mul.(size_word a * len) -> Tot (s:S.seq (word a){S.length s = len})) = function
  | SHA2_224 | SHA2_256 -> Spec.Lib.uint32s_from_be
  | SHA2_384 | SHA2_512 -> Spec.Lib.uint64s_from_be

let word_add_mod: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.add_mod
  | SHA2_384 | SHA2_512 -> U64.add_mod

let word_logxor: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logxor
  | SHA2_384 | SHA2_512 -> U64.logxor

let word_logand: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logand
  | SHA2_384 | SHA2_512 -> U64.logand

let word_logor: a:hash_alg -> Tot ((word a) -> (word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.logor
  | SHA2_384 | SHA2_512 -> U64.logor

let word_lognot: a:hash_alg -> Tot ((word a) -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> U32.lognot
  | SHA2_384 | SHA2_512 -> U64.lognot

let word_shift_right: t:hash_alg -> Tot (a:word t -> s:U32.t -> Pure (word t)
  (requires (FStar.Mul.(U32.v s < 8 * size_word t)))
  (ensures (fun c -> v' c = (v' a / (pow2 (U32.v s)))))) = function
  | SHA2_224 | SHA2_256 -> U32.shift_right
  | SHA2_384 | SHA2_512 -> U64.shift_right

let rotate_right32 (x:U32.t) (s:U32.t{0 < U32.v s /\ U32.v s < 32}): Tot U32.t =
  U32.((x >>^ s) |^ (x <<^ (32ul -^ s)))

let rotate_right64 (a:U64.t) (s:U32.t{0 < U32.v s /\ U32.v s < 64}): Tot U64.t =
  U64.((a >>^ s) |^ (a <<^ (U32.sub 64ul s)))

let word_rotate_right: a:hash_alg -> Tot (word a -> s:U32.t{0 < U32.v s /\ U32.v s < word_n a} -> Tot (word a)) = function
  | SHA2_224 | SHA2_256 -> rotate_right32
  | SHA2_384 | SHA2_512 -> rotate_right64

type ops = {
  c0: U32.t; c1: U32.t; c2: U32.t;
  c3: U32.t; c4: U32.t; c5: U32.t;
  e0: U32.t; e1: U32.t; e2: U32.t;
  e3: U32.t; e4: U32.t; e5: U32.t;
}

(* Definition of constants used in word functions *)
let op224_256: ops = {
  c0 = 2ul; c1 = 13ul; c2 = 22ul;
  c3 = 6ul; c4 = 11ul; c5 = 25ul;
  e0 = 7ul; e1 = 18ul; e2 = 3ul;
  e3 = 17ul; e4 = 19ul; e5 = 10ul
}

let op384_512: ops = {
  c0 = 28ul; c1 = 34ul; c2 = 39ul;
  c3 = 14ul; c4 = 18ul; c5 = 41ul;
  e0 = 1ul ; e1 =  8ul; e2 =  7ul;
  e3 = 19ul; e4 = 61ul; e5 =  6ul
}

let op0: a:hash_alg -> Tot ops = function
  | SHA2_224 -> op224_256
  | SHA2_256 -> op224_256
  | SHA2_384 -> op384_512
  | SHA2_512 -> op384_512


(* Definition of the SHA2 word functions *)
val _Ch: a:hash_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Ch a x y z = word_logxor a (word_logand a x y)
                                (word_logand a (word_lognot a x) z)

val _Maj: a:hash_alg -> x:(word a) -> y:(word a) -> z:(word a) -> Tot (word a)
let _Maj a x y z = word_logxor a (word_logand a x y)
                                 (word_logxor a (word_logand a x z)
                                                (word_logand a y z))

val _Sigma0: a:hash_alg -> x:(word a) -> Tot (word a)
let _Sigma0 a x = word_logxor a (word_rotate_right a x (op0 a).c0)
                                (word_logxor a (word_rotate_right a x (op0 a).c1)
                                               (word_rotate_right a x (op0 a).c2))

val _Sigma1: a:hash_alg -> x:(word a) -> Tot (word a)
let _Sigma1 a x = word_logxor a (word_rotate_right a x (op0 a).c3)
                                (word_logxor a (word_rotate_right a x (op0 a).c4)
                                               (word_rotate_right a x (op0 a).c5))

val _sigma0: a:hash_alg -> x:(word a) -> Tot (word a)
let _sigma0 a x = word_logxor a (word_rotate_right a x (op0 a).e0)
                                (word_logxor a (word_rotate_right a x (op0 a).e1)
                                               (word_shift_right a x (op0 a).e2))

val _sigma1: a:hash_alg -> x:(word a) -> Tot (word a)
let _sigma1 a x = word_logxor a (word_rotate_right a x (op0 a).e3)
                                (word_logxor a (word_rotate_right a x (op0 a).e4)
                                               (word_shift_right a x (op0 a).e5))

let k0: a:hash_alg -> Tot (m:S.seq (word a) {S.length m = size_k_w a}) = function
  | SHA2_224 -> C.k224_256
  | SHA2_256 -> C.k224_256
  | SHA2_384 -> C.k384_512
  | SHA2_512 -> C.k384_512

let h0: a:hash_alg -> Tot (m:S.seq (word a) {S.length m = size_hash_w}) = function
  | SHA2_224 -> C.h224
  | SHA2_256 -> C.h256
  | SHA2_384 -> C.h384
  | SHA2_512 -> C.h512

unfold
let (.[]) = S.index

(* Scheduling function *)
let rec ws (a:hash_alg) (b:block_w a) (t:counter{t < size_k_w a}): Tot (word a) =
  if t < size_block_w then b.[t]
  else
    let t16 = ws a b (t - 16) in
    let t15 = ws a b (t - 15) in
    let t7  = ws a b (t - 7) in
    let t2  = ws a b (t - 2) in

    let s1 = _sigma1 a t2 in
    let s0 = _sigma0 a t15 in
    (word_add_mod a s1 (word_add_mod a t7 (word_add_mod a s0 t16)))


(* Core shuffling function *)
let shuffle_core (a:hash_alg) (block:block_w a) (hash:hash_w a) (t:counter{t < size_k_w a}): Tot (hash_w a) =
  (**) assert(7 <= S.length hash);
  let a0 = hash.[0] in
  let b0 = hash.[1] in
  let c0 = hash.[2] in
  let d0 = hash.[3] in
  let e0 = hash.[4] in
  let f0 = hash.[5] in
  let g0 = hash.[6] in
  let h0 = hash.[7] in

  (**) assert(S.length (k0 a) = size_k_w a);
  let t1 = word_add_mod a h0 (word_add_mod a (_Sigma1 a e0) (word_add_mod a (_Ch a e0 f0 g0) (word_add_mod a (k0 a).[t] (ws a block t)))) in
  let t2 = word_add_mod a (_Sigma0 a a0) (_Maj a a0 b0 c0) in

  (**) assert(t < S.length (k0 a));
  // JP: was a S.create: understand if the post-condition was really needed
  S.seq_of_list [ word_add_mod a t1 t2; a0; b0; c0; word_add_mod a d0 t1; e0; f0; g0 ]


(* Full shuffling function *)
let shuffle (a:hash_alg) (hash:hash_w a) (block:block_w a): Tot (hash_w a) =
  Spec.Loops.repeat_range_spec 0 (size_ws_w a) (shuffle_core a block) hash

(* Compression function *)
let update (a:hash_alg) (hash:hash_w a) (block:bytes{S.length block = size_block a}): Tot (hash_w a) =
  let block_w = words_from_be a size_block_w block in
  let hash_1 = shuffle a hash block_w in
  Spec.Loops.seq_map2 (fun x y -> word_add_mod a x y) hash hash_1

let split_block (a: hash_alg)
  (blocks: bytes)
  (n: nat):
  Pure
    (bytes * bytes)
    (requires (
      S.length blocks % size_block a = 0 /\
      n <= S.length blocks / size_block a))
    (ensures (fun ret ->
      let block, rem = ret in
      S.length rem % size_block a = 0 /\
      S.length block % size_block a = 0))
=
  let block, rem = S.split blocks FStar.Mul.(n * size_block a) in
  assert (S.length rem = S.length blocks - S.length block);
  Math.Lemmas.modulo_distributivity (S.length rem) (S.length block) (size_block a);
  assert (S.length rem % size_block a = 0);
  block, rem

(* Compression function for multiple blocks *)
let rec update_multi
  (a:hash_alg)
  (hash:hash_w a)
  (blocks:bytes{S.length blocks % size_block a = 0}):
  Tot (hash_w a) (decreases (S.length blocks))
=
  if S.length blocks = 0 then
    hash
  else
    let block, rem = split_block a blocks 1 in
    let hash = update a hash block in
    update_multi a hash rem

(* Compute the length for the zeroed part of the padding *)
let pad0_length (a:hash_alg) (len:nat): Tot (n:nat{(len + 1 + n + (size_len_8 a)) % (size_block a) = 0}) =
  ((size_block a) - (len + (size_len_8 a) + 1)) % (size_block a)

(* Compute the padding *)
let pad (a:hash_alg) (prevlen:nat{prevlen % (size_block a) = 0}) (len:nat{prevlen + len < (max_input8 a)}): Tot (b:bytes{(S.length b + len) % (size_block a) = 0}) =
  let open FStar.Mul in
  let total_len = prevlen + len in
  let firstbyte = S.create 1 0x80uy in
  let zeros = S.create (pad0_length a len) 0uy in
  let total_byte_len = total_len * 8 in
  // Saves the need for high fuel + makes hint replayable.
  (match a with
    | SHA2_224 | SHA2_256 ->
        assert_norm (max_input8 a * 8 = pow2 (size_len_8 a * 8))
    | SHA2_384 | SHA2_512 ->
        assert_norm (max_input8 a * 8 = pow2 (size_len_8 a * 8))
  );
  let encodedlen = Endianness.big_bytes (size_len_ul_8 a) (total_len * 8) in
  S.(firstbyte @| zeros @| encodedlen)

(* Compress full blocks, then pad the partial block and compress the last block *)
let update_last (a:hash_alg) (hash:hash_w a) (prevlen:nat{prevlen % (size_block a) = 0}) (input:bytes{(S.length input) + prevlen < (max_input8 a)}): Tot (hash_w a) =
  let blocks = pad a prevlen (S.length input) in
  update_multi a hash S.(input @| blocks)

(* Unflatten the hash from the sequence of words to bytes up to the correct size *)
let finish (a:hash_alg) (hashw:hash_w a): Tot (hash:bytes{S.length hash = (size_hash a)}) =
  let hash_final_w = S.slice hashw 0 (size_hash_final_w a) in
  words_to_be a (size_hash_final_w a) hash_final_w

(* Hash function using the incremental definition *)
let hash (a:hash_alg) (input:bytes{S.length input < (max_input8 a)}):
  Tot (hash:bytes{S.length hash = (size_hash a)})
=
  let open FStar.Mul in
  let n = S.length input / (size_block a) in
  let (bs,l) = S.split input (n * (size_block a)) in
  let hash = update_multi a (h0 a) bs in
  let hash = update_last a hash (n * (size_block a)) l in
  finish a hash

(* Hash function using the padding function first. Closer to the NIST spec, but
   less amenable to implementing directly. *)
let hash_nist (a:hash_alg) (input:bytes{S.length input < (max_input8 a)}):
  Tot (hash:bytes{S.length hash = (size_hash a)})
=
  let blocks = pad a 0 (S.length input) in
  finish a (update_multi a (h0 a) S.(input @| blocks))

(* Now proving that these two are equivalent. *)

let update_multi_zero (a: hash_alg) (h: hash_w a): Lemma
  (ensures (S.equal (update_multi a h S.empty) h))
=
  ()

#set-options "--z3rlimit 50"

let update_multi_one (a: hash_alg) (h: hash_w a) (input: bytes):
  Lemma
    (requires (
      S.length input = size_block a
    ))
    (ensures (
      S.equal (update a h input) (update_multi a h input)
    ))
=
  let block, rem = split_block a input 1 in
  update_multi_zero a (update a h block)

let update_multi_block (a: hash_alg) (h: hash_w a) (input: bytes):
  Lemma
    (requires (
      S.length input % size_block a = 0 /\
      S.length input < max_input8 a /\
      size_block a <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input 1 in
      (update_multi a (update_multi a h input1) input2) == (update_multi a h input)))
=
  ()

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let rec update_multi_associative (a: hash_alg) (h: hash_w a) (input: bytes) (len: nat):
  Lemma
    (requires (
      len % size_block a = 0 /\
      S.length input % size_block a = 0 /\
      S.length input < max_input8 a /\
      len <= S.length input
    ))
    (ensures (
      let input1, input2 = split_block a input (len / size_block a) in
      S.equal (update_multi a (update_multi a h input1) input2) (update_multi a h input)))
    (decreases (
      %[ S.length input; len ]))
=
  let i_l, i_r = S.split input len in
  let n = len / size_block a in
  if len = 0 then begin
    assert (S.equal i_l S.empty);
    assert (S.equal i_r input);
    update_multi_zero a h
  end else if len = size_block a then begin
    update_multi_block a h input
  end else begin
    let i0, _ = split_block a i_l (n - 1) in
    let _, i3 = split_block a input (n - 1) in
    update_multi_associative a h i_l (len - size_block a);
    update_multi_associative a (update_multi a h i0) i3 (size_block a);
    update_multi_associative a h input (len - size_block a)
  end

let hash_is_hash_nist (a: hash_alg) (input: bytes { S.length input < max_input8 a }):
  Lemma (ensures (hash_nist a input == hash a input))
=
  ()
