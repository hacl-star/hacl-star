module Hacl.Hash.PadFinish

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module Cast = FStar.Int.Cast.Full
module Constants = Spec.SHA2.Constants
module Helpers = Spec.Hash.Definitions
module Endianness = FStar.Kremlin.Endianness
module Math = FStar.Math.Lemmas
module Helpers = Spec.Hash.Definitions

module M = LowStar.Modifies
module S = FStar.Seq
module B = LowStar.Buffer
module G = FStar.Ghost
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open Hacl.Hash.Definitions
open Hacl.Hash.Lemmas
open Spec.Hash.Definitions
open Spec.Hash.Lemmas0

(** Padding *)

#set-options "--z3rlimit 50"
inline_for_extraction
val store_len: a:hash_alg -> len:len_t a -> b:B.buffer U8.t ->
  ST.Stack unit
    (requires (fun h ->
      B.live h b /\
      B.length b = Helpers.len_length a))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer b) h0 h1) /\ (
      match a with
      | MD5 -> B.as_seq h1 b == Endianness.n_to_le (len_len a) (len_v a len)
      | _ -> B.as_seq h1 b == Endianness.n_to_be (len_len a) (len_v a len))))

inline_for_extraction
let store_len a len b =
  match a with
  | MD5 ->
      C.Endianness.store64_le b len;
      let h = ST.get () in
      Endianness.n_to_le_le_to_n 8ul (B.as_seq h b)
  | SHA1 | SHA2_224 | SHA2_256 ->
      C.Endianness.store64_be b len;
      let h = ST.get () in
      Endianness.n_to_be_be_to_n 8ul (B.as_seq h b)
  | SHA2_384 | SHA2_512 ->
      C.Endianness.store128_be b len;
      let h = ST.get () in
      Endianness.n_to_be_be_to_n 16ul (B.as_seq h b)

#set-options "--z3rlimit 20"

inline_for_extraction noextract
let len_mod_32 (a: hash_alg) (len: len_t a):
  Tot (n:U32.t { U32.v n = len_v a len % Helpers.block_length a })
=
  assert (block_len a <> 0ul);
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 ->
      Math.lemma_mod_lt (U64.v len) (U32.v (block_len a));
      Math.modulo_lemma (U64.v len % U32.v (block_len a)) (pow2 32);
      Cast.uint64_to_uint32 (U64.(len %^ Cast.uint32_to_uint64 (block_len a)))
  | _ ->
      // this case is more difficult because we do: (len % pow2 64) % block_len
      // and then we need to show it's equal to len % block_len
      [@inline_let]
      let len = Cast.uint128_to_uint64 len in
      Math.lemma_mod_lt (U64.v len) (U32.v (block_len a));
      Math.modulo_lemma (U64.v len % U32.v (block_len a)) (pow2 32);
      Cast.uint64_to_uint32 (U64.(len %^ Cast.uint32_to_uint64 (block_len a)))

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100 --z3seed 1"

// JP: this proof works instantly in interactive mode, not in batch mode unless
// there's a high rlimit
inline_for_extraction
let pad0_len (a: hash_alg) (len: len_t a):
  Tot (n:U32.t { U32.v n = pad0_length a (len_v a len) })
=
  let open U32 in
  (* 1. *)
  Math.lemma_mod_mod (U32.v (len_mod_32 a len)) (len_v a len) (block_length a);
  assert (U32.v (len_mod_32 a len) % U32.v (block_len a) =
    len_v a len % U32.v (block_len a));
  assert ((- U32.v (len_mod_32 a len)) % U32.v (block_len a) =
    (- len_v a len) % (U32.v (block_len a)));
  Math.modulo_add (U32.v (block_len a)) (- U32.v (len_len a) - 1)
    (- U32.v (len_mod_32 a len)) (- len_v a len);
  assert ((- (U32.v (len_len a) + 1 + U32.v (len_mod_32 a len))) % U32.v (block_len a) =
    (- (U32.v (len_len a) + 1 + len_v a len)) % (U32.v (block_len a)));
  (* 2. *)
  Math.lemma_mod_plus (U32.v (block_len a)) 1 (U32.v (block_len a));
  assert ((U32.v (block_len a) + U32.v (block_len a)) % U32.v (block_len a) =
    (U32.v (block_len a)) % U32.v (block_len a));
  (* Combine 1 and 2 *)
  Math.modulo_add (U32.v (block_len a))
    (U32.v (block_len a))
    (- (U32.v (len_len a) + 1 + U32.v (len_mod_32 a len)))
    (- (U32.v (len_len a) + 1 + len_v a len));
  assert (
    (U32.v (block_len a) - (U32.v (len_len a) + 1 + U32.v (len_mod_32 a len))) %
      U32.v (block_len a) =
    (U32.v (block_len a) - (U32.v (len_len a) + 1 + len_v a len)) %
      U32.v (block_len a));
  Math.modulo_add (U32.v (block_len a))
    (- (U32.v (len_len a) + 1 + U32.v (len_mod_32 a len)))
    (U32.v (block_len a))
    (U32.v (block_len a) + U32.v (block_len a));
  [@inline_let]
  let r = (block_len a +^ block_len a) -^ (len_len a +^ 1ul +^ len_mod_32 a len) in
  r %^ block_len a

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

inline_for_extraction
let pad_1 (a: hash_alg) (dst: B.buffer U8.t):
  ST.Stack unit
    (requires (fun h ->
      B.live h dst /\ B.length dst = 1))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      S.equal (B.as_seq h1 dst) (S.create 1 0x80uy)))
=
  dst.(0ul) <- 0x80uy

inline_for_extraction
let pad_2 (a: hash_alg) (len: len_t a) (dst: B.buffer U8.t):
  ST.Stack unit
    (requires (fun h ->
      B.live h dst /\ B.length dst = pad0_length a (len_v a len)))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer dst) h0 h1) /\
      S.equal (B.as_seq h1 dst) (S.create (pad0_length a (len_v a len)) 0uy)))
=
  let h0 = ST.get () in
  let len_zero = pad0_len a len in
  let inv h1 (i: nat) =
    M.(modifies (loc_buffer dst) h0 h1) /\
    i <= U32.v len_zero /\
    S.equal (S.slice (B.as_seq h1 dst) 0 i) (S.slice (S.create (U32.v len_zero) 0uy) 0 i)
  in
  let f (i:U32.t { U32.(0 <= v i /\ v i < U32.v len_zero)}):
    ST.Stack unit
      (requires (fun h -> inv h (U32.v i)))
      (ensures (fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 U32.(v i + 1)))
    =
    dst.(i) <- 0uy;
    (**) let h' = ST.get () in
    (**) create_next (B.as_seq h' dst) 0uy (U32.v i)
  in
  C.Loops.for 0ul (pad0_len a len) inv f

inline_for_extraction
let pad_3 (a: hash_alg) (len: len_t a) (dst: B.buffer U8.t):
  ST.Stack unit
    (requires (fun h ->
      len_v a len < max_input_length a /\
      B.live h dst /\ B.length dst = len_length a))
    (ensures (fun h0 _ h1 ->
      max_input_size_len a;
      B.(modifies (loc_buffer dst) h0 h1) /\
      S.equal (B.as_seq h1 dst)
        (match a with
        | MD5 -> Endianness.n_to_le (len_len a) FStar.Mul.(len_v a len * 8)
        | _ -> Endianness.n_to_be (len_len a) FStar.Mul.(len_v a len * 8))))
=
  begin match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 ->
      (**) FStar.UInt.shift_left_value_lemma #64 (U64.v len) 3;
      (**) assert (len_v a len <= pow2 61 - 1);
      (**) assert_norm FStar.Mul.((pow2 61 - 1) * 8 < pow2 64);
      (**) assert_norm (pow2 3 = 8);
      (**) assert FStar.Mul.(U64.v len * 8 < pow2 64);
      (**) assert FStar.Mul.(FStar.UInt.shift_left #64 (len_v a len) 3 < pow2 64);
      (**) assert FStar.Mul.(U64.(v (shift_left len 3ul)) = U64.v len * 8);
      store_len a U64.(shift_left len 3ul) dst
  | SHA2_384 | SHA2_512 ->
      (**) FStar.UInt.shift_left_value_lemma #128 (U128.v len) 3;
      (**) assert (len_v a len <= pow2 125 - 1);
      (**) assert_norm FStar.Mul.((pow2 125 - 1) * 8 < pow2 128);
      (**) assert_norm (pow2 3 = 8);
      (**) assert FStar.Mul.(U128.v len * 8 < pow2 128);
      (**) assert FStar.Mul.(FStar.UInt.shift_left #128 (len_v a len) 3 < pow2 128);
      (**) assert FStar.Mul.(U128.(v (shift_left len 3ul)) = U128.v len * 8);
      store_len a U128.(shift_left len 3ul) dst
  end

noextract inline_for_extraction
let pad a len dst =
  (* i) Append a single 1 bit. *)
  let dst1 = B.sub dst 0ul 1ul in
  pad_1 a dst1;

  (* ii) Fill with zeroes *)
  let dst2 = B.sub dst 1ul (pad0_len a len) in
  pad_2 a len dst2;

  (* iii) Encoded length *)
  let dst3 = B.sub dst U32.(1ul +^ (pad0_len a len)) (len_len a) in
  pad_3 a len dst3;

  (**) let h2 = ST.get () in
  (**) assert (
  (**)   let pad0_length = pad0_length a (len_v a len) in
  (**)   max_input_size_len a;
  (**)   let s = B.as_seq h2 dst in
  (**)   let s1 = S.slice s 0 1 in
  (**)   let s2 = S.slice s 1 (1 + pad0_length) in
  (**)   let s3 = S.slice s (1 + pad0_length) (1 + pad0_length + len_length a) in
  (**)   S.equal s (S.append s1 (S.append s2 s3)) /\
  (**)   True)

inline_for_extraction noextract
let pad_len (a: hash_alg) (len: len_t a) =
  U32.(1ul +^ pad0_len a len +^ len_len a)

#set-options "--max_ifuel 1"
inline_for_extraction
let hash_word_len (a: hash_alg): n:U32.t { U32.v n = hash_word_length a } =
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul


#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

noextract inline_for_extraction
let finish a s dst =
  let open FStar.Mul in
  let h0 = ST.get () in
  let inv (h: HS.mem) (i: nat) =
    let words_state = B.as_seq h s in
    let hash = B.as_seq h dst in
    i <= hash_word_length a /\
    B.live h dst /\ B.live h s /\
    M.(modifies (loc_buffer dst) h0 h) /\
    S.equal (S.slice hash 0 (i * Helpers.word_length a))
      (bytes_of_words a (S.slice words_state 0 i))
  in
  let f (i: U32.t { U32.(0 <= v i /\ v i < hash_word_length a) }): ST.Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
  =
    match a with
    | MD5 ->
        let dst0 = B.sub dst 0ul U32.(4ul *^ i) in
        let dsti = B.sub dst U32.(4ul *^ i) 4ul in
        C.Endianness.store32_le dsti s.(i);
        let h2 = ST.get () in
        Endianness.le_of_seq_uint32_base (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1)) (B.as_seq h2 dsti);
        Endianness.le_of_seq_uint32_append (S.slice (B.as_seq h2 s) 0 (U32.v i))
          (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1))
    | SHA1 | SHA2_224 | SHA2_256 ->
        let dst0 = B.sub dst 0ul U32.(4ul *^ i) in
        let dsti = B.sub dst U32.(4ul *^ i) 4ul in
        C.Endianness.store32_be dsti s.(i);
        let h2 = ST.get () in
        Endianness.be_of_seq_uint32_base (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1)) (B.as_seq h2 dsti);
        Endianness.be_of_seq_uint32_append (S.slice (B.as_seq h2 s) 0 (U32.v i))
          (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1))
    | SHA2_384 | SHA2_512 ->
        let dst0 = B.sub dst 0ul U32.(8ul *^ i) in
        let dsti = B.sub dst U32.(8ul *^ i) 8ul in
        C.Endianness.store64_be dsti s.(i);
        let h2 = ST.get () in
        Endianness.be_of_seq_uint64_base (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1)) (B.as_seq h2 dsti);
        Endianness.be_of_seq_uint64_append (S.slice (B.as_seq h2 s) 0 (U32.v i))
          (S.slice (B.as_seq h2 s) (U32.v i) (U32.v i + 1))
  in
  C.Loops.for 0ul (hash_word_len a) inv f

