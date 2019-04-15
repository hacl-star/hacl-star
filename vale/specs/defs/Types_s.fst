module Types_s

open Opaque_s
open Words_s
open Words.Two_s
open Words.Four_s
open Words.Seq_s
open FStar.Seq
open Collections.Seqs_s

unfold let nat8 = Words_s.nat8
unfold let nat16 = Words_s.nat16
unfold let nat32 = Words_s.nat32
unfold let nat64 = Words_s.nat64

let add_wrap (#n:nat) (x:natN n) (y:natN n) : natN n = if x + y < n then x + y else x + y - n

// abstract bitwise operations on integers:
assume val iand : #n:nat -> a:natN n -> b:natN n -> natN n
assume val ixor : #n:nat -> a:natN n -> b:natN n -> natN n
assume val ior : #n:nat -> a:natN n -> b:natN n -> natN n
assume val inot : #n:nat -> a:natN n  -> natN n
assume val ishl : #n:nat -> a:natN n -> s:int -> natN n
assume val ishr : #n:nat -> a:natN n -> s:int -> natN n

// Alias
unfold let nat32_xor (x y:nat32) : nat32 = ixor x y

type twobits:eqtype = natN 4
type bits_of_byte:eqtype = four twobits

let byte_to_twobits (b:nat8) : bits_of_byte = nat_to_four_unfold 2 b

type double32:eqtype = two nat32
type quad32:eqtype = four nat32

let quad32_xor_def (x y:quad32) : quad32 = four_map2 nat32_xor x y
let quad32_xor  = make_opaque quad32_xor_def

let select_word (q:quad32) (selector:twobits) : nat32 = four_select q selector
let insert_nat32 (q:quad32) (n:nat32) (i:twobits) : quad32 = four_insert q n i
let insert_nat64 (q:quad32) (n:nat64) (i:nat1) : quad32 =
  two_two_to_four (two_insert (four_to_two_two q) (nat_to_two 32 n) i)

open FStar.Seq

let le_bytes_to_nat32 (b:seq4 nat8) : nat32 =
  four_to_nat 8 (seq_to_four_LE b)

let nat32_to_le_bytes (n:nat32) : b:seq4 nat8 {
  le_bytes_to_nat32 b == n} =
  let b = four_to_seq_LE (nat_to_four 8 n) in
  assume (le_bytes_to_nat32 b == n);
  b

let be_bytes_to_nat32 (b:seq4 nat8) : nat32 =
  four_to_nat 8 (seq_to_four_BE b)

let nat32_to_be_bytes (n:nat32) : b:seq4 nat8 { be_bytes_to_nat32 b == n } =
  let b = four_to_seq_BE (nat_to_four 8 n) in
  assume (be_bytes_to_nat32 b == n);
  b

assume val be_bytes_to_nat32_to_be_bytes (b:seq4 nat8) :
  Lemma (nat32_to_be_bytes (be_bytes_to_nat32 b) == b)

let le_bytes_to_nat64_def (b:seq nat8) : Pure nat64 (requires length b == 8) (ensures fun _ -> True) =
  two_to_nat 32 (seq_to_two_LE (seq_nat8_to_seq_nat32_LE b))
let le_bytes_to_nat64 = make_opaque le_bytes_to_nat64_def

let le_nat64_to_bytes_def (b:nat64) : Pure (seq nat8) (requires True) (ensures fun s -> length s == 8) =
  seq_nat32_to_seq_nat8_LE (two_to_seq_LE (nat_to_two 32 b))
let le_nat64_to_bytes = make_opaque le_nat64_to_bytes_def

let le_bytes_to_quad32_def (b:seq nat8) : Pure quad32 (requires length b == 16) (ensures fun _ -> True) =
  seq_to_four_LE (seq_map (four_to_nat 8) (seq_to_seq_four_LE b))
let le_bytes_to_quad32 = make_opaque le_bytes_to_quad32_def

let be_bytes_to_quad32_def (b:seq nat8) : Pure quad32 (requires length b == 16) (ensures fun _ -> True) =
  seq_to_four_BE (seq_map (four_to_nat 8) (seq_to_seq_four_BE b))
let be_bytes_to_quad32 = make_opaque be_bytes_to_quad32_def

[@"opaque_to_smt"]
let le_quad32_to_bytes (b:quad32) : Pure (seq nat8) (requires True) (ensures fun s -> length s == 16) =
  seq_four_to_seq_LE (seq_map (nat_to_four 8) (four_to_seq_LE b))

let le_seq_quad32_to_bytes_def (b:seq quad32) : seq nat8 =
  seq_nat32_to_seq_nat8_LE (seq_four_to_seq_LE b)
let le_seq_quad32_to_bytes = make_opaque le_seq_quad32_to_bytes_def

let le_seq_quad32_to_bytes_length (s:seq quad32) : Lemma
  (ensures length (le_seq_quad32_to_bytes s) == 16 `op_Multiply` (length s))
  [SMTPat (length (le_seq_quad32_to_bytes s))]
  =
  reveal_opaque le_seq_quad32_to_bytes_def

[@"opaque_to_smt"]
let le_bytes_to_seq_quad32 (b:seq nat8) : Pure (seq quad32) (requires length b % 16 == 0) (ensures fun _ -> True) =
  seq_to_seq_four_LE (seq_nat8_to_seq_nat32_LE b)

let reverse_bytes_nat32_def (n:nat32) : nat32 =
  be_bytes_to_nat32 (reverse_seq (nat32_to_be_bytes n))
let reverse_bytes_nat32 = make_opaque reverse_bytes_nat32_def  

let reverse_bytes_nat64_def (n:nat64) : nat64 =
  let Mktwo n0 n1 = nat_to_two 32 n in
  two_to_nat 32 (Mktwo (reverse_bytes_nat32 n1) (reverse_bytes_nat32 n0))
let reverse_bytes_nat64 = make_opaque reverse_bytes_nat64_def 

assume val reverse_bytes_quad32 (q:quad32) : quad32

assume val reveal_reverse_bytes_quad32 (q:quad32) : Lemma
  (reverse_bytes_quad32 q == four_reverse (four_map reverse_bytes_nat32 q))

// Reverses the bytes in each nat32, but not the nat32s themselves
assume val reverse_bytes_nat32_seq (s:seq nat32) : s':seq nat32 { length s == length s' }

assume val reveal_reverse_bytes_nat32_seq (s:seq nat32) : Lemma
  (reverse_bytes_nat32_seq s == seq_map reverse_bytes_nat32 s)
