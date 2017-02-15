module Spec.Poly1305

open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness

(* Field types and parameters *)

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

unfold let prime : (p:pos{p = pow2 130 - 5}) =
  assert_norm(pow2 130 - 5 = 0x3fffffffffffffffffffffffffffffffb);
  0x3fffffffffffffffffffffffffffffffb

type elem = e:int{e >= 0 /\ e < prime}

let zero : elem = 0
let one  : elem = 1

val fadd: elem -> elem -> Tot elem
let fadd e1 e2 = (e1 + e2) % prime
let op_Plus_At e1 e2 = fadd e1 e2

val fmul: elem -> elem -> Tot elem
let fmul e1 e2 = (e1 * e2) % prime
let op_Star_At e1 e2 = fmul e1 e2


(* Types from Low-level crypto *)
type byte = FStar.UInt8.t
type bytes = seq byte
type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type tag = word_16
type text = seq word


let encode (w:word) : Tot elem =
  let l = length w in
  Math.Lemmas.pow2_le_compat 128 (8 * l);
  assert_norm(pow2 128 < pow2 130 - 5);
  lemma_little_endian_is_bounded w;
  pow2 (8 * l) +@ little_endian w


val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = Seq.head vs in
    (encode v +@ poly (Seq.tail vs) r) *@ r


module L = FStar.List.Tot
open FStar.Seq

#set-options "--initial_fuel 0 --max_fuel 0"

unfold let mask = 0x0ffffffc0ffffffc0ffffffc0fffffff

#set-options "--initial_ifuel 1 --max_ifuel 1"

open FStar.Seq

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

(* Little endian integer value of a sequence of bytes *)
(* JK: should be removed, and FStar.Endianness be moved as part of the standard library *)
inline_for_extraction
let little_endian (b:bytes) : Tot (n:nat) = little_endian b

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"


let rec lemma_little_endian_eq (b:bytes) : Lemma
  (requires (True))
  (ensures (little_endian b = FStar.Endianness.little_endian b))
  (decreases (length b))
  [SMTPat (FStar.Endianness.little_endian b)]
  = if length b = 0 then ()
    else lemma_little_endian_eq (slice b 1 (length b))


val encode_r: rb:word_16 -> Tot (r:elem)
let encode_r rb =
  lemma_little_endian_is_bounded rb;
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  UInt.logand #128 (little_endian rb) 0x0ffffffc0ffffffc0ffffffc0fffffff


(** Finish: truncate and pad (or pad and truncate) *)
val finish: a:elem -> s:tag -> Tot tag
let finish a s =
  (* REMARK: this is equivalent to n = ((a % pow2 128) + little_endian s) % pow2 128 *)
  let n = (a + little_endian s) % pow2 128 in
  little_bytes 16ul n


val mac_1305: vs:text -> r:elem -> s:tag -> Tot tag
let mac_1305 vs r s = finish (poly vs r) s


val encode_bytes: txt:bytes -> Tot (text) (decreases (Seq.length txt))
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then
    Seq.createEmpty
  else
    let l0 = FStar.Math.Lib.min l 16 in
    let w, txt = Seq.split txt l0 in
    Seq.snoc (encode_bytes txt) w


val poly1305: msg:bytes -> k:bytes{length k = 32} -> Tot tag
let poly1305 msg k =
  let text = encode_bytes msg in
  let r = encode_r (slice k 0 16) in
  let s = slice k 16 32 in
  mac_1305 text r s


let test () =
  let msg = createL [0x43uy; 0x72uy; 0x79uy; 0x70uy; 0x74uy; 0x6fuy; 0x67uy; 0x72uy;
                     0x61uy; 0x70uy; 0x68uy; 0x69uy; 0x63uy; 0x20uy; 0x46uy; 0x6fuy;
                     0x72uy; 0x75uy; 0x6duy; 0x20uy; 0x52uy; 0x65uy; 0x73uy; 0x65uy;
                     0x61uy; 0x72uy; 0x63uy; 0x68uy; 0x20uy; 0x47uy; 0x72uy; 0x6fuy;
                     0x75uy; 0x70uy] in
  let key = createL [0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy;
                     0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy;
                     0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy;
                     0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy] in
  0xa927010caf8b2bc2c6365130c11d06a8 = little_endian (poly1305 msg key)
