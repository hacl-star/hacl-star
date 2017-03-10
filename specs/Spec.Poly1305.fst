module Spec.Poly1305

open FStar.Math.Lib
open FStar.Mul
open FStar.Seq
open FStar.UInt8
open FStar.Endianness
open Spec.Poly1305.Lemmas

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* Field types and parameters *)
let prime = pow2 130 - 5

type elem = e:int{e >= 0 /\ e < prime}

let zero : elem = 0
let one  : elem = 1

val fadd: elem -> elem -> Tot elem
let fadd e1 e2 = (e1 + e2) % prime
let op_Plus_At e1 e2 = fadd e1 e2

val fmul: elem -> elem -> Tot elem
let fmul e1 e2 = (e1 * e2) % prime
let op_Star_At e1 e2 = fmul e1 e2


(* Type aliases *)
type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type tag = word_16
type key = lbytes 32
type text = seq word

(* Specification code *)
let encode (w:word) : Tot elem =
  pow2 (8 * length w) +@ little_endian w

val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if length vs = 0 then zero
  else
    let v = Seq.head vs in
    (encode v +@ poly (Seq.tail vs) r) *@ r

val encode_r: rb:word_16 -> Tot (r:elem)
let encode_r rb =
  UInt.logand #128 (little_endian rb) 0x0ffffffc0ffffffc0ffffffc0fffffff

(** Finish: truncate and pad (or pad and truncate) *)
val finish: a:elem -> s:tag -> Tot tag
let finish a s =
  let n = (a + little_endian s) % pow2 128 in
  little_bytes 16ul n

val encode_bytes: txt:bytes -> Tot (text) (decreases (Seq.length txt))
let rec encode_bytes txt =
  if length txt = 0 then createEmpty
  else
    let w, txt = split txt (min (length txt) 16) in
    append_last (encode_bytes txt) w

val poly1305: msg:bytes -> k:key -> Tot tag
let poly1305 msg k =
  let text = encode_bytes msg in
  let r = encode_r (slice k 0 16) in
  let s = slice k 16 32 in
  finish (poly text r) s


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(* ********************* *)
(* RFC 7539 Test Vectors *)
(* ********************* *)

unfold let msg = [
  0x43uy; 0x72uy; 0x79uy; 0x70uy; 0x74uy; 0x6fuy; 0x67uy; 0x72uy;
  0x61uy; 0x70uy; 0x68uy; 0x69uy; 0x63uy; 0x20uy; 0x46uy; 0x6fuy;
  0x72uy; 0x75uy; 0x6duy; 0x20uy; 0x52uy; 0x65uy; 0x73uy; 0x65uy;
  0x61uy; 0x72uy; 0x63uy; 0x68uy; 0x20uy; 0x47uy; 0x72uy; 0x6fuy;
  0x75uy; 0x70uy ]

unfold let k = [
  0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy;
  0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy;
  0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy;
  0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy ]

unfold let expected = [
  0xa8uy; 0x06uy; 0x1duy; 0xc1uy; 0x30uy; 0x51uy; 0x36uy; 0xc6uy;
  0xc2uy; 0x2buy; 0x8buy; 0xafuy; 0x0cuy; 0x01uy; 0x27uy; 0xa9uy ]

let test () : Tot bool =
  assert_norm(List.Tot.length msg      = 34);
  assert_norm(List.Tot.length k        = 32);
  assert_norm(List.Tot.length expected = 16);
  let msg      = createL msg in
  let k        = createL k   in
  let expected = createL expected in
  poly1305 msg k = expected
