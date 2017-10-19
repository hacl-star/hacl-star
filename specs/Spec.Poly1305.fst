module Spec.Poly1305

open FStar.Mul
open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Poly1305.Lemmas
#set-options "--z3rlimit 30 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* Field types and parameters *)
let prime =  pow2 130 - 5
type elem = e:nat{e >= 0 /\ e < prime}
let fadd (e1:elem) (e2:elem) = (e1 + e2) % prime
let fmul (e1:elem) (e2:elem) = (e1 * e2) % prime
let zero : elem = 0
let one  : elem = 1
let op_Plus_At = fadd
let op_Star_At = fmul


type lbytes (s:size_t) = intseq U8 s
let nat_from_bytes_le = nat_from_intseq_le

let blocksize : size_t = 16
let keysize   : size_t = 32

type block = lbytes blocksize
type tag   = lbytes blocksize
type key   = lbytes keysize

(* Specification code *)
let encode_block (w:block) =
  pow2 128 `fadd` nat_from_bytes_le  w 

let encode_last (#l:size_t{l < blocksize}) (w:lbytes l) =
  assert (pow2 (8 * l) < pow2 128);
  pow2 (8 * l) `fadd` nat_from_bytes_le w

val poly: #len:size_t -> txt:lbytes len -> r:elem -> acc:elem
let poly #len txt r =
  let blocks = len / blocksize in
  assert (rem < blocksize /\ len = (blocks * blocksize) + rem);
  let rem = len % blocksize in
  let acc = 
    repeati blocks
      (fun i acc -> 
	let b = sub txt (i * blocksize) blocksize in
	let n = encode_block b in
	(n `fadd` acc) `fmul` r) 0 in
  let last = sub txt (blocks * blocksize) rem in
  let n = encode_last last in
  (n `fadd` acc) `fmul` r
  
  
let encode_r (rb:block) : elem =
    uint_to_nat ((uint_from_bytes_le #U128 rb) &. 
		  u128 0x0ffffffc0ffffffc0ffffffc0fffffff)

let finish (a:elem) (s:block) : Tot tag =
  let n = (a + nat_from_bytes_le s) % pow2 128 in
  nat_to_bytes_le 16 n

let poly1305 (#len:size_t) (msg:lbytes len) (k:key) : Tot tag =
  let r = encode_r (sub k 0 16) in
  let s = sub k 16 16 in
  finish (poly msg r) s


(* ********************* *)
(* RFC 7539 Test Vectors *)
(* ********************* *)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

let msg = List.Tot.map u8uy [
  0x43uy; 0x72uy; 0x79uy; 0x70uy; 0x74uy; 0x6fuy; 0x67uy; 0x72uy;
  0x61uy; 0x70uy; 0x68uy; 0x69uy; 0x63uy; 0x20uy; 0x46uy; 0x6fuy;
  0x72uy; 0x75uy; 0x6duy; 0x20uy; 0x52uy; 0x65uy; 0x73uy; 0x65uy;
  0x61uy; 0x72uy; 0x63uy; 0x68uy; 0x20uy; 0x47uy; 0x72uy; 0x6fuy;
  0x75uy; 0x70uy]

let k = List.Tot.map u8uy [
  0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy;
  0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy;
  0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy;
  0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy]

let expected = List.Tot.map u8uy [
  0xa8uy; 0x06uy; 0x1duy; 0xc1uy; 0x30uy; 0x51uy; 0x36uy; 0xc6uy;
  0xc2uy; 0x2buy; 0x8buy; 0xafuy; 0x0cuy; 0x01uy; 0x27uy; 0xa9uy]

let test () : Tot bool =
  assert_norm(List.Tot.length msg      = 34);
  assert_norm(List.Tot.length k        = 32);
  assert_norm(List.Tot.length expected = 16);
  let msg      : lseq uint8 34  = createL #uint8 msg in
  let k        : lseq uint8 keysize  = createL #uint8 k   in
  let expected : lseq uint8 blocksize = createL #uint8 expected in
  let mac      : lseq uint8 blocksize = poly1305 msg k in
  for_all2 #uint8 #uint8 (fun a b -> uint_to_nat #U8 a = uint_to_nat #U8 b) mac expected
