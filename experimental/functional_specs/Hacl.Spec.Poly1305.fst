module Hacl.Spec.Poly1305

open FStar.Mul
open FStar.Seq
open FStar.UInt8

(* Field types and parameters *)

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

(* Assumed for simplicity sake for now (see low-level/crypto *)
let rec little_endian (b:bytes) : Tot (n:nat) (decreases (Seq.length b)) =
  if Seq.length b = 0 then 0
  else
    UInt8.v (SeqProperties.head b) + pow2 8 * little_endian (SeqProperties.tail b)

assume val lemma_little_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))


let encode (w:word) : Tot elem =
  let l = length w in
  Math.Lemmas.pow2_le_compat 128 (8 * l);
  assert_norm(pow2 128 < pow2 130 - 5);
  lemma_little_endian_is_bounded w;
  pow2 (8 * l) +@ little_endian w


val poly: vs:text -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else 
    let v = SeqProperties.head vs in
    (encode v +@ poly (SeqProperties.tail vs) r) *@ r


private val fix: word_16 -> i:nat{i < 16} -> m:byte -> Tot word_16
let fix r i m = Seq.upd r i (FStar.UInt8.(Seq.index r i &^ m))

val encode_r: word_16 -> Tot elem
let encode_r r =
  assert_norm(pow2 8 = 256);
  assert_norm(pow2 128 < pow2 130 - 5);
  let r = fix r  3  15uy in // 0000****
  let r = fix r  7  15uy in
  let r = fix r 11  15uy in
  let r = fix r 15  15uy in
  let r = fix r  4 252uy in // ******00
  let r = fix r  8 252uy in
  let r = fix r 12 252uy in
  lemma_little_endian_is_bounded r;
  little_endian r


(** Final truncation to 128 bits to compute the tag *)
val trunc_1305: elem -> Tot elem
let trunc_1305 e = e % pow2 128

assume val little_bytes: 
  len:UInt32.t -> n:nat{n < pow2 (8 * FStar.UInt32.v len)} ->
  Tot (b:bytes{length b = UInt32.v len /\ n == little_endian b}) (decreases (UInt32.v len))
(* let rec little_bytes len n = *)
(*   admit(); // Temporary *)
(*   if len = 0ul then *)
(*     Seq.createEmpty *)
(*   else *)
(*     let open FStar.UInt32 in *)
(*     let len = len -^ 1ul in *)
(*     let byte = UInt8.uint_to_t (n % 256) in *)
(*     let n' = n / 256 in *)
(*     Math.Lemmas.pow2_plus 8 (8 * v len); *)
(*     assert(n' < pow2 (8 * v len )); *)
(*     let b' = little_bytes len n' in *)
(*     let b = SeqProperties.cons byte b' in *)
(*     assert(Seq.equal b' (SeqProperties.tail b)); *)
(*     b *)

(** Finish: truncate and pad (or pad and truncate) *)
val finish: a:elem -> s:tag -> Tot tag
let finish a s =
  (* REMARK: this is equivalent to n = (a + little_endian s) % pow2 128 *)
  let n = (trunc_1305 a + little_endian s) % pow2 128 in
  little_bytes 16ul n

val mac_1305: vs:text -> r:elem -> s:tag -> Tot tag
let mac_1305 vs r s = finish (poly vs r) s

val poly1305: msg:bytes -> k:bytes{length k = 32} -> Tot tag
let poly1305 msg k =
  let rec msg_to_text (msg:bytes) : Tot text (decreases (length msg)) =
    if length msg <= 16 then create 1 msg
    else SeqProperties.cons (slice msg 0 16) (msg_to_text (slice msg 16 (length msg))) in
  let text = msg_to_text msg in
  let r = encode_r (slice k 0 16) in
  let s = slice k 16 32 in
  mac_1305 text r s
