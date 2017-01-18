module Hacl.Spec.Poly1305

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
  if Seq.length vs = 0 then 0
  else
    let v = SeqProperties.head vs in
    (encode v +@ poly (SeqProperties.tail vs) r) *@ r


private val fix: word_16 -> i:nat{i < 16} -> m:byte -> Tot word_16
let fix r i m = Seq.upd r i (FStar.UInt8.(Seq.index r i &^ m))


module L = FStar.List.Tot
open FStar.SeqProperties

#set-options "--initial_fuel 0 --max_fuel 0"


unfold let clamp_mask : word_16 = createL [ 255uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy ]

type bytes_list = bl:list byte

unfold let mask = 0x0ffffffc0ffffffc0ffffffc0fffffff

#set-options "--initial_ifuel 1 --max_ifuel 1"

val little_endian_l: bl:bytes_list -> Tot nat
let rec little_endian_l bl =
  match bl with
  | [] -> 0
  | hd::tl -> UInt8.v hd + pow2 8 * little_endian_l tl

#set-options "--initial_ifuel 0 --max_ifuel 0"

let test = assert_norm(little_endian_l [ 255uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy ] = mask)

open FStar.SeqProperties

unfold let little_endian_post (b:bytes_list) (n:nat) : GTot Type0 =
  (* normalize  *)(little_endian_l (b) = n)

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:bytes) :
  Tot (n:nat{let l = seq_to_list b in little_endian_post l n})
      (decreases (Seq.length b)) =
  if Seq.length b = 0 then 0
  else
    UInt8.v (head b) + pow2 8 * little_endian (tail b)

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"

unfold let createL_wrapper_post (l:bytes_list) (n:nat) : GTot Type0 =
  normalize (n = little_endian_l l)

val createL: b:bytes_list -> Tot (s:bytes{let n = little_endian s in createL_wrapper_post b n})
let createL b = createL b

unfold let mask_list = [ 255uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy;
                         252uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy ]


let test' (u:unit) : Tot unit =
  assert(little_endian (createL [ 255uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy;
                                       252uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy ] )
              = 0x0ffffffc0ffffffc0ffffffc0fffffff)

unfold let r_mask : w:word_16{little_endian w = 0x0ffffffc0ffffffc0ffffffc0fffffff}
  = createL [ 255uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy; 252uy; 255uy; 255uy; 15uy ]

let rec lemma_little_endian_eq (b:bytes) : Lemma
  (requires (True))
  (ensures (little_endian b = Endianness.little_endian b))
  (decreases (length b))
  [SMTPat (Endianness.little_endian b)]
  = if length b = 0 then ()
    else lemma_little_endian_eq (slice b 1 (length b))


let encode_r_post (rb:word_16) (r:elem) : GTot Type0 =
  lemma_little_endian_is_bounded rb;
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  r = UInt.logand #128 (little_endian rb) 0x0ffffffc0ffffffc0ffffffc0fffffff


val encode_r: rb:word_16 -> Tot (r:elem{encode_r_post rb r})
let encode_r rb =
  lemma_little_endian_is_bounded rb;
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  UInt.logand #128 (little_endian rb) (little_endian r_mask)


(** Final truncation to 128 bits to compute the tag *)
val trunc_1305: elem -> Tot elem
let trunc_1305 e = e % normalize_term (pow2 128)


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
