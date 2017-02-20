module Spec.Poly1305_exp

open FStar.Seq
open FStar.UInt8
open FStar.Endianness

(* Field types and parameters *)

private let rec lemma_append (#a:Type) (x:list a) (y:list a) (z:list a) :
  Lemma ((x @ y) @ z == x @ (y @ z))
  = admit()


val split_l: #a:Type -> l:list a -> n:nat{n <= List.Tot.length l} -> Tot (t:(list a * list a){fst t @ snd t == l /\ List.Tot.length (fst t) = n}) (decreases n)
let rec split_l #a l n =
  if n = 0 then (List.Tot.append_nil_l l; [], l)
  else
    let hd = List.Tot.hd l in
    let tl = List.Tot.tl l in
    let l1, l2 = split_l tl (n-1) in
    hd::l1, l2


val slice_l: #a:Type -> l:list a -> x:nat -> y:nat{x <= y /\ y <= List.Tot.length l} -> Tot (l':list a{List.Tot.length l' = y - x})
let slice_l #a l x y =
  let w, ll = split_l l x in
  List.Tot.append_length w ll;
  let lll, _ = split_l ll (y - x) in
  lll


open FStar.Mul

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

unfold let prime : (p:pos{p = pow2 130 - 5}) =
  assert_norm(pow2 130 - 5 = 0x3fffffffffffffffffffffffffffffffb);
  0x3fffffffffffffffffffffffffffffffb

type elem = e:int{e >= 0 /\ e < prime}

let zero : elem = 0
let one  : elem = 1

unfold val fadd: elem -> elem -> Tot elem
unfold let fadd e1 e2 = (e1 + e2) % prime
unfold let op_Plus_At e1 e2 = fadd e1 e2

unfold val fmul: elem -> elem -> Tot elem
unfold let fmul e1 e2 = (e1 * e2) % prime
unfold let op_Star_At e1 e2 = fmul e1 e2


(* Types from Low-level crypto *)
type byte = FStar.UInt8.t
type bytes = seq byte
type word = w:bytes{length w <= 16}
type word_16 = w:bytes{length w = 16}
type tag = word_16
type text = seq word


module L = FStar.List.Tot
open FStar.Seq


unfold let clamp_mask : word_16 = createL [ 255uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy ]

unfold let mask = 0x0ffffffc0ffffffc0ffffffc0fffffff


#set-options "--initial_ifuel 1 --max_ifuel 1"

val little_endian_l: bl:list byte -> GTot nat
let rec little_endian_l bl =
  match bl with
  | [] -> 0
  | hd::tl -> UInt8.v hd + pow2 8 * little_endian_l tl

#set-options "--initial_ifuel 0 --max_ifuel 0"

let test = assert_norm(little_endian_l [ 255uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy;
                                                        252uy; 255uy; 255uy; 15uy ] = mask)

open FStar.Seq

unfold let little_endian_post (b:list byte) (n:nat) : GTot Type0 =
  (* normalize  *)(little_endian_l (b) = n)


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:bytes) :
  Tot (n:nat{let l = seq_to_list b in little_endian_post l n})
      (decreases (Seq.length b)) =
  if Seq.length b = 0 then 0
  else
    UInt8.v (head b) + pow2 8 * little_endian (tail b)

type lbytes_l (n:nat) : Type0 = l:list byte{List.Tot.length l = n}

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

(* unfold let eq (x y:nat) = x = y *)

val little_bytes_l: len:UInt32.t -> n:nat{n < pow2 (8 * UInt32.v len)} ->
  Tot (b:lbytes_l (UInt32.v len){(* little_bytes_l_post len n b *)n = little_endian_l b}) (decreases (UInt32.v len))
let rec little_bytes_l len n =
  if len = 0ul then []
  else
    let len' = FStar.UInt32.(len -^ 1ul) in 
    let byte = UInt8.uint_to_t (n % 256) in
    let n' = n / 256 in 
    Math.Lemmas.pow2_plus 8 (8 * UInt32.v len');
    let b':lbytes_l (UInt32.v len') = little_bytes_l len' n' in
    let b:lbytes_l (UInt32.v len) = byte::b' in
    Math.Lemmas.lemma_div_mod n 256;
    b


unfold let little_bytes_post (l:UInt32.t) (n:nat{n < pow2 (8 * UInt32.v l)}) (b:lbytes (UInt32.v l)) : GTot Type0 =
  little_bytes_l l n = seq_to_list b

val little_bytes:
  len:FStar.UInt32.t -> n:nat{n < pow2 (8 * UInt32.v len)} ->
  Tot (b:lbytes (UInt32.v len) {little_bytes_post len n b}) (decreases (UInt32.v len))
let rec little_bytes len n =
  if len = 0ul then
    createEmpty
  else
    let len = FStar.UInt32.(len -^ 1ul) in
    let byte = UInt8.uint_to_t (n % 256) in
    let n' = n / 256 in
    Math.Lemmas.pow2_plus 8 (8 * UInt32.v len);
    assert(n' < pow2 (8 * UInt32.v len ));
    let b' = little_bytes len n' in
    let b = cons byte b' in
    assert(Seq.equal b' (tail b));
    b


#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"

unfold let createL_wrapper_post (l:list byte) (n:nat) : GTot Type0 =
  normalize (n = little_endian_l l)

val createL: b:list byte -> Tot (s:bytes{let n = little_endian s in createL_wrapper_post b n})
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
  (ensures (little_endian b = FStar.Endianness.little_endian b))
  (decreases (length b))
  [SMTPat (FStar.Endianness.little_endian b)]
  = if length b = 0 then ()
    else lemma_little_endian_eq (slice b 1 (length b))


unfold let encode_r_post (rb:word_16) (r:elem) : GTot Type0 =
  lemma_little_endian_is_bounded rb;
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  normalize (r = UInt.logand #128 (little_endian rb) 0x0ffffffc0ffffffc0ffffffc0fffffff)


val encode_r: rb:word_16 -> Tot (r:elem{encode_r_post rb r})
let encode_r rb =
  lemma_little_endian_is_bounded rb;
  assert_norm(pow2 128 = 0x100000000000000000000000000000000);
  UInt.logand #128 (little_endian rb) (little_endian r_mask)


type word_l = list byte
type text_l = list word_l


let encode_l (w:word_l) : GTot elem =
  admit();
  let l = List.Tot.length w in
  Math.Lemmas.pow2_le_compat 128 (8 * l);
  assert_norm(pow2 128 < pow2 130 - 5);
  pow2 (8 * l) +@ little_endian_l w


unfold let encode_post (w:word) (e:elem) : GTot Type0 =
  let wl = seq_to_list w in
  e = encode_l wl


unfold let encode (w:word) : Tot (e:elem{encode_post w e}) =
  let l = length w in
  Math.Lemmas.pow2_le_compat 128 (8 * l);
  assert_norm(pow2 128 < pow2 130 - 5);
  lemma_little_endian_is_bounded w;
  pow2 (8 * l) +@ little_endian w


val encode_bytes_l: txt:bytes -> Tot (text_l) (decreases (Seq.length txt))
let rec encode_bytes_l txt =
  let l = Seq.length txt in
  if l = 0 then []
  else
    let l0 = FStar.Math.Lib.min l 16 in
    let w, txt = Seq.split txt l0 in
    (encode_bytes_l txt)@[seq_to_list w]

val encode_bytes_l': txt:list byte -> Tot (text_l) (decreases (List.Tot.length txt))
let rec encode_bytes_l' txt =
  let l = List.Tot.length txt in
  if l = 0 then []
  else
    let l0 = FStar.Math.Lib.min l 16 in
    let w, txt = split_l txt l0 in
    List.Tot.append_length w txt;
    (encode_bytes_l' txt)@[w]


val text_to_text_l: txt:text -> Tot (txtl:text_l) (decreases (Seq.length txt))
let rec text_to_text_l txt =
  let l = Seq.length txt in
  if l = 0 then []
  else let h = Seq.head txt in
       let tl = Seq.tail txt in
       seq_to_list h::text_to_text_l tl


unfold let encode_bytes_post (txt:bytes) (t:text) : GTot Type0 =
  text_to_text_l t == encode_bytes_l' (seq_to_list txt)


#reset-options "--initial_fuel 0 --max_fuel 2 --z3rlimit 100"

val encode_bytes: txt:bytes -> Tot (t:text{encode_bytes_post txt t}) (decreases (Seq.length txt))
let rec encode_bytes txt =
  admit();
  let l = Seq.length txt in
  if l = 0 then
    begin
    Seq.createEmpty
    end
  else
    let l0 = FStar.Math.Lib.min l 16 in
    let w, txt = Seq.split txt l0 in
    Seq.snoc (encode_bytes txt) w


val poly_l: vs:text_l -> r:elem -> GTot (a:elem) (decreases (List.Tot.length vs))
let rec poly_l vs r =
  if List.Tot.length vs = 0 then zero
  else
    let v = List.Tot.hd vs in
    (encode_l v +@ poly_l (List.Tot.tail vs) r) *@ r


unfold let poly_post (vs:text) (r:elem) (a:elem) : GTot Type0 =
  let vsl = text_to_text_l vs in
  poly_l vsl r = a


val poly: vs:text -> r:elem -> Tot (a:elem{poly_post vs r a}) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then zero
  else
    let v = Seq.head vs in
    (encode v +@ poly (Seq.tail vs) r) *@ r


type tag_l = l:list byte{List.Tot.length l = 16}



val finish_l: a:elem -> s:tag_l -> GTot tag_l
let finish_l a s =
  let n = (a + little_endian_l s) % pow2 128 in
  little_bytes_l 16ul n

unfold let finish_post (a:elem) (s:tag) (t:tag) : GTot Type0 =
  seq_to_list t = finish_l a (seq_to_list s)

(** Finish: truncate and pad (or pad and truncate) *)
val finish: a:elem -> s:tag -> Tot (t:tag{finish_post a s t})
let finish a s =
  (* REMARK: this is equivalent to n = (a + little_endian s) % pow2 128 *)
  (* let n = (trunc_1305 a + little_endian s) % pow2 128 in *)
  let n = (a + little_endian s) % pow2 128 in
  little_bytes 16ul n


val mac_1305_l: vs:text_l -> r:elem -> s:tag_l -> GTot tag_l
let mac_1305_l vs r s = finish_l (poly_l vs r) s


unfold let mac_1305_post (vs:text) (r:elem) (s:tag) (t:tag) : GTot Type0 =
  seq_to_list t = mac_1305_l (text_to_text_l vs) r (seq_to_list s)

val mac_1305: vs:text -> r:elem -> s:tag -> Tot (t:tag{mac_1305_post vs r s t})
let mac_1305 vs r s = finish (poly vs r) s


unfold let slice_post (b:bytes) (x:nat) (y:nat{x <= y /\ y <= length b}) (t:bytes) : GTot Type0 =
  seq_to_list t == slice_l (seq_to_list b) x y


(* val slice: bytes -> x:nat -> y:nat -> Tot (tuple2 bytes bytes) *)
(* let slice  *)

val poly1305_l: msg:list byte -> k:list byte{List.Tot.length k = 32} -> GTot (tag_l)
let poly1305_l msg k =
  let text = encode_bytes_l' msg in
  assert_norm(pow2 128 < pow2 130 - 5);
  let kr = slice_l k 0 16 in
  assume ((little_endian_l (slice_l k 0 16)) < pow2 128);
  let r = UInt.logand #128 (little_endian_l (slice_l k 0 16)) 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let s = slice_l k 16 32 in
  cut (List.Tot.length s = 16);
  mac_1305_l text r s


unfold let poly1305_post (msg:bytes) (k:bytes{length k = 32}) (t:tag) : GTot Type0 =
  seq_to_list t == poly1305_l (seq_to_list msg) (seq_to_list k)

val poly1305: msg:bytes -> k:bytes{length k = 32} -> Tot (t:tag{poly1305_post msg k t})
let poly1305 msg k =
  admit();
  let text = encode_bytes msg in
  let r = encode_r (slice k 0 16) in
  let s = slice k 16 32 in
  mac_1305 text r s


unfold let k=  [0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy;
                0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy;
                0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy;
                0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy]


let test () =
  // RFC test vectors
  let msg = createL [0x43uy; 0x72uy; 0x79uy; 0x70uy; 0x74uy; 0x6fuy; 0x67uy; 0x72uy;
                     0x61uy; 0x70uy; 0x68uy; 0x69uy; 0x63uy; 0x20uy; 0x46uy; 0x6fuy;
                     0x72uy; 0x75uy; 0x6duy; 0x20uy; 0x52uy; 0x65uy; 0x73uy; 0x65uy;
                     0x61uy; 0x72uy; 0x63uy; 0x68uy; 0x20uy; 0x47uy; 0x72uy; 0x6fuy;
                     0x75uy; 0x70uy] in
  (* let key:k:list byte{List.Tot.length k = 32} = createL [0x85uy; 0xd6uy; 0xbeuy; 0x78uy; 0x57uy; 0x55uy; 0x6duy; 0x33uy; *)
  (*                    0x7fuy; 0x44uy; 0x52uy; 0xfeuy; 0x42uy; 0xd5uy; 0x06uy; 0xa8uy; *)
  (*                    0x01uy; 0x03uy; 0x80uy; 0x8auy; 0xfbuy; 0x0duy; 0xb2uy; 0xfduy; *)
  (*                    0x4auy; 0xbfuy; 0xf6uy; 0xafuy; 0x41uy; 0x49uy; 0xf5uy; 0x1buy] in *)
  (*                    admit() *)
  let text = encode_bytes msg in
  assert_norm(List.Tot.length k = 32);
  let k = normalize_term (createL k) in
  let r = encode_r (slice k 0 16) in
  assert_norm(r == 0x806d5400e52447c036d555408bed685); admit();
  let s = slice k 16 32 in
  assert_norm(0xa927010caf8b2bc2c6365130c11d06a8 = little_endian (poly1305 (msg) (key)))
