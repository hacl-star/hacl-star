module Hacl.Spec.Chacha20

module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.Seq
open FStar.UInt32

(* not relying on protected integers in the spec
open Hacl.Cast
open Hacl.UInt32

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_s = seq H8.t
*)

(* This should go elsewhere! *)

(*
private val lemma_max_uint32: n:nat ->
  Lemma (requires (n = 32))
        (ensures (pow2 n = 4294967296))
        [SMTPat (pow2 n)]
private let lemma_max_uint32 n = assert_norm (pow2 32 = 4294967296)

(* Needs to go to a general library *)
let bytes_to_h32 (k:uint8_s{length k >= 4}) : Tot h32
  = let k0 = Seq.index k 0 in
    let k1 = Seq.index k 1 in
    let k2 = Seq.index k 2 in
    let k3 = Seq.index k 3 in
    let z = sint8_to_sint32 k0 |^ (sint8_to_sint32 k1 <<^ 8ul)
            |^ (sint8_to_sint32 k2 <<^ 16ul) |^ (sint8_to_sint32 k3 <<^ 24ul) in
    z

(* Needs to go to a general library *)
let h32_to_bytes (x:h32) : Tot (s':uint8_s{length s' = 4})
  = let s = Seq.create 4 (uint8_to_sint8 0uy) in
    let s = Seq.upd s 0 (sint32_to_sint8 x) in
    let s = Seq.upd s 1 (sint32_to_sint8 (x >>^ 8ul)) in
    let s = Seq.upd s 2 (sint32_to_sint8 (x >>^ 16ul)) in
    let s = Seq.upd s 3 (sint32_to_sint8 (x >>^ 24ul)) in
    s

#set-options "--initial_fuel 1 --max_fuel 1"

val map2: ('a -> 'b -> Tot 'c) -> a:list 'a -> b:list 'b{List.Tot.length a = List.Tot.length b} -> Tot (c:list 'c{List.Tot.length c = List.Tot.length a}) (decreases (List.Tot.length a))
let rec map2 f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | hd::tl, hd'::tl' -> (f hd hd')::(map2 f tl tl')
*)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val iter: n:nat -> (f: 'a -> Tot 'a) -> 'a -> 'a 
let rec iter n f x = if n = 0 then x else iter (n-1) f (f x)

type lbytes l = b:seq UInt8.t {length b = l}

// left rotation by s bits; could go elsewhere
inline_for_extraction let rotate (a:UInt32.t) (s:UInt32.t {v s<32}) : Tot UInt32.t =
  (a <<^ s) |^ (a >>^ (32ul -^ s))

(*** pure Chacha20 ***)
// roughly aligned to Crypto.Symmetric.Chacha20

inline_for_extraction let keylen = 32 (* in bytes *)
inline_for_extraction let blocklen = 64  (* in bytes *)
inline_for_extraction let ivlen = 12 (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type iv = lbytes ivlen
type counter = UInt32.t

// internally, blocks are represented as 16 x 4-byte integers
type state = m:seq UInt32.t {length m = blocklen / 4}
type idx = n:nat{n < blocklen / 4}
type shuffle = state -> Tot state 

val line: idx -> idx -> idx -> s:UInt32.t {v s < 32} -> shuffle
let line a b d s m = 
  let m = upd m a (index m a +%^ index m b) in
  let m = Seq.upd m d (rotate (index m d ^^  index m a) s) in
  m

// using @ as a functional substitute for ;
let op_At f g = fun x -> g (f x) 

let quarter_round a b c d : shuffle = 
  line a b d 16ul @ 
  line c d b 12ul @
  line a b d 8ul @ 
  line c d b 7ul 

let column_round : shuffle = 
  quarter_round 0 4 8 12 @
  quarter_round 1 5 9 13 @
  quarter_round 2 6 10 14 @
  quarter_round 3 7 11 15

let diagonal_round : shuffle = 
  quarter_round 0 5 10 15 @
  quarter_round 1 6 11 12 @
  quarter_round 2 7 8 13 @
  quarter_round 3 4 9 14

let double_round: shuffle = column_round @ diagonal_round 

let rec rounds : shuffle = iter 10 double_round (* 20 rounds *)

(* state initialization *) 

assume val uint32_of_bytes: b:seq UInt8.t {length b = 4} -> Tot UInt32.t
assume val uint32_to_bytes: UInt32.t -> Tot (b:seq UInt8.t {length b = 4})

val uint32s_to_bytes: m:seq UInt32.t -> Tot (b:lbytes (4*length m)) (decreases (length m))
let rec uint32s_to_bytes m = 
  if length m = 0 then Seq.createEmpty else
  uint32_to_bytes (Seq.head m) @| uint32s_to_bytes (Seq.tail m)

let set (i:idx) v (s:state) : state = Seq.upd s i v
val fill: i:nat -> len:nat {i + len <= 16}-> lbytes (4 * len) -> Tot shuffle (decreases len)
let rec fill i len src =
  if len = 0 then (fun m -> m) 
  else 
    set i (uint32_of_bytes (slice src 0 4)) @  (* or bytes_to_h32 ? *)
    fill (i + 1) (len - 1) (slice src 4 (4*len)) 

inline_for_extraction let constant_0 = 0x61707865ul
inline_for_extraction let constant_1 = 0x3320646eul
inline_for_extraction let constant_2 = 0x79622d32ul
inline_for_extraction let constant_3 = 0x6b206574ul

let init0 (k:key) (n:iv) (c:counter): shuffle =
  set 0 constant_0 @
  set 1 constant_1 @
  set 2 constant_2  @
  set 3 constant_3  @
  fill 4 8 k @ 
  set 12 c @ 
  fill 13 3 n

let init (k:key) (n:iv) (c:counter): state = 
  init0 k n c (Seq.create (blocklen/4) 0ul)

let lemma_incr (k:key) (n:iv) (c:counter {v c < pow2 32 - 1}) :
  Lemma(
  let s = init k n c in 
  index s 12 == c /\
  Seq.equal (init k n (c +^ 1ul)) (set 12 (index s 12 +^ 1ul) s))
  = 
  let s = init k n c in 
  assert_norm(index s 12 == c);
  assert_norm(Seq.equal (init k n (c +^ 1ul)) (set 12 (index s 12 +^ 1ul) s))


val map2: 
  #a:Type -> 
  f:(a -> a -> Tot a) -> 
  s0: seq a -> 
  s1: seq a {length s0 = length s1} -> 
  Tot (s: seq a {length s = length s0}) (decreases (length s0))
let rec map2 #a f s0 s1 = 
  if length s0 = 0 then createEmpty else
  cons (f (head s0) (head s1)) (map2 f (tail s0) (tail s1))

(*
val add: idx -> state -> state -> Tot state 
let add i m m0 = 
*)

//val add_state: state -> state -> Tot state
////17-02-09 strangely, I had to unfold idx
////let add (m0:state) (m1:state) (i:idx) = index m0 i +%^ index m1 i 
//let add (m0:state) (m1:state) (i:nat {i < blocklen/4}) = index m0 i +%^ index m1 i 
val add_state: state -> state -> Tot state
let add_state m0 m1 = map2 (fun x y -> x +%^ y) m0 m1 

val compute: key -> iv -> counter -> Tot (lbytes blocklen)
let compute k n c =
  let m = init k n c in 
  let m = add_state m (rounds m) in
  uint32s_to_bytes m

// rename to block?
val chacha20: len:nat {len <= blocklen} -> key -> iv -> counter -> Tot (lbytes len)
let chacha20 len k iv c = slice (compute k iv c) 0 len

let xor_block (m0 m1: block) = map2 (fun x y -> FStar.UInt8.(x ^^ y)) m0 m1

// used in AEAD but not great; truncation should be handled in the mode.

(*** Counter-mode encryption ***)
// a generic construction on top of cipher--- not Chacha20-specific
// could move to its own spec; see also AEAD

private let prf = chacha20

val counter_mode: 
  k:key -> n:iv -> counter:UInt32.t -> 
  plain:seq UInt8.t {v counter + length plain / blocklen < pow2 32} ->
  Tot (lbytes (length plain))
  (decreases (length plain))

// migrate to FStar.Seq
val xor: #len:nat -> x:lbytes len -> y:lbytes len -> Tot (lbytes len)
let rec xor #len x y = 
  if len = 0 then createEmpty 
  else cons (UInt8.logxor (head x) (head y)) (xor #(len -1) (tail x) (tail y))

#reset-options "--z3rlimit 40 --max_fuel 2"
let rec counter_mode key iv counter plain =
  let len = length plain in 
  if len = 0 then Seq.createEmpty else
  if len < blocklen 
  then (* encrypt final partial block *)
      let mask = prf len key iv counter in 
      xor plain mask
  else (* encrypt full block *)
      let (b, plain) = split plain blocklen in 
      let mask = prf blocklen key iv counter in 
      let cipher = counter_mode key iv (counter +^ 1ul) plain in
      xor b mask @| cipher 


(* older spec for counter-mode encryption: 

val encrypt_bytes: k:key -> counter:ctr -> n:iv -> plaintext:bytes -> Tot (lbytes (lenght plaintext))
let chacha20_encrypt k counter n plaintext =
  let max = length plaintext / 64 in
  let rem = length plaintext % 64 in
  let rec loop (j:nat{j <= max}) (encrypted_message:uint8_s) : Tot uint8_s (decreases (max - j)) =
    if j = max then encrypted_message
    else let keystream = chacha_block k counter n in
         let block = slice plaintext (j*64) (j*64+64) in
         let encrypted_message = encrypted_message @|
                                (Seq.seq_of_list (map2 (H8.logxor)
                                                           (Seq.seq_to_list keystream)
                                                           (Seq.seq_to_list block))) in
         loop (j+1) encrypted_message in
  let encrypted_message = loop 0 (createEmpty) in
  if rem = 0 then encrypted_message
  else let keystream = chacha_block k (UInt32.uint_to_t max) n in
       let block = slice plaintext max (length plaintext) in
       let encrypted_mesage = encrypted_message @|
                              Seq.seq_of_list (map2 (H8.logxor)
                                                        (Seq.seq_to_list keystream)
                                                        (Seq.seq_to_list (slice block 0 rem))) in
       encrypted_message
*)
