(* Implementation of Poly1305 based on the rfc7539 *)
module Hacl.Symmetric.Poly1305

open FStar.Mul
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open FStar.Buffer
open Math.Axioms
open Math.Lib
open Math.Lemmas
open Hacl.UInt64
open Hacl.Cast
open Hacl.SBuffer
open Hacl.Symmetric.Poly1305.Parameters
open Hacl.Symmetric.Poly1305.Bigint
open Hacl.Symmetric.Poly1305.Bignum.Lemmas
open Hacl.Symmetric.Poly1305.Bignum
open Hacl.Symmetric.Poly1305.Lemmas
open Utils


(* Module abbreviations *)
module B  = Hacl.SBuffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module H8   = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

(* Type abbreviations *)
type elemB = bigint
type wordB = bytes

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

(*** Poly1305 code ***)
let mk_mask (nbits:U32.t{U32.v nbits < 64}) :
  Tot (z:H64.t{v z = pow2 (U32.v nbits) - 1})
  = Math.Lib.pow2_increases_lemma 64 (U32.v nbits);
    H64 ((uint64_to_sint64 1uL <<^ nbits) -^ uint64_to_sint64 1uL)

(* Formats a wordB into an elemB *)
val toGroup: a:elemB -> b:wordB{length b = 16 /\ disjoint a b} -> STStack unit
  (requires (fun h -> live h a /\ B.live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let toGroup b s =
  let h0 = HST.get() in
  let mask_26 = mk_mask 26ul in
  let s0 = sub s 0ul  4ul in
  let s1 = sub s 4ul  4ul in
  let s2 = sub s 8ul  4ul in
  let s3 = sub s 12ul 4ul in
  let n0 = (uint32_of_bytes s0) in
  let n1 = (uint32_of_bytes s1) in
  let n2 = (uint32_of_bytes s2) in
  let n3 = (uint32_of_bytes s3) in
  let n0 = sint32_to_sint64 n0 in
  let n1 = sint32_to_sint64 n1 in
  let n2 = sint32_to_sint64 n2 in
  let n3 = sint32_to_sint64 n3 in
  let n0' = n0 &^ mask_26 in
  let n1' = (n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26) in
  let n2' = (n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26) in
  let n3' = (n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26) in
  let n4' = (n3 >>^ 8ul) in
  upd b 0ul n0';
  upd b 1ul n1';
  upd b 2ul n2';
  upd b 3ul n3';
  upd b 4ul n4'

(* Formats a wordB into an elemB *)
val toGroup_plus_2_128: a:elemB -> b:wordB{length b = 16 /\ disjoint a b} -> STL unit
  (requires (fun h -> live h a /\ B.live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let toGroup_plus_2_128 b s =
  toGroup b s;
  let h0 = HST.get() in
  let b4 = b.(4ul) in
  let b4' = b4 +%^ (uint64_to_sint64 1uL <<^ 24ul) in
  b.(4ul) <- b4'

val trunc1305_: a:elemB -> b:wordB{disjoint a b /\ length b >= 16} -> STL unit
  (requires (fun h -> live h a /\ B.live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 -> B.live h1 b /\ modifies_1 b h0 h1))
let trunc1305_ b s =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  (* (\* JK: some bitvector theory would simplify a lot the rest of the proof *\) *)
  (* admit(); // TODO *)
  let s0 = sint64_to_sint8 b0 in
  let s1 = sint64_to_sint8 (b0 >>^ 8ul) in
  let s2 = sint64_to_sint8 (b0 >>^ 16ul) in
  let s3 = sint64_to_sint8 ((b0 >>^ 24ul) +%^ (b1 <<^ 2ul)) in
  let s4 = sint64_to_sint8 (b1 >>^ 6ul) in
  let s5 = sint64_to_sint8 (b1 >>^ 14ul) in
  let s6 = sint64_to_sint8 ((b1 >>^ 22ul) +%^ (b2 <<^ 4ul)) in
  let s7 = sint64_to_sint8 (b2 >>^ 4ul) in
  let s8 = sint64_to_sint8 (b2 >>^ 12ul) in
  let s9 = sint64_to_sint8 ((b2 >>^ 20ul) +%^ (b3 <<^ 6ul)) in
  let s10 = sint64_to_sint8 (b3 >>^ 2ul) in
  let s11 = sint64_to_sint8 (b3 >>^ 10ul) in
  let s12 = sint64_to_sint8 (b3 >>^ 18ul) in
  let s13 = sint64_to_sint8 (b4) in
  let s14 = sint64_to_sint8 (b4 >>^ 8ul) in
  let s15 = sint64_to_sint8 (b4 >>^ 16ul) in
  s.(0ul) <- s0;
  s.(1ul) <- s1;
  s.(2ul) <- s2;
  s.(3ul) <- s3;
  s.(4ul) <- s4;
  s.(5ul) <- s5;
  s.(6ul) <- s6;
  s.(7ul) <- s7;
  s.(8ul) <- s8;
  s.(9ul) <- s9;
  s.(10ul) <- s10;
  s.(11ul) <- s11;
  s.(12ul) <- s12;
  s.(13ul) <- s13;
  s.(14ul) <- s14;
  s.(15ul) <- s15;
  ()

val trunc1305: a:elemB -> b:wordB{disjoint a b /\ length b >= 16} -> STL unit
  (requires (fun h -> live h a /\ B.live h b /\ disjoint a b))
  (ensures  (fun h0 _ h1 -> live h1 a /\ B.live h1 b /\ modifies_2 a b h0 h1))
let trunc1305 b s =
  finalize b;
  trunc1305_ b s

(* Clamps the key, see RFC *)
val clamp: r:wordB{length r = 16} -> STL unit
  (requires (fun h -> B.live h r))
  (ensures (fun h0 _ h1 -> B.live h1 r /\ modifies_1 r h0 h1))
let clamp r =
  let mask_15 = uint8_to_sint8 15uy in
  let mask_252 = uint8_to_sint8 252uy in
  r.(3ul)  <- (H8 (r.(3ul) &^ mask_15));
  r.(7ul)  <- (H8 (r.(7ul) &^ mask_15));
  r.(11ul) <- (H8 (r.(11ul) &^ mask_15));
  r.(15ul) <- (H8 (r.(15ul) &^ mask_15));
  r.(4ul)  <- (H8 (r.(4ul) &^ mask_252));
  r.(8ul)  <- (H8 (r.(8ul) &^ mask_252));
  r.(12ul) <- (H8 (r.(12ul) &^ mask_252));
  ()

(* * ******************************************** *)
(* *        Polynomial computation step           *)
(* * ******************************************** *)

(**
    Runs "Acc = ((Acc+block)*r) % p." on the accumulator, the well formatted block of the message
    and the clamped part of the key
    *)
val add_and_multiply: acc:elemB -> block:elemB{disjoint acc block} -> r:elemB{disjoint acc r /\ disjoint block r} -> STL unit
  (requires (fun h -> live h block /\ live h acc /\ live h r))
  (ensures (fun h0 _ h1 -> live h1 acc /\ modifies_1 acc h0 h1))
let add_and_multiply acc block r =
  push_frame();
  let tmp = create (uint64_to_sint64 0UL) (U32 (2ul *^ nlength -^ 1ul)) in
  fsum' acc block;
  multiplication tmp acc r;
  modulo tmp;
  blit tmp 0ul acc 0ul nlength;
  pop_frame()

(**
   Sets the accumulator to the value '0'
   *)
val zeroB: a:elemB -> STL unit
  (requires (fun h -> live h a))
  (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let zeroB a =
  let zero = uint64_to_sint64 0uL in
  a.(0ul) <- zero;
  a.(1ul) <- zero;
  a.(2ul) <- zero;
  a.(3ul) <- zero;
  a.(4ul) <- zero

(* Initialization function:
   - zeros the accumulator
   - clamp the first half of the key
   - stores the well-formatted first half of the key in 'r' *)
val poly1305_init: acc:elemB -> // Accumulator
  r:elemB{disjoint acc r} -> // First half of the key, on which the polynome is evaluated
  key:bytes{length key >= 32 /\ disjoint acc key /\ disjoint r key} ->
  STStack unit
  (requires (fun h -> live h acc /\ live h r /\ B.live h key))
  (ensures  (fun h0 log h1 -> live h1 acc /\ live h1 r /\ modifies_2 acc r h0 h1))
let poly1305_init acc r key =
  push_frame();
  let h0 = HST.get() in
  let r' = sub key 0ul 16ul in
  let r'' = create (uint8_to_sint8 0uy) 16ul in
  let h1 = HST.get() in
  (* Zero the accumulator *)
  zeroB acc;
  let h2 = HST.get() in
  assert(modifies_2_1 acc h0 h2);
  (* Format the keys *)
  (* Make a copy of the first half of the key to clamp it *)
  blit r' 0ul r'' 0ul 16ul;
  let h3 = HST.get() in
  assert(modifies_2_1 acc h0 h3);
  (* Clamp r *)
  clamp r'';
  let h4 = HST.get() in
  assert(modifies_2_1 acc h0 h4);
  (* Format r to elemB *)
  toGroup r r'';
  let h5 = HST.get() in
  assert(modifies_3_2 acc r h0 h5);
  pop_frame()

(**
   Update function:
   - takes a ghost log
   - takes a message block, appends '1' to it and formats it to bigint format
   - runs acc = ((acc*block)+r) % p
   *)
val poly1305_update:
  msg:wordB{length msg >= 16} ->
  acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} -> STStack unit
    (requires (fun h -> B.live h msg /\ live h acc /\ live h r))
    (ensures (fun h0 updated_log h1 -> live h1 acc /\ modifies_1 acc h0 h1))
let poly1305_update msg acc r =
  push_frame();
  let n = sub msg 0ul 16ul in // Select the message to update
  let block = create (uint64_to_sint64 0uL) nlength in
  toGroup_plus_2_128 block n;
  add_and_multiply acc block r;
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0"

(* Loop over Poly1305_update *)
val poly1305_loop:
  msg:bytes ->
  acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} ->
  ctr:u32{length msg >= 16 * U32.v ctr} ->
  STL unit
    (requires (fun h -> B.live h msg /\ live h acc /\ live h r))
    (ensures (fun h0 _ h1 -> live h1 acc /\ modifies_1 acc h0 h1))
let rec poly1305_loop msg acc r ctr =
  if U32 (ctr =^ 0ul) then ()
  else begin
    let updated_log = poly1305_update msg acc r in
    let msg = offset msg 16ul in
    poly1305_loop msg acc r (U32 (ctr -^ 1ul))
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val poly1305_last_word: msg:wordB -> n:wordB{length n = 16 /\ disjoint msg n} -> len:u32{U32.v len <= length msg /\ U32.v len < 16} -> STStack unit
  (requires (fun h -> B.live h msg /\ B.live h n))
  (ensures  (fun h0 _ h1 -> B.live h1 n /\ modifies_1 n h0 h1))
let poly1305_last_word msg n len =
  blit msg 0ul n 0ul len;
  upd n len (uint8_to_sint8 1uy)

val poly1305_last_block: n:wordB{length n = 16} -> acc:elemB{disjoint n acc} ->
  r:elemB{disjoint n r /\ disjoint acc r} -> STStack unit
  (requires (fun h -> B.live h n /\ live h acc /\ live h r))
  (ensures  (fun h0 _ h1 -> live h1 acc /\ modifies_1 acc h0 h1))
let poly1305_last_block n acc r =
  push_frame();
  let block = create (uint64_to_sint64 0uL) nlength in
  toGroup block n;
  add_and_multiply acc block r;
  pop_frame()

val poly1305_last_: msg:wordB{length msg < 16} -> acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} -> len:u32{U32.v len > 0 /\ U32.v len <= length msg} ->
  STL unit
    (requires (fun h -> B.live h msg /\ live h acc /\ live h r))
    (ensures (fun h0 _ h1 -> live h1 acc /\ modifies_1 acc h0 h1))
let poly1305_last_ msg acc r len =
  push_frame();
  let n = create (uint8_to_sint8 0uy) 16ul in
  poly1305_last_word msg n len;
  poly1305_last_block n acc r;
  pop_frame()

(**
   Performs the last step if there is an incomplete block
   NB: Not relevant for AEAD-ChachaPoly which only uses complete blocks of 16 bytes, hence
       only the 'update' and 'loop' functions are necessary there
   *)
val poly1305_last: msg:wordB{length msg < 16} -> acc:elemB{disjoint msg acc} ->
  r:elemB{disjoint msg r /\ disjoint acc r} -> len:u32{U32.v len <= length msg} ->
  STL unit
    (requires (fun h -> B.live h msg /\ live h acc /\ live h r))
    (ensures (fun h0 _ h1 -> live h1 acc /\ modifies_1 acc h0 h1))
let poly1305_last msg acc r len =
  if U32 (len =^ 0ul) then ()
  else (
    poly1305_last_ msg acc r len
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val add_word: a:wordB{length a = 16} -> b:wordB{length b = 16 /\ disjoint a b} -> STL unit
  (requires (fun h -> B.live h a /\ B.live h b))
  (ensures  (fun h0 _ h1 -> B.live h1 a /\ modifies_1 a h0 h1))
let add_word a b =
  let a04:H64.t = let (x:H32.t) = uint32_of_bytes a in sint32_to_sint64 x  in
  let a48:H64.t = let (x:H32.t) = uint32_of_bytes (offset a 4ul) in sint32_to_sint64 x in
  let a812:H64.t = let (x:H32.t) = uint32_of_bytes (offset a 8ul) in sint32_to_sint64 x in
  let a1216:H64.t = let (x:H32.t) = uint32_of_bytes (offset a 12ul) in sint32_to_sint64 x in
  let b04:H64.t = let (x:H32.t) = uint32_of_bytes b in sint32_to_sint64 x  in
  let b48:H64.t = let (x:H32.t) = uint32_of_bytes (offset b 4ul) in sint32_to_sint64 x in
  let b812:H64.t = let (x:H32.t) = uint32_of_bytes (offset b 8ul) in sint32_to_sint64 x in
  let b1216:H64.t = let (x:H32.t) = uint32_of_bytes (offset b 12ul) in sint32_to_sint64 x in
  let open Hacl.UInt64 in
  let z0 = a04 +%^ b04 in
  let z1 = a48 +%^ b48 +%^ (z0 >>^ 32ul) in
  let z2 = a812 +%^ b812 +%^ (z1 >>^ 32ul) in
  let z3 = a1216 +%^ b1216 +%^ (z2 >>^ 32ul) in
  let a04   = B.sub a 0ul  4ul in
  let a48   = B.sub a 4ul  4ul in
  let a812  = B.sub a 8ul  4ul in
  let a1216 = B.sub a 12ul 4ul in
  assert(a `includes` a04);  assert(a `includes` a48);
  assert(a `includes` a812); assert(a `includes` a1216);
  bytes_of_uint32 a04   (sint64_to_sint32 z0);
  bytes_of_uint32 a48   (sint64_to_sint32 z1);
  bytes_of_uint32 a812  (sint64_to_sint32 z2);
  bytes_of_uint32 a1216 (sint64_to_sint32 z3)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

(* Finish function, with final accumulator value *)
val poly1305_finish:
  tag:wordB{length tag = 16} ->
  acc:elemB ->
  s:wordB{length s = 16} -> STL unit
  (requires (fun h -> B.live h tag /\ live h acc /\ B.live h s
    /\ disjoint tag acc /\ disjoint tag s /\ disjoint acc s))
  (ensures  (fun h0 _ h1 -> modifies_2 tag acc h0 h1 /\ live h1 acc /\ B.live h1 tag
  ))
let poly1305_finish tag acc s =
  trunc1305 acc tag;
  add_word tag s

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

(**
   Computes the poly1305 mac function on a buffer
   *)
val poly1305_mac: tag:wordB{length tag >= 16} -> msg:bytes{disjoint tag msg} ->
  len:u32{U32.v len <= length msg} -> key:bytes{length key = 32 /\ disjoint msg key /\ disjoint tag key} ->
  STStack unit
    (requires (fun h -> B.live h msg /\ B.live h key /\ B.live h tag))
    (ensures (fun h0 _ h1 -> B.live h1 tag /\ modifies_1 tag h0 h1))
let poly1305_mac tag msg len key =
  push_frame();
  (* Create buffers for the 2 parts of the key and the accumulator *)
  let tmp = create (uint64_to_sint64 0uL) 10ul in
  let acc = sub tmp 0ul 5ul in
  let r   = sub tmp 5ul 5ul in
  (* Initializes the accumulator and the keys values *)
  poly1305_init acc r key;
  (* Compute the number of 'plain' blocks *)
  let ctr = U32.div len 16ul in
  let rest = U32.rem len 16ul in
  (* Run the poly1305_update function ctr times *)
  poly1305_loop msg acc r ctr;
  (* Run the poly1305_update function one more time on the incomplete block *)
  let last_block = sub msg (FStar.UInt32 (ctr *^ 16ul)) rest in
  poly1305_last last_block acc r rest;
  (* Finish *)
  poly1305_finish (sub tag 0ul 16ul) acc (sub key 16ul 16ul);
  pop_frame()
