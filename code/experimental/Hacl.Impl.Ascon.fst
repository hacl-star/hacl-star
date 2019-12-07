module Hacl.Impl.Ascon

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.ByteBuffer.Tuples
open Lib.LoopCombinators

module Spec = Spec.Ascon
module ST = FStar.HyperStack.ST


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* Constants *)
inline_for_extraction
let size_state: size_t = size Spec.vsize_state

inline_for_extraction
let size_rc: size_t = size Spec.vsize_rc


(* Define the Ascon state *)
type state_p = lbuffer uint64 size_state


let rcTable : x:ilbuffer (rotval U64) 10ul{witnessed x Spec.rc /\ recallable x} =
  createL_global Spec.rc_list


(* Creation of the Ascon state *)
val create_state: unit ->
  StackInline state_p
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> live h1 r /\ stack_allocated r h0 h1 (Spec.create_state ())))

let create_state () = create #uint64 size_state (u64 0)


(* Definition of the sbox (from Keccak) *)
val sbox: s:state_p -> t:state_p ->
  Stack unit
  (requires (fun h -> live h s /\ live h t /\ disjoint s t))
  (ensures  (fun h0 _ h1 -> modifies2 s t h0 h1))

let sbox s t =
  let t0,t1,t2,t3,t4 = expand t in
  let s0,s1,s2,s3,s4 = expand s in
  let t0 = lognot s0 in
  let t1 = lognot s1 in
  let t2 = lognot s2 in
  let t3 = lognot s3 in
  let t4 = lognot s4 in
  let t0 = t0 &. s1 in
  let t1 = t1 &. s2 in
  let t2 = t2 &. s3 in
  let t3 = t3 &. s4 in
  let t4 = t4 &. s0 in
  let s0 = s0 &. t1 in
  let s1 = s1 &. t2 in
  let s2 = s2 &. t3 in
  let s3 = s3 &. t4 in
  let s4 = s4 &. t0 in
  collapse s (u64 0) (s0,s1,s2,s3,s4);
  admit()


(* Definition of the round function *)
val round: c:uint8 -> s:state_p ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))

let round c s =
  push_frame ();
  let empty:state_p = create_state () in
  let fake:rotval U64 = size 1 in
  (* let rc0,rc1,rc2,rc3,rc4,rc5,rc6,rc7,rc8,rc9 = expand rcTable in *)
  let rc0 = fake in
  let rc1 = fake in
  let rc2 = fake in
  let rc3 = fake in
  let rc4 = fake in
  let rc5 = fake in
  let rc6 = fake in
  let rc7 = fake in
  let rc8 = fake in
  let rc9 = fake in
  let h = ST.get () in
  let s0,s1,s2,s3,s4 = expand s in
  // addition of round constant
  let c64 = to_u64 c in
  let s2 = c64 ^. s2 in
  // substitution layer
  let s0 = s0 ^. s4 in
  let s4 = s4 ^. s3 in
  let s2 = s2 ^. s1 in
  // start of keccak s-box
  sbox s empty;
  // end of keccak s-box
  let s1 = s1 ^. s0 in
  let s0 = s0 ^. s4 in
  let s3 = s3 ^. s2 in
  let s2 = lognot s2 in
  // linear diffusion layer
  let s0 = s0 ^. ((s0 >>>. rc0) ^. (s0 >>>. rc1)) in
  let s1 = s1 ^. ((s1 >>>. rc2) ^. (s1 >>>. rc3)) in
  let s2 = s2 ^. ((s2 >>>. rc4) ^. (s2 >>>. rc5)) in
  let s3 = s3 ^. ((s3 >>>. rc6) ^. (s3 >>>. rc7)) in
  let s4 = s4 ^. ((s4 >>>. rc8) ^. (s4 >>>. rc9)) in
  collapse s (u64 0) (s0,s1,s2,s3,s4);
  pop_frame ();
  admit()


(* Define 12 rounds permutation *)
val p12: s:state_p ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))
let p12 s =
  round (u8 0xf0) s;
  round (u8 0xe1) s;
  round (u8 0xd2) s;
  round (u8 0xc3) s;
  round (u8 0xb4) s;
  round (u8 0xa5) s;
  round (u8 0x96) s;
  round (u8 0x87) s;
  round (u8 0x78) s;
  round (u8 0x69) s;
  round (u8 0x5a) s;
  round (u8 0x4b) s

(* Define 8 rounds permutation *)
val p8: s:state_p ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))
let p8 s =
  round (u8 0xb4) s;
  round (u8 0xa5) s;
  round (u8 0x96) s;
  round (u8 0x87) s;
  round (u8 0x78) s;
  round (u8 0x69) s;
  round (u8 0x5a) s;
  round (u8 0x4b) s

(* Define 6 rounds permutation *)
val p6: s:state_p ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> modifies1 s h0 h1))
let p6 s =
  round (u8 0x96) s;
  round (u8 0x87) s;
  round (u8 0x78) s;
  round (u8 0x69) s;
  round (u8 0x5a) s;
  round (u8 0x4b) s
