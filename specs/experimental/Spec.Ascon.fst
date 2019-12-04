module Spec.Ascon

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence.Tuples


(* Define constants *)
inline_for_extraction
let vsize_state : size_nat = 5

inline_for_extraction
let vsize_rc = 10


(* Define rotation constants *)
inline_for_extraction
let rc_list: l:List.Tot.llist (rotval U64) vsize_rc =
  [@inline_let]
  let l: list (rotval U64) = [ size 19; size 28; size 61; size 39;
            size 1;  size 6;  size 10; size 17;
            size 7;  size 41 ] in
  assert_norm(List.Tot.length l == vsize_rc);
  l

let rc: lseq (rotval U64) vsize_rc  = createL rc_list


(* Define the Ascon state *)
type state_s = lseq uint64 vsize_state

(* Creation of the Ascon state *)
val create_state: unit -> state_s
let create_state () = create vsize_state (u64 0)


(* Definition of the sbox (from Keccak) *)
[@"opaque_to_smt"]
val sbox: state_s -> state_s -> state_s
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
  let s = collapse (u64 0) (s0,s1,s2,s3,s4) in
  s


(* Definition of the round function *)
val round: uint8 -> state_s -> state_s
let round c s =
  let rc0,rc1,rc2,rc3,rc4,rc5,rc6,rc7,rc8,rc9 = expand rc in
  let s0,s1,s2,s3,s4 = expand s in
  // addition of round constant
  let c64 = to_u64 c in
  let s2 = c64 ^. s2 in
  // substitution layer
  let s0 = s0 ^. s4 in
  let s4 = s4 ^. s3 in
  let s2 = s2 ^. s1 in
  // start of keccak s-box
  let s = sbox s (create_state ()) in
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
  collapse (u64 0) (s0,s1,s2,s3,s4)


(* Define 12 rounds permutation *)
val p12: state_s -> state_s
let p12 s =
  let s = round (u8 0xf0) s in
  let s = round (u8 0xe1) s in
  let s = round (u8 0xd2) s in
  let s = round (u8 0xc3) s in
  let s = round (u8 0xb4) s in
  let s = round (u8 0xa5) s in
  let s = round (u8 0x96) s in
  let s = round (u8 0x87) s in
  let s = round (u8 0x78) s in
  let s = round (u8 0x69) s in
  let s = round (u8 0x5a) s in
  let s = round (u8 0x4b) s in
  s

(* Define 8 rounds permutation *)
val p8: state_s -> state_s
let p8 s =
  let s = round (u8 0xb4) s in
  let s = round (u8 0xa5) s in
  let s = round (u8 0x96) s in
  let s = round (u8 0x87) s in
  let s = round (u8 0x78) s in
  let s = round (u8 0x69) s in
  let s = round (u8 0x5a) s in
  let s = round (u8 0x4b) s in
  s

(* Define 6 rounds permutation *)
val p6: state_s -> state_s
let p6 s =
  let s = round (u8 0x96) s in
  let s = round (u8 0x87) s in
  let s = round (u8 0x78) s in
  let s = round (u8 0x69) s in
  let s = round (u8 0x5a) s in
  let s = round (u8 0x4b) s in
  s
