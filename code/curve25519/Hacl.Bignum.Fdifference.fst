module Hacl.Bignum.Fdifference

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fdifference

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


[@"substitute"]
inline_for_extraction val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> len = 5 /\ gte_limbs_c h a h b (U32.v i)))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b (U32.v i) /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
[@"substitute"]
inline_for_extraction let rec fdifference_ a b i =
    let a0 = a.(0ul) in 
    let b0 = b.(0ul) in
    let a1 = a.(1ul) in 
    let b1 = b.(1ul) in
    let a2 = a.(2ul) in 
    let b2 = b.(2ul) in
    let a3 = a.(3ul) in 
    let b3 = b.(3ul) in
    let a4 = a.(4ul) in 
    let b4 = b.(4ul) in

    a.(0ul) <- b0 -^ a0;
    a.(1ul) <- b1 -^ a1;
    a.(2ul) <- b2 -^ a2;
    a.(3ul) <- b3 -^ a3;
    a.(4ul) <- b4 -^ a4

