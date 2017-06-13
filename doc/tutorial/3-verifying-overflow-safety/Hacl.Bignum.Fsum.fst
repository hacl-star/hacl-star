module Hacl.Bignum.Fsum

open Hacl.Bignum

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.UInt64     // F* 64-bit unsigned machine integers
open FStar.HyperStack // F* memory model
open FStar.Buffer     // F* pointer arithmetic model


#set-options "--initial_fuel 0 --max_fuel 0" // Tuning verification parameters

type u64 = FStar.UInt64.t                // Type alias for uint64
type felem = b:buffer u64{length b = 5}  // X25519-donna bignum array


module U32 = FStar.UInt32

#set-options "--initial_fuel 0 --max_fuel 0"

let fsum_pre h (a:felem) (b:felem) : GTot Type0 =
  live h a /\ live h b /\
  (let s = as_seq h a in let s' = as_seq h b in
  v (Seq.index s 0) + v (Seq.index s' 0) < pow2 64
  /\ v (Seq.index s 1) + v (Seq.index s' 1) < pow2 64
  /\ v (Seq.index s 2) + v (Seq.index s' 2) < pow2 64
  /\ v (Seq.index s 3) + v (Seq.index s' 3) < pow2 64
  /\ v (Seq.index s 4) + v (Seq.index s' 4) < pow2 64)


val fsum:
  a:felem -> b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> fsum_pre h a b))
    (ensures (fun h0 _ h1 -> fsum_pre h0 a b
      /\ live h1 a /\ live h1 b /\ modifies_1 a h0 h1
      /\ as_seq h1 b == as_seq h0 b))
let fsum a b =
  let a0 = a.(0ul) in
  let a1 = a.(1ul) in
  let a2 = a.(2ul) in
  let a3 = a.(3ul) in
  let a4 = a.(4ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  a.(0ul) <- a0 +^ b0;
  a.(1ul) <- a1 +^ b1;
  a.(2ul) <- a2 +^ b2;
  a.(3ul) <- a3 +^ b3;
  a.(4ul) <- a4 +^ b4
