module Hacl.Bignum.Fdifference

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum.Fdifference.Spec

module U32 = FStar.UInt32

#set-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 20"

let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  i:ctr{U32.v i <= len} ->
  Stack unit
    (requires (fun h -> gte_limbs_c h a h b (U32.v i)))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b (U32.v i) /\ live h1 a
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b) (U32.v i)))
let rec fdifference_ a b i =
  if U32.(i =^ 0ul) then ()
  else (
    let i = U32.(i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    a.(i) <- bi -^ ai;
    fdifference_ a b i
  )
