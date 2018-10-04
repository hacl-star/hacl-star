module Hacl.Bignum.Fdifference

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Spec.Bignum.Fdifference

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let gte_limbs_c h (a:felem) h' (b:felem) (l:nat{l <= len}) : GTot Type0 =
  live h a /\ live h' b /\ gte_limbs (as_seq h a) (as_seq h' b) l


[@"substitute"]
val fdifference_:
  a:felem ->
  b:felem{disjoint a b} ->
  Stack unit
    (requires (fun h -> gte_limbs_c h a h b len))
    (ensures (fun h0 _ h1 -> gte_limbs_c h0 a h0 b len /\ live h1 a /\ modifies_1 a h0 h1
      /\ as_seq h1 a == fdifference_spec (as_seq h0 a) (as_seq h0 b)))
[@"substitute"]
let fdifference_ a b =
  C.Compat.Loops.in_place_map2 a b clen (fun x y -> y -%^ x)
