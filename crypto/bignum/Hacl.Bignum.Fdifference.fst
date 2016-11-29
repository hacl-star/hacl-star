module Hacl.Bignum.Fdifference

open FStar.HyperStack
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb


module U32 = FStar.UInt32

let gte_felem h (b:felem) h' (b':felem) (l:nat{l <= len}) : GTot Type0 =
  live h b /\ live h' b'
  /\ (forall (i:nat). {:pattern (get h b i) \/ (get h' b' i)} i < l ==> v (get h b i) >= v (get h' b' i))


let is_subtraction h (b:felem) h' (b':felem) (l:nat{l <= len}) : GTot Type0 =
  live h b /\ live h' b /\ live h' b'
  /\ (forall (i:nat). {:pattern (get h b i)} (i >= l /\ i < len) ==> v (get h b i) = v (get h' b' i) - v (get h' b i))


val fdifference_:
  a:felem ->
  b:felem ->
  i:ctr ->
  Stack unit
    (requires (fun h -> true))
    (ensures (fun _ _ _ -> true))
let rec fdifference_ a b i =
  if U32 (i =^ 0ul) then ()
  else (
    let i = U32 (i -^ 1ul) in
    let ai = a.(i) in let bi = b.(i) in
    a.(i) <- bi -^ ai;
    fdifference_ a b i
  )


val fdifference:
  a:felem ->
  b:felem ->
  Stack unit
    (requires (fun h -> gte_felem h b h a len))
    (ensures  (fun h0 _ h1 -> is_subtraction h1 a h0 b 0))
let fdifference a b =
  fdifference_ a b clen
