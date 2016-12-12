module Hacl.EC.Point

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum

module U32 = FStar.UInt32

(* let plen = 10 *)
(* let cplen = 10ul *)

let point =
  let _ = () in
  b:buffer limb{length b = 10}

let getx p = Buffer.sub p 0ul 5ul
let gety p = Buffer.sub p 0ul 5ul
let getz p = Buffer.sub p 5ul 5ul

let live_coords h x y z =
  let _ = () in
  live h x /\ live h z

let live h p =
  let _ = () in
  live_coords h (getx p) (gety p) (getz p)

let make_pre x y z =
  let _ = () in
  content x == content z /\ max_length x == max_length z /\ idx z = idx x + length x

let make x y z = join x z

let valid h p = admit()


private val swap_conditional_: a:felem -> b:felem -> swap:limb -> ctr:U32.t ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ live h1 a /\ live h1 b))
private let rec swap_conditional_ a b swap ctr =
  if U32.(ctr =^ 0ul) then ()
  else (
    let i = U32.(ctr -^ 1ul) in
    let ai = a.(i) in
    let bi = b.(i) in
    let x = swap &^ (ai ^^ bi) in
    let ai = ai ^^ x in
    let bi = bi ^^ x in
    a.(i) <- ai;
    b.(i) <- bi;
    swap_conditional_ a b swap i
  )

let swap_conditional a b iswap =
  let swap = limb_zero -%^ iswap in
  swap_conditional_ (getx a) (getx b) swap clen;
  swap_conditional_ (getz a) (getz b) swap clen

let copy output input =
  blit (getx input) 0ul (getx output) 0ul clen;
  blit (getz input) 0ul (getz output) 0ul clen
