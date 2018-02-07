module Hacl.EC.Point

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Bignum.Limb
open Hacl.Bignum
open Hacl.Spec.EC.Point


module U32 = FStar.UInt32


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val point : Type0
let point =
  let _ = () in
  b:buffer limb{length b = 10}


(** Coordinate getters *)
unfold inline_for_extraction val getx: point -> Tot felem
unfold inline_for_extraction val gety: point -> Tot felem
unfold inline_for_extraction val getz: point -> Tot felem
unfold inline_for_extraction let getx p = Buffer.sub p 0ul 5ul
unfold inline_for_extraction let gety p = Buffer.sub p 0ul 5ul
unfold inline_for_extraction let getz p = Buffer.sub p 5ul 5ul

unfold val live_coords: mem -> felem -> felem -> felem -> GTot Type0
let live_coords h x y z =
  let _ = () in
  live h x /\ live h z

unfold val live: mem -> point -> GTot Type0
let live h p =
  let _ = () in
  live_coords h (getx p) (gety p) (getz p)

val make_pre: x:felem -> y:felem -> z:felem -> GTot Type0
let make_pre x y z =
  let _ = () in
  max_length x == max_length z /\ content x == content z /\ idx z = idx x + length x

unfold inline_for_extraction val make: x:felem -> y:felem -> z:felem{make_pre x y z} -> Tot (p:point)
unfold inline_for_extraction let make x y z = join x z

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val swap_conditional_step: a:felem -> b:felem -> swap:limb{v swap = pow2 64 - 1 \/ v swap = 0} -> ctr:U32.t{U32.v ctr <= len /\ U32.v ctr > 0} ->
  Stack unit
    (requires (fun h -> disjoint a b /\ Buffer.live h a /\ Buffer.live h b
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h a)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h b)
    ))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ Buffer.live h1 a /\ Buffer.live h1 b
      /\ Buffer.live h0 a /\ Buffer.live h0 b
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 a)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 b)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 a)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 b)
      /\ (as_seq h1 a, as_seq h1 b) == swap_conditional_step_spec (as_seq h0 a) (as_seq h0 b) swap ctr
    ))
private let swap_conditional_step a b swap ctr =
  let i = U32.(ctr -^ 1ul) in
  let ai = a.(i) in
  let bi = b.(i) in
  let x = swap &^ (ai ^^ bi) in
  lemma_and (v (ai ^^ bi));
  cut (v x = v (ai ^^ bi) \/ v x = 0);
  lemma_xor (v ai) (v bi);
  lemma_xor (v bi) (v ai);  
  let ai = ai ^^ x in
  let bi = bi ^^ x in
  a.(i) <- ai;
  b.(i) <- bi


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 5"

private val swap_conditional_: a:felem -> b:felem -> swap:limb{v swap = pow2 64 - 1 \/ v swap = 0} -> ctr:U32.t{U32.v ctr <= len} ->
  Stack unit
    (requires (fun h -> disjoint a b /\ Buffer.live h a /\ Buffer.live h b
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h a)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h b)
    ))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1 /\ Buffer.live h1 a /\ Buffer.live h1 b
      /\ Buffer.live h0 a /\ Buffer.live h0 b
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 a)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 b)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 a)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 b)
     /\ (as_seq h1 a, as_seq h1 b) == swap_conditional_spec_ (as_seq h0 a) (as_seq h0 b) swap ctr
    ))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 50"
private let rec swap_conditional_ a b swap ctr =
  if not U32.(ctr =^ 0ul) then 
  (
    cut (U32.v ctr > 0);
    swap_conditional_step a b swap ctr;
    let i = U32.(ctr -^ 1ul) in
    swap_conditional_ a b swap i
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val swap_conditional:
  a:point ->
  b:point ->
  i:limb{v i = 0 \/ v i = 1} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b
      /\ disjoint (getx a) (getx b) /\ disjoint (getx a) (getz b) /\ disjoint (getx a) (getz a)
      /\ disjoint (getz a) (getx b) /\ disjoint (getz a) (getz b) /\ disjoint (getx b) (getz b)
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getx a))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getx b))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getz a))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h (getz b))
    ))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ modifies_2 a b h0 h1
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getx a))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getx b))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getz a))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h0 (getz b))
      /\ live h1 a /\ live h1 b
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getx a))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getx b))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getz a))
      /\ Hacl.Spec.EC.AddAndDouble.red_513 (as_seq h1 (getz b))
      /\ (let spointa1 : spoint_513 = (as_seq h1 (getx a), (as_seq h1 (getz a))) in
         let spointb1 : spoint_513 = (as_seq h1 (getx b), (as_seq h1 (getz b))) in
         (spointa1, spointb1) == 
          swap_conditional_spec (as_seq h0 (getx a), as_seq h0 (getz a)) (as_seq h0 (getx b), as_seq h0 (getz b)) i)
      ))
let swap_conditional a b iswap =
  let swap = limb_zero -%^ iswap in
  assert_norm((0 - 1) % pow2 64 = pow2 64 - 1);
  assert_norm((0 - 0) % pow2 64 = 0);
  swap_conditional_ (getx a) (getx b) swap clen;
  swap_conditional_ (getz a) (getz b) swap clen


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 30"

val copy:
  output:point ->
  input:point ->
  Stack unit
    (requires (fun h -> live h output /\ live h input
      /\ disjoint (getx output) (getx input) /\ disjoint (getx output) (getz input)
      /\ disjoint (getz output) (getx input) /\ disjoint (getz output) (getz input)
      /\ disjoint (getx output) (getz output)
    ))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input
      /\ live h1 output /\ live h1 input
      /\ modifies_1 output h0 h1
      /\ disjoint (getx output) (getx input) /\ disjoint (getx output) (getz input)
      /\ disjoint (getz output) (getx input) /\ disjoint (getz output) (getz input)
      /\ as_seq h1 (getx output) == as_seq h0 (getx input)
      /\ as_seq h1 (getz output) == as_seq h0 (getz input)
    ))
let copy output input =
  let h = ST.get() in
  blit (getx input) 0ul (getx output) 0ul clen;
  blit (getz input) 0ul (getz output) 0ul clen;
  let h' = ST.get() in
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h' (getx output));
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h' (getz output));
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h (getx input));
  Hacl.Spec.Bignum.Fmul.lemma_whole_slice (as_seq h (getz input))
