module Hacl.Impl.Ed25519.SwapConditional

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open Hacl.UInt64
open Hacl.Bignum25519
open Hacl.Impl.Ed25519.ExtPoint


module U32 = FStar.UInt32


#reset-options "--max_fuel 0 --z3rlimit 10"

let felem = b:buffer Hacl.UInt64.t{length b = 5}


#reset-options "--max_fuel 0 --z3rlimit 10"

private
val lemma_xor: #n:pos -> a:UInt.uint_t n -> b:UInt.uint_t n -> Lemma
  (UInt.logxor a (UInt.logxor a b) = b /\ UInt.logxor a (UInt.logxor b a) = b
    /\ UInt.logxor a (UInt.zero n) = a)
let lemma_xor #n a b =
  UInt.logxor_associative a a b;
  UInt.logxor_commutative a b;
  UInt.logxor_commutative (UInt.zero n) b;
  UInt.logxor_self a;
  UInt.logxor_lemma_1 a;
  UInt.logxor_lemma_1 b

private
val lemma_and: #n:pos -> a:UInt.uint_t n -> Lemma (UInt.logand (UInt.ones n) a = a /\ UInt.logand (UInt.zero n) a = UInt.zero n)
let lemma_and #n a =
  UInt.logand_lemma_1 #n a;
  UInt.logand_lemma_2 #n a;
  UInt.logand_commutative #n a (UInt.zero n); 
  UInt.logand_commutative #n a (UInt.ones n)


private 
val swap_conditional_step:
  out_a:felem -> out_b:felem{disjoint out_a out_b} ->
  a:felem -> b:felem{disjoint a b} ->
  swap:limb{v swap = pow2 64 - 1 \/ v swap = 0} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h out_a /\ live h out_b))
    (ensures (fun h0 _ h1 -> modifies_2 out_a out_b h0 h1 /\ live h1 out_a /\ live h1 out_b /\
      live h0 a /\ live h0 b
      /\ (if v swap = pow2 64 - 1 then (as_seq h1 out_a == as_seq h0 b /\ as_seq h1 out_b == as_seq h0 a)
         else (as_seq h1 out_a == as_seq h0 a /\ as_seq h1 out_b == as_seq h0 b)) ))
#reset-options "--max_fuel 0 --z3rlimit 200"
let swap_conditional_step a' b' a b swap =
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
  let x0 = swap &^ (a0 ^^ b0) in
  let x1 = swap &^ (a1 ^^ b1) in
  let x2 = swap &^ (a2 ^^ b2) in
  let x3 = swap &^ (a3 ^^ b3) in
  let x4 = swap &^ (a4 ^^ b4) in
  lemma_and (v (a0 ^^ b0));
  lemma_and (v (a1 ^^ b1));
  lemma_and (v (a2 ^^ b2));
  lemma_and (v (a3 ^^ b3));
  lemma_and (v (a4 ^^ b4));
  assert (v x0 = v (a0 ^^ b0) \/ v x0 = 0);
  assert (v x1 = v (a1 ^^ b1) \/ v x1 = 0);
  assert (v x2 = v (a2 ^^ b2) \/ v x2 = 0);
  assert (v x3 = v (a3 ^^ b3) \/ v x3 = 0);
  assert (v x4 = v (a4 ^^ b4) \/ v x4 = 0);
  lemma_xor (v a0) (v b0);
  lemma_xor (v b0) (v a0);
  lemma_xor (v a1) (v b1);
  lemma_xor (v b1) (v a1);
  lemma_xor (v a2) (v b2);
  lemma_xor (v b2) (v a2);
  lemma_xor (v a3) (v b3);
  lemma_xor (v b3) (v a3);
  lemma_xor (v a4) (v b4);
  lemma_xor (v b4) (v a4);
  let a0' = a0 ^^ x0 in
  let b0' = b0 ^^ x0 in
  let a1' = a1 ^^ x1 in
  let b1' = b1 ^^ x1 in
  let a2' = a2 ^^ x2 in
  let b2' = b2 ^^ x2 in
  let a3' = a3 ^^ x3 in
  let b3' = b3 ^^ x3 in
  let a4' = a4 ^^ x4 in
  let b4' = b4 ^^ x4 in
  let h0 = ST.get() in
  Hacl.Lib.Create64.make_h64_5 a' a0' a1' a2' a3' a4';
  let h1 = ST.get() in
  Hacl.Lib.Create64.make_h64_5 b' b0' b1' b2' b3' b4';
  let h2 = ST.get() in
  no_upd_lemma_1 h1 h2 b' a';
  Seq.lemma_eq_intro (as_seq h2 a') (if v swap = pow2 64 - 1 then as_seq h0 b else as_seq h0 a);
  Seq.lemma_eq_intro (as_seq h2 b') (if v swap = pow2 64 - 1 then as_seq h0 a else as_seq h0 b)


#reset-options "--max_fuel 0 --z3rlimit 10"

private
inline_for_extraction let mk_mask (iswap:Hacl.UInt64.t{v iswap = 0 \/ v iswap = 1}) :
  Tot (z:Hacl.UInt64.t{if v iswap = 1 then v z = pow2 64 - 1 else v z = 0})
  = let swap = Hacl.Cast.uint64_to_sint64 0uL -%^ iswap in
    assert_norm((0 - 1) % pow2 64 = pow2 64 - 1);
    assert_norm((0 - 0) % pow2 64 = 0);
    swap


#reset-options "--max_fuel 0 --z3rlimit 10"

private
val lemma_point_from_coord: h:mem -> p:point{live h p} ->
  Lemma (let x = as_seq h (getx p) in let y = as_seq h (gety p) in
         let z = as_seq h (getz p) in let t = as_seq h (gett p) in
         as_seq h p == FStar.Seq.(x @| y @| z @| t))
#reset-options "--max_fuel 0 --z3rlimit 100"
let lemma_point_from_coord h p =
  let x = as_seq h (getx p) in let y = as_seq h (gety p) in
  let z = as_seq h (getz p) in let t = as_seq h (gett p) in
  Seq.lemma_eq_intro (as_seq h p) FStar.Seq.(x @| y @| z @| t)


#reset-options "--max_fuel 0 --z3rlimit 100"

private
val lemma_point_eq:
  h:mem -> h':mem -> p:point{live h p} -> p':point{live h' p'} ->
  Lemma (requires (
    let x = as_seq h (getx p) in let y = as_seq h (gety p) in
    let z = as_seq h (getz p) in let t = as_seq h (gett p) in
    let x' = as_seq h' (getx p') in let y' = as_seq h' (gety p') in
    let z' = as_seq h' (getz p') in let t' = as_seq h' (gett p') in
    x == x' /\ y == y' /\ z == z' /\ t == t'))
        (ensures (as_seq h p == as_seq h' p'))
let lemma_point_eq h h' p p' =
  lemma_point_from_coord h p;
  lemma_point_from_coord h' p';
  Seq.lemma_eq_intro (as_seq h p) (as_seq h' p')


val swap_conditional:
  out_a:point -> out_b:point{disjoint out_a out_b} ->
  a:point{disjoint a out_a /\ disjoint a out_b} ->
  b:point{disjoint b out_b /\ disjoint b out_a /\ disjoint a b} ->
  i:limb{v i = 0 \/ v i = 1} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h out_a /\ live h out_b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 out_a /\ live h1 out_b /\
      modifies_2 out_a out_b h0 h1 /\
      (if v i = 1 then (as_seq h1 out_a == as_seq h0 b /\ as_seq h1 out_b == as_seq h0 a)
         else (as_seq h1 out_a == as_seq h0 a /\ as_seq h1 out_b == as_seq h0 b))
    ))

#reset-options "--max_fuel 0 --z3rlimit 500"

let swap_conditional a' b' a b iswap =
  let swap = mk_mask iswap in
  assert(disjoint (getx a) (getx b));
  assert(disjoint (gety a) (gety b));
  assert(disjoint (getz a) (getz b));
  assert(disjoint (gett a) (gett b));
  assert(disjoint (getx a') (getx b'));
  assert(disjoint (gety a') (gety b'));
  assert(disjoint (getz a') (getz b'));
  assert(disjoint (gett a') (gett b'));
  let h0 = ST.get() in
  swap_conditional_step (getx a') (getx b') (getx a) (getx b) swap;
  let h1 = ST.get() in
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (getx a);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (gety a);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (getz a);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (gett a);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (getx b);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (gety b);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (getz b);
  no_upd_lemma_2 h0 h1 (getx a') (getx b') (gett b);
  swap_conditional_step (gety a') (gety b') (gety a) (gety b) swap;
  let h2 = ST.get() in
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (getx a');
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (getx b');
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (getx a);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (gety a);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (getz a);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (gett a);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (getx b);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (gety b);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (getz b);
  no_upd_lemma_2 h1 h2 (gety a') (gety b') (gett b);
  swap_conditional_step (getz a') (getz b') (getz a) (getz b) swap;
  let h3 = ST.get() in
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (getx a');
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (getx b');
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (gety a');
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (gety b');
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (getx a);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (gety a);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (getz a);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (gett a);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (getx b);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (gety b);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (getz b);
  no_upd_lemma_2 h2 h3 (getz a') (getz b') (gett b);
  swap_conditional_step (gett a') (gett b') (gett a) (gett b) swap;
  let h4 = ST.get() in
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getx a');
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getx b');
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (gety a');
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (gety b');
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getz a');
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getz b');
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getx a);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (gety a);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getz a);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (gett a);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getx b);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (gety b);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (getz b);
  no_upd_lemma_2 h3 h4 (gett a') (gett b') (gett b);
  lemma_point_eq h4 h0 a' (if v iswap = 1 then b else a);
  lemma_point_eq h4 h0 b' (if v iswap = 1 then a else b);
  Seq.lemma_eq_intro (as_seq h4 a') (if v iswap = 1 then as_seq h0 b else as_seq h0 a);
  Seq.lemma_eq_intro (as_seq h4 b') (if v iswap = 1 then as_seq h0 a else as_seq h0 b)


#reset-options "--max_fuel 0 --z3rlimit 100"

val swap_conditional_inplace:
  a:point -> b:point{disjoint a b} ->
  i:limb{v i = 0 \/ v i = 1} ->
  Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a /\ live h1 b /\
      modifies_2 a b h0 h1 /\
      (if v i = 1 then (as_seq h1 a == as_seq h0 b /\ as_seq h1 b == as_seq h0 a)
         else (as_seq h1 a == as_seq h0 a /\ as_seq h1 b == as_seq h0 b))
    ))

#reset-options "--max_fuel 0 --z3rlimit 500"

let swap_conditional_inplace a b iswap =
  let swap = mk_mask iswap in
  assert(disjoint (getx a) (getx b));
  assert(disjoint (gety a) (gety b));
  assert(disjoint (getz a) (getz b));
  assert(disjoint (gett a) (gett b));
  let h0 = ST.get() in
  swap_conditional_step (getx a) (getx b) (getx a) (getx b) swap;
  let h1 = ST.get() in
  no_upd_lemma_2 h0 h1 (getx a) (getx b) (gety a);
  no_upd_lemma_2 h0 h1 (getx a) (getx b) (getz a);
  no_upd_lemma_2 h0 h1 (getx a) (getx b) (gett a);
  no_upd_lemma_2 h0 h1 (getx a) (getx b) (gety b);
  no_upd_lemma_2 h0 h1 (getx a) (getx b) (getz b);
  no_upd_lemma_2 h0 h1 (getx a) (getx b) (gett b);
  swap_conditional_step (gety a) (gety b) (gety a) (gety b) swap;
  let h2 = ST.get() in
  no_upd_lemma_2 h1 h2 (gety a) (gety b) (getx a);
  no_upd_lemma_2 h1 h2 (gety a) (gety b) (getx b);
  no_upd_lemma_2 h1 h2 (gety a) (gety b) (getz a);
  no_upd_lemma_2 h1 h2 (gety a) (gety b) (gett a);
  no_upd_lemma_2 h1 h2 (gety a) (gety b) (getz b);
  no_upd_lemma_2 h1 h2 (gety a) (gety b) (gett b);
  swap_conditional_step (getz a) (getz b) (getz a) (getz b) swap;
  let h3 = ST.get() in
  no_upd_lemma_2 h2 h3 (getz a) (getz b) (getx a);
  no_upd_lemma_2 h2 h3 (getz a) (getz b) (getx b);
  no_upd_lemma_2 h2 h3 (getz a) (getz b) (gety a);
  no_upd_lemma_2 h2 h3 (getz a) (getz b) (gety b);
  no_upd_lemma_2 h2 h3 (getz a) (getz b) (gett a);
  no_upd_lemma_2 h2 h3 (getz a) (getz b) (gett b);
  swap_conditional_step (gett a) (gett b) (gett a) (gett b) swap;
  let h4 = ST.get() in
  no_upd_lemma_2 h3 h4 (gett a) (gett b) (getx a);
  no_upd_lemma_2 h3 h4 (gett a) (gett b) (getx b);
  no_upd_lemma_2 h3 h4 (gett a) (gett b) (gety a);
  no_upd_lemma_2 h3 h4 (gett a) (gett b) (gety b);
  no_upd_lemma_2 h3 h4 (gett a) (gett b) (getz a);
  no_upd_lemma_2 h3 h4 (gett a) (gett b) (getz b);
  lemma_point_eq h4 h0 a (if v iswap = 1 then b else a);
  lemma_point_eq h4 h0 b (if v iswap = 1 then a else b);
  Seq.lemma_eq_intro (as_seq h4 a) (if v iswap = 1 then as_seq h0 b else as_seq h0 a);
  Seq.lemma_eq_intro (as_seq h4 b) (if v iswap = 1 then as_seq h0 a else as_seq h0 b)


#reset-options "--max_fuel 0 --z3rlimit 30"

val copy:
  output:point ->
  input:point{disjoint input output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h0 input /\ live h1 output /\ live h1 input
      /\ modifies_1 output h0 h1 /\ as_seq h1 output == as_seq h0 input))
let copy output input =
  let h  = ST.get() in
  blit input 0ul output 0ul 20ul;
  let h' = ST.get() in
  Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 20);
  Seq.lemma_eq_intro (as_seq h' output) (Seq.slice (as_seq h' output) 0 20)
