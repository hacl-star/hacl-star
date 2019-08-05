module Hacl.Impl.Ed25519.SwapConditional

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum25519

module F51 = Hacl.Impl.Ed25519.Field51
module F56 = Hacl.Impl.Ed25519.Field56

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

val swap_conditional_step:
    out_a:felem
  -> out_b:felem
  -> a:felem
  -> b:felem
  -> swap:uint64{v swap = pow2 64 - 1 \/ v swap = 0} ->
  Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h out_a /\ live h out_b /\
      disjoint out_a out_b /\ disjoint a b)
    (ensures fun h0 _ h1 -> modifies (loc out_a |+| loc out_b) h0 h1 /\
      (if v swap = pow2 64 - 1 then (as_seq h1 out_a == as_seq h0 b /\ as_seq h1 out_b == as_seq h0 a)
      else (as_seq h1 out_a == as_seq h0 a /\ as_seq h1 out_b == as_seq h0 b)))

let swap_conditional_step a' b' a b swap =
  let h0 = get() in
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
  let x0 = (a0 ^. b0) &. swap in
  let x1 = (a1 ^. b1) &. swap in
  let x2 = (a2 ^. b2) &. swap in
  let x3 = (a3 ^. b3) &. swap in
  let x4 = (a4 ^. b4) &. swap in
  logxor_lemma a0 b0;
  logxor_lemma b0 a0;
  logxor_lemma a1 b1;
  logxor_lemma b1 a1;
  logxor_lemma a2 b2;
  logxor_lemma b2 a2;
  logxor_lemma a3 b3;
  logxor_lemma b3 a3;
  logxor_lemma a4 b4;
  logxor_lemma b4 a4;
  a'.(0ul) <- a0 ^. x0;
  b'.(0ul) <- b0 ^. x0;
  a'.(1ul) <- a1 ^. x1;
  b'.(1ul) <- b1 ^. x1;
  a'.(2ul) <- a2 ^. x2;
  b'.(2ul) <- b2 ^. x2;
  a'.(3ul) <- a3 ^. x3;
  b'.(3ul) <- b3 ^. x3;
  a'.(4ul) <- a4 ^. x4;
  b'.(4ul) <- b4 ^. x4;
  let h1 = get() in
  let lemma_ones () : Lemma
    (requires v swap == pow2 64 - 1)
    (ensures as_seq h1 a' == as_seq h0 b /\ as_seq h1 b' == as_seq h0 a)
  = Lib.IntTypes.Compatibility.uintv_extensionality swap (ones U64 SEC);
    logand_ones (a0 ^. b0);
    logand_ones (a1 ^. b1);
    logand_ones (a2 ^. b2);
    logand_ones (a3 ^. b3);
    logand_ones (a4 ^. b4);
    assert (Seq.equal (as_seq h1 a') (as_seq h0 b));
    assert (Seq.equal (as_seq h0 a) (as_seq h1 b'))
  in
  let lemma_zero () : Lemma
    (requires v swap == 0)
    (ensures as_seq h1 a' == as_seq h0 a /\ as_seq h1 b' == as_seq h0 b)
  = logand_zeros (a0 ^. b0);
    logand_zeros (a1 ^. b1);
    logand_zeros (a2 ^. b2);
    logand_zeros (a3 ^. b3);
    logand_zeros (a4 ^. b4);
    assert (Seq.equal (as_seq h1 a') (as_seq h0 a));
    assert (Seq.equal (as_seq h0 b) (as_seq h1 b'))
  in
  Classical.move_requires lemma_zero ();
  Classical.move_requires lemma_ones ()

val swap_conditional:
    out_a:point
  -> out_b:point
  -> a:point
  -> b:point
  -> i:uint64{v i = 0 \/ v i = 1} ->
  Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h out_a /\ live h out_b /\
      disjoint out_a out_b /\ disjoint a out_a /\disjoint a out_b /\
      disjoint b out_b /\ disjoint b out_a /\ disjoint a b /\
      F51.point_inv_t h a /\ F51.point_inv_t h b
    )
    (ensures  fun h0 _ h1 -> modifies (loc out_a |+| loc out_b) h0 h1 /\
      F51.point_inv_t h1 out_a /\ F51.point_inv_t h1 out_b /\
      (F51.point_eval h1 out_a, F51.point_eval h1 out_b) ==
      Spec.Ed25519.cswap2 (to_u8 i) (F51.point_eval h0 a) (F51.point_eval h0 b)
    )

#set-options "--z3rlimit 50"

let swap_conditional a' b' a b iswap =
  let swap = u64 0 -. iswap in
  Math.Lemmas.small_mod (v iswap) (pow2 8);
  swap_conditional_step (getx a') (getx b') (getx a) (getx b) swap;
  swap_conditional_step (gety a') (gety b') (gety a) (gety b) swap;
  swap_conditional_step (getz a') (getz b') (getz a) (getz b) swap;
  swap_conditional_step (gett a') (gett b') (gett a) (gett b) swap

val swap_conditional_inplace:
    a:point
  -> b:point
  -> i:uint64{v i = 0 \/ v i = 1} ->
  Stack unit
    (requires fun h -> live h a /\ live h b /\ disjoint a b /\
      F51.point_inv_t h a /\ F51.point_inv_t h b
    )
    (ensures  fun h0 _ h1 -> modifies (loc a |+| loc b) h0 h1 /\
      F51.point_inv_t h1 a /\ F51.point_inv_t h1 b /\
      (F51.point_eval h1 a, F51.point_eval h1 b) ==
      Spec.Ed25519.cswap2 (to_u8 i) (F51.point_eval h0 a) (F51.point_eval h0 b)
    )
let swap_conditional_inplace a b iswap =
  let swap = u64 0 -. iswap in
  Math.Lemmas.small_mod (v iswap) (pow2 8);
  swap_conditional_step (getx a) (getx b) (getx a) (getx b) swap;
  swap_conditional_step (gety a) (gety b) (gety a) (gety b) swap;
  swap_conditional_step (getz a) (getz b) (getz a) (getz b) swap;
  swap_conditional_step (gett a) (gett b) (gett a) (gett b) swap
