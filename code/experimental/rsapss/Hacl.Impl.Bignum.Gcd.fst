module Hacl.Impl.Bignum.Gcd

open FStar.HyperStack.ST
open FStar.HyperStack
open FStar.Buffer
open FStar.Mul

open LowStar.Buffer

open Lib.Buffer
open Lib.IntTypes
open Lib.Math.Algebra

open Hacl.Impl.Bignum.Addition
open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Division
open Hacl.Impl.Bignum.Misc
open Hacl.Impl.Bignum.Multiplication
open Hacl.Spec.Bignum


val bn_gcd_:
     #aLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> g:lbignum aLen
  -> tmp_q:lbignum aLen
  -> tmp_r:lbignum aLen
  -> Stack unit
    (requires fun h ->
     live h a /\ live h b /\ live h g /\ live h tmp_q /\ live h tmp_r /\
     all_disjoint [loc a; loc b; loc g; loc tmp_q; loc tmp_r] /\
     as_snat h b <> 0)
    (ensures fun h0 _ h1 ->
     modifies (loc a |+| loc b |+| loc g |+| loc tmp_q |+| loc tmp_r) h0 h1 /\
     as_snat h1 g > 0 /\
     as_snat h1 g = gcd_standalone (as_snat h0 a) (as_snat h0 b) /\
     is_gcd (as_snat h0 a) (as_snat h0 b) (as_snat h1 g)
     )
let rec bn_gcd_ #aLen a b g tmp_q tmp_r =
  if bn_is_zero a
  then bn_assign_bn g b
  else begin
    bn_divide b a tmp_q tmp_r;
    bn_assign_bn b tmp_r;
    bn_gcd_ b a g tmp_q tmp_r
  end


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_gcd:
     #aLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> g:lbignum aLen
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h g /\
      all_disjoint [loc a; loc b; loc g] /\
      as_snat h b <> 0)
    (ensures fun h0 _ h1 ->
      modifies1 g h0 h1 /\
      as_snat h1 g > 0 /\
      as_snat h1 g = gcd_standalone (as_snat h0 a) (as_snat h0 b) /\
      is_gcd (as_snat h0 a) (as_snat h0 b) (as_snat h1 g))
let bn_gcd #aLen a b g =
  push_frame ();
  let a' = bn_copy a in
  let b' = bn_copy b in
  let tmp_q = create aLen (u64 0) in
  let tmp_r = create aLen (u64 0) in
  bn_gcd_ a' b' g tmp_q tmp_r;
  pop_frame ()

val bn_lcm:
     #nLen:bn_len{v nLen * 2 < max_size_t}
  -> a:lbignum nLen
  -> b:lbignum nLen
  -> l:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h a /\ live h b /\ live h l /\
      all_disjoint [loc a; loc b; loc l] /\
      as_snat h a > 0 /\
      as_snat h b > 0 /\
      issnat (as_snat h a * as_snat h b) /\
      v (nat_bytes_num (as_snat h a * as_snat h b)) <= v nLen
      )
    (ensures fun h0 _ h1 ->
      modifies1 l h0 h1 /\
      as_snat h1 l > 0 /\
      as_snat h1 l = lcm (as_snat h0 a) (as_snat h0 b))
let bn_lcm #nLen a b l =
  push_frame ();
  let g = create nLen (u64 0) in
  bn_gcd a b g;
  let tmp = create nLen (u64 0) in
  let tmp_unused = create nLen (u64 0) in
  bn_divide a g tmp tmp_unused;

  let h = FStar.HyperStack.ST.get () in
  division_post_size (as_snat h a) (as_snat h g);
  snat_order (as_snat h tmp * as_snat h b) (as_snat h a * as_snat h b);
  nat_bytes_num_fit (as_snat h tmp * as_snat h b) (as_snat h a * as_snat h b);

  bn_mul_fitting tmp b l;

  pop_frame ()
