module Hacl.Impl.HE.GM

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.PrintBuffer
open Lib.Math.Algebra

open Hacl.Impl.Bignum

module S = Hacl.Spec.HE.GM

// max 2^14 bits
type bn_len_s = s:bn_len{v s <= 256}

val to_fe:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h res /\
       disjoint n res /\ disjoint a res /\
       as_snat h n > 1)
    (ensures fun h0 _ h1 ->
       modifies1 res h0 h1 /\
       as_snat h1 res = to_fe #(as_snat h0 n) (as_snat h0 a))
let to_fe #nLen n a res = bn_remainder a n res

val leg_symbol:
     #nLen:bn_len_s
  -> a:lbignum nLen
  -> p:lbignum nLen
  -> p_min_one:lbignum nLen
  -> p_min_one_half:lbignum nLen
  -> Stack Int32.t
    (requires fun h ->
       live h a /\ live h p /\ live h p_min_one /\ live h p_min_one_half /\
       disjoint a p /\
       as_snat h p > 1 /\
       as_snat h p_min_one = as_snat h p - 1 /\
       as_snat h p_min_one_half = as_snat h p_min_one / 2)
    (ensures  fun h0 _ h1 ->
       live h1 a /\ live h1 p /\ modifies0 h0 h1)
let leg_symbol #nLen a p p_min_one p_min_one_half =
  push_frame ();
  let tmp = create nLen (uint 0) in
  bn_modular_exp p a p_min_one_half tmp;
  let res = if bn_is_equal p_min_one tmp then (-1l)
            else (if eq_u64 (tmp.(0ul) &. uint 1) (uint 1) then 1l else 0l) in
  pop_frame ();
  res


val encrypt:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> y:lbignum nLen
  -> m:bool
  -> r:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
       live h n /\ live h y /\ live h r /\ live h res /\
       disjoint n res /\ disjoint y res /\ disjoint r res /\
       as_snat h n > 1)
    (ensures fun h0 _ h1 ->
       live h1 n /\ live h1 y /\ live h1 r /\ live h1 res /\
       modifies1 res h0 h1)
let encrypt #nLen n y m r res =
  if m then bn_modular_mul n r r res else begin
    push_frame ();
    let r' = create nLen (uint 0) in
    bn_modular_mul n r r res;
    bn_modular_mul n r' y res;
    pop_frame ()
  end
