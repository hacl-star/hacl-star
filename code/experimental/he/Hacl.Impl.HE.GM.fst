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
module M = Lib.Math.Algebra

// max 2^14 bits
type bn_len_s = s:bn_len{v s <= 256}


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val to_fe_:
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
let to_fe_ #nLen n a res = bn_remainder a n res


inline_for_extraction
val conv_one_zero_to_int:
     #nLen:bn_len_s
  -> x:lbignum nLen
  -> Stack Int32.t
    (requires fun h -> live h x /\ (as_snat h x = 1 \/ as_snat h x = 0))
    (ensures fun h0 b h1 -> h0 == h1 /\ Int32.v b = as_snat h1 x)
let conv_one_zero_to_int #nLen x =
  let h = FStar.HyperStack.ST.get () in
  bignum_of_uL x h (uint 1);
  bignum_of_uL x h (uint 0);
  if eq_u64 (x.(0ul)) (uint 0) then 0l else 1l

val leg_symbol:
     #nLen:bn_len_s
  -> p:lbignum nLen
  -> p_min_one:lbignum nLen
  -> p_min_one_half:lbignum nLen
  -> a:lbignum nLen
  -> Stack Int32.t
    (requires fun h ->
       live h a /\ live h p /\ live h p_min_one /\ live h p_min_one_half /\
       disjoint a p /\
       as_snat h p > 1 /\
       isprm (as_snat h p) /\
       as_snat h p_min_one = as_snat h p - 1 /\
       as_snat h p_min_one_half = as_snat h p_min_one / 2)
    (ensures fun h0 b h1 ->
       live h1 a /\ live h1 p /\ modifies0 h0 h1 /\
       Int32.v b = S.leg_symbol (as_snat h0 a) (as_snat h0 p)
       )
let leg_symbol #nLen p p_min_one p_min_one_half a =
  push_frame ();
  let tmp = create nLen (uint 0) in
  bn_modular_exp p a p_min_one_half tmp;
  let h = FStar.HyperStack.ST.get () in

  let res = if bn_is_equal p_min_one tmp then (-1l) else begin
              S.is_leg_symbol_raw (as_snat h p) (as_snat h a);
              assert (let res = as_snat h tmp in res = 0 \/ res = 1);
              conv_one_zero_to_int tmp
            end in

  pop_frame ();
  res


val encrypt:
     #nLen:bn_len_s
  -> n:lbignum nLen
  -> y:lbignum nLen
  -> r:lbignum nLen
  -> msg:bool
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
       live h n /\ live h y /\ live h r /\ live h res /\
       disjoint n res /\ disjoint y res /\ disjoint r res /\
       (let n' = as_snat h n in
       let r' = as_snat h r in
       let y' = as_snat h y in
       n' > 1 /\
       y' < n' /\
       r' < n' /\ sqr #n' r' > 0 /\ sqr #n' r' *% y' > 0))
    (ensures fun h0 _ h1 ->
       live h1 n /\ live h1 y /\ live h1 r /\ live h1 res /\
       modifies1 res h0 h1 /\
       as_snat h1 res = S.encrypt_minimal (as_snat h0 n) (as_snat h0 y) (as_snat h0 r) msg)
let encrypt #nLen n y r msg res =
  if not msg then bn_modular_mul n r r res else begin
    push_frame ();
    let r' = create nLen (uint 0) in
    bn_modular_mul n r r r';
    bn_modular_mul n r' y res;
    pop_frame ()
  end


val decrypt:
     #nLen:bn_len_s
  -> p:lbignum nLen
  -> p_min_one:lbignum nLen
  -> p_min_one_half:lbignum nLen
  -> c:lbignum nLen
  -> Stack bool
    (requires fun h ->
       live h p /\ live h p_min_one /\ live h p_min_one_half /\ live h c /\
       disjoint c p /\
       as_snat h c > 0 /\
       as_snat h p > 1 /\
       isprm (as_snat h p) /\
       as_snat h p_min_one = as_snat h p - 1 /\
       as_snat h p_min_one_half = as_snat h p_min_one / 2)
    (ensures fun h0 b h1 -> modifies0 h0 h1 /\
      (let c' = as_snat h0 c in
       b = S.decrypt_minimal (as_snat h0 p) c'))
let decrypt #nLen p p_min_one p_min_one_half c =
  let v = leg_symbol p p_min_one p_min_one_half c in
  if v = 1l then false else true
