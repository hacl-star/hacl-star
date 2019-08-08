module Hacl.Impl.Bignum.Openssl

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open LowStar.Buffer

open Hacl.Impl.Bignum.Core
open Hacl.Spec.Bignum

open Lib.IntTypes
open Lib.Math.Algebra
open Lib.Buffer

noextract inline_for_extraction
val enable_ossl : bool
let enable_ossl = true

val ossl_is_prm:
     #pLen:bn_len
  -> tries:size_t
  -> p:lbignum pLen
  -> Stack size_t
    (requires fun h -> live h p)
    (ensures fun h0 _ h1 -> h0 == h1)


val ossl_divide:
     #aLen:bn_len
  -> a:lbignum aLen
  -> b:lbignum aLen
  -> q:lbignum aLen
  -> r:lbignum aLen
  -> Stack unit
    (requires fun h ->
     live h a /\ live h b /\ live h q /\ live h r /\
     all_disjoint [loc a; loc b; loc q; loc r] /\
     as_snat h b <> 0)
    (ensures fun h0 _ h1 -> modifies2 q r h0 h1 /\
      as_snat h1 q = as_snat h0 a / as_snat h0 b /\
      as_snat h1 r = as_snat h0 a % as_snat h0 b)

val ossl_mod:
     #aLen:bn_len{ v aLen * 64 <= max_size_t }
  -> #modLen:bn_len{ v modLen * 64 <= max_size_t }
  -> a:lbignum aLen
  -> mod:lbignum modLen
  -> res:lbignum modLen
  -> Stack unit
    (requires fun h ->
       live h a /\ live h mod /\ live h res /\
       disjoint res a /\ disjoint res mod /\ as_snat h mod > 1)
    (ensures fun h0 _ h1 ->
       live h1 a /\ live h1 mod /\ live h1 res /\ modifies1 res h0 h1 /\
       as_snat h1 res = as_snat h0 a % as_snat h0 mod)

val ossl_mod_add:
     #len:bn_len{ (v len + 1) * 64 <= max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       disjoint res a /\ disjoint res b /\ disjoint res n /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
       live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
       modifies (loc res) h0 h1 /\
       as_snat h1 res = (as_snat h0 a + as_snat h0 b) % as_snat h0 n)

val ossl_mod_sub:
     #len:bn_len{ (v len + 1) * 64 <= max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       disjoint res a /\ disjoint res b /\ disjoint res n /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
       live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
       modifies (loc res) h0 h1 /\
       as_snat h1 res = (as_snat h0 a - as_snat h0 b) % as_snat h0 n)

val ossl_mod_mul:
     #len:bn_len_strict{v len * 128 < max_size_t}
  -> n:lbignum len
  -> a:lbignum len
  -> b:lbignum len
  -> res:lbignum len
  -> Stack unit
    (requires fun h ->
       live h n /\ live h a /\ live h b /\ live h res /\
       disjoint res a /\ disjoint res b /\ disjoint res n /\
       as_snat h n > 1)
    (ensures  fun h0 _ h1 ->
       live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
       modifies (loc res) h0 h1 /\
       as_snat h1 res = (as_snat h0 a * as_snat h0 b) % as_snat h0 n)

val ossl_mod_exp:
     #nLen:bn_len_strict{v nLen * 128 < max_size_t}
  -> #expLen:bn_len_strict
  -> n:lbignum nLen
  -> a:lbignum nLen
  -> b:lbignum expLen
  -> res:lbignum nLen
  -> Stack unit
    (requires fun h ->
      live h n /\ live h a /\ live h b /\ live h res /\
      disjoint a res /\ disjoint b res /\ disjoint n res /\
      as_snat h n > 1)
    (ensures  fun h0 _ h1 -> modifies1 res h0 h1 /\
      live h1 n /\ live h1 a /\ live h1 b /\ live h1 res /\
      (let n = as_snat h0 n in
       as_snat h1 res = mexp (to_fe #n (as_snat h0 a)) (as_snat h0 b)))

val solve_dlp_single_external:
     #nLen:bn_len_strict{v nLen * 128 < max_size_t}
  -> n:lbignum nLen
  -> p:lbignum nLen
  -> e:lbignum nLen
  -> g:lbignum nLen
  -> a:lbignum nLen
  -> res:lbignum nLen
  -> Stack unit
  (requires fun h ->
      live h n /\ live h p /\ live h e /\ live h g /\ live h a /\ live h res /\
      all_disjoint [loc n; loc p; loc e; loc g; loc a; loc res] /\
      exp (as_snat h p) (as_snat h e) < as_snat h n /\
      as_snat h g < as_snat h n /\
      as_snat h a < as_snat h n
      )
  (ensures fun h0 _ h1 ->
      modifies1 res h0 h1 /\
      as_snat h1 res < exp (as_snat h0 p) (as_snat h0 e) /\
      (let n = as_snat h0 n in
       mexp #n (as_snat h0 g) (as_snat h1 res) = as_snat h0 a))
