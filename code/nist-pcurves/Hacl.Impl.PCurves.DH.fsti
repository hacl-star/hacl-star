module Hacl.Impl.PCurves.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.PCurves.Bignum
open Hacl.Impl.PCurves.Constants
open Hacl.Impl.PCurves.Field
open Hacl.Impl.PCurves.Scalar
open Hacl.Impl.PCurves.InvSqrt
open Hacl.Impl.PCurves.Group

module S = Spec.PCurves
module PP = Hacl.PCurves.PrecompTable

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"
[@(strict_on_arguments [0;1;2;3;4;5;6;7])]
inline_for_extraction noextract
val ecp256dh_i {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |}
               {| order_ops |} {| curve_inv_sqrt |} {| point_ops |} {| PP.precomp_tables |} :
    public_key:lbuffer uint8 (2ul *. size cp.bytes)
  -> private_key:lbuffer uint8 (size cp.bytes) ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\ disjoint public_key private_key)
  (ensures fun h0 r h1 -> modifies (loc public_key) h0 h1 /\
    (let pk = S.secret_to_public (as_seq h0 private_key) in
    (r <==> Some? pk) /\ (r ==> (as_seq h1 public_key == Some?.v pk))))


[@(strict_on_arguments [0;1;2;3;4;5;6;7])]
inline_for_extraction noextract
val ecp256dh_r {| cp:S.curve_params |} {| curve_constants |} {| bn_ops |} {| field_ops |} 
               {| order_ops |} {| curve_inv_sqrt |} {| point_ops |} {| PP.precomp_tables |} :
    shared_secret:lbuffer uint8 (2ul *. size cp.bytes)
  -> their_pubkey:lbuffer uint8 (2ul *. size cp.bytes)
  -> private_key:lbuffer uint8 (size cp.bytes) ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (let ss = S.ecdh (as_seq h0 their_pubkey) (as_seq h0 private_key) in
    (r <==> Some? ss) /\ (r ==> (as_seq h1 shared_secret == Some?.v ss))))
