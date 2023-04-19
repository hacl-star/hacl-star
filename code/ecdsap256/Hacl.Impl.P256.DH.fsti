module Hacl.Impl.P256.DH

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module S = Spec.P256

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val ecp256dh_i:
    public_key:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h public_key /\ live h private_key /\ disjoint public_key private_key)
  (ensures fun h0 r h1 -> modifies (loc public_key) h0 h1 /\
    (let pk = S.secret_to_public (as_seq h0 private_key) in
    (r <==> Some? pk) /\ (r ==> (as_seq h1 public_key == Some?.v pk))))


val ecp256dh_r:
    shared_secret:lbuffer uint8 64ul
  -> their_pubkey:lbuffer uint8 64ul
  -> private_key:lbuffer uint8 32ul ->
  Stack bool
  (requires fun h ->
    live h shared_secret /\ live h their_pubkey /\ live h private_key /\
    disjoint shared_secret their_pubkey /\ disjoint shared_secret private_key)
  (ensures fun h0 r h1 -> modifies (loc shared_secret) h0 h1 /\
    (let ss = S.ecdh (as_seq h0 their_pubkey) (as_seq h0 private_key) in
    (r <==> Some? ss) /\ (r ==> (as_seq h1 shared_secret == Some?.v ss))))
