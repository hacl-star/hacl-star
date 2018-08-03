module EverCrypt.Hash.Test

open FStar.HyperStack.ST
open FStar.Integers
open FStar.Seq
open EverCrypt.Helpers
open EverCrypt.Hash

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies

val compute:
  a: alg ->
  len: UInt32.t ->
  text: uint8_pl (v len) ->
  tag: uint8_pl (tagLength (Ghost.hide a)) -> ST unit
  (requires fun h0 ->
    B.live h0 text /\
    B.live h0 tag /\
    M.(loc_disjoint (loc_buffer text) (loc_buffer tag)))
  (ensures fun h0 () h1 ->
    B.live h1 text /\ B.live h1 tag /\
    // M.(modifies (loc_buffer tag) h0 h1) /\
    v len <= maxLength (Ghost.hide a) /\ (* required for subtyping the RHS below *)
    B.as_seq h1 tag = spec (Ghost.hide a) (B.as_seq h0 text))
//18-07-07 TODO add dealloation; restore Stack (not ST); restore modifies clause
