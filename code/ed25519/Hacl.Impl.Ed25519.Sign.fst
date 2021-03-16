module Hacl.Impl.Ed25519.Sign

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
open Lib.Buffer

open Hacl.Impl.Ed25519.Sign.Expanded

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val sign:
    signature:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h secret)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 secret) (as_seq h0 msg)
    )

let sign signature secret len msg =
  push_frame();
  let ks = create 96ul (u8 0) in
  expand_keys ks secret;
  sign_expanded signature ks len msg;
  pop_frame()
