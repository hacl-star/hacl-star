module Hacl.Impl.Chacha20Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
module Seq = Lib.Sequence
open FStar.Mul

module Spec = Spec.Chacha20Poly1305

val aead_encrypt_chacha_poly:
  k:lbuffer uint8 32ul ->
  n:lbuffer uint8 12ul ->
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen ->
  out:lbuffer uint8 (UInt32.add mlen 16ul) ->
  Stack unit
    (requires (fun h ->
      disjoint k out /\
      disjoint n out /\
      eq_or_disjoint m out /\
      disjoint aad out /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h out))
    (ensures  (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      Seq.equal
        (as_seq h1 out)
        (Spec.aead_encrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) (as_seq h0 aad))
    ))
