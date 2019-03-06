module Hacl.Impl.Chacha20Poly1305.Poly

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.ByteSequence
module Seq = Lib.Sequence
open FStar.Mul

module Spec = Spec.Chacha20Poly1305
module Poly = Hacl.Impl.Poly1305

val poly1305_do:
  k:lbuffer uint8 32ul ->
  n:lbuffer uint8 12ul ->
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen ->
  out:lbuffer uint8 16ul ->
  Stack unit
    (requires (fun h ->
      live h k /\ live h aad /\ live h m /\ live h out))
    (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
      let poly_k = Seq.sub (Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n)) 0 32 in
      as_seq h1 out == Spec.poly1305_do poly_k (v mlen) (as_seq h0 m) (v aadlen) (as_seq h0 aad))))

let poly1305_do k aadlen aad mlen m out = admit()
