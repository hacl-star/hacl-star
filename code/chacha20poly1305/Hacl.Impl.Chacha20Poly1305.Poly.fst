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
open Hacl.Impl.Poly1305.Fields
module ChachaCore = Hacl.Impl.Chacha20.Core32
module Chacha = Hacl.Impl.Chacha20

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

val derive_key:
  k:lbuffer uint8 32ul ->
  n:lbuffer uint8 12ul ->
  out:lbuffer uint8 64ul ->
  Stack unit
    (requires fun h -> live h k /\ live h out /\ live h n /\
      disjoint k out /\ disjoint n out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      Seq.equal
        (as_seq h1 out)
        (Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n))
    )

let derive_key k n out =
  push_frame();
  let ctx = ChachaCore.create_state () in
  Chacha.chacha20_init ctx k n 0ul;
  ChachaCore.store_state out ctx;
  pop_frame()
  
// Implements the actual poly1305_do operation
val poly1305_do_core:
  s:field_spec ->         // Needed for the vectorized operation
  k:lbuffer uint8 32ul -> // key
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen -> // authenticated additional data  
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen -> // plaintext
  out:lbuffer uint8 16ul -> // output: tag
  Stack unit
    (requires fun h ->
      live h k /\ live h aad /\ live h m /\ live h out)
    (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.poly1305_do (as_seq h0 k) (v mlen) (as_seq h0 m) (v aadlen) (as_seq h0 aad)))

let poly1305_do_core s k aadlen aad mlen m out =
  push_frame();
  let ctx = create (nlimb s +. precomplen s) (limb_zero s) in
  Poly.poly1305_init ctx k;
  let block = create 16ul (u8 0) in
  // TODO: Padding should go here
  admit();
  pop_frame()

// Derives the key, and then perform poly1305
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
      live h k /\ live h n /\ live h aad /\ live h m /\ live h out))
    (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
      let poly_k = Seq.sub (Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n)) 0 32 in
      as_seq h1 out == Spec.poly1305_do poly_k (v mlen) (as_seq h0 m) (v aadlen) (as_seq h0 aad))))

let poly1305_do k n aadlen aad mlen m out =
  push_frame ();
  // Create a new buffer to derive the key
  let tmp = create 64ul (u8 0) in
  derive_key k n tmp;
  // The derived key should only be the first 32 bytes
  let key = sub tmp 0ul 32ul in
  // M32 can be abstracted away for a vectorized AEAD
  poly1305_do_core M32 key aadlen aad mlen m out;
  pop_frame()

