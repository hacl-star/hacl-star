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
module Chacha = Hacl.Impl.Chacha20

open Hacl.Impl.Chacha20Poly1305.Poly

inline_for_extraction
val aead_encrypt_chacha_poly_:
  k:lbuffer uint8 32ul ->
  n:lbuffer uint8 12ul ->
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen ->
  cipher:lbuffer uint8 mlen ->
  mac:lbuffer uint8 16ul ->
  Stack unit
    (requires (fun h ->
      disjoint k cipher /\ disjoint n cipher /\ 
      disjoint k mac /\ disjoint n mac /\
      disjoint cipher mac /\
      eq_or_disjoint m cipher /\
      disjoint aad cipher /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h cipher /\ live h mac))
    (ensures  (fun h0 _ h1 -> modifies (loc cipher |+| loc mac) h0 h1 /\
    Seq.equal
      (Seq.concat (as_seq h1 cipher) (as_seq h1 mac))
      (Spec.aead_encrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) (as_seq h0 aad))))

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let aead_encrypt_chacha_poly_ k n aadlen aad mlen m cipher mac =
  let h0 = ST.get() in
  Chacha.chacha20_encrypt mlen cipher m k n 1ul;
  let h1 = ST.get() in
  poly1305_do k n aadlen aad mlen cipher mac;
  let h2 = ST.get() in
  assert (
    let poly_k = Seq.sub (Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n)) 0 32 in
    Seq.equal (as_seq h2 mac)
      (Spec.poly1305_do poly_k (v mlen) (as_seq h1 cipher) (v aadlen) (as_seq h1 aad))
    )

let aead_encrypt_chacha_poly k n aadlen aad mlen m out =
  let cipher = sub out 0ul mlen in
  let mac = sub out mlen 16ul in
  aead_encrypt_chacha_poly_ k n aadlen aad mlen m cipher mac

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let aead_decrypt_chacha_poly k n aadlen aad mlen m cipher mac =
  push_frame();
  let h0 = get() in
  // Create a buffer to store the temporary mac
  let computed_mac = create 16ul (u8 0) in
  // Compute the expected mac using Poly1305
  poly1305_do k n aadlen aad mlen cipher computed_mac;
  let h1 = get() in
  assert (
    let poly_k = Seq.sub (Spec.Chacha20.chacha20_key_block0 (as_seq h0 k) (as_seq h0 n)) 0 32 in
    Seq.equal (as_seq h1 computed_mac)
      (Spec.poly1305_do poly_k (v mlen) (as_seq h0 cipher) (v aadlen) (as_seq h0 aad))
    );
  let res =
    if lbytes_eq computed_mac mac then (
      assert (Lib.ByteSequence.lbytes_eq (as_seq h1 computed_mac) (as_seq h1 mac));
      // If the computed mac matches the mac given, decrypt the ciphertext and return 0
      Chacha.chacha20_encrypt mlen m cipher k n 1ul;
      0ul
    ) else 1ul // Macs do not agree, do not decrypt
  in
  pop_frame();
  res
