module Hacl.Chacha20Poly1305

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.All

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Hacl.Impl.Chacha20Poly1305.Poly


module LSeq = Lib.Sequence
module ST = FStar.HyperStack.ST
module Spec = Spec.Chacha20Poly1305
module Chacha = Hacl.Impl.Chacha20


#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let aead_encrypt k n aadlen aad mlen m cipher mac =
  Chacha.chacha20_encrypt mlen cipher m k n 1ul;
  poly1305_do k n aadlen aad mlen cipher mac

let aead_decrypt k n aadlen aad mlen m cipher mac =
  push_frame();
  let h0 = get() in
  // Create a buffer to store the temporary mac
  let computed_mac = create 16ul (u8 0) in
  // Compute the expected mac using Poly1305
  poly1305_do k n aadlen aad mlen cipher computed_mac;
  let h1 = get() in
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
