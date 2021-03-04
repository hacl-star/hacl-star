module EverCrypt.Chacha20Poly1305

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
module Seq = Lib.Sequence
open FStar.Mul

module Spec = Spec.Chacha20Poly1305

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let aead_encrypt k n aadlen aad mlen m cipher tag =
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in
  let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
  let vec128 = EverCrypt.AutoConfig2.has_vec128 () in

  if EverCrypt.TargetConfig.evercrypt_can_compile_vec256 && vec256 then begin
    Hacl.Chacha20Poly1305_256.aead_encrypt k n aadlen aad mlen m cipher tag

  end else if EverCrypt.TargetConfig.evercrypt_can_compile_vec128 && vec128 then begin
    Hacl.Chacha20Poly1305_128.aead_encrypt k n aadlen aad mlen m cipher tag

  end else begin
    Hacl.Chacha20Poly1305_32.aead_encrypt k n aadlen aad mlen m cipher tag
  end

let aead_decrypt k n aadlen aad mlen m cipher tag =
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in
  let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
  let vec128 = EverCrypt.AutoConfig2.has_vec128 () in

  if EverCrypt.TargetConfig.evercrypt_can_compile_vec256 && vec256 then begin
    Hacl.Chacha20Poly1305_256.aead_decrypt k n aadlen aad mlen m cipher tag

  end else if EverCrypt.TargetConfig.evercrypt_can_compile_vec128 && vec128 then begin
    Hacl.Chacha20Poly1305_128.aead_decrypt k n aadlen aad mlen m cipher tag

  end else begin
    Hacl.Chacha20Poly1305_32.aead_decrypt k n aadlen aad mlen m cipher tag
  end
