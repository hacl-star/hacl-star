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

  if EverCrypt.TargetConfig.x64 && avx2 then begin
    Hacl.Chacha20Poly1305_256.aead_encrypt k n aadlen aad mlen m cipher tag

  end else if EverCrypt.TargetConfig.x64 && avx then begin
    Hacl.Chacha20Poly1305_128.aead_encrypt k n aadlen aad mlen m cipher tag

  end else begin
    Hacl.Chacha20Poly1305_32.aead_encrypt k n aadlen aad mlen m cipher tag
  end

let aead_decrypt k n aadlen aad mlen m cipher tag =
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in

  if EverCrypt.TargetConfig.x64 && avx2 then begin
    Hacl.Chacha20Poly1305_256.aead_decrypt k n aadlen aad mlen m cipher tag

  end else if EverCrypt.TargetConfig.x64 && avx then begin
    Hacl.Chacha20Poly1305_128.aead_decrypt k n aadlen aad mlen m cipher tag

  end else begin
    Hacl.Chacha20Poly1305_32.aead_decrypt k n aadlen aad mlen m cipher tag
  end
