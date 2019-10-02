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
module Fields = Hacl.Impl.Poly1305.Fields

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let aead_encrypt k n aadlen aad mlen m cipher tag =
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in

  if EverCrypt.TargetConfig.x64 && avx2 then begin
    Hacl.Impl.Chacha20Poly1305.aead_encrypt #Fields.M256 k n aadlen aad mlen m cipher tag

  end else if EverCrypt.TargetConfig.x64 && avx then begin
    Hacl.Impl.Chacha20Poly1305.aead_encrypt #Fields.M128 k n aadlen aad mlen m cipher tag

  end else begin
    Hacl.Impl.Chacha20Poly1305.aead_encrypt #Fields.M32 k n aadlen aad mlen m cipher tag
  end

let aead_decrypt k n aadlen aad mlen m cipher tag =
  let avx2 = EverCrypt.AutoConfig2.has_avx2 () in
  let avx = EverCrypt.AutoConfig2.has_avx () in

  if EverCrypt.TargetConfig.x64 && avx2 then begin
    Hacl.Impl.Chacha20Poly1305.aead_decrypt #Fields.M256 k n aadlen aad mlen m cipher tag

  end else if EverCrypt.TargetConfig.x64 && avx then begin
    Hacl.Impl.Chacha20Poly1305.aead_decrypt #Fields.M128 k n aadlen aad mlen m cipher tag

  end else begin
    Hacl.Impl.Chacha20Poly1305.aead_decrypt #Fields.M32 k n aadlen aad mlen m cipher tag
  end
