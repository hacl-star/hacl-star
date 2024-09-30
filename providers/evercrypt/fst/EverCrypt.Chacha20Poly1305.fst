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
  let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
  let vec128 = EverCrypt.AutoConfig2.has_vec128 () in
  if EverCrypt.TargetConfig.hacl_can_compile_vec256 && vec256 then begin
    LowStar.Ignore.ignore vec128;
    Hacl.Chacha20Poly1305_256.encrypt cipher tag m mlen aad aadlen k n
  end else if EverCrypt.TargetConfig.hacl_can_compile_vec128 && vec128 then begin
    LowStar.Ignore.ignore vec256;
    Hacl.Chacha20Poly1305_128.encrypt cipher tag m mlen aad aadlen k n

  end else begin
    LowStar.Ignore.ignore vec128;
    LowStar.Ignore.ignore vec256;
    Hacl.Chacha20Poly1305_32.encrypt cipher tag m mlen aad aadlen k n
  end

let aead_decrypt k n aadlen aad mlen m cipher tag =
  let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
  let vec128 = EverCrypt.AutoConfig2.has_vec128 () in

  if EverCrypt.TargetConfig.hacl_can_compile_vec256 && vec256 then begin
    LowStar.Ignore.ignore vec128;
    Hacl.Chacha20Poly1305_256.decrypt m cipher mlen aad aadlen k n tag

  end else if EverCrypt.TargetConfig.hacl_can_compile_vec128 && vec128 then begin
    LowStar.Ignore.ignore vec256;
    Hacl.Chacha20Poly1305_128.decrypt m cipher mlen aad aadlen k n tag

  end else begin
    LowStar.Ignore.ignore vec128;
    LowStar.Ignore.ignore vec256;
    Hacl.Chacha20Poly1305_32.decrypt m cipher mlen aad aadlen k n tag
  end
