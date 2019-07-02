module EverCrypt.CTR.Keys

/// This is an internal-to-EverCrypt module, which provides low-level
/// definitions corresponding to Spec.Cipher.Expansion, i.e. shared between CTR
/// and AEAD.

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers

open Spec.Cipher.Expansion
friend Spec.Cipher.Expansion

#set-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0"

let _: squash (inversion impl) = allow_inversion impl

inline_for_extraction noextract
let vale_impl = a:impl { a = Vale_AES128 \/ a = Vale_AES256 }

let vale_alg_of_vale_impl (i: vale_impl) =
  match i with
  | Vale_AES128 -> Vale.AES.AES_s.AES_128
  | Vale_AES256 -> Vale.AES.AES_s.AES_256

inline_for_extraction noextract
let key_offset (i: vale_impl) =
  match i with
  | Vale_AES128 -> 176ul
  | Vale_AES256 -> 240ul

inline_for_extraction
let concrete_xkey_len (i: impl): Tot (x:UInt32.t { UInt32.v x = concrete_xkey_length i }) =
  match i with
  | Hacl_CHACHA20 -> 32ul
  | Vale_AES256
  | Vale_AES128 ->
      key_offset i + 128ul

inline_for_extraction noextract
let aes_gcm_key_expansion (i: vale_impl):
  Vale.Wrapper.X64.AES.key_expansion_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.AES.aes128_key_expansion_stdcall
  | Vale_AES256 -> Vale.Wrapper.X64.AES.aes256_key_expansion_stdcall

inline_for_extraction noextract
let aes_gcm_keyhash_init (i: vale_impl):
  Vale.Wrapper.X64.AEShash.keyhash_init_st (vale_alg_of_vale_impl i) =
  match i with
  | Vale_AES128 -> Vale.Wrapper.X64.AEShash.aes128_keyhash_init_stdcall
  | Vale_AES256 -> Vale.Wrapper.X64.AEShash.aes256_keyhash_init_stdcall

