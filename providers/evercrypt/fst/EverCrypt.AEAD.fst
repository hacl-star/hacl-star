module EverCrypt.AEAD

module S = FStar.Seq
module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Integers

open Spec.AEAD

friend Spec.AEAD

#set-options "--max_fuel 0 --max_ifuel 0"

let ekv_len (a: supported_alg): Tot (x:UInt32.t { UInt32.v x = ekv_length a }) =
  match a with
  | CHACHA20_POLY1305 -> 32ul
  | AES128_GCM -> 176ul
  | AES256_GCM -> 240ul

let expand_in #a r k =
  match a with
  | AES128_GCM | AES256_GCM ->
      let h0 = ST.get () in
      let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
      if EverCrypt.TargetConfig.x64 then
        let ek =
          MB.mmalloc #UInt8.t #(frozen_preorder (expand #a (G.reveal kv))) r 0uy (ekv_len a)
        in
        admit () // waiting for interop wrappers
      else
        EK kv MB.mnull
  | CHACHA20_POLY1305 ->
      let h0 = ST.get () in
      let kv: G.erased (kv a) = G.hide (B.as_seq h0 k) in
      let ek = MB.mmalloc #UInt8.t #(frozen_preorder (expand #a (G.reveal kv))) r 0uy 32ul in
      MB.blit k 0ul ek 0ul 32ul;
      let h2 = ST.get () in
      B.modifies_only_not_unused_in B.loc_none h0 h2;
      assert (B.as_seq h2 ek == B.as_seq h0 k);
      MB.witness_p ek (S.equal (G.reveal kv));
      EK kv ek
  | _ ->
      EK (G.hide (S.empty #UInt8.t)) MB.mnull

#set-options "--z3rlimit 100"
let encrypt #a ek iv ad ad_len plain plain_len dst =
  if MB.is_null (EK?.ek ek) then
    InvalidKey
  else match a with
  | AES128_GCM | AES256_GCM ->
      admit ()
  | CHACHA20_POLY1305 ->
      // Monotonicity; gives us proper length for ek while we're at it.
      MB.recall_p (EK?.ek ek) (S.equal (expand_or_dummy a (EK?.kv ek)));
      assert (MB.length (EK?.ek ek) = 32);
      assert (B.length iv = 12);

      push_frame ();
      // Cannot pass a frozen buffer to a function that expects a regular
      // buffer. (Or can we? Prove compatibility of preorders?). In any case, we
      // just allocate a temporary on the stack and blit.
      let tmp = B.alloca 0uy 32ul in
      MB.blit (EK?.ek ek) 0ul tmp 0ul 32ul;

      // Length restrictions
      assert_norm (pow2 31 + pow2 32 / 64 <= pow2 32 - 1);

      Hacl.Impl.Chacha20Poly1305.aead_encrypt_chacha_poly
        tmp iv ad_len ad plain_len plain dst;
      pop_frame ();
      Success
