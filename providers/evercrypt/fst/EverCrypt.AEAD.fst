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
      let ek =
        MB.mmalloc #UInt8.t #(frozen_preorder (expand #a (G.reveal kv))) r 0uy (ekv_len a)
      in
      admit () // waiting for interop wrappers
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
