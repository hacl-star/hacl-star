module Hacl.Impl.ECIES

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.ECIES


///
/// Constants
///

inline_for_extraction
let size_id_of_ciphersuite = size 1

inline_for_extraction
let size_nonce = size (Spec.ECIES.size_nonce ciphersuite)

inline_for_extraction
let size_aead_key = size 32

inline_for_extraction
let size_aead_nonce = size 16

inline_for_extraction
let size_key = size (Spec.ECIES.size_key ciphersuite)

inline_for_extraction
let size_key_dh = size (Spec.ECIES.size_key_dh ciphersuite)

inline_for_extraction
let size_ecies_secret = 1ul +. size_key +. 2ul *. size_key_dh

inline_for_extraction
let size_context = size 32

inline_for_extraction
let size_info = size_id_of_ciphersuite + (size Spec.ECIES.size_label_key) + size_context



val encap:
    output: lbuffer uint8 size_ecies_secret
  -> pk: key_public_p
  -> context: lbuffer uint8 size_context ->
  Stack unit
  (requires (fun h -> live h output /\ live h pk /\ live h context
                 /\ disjoint output pk /\ disjoint output context))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let encap output pk context = Hacl.Impl.ECIES.encap output pk context


val decap:
    output: lbuffer uint8 (size_key +. 1ul)
  -> kpriv: key_private_p
  -> eph_kpub: key_public_p
  -> context: lbuffer uint8 size_context ->
  Stack unit
  (requires (fun h -> live h output /\ live h kpriv /\ live h eph_kpub /\ live h context))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let decap output sk epk context = Hacl.Impl.ECIES.decap output sk epk context


val encrypt:
    output: buffer uint8
  -> sk: lbuffer uint8 size_key_dh
  -> input: buffer uint8
  -> len: size_t{v len == length input}
  -> aad: buffer uint8
  -> alen: size_t{v alen == length aad}
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h output /\ live h sk /\ live h input /\ live h aad
                 /\ disjoint output sk /\ disjoint output input /\ disjoint output aad))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let encrypt output sk input len aad alen counter = Hacl.Impl.ECIES.encrypt output sk input len aad alen counter
