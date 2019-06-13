module Hacl.Impl.Ed25519.Sign.Expanded

module ST = FStar.HyperStack.ST
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Ed25519.Sign
open Hacl.Impl.Ed25519.Sign.Steps
open Hacl.Impl.Ed25519.SecretExpand
open Hacl.Impl.Ed25519.SecretToPublic

type keys = lbuffer uint8 96ul
inline_for_extraction private let pk (ks:keys) = sub ks 0ul 32ul
inline_for_extraction private let xsk (ks:keys) = sub ks 32ul 64ul
inline_for_extraction private let xlow (ks:keys) = sub ks 32ul 32ul
inline_for_extraction private let xhigh (ks:keys) = sub ks 64ul 32ul

inline_for_extraction
val expand_keys:
    ks:keys
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h ks /\ live h secret /\ disjoint ks secret)
    (ensures  fun h0 _ h1 -> modifies (loc ks) h0 h1)
let expand_keys ks secret =
  secret_expand (xsk ks) secret;
  secret_to_public (pk ks) secret

inline_for_extraction
val load_keys:
    tmp_bytes:lbuffer uint8 352ul
  -> ks:keys ->
  Stack unit
    (requires fun h -> live h ks /\ live h tmp_bytes /\ disjoint ks tmp_bytes)
    (ensures  fun h0 _ h1 -> modifies (loc tmp_bytes) h0 h1)
let load_keys tmp_bytes ks =
  let tmp_public = sub tmp_bytes 96ul 32ul in
  let tmp_xsecret = sub tmp_bytes 224ul 64ul in
  copy tmp_public (pk ks);
  copy tmp_xsecret (xsk ks)

inline_for_extraction
val sign_:
    signature:lbuffer uint8 64ul
  -> ks:keys
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 352ul
  -> tmp_ints:lbuffer uint64 65ul ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h ks /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes signature /\ disjoint tmp_bytes ks /\ disjoint tmp_bytes msg /\
      disjoint tmp_ints tmp_bytes /\ disjoint tmp_ints signature /\
      disjoint tmp_ints ks /\ disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc signature |+| loc tmp_bytes |+| loc tmp_ints) h0 h1)
let sign_ signature ks len msg tmp_bytes tmp_ints =
  let r    = sub tmp_ints 20ul 5ul  in
  let h    = sub tmp_ints 60ul 5ul  in
  let rs'  = sub tmp_bytes 160ul 32ul in
  let s'   = sub tmp_bytes 192ul 32ul in
  load_keys tmp_bytes ks;
  sign_step_2 len msg tmp_bytes tmp_ints;
  sign_step_3 tmp_bytes tmp_ints;
  sign_step_4 len msg tmp_bytes tmp_ints;
  sign_step_5 tmp_bytes tmp_ints;
  concat2 32ul rs' 32ul s' signature

inline_for_extraction
val sign:
    signature:lbuffer uint8 64ul
  -> ks:keys
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h ks)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1)
let sign signature ks msg len =
  push_frame();
  let tmp_bytes = create 352ul (u8 0) in
  let tmp_ints  = create 65ul (u64 0) in
  sign_ signature ks msg len tmp_bytes tmp_ints;
  pop_frame()
