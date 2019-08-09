module Hacl.Impl.Ed25519.Sign.Expanded

module ST = FStar.HyperStack.ST
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Buffer

open Hacl.Impl.Ed25519.Sign
open Hacl.Impl.Ed25519.Sign.Steps
open Hacl.Impl.Ed25519.SecretExpand
open Hacl.Impl.Ed25519.SecretToPublic

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

type keys = lbuffer uint8 96ul
inline_for_extraction noextract private
let pk (ks:keys) : Stack (lbuffer uint8 32ul)
  (requires fun h -> live h ks)
  (ensures fun h0 f h1 -> f == gsub ks 0ul 32ul /\ h0 == h1)
  = sub ks 0ul 32ul
inline_for_extraction private
let xsk (ks:keys) : Stack (lbuffer uint8 64ul)
  (requires fun h -> live h ks)
  (ensures fun h0 f h1 -> f == gsub ks 32ul 64ul /\ h0 == h1)
  = sub ks 32ul 64ul
inline_for_extraction private
let xlow (ks:keys) : Stack (lbuffer uint8 32ul)
  (requires fun h -> live h ks)
  (ensures fun h0 f h1 -> f == gsub ks 32ul 32ul /\ h0 == h1)
  = sub ks 32ul 32ul
inline_for_extraction private
let xhigh (ks:keys) : Stack (lbuffer uint8 32ul)
  (requires fun h -> live h ks)
  (ensures fun h0 f h1 -> f == gsub ks 64ul 32ul /\ h0 == h1)
  = sub ks 64ul 32ul

inline_for_extraction
val expand_keys:
    ks:keys
  -> secret:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h -> live h ks /\ live h secret /\ disjoint ks secret)
    (ensures  fun h0 _ h1 -> modifies (loc ks) h0 h1 /\
      (let pub, s, prefix = Spec.Ed25519.expand_keys (as_seq h0 secret) in
      as_seq h1 (gsub ks 0ul 32ul) == pub /\
      as_seq h1 (gsub ks 32ul 32ul) == s /\
      as_seq h1 (gsub ks 64ul 32ul) == prefix)
    )
let expand_keys ks secret =
  secret_expand (xsk ks) secret;
  secret_to_public (pk ks) secret

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
    (ensures fun h0 _ h1 -> modifies (loc signature |+| loc tmp_bytes |+| loc tmp_ints) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub ks 0ul 32ul))
        (as_seq h0 (gsub ks 32ul 32ul))
        (as_seq h0 (gsub ks 64ul 32ul))
        (as_seq h0 msg)
    )

#set-options "--z3rlimit 50"

let sign_ signature ks len msg tmp_bytes tmp_ints =
  let r    = sub tmp_ints 20ul 5ul  in
  let h    = sub tmp_ints 60ul 5ul  in
  let rs'  = sub tmp_bytes 160ul 32ul in
  let s'   = sub tmp_bytes 192ul 32ul in
  let tmp_public = sub tmp_bytes 96ul 32ul in
  let tmp_xsecret = sub tmp_bytes 224ul 64ul in
  (**) let h0 = get() in

  copy tmp_public (pk ks);
  copy tmp_xsecret (xsk ks);

  (**) let h1 = get() in
  (**) assert (as_seq h1 (gsub tmp_bytes 96ul 32ul) `Seq.equal` as_seq h0 (gsub ks 0ul 32ul));
  (**) assert (Seq.slice (as_seq h0 (gsub ks 32ul 64ul)) 0 32 `Seq.equal` as_seq h0 (gsub ks 32ul 32ul));
  (**) assert (as_seq h1 (gsub tmp_bytes 224ul 32ul) `Seq.equal` as_seq h0 (gsub ks 32ul 32ul));
  (**) assert (Seq.slice (as_seq h0 (gsub ks 32ul 64ul)) 32 64 `Seq.equal` as_seq h0 (gsub ks 64ul 32ul));
  (**) assert (as_seq h1 (gsub tmp_bytes 256ul 32ul) `Seq.equal` as_seq h0 (gsub ks 64ul 32ul));

  sign_step_2 len msg tmp_bytes tmp_ints;
  sign_step_3 tmp_bytes tmp_ints;
  sign_step_4 len msg tmp_bytes tmp_ints;

  (**) assert_norm (pow2 56 == 0x100000000000000);
  sign_step_5 tmp_bytes tmp_ints;

  (**) let h5 = ST.get() in
  (**) lemma_nat_from_to_bytes_le_preserves_value (as_seq h5 s') 32;

  concat2 32ul rs' 32ul s' signature

inline_for_extraction
val sign:
    signature:lbuffer uint8 64ul
  -> ks:keys
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h ks)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign_expanded
        (as_seq h0 (gsub ks 0ul 32ul))
        (as_seq h0 (gsub ks 32ul 32ul))
        (as_seq h0 (gsub ks 64ul 32ul))
        (as_seq h0 msg)
    )
let sign signature ks msg len =
  push_frame();
  let tmp_bytes = create 352ul (u8 0) in
  let tmp_ints  = create 65ul (u64 0) in
  sign_ signature ks msg len tmp_bytes tmp_ints;
  pop_frame()
