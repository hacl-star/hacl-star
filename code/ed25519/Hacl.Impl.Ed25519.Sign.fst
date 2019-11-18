module Hacl.Impl.Ed25519.Sign

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
open Lib.Buffer

open Hacl.Impl.Ed25519.Sign.Steps

inline_for_extraction noextract
val sign_:
    signature:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 352ul
  -> tmp_ints:lbuffer uint64 65ul ->
  Stack unit
    (requires fun h ->
      live h signature /\ live h msg /\ live h secret /\
      live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes signature /\ disjoint tmp_bytes secret /\ disjoint tmp_bytes msg /\
      disjoint tmp_ints tmp_bytes /\ disjoint tmp_ints signature /\
      disjoint tmp_ints secret /\ disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc signature |+| loc tmp_bytes |+| loc tmp_ints) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 secret) (as_seq h0 msg))

#set-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let sign_ signature secret len msg tmp_bytes tmp_ints =
  let r    = sub tmp_ints 20ul 5ul  in
  let h    = sub tmp_ints 60ul 5ul  in
  let rs'  = sub tmp_bytes 160ul 32ul in
  let s'   = sub tmp_bytes 192ul 32ul in

  sign_step_1 secret tmp_bytes;
  sign_step_2 len msg tmp_bytes tmp_ints;
  sign_step_3 tmp_bytes tmp_ints;
  sign_step_4 len msg tmp_bytes tmp_ints;
  assert_norm (pow2 56 == 0x100000000000000);
  sign_step_5 tmp_bytes tmp_ints;

  (**) let h5 = ST.get() in
  (**) lemma_nat_from_to_bytes_le_preserves_value (as_seq h5 s') 32;

  concat2 32ul rs' 32ul s' signature

inline_for_extraction noextract
val sign:
    signature:lbuffer uint8 64ul
  -> secret:lbuffer uint8 32ul
  -> len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len ->
  Stack unit
    (requires fun h -> live h signature /\ live h msg /\ live h secret)
    (ensures  fun h0 _ h1 -> modifies (loc signature) h0 h1 /\
      as_seq h1 signature == Spec.Ed25519.sign (as_seq h0 secret) (as_seq h0 msg)
    )
let sign signature secret len msg =
  push_frame();
  let tmp_bytes = create 352ul (u8 0) in
  let tmp_ints  = create 65ul (u64 0) in
  sign_ signature secret len msg tmp_bytes tmp_ints;
  pop_frame()
