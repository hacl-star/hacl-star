module Hacl.Impl.Ed25519.Sign.Steps

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
open Lib.Buffer

module F51 = Hacl.Impl.Ed25519.Field51
module F56 = Hacl.Impl.Ed25519.Field56
module S56 = Hacl.Spec.Ed25519.Field56.Definition

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

inline_for_extraction noextract
let point = lbuffer uint64 20ul

val point_mul_compress:
    out:lbuffer uint8 32ul
  -> s:lbuffer uint8 32ul
  -> p:point ->
  Stack unit
    (requires fun h ->
      live h out /\ live h s /\ live h p /\
      disjoint s out /\ disjoint p out /\
      F51.point_inv_t h p)
    (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1)
let point_mul_compress out s p =
  push_frame();
  let tmp:point = create 20ul (u64 0) in
  Hacl.Impl.Ed25519.Ladder.point_mul tmp s p;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  pop_frame()


val point_mul_g_compress:
    out:lbuffer uint8 32ul
  -> s:lbuffer uint8 32ul ->
  Stack unit
    (requires fun h ->
      live h out /\ live h s /\ disjoint s out)
    (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Ed25519.point_compress (Spec.Ed25519.point_mul (as_seq h0 s) Spec.Ed25519.g)
    )

let point_mul_g_compress out s =
  push_frame();
  let tmp:point = create 20ul (u64 0) in
  Hacl.Impl.Ed25519.Ladder.point_mul_g tmp s;
  Hacl.Impl.Ed25519.PointCompress.point_compress out tmp;
  pop_frame()

val sign_step_1:
    secret:lbuffer uint8 32ul
  -> tmp_bytes:lbuffer uint8 352ul ->
  Stack unit
    (requires fun h ->
      live h secret /\ live h tmp_bytes /\ disjoint secret tmp_bytes)
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes) h0 h1 /\
      (let a, prefix = Spec.Ed25519.secret_expand (as_seq h0 secret) in
        as_seq h1 (gsub tmp_bytes 224ul 32ul) == a /\
        as_seq h1 (gsub tmp_bytes 256ul 32ul) == prefix /\
        as_seq h1 (gsub tmp_bytes 96ul 32ul) ==
        Spec.Ed25519.point_compress (Spec.Ed25519.point_mul a Spec.Ed25519.g)))

let sign_step_1 secret tmp_bytes =
  let a''    = sub tmp_bytes 96ul  32ul in
  let apre   = sub tmp_bytes 224ul 64ul in
  let a      = sub apre 0ul 32ul in
  let prefix = sub apre 32ul 32ul in
  Hacl.Impl.Ed25519.SecretExpand.secret_expand apre secret;
  point_mul_g_compress a'' a

val sign_step_2:
    len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 352ul
  -> tmp_ints:lbuffer uint64 65ul ->
  Stack unit
    (requires fun h ->
      live h msg /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes msg /\ disjoint tmp_bytes tmp_ints /\
      disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc tmp_ints) h0 h1 /\
    (let s = as_seq h1 (gsub tmp_ints 20ul 5ul) in
       v (Seq.index s 0) < pow2 56 /\
       v (Seq.index s 1) < pow2 56 /\
       v (Seq.index s 2) < pow2 56 /\
       v (Seq.index s 3) < pow2 56 /\
       v (Seq.index s 4) < pow2 32) /\
      F56.as_nat h1 (gsub tmp_ints 20ul 5ul) == Spec.Ed25519.sha512_modq (32 + v len)
        (concat #uint8 #32 #(v len) (as_seq h0 (gsub tmp_bytes 256ul 32ul)) (as_seq h0 msg)))

let sign_step_2 len msg tmp_bytes tmp_ints =
  let r      = sub tmp_ints 20ul 5ul  in
  let a''    = sub tmp_bytes 96ul  32ul in
  let apre   = sub tmp_bytes 224ul 64ul in
  let a      = sub apre 0ul 32ul in
  let prefix = sub apre 32ul 32ul in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre r prefix len msg

val sign_step_3:
    tmp_bytes:lbuffer uint8 352ul
  -> tmp_ints:lbuffer uint64 65ul ->
  Stack unit
    (requires fun h ->
      live h tmp_bytes /\ live h tmp_ints /\ disjoint tmp_bytes tmp_ints /\
      (let s = as_seq h (gsub tmp_ints 20ul 5ul) in
       v (Seq.index s 0) < pow2 56 /\
       v (Seq.index s 1) < pow2 56 /\
       v (Seq.index s 2) < pow2 56 /\
       v (Seq.index s 3) < pow2 56 /\
       v (Seq.index s 4) < pow2 32)
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_bytes 96ul 32ul) == as_seq h1 (gsub tmp_bytes 96ul 32ul) /\
      as_seq h0 (gsub tmp_bytes 224ul 32ul) == as_seq h1 (gsub tmp_bytes 224ul 32ul) /\
      // Postcondition
      (assert_norm (pow2 56 < pow2 64); assert_norm (pow2 32 < pow2 64);
        assert_norm (S56.as_nat5 (u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 56 - 1), u64 (pow2 32 - 1)) < pow2 256);
      as_seq h1 (gsub tmp_bytes 160ul 32ul) ==
      Spec.Ed25519.point_compress (Spec.Ed25519.point_mul
        (nat_to_bytes_le 32 (F56.as_nat h0 (gsub tmp_ints 20ul 5ul)))
        (Spec.Ed25519.g))))

let sign_step_3 tmp_bytes tmp_ints =
  let a''  = sub tmp_bytes 96ul  32ul in
  let apre = sub tmp_bytes 224ul 64ul in
  let a    = sub apre 0ul 32ul in
  push_frame();
  let rb = create 32ul (u8 0) in
  let r  = sub tmp_ints 20ul 5ul  in
  let rs' = sub tmp_bytes 160ul 32ul in
  let h0 = ST.get() in
  Hacl.Impl.Store56.store_56 rb r;
  let h1 = ST.get() in
  point_mul_g_compress rs' rb;
  pop_frame()

val sign_step_4:
    len:size_t{v len + 64 <= max_size_t}
  -> msg:lbuffer uint8 len
  -> tmp_bytes:lbuffer uint8 352ul
  -> tmp_ints:lbuffer uint64 65ul ->
  Stack unit
    (requires fun h ->
      live h msg /\ live h tmp_bytes /\ live h tmp_ints /\
      disjoint tmp_bytes msg /\ disjoint tmp_bytes tmp_ints /\
      disjoint tmp_ints msg)
    (ensures fun h0 _ h1 -> modifies (loc tmp_ints) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_ints 20ul 5ul) == as_seq h1 (gsub tmp_ints 20ul 5ul) /\
      // Postcondition
      (let s = as_seq h1 (gsub tmp_ints 60ul 5ul) in
       let op_String_Access = Seq.index in
       v s.[0] < 0x100000000000000 /\
       v s.[1] < 0x100000000000000 /\
       v s.[2] < 0x100000000000000 /\
       v s.[3] < 0x100000000000000 /\
       v s.[4] < 0x100000000000000) /\
      F56.as_nat h1 (gsub tmp_ints 60ul 5ul) ==
      Spec.Ed25519.sha512_modq (64 + v len)
        (concat #uint8 #64 #(v len)
          (concat #uint8 #32 #32
            (as_seq h0 (gsub tmp_bytes 160ul 32ul))
            (as_seq h0 (gsub tmp_bytes 96ul 32ul)))
          (as_seq h0 msg)
        )
      )

let sign_step_4 len msg tmp_bytes tmp_ints =
  let tmp_bytes' = tmp_bytes in
  let r    = sub tmp_ints 20ul 5ul  in
  let h    = sub tmp_ints 60ul 5ul  in
  let a''  = sub tmp_bytes 96ul  32ul in
  let rb   = sub tmp_bytes 128ul 32ul in
  let rs'  = sub tmp_bytes 160ul 32ul in
  let apre = sub tmp_bytes 224ul 64ul in
  let a    = sub apre 0ul 32ul in
  assert_norm (pow2 56 == 0x100000000000000);
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 h rs' a'' len msg

val sign_step_5:
    tmp_bytes:lbuffer uint8 352ul
  -> tmp_ints:lbuffer uint64 65ul ->
  Stack unit
    (requires fun h ->
      live h tmp_bytes /\ live h tmp_ints /\ disjoint tmp_bytes tmp_ints /\
      (let s = as_seq h (gsub tmp_ints 60ul 5ul) in
       let op_String_Access = Seq.index in
       v s.[0] < 0x100000000000000 /\
       v s.[1] < 0x100000000000000 /\
       v s.[2] < 0x100000000000000 /\
       v s.[3] < 0x100000000000000 /\
       v s.[4] < 0x100000000000000) /\
      (let s = as_seq h (gsub tmp_ints 20ul 5ul) in
       let op_String_Access = Seq.index in
       v s.[0] < 0x100000000000000 /\
       v s.[1] < 0x100000000000000 /\
       v s.[2] < 0x100000000000000 /\
       v s.[3] < 0x100000000000000 /\
       v s.[4] < 0x100000000000000) /\
       F56.as_nat h (gsub tmp_ints 20ul 5ul) < Spec.Ed25519.q /\
       F56.as_nat h (gsub tmp_ints 60ul 5ul) < pow2 256
    )
    (ensures fun h0 _ h1 -> modifies (loc tmp_bytes |+| loc tmp_ints) h0 h1 /\
      // Framing
      as_seq h0 (gsub tmp_bytes 160ul 32ul) == as_seq h1 (gsub tmp_bytes 160ul 32ul) /\
      // Postcondition
      (let r = F56.as_nat h0 (gsub tmp_ints 20ul 5ul) in
       let h = F56.as_nat h0 (gsub tmp_ints 60ul 5ul) in
       let a = as_seq h0 (gsub tmp_bytes 224ul 32ul) in
      nat_from_bytes_le (as_seq h1 (gsub tmp_bytes 192ul 32ul)) ==
      (r + (h * nat_from_bytes_le a) % Spec.Ed25519.q) % Spec.Ed25519.q))

#set-options "--z3rlimit 40"

let sign_step_5 tmp_bytes tmp_ints =
  let r    = sub tmp_ints 20ul 5ul  in
  let aq   = sub tmp_ints 45ul 5ul  in
  let ha   = sub tmp_ints 50ul 5ul  in
  let s    = sub tmp_ints 55ul 5ul  in
  let h    = sub tmp_ints 60ul 5ul  in
  let s'   = sub tmp_bytes 192ul 32ul in
  let rs'  = sub tmp_bytes 160ul 32ul in
  let a = sub tmp_bytes 224ul 32ul in
  Hacl.Impl.Load56.load_32_bytes aq a;
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  assert_norm (0x100000000000000 == pow2 56);
  Hacl.Impl.Store56.store_56 s' s
