module Hacl.HPKE.Interface.DH

open FStar.HyperStack
open FStar.HyperStack.All
module HST = FStar.HyperStack.ST

open Lib.Buffer
open Lib.IntTypes
open Lib.ByteBuffer

module DH = Spec.Agile.DH
module S = Spec.Agile.HPKE

#set-options "--z3rlimit 20 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

unfold noextract
let nsize_key (a:DH.algorithm) =
  match a with
  | DH.DH_Curve25519 -> 32ul
  | DH.DH_P256 -> 32ul

unfold noextract
let nsize_public (a:DH.algorithm) =
  match a with
  | DH.DH_Curve25519 -> 32ul
  | DH.DH_P256 -> 64ul

inline_for_extraction noextract
let dh_st (a:DH.algorithm) (p:Type0) =
     o:lbuffer uint8 (nsize_public a)
  -> k:lbuffer uint8 (nsize_key a)
  -> i:lbuffer uint8 (nsize_public a)
  -> Stack UInt32.t
     (requires fun h0 ->
       p /\
       live h0 o /\ live h0 k /\ live h0 i /\
       disjoint o i /\ disjoint o k)
     (ensures fun h0 result h1 -> modifies (loc o) h0 h1 /\ (
       let output = DH.dh a (as_seq h0 k) (as_seq h0 i) in
       match result with
       | 0ul -> Some? output /\ as_seq h1 o `Seq.equal` Some?.v output // DH succeeded
       | 1ul -> None? output
       | _ -> False))

inline_for_extraction noextract
let secret_to_public_st (a: DH.algorithm) (p:Type0) =
    o:lbuffer uint8 (nsize_public a)
  -> i:lbuffer uint8 (nsize_key a)
  -> Stack UInt32.t
    (requires fun h0 ->
      p /\
      live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 result h1 -> modifies (loc o) h0 h1 /\
      (let output = DH.secret_to_public a (as_seq h0 i) in
      match result with
      | 0ul -> Some? output /\ as_seq h1 o `Seq.equal` Some?.v output
      | 1ul -> None? output
      | _ -> False))

[@ Meta.Attribute.specialize]
assume val dh: #a:S.ciphersuite -> dh_st (S.curve_of_cs a) True

[@ Meta.Attribute.specialize]
assume val secret_to_public: #a:S.ciphersuite -> secret_to_public_st (S.curve_of_cs a) True

(** Instantiations for Curve25519 **)

inline_for_extraction noextract
let secret_to_public_c51 : secret_to_public_st (DH.DH_Curve25519) True = fun o i ->
  Hacl.Curve25519_51.secret_to_public o i;
  0ul
inline_for_extraction noextract
let dh_c51 : dh_st (DH.DH_Curve25519) True = fun o k i ->
  push_frame();
  let zeros = create 32ul (u8 0) in
  Hacl.Curve25519_51.scalarmult o k i;
  let res = if lbytes_eq o zeros then 1ul else 0ul in
  pop_frame();
  res

let vale_p = Vale.X64.CPU_Features_s.(adx_enabled /\ bmi2_enabled)

inline_for_extraction noextract
let secret_to_public_c64 : secret_to_public_st (DH.DH_Curve25519) vale_p = fun o i ->
  Hacl.Curve25519_64.secret_to_public o i;
  0ul
inline_for_extraction noextract
let dh_c64 : dh_st (DH.DH_Curve25519) vale_p = fun o k i ->
  push_frame();
  let zeros = create 32ul (u8 0) in
  Hacl.Curve25519_64.scalarmult o k i;
  let res = if lbytes_eq o zeros then 1ul else 0ul in
  pop_frame();
  res

// TODO: After unification of error codes, this should be removed
inline_for_extraction noextract
let change_error_code (r:uint64) : Pure UInt32.t
  (requires v r = 0 \/ v r = pow2 64 - 1)
  (ensures fun r' -> UInt32.v r' <= 1 /\ (UInt32.v r' = 0 <==> v r = 0))
  = let r' = logand r (u64 1) in
    logand_mask r (u64 1) 1;
    let r' = cast U32 SEC r' in
    Lib.RawIntTypes.u32_to_UInt32 r'

inline_for_extraction noextract
let secret_to_public_p256 : secret_to_public_st (DH.DH_P256) True = fun o i ->
  let res = Hacl.Impl.P256.DH.ecp256dh_i o i in
  change_error_code res

let rec nat_from_bytes_le_zero_is_zero (n:size_nat{n >= 1}) (s:Lib.ByteSequence.lbytes n)
  : Lemma (requires s `Seq.equal` Lib.Sequence.create n (u8 0))
          (ensures Lib.ByteSequence.nat_from_bytes_le s == 0)
  = let open Lib.Sequence in
    let open Lib.ByteSequence in
    if n = 1 then nat_from_intseq_le_lemma0 s
    else (
      nat_from_intseq_le_slice_lemma s 1;
      nat_from_bytes_le_zero_is_zero (n-1) (slice s 1 n);
      nat_from_intseq_le_lemma0 (slice s 0 1)
   )

inline_for_extraction noextract
let dh_p256 : dh_st (DH.DH_P256) True = fun o k i ->
  push_frame();
  let tmp = create (size 64) (u8 0) in
  (**) let h0 = HyperStack.ST.get() in
  (**) nat_from_bytes_le_zero_is_zero 32 (as_seq h0 (gsub tmp (size 0) (size 32)));
  (**) nat_from_bytes_le_zero_is_zero 32 (as_seq h0 (gsub tmp (size 32) (size 32)));
  let res = Hacl.Impl.P256.DH.ecp256dh_r tmp i k in
  copy o tmp;
  pop_frame();
  change_error_code res
