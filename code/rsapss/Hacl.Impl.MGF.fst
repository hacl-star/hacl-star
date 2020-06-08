module Hacl.Impl.MGF

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Mul

open Lib.IntTypes
open Lib.Buffer

open Hacl.Bignum.Definitions

module ST = FStar.HyperStack.ST
module S = Spec.RSAPSS
module BSeq = Lib.ByteSequence
module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(* SHA 256 *)
inline_for_extraction
let hLen = 32ul

val hash_sha256:
    mHash:lbuffer uint8 hLen
  -> msgLen:size_t{v msgLen <= S.max_input}
  -> msg:lbuffer uint8 msgLen ->
  Stack unit
  (requires fun h -> live h mHash /\ live h msg /\ disjoint msg mHash)
  (ensures  fun h0 _ h1 -> modifies (loc mHash) h0 h1 /\
    as_seq h1 mHash == S.sha2_256 (as_seq h0 msg))
let hash_sha256 mHash msgLen msg =
  Hacl.Hash.SHA2.hash_256 msg msgLen mHash

(* Mask Generation Function *)
inline_for_extraction noextract
val counter_to_bytes:
    i:size_t
  -> counter:lbuffer uint8 4ul ->
  Stack unit
  (requires fun h -> live h counter)
  (ensures  fun h0 _ h1 -> modifies (loc counter) h0 h1 /\
    as_seq h1 counter == BSeq.nat_to_intseq_be 4 (v i))

let counter_to_bytes i c =
  let h0 = ST.get () in
  c.(0ul) <- to_u8 (i >>. 24ul);
  c.(1ul) <- to_u8 (i >>. 16ul);
  c.(2ul) <- to_u8 (i >>. 8ul);
  c.(3ul) <- to_u8 i;
  let h1 = ST.get () in
  BSeq.index_nat_to_intseq_be #U8 #SEC 4 (v i) 0;
  BSeq.index_nat_to_intseq_be #U8 #SEC 4 (v i) 1;
  BSeq.index_nat_to_intseq_be #U8 #SEC 4 (v i) 2;
  BSeq.index_nat_to_intseq_be #U8 #SEC 4 (v i) 3;
  LSeq.eq_intro (as_seq h1 c) (BSeq.nat_to_intseq_be 4 (v i))


inline_for_extraction noextract
val mgf_sha256_f:
    len:size_t{v len + 4 <= max_size_t /\ v len + 4 <= S.max_input}
  -> i:size_t
  -> mgfseed_counter:lbuffer uint8 (len +! 4ul)
  -> block:lbuffer uint8 hLen ->
  Stack unit
  (requires fun h -> live h mgfseed_counter /\ live h block /\ disjoint mgfseed_counter block)
  (ensures  fun h0 _ h1 -> modifies (loc mgfseed_counter |+| loc block) h0 h1 /\
    (as_seq h1 mgfseed_counter, as_seq h1 block) == S.mgf_sha256_f (v len) (v i) (as_seq h0 mgfseed_counter))

let mgf_sha256_f len i mgfseed_counter block =
  let h0 = ST.get () in
  update_sub_f h0 mgfseed_counter len 4ul
    (fun h -> BSeq.nat_to_intseq_be 4 (v i))
    (fun _ -> counter_to_bytes i (sub mgfseed_counter len 4ul));
  hash_sha256 block (len +! 4ul) mgfseed_counter


val mgf_sha256:
    len:size_t{v len + 4 <= max_size_t /\ v len + 4 <= S.max_input}
  -> mgfseed:lbuffer uint8 len
  -> maskLen:size_t{0 < v maskLen /\ v (blocks maskLen hLen) * v hLen < pow2 32}
  -> res:lbuffer uint8 maskLen ->
  Stack unit
  (requires fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.mgf_sha256 #(v len) (as_seq h0 mgfseed) (v maskLen))

[@CInline]
let mgf_sha256 len mgfseed maskLen res =
  push_frame ();
  let mgfseed_counter = create (len +! 4ul) (u8 0) in
  update_sub mgfseed_counter 0ul len mgfseed;

  let n = blocks maskLen hLen in
  let accLen = n *! hLen in
  let acc = create accLen (u8 0) in
  [@ inline_let]
  let a_spec = S.mgf_sha256_a (v len) (v n) in
  let h0 = ST.get () in
  fill_blocks h0 hLen n acc a_spec
    (fun h i -> as_seq h mgfseed_counter)
    (fun _ -> loc mgfseed_counter)
    (fun h0 -> S.mgf_sha256_f (v len))
    (fun i -> mgf_sha256_f len i mgfseed_counter (sub acc (i *! hLen) hLen));
  copy res (sub acc 0ul maskLen);
  pop_frame ()
