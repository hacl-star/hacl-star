module Hacl.Impl.RSAPSS.MGF

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

module Hash = Spec.Agile.Hash

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val hash_len: a:Hash.algorithm{S.hash_is_supported a} -> Tot (res:size_t{v res == Hash.hash_length a})
[@CInline]
let hash_len a =
  Hacl.Hash.Definitions.hash_len a


val hash:
    a:Hash.algorithm{S.hash_is_supported a}
  -> mHash:lbuffer uint8 (hash_len a)
  -> msgLen:size_t{v msgLen <= Hash.max_input_length a}
  -> msg:lbuffer uint8 msgLen ->
  Stack unit
  (requires fun h -> live h mHash /\ live h msg /\ disjoint msg mHash)
  (ensures  fun h0 _ h1 -> modifies (loc mHash) h0 h1 /\
    as_seq h1 mHash == Hash.hash a (as_seq h0 msg))

[@CInline]
let hash a mHash msgLen msg =
  match a with
  | Hash.SHA2_256 -> Hacl.Hash.SHA2.hash_256 msg msgLen mHash
  | Hash.SHA2_384 -> Hacl.Hash.SHA2.hash_384 msg msgLen mHash
  | Hash.SHA2_512 -> Hacl.Hash.SHA2.hash_512 msg msgLen mHash


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
val mgf_hash_f:
    a:Hash.algorithm{S.hash_is_supported a}
  -> len:size_t{v len + 4 <= max_size_t /\ v len + 4 <= Hash.max_input_length a}
  -> i:size_t
  -> mgfseed_counter:lbuffer uint8 (len +! 4ul)
  -> block:lbuffer uint8 (hash_len a) ->
  Stack unit
  (requires fun h -> live h mgfseed_counter /\ live h block /\ disjoint mgfseed_counter block)
  (ensures  fun h0 _ h1 -> modifies (loc mgfseed_counter |+| loc block) h0 h1 /\
    (as_seq h1 mgfseed_counter, as_seq h1 block) == S.mgf_hash_f a (v len) (v i) (as_seq h0 mgfseed_counter))

let mgf_hash_f a len i mgfseed_counter block =
  let h0 = ST.get () in
  update_sub_f h0 mgfseed_counter len 4ul
    (fun h -> BSeq.nat_to_intseq_be 4 (v i))
    (fun _ -> counter_to_bytes i (sub mgfseed_counter len 4ul));
  hash a block (len +! 4ul) mgfseed_counter


inline_for_extraction noextract
let mgf_hash_st (a:Hash.algorithm{S.hash_is_supported a}) =
  len:size_t{v len + 4 <= max_size_t /\ v len + 4 <= Hash.max_input_length a}
  -> mgfseed:lbuffer uint8 len
  -> maskLen:size_t{0 < v maskLen /\ S.blocks (v maskLen) (Hash.hash_length a) * Hash.hash_length a < pow2 32}
  -> res:lbuffer uint8 maskLen ->
  Stack unit
  (requires fun h -> live h mgfseed /\ live h res /\ disjoint res mgfseed)
  (ensures  fun h0 _ h1 -> modifies (loc res) h0 h1 /\
    as_seq h1 res == S.mgf_hash a (v len) (as_seq h0 mgfseed) (v maskLen))

val mgf_hash: a:Hash.algorithm{S.hash_is_supported a} -> mgf_hash_st a
[@CInline]
let mgf_hash a len mgfseed maskLen res =
  push_frame ();
  let mgfseed_counter = create (len +! 4ul) (u8 0) in
  update_sub mgfseed_counter 0ul len mgfseed;

  let hLen = hash_len a in
  let n = blocks maskLen hLen in
  let accLen = n *! hLen in
  let acc = create accLen (u8 0) in
  [@ inline_let]
  let a_spec = S.mgf_hash_a (v len) (v n) in
  let h0 = ST.get () in
  fill_blocks h0 hLen n acc a_spec
    (fun h i -> as_seq h mgfseed_counter)
    (fun _ -> loc mgfseed_counter)
    (fun h0 -> S.mgf_hash_f a (v len))
    (fun i -> mgf_hash_f a len i mgfseed_counter (sub acc (i *! hLen) hLen));
  copy res (sub acc 0ul maskLen);
  pop_frame ()
