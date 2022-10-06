module Hacl.SHA2.Vec128

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.IntTypes
open Lib.NTuple
open Lib.Buffer
open Lib.MultiBuffer

open Spec.Hash.Definitions
open Hacl.Spec.SHA2.Vec
open Hacl.Impl.SHA2.Generic

module ST = FStar.HyperStack.ST
module Spec = Spec.Agile.Hash
module SpecVec = Hacl.Spec.SHA2.Vec


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"

[@CInline]
private
val sha224_update4: update_vec_t SHA2_224 M128
let sha224_update4 block hash = update #SHA2_224 #M128 block hash


val sha224_4 (dst0 dst1 dst2 dst3: lbuffer uint8 28ul) (input_len:size_t) (input0 input1 input2 input3: lbuffer uint8 input_len) :
  Stack unit
  (requires fun h0 -> v input_len `less_than_max_input_length` SHA2_224 /\
    live4 h0 input0 input1 input2 input3 /\
    live4 h0 dst0 dst1 dst2 dst3 /\
    internally_disjoint4 dst0 dst1 dst2 dst3)
  (ensures  fun h0 _ h1 -> modifies (loc dst0 |+| loc dst1 |+| loc dst2 |+| loc dst3) h0 h1 /\
    as_seq h1 dst0 == Spec.hash SHA2_224 (as_seq h0 input0) /\
    as_seq h1 dst1 == Spec.hash SHA2_224 (as_seq h0 input1) /\
    as_seq h1 dst2 == Spec.hash SHA2_224 (as_seq h0 input2) /\
    as_seq h1 dst3 == Spec.hash SHA2_224 (as_seq h0 input3))

let sha224_4 dst0 dst1 dst2 dst3 input_len input0 input1 input2 input3 =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (dst0,(dst1,(dst2,dst3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  loc_multi4 rb;
  hash #SHA2_224 #M128 sha224_update4 rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_224 #M128 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 dst1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 dst2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 dst3)


[@CInline]
private
val sha256_update4: update_vec_t SHA2_256 M128
let sha256_update4 block hash = update #SHA2_256 #M128 block hash


val sha256_4 (dst0 dst1 dst2 dst3: lbuffer uint8 32ul) (input_len:size_t) (input0 input1 input2 input3: lbuffer uint8 input_len) :
  Stack unit
  (requires fun h0 -> v input_len `less_than_max_input_length` SHA2_256 /\
    live4 h0 input0 input1 input2 input3 /\
    live4 h0 dst0 dst1 dst2 dst3 /\
    internally_disjoint4 dst0 dst1 dst2 dst3)
  (ensures  fun h0 _ h1 -> modifies (loc dst0 |+| loc dst1 |+| loc dst2 |+| loc dst3) h0 h1 /\
    as_seq h1 dst0 == Spec.hash SHA2_256 (as_seq h0 input0) /\
    as_seq h1 dst1 == Spec.hash SHA2_256 (as_seq h0 input1) /\
    as_seq h1 dst2 == Spec.hash SHA2_256 (as_seq h0 input2) /\
    as_seq h1 dst3 == Spec.hash SHA2_256 (as_seq h0 input3))

let sha256_4 dst0 dst1 dst2 dst3 input_len input0 input1 input2 input3 =
  let ib = ntup4 (input0,(input1,(input2,input3))) in
  let rb = ntup4 (dst0,(dst1,(dst2,dst3))) in
  let h0 = ST.get() in
  assert (live_multi h0 ib);
  assert (live_multi h0 rb);
  assert (internally_disjoint rb);
  loc_multi4 rb;
  hash #SHA2_256 #M128 sha256_update4 rb input_len ib;
  let h1 = ST.get() in
  Hacl.Spec.SHA2.Equiv.hash_agile_lemma #SHA2_256 #M128 (v input_len) (as_seq_multi h0 ib);
  assert ((as_seq_multi h1 rb).(|0|) == as_seq h1 dst0);
  assert ((as_seq_multi h1 rb).(|1|) == as_seq h1 dst1);
  assert ((as_seq_multi h1 rb).(|2|) == as_seq h1 dst2);
  assert ((as_seq_multi h1 rb).(|3|) == as_seq h1 dst3)
