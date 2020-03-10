module Hacl.Spec.Bignum.Convert

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Spec.Bignum.Definitions


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_from_bytes_be_f: len:size_nat{8 * len <= max_size_t} -> lseq uint8 (8 * len) -> i:nat{i < len} -> uint64
let bn_from_bytes_be_f len b i =
  uint_from_bytes_be (sub b ((len - i - 1) * 8) 8)


val bn_from_bytes_be_: len:size_nat{8 * len <= max_size_t} -> lseq uint8 (8 * len) -> lbignum len
let bn_from_bytes_be_ len b = createi len (bn_from_bytes_be_f len b)


val bn_from_bytes_be: len:size_pos{8 * blocks len 8 <= max_size_t} -> lseq uint8 len -> lbignum (blocks len 8)
let bn_from_bytes_be len b =
  let bnLen = blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp (tmpLen - len) len b in
  bn_from_bytes_be_ bnLen tmp


val bn_to_bytes_be_f: len:size_nat{8 * len <= max_size_t} -> lbignum len -> i:nat{i < len} -> unit -> unit & lseq uint8 8
let bn_to_bytes_be_f len b i () =
  (), uint_to_bytes_be b.[len - i - 1]


val bn_to_bytes_be_: len:size_nat{8 * len <= max_size_t} -> lbignum len -> lseq uint8 (8 * len)
let bn_to_bytes_be_ len b =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks 8 len len a_spec
    (bn_to_bytes_be_f len b) () in
  o


val bn_to_bytes_be: len:size_pos{8 * blocks len 8 <= max_size_t} -> lbignum (blocks len 8) -> lseq uint8 len
let bn_to_bytes_be len b =
  let bnLen = blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = bn_to_bytes_be_ bnLen b in
  sub tmp (tmpLen - len) len

///
///  Lemmas
///

val reverse: #len:size_nat -> b:lseq uint64 len -> lseq uint64 len
let reverse #len b = createi len (fun i -> b.[len - i - 1])

val twice_reverse: #len:size_nat -> b:lseq uint64 len -> Lemma (reverse (reverse b) == b)
let twice_reverse #len b =
  let lemma_aux (i:nat{i < len}) : Lemma ((reverse (reverse b)).[i] == b.[i]) = () in
  Classical.forall_intro lemma_aux;
  eq_intro (reverse (reverse b)) b

val reverse_slice1: #len:size_pos -> b:lseq uint64 len -> Lemma
  (slice (reverse b) 1 len == reverse (slice b 0 (len - 1)))
let reverse_slice1 #len b =
  let lemma_aux (i:nat{i < len - 1}) : Lemma ((slice (reverse b) 1 len).[i] == (reverse (slice b 0 (len - 1))).[i]) =
    () in
  Classical.forall_intro lemma_aux;
  eq_intro (slice (reverse b) 1 len) (reverse (slice b 0 (len - 1)))


val bn_from_bytes_be_is_uints_from_bytes_be_reverse: len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (bn_from_bytes_be_ len b == reverse (uints_from_bytes_be b))
let bn_from_bytes_be_is_uints_from_bytes_be_reverse len b =
  let lemma_aux (i:nat{i < len}) : Lemma ((bn_from_bytes_be_ len b).[i] == (reverse #len (uints_from_bytes_be b)).[i]) =
    index_uints_from_bytes_be #U64 #SEC #len b (len - i - 1) in
  Classical.forall_intro lemma_aux;
  eq_intro (bn_from_bytes_be_ len b) (reverse (uints_from_bytes_be b))


val bn_v_is_nat_from_intseq_le_lemma: len:size_nat -> b:lseq uint64 len -> Lemma (bn_v b == nat_from_intseq_be (reverse b))
let rec bn_v_is_nat_from_intseq_le_lemma len b =
  if len = 0 then bn_eval0 b
  else begin
    let b1 = slice b 0 (len - 1) in
    bn_v_is_nat_from_intseq_le_lemma (len - 1) b1;
    assert (bn_v b1 == nat_from_intseq_be (reverse b1));

    bn_eval_split_i #len b (len - 1);
    //assert (bn_v b == bn_v b1 + pow2 (64 * (len - 1)) * bn_v (slice b (len - 1) len));
    bn_eval_unfold_i #1 (slice b (len - 1) len) 1;
    bn_eval0 #1 (slice b (len - 1) len);
    assert (bn_v (slice b (len - 1) len) == v b.[len - 1]);
    assert (bn_v b == nat_from_intseq_be (reverse b1) + pow2 (64 * (len - 1)) * v b.[len - 1]);

    nat_from_intseq_be_slice_lemma (reverse b) 1;
    //assert (nat_from_intseq_be (reverse b) == nat_from_intseq_be (slice (reverse b) 1 len) + pow2 ((len - 1) * 64) * nat_from_intseq_be (slice (reverse b) 0 1));
    reverse_slice1 #len b;
    //assert (slice (reverse b) 1 len == reverse (slice b 0 (len - 1)));
    //assert (nat_from_intseq_be (reverse b) == nat_from_intseq_be (reverse b1) + pow2 ((len - 1) * 64) * nat_from_intseq_be (slice (reverse b) 0 1));
    assert ((reverse b).[0] == b.[len - 1]);
    nat_from_intseq_be_lemma0 (slice (reverse b) 0 1);
    assert (nat_from_intseq_be (slice (reverse b) 0 1) == v b.[len - 1]);
    assert  (bn_v b == nat_from_intseq_be (reverse b));
    () end


val bn_from_bytes_be_lemma_: len:size_nat{8 * len <= max_size_t} -> b:lseq uint8 (8 * len) -> Lemma
  (bn_v (bn_from_bytes_be_ len b) == nat_from_bytes_be b)
let bn_from_bytes_be_lemma_ len b =
  bn_v_is_nat_from_intseq_le_lemma len (bn_from_bytes_be_ len b);
  bn_from_bytes_be_is_uints_from_bytes_be_reverse len b;
  twice_reverse (uints_from_bytes_be #U64 #SEC #len b);
  assert (bn_v (bn_from_bytes_be_ len b) == nat_from_intseq_be (uints_from_bytes_be #U64 #SEC #len b));
  assume (nat_from_intseq_be (uints_from_bytes_be #U64 #SEC #len b) == nat_from_bytes_be b)
  //the uints_from_bytes_be_nat_lemma b lemma from master

val lemma_nat_from_bytes_be_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_be b == 0)

let rec lemma_nat_from_bytes_be_zeroes len b =
  if len = 0 then ()
  else begin
    nat_from_intseq_be_slice_lemma #U8 #SEC #len b 1;
    nat_from_intseq_be_lemma0 (slice b 0 1);
    lemma_nat_from_bytes_be_zeroes (len-1) (slice b 1 len) end


val nat_from_bytes_be_eq_lemma: len0:size_nat -> len:size_nat{len0 <= len} -> b:lseq uint8 len0 -> Lemma
 (let tmp = create len (u8 0) in
  nat_from_intseq_be b == nat_from_intseq_be (update_sub tmp (len - len0) len0 b))

let nat_from_bytes_be_eq_lemma len0 len b =
  let tmp = create len (u8 0) in
  let r = update_sub tmp (len - len0) len0 b in
  assert (slice r (len - len0) len == b);
  assert (forall (i:nat). i < len - len0 ==> r.[i] == u8 0);
  nat_from_intseq_be_slice_lemma #U8 #SEC #len r (len - len0);
  assert (nat_from_intseq_be r == nat_from_intseq_be (slice r (len - len0) len) + pow2 (len0 * 8) * nat_from_intseq_be (Seq.slice r 0 (len - len0)));
  assert (nat_from_intseq_be r == nat_from_intseq_be b + pow2 (len0 * 8) * nat_from_intseq_be (Seq.slice r 0 (len - len0)));
  lemma_nat_from_bytes_be_zeroes (len - len0) (Seq.slice r 0 (len - len0))


val bn_from_bytes_be_lemma: len:size_pos{8 * blocks len 8 <= max_size_t} -> b:lseq uint8 len -> Lemma
  (bn_v (bn_from_bytes_be len b) == nat_from_bytes_be b)
let bn_from_bytes_be_lemma len b =
  let bnLen = blocks len 8 in
  let tmpLen = 8 * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp (tmpLen - len) len b in
  let res = bn_from_bytes_be_ bnLen tmp in
  bn_from_bytes_be_lemma_ bnLen tmp;
  assert (bn_v (bn_from_bytes_be_ bnLen tmp) == nat_from_bytes_be tmp);
  nat_from_bytes_be_eq_lemma len tmpLen b


val bn_to_bytes_be_lemma: len:size_pos{8 * blocks len 8 <= max_size_t} -> b:lbignum (blocks len 8){bn_v b < pow2 (8 * len)} -> Lemma
  (bn_to_bytes_be len b == nat_to_bytes_be len (bn_v b))
let bn_to_bytes_be_lemma len b = admit()
