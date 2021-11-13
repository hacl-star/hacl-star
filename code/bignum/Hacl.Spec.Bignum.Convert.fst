module Hacl.Spec.Bignum.Convert

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open Hacl.Spec.Bignum.Definitions


#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

val bn_from_uint: #t:limb_t -> len:size_pos -> x:limb t -> lbignum t len
let bn_from_uint #t len x =
  let b = create len (uint #t 0) in
  b.[0] <- x

val bn_from_uint_lemma: #t:limb_t -> len:size_pos -> x:limb t ->
  Lemma (bn_v (bn_from_uint len x) == uint_v x)

let bn_from_uint_lemma #t len x =
  let b = create len (uint #t 0) in
  let b = b.[0] <- x in
  bn_eval_split_i b 1;
  assert (bn_v b == bn_v (slice b 0 1) + pow2 (bits t) * bn_v (slice b 1 len));
  eq_intro (slice b 1 len) (create (len - 1) (uint #t 0));
  bn_eval_zeroes #t (len - 1) (len - 1);
  assert (bn_v b == bn_v (slice b 0 1));
  bn_eval1 (slice b 0 1)


val bn_from_bytes_be_f:
    #t:limb_t
  -> len:size_nat{numbytes t * len <= max_size_t}
  -> lseq uint8 (numbytes t * len)
  -> i:nat{i < len} ->
  limb t

let bn_from_bytes_be_f #t len b i =
  uint_from_bytes_be (sub b ((len - i - 1) * numbytes t) (numbytes t))


val bn_from_bytes_be_:
    #t:limb_t
  -> len:size_nat{numbytes t * len <= max_size_t}
  -> lseq uint8 (numbytes t * len) ->
  lbignum t len

let bn_from_bytes_be_ #t len b =
  createi len (bn_from_bytes_be_f len b)


val bn_from_bytes_be:
    #t:limb_t
  -> len:size_pos{numbytes t * blocks len (numbytes t) <= max_size_t}
  -> lseq uint8 len ->
  lbignum t (blocks len (numbytes t))

let bn_from_bytes_be #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp (tmpLen - len) len b in
  bn_from_bytes_be_ bnLen tmp


val bn_from_bytes_le:
    #t:limb_t
  -> len:size_pos{numbytes t * blocks len (numbytes t) <= max_size_t}
  -> lseq uint8 len ->
  lbignum t (blocks len (numbytes t))

let bn_from_bytes_le #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp 0 len b in
  uints_from_bytes_le tmp


val bn_to_bytes_be_f:
    #t:limb_t
  -> len:size_nat
  -> lbignum t len
  -> i:nat{i < len}
  -> unit ->
  unit & lseq uint8 (numbytes t)

let bn_to_bytes_be_f #t len b i () =
  (), uint_to_bytes_be b.[len - i - 1]


val bn_to_bytes_be_:
    #t:limb_t
  -> len:size_nat{numbytes t * len <= max_size_t}
  -> lbignum t len ->
  lseq uint8 (numbytes t * len)

let bn_to_bytes_be_ #t len b =
  let a_spec (i:nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes t) len len a_spec
    (bn_to_bytes_be_f len b) () in
  o


val bn_to_bytes_be:
    #t:limb_t
  -> len:size_pos{numbytes t * blocks len (numbytes t) <= max_size_t}
  -> lbignum t (blocks len (numbytes t)) ->
  lseq uint8 len

let bn_to_bytes_be #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = bn_to_bytes_be_ bnLen b in
  sub tmp (tmpLen - len) len


val bn_to_bytes_le:
    #t:limb_t
  -> len:size_pos{numbytes t * blocks len (numbytes t) <= max_size_t}
  -> lbignum t (blocks len (numbytes t)) ->
  lseq uint8 len

let bn_to_bytes_le #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = uints_to_bytes_le b in
  sub tmp 0 len

///
///  Lemmas
///

val reverse: #t:limb_t -> #len:size_nat -> b:lbignum t len -> lbignum t len
let reverse #t #len b = createi len (fun i -> b.[len - i - 1])


val twice_reverse: #t:limb_t -> #len:size_nat -> b:lbignum t len -> Lemma (reverse (reverse b) == b)
let twice_reverse #t #len b =
  let lemma_aux (i:nat{i < len}) : Lemma ((reverse (reverse b)).[i] == b.[i]) = () in

  Classical.forall_intro lemma_aux;
  eq_intro (reverse (reverse b)) b


val reverse_slice1: #t:limb_t -> #len:size_pos -> b:lbignum t len ->
  Lemma (slice (reverse b) 1 len == reverse (slice b 0 (len - 1)))
let reverse_slice1 #t #len b =
  let lemma_aux (i:nat{i < len - 1}) :
    Lemma ((slice (reverse b) 1 len).[i] == (reverse (slice b 0 (len - 1))).[i]) = () in

  Classical.forall_intro lemma_aux;
  eq_intro (slice (reverse b) 1 len) (reverse (slice b 0 (len - 1)))


val bn_from_bytes_be_is_uints_from_bytes_be_reverse:
    #t:limb_t
  -> len:size_nat{numbytes t * len <= max_size_t}
  -> b:lseq uint8 (numbytes t * len) ->
  Lemma (bn_from_bytes_be_ len b == reverse (uints_from_bytes_be b))

let bn_from_bytes_be_is_uints_from_bytes_be_reverse #t len b =
  let lemma_aux (i:nat{i < len}) :
    Lemma ((bn_from_bytes_be_ len b).[i] == (reverse #t #len (uints_from_bytes_be b)).[i])
  =
    index_uints_from_bytes_be #t #SEC #len b (len - i - 1) in

  Classical.forall_intro lemma_aux;
  eq_intro (bn_from_bytes_be_ len b) (reverse (uints_from_bytes_be b))


val bn_v_is_nat_from_intseq_be_lemma: #t:limb_t -> len:size_nat -> b:lbignum t len ->
  Lemma (bn_v b == nat_from_intseq_be (reverse b))

let rec bn_v_is_nat_from_intseq_be_lemma #t len b =
  if len = 0 then bn_eval0 b
  else begin
    let b1 = slice b 0 (len - 1) in
    bn_v_is_nat_from_intseq_be_lemma (len - 1) b1;
    assert (bn_v b1 == nat_from_intseq_be (reverse b1));

    bn_eval_split_i #t #len b (len - 1);
    bn_eval_unfold_i #t #1 (slice b (len - 1) len) 1;
    bn_eval0 #t #1 (slice b (len - 1) len);
    assert (bn_v (slice b (len - 1) len) == v b.[len - 1]);
    assert (bn_v b == nat_from_intseq_be (reverse b1) + pow2 (bits t * (len - 1)) * v b.[len - 1]);

    nat_from_intseq_be_slice_lemma (reverse b) 1;
    reverse_slice1 #t #len b;
    assert ((reverse b).[0] == b.[len - 1]);
    nat_from_intseq_be_lemma0 (slice (reverse b) 0 1);
    assert (nat_from_intseq_be (slice (reverse b) 0 1) == v b.[len - 1]);
    assert  (bn_v b == nat_from_intseq_be (reverse b));
    () end


val bn_from_bytes_be_lemma_:
    #t:limb_t
  -> len:size_nat{numbytes t * len <= max_size_t}
  -> b:lseq uint8 (numbytes t * len) ->
  Lemma (bn_v (bn_from_bytes_be_ len b) == nat_from_bytes_be b)

let bn_from_bytes_be_lemma_ #t len b =
  bn_v_is_nat_from_intseq_be_lemma len (bn_from_bytes_be_ len b);
  bn_from_bytes_be_is_uints_from_bytes_be_reverse len b;
  twice_reverse (uints_from_bytes_be #t #SEC #len b);
  assert (bn_v (bn_from_bytes_be_ len b) == nat_from_intseq_be (uints_from_bytes_be #t #SEC #len b));
  uints_from_bytes_be_nat_lemma #t #SEC #len b;
  assert (nat_from_intseq_be (uints_from_bytes_be #t #SEC #len b) == nat_from_bytes_be b)


val lemma_nat_from_bytes_be_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_be b == 0)

let rec lemma_nat_from_bytes_be_zeroes len b =
  if len = 0 then ()
  else begin
    nat_from_intseq_be_slice_lemma #U8 #SEC #len b 1;
    nat_from_intseq_be_lemma0 (slice b 0 1);
    lemma_nat_from_bytes_be_zeroes (len-1) (slice b 1 len) end


val nat_from_bytes_be_eq_lemma: len0:size_nat -> len:size_nat{len0 <= len} -> b:lseq uint8 len0 ->
  Lemma (let tmp = create len (u8 0) in
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


val bn_from_bytes_be_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * blocks len (numbytes t) <= max_size_t}
  -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_be #t len b) == nat_from_bytes_be b)

let bn_from_bytes_be_lemma #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp (tmpLen - len) len b in
  let res = bn_from_bytes_be_ #t bnLen tmp in
  bn_from_bytes_be_lemma_ #t bnLen tmp;
  assert (bn_v (bn_from_bytes_be_ #t bnLen tmp) == nat_from_bytes_be tmp);
  nat_from_bytes_be_eq_lemma len tmpLen b


val index_bn_to_bytes_be_:
    #t:limb_t
  -> len:size_nat{numbytes t * len <= max_size_t}
  -> b:lbignum t len
  -> i:nat{i < numbytes t * len} ->
  Lemma (let numb = numbytes t in
    (bn_to_bytes_be_ #t len b).[i] ==
    uint #U8 #SEC (v b.[len - i / numb - 1] / pow2 (8 * (numb - 1 - i % numb)) % pow2 8))

let index_bn_to_bytes_be_ #t len b i =
  let numb = numbytes t in
  let bi = b.[len - i / numb - 1] in
  index_generate_blocks (numb) len len (bn_to_bytes_be_f len b) i;
  assert ((bn_to_bytes_be_ #t len b).[i] == (uint_to_bytes_be bi).[i % numb]);
  index_uint_to_bytes_be bi;
  assert ((uint_to_bytes_be bi).[i % numb] == uint #U8 #SEC (v bi / pow2 (8 * (numb - 1 - i % numb)) % pow2 8))


val bn_to_bytes_be_lemma_aux:
    #t:limb_t
  -> len:size_pos{numbytes t * len <= max_size_t}
  -> b:lbignum t len{bn_v b < pow2 (bits t * len)}
  -> i:nat{i < numbytes t * len} ->
  Lemma (let numb = numbytes t in
    bn_v b / pow2 (8 * (numb * len - i - 1)) % pow2 8 ==
    v b.[len - i / numb - 1] / pow2 (8 * (numb - 1 - i % numb)) % pow2 8)

let bn_to_bytes_be_lemma_aux #t len b i =
  let pbits = bits t in
  let numb = numbytes t in
  let e  = numb - 1 - i % numb in
  let e1 = len - i / numb - 1 in
  let e2 = numb * len - 1 - i in

  calc (==) {
    v b.[e1] / pow2 (8 * e) % pow2 8;
    (==) { bn_eval_index b e1 }
    (bn_v b / pow2 (pbits * e1) % pow2 (pbits)) / pow2 (8 * e) % pow2 8;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b) (pbits * e1) (pbits + pbits * e1) }
    (bn_v b % pow2 (pbits + pbits * e1) / pow2 (pbits * e1)) / pow2 (8 * e) % pow2 8;
    (==) { Math.Lemmas.division_multiplication_lemma (bn_v b % pow2 (pbits + pbits * e1)) (pow2 (pbits * e1)) (pow2 (8 * e)) }
    (bn_v b % pow2 (pbits + pbits * e1)) / (pow2 (pbits * e1) * pow2 (8 * e)) % pow2 8;
    (==) { Math.Lemmas.pow2_plus (pbits * e1) (8 * e) }
    (bn_v b % pow2 (pbits + pbits * e1)) / pow2 (pbits * e1 + 8 * e) % pow2 8;
    (==) { Math.Lemmas.pow2_modulo_division_lemma_1 (bn_v b) (8 * e2) (pbits + pbits * e1) }
    (bn_v b / pow2 (8 * e2)) % pow2 (pbits + pbits * e1 - 8 * e2) % pow2 8;
    (==) { Math.Lemmas.pow2_modulo_modulo_lemma_1 (bn_v b / pow2 (8 * e2)) 8 (pbits + pbits * e1 - 8 * e2) }
    (bn_v b / pow2 (8 * (numb * len - i - 1))) % pow2 8;
    }


val bn_to_bytes_be_lemma_:
    #t:limb_t
  -> len:size_pos{numbytes t * len <= max_size_t}
  -> b:lbignum t len{bn_v b < pow2 (bits t * len)} ->
  Lemma (bn_to_bytes_be_ #t len b == nat_to_intseq_be #U8 #SEC (numbytes t * len) (bn_v b))

let bn_to_bytes_be_lemma_ #t len b =
  let numb = numbytes t in

  let lemma_aux (i:nat{i < numb * len}) :
    Lemma ((bn_to_bytes_be_ #t len b).[i] == index #uint8 #(numb * len) (nat_to_intseq_be (numb * len) (bn_v b)) i)
  =
    let rp = nat_to_intseq_be #U8 #SEC (numb * len) (bn_v b) in
    index_nat_to_intseq_be #U8 #SEC (numb * len) (bn_v b) (numb * len - i - 1);
    assert (index #uint8 #(numb * len) rp i == uint #U8 #SEC (bn_v b / pow2 (8 * (numb * len - i - 1)) % pow2 8));
    index_bn_to_bytes_be_ len b i;
    assert ((bn_to_bytes_be_ #t len b).[i] == uint #U8 #SEC (v b.[len - i / numb - 1] / pow2 (8 * (numb - 1 - i % numb)) % pow2 8));
    bn_to_bytes_be_lemma_aux len b i;
    () in

  Classical.forall_intro lemma_aux;
  eq_intro (bn_to_bytes_be_ len b) (nat_to_intseq_be (numb * len) (bn_v b))


val bn_to_bytes_be_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * blocks len (numbytes t) <= max_size_t}
  -> b:lbignum t (blocks len (numbytes t)){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_be #t len b == nat_to_intseq_be #U8 #SEC len (bn_v b))

let bn_to_bytes_be_lemma #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = bn_to_bytes_be_ bnLen b in
  let res = sub tmp (tmpLen - len) len in
  assert (bn_v b < pow2 (8 * len));
  Math.Lemmas.pow2_le_compat (bits t * bnLen) (8 * len);
  assert (bn_v b < pow2 (bits t * bnLen));
  bn_to_bytes_be_lemma_ bnLen b;
  assert (tmp == nat_to_intseq_be #U8 #SEC tmpLen (bn_v b));

  let lemma_aux (i:nat{i < len}) :
    Lemma (index (sub #uint8 #tmpLen (nat_to_intseq_be #U8 #SEC tmpLen (bn_v b)) (tmpLen - len) len) i ==
           index #uint8 #len (nat_to_intseq_be #U8 #SEC len (bn_v b)) i) =
    let rp = nat_to_intseq_be #U8 #SEC len (bn_v b) in
    index_nat_to_intseq_be #U8 #SEC len (bn_v b) (len - i - 1);
    assert (index #uint8 #len rp i == uint #U8 #SEC (bn_v b / pow2 (8 * (len - i - 1)) % pow2 8));
    let lp = nat_to_intseq_be #U8 #SEC tmpLen (bn_v b) in
    assert (index (sub #uint8 #tmpLen lp (tmpLen - len) len) i == index #uint8 #tmpLen lp (tmpLen - len + i));
    index_nat_to_intseq_be #U8 #SEC tmpLen (bn_v b) (len - i - 1);
    assert (index #uint8 #tmpLen lp (tmpLen - len + i) == uint #U8 #SEC (bn_v b / pow2 (8 * (len - i - 1)) % pow2 8));
    () in

  Classical.forall_intro lemma_aux;
  eq_intro (nat_to_intseq_be #U8 #SEC len (bn_v b)) res


(* Little-endian *)

val bn_v_is_nat_from_intseq_le_lemma: #t:limb_t -> len:size_nat -> b:lbignum t len ->
  Lemma (bn_v b == nat_from_intseq_le b)

let rec bn_v_is_nat_from_intseq_le_lemma #t len b =
  if len = 0 then
    bn_eval0 b
  else begin
    let b1 = slice b 0 (len - 1) in
    bn_v_is_nat_from_intseq_le_lemma (len - 1) b1;
    assert (bn_v b1 == nat_from_intseq_le b1);

    bn_eval_split_i #t #len b (len - 1);
    bn_eval_unfold_i #t #1 (slice b (len - 1) len) 1;
    bn_eval0 #t #1 (slice b (len - 1) len);
    assert (bn_v b == nat_from_intseq_le b1 + pow2 (bits t * (len - 1)) * v b.[len - 1]);
    nat_from_intseq_le_slice_lemma b (len - 1);
    nat_from_intseq_le_lemma0 (slice b (len - 1) len);
    assert (nat_from_intseq_le b == nat_from_intseq_le b1 + pow2 ((len - 1) * bits t) * v b.[len - 1]) end


val lemma_nat_from_bytes_le_zeroes: len:size_nat -> b:lseq uint8 len -> Lemma
  (requires (forall (i:nat). i < len ==> b.[i] == u8 0))
  (ensures  nat_from_intseq_le b == 0)

let rec lemma_nat_from_bytes_le_zeroes len b =
  if len = 0 then ()
  else begin
    nat_from_intseq_le_slice_lemma #U8 #SEC #len b 1;
    nat_from_intseq_le_lemma0 (slice b 0 1);
    lemma_nat_from_bytes_le_zeroes (len-1) (slice b 1 len) end


val nat_from_bytes_le_eq_lemma: len0:size_nat -> len:size_nat{len0 <= len} -> b:lseq uint8 len0 -> Lemma
 (let tmp = create len (u8 0) in
  nat_from_intseq_le b == nat_from_intseq_le (update_sub tmp 0 len0 b))

let nat_from_bytes_le_eq_lemma len0 len b =
  let tmp = create len (u8 0) in
  let r = update_sub tmp 0 len0 b in
  assert (slice r 0 len0 == b);
  assert (forall (i:nat). i < len - len0 ==> r.[len0 + i] == u8 0);
  nat_from_intseq_le_slice_lemma #U8 #SEC #len r len0;
  assert (nat_from_intseq_le r == nat_from_intseq_le (slice r 0 len0) + pow2 (len0 * 8) * nat_from_intseq_le (Seq.slice r len0 len));
  assert (nat_from_intseq_le r == nat_from_intseq_le b + pow2 (len0 * 8) * nat_from_intseq_le (Seq.slice r len0 len));
  lemma_nat_from_bytes_le_zeroes (len - len0) (Seq.slice r len0 len)


val bn_from_bytes_le_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lseq uint8 len ->
  Lemma (bn_v (bn_from_bytes_le #t len b) == nat_from_bytes_le b)

let bn_from_bytes_le_lemma #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = create tmpLen (u8 0) in
  let tmp = update_sub tmp 0 len b in
  let res = uints_from_bytes_le #t #SEC #bnLen tmp in
  uints_from_bytes_le_nat_lemma #t #SEC #bnLen tmp;
  bn_v_is_nat_from_intseq_le_lemma bnLen res;
  nat_from_bytes_le_eq_lemma len tmpLen b


val bn_to_bytes_le_lemma:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t}
  -> b:lbignum t (blocks len (numbytes t)){bn_v b < pow2 (8 * len)} ->
  Lemma (bn_to_bytes_le len b == nat_to_intseq_le #U8 len (bn_v b))

let bn_to_bytes_le_lemma #t len b =
  let bnLen = blocks len (numbytes t) in
  let tmpLen = numbytes t * bnLen in
  let tmp = uints_to_bytes_le b in
  let res = sub tmp 0 len in
  assert (bn_v b < pow2 (8 * len));
  Math.Lemmas.pow2_le_compat (bits t * bnLen) (8 * len);
  assert (bn_v b < pow2 (bits t * bnLen));

  uints_to_bytes_le_nat_lemma #t #SEC bnLen (bn_v b);
  bn_v_is_nat_from_intseq_le_lemma bnLen b;
  lemma_nat_from_to_intseq_le_preserves_value bnLen b;
  assert (uints_to_bytes_le #t #SEC #bnLen b == nat_to_intseq_le #U8 tmpLen (bn_v b));

  let aux (i:nat{i < len}) :
    Lemma (index #uint8 #tmpLen (nat_to_intseq_le #U8 tmpLen (bn_v b)) i ==
           index #uint8 #len (nat_to_intseq_le #U8 len (bn_v b)) i) =
    index_nat_to_intseq_le #U8 #SEC tmpLen (bn_v b) i;
    index_nat_to_intseq_le #U8 #SEC len (bn_v b) i in

  Classical.forall_intro aux;
  eq_intro (nat_to_intseq_le #U8 #SEC len (bn_v b)) res


val bn_from_bytes_le_is_uints_from_bytes_le:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t /\ len % numbytes t = 0}
  -> b:lseq uint8 len ->
  Lemma (bn_from_bytes_le #t len b == uints_from_bytes_le b)

let bn_from_bytes_le_is_uints_from_bytes_le #t len b =
  let lp = bn_from_bytes_le #t len b in
  let rp = uints_from_bytes_le #t #SEC #(len / numbytes t) b in
  //uints_from_bytes_le_nat_lemma #t #SEC #(len / numbytes t) b;
  //assert (nat_from_intseq_le rp == nat_from_bytes_le b);

  //bn_from_bytes_le_lemma #t len b;
  //assert (bn_v lp == nat_from_bytes_le b);
  //assert (nat_from_intseq_le rp == bn_v lp);
  assert (bn_v rp == bn_v lp);
  bn_eval_inj (len / numbytes t) rp lp


val bn_from_bytes_be_is_uints_from_bytes_be:
    #t:limb_t
  -> len:size_pos{numbytes t * (blocks len (numbytes t)) <= max_size_t /\ len % numbytes t = 0}
  -> b:lseq uint8 len ->
  Lemma (reverse (bn_from_bytes_be #t len b) == uints_from_bytes_be b)

let bn_from_bytes_be_is_uints_from_bytes_be #t len b =
  let lp = bn_from_bytes_be #t len b in
  let rp = uints_from_bytes_be #t #SEC #(len / numbytes t) b in
  uints_from_bytes_be_nat_lemma #t #SEC #(len / numbytes t) b;
  assert (nat_from_intseq_be rp == nat_from_bytes_be b);

  bn_from_bytes_be_lemma #t len b;
  assert (bn_v lp == nat_from_bytes_be b);

  bn_v_is_nat_from_intseq_be_lemma (len / numbytes t) lp;
  assert (bn_v lp == nat_from_intseq_be (reverse lp));
  assert (nat_from_intseq_be rp == nat_from_intseq_be (reverse lp));
  nat_from_intseq_be_inj rp (reverse lp)
