module Lib.ByteSequence

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.RawIntTypes
open Lib.LoopCombinators

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 1"

/// BEGIN constant-time sequence equality

val lemma_not_equal_slice: #a:Type -> b1:Seq.seq a -> b2:Seq.seq a -> i:nat -> j:nat ->
  k:nat{i <= j /\ i <= k /\ j <= k /\ k <= Seq.length b1 /\ k <= Seq.length b2 } ->
  Lemma
    (requires ~(Seq.equal (Seq.slice b1 i j) (Seq.slice b2 i j)))
    (ensures  ~(Seq.equal (Seq.slice b1 i k) (Seq.slice b2 i k)))
let lemma_not_equal_slice #a b1 b2 i j k =
  assert (forall (n:nat{n < k - i}). Seq.index (Seq.slice b1 i k) n == Seq.index b1 (n + i))

val lemma_not_equal_last: #a:Type -> b1:Seq.seq a -> b2:Seq.seq a -> i:nat ->
  j:nat{i < j /\ j <= Seq.length b1 /\ j <= Seq.length b2} ->
  Lemma
    (requires ~(Seq.index b1 (j - 1) == Seq.index b2 (j - 1)))
    (ensures  ~(Seq.equal (Seq.slice b1 i j) (Seq.slice b2 i j)))
let lemma_not_equal_last #a b1 b2 i j =
  Seq.lemma_index_slice b1 i j (j - i - 1);
  Seq.lemma_index_slice b2 i j (j - i - 1)

val seq_eq_mask_inner: #t:inttype{~(U1? t)} -> #len1:size_nat -> #len2:size_nat
  -> b1:lseq (uint_t t SEC) len1
  -> b2:lseq (uint_t t SEC) len2
  -> len:size_nat{len <= len1 /\ len <= len2}
  -> i:size_nat{i < len}
  -> res:uint_t t SEC{
      (sub b1 0 i == sub b2 0 i  ==> v res == v (ones t SEC)) /\
      (sub b1 0 i =!= sub b2 0 i ==> v res == v (zeroes t SEC))}
  -> res':uint_t t SEC{
      (sub b1 0 (i + 1) == sub b2 0 (i + 1)  ==> v res' == v (ones t SEC)) /\
      (sub b1 0 (i + 1) =!= sub b2 0 (i + 1) ==> v res' == v (zeroes t SEC))}
let seq_eq_mask_inner #t #len1 #len2 b1 b2 len i res =
  UInt.logand_lemma_1 #(8 * numbytes t) (maxint t);
  UInt.logand_lemma_2 #(8 * numbytes t) (maxint t);
  UInt.logand_lemma_1 #(8 * numbytes t) 0;
  UInt.logand_lemma_2 #(8 * numbytes t) 0;
  let z0 = res in
  let res = eq_mask b1.[i] b2.[i] &. z0 in
  logand_spec (eq_mask b1.[i] b2.[i]) z0;
  if v res = maxint t then
    begin
    let s1 = sub b1 0 (i + 1) in
    let s2 = sub b2 0 (i + 1) in
    Seq.lemma_split s1 i;
    Seq.lemma_split s2 i;
    uintv_extensionality b1.[i] b2.[i];
    assert (equal s1 s2)
    end
  else if v z0 = 0 then
    lemma_not_equal_slice b1 b2 0 i (i + 1)
  else
    lemma_not_equal_last b1 b2 0 (i + 1);
  res

let seq_eq_mask #t #len1 #len2 b1 b2 len =
  repeati_inductive len
    (fun (i:nat{i <= len}) res ->
      (sub b1 0 i == sub b2 0 i  ==> v res == v (ones t SEC)) /\
      (sub b1 0 i =!= sub b2 0 i ==> v res == v (zeroes t SEC)))
    (seq_eq_mask_inner b1 b2 len)
    (ones t SEC)

let lbytes_eq #len b1 b2 =
  let res = seq_eq_mask b1 b2 len in
  RawIntTypes.u8_to_UInt8 res = 255uy

/// END constant-time sequence equality

val nat_from_intseq_be_:
    #t:inttype -> #l:secrecy_level
  -> b:seq (uint_t t l)
  -> Tot (n:nat{n < pow2 (length b * bits t)}) (decreases (length b))
let rec nat_from_intseq_be_ #t #l b =
  let len = length b in
  if len = 0 then 0
  else
    let l = uint_to_nat (Seq.index b (len - 1)) in
    let pre = Seq.slice b 0 (len - 1) in
    let shift = pow2 (bits t) in
    let n' = nat_from_intseq_be_ pre in
    Math.Lemmas.pow2_plus (bits t) (len * bits t - bits t);
    l + shift * n'

let nat_from_intseq_be = nat_from_intseq_be_

val nat_from_intseq_le_:
    #t:inttype -> #l:secrecy_level
  -> b:seq (uint_t t l)
  -> Tot (n:nat{n < pow2 (length b * bits t)}) (decreases (length b))

let rec nat_from_intseq_le_ #t #l b =
  let len = length b in
  if len = 0 then 0
  else
    let shift = pow2 (bits t) in
    let tt = Seq.slice b 1 len in
    let n' = nat_from_intseq_le_ #t #l tt in
    let l = uint_to_nat #t #l (Seq.index b 0) in
    Math.Lemmas.pow2_plus (bits t) ( len * bits t - bits t);
    let n = l + shift * n' in
    n

let nat_from_intseq_le = nat_from_intseq_le_
let nat_from_bytes_be = nat_from_intseq_be #U8
let nat_from_bytes_le = nat_from_intseq_le #U8

#set-options "--max_fuel 1"

val nat_to_intseq_be_:
    #t:inttype -> #l:secrecy_level
  -> len:nat
  -> n:nat{n < pow2 (bits t * len)}
  -> Tot (b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_be b}) (decreases len)
let rec nat_to_intseq_be_ #t #l len n =
  if len = 0 then create len (uint #t #l 0)
  else
    let len' = len - 1 in
    let tt = uint #t #l (n % modulus t) in
    let n' = n / modulus t in
    assert (modulus t = pow2 (bits t));
    FStar.Math.Lemmas.lemma_div_lt_nat n (bits t * len) (bits t);
    let b' = nat_to_intseq_be_ len' n' in
    let b  = Seq.append b' (create 1 tt) in
    Seq.append_slices b' (create 1 tt);
    b

let nat_to_intseq_be = nat_to_intseq_be_

val nat_to_intseq_le_:
    #t:inttype -> #l:secrecy_level
  -> len:nat
  -> n:nat{n < pow2 (bits t * len)}
  -> Tot (b:seq (uint_t t l){length b == len /\ n == nat_from_intseq_le b}) (decreases len)
let rec nat_to_intseq_le_ #t #l len n =
  if len = 0 then create len (uint #t #l 0)
  else
    let len' = len - 1 in
    let tt = uint #t #l (n % modulus t) in
    let n' = n / modulus t in
    assert (modulus t = pow2 (bits t));
    FStar.Math.Lemmas.lemma_div_lt_nat n (bits t * len) (bits t);
    let b' = nat_to_intseq_le_ len' n' in
    let b = Seq.append (create 1 tt) b' in
    Seq.append_slices (create 1 tt) b';
    b

let nat_to_intseq_le = nat_to_intseq_le_

let nat_to_bytes_be = nat_to_intseq_be_ #U8
let nat_to_bytes_le = nat_to_intseq_le_ #U8

val index_nat_to_bytes_le:
    #l:secrecy_level
  -> len:size_nat
  -> n:nat{n < pow2 (8 * len)}
  -> i:nat{i < len}
  -> Lemma (Seq.index (nat_to_bytes_le #l len n) i == uint #U8 #l (n / pow2 (8 * i) % pow2 8))
let rec index_nat_to_bytes_le #l len n i =
  if i = 0 then ()
  else
    begin
    index_nat_to_bytes_le #l (len - 1) (n / 256) (i - 1);
    assert (Seq.index (nat_to_bytes_le (len - 1) (n / 256)) (i - 1) ==
            uint #U8 #l ((n / 256) / pow2 (8 * (i - 1)) % pow2 8));
    assert_norm (pow2 8 == 256);
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (i - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (i - 1));
    assert (n / pow2 8 / pow2 (8 * (i - 1)) == n / (pow2 8 * pow2 (8 * i - 8)))
    end

let uint_to_bytes_le #t #l n =
  nat_to_bytes_le (numbytes t) (uint_to_nat n)

let index_uint_to_bytes_le #t #l u =
  Classical.forall_intro (index_nat_to_bytes_le #l (numbytes t) (uint_to_nat u))

let uint_to_bytes_be #t #l n =
  nat_to_bytes_be (numbytes t) (uint_to_nat n)

let uint_from_bytes_le #t #l b =
  let n = nat_from_intseq_le #U8 b in
  nat_to_uint #t #l n

let uint_from_bytes_be #t #l b =
  let n = nat_from_intseq_be #U8 b in
  nat_to_uint #t #l n

val uints_to_bytes_le_inner: #t:inttype -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len
  -> i:nat{i < len} -> unit -> unit & (lseq (uint_t U8 l) (numbytes t))
let uints_to_bytes_le_inner #t #l #len b i () =
  let open Lib.Sequence in
  (), uint_to_bytes_le #t #l b.[i]

let uints_to_bytes_le #t #l #len ul =
  let a_spec (i:size_nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes t) len a_spec
    (uints_to_bytes_le_inner #t #l #len ul) () in
  o

val uints_to_bytes_be_inner: #t:inttype -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> lseq (uint_t t l) len
  -> i:nat{i < len} -> unit -> unit & (lseq (uint_t U8 l) (numbytes t))
let uints_to_bytes_be_inner #t #l #len b i () =
  let open Lib.Sequence in
  (), uint_to_bytes_be #t #l b.[i]

let uints_to_bytes_be #t #l #len ul =
  let a_spec (i:size_nat{i <= len}) = unit in
  let _, o = generate_blocks (numbytes t) len a_spec
    (uints_to_bytes_be_inner #t #l #len ul) () in
  o

let uints_from_bytes_le #t #l #len b =
  Lib.Sequence.createi #(uint_t t l) len
    (fun i -> uint_from_bytes_le (sub b (i * numbytes t) (numbytes t)))

let uints_from_bytes_be #t #l #len b =
  Lib.Sequence.createi #(uint_t t l) len
    (fun i -> uint_from_bytes_be (sub b (i * numbytes t) (numbytes t)))

val nat_from_intseq_le_slice_lemma0:
  #t:inttype -> #l:secrecy_level -> #len:size_nat{len > 0} -> b:lseq (uint_t t l) len -> i:size_nat{0 < i /\ i <= len} ->
  Lemma
    (pow2 ((i - 1) * bits t) * nat_from_intseq_le_ (Seq.slice b (i - 1) len) ==
     pow2 ((i - 1) * bits t) * v b.[i - 1] + pow2 (i * bits t) * nat_from_intseq_le_ (Seq.slice b i len))
let nat_from_intseq_le_slice_lemma0 #t #l #len b i =
  FStar.Math.Lemmas.distributivity_add_right (pow2 ((i - 1) * bits t)) (v b.[i - 1]) (pow2 (bits t) * nat_from_intseq_le_ (Seq.slice b i len));
  FStar.Math.Lemmas.paren_mul_right (pow2 ((i - 1) * bits t)) (pow2 (bits t)) (nat_from_intseq_le_ (Seq.slice b i len));
  FStar.Math.Lemmas.pow2_plus ((i - 1) * bits t) (bits t)

val nat_from_intseq_le_slice_lemma1:
  #t:inttype -> #l:secrecy_level -> #len:size_nat -> b:lseq (uint_t t l) len -> i:size_nat{0 < i /\ i <= len} ->
  Lemma
    (requires (let b1 = Seq.slice b 0 i in
      nat_from_intseq_le_ b1 == nat_from_intseq_le_ (Seq.slice b1 0 (i - 1)) + pow2 ((i - 1) * bits t) * nat_from_intseq_le_ (Seq.slice b1 (i - 1) i)))
    (ensures
      nat_from_intseq_le_ (Seq.slice b 0 i) == nat_from_intseq_le_ (Seq.slice b 0 (i - 1)) + pow2 ((i - 1) * bits t) * v b.[i - 1])
let nat_from_intseq_le_slice_lemma1 #t #l #len b i = ()

val nat_from_intseq_le_slice_lemma_:
  #t:inttype -> #l:secrecy_level -> #len:size_nat -> b:lseq (uint_t t l) len -> i:nat{i <= len} ->
  Lemma
    (nat_from_intseq_le_ b == nat_from_intseq_le_ (Seq.slice b 0 i) + pow2 (i * bits t) * nat_from_intseq_le_ (Seq.slice b i len))
let rec nat_from_intseq_le_slice_lemma_ #t #l #len b i =
  if len = 0 then ()
  else begin
    if i = 0 then ()
    else begin
      nat_from_intseq_le_slice_lemma_ b (i - 1);
      nat_from_intseq_le_slice_lemma0 b i;
      nat_from_intseq_le_slice_lemma_ #t #l #i (Seq.slice b 0 i) (i - 1);
      nat_from_intseq_le_slice_lemma1 b i
    end
  end

let nat_from_intseq_le_slice_lemma #t #l #len b i = nat_from_intseq_le_slice_lemma_ b i
let nat_from_bytes_le_slice_lemma #l #len b i = nat_from_intseq_le_slice_lemma_ b i


val uints_from_bytes_le_lemma0:
    #t:inttype{~(t == U1)}
  -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (forall (i:nat). i < len - 1 ==>
    (uints_from_bytes_le #t #l #len b).[i + 1] == uint_from_bytes_le (sub b ((i + 1) * numbytes t) (numbytes t)))
let uints_from_bytes_le_lemma0 #t #l #len b = ()

val uints_from_bytes_le_lemma1:
    #t:inttype{~(t == U1)}
  -> #l:secrecy_level
  -> #len:size_nat{0 < len /\ len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (forall (i:nat). i < len - 1 ==>
    Seq.index (Seq.slice (uints_from_bytes_le #t #l #len b) 1 len) i ==
    uint_from_bytes_le (sub b ((i + 1) * numbytes t) (numbytes t)))
let uints_from_bytes_le_lemma1 #t #l #len b =
  uints_from_bytes_le_lemma0 b

#set-options "--z3rlimit 300"

val uints_from_bytes_le_slice_lemma:
    #t:inttype{~(t == U1)}
  -> #l:secrecy_level
  -> #len:size_nat{0 < len /\ len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (
    Seq.slice (uints_from_bytes_le #t #_ #len b) 1 len ==
    uints_from_bytes_le #t #_ #(len-1) (Seq.slice b (numbytes t) (len * numbytes t)))
let uints_from_bytes_le_slice_lemma #t #l #len b =
  let r = uints_from_bytes_le #t #_ #len b in
  let r1 = uints_from_bytes_le #t #_ #(len-1) (Seq.slice b (numbytes t) (len * numbytes t)) in
  assert (forall (i:nat). i < len - 1 ==> r1.[i] == uint_from_bytes_le (sub b ((i + 1) * numbytes t) (numbytes t)));
  uints_from_bytes_le_lemma1 b;
  eq_intro (Seq.slice r 1 len) r1

val uints_from_bytes_le_nat_lemma0:
    #t:inttype{~(t == U1)}
  -> #l:secrecy_level
  -> #len:size_nat{0 < len /\ len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (
    nat_from_intseq_le_ (uints_from_bytes_le #t #_ #len b) ==
    nat_from_intseq_le_ (Seq.slice b 0 (numbytes t)) +
    pow2 (bits t) * nat_from_intseq_le_ (uints_from_bytes_le #t #_ #(len-1) (Seq.slice b (numbytes t) (numbytes t * len))))
let uints_from_bytes_le_nat_lemma0 #t #l #len b =
  let r = uints_from_bytes_le #t #_ #len b in
  let r2 = Seq.slice r 1 len in
  let b1 = Seq.slice b (numbytes t) (numbytes t * len) in
  let r1 = uints_from_bytes_le #t #_ #(len-1) b1 in
  uints_from_bytes_le_slice_lemma b;
  assert (nat_from_intseq_le_ r == v r.[0] + pow2 (bits t) * nat_from_intseq_le_ r2);
  assert (nat_from_intseq_le_ (Seq.slice b 0 (numbytes t)) == v r.[0])

val uints_from_bytes_le_nat_lemma_:
    #t:inttype{~(t == U1)}
  -> #l:secrecy_level
  -> #len:size_nat{len * numbytes t < pow2 32}
  -> b:lbytes_l l (len * numbytes t) ->
  Lemma (nat_from_intseq_le_ (uints_from_bytes_le #t #l #len b) == nat_from_intseq_le_ b)
let rec uints_from_bytes_le_nat_lemma_ #t #l #len b =
  if len = 0 then ()
  else begin
    let b1 = Seq.slice b (numbytes t) (len * numbytes t) in
    uints_from_bytes_le_nat_lemma_ #t #l #(len - 1) b1;
    nat_from_bytes_le_slice_lemma #l #(len * numbytes t) b (numbytes t);
    uints_from_bytes_le_nat_lemma0 b
  end

let uints_from_bytes_le_nat_lemma #t #l #len b = uints_from_bytes_le_nat_lemma_ #t #l #len b

let uints_to_bytes_le_nat_lemma #t #l len n = admit()

let rec nat_from_intseq_le_inj #t #l b1 b2 =
  if length b1 = 0 then ()
  else begin
    nat_from_intseq_le_inj (Seq.slice b1 1 (length b1)) (Seq.slice b2 1 (length b2));
    Seq.lemma_split b1 1;
    Seq.lemma_split b2 1;
    uintv_extensionality (Seq.index b1 0) (Seq.index b2 0)
  end
