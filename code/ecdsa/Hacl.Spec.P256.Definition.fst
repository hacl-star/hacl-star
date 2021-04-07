module Hacl.Spec.P256.Definition

open Lib.IntTypes
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.Sequence
open Lib.Buffer
open FStar.Mul

open Spec.ECC.Curves

#set-options " --z3rlimit 200"

noextract
let point_seq (c: curve) = lseq uint64 (uint_v (getCoordinateLenU64 c) * 3)

noextract
let felem_seq (c: curve) = lseq uint64 (uint_v (getCoordinateLenU64 c))

inline_for_extraction
let felem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c)

inline_for_extraction 
let widefelem (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 2ul)


noextract 
val lseq_as_nat_: #l: size_nat -> a: lseq uint64 l -> i: nat {i <= Lib.Sequence.length a} -> Tot nat

let rec lseq_as_nat_ #l a i = 
  if i = 0 then 0 else
  let a_i_1 = Lib.Sequence.index a (i - 1) in
  lseq_as_nat_ a (i - 1) + pow2 (64 * (i - 1)) * v a_i_1

val lseq_as_nat_last: #l: size_nat -> a: lseq uint64 l -> Lemma (lseq_as_nat_ #l a 0 == 0)

let lseq_as_nat_last #l a = ()

val lseq_as_nat_first: a: lseq uint64 1 -> Lemma (lseq_as_nat_ a 1 == v (Lib.Sequence.index a 0))

let lseq_as_nat_first a = ()


noextract 
val lseq_as_nat: #l: size_nat -> a: lseq uint64 l -> Tot nat

let lseq_as_nat #l a = lseq_as_nat_ a l


val lseq_as_nat_definiton: #len:size_nat -> a: lseq uint64 len 
  -> i: nat {i > 0 /\ i <= len} ->
  Lemma (lseq_as_nat_ #len a i == 
    lseq_as_nat_ a (i - 1) + pow2 (64 * (i - 1)) * v (Lib.Sequence.index a (i - 1)))

let lseq_as_nat_definiton #len b i = ()


val lemma_create_: #l: size_nat -> i: nat {i > 0 /\ i <= l} ->
  Lemma (let a = Seq.create l (u64 0) in lseq_as_nat_ #l a i == 0)


let rec lemma_create_ #l i = 
  let a = Seq.create l (u64 0) in 
  match i with 
  |1 -> 
    lseq_as_nat_definiton #l a 1
  |_ -> 
    lemma_create_ #l (i - 1);
    lseq_as_nat_definiton #l a i


val lemma_create_zero_buffer: len: size_nat {len > 0} -> c: curve -> Lemma (
  lseq_as_nat #len (Seq.create len (u64 0)) == 0)

let lemma_create_zero_buffer len c = lemma_create_ #len len


val lemma_lseq_as_seq_as_forall: #l: size_nat -> a: lseq uint64 l -> b: lseq uint64 l -> i: nat {i >= 0 /\ i < l} ->
  Lemma 
    (requires (forall (k: nat). k <= (i - 1) ==> Lib.Sequence.index a k == Lib.Sequence.index b k))
    (ensures (lseq_as_nat_ #l a i == lseq_as_nat_ #l b i))

let rec lemma_lseq_as_seq_as_forall #l a b i = 
  match i with 
  |0 -> lseq_as_nat_last a; lseq_as_nat_last b
  |_ -> 
    assert(forall (k:nat). k <= i - 1 ==> Lib.Sequence.index a k == Lib.Sequence.index b k);
    lemma_lseq_as_seq_as_forall a b (i - 1);
    lseq_as_nat_definiton a i;
    lseq_as_nat_definiton b i;
    assert(v (Lib.Sequence.index a (i - 1)) == v (Lib.Sequence.index b (i - 1)))


val lemma_lseq_as_seq_extension: 
  #l0: size_nat ->  #l1: size_nat -> 
  a0: lseq uint64 l0 -> a1: lseq uint64 l1 -> 
  i: nat {i <= l0 /\ i <= l1} ->
  Lemma 
    (requires (Lib.Sequence.sub a0 0 i == Lib.Sequence.sub a1 0 i))
    (ensures lseq_as_nat_ a0 i == lseq_as_nat_ a1 i)

let rec lemma_lseq_as_seq_extension #l0 #l1 a0 a1 i = 
  match i with 
  | 0 -> ()
  | _ -> 
    assert(forall (k: nat {k < i}). Lib.Sequence.index (Lib.Sequence.sub a1 0 i) k == Lib.Sequence.index a0 k);
    assert(forall (k: nat {k < i}). Lib.Sequence.index (Lib.Sequence.sub a0 0 i) k == Lib.Sequence.index a0 k);
    
    eq_intro (Lib.Sequence.sub a0 0 (i - 1)) (Lib.Sequence.sub a1 0 (i - 1));
    assert(Lib.Sequence.sub a0 0 (i - 1) == Lib.Sequence.sub a1 0 (i - 1));
    
    lemma_lseq_as_seq_extension a0 a1 (i - 1);

    lseq_as_nat_definiton a0 i;
    lseq_as_nat_definiton a1 i;

    assert(forall (k: nat {k < i}). Lib.Sequence.index a0 k == Lib.Sequence.index a1 k);
    assert (Lib.Sequence.index a0 (i - 1) == Lib.Sequence.index a1 (i - 1))


assume val lseq_upperbound: #l: size_nat -> a: lseq uint64 l -> Lemma (lseq_as_nat a < pow2 (64 * l))


noextract
let felem_seq_as_nat (c: curve) (a: felem_seq c) : Tot nat = lseq_as_nat a

let point_prime_to_coordinates (c: curve) (p:point_seq c) : point_nat_prime #c =
  let len = uint_v (getCoordinateLenU64 c) in 
  lseq_as_nat (Lib.Sequence.sub p 0 len),
  lseq_as_nat (Lib.Sequence.sub p len len),
  lseq_as_nat (Lib.Sequence.sub p (len * 2) len)
  

noextract
let as_nat (c: curve) (h:mem) (e:felem c) : GTot nat = lseq_as_nat (as_seq h e)

noextract
let as_nat_il (c: curve) (h:mem) (e:glbuffer uint64 (getCoordinateLenU64 c)) : GTot nat =
  lseq_as_nat (as_seq h e)


noextract
let wide_as_nat (c: curve) (h:mem) (e: widefelem c) : GTot nat = lseq_as_nat (as_seq h e)


inline_for_extraction
type point (c: curve) = lbuffer uint64 (getCoordinateLenU64 c *! 3ul)

type scalar (c: curve) = lbuffer uint8 (getScalarLen c)



noextract 
let point_x_as_nat (c: curve) (h: mem) (e: point c) : GTot nat = 
  as_nat c h (gsub e (size 0) (getCoordinateLenU64 c))

noextract 
let point_y_as_nat (c: curve) (h: mem) (e: point c) : GTot nat = 
  as_nat c h (gsub e (getCoordinateLenU64 c) (getCoordinateLenU64 c))


val getZ: #c: curve -> p: point c -> GTot (felem c)

let getZ #c p = gsub p (size 2 *! getCoordinateLenU64 c) (getCoordinateLenU64 c)

noextract 
let point_z_as_nat (c: curve) (h: mem) (e: point c) : GTot nat = 
  as_nat c h (getZ #c e)

val felem_eval: c: curve -> h: mem -> f: felem c -> Type0

let felem_eval c h f = as_nat c h f < getPrime c



val changeEndianStep: #c: curve 
  -> i: nat {i <= v (shift_right (getCoordinateLenU64 c) 1ul)}  -> felem_seq c -> felem_seq c 

let changeEndianStep #c i b =
  let len = v (getCoordinateLenU64 c) in 
  let lenRight = len - 1 - i in 
  let left = Lib.Sequence.index b i in 
  let right = Lib.Sequence.index b lenRight in 
  let b = Lib.Sequence.upd b i right in 
  Lib.Sequence.upd b lenRight left


val changeEndian: #c: curve -> felem_seq c -> felem_seq c

let changeEndian #c b =
  let len = getCoordinateLenU64 c in 
  let lenByTwo = shift_right len 1ul in 
  Lib.LoopCombinators.repeati (v lenByTwo) (changeEndianStep) b


val changeEndianLemma: #c: curve -> k: lseq uint64 (getCoordinateLen c) -> Lemma
  (Lib.ByteSequence.nat_from_intseq_le (changeEndian #c k) == Lib.ByteSequence.nat_from_intseq_be k)

let changeEndianLemma #c k =
  let open Lib.ByteSequence in 
  let k0 = changeEndian #c k in

  nat_from_intseq_be_slice_lemma (slice k 2 4) 1;
  nat_from_intseq_be_slice_lemma (slice k 1 4) 1;
  nat_from_intseq_be_slice_lemma k 1;

  nat_from_intseq_be_lemma0 (slice k 0 1);
  nat_from_intseq_be_lemma0 (slice k 1 2);
  nat_from_intseq_be_lemma0 (slice k 2 3);
  nat_from_intseq_be_lemma0 (slice k 3 4);

  nat_from_intseq_le_slice_lemma (slice k0 2 4) 1;
  nat_from_intseq_le_slice_lemma (slice k0 1 4) 1;
  nat_from_intseq_le_slice_lemma k0 1;

  nat_from_intseq_le_lemma0 (slice k0 0 1);
  nat_from_intseq_le_lemma0 (slice k0 1 2);
  nat_from_intseq_le_lemma0 (slice k0 2 3);
  nat_from_intseq_le_lemma0 (slice k0 3 4);

  assert_norm (pow2 (2 * 64) * pow2 64 == pow2 (3 * 64))


val changeEndianLemmaI: #c: curve -> a: nat {a < pow2 (getPower c)} -> Lemma
  (changeEndian #c (Lib.ByteSequence.nat_to_intseq_le (uint_v (getCoordinateLenU64 c)) a) == Lib.ByteSequence.nat_to_intseq_be (uint_v (getCoordinateLenU64 c)) a)

let changeEndianLemmaI #c a =
  let open Lib.ByteSequence in 
  let len = getCoordinateLenU64 c in
  let a0 = nat_to_intseq_le #U64 #SEC 4 a in
  index_nat_to_intseq_le #U64 #SEC  4 a 0;
  index_nat_to_intseq_le #U64 #SEC  4 a 1;
  index_nat_to_intseq_le #U64 #SEC  4 a 2;
  index_nat_to_intseq_le #U64 #SEC  4 a 3;

  index_nat_to_intseq_be #U64 #SEC 4 a 0;
  index_nat_to_intseq_be #U64 #SEC 4 a 2;
  index_nat_to_intseq_be #U64 #SEC 4 a 3;
  index_nat_to_intseq_be #U64 #SEC 4 a 1;


  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 3 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 3);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 2 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 2);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 1 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 1);

  assert(Lib.Sequence.index #_ #4 (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) 0 == Lib.Sequence.index #_ #4 (nat_to_intseq_be #U64 #SEC 4 a) 0);
  eq_intro (changeEndian #c (nat_to_intseq_le #U64 #SEC 4 a)) (nat_to_intseq_be 4 a)


val changeEndian_le_be: #c: curve -> a:nat{a < pow2 (getPower c)} -> Lemma
  (Lib.ByteSequence.uints_to_bytes_be (changeEndian #c (Lib.ByteSequence.nat_to_intseq_le (uint_v (getCoordinateLenU64 c)) a)) == Lib.ByteSequence.nat_to_bytes_be (getCoordinateLen c) a)

let changeEndian_le_be #c a =
  changeEndianLemmaI #c a;
  Lib.ByteSequence.uints_to_bytes_be_nat_lemma #U64 #SEC (uint_v (getCoordinateLenU64 c)) a


let point_eval (c: curve) (h:mem) (p:point c) = 
  point_x_as_nat c h p < getPrime c /\
  point_y_as_nat c h p < getPrime c /\
  point_z_as_nat c h p < getPrime c 
  
