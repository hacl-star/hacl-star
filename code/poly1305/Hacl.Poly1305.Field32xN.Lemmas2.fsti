module Hacl.Poly1305.Field32xN.Lemmas2

open Lib.IntTypes
open Lib.IntVector
open Lib.Sequence
open FStar.Mul

open Hacl.Spec.Poly1305.Vec
include Hacl.Spec.Poly1305.Field32xN

val load_tup64_lemma0_lo: lo:uint64 ->
  Lemma
   (v lo % pow2 26 + ((v lo / pow2 26) % pow2 26) * pow26 +
    v lo / pow2 52 * pow52 == v lo)

val load_tup64_lemma0_hi: hi:uint64 ->
  Lemma
  ((v hi % pow2 14) * pow2 64 + (v hi / pow2 14) % pow2 26 * pow78 + v hi / pow2 40 * pow104 ==
    v hi * pow2 64)

val load_tup64_lemma0:
    f:tup64_5
  -> lo:uint64
  -> hi:uint64 ->
  Lemma
  (requires
   (let (f0, f1, f2, f3, f4) = f in
    v f0 == v lo % pow2 26 /\
    v f1 == (v lo / pow2 26) % pow2 26 /\
    v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12 /\
    v f3 == (v hi / pow2 14) % pow2 26 /\
    v f4 == v hi / pow2 40))
  (ensures as_nat5 f == v hi * pow2 64 + v lo)

val load_tup64_fits_lemma:
    f:tup64_5
  -> lo:uint64
  -> hi:uint64 ->
  Lemma
  (requires
   (let (f0, f1, f2, f3, f4) = f in
    v f0 == v lo % pow2 26 /\
    v f1 == (v lo / pow2 26) % pow2 26 /\
    v f2 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12 /\
    v f3 == (v hi / pow2 14) % pow2 26 /\
    v f4 == v hi / pow2 40))
  (ensures tup64_fits5 f (1, 1, 1, 1, 1))

val load_tup64_lemma_f2: lo:uint64 -> hi:uint64 -> Lemma
  (v ((lo >>. 52ul) |. ((hi &. u64 0x3fff) <<. 12ul)) ==
    v lo / pow2 52 + (v hi % pow2 14) * pow2 12)

noextract
val load_tup64_lemma: lo:uint64 -> hi:uint64 ->
  Pure tup64_5
  (requires True)
  (ensures  fun f ->
    tup64_fits5 f (1, 1, 1, 1, 1) /\
    as_nat5 f < pow2 128 /\
    as_nat5 f % prime == v hi * pow2 64 + v lo)

val load_felem5_lemma_i:
    #w:lanes
  -> lo:uint64xN w
  -> hi:uint64xN w
  -> i:nat{i < w} ->
  Lemma
  (let f = as_tup64_i (load_felem5 #w lo hi) i in
   tup64_fits5 f (1, 1, 1, 1, 1) /\
   as_nat5 f < pow2 128 /\
   as_nat5 f % prime == (uint64xN_v hi).[i] * pow2 64 + (uint64xN_v lo).[i])

noextract
let load_tup64_4_compact (lo hi : uint64) : tup64_5 =
  let mask26 = u64 0x3ffffff in
  let t3 = (lo >>. 48ul) |. (hi <<. 16ul) in
  let o0 = lo &. mask26 in
  let o1 = (lo >>. 26ul) &. mask26 in
  let o2 = (t3 >>. 4ul) &. mask26 in
  let o3 = (t3 >>. 30ul) &. mask26 in
  let o4 = hi >>. 40ul in
  (o0, o1, o2, o3, o4)

val load_tup64_4_compact_lemma_f2_mod: lo:uint64 -> hi:uint64 -> Lemma
  ((v lo / pow2 52 + (v hi % pow2 14) * pow2 12) % pow2 26 == v lo / pow2 52 + (v hi % pow2 14) * pow2 12)

val load_tup64_4_compact_lemma_f2: lo:uint64 -> hi:uint64 -> Lemma
  (let t3 = (lo >>. 48ul) |. (hi <<. 16ul) in
   v ((t3 >>. 4ul) &. u64 0x3ffffff) == v lo / pow2 52 + (v hi % pow2 14) * pow2 12)

val load_tup64_4_compact_lemma_f3: lo:uint64 -> hi:uint64 -> Lemma
  (let t3 = (lo >>. 48ul) |. (hi <<. 16ul) in
   v ((t3 >>. 30ul) &. u64 0x3ffffff) == (v hi / pow2 14) % pow2 26)

val load_tup64_4_compact_lemma: lo:uint64 -> hi:uint64 ->
  Lemma (load_tup64_4_compact lo hi == load_tup64_lemma lo hi)

val lemma_store_felem_lo:
    f:tup64_5{tup64_fits5 f (1, 1, 1, 1, 1)}
  -> lo:uint64 ->
  Lemma
  (let (f0, f1, f2, f3, f4) = f in
   let lo = f0 |. (f1 <<. 26ul) |. (f2 <<. 52ul) in
   v lo == v f0 + v f1 * pow2 26 + (v f2 * pow2 52) % pow2 64)

val lemma_store_felem_hi: f:tup64_5 -> hi:uint64 ->
  Lemma
  (requires tup64_fits5 f (1, 1, 1, 1, 1))
  (ensures
   (let (f0, f1, f2, f3, f4) = f in
    let hi = (f2 >>. 12ul) |. (f3 <<. 14ul) |. (f4 <<. 40ul) in
    v hi == v f2 / pow2 12 + v f3 * pow2 14 + (v f4 * pow2 40) % pow2 64))

val lemma_tup64_pow2_128: f:tup64_5 ->
  Lemma
  (requires tup64_fits5 f (1, 1, 1, 1, 1))
  (ensures
    (let (f0, f1, f2, f3, f4) = f in
     v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + (v f4 % pow2 24) * pow104 < pow2 128))

val lemma_tup64_mod_pow2_128: f:tup64_5 ->
  Lemma
  (requires tup64_fits5 f (1, 1, 1, 1, 1))
  (ensures
    (let (f0, f1, f2, f3, f4) = f in
    (as_nat5 f) % pow2 128 == v f0 + v f1 * pow26 + v f2 * pow52 + v f3 * pow78 + (v f4 % pow2 24) * pow104))

noextract
val store_tup64_lemma: f:tup64_5 ->
  Pure (uint64 & uint64)
  (requires tup64_fits5 f (1, 1, 1, 1, 1))
  (ensures (fun (lo, hi) -> v hi * pow2 64 + v lo == as_nat5 f % pow2 128))

val store_felem5_lemma:
    #w:lanes
  -> f:felem5 w ->
  Lemma
  (requires felem_fits5 f (1, 1, 1, 1, 1))
  (ensures
    (let (lo, hi) = store_felem5 f in
    v hi * pow2 64 + v lo == (fas_nat5 f).[0] % pow2 128))

val lemma_sum_lt_pow2_26: i:nat -> a:nat{a < pow2 (i % 26)} -> b:nat{b <= pow2 (i % 26)} ->
  Lemma (a + b <= max26)

val lset_bit5_lemma_aux: fi:uint64 -> i:size_nat{i <= 128} ->
  Lemma
  (requires v fi < pow2 (i % 26))
  (ensures  (v (fi |. (u64 1 <<. size (i % 26))) == v fi + pow2 (i % 26)))

val lset_bit5_lemma0:
    f:lseq uint64 5
  -> i:size_nat{i <= 128 /\ i / 26 = 0} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
    as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) ==
      pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4])))

val lset_bit5_lemma1:
    f:lseq uint64 5
  -> i:size_nat{i <= 128 /\ i / 26 = 1} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
    as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) ==
      pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4])))

val lset_bit5_lemma2:
    f:lseq uint64 5
  -> i:size_nat{i <= 128 /\ i / 26 = 2} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
    as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) ==
      pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4])))

val lset_bit5_lemma3:
    f:lseq uint64 5
  -> i:size_nat{i <= 128 /\ i / 26 = 3} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
    as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) ==
      pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4])))

val lset_bit5_lemma4:
    f:lseq uint64 5
  -> i:size_nat{i <= 128 /\ i / 26 = 4} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
    as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) ==
      pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4])))

val lset_bit5_:
    f:lseq uint64 5
  -> i:size_nat{i <= 128} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
     as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) ==
      pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4])))

val lset_bit5:
    f:lseq uint64 5
  -> i:size_nat{i <= 128} ->
  Lemma
  (requires
    (forall (i:nat). i < 5 ==> v f.[i] <= max26) /\
     as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) < pow2 i)
  (ensures
   (let b = u64 1 <<. size (i % 26) in
    let out = f.[i / 26] <- f.[i / 26] |. b in
    (forall (i:nat). i < 5 ==> v out.[i] <= max26) /\
    as_nat5 (out.[0], out.[1], out.[2], out.[3], out.[4]) % prime ==
      (pow2 i + as_nat5 (f.[0], f.[1], f.[2], f.[3], f.[4]) % prime) % prime))

val set_bit5_lemma_k:
    #w:lanes
  -> f:lseq (uint64xN w) 5
  -> i:size_nat{i <= 128}
  -> k:nat{k < w} ->
  Lemma
  (requires
    lfelem_fits f (1, 1, 1, 1, 1) /\
    lfelem_less f (pow2 i))
  (ensures (
    let out = set_bit5 f i in
    tup64_fits5 (as_tup64_i (as_tup5 out) k) (1, 1, 1, 1, 1) /\
    (lfeval out).[k] == pfadd (pow2 i) (lfeval f).[k]))
