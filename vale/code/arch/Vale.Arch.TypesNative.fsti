module Vale.Arch.TypesNative
open Vale.Def.Words_s
open Vale.Def.Types_s
open Vale.Def.TypesNative_s
open FStar.Seq

unfold let nth (#n:pos) (a:UInt.uint_t n) (i:nat{i < n}) : bool = index (UInt.to_vec #n a) i
unfold let natN = Vale.Def.Words_s.natN
unfold let pow2_norm = Vale.Def.Words_s.pow2_norm

val lemma_equal_nth (n:pos) (x y:natN (pow2 n)) : Lemma
  (requires (forall (i:nat).{:pattern (nth #n x i) \/ (nth #n y i)} i < n ==> nth #n x i == nth #n y i))
  (ensures x == y)

val lemma_zero_nth (n:nat) : Lemma
  (forall (i:nat{i < n}).{:pattern (nth #n 0 i)} not (nth #n 0 i))

val lemma_quad32_vec_equal (a b:quad32) : Lemma
  (requires (
    let Mkfour a0 a1 a2 a3 = a in
    let Mkfour b0 b1 b2 b3 = b in
    equal (UInt.to_vec #32 a0) (UInt.to_vec #32 b0) /\
    equal (UInt.to_vec #32 a1) (UInt.to_vec #32 b1) /\
    equal (UInt.to_vec #32 a2) (UInt.to_vec #32 b2) /\
    equal (UInt.to_vec #32 a3) (UInt.to_vec #32 b3)
  ))
  (ensures a == b)

val lemma_iand_nth_i (n:pos) (x y:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (nth #n (iand x y) i == (nth #n x i && nth #n y i))

val lemma_ixor_nth_i (n:pos) (x y:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (nth #n (ixor x y) i == (nth #n x i <> nth #n y i))

val lemma_ior_nth_i (n:pos) (x y:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (nth #n (ior x y) i == (nth #n x i || nth #n y i))

val lemma_inot_nth_i (n:pos) (x:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (nth #n (inot x) i == not (nth #n x i))

val lemma_ishl_nth_i (n:pos) (x:natN (pow2 n)) (y:nat) (i:nat{i < n}) : Lemma
  (nth #n (ishl x y) i == (i + y < n && nth #n x (i + y)))

val lemma_ishr_nth_i (n:pos) (x:natN (pow2 n)) (y:nat) (i:nat{i < n}) : Lemma
  (nth #n (ishr x y) i == (i - y >= 0 && nth #n x (i - y)))

val lemma_iand_nth (n:pos) (x y:natN (pow2 n)) : Lemma
  (forall (m:_{m==pow2_norm n}) (i:nat{i < n}).{:pattern (nth #n (iand #m x y) i)}
    nth #n (iand #m x y) i == (nth #n x i && nth #n y i))

val lemma_ixor_nth (n:pos) (x y:natN (pow2 n)) : Lemma
  (forall (m:_{m==pow2_norm n}) (i:nat{i < n}).{:pattern (nth #n (ixor #m x y) i)}
    nth #n (ixor #m x y) i == (nth #n x i <> nth #n y i))

val lemma_ior_nth (n:pos) (x y:natN (pow2 n)) : Lemma
  (forall (m:_{m==pow2_norm n}) (i:nat{i < n}).{:pattern (nth #n (ior #m x y) i)}
    nth #n (ior #m x y) i == (nth #n x i || nth #n y i))

val lemma_inot_nth (n:pos) (x:natN (pow2 n)) : Lemma
  (forall (m:_{m==pow2_norm n}) (i:nat{i < n}).{:pattern (nth #n (inot #m x) i)}
    nth #n (inot #m x) i == not (nth #n x i))

val lemma_ishl_nth (n:pos) (x:natN (pow2 n)) (y:nat) : Lemma
  (forall (m:_{m==pow2_norm n}) (i:nat{i < n}).{:pattern (nth #n (ishl #m x y) i)}
    nth #n (ishl #m x y) i == (i + y < n && nth #n x (i + y)))

val lemma_ishr_nth (n:pos) (x:natN (pow2 n)) (y:nat) : Lemma
  (forall (m:_{m==pow2_norm n}) (i:nat{i < n}).{:pattern (nth #n (ishr #m x y) i)}
    nth #n (ishr #m x y) i == (i - y >= 0 && nth #n x (i - y)))

val lemma_iand_nth_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x y:natN (pow2 n)).{:pattern (iand #m x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (iand #m x y) i)}
      nth #n (iand #m x y) i == (nth #n x i && nth #n y i)))

val lemma_ixor_nth_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x y:natN (pow2 n)).{:pattern (ixor #m x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ixor #m x y) i)}
      nth #n (ixor #m x y) i == (nth #n x i <> nth #n y i)))

val lemma_ior_nth_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x y:natN (pow2 n)).{:pattern (ior #m x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ior #m x y) i)}
      nth #n (ior #m x y) i == (nth #n x i || nth #n y i)))

val lemma_inot_nth_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x:natN (pow2 n)).{:pattern (inot #m x)}
    (forall (i:nat{i < n}).{:pattern (nth #n (inot #m x) i)}
      nth #n (inot #m x) i == not (nth #n x i)))

val lemma_ishl_nth_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x:natN (pow2 n)) (y:nat).{:pattern (ishl #m x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ishl #m x y) i)}
      nth #n (ishl #m x y) i == (i + y < n && nth #n x (i + y))))

val lemma_ishr_nth_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x:natN (pow2 n)) (y:nat).{:pattern (ishr #m x y)}
    (forall (i:nat{i < n}).{:pattern (nth #n (ishr #m x y) i)}
      nth #n (ishr #m x y) i == (i - y >= 0 && nth #n x (i - y))))

val reveal_iand_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x y:natN (pow2 n)).{:pattern (iand #m x y)}
    iand #m x y == UInt.logand #n x y)

val reveal_ixor_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x y:natN (pow2 n)).{:pattern (ixor #m x y)}
    ixor #m x y == UInt.logxor #n x y)

val reveal_ior_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x y:natN (pow2 n)).{:pattern (ior #m x y)}
    ior #m x y == UInt.logor #n x y)

val reveal_inot_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x:natN (pow2 n)).{:pattern (inot #m x)}
    inot #m x == UInt.lognot #n x)

val reveal_ishl_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x:natN (pow2 n)) (y:nat).{:pattern (ishl #m x y)}
    ishl #m x y == UInt.shift_left #n x y)

val reveal_ishr_all (n:pos) : Lemma
  (forall (m:_{m==pow2_norm n}) (x:natN (pow2 n)) (y:nat).{:pattern (ishr #m x y)}
    ishr #m x y == UInt.shift_right #n x y)

val lemma_nat32_xor_commutes (x y:nat32) : Lemma
  (nat32_xor x y = nat32_xor y x)

val lemma_nat32_xor_commutes_forall (_:unit) : Lemma
  (forall (x y:nat32) . nat32_xor x y = nat32_xor y x)

val lemma_quad32_xor_commutes (x y:quad32) :Lemma
  (quad32_xor x y = quad32_xor y x)

val lemma_quad32_xor_commutes_forall (_:unit) : Lemma
  (forall (x y:quad32) . {:pattern (quad32_xor x y)} quad32_xor x y = quad32_xor y x)

val lemma_quad32_xor_associates (x y z:quad32) : Lemma
  (quad32_xor (quad32_xor x y) z == (quad32_xor x (quad32_xor y z)))

val lemma_iand_pow2 (n:pos) (x:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (pow2 i < pow2 n /\ (iand x (pow2 i) == 0 \/ iand x (pow2 i) == pow2 i))

val lemma_ishr_pow2_diff (n:pos) (i:nat{i < n}) (j:nat{i <= j /\ j < n}) : Lemma
  (pow2 j < pow2 n /\ ishr #(pow2 n) (pow2 j) (j - i) == pow2 i)

let not (b:bool) : bool = if b then false else true

val lemma_iand_maybe_pow2 (n:pos) (x y:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (requires (x == 0 \/ x == pow2 i) /\ (y == 0 \/ y == pow2 i))
  (ensures not (iand x y = 0) <==> not (x = 0) /\ not (y = 0))

val lemma_iand_pow2_64 (x:nat64) (i:nat{i < 64}) : Lemma
  (pow2 i < pow2 64 /\ (iand x (pow2 i) == 0 \/ iand x (pow2 i) == pow2 i))

val lemma_ishr_pow2_diff64 (i:nat{i < 64}) (j:nat) : Lemma
  (requires i <= j /\ j < 64)
  (ensures pow2 j < pow2 64 /\ ishr #(pow2 64) (pow2 j) (j - i) == pow2 i)

val lemma_ishr_zero64 (i:nat{i < 64}) : Lemma
  (ishr #(pow2 64) 0 i == 0)

val lemma_iand_maybe_pow2_64 (x y:nat64) (i:nat{i < 64}) : Lemma
  (requires (x == 0 \/ x == pow2 i) /\ (y == 0 \/ y == pow2 i))
  (ensures not (iand x y = 0) <==> not (x = 0) /\ not (y = 0))
