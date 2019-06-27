module Vale.Arch.TypesNative

let lemma_equal_nth n x y =
  UInt.to_vec_lemma_2 #n x y

let lemma_zero_nth n =
  let f (i:nat{i < n}) : Lemma (not (nth #n 0 i)) = UInt.zero_nth_lemma #n i in
  FStar.Classical.forall_intro f //(UInt.zero_nth_lemma #n)

let lemma_quad32_vec_equal a b =
  let Mkfour a0 a1 a2 a3 = a in
  let Mkfour b0 b1 b2 b3 = b in
  UInt.to_vec_lemma_2 #32 a0 b0;
  UInt.to_vec_lemma_2 #32 a1 b1;
  UInt.to_vec_lemma_2 #32 a2 b2;
  UInt.to_vec_lemma_2 #32 a3 b3;
  ()

#push-options "--z3rlimit 60 --z3refresh"
let lemma_iand_nth_i n x y i =
  reveal_iand n x y

let lemma_ixor_nth_i n x y i =
  reveal_ixor n x y

let lemma_ior_nth_i n x y i =
  reveal_ior n x y

let lemma_inot_nth_i n x i =
  reveal_inot n x

let lemma_ishl_nth_i n x y i =
  reveal_ishl n x y

let lemma_ishr_nth_i n x y i =
  reveal_ishr n x y

let lemma_iand_nth n x y =
  FStar.Classical.forall_intro (lemma_iand_nth_i n x y)

let lemma_ixor_nth n x y =
  FStar.Classical.forall_intro (lemma_ixor_nth_i n x y)

let lemma_ior_nth n x y =
  FStar.Classical.forall_intro (lemma_ior_nth_i n x y)

let lemma_inot_nth n x =
  FStar.Classical.forall_intro (lemma_inot_nth_i n x)

let lemma_ishl_nth n x y =
  FStar.Classical.forall_intro (lemma_ishl_nth_i n x y)

let lemma_ishr_nth n x y =
  FStar.Classical.forall_intro (lemma_ishr_nth_i n x y)

let lemma_iand_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_iand_nth n)

let lemma_ixor_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ixor_nth n)

let lemma_ior_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ior_nth n)

let lemma_inot_nth_all n =
  FStar.Classical.forall_intro (lemma_inot_nth n)

let lemma_ishl_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ishl_nth n)

let lemma_ishr_nth_all n =
  FStar.Classical.forall_intro_2 (lemma_ishr_nth n)

let reveal_iand_all n =
  FStar.Classical.forall_intro_2 (reveal_iand n)

let reveal_ixor_all n =
  FStar.Classical.forall_intro_2 (reveal_ixor n)

let reveal_ior_all n =
  FStar.Classical.forall_intro_2 (reveal_ior n)

let reveal_inot_all n =
  FStar.Classical.forall_intro (reveal_inot n)

let reveal_ishl_all n =
  FStar.Classical.forall_intro_2 (reveal_ishl n)

let reveal_ishr_all n =
  FStar.Classical.forall_intro_2 (reveal_ishr n)
#pop-options

let lemma_nat32_xor_commutes (x y:nat32) : Lemma
  (nat32_xor x y = nat32_xor y x)
  =
  reveal_ixor 32 x y;
  assert (nat32_xor x y = FStar.UInt.logxor #32 x y);
  FStar.UInt.logxor_commutative #32 x y;
  assert (FStar.UInt.logxor #32 x y = FStar.UInt.logxor #32 y x);
  reveal_ixor 32 y x;
  assert (nat32_xor y x = FStar.UInt.logxor #32 y x);
  ()

let lemma_nat32_xor_commutes_forall () : Lemma
  (forall (x y:nat32) . nat32_xor x y = nat32_xor y x)
  =
  FStar.Classical.forall_intro_2 lemma_nat32_xor_commutes

let lemma_quad32_xor_commutes (x y:quad32) :Lemma
  (quad32_xor x y = quad32_xor y x)
  =
  //lemma_nat32_xor_commutes_forall() // REVIEW: Why doesn't this work?
  Vale.Def.Opaque_s.reveal_opaque quad32_xor_def;
  let Mkfour x0 x1 x2 x3 = x in
  let Mkfour y0 y1 y2 y3 = y in
  lemma_nat32_xor_commutes x0 y0;
  lemma_nat32_xor_commutes x1 y1;
  lemma_nat32_xor_commutes x2 y2;
  lemma_nat32_xor_commutes x3 y3;
  ()

let lemma_quad32_xor_commutes_forall () : Lemma
  (forall (x y:quad32) . {:pattern (quad32_xor x y)} quad32_xor x y = quad32_xor y x)
  =
  FStar.Classical.forall_intro_2 lemma_quad32_xor_commutes


let lemma_nat32_xor_associates (x y z:nat32) : Lemma
  (nat32_xor (nat32_xor x y) z = nat32_xor x (nat32_xor y z))
  =
  reveal_ixor 32 x y;
  reveal_ixor 32 y z;
  reveal_ixor 32 (nat32_xor x y) z;
  reveal_ixor 32 x (nat32_xor y z);
  FStar.UInt.logxor_associative #32 x y z;
  ()

let lemma_quad32_xor_associates (x y z:quad32) : Lemma
  (quad32_xor (quad32_xor x y) z == (quad32_xor x (quad32_xor y z)))
  =
  Vale.Def.Opaque_s.reveal_opaque quad32_xor_def;
  let Mkfour x0 x1 x2 x3 = x in
  let Mkfour y0 y1 y2 y3 = y in
  let Mkfour z0 z1 z2 z3 = z in
  lemma_nat32_xor_associates x0 y0 z0;
  lemma_nat32_xor_associates x1 y1 z1;
  lemma_nat32_xor_associates x2 y2 z2;
  lemma_nat32_xor_associates x3 y3 z3;
  ()

let lemma_iand_pow2 (n:pos) (x:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (pow2 i < pow2 n /\ (iand x (pow2 i) == 0 \/ iand x (pow2 i) == pow2 i))
  =
  let open FStar.UInt in
  FStar.Math.Lemmas.pow2_lt_compat n i;
  assert (pow2 i < pow2 n);
  let result = iand x (pow2 i) in

  if nth #n x (n - i - 1) then (
    let helper (j:nat{j < n}) : Lemma (nth #n result j = nth #n (pow2 i) j)
        =
        pow2_nth_lemma #n i j;
        lemma_iand_nth_i n x (pow2 i) j;
        assert (nth #n result j = (nth #n x j && nth #n (pow2 i) j));
        ()
    in
    FStar.Classical.forall_intro helper;
    nth_lemma #n result (pow2 i);
    assert(iand x (pow2 i) == pow2 i);
    ()
  ) else (
    let helper (j:nat{j < n}) : Lemma (nth #n result j = false)
        =
        pow2_nth_lemma #n i j;
        lemma_iand_nth_i n x (pow2 i) j;
        assert (nth #n result j = (nth #n x j && nth #n (pow2 i) j));
        ()
    in
    FStar.Classical.forall_intro helper;
    nth_lemma #n (zero n) result;
    assert(iand x (pow2 i) == 0);
    ()
  );
  ()

#set-options "--max_fuel 1 --max_ifuel 0"
let lemma_ishr_pow2_diff (n:pos) (i:nat{i < n}) (j:nat{i <= j /\ j < n}) : Lemma
  (pow2 j < pow2 n /\ ishr #(pow2 n) (pow2 j) (j - i) == pow2 i)
  =
  FStar.Math.Lemmas.pow2_lt_compat n i;
  FStar.Math.Lemmas.pow2_lt_compat n j;
  let open FStar.UInt in
  let result = ishr #(pow2 n) (pow2 j) (j - i) in
  let helper (k:nat{k < n}) : Lemma (nth #n result k == nth #n (pow2 i) k) =
    reveal_ishr_all n;
    pow2_nth_lemma #n j k;
    pow2_nth_lemma #n i k;
    if k < (j - i) then (
      shift_right_lemma_1 #n (pow2 j) (j - i) k;
      ()
    ) else (
      shift_right_lemma_2 #n (pow2 j) (j - i) k;
      assert (nth #n result k = nth #n (pow2 j) (k - (j - i)));
      ()
    )
    ;
    ()
  in
  FStar.Classical.forall_intro helper;
  nth_lemma #n result (pow2 i);
  ()

let lemma_iand_maybe_pow2 (n:pos) (x y:natN (pow2 n)) (i:nat{i < n}) : Lemma
  (requires (x == 0 \/ x == pow2 i) /\ (y == 0 \/ y == pow2 i))
  (ensures not (iand x y = 0) <==> not (x = 0) /\ not (y = 0))
  =
  let open FStar.UInt in
  reveal_iand_all n;
  let result = iand x y in
  (* Prove ==> *)
  if not (iand x y = 0) then (
    if x = 0 then (
      assert (x = zero n);
      logand_commutative #n x y;
      logand_lemma_1 #n y;
      assert (iand x y = 0)
    ) else ()
    ;
    assert (not (x = 0));
    if y = 0 then (
      assert (y = zero n);
      logand_commutative #n x y;
      logand_lemma_1 #n x;
      assert (iand x y = 0)
    ) else ()
    ;
    assert (not (y = 0));
    ()
  ) else ()
  ;
  (* Prove <== *)
  if not (x = 0) && not (y = 0) then (
    assert (x = pow2 i /\ y = pow2 i);
    logand_self #n (pow2 i);
    assert (result = pow2 i)
  ) else ()
  ;
  ()

let lemma_iand_pow2_64 (x:nat64) (i:nat{i < 64}) : Lemma
  (pow2 i < pow2 64 /\ (iand x (pow2 i) == 0 \/ iand x (pow2 i) == pow2 i))
  =
  lemma_iand_pow2 64 x i

let lemma_ishr_pow2_diff64 (i:nat{i < 64}) (j:nat) : Lemma
  (requires i <= j /\ j < 64)
  (ensures pow2 j < pow2 64 /\ ishr #(pow2 64) (pow2 j) (j - i) == pow2 i)
  =
  lemma_ishr_pow2_diff 64 i j

let lemma_ishr_zero64 (i:nat{i < 64}) : Lemma
  (ishr #(pow2 64) 0 i == 0)
  =
  reveal_ishr_all 64;
  FStar.UInt.shift_right_value_lemma #64 0 i;
  assert (ishr #(pow2 64) 0 i = 0 / (pow2 i));
  FStar.Math.Lemmas.small_division_lemma_1 0 (pow2 i); // Prove that 0 / pow2 i == 0
  ()

let lemma_iand_maybe_pow2_64 (x y:nat64) (i:nat{i < 64}) : Lemma
  (requires (x == 0 \/ x == pow2 i) /\ (y == 0 \/ y == pow2 i))
  (ensures not (iand x y = 0) <==> not (x = 0) /\ not (y = 0))
  =
  lemma_iand_maybe_pow2 64 x y i
