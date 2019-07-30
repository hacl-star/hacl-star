module Lib.Arithmetic.Ring

open FStar.Math.Lemmas
open FStar.Mul

open Lib.Arithmetic.Group
open Lib.ModularArithmetic.Lemmas
open Lib.ModularArithmetic


#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0 --print_universes --using_facts_from '* -FStar.Seq'"

class ring (a:Type0) = {
  add_ag: abelian_group a;
  mul_m: monoid a;
  lemma_distr_left: (x:a) -> (y:a) -> (z:a) -> Lemma (mul_m.op x (add_ag.g.m.op y z) == add_ag.g.m.op (mul_m.op x y) (mul_m.op x z));
  lemma_distr_right: (x:a) -> (y:a) -> (z:a) -> Lemma (mul_m.op (add_ag.g.m.op y z) x == add_ag.g.m.op (mul_m.op y x) (mul_m.op z x));
}

class commutative_ring (a:Type0) = {
  r:ring a;
  lemma_mul_swap: (x:a) -> (y:a) -> Lemma (r.mul_m.op x y == r.mul_m.op y x);
}

let zero (#a:Type0) [|ring a|] : a = add_ag.g.m.id

let one (#a:Type0) [|ring a |] : a = mul_m.id

let plus (#a:Type0) [|ring a|] : a -> a -> a = add_ag.g.m.op

let opp (#a:Type0) [|ring a|] : a -> a = add_ag.g.sym

let minus (#a:Type0) [|ring a|] (x:a) (y:a) : a = plus x (opp y)

let mul (#a:Type0) [|ring a|] : a -> a -> a = mul_m.op

let lemma_plus_assoc (#a:Type0) [|ring a |] (x:a) (y:a) (z:a) : Lemma (plus (plus x y) z == plus x (plus y z)) =
  add_ag.g.m.lemma_assoc x y z

let lemma_plus_swap (#a:Type0) [|ring a|] (x:a) (y:a) : Lemma (plus x y == plus y x) =
  add_ag.lemma_swap x y

let lemma_plus_opp1 (#a:Type0) [| ring a |] (x:a) : Lemma (plus x (opp x) == zero) =
  add_ag.g.lemma_sym1 x

let lemma_plus_opp2 (#a:Type0) [| ring a |] (x:a) : Lemma (plus (opp x) x == zero) =
  add_ag.g.lemma_sym2 x

let lemma_plus_eq1 (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (requires plus x y == plus x z) (ensures y == z) = lemma_op_eq1 #a #add_ag.g x y z

let lemma_plus_eq2 (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (requires plus y x == plus z x) (ensures y == z) = lemma_op_eq2 #a #add_ag.g x y z

let lemma_mul_assoc (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (mul (mul x y) z == mul x (mul y z)) =
  mul_m.lemma_assoc x y z

let lemma_zero1 (#a:Type0) [| ring a |] (x:a) : Lemma (plus zero x == x) =
  add_ag.g.m.lemma_id1 x

let lemma_zero2 (#a:Type0) [| ring a |] (x:a) : Lemma (plus x zero == x) =
  add_ag.g.m.lemma_id2 x

let lemma_one1 (#a:Type0) [| ring a |] (x:a) : Lemma (mul one x == x) =
  mul_m.lemma_id1 x

let lemma_one2 (#a:Type0) [| ring a |] (x:a) : Lemma (mul x one == x) =
  mul_m.lemma_id2 x

let lemma_zero_absorb1 (#a:Type0) [|ring a|] (x:a) : Lemma (mul zero x == zero) =
  lemma_zero1 (mul x x);
  lemma_zero1 x;
  lemma_distr_right x zero x;
  lemma_plus_opp1 (mul x x);
  lemma_plus_assoc (mul zero x) (mul x x) (opp (mul x x));
  lemma_zero2 (mul zero x)

let lemma_zero_absorb2 (#a:Type0) [|ring a|] (x:a) : Lemma (mul x zero == zero) =
  lemma_zero2 (mul x x);
  lemma_zero2 x;
  lemma_distr_left x x zero;
  lemma_plus_opp2 (mul x x);
  lemma_plus_assoc (opp (mul x x)) (mul x x) (mul x zero);
  lemma_zero1 (mul x zero)

let lemma_mul_opp1 (#a:Type0) [| ring a |] (x:a) (y:a) : Lemma (opp (mul x y) == mul (opp x) y) =
  lemma_distr_right y x (opp x);
  lemma_plus_opp1 x;
  lemma_zero_absorb1 y;
  lemma_plus_opp1 (mul x y);
  lemma_plus_eq1 (mul x y) (opp (mul x y)) (mul (opp x) y)

let lemma_mul_opp2 (#a:Type0) [| ring a |] (x:a) (y:a) : Lemma (opp (mul x y) == mul x (opp y)) =
  lemma_distr_left x y (opp y);
  lemma_plus_opp1 y;
  lemma_zero_absorb2 x;
  lemma_plus_opp1 (mul x y);
  lemma_plus_eq1 (mul x y) (opp (mul x y)) (mul x (opp y))

let lemma_mul_opp_swap (#a:Type0) [| ring a |] (x:a) (y:a) : Lemma (mul (opp x) y == mul x (opp y)) =
  lemma_mul_opp1 x y;
  lemma_mul_opp2 x y

let lemma_mul_double_opp (#a:Type0) [| ring a |] (x:a) (y:a) : Lemma (mul (opp x) (opp y) == mul x y) =
  lemma_mul_opp_swap x (opp y);
  lemma_sym_involutive #a #add_ag.g y

let lemma_minus_assoc1 (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (plus x (minus y z) == minus (plus x y) z) =
  lemma_plus_assoc x y (opp z)

let lemma_minus_assoc2 (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (minus x (minus y z) == plus x (minus z y)) =
  let g = (add_ag #a).g in
  lemma_sym_expand y (opp z);
  lemma_sym_involutive z;
  lemma_plus_assoc x z (opp y)

let lemma_minus_assoc3 (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (minus x (plus y z) == minus (minus x z) y) =
  let g = (add_ag #a).g in
  lemma_sym_expand y z;
  lemma_plus_assoc x (opp z) (opp y)

let lemma_minus_mul_distr_left (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (mul x (minus y z) == minus (mul x y) (mul x z)) =
  lemma_distr_left x y (opp z);
  lemma_mul_opp2 x z

let lemma_minus_mul_distr_right (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (mul (minus y z) x == minus (mul y x) (mul z x)) =
  lemma_distr_right x y (opp z);
  lemma_mul_opp1 z x

instance ring_int : ring int =
  { add_ag = abelian_group_int;
    mul_m = monoid_mul_int;
    lemma_distr_left = distributivity_add_right;
    lemma_distr_right = (fun x y z -> distributivity_add_left y z x);
  }

instance commutative_ring_int : commutative_ring int =
  { r = ring_int;
    lemma_mul_swap = (fun x y -> ());
   }

instance ring_mod : #(q:pos) -> ring (field q) =
  fun #q -> {
    add_ag = abelian_group_mod;
    mul_m = monoid_mul_mod;
    lemma_distr_left = modular_mul_add_distrib_left_lemma;
    lemma_distr_right = (fun x y z -> modular_mul_add_distrib_lemma y z x);
 }

instance commutative_ring_mod : (#q:pos) -> commutative_ring (field q) = 
  fun #q -> {
    r = ring_mod;
    lemma_mul_swap = modular_mul_swap_lemma;
 }


let is_invertible (#a:Type0) [| ring a |] (x:a) : Type0 =
  has_sym #a #mul_m x

let lemma_mul_eq1_m (#a:Type0) [|ring a |] (x:a{is_invertible x}) (y:a) (z:a) : Lemma (requires mul x y == mul x z) (ensures y == z) =
  lemma_op_eq1_m #a #mul_m x y z

let lemma_mul_eq2_m (#a:Type0) [|ring a |] (x:a{is_invertible x}) (y:a) (z:a) : Lemma (requires mul y x == mul z x) (ensures y == z) =
  lemma_op_eq2_m #a #mul_m x y z

let exp (#a:Type0) [| ring a |] = repeat_op #a #mul_m

let lemma_exp_succ1 (#a:Type0) [| ring a |] (x:a) (n:nat) : Lemma (ensures exp x (n+1) == mul x (exp x n)) =
  lemma_repeat_op_succ1 #a #mul_m x n

let lemma_exp_succ2 (#a:Type0) [| ring a |] (x:a) (n:nat) : Lemma (ensures exp x (n+1) == mul (exp x n) x) =
  lemma_repeat_op_succ2 #a #mul_m x n

let lemma_exp_zero (#a:Type0) [| ring a |] (x:a) : Lemma (ensures exp x 0 == one) =
  lemma_repeat_op_zero #a #mul_m x

let lemma_exp_morphism (#a:Type0) [| ring a |] (x:a) (n:nat) (m:nat) : Lemma (ensures exp x (n+m) == mul (exp x n) (exp x m)) =
  lemma_repeat_op_morphism #a #mul_m x n m

let lemma_exp_one (#a:Type0) [| ring a |] (n:nat) : Lemma (exp #a one n == one) =
  lemma_repeat_op_id #a #mul_m n

let lemma_exp_inv (#a:Type0) [| ring a |] (x:a) (y:a{mul x y == one}) (n:nat) : Lemma (ensures mul (exp x n) (exp #a y n) == one) =
  lemma_repeat_op_sym #a #mul_m x y n

let lemma_exp_exp (#a:Type0) [| ring a |] (x:a) (n:nat) (m:nat) : Lemma (ensures exp x (n*m) == exp (exp x n) m) =
  lemma_repeat_repeat_op #a #mul_m x n m

let lemma_simpl_exp (#a:Type0) [| ring a |] (x:a) (n:pos) (m:nat) : Lemma (requires exp x n == one) (ensures exp x m == exp x (m%n)) = lemma_simpl_repeat_op #a #mul_m x n m

let lemma_simpl_exp_with_inv1 (#a:Type0) [| ring a |] (x:a) (invx:a) (n:pos) (j:nat) (k:nat) : Lemma (requires exp x n == one /\ mul x invx == one) (ensures mul (exp x j) (exp invx k) == exp x ((j-k)%n)) = lemma_simpl_repeat_op_with_sym1 #a #mul_m x invx n j k

let lemma_simpl_exp_with_inv2 (#a:Type0) [| ring a |] (x:a) (invx:a) (n:pos) (j:nat) (k:nat) : Lemma (requires exp x n == one /\ mul invx x == one) (ensures mul (exp invx j) (exp x k) == exp x ((k-j)%n)) = lemma_simpl_repeat_op_with_sym2 #a #mul_m x invx n j k

let repeat_plus (#a:Type0) [| ring a |] (x:a) (n:nat) = repeat_op #a #add_ag.g.m x n

let rec lemma_repeat_plus_swap_mul (#a:Type0) [| ring a |] (x:a) (y:a) (n:nat) : Lemma (requires mul x y == mul y x) (ensures mul (repeat_plus x n) y == mul y (repeat_plus x n)) (decreases n) =
  let m = (add_ag #a).g.m in
  if n=0 then (lemma_repeat_op_zero #a #add_ag.g.m x; lemma_zero_absorb1 y; lemma_zero_absorb2 y)
  else begin
    lemma_repeat_op_succ1 x (n-1);
    lemma_distr_right y x (repeat_plus x (n-1));
    lemma_repeat_plus_swap_mul x y (n-1);
    lemma_distr_left y x (repeat_plus x (n-1));
    lemma_repeat_op_succ1 x (n-1)
    end


let lemma_mul_swap_inverse_ (#a:Type0) [| ring a |] (x:a) (y:a) (z:a) : Lemma (requires (forall (b:a). mul x b == mul b x) /\ (mul y x == one \/ mul x y == one)) (ensures mul y z == mul z y) =
  assert(mul x y == one /\ mul y x == one);
  assert(is_invertible x);
  lemma_one1 z;
  lemma_one2 z;
  assert(mul z (mul y x) == mul (mul x y) z);
  lemma_mul_assoc z y x;
  lemma_mul_assoc x y z;
  assert(mul (mul z y) x == mul x (mul y z));
  assert(mul (mul z y) x == mul (mul y z) x);
  lemma_mul_eq2_m x (mul z y) (mul y z)

let lemma_mul_swap_inverse (#a:Type0) [| ring a |] (x:a) (y:a) : Lemma (requires (forall (b:a). mul x b == mul b x) /\ (mul y x == one \/ mul x y == one)) (ensures (forall (b:a). mul y b == mul b y)) =
  let customprop (b:a) : GTot Type0 = (mul y b == mul b y) in
  let customlemma (b:a) : Lemma (customprop b) = lemma_mul_swap_inverse_ x y b in
  FStar.Classical.forall_intro customlemma

let lemma_mul_swap_repeat_plus_one (#a:Type0) [| ring a |] (n:nat) : Lemma (forall (b:a). mul (repeat_plus one n) b == mul b (repeat_plus one n)) =
  let customprop (b:a) : GTot Type0 = (mul (repeat_plus one n) b == mul b (repeat_plus one n)) in
  let customlemma (b:a) : Lemma (customprop b) =
    lemma_one1 b;
    lemma_one2 b;
    lemma_repeat_plus_swap_mul one b n
  in FStar.Classical.forall_intro customlemma

let lemma_mul_swap_inverse_repeat_plus_one (#a:Type0) [| ring a |] (n:nat) (x:a) : Lemma(requires (mul #a x (repeat_plus one n) == one \/ mul (repeat_plus one n) x == one)) (ensures forall (b:a). mul x b == mul b x) =
  lemma_mul_swap_repeat_plus_one #a n;
  lemma_mul_swap_inverse (repeat_plus one n) x
