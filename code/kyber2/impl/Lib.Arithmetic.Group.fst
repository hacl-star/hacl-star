module Lib.Arithmetic.Group

open FStar.Math.Lemmas
open FStar.Mul
open FStar.Classical
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas


class monoid (a:Type0) = {
  id: a;
  op: a -> a -> a;
  lemma_assoc : (x:a) -> (y:a) -> (z:a) -> Lemma (op (op x y) z == op x (op y z));
  lemma_id1: (x:a) -> Lemma (op id x == x);
  lemma_id2: (x:a) -> Lemma (op x id == x);
}

class commutative_monoid (a:Type0) = {
  bm: monoid a;
  lemma_swap_m: (x:a) -> (y:a) -> Lemma(bm.op x y == bm.op y x);
}

instance monoid_plus_int : monoid int =
  { id = 0;
    op = ( + );
    lemma_assoc = (fun x y z -> ());
    lemma_id1 = (fun x -> ());
    lemma_id2 = (fun x -> ());
   }

instance monoid_mul_int : monoid int =
 { id = 1;
   op = ( * );
   lemma_assoc = (fun x y z -> ());
   lemma_id1 = (fun x -> ());
   lemma_id2 = (fun x -> ());
  }

instance monoid_plus_nat : monoid nat =
   { id = 0;
    op = (fun (x:nat) (y:nat) -> x + y);
    lemma_assoc = (fun x y z -> ());
    lemma_id1 = (fun x -> ());
    lemma_id2 = (fun x -> ());
   }

instance monoid_mul_nat : monoid nat =
 { id = 1;
   op = (fun (x:nat) (y:nat) -> x * y);
   lemma_assoc = (fun x y z -> ());
   lemma_id1 = (fun x -> ());
   lemma_id2 = (fun x -> ());
  }

instance monoid_plus_mod : (#q:pos) -> monoid (field q) =
  fun #q -> {
    id = 0;
    op = modular_add;
    lemma_assoc = modular_add_associativity_lemma;
    lemma_id1 = (fun x -> ());
    lemma_id2 = (fun x -> ());
   }

instance monoid_mul_mod : (#q:pos) -> monoid (field q) =
  fun #q -> {
    id = if q = 1 then 0 else 1;
    op = modular_mul;
    lemma_assoc = modular_mul_associativity_lemma;
    lemma_id1 = (fun x -> ());
    lemma_id2 = (fun x -> ());
  }

let has_sym (#a:Type0) [| monoid a |] (x:a) : Type0 = (exists (y:a). op x y == id /\ op y x == id)

let lemma_op_eq1_m_witness (#a:Type0) [| monoid a |] (x:a) (symx:a{op symx x == id}) (y:a) (z:a) : Lemma (requires (op x y == op x z)) (ensures y == z) =
  lemma_assoc (symx) x y;
  lemma_assoc (symx) x z;
  lemma_id1 y;
  lemma_id1 z

#reset-options
let lemma_op_eq2_m_witness (#a:Type0) [| monoid a |] (x:a) (symx:a{op x symx == id}) (y:a) (z:a) : Lemma (requires op y x == op z x) (ensures y == z) =
  lemma_assoc y x (symx);
  lemma_assoc z x (symx);
  lemma_id2 y;
  lemma_id2 z


let lemma_op_eq1_m (#a:Type0) [| monoid a |] (x:a{has_sym x}) (y:a) (z:a) : Lemma (requires op x y == op x z) (ensures y == z) =
  let _lemma_p (symx:a) : Type = (op symx x == id) in
  let _lemma_r : Type = (y == z) in
  let _lemma_forall_to_exists (symx:a) : Lemma (_lemma_p symx ==> _lemma_r) =
    let _lemma (symx:a) : Lemma (requires _lemma_p symx) (ensures _lemma_r) =
      lemma_op_eq1_m_witness x symx y z in
    move_requires #a #_lemma_p #(fun (x:a) -> _lemma_r) _lemma symx
 in FStar.Classical.forall_to_exists _lemma_forall_to_exists

let lemma_op_eq2_m (#a:Type0) [| monoid a |] (x:a{has_sym x}) (y:a) (z:a) : Lemma (requires op y x == op z x) (ensures y == z) =
  let _lemma_p (symx:a) : Type = (op x symx == id) in
  let _lemma_r : Type = (y == z) in
  let _lemma_forall_to_exists (symx:a) : Lemma (_lemma_p symx ==> _lemma_r) =
    let _lemma (symx:a) : Lemma (requires _lemma_p symx) (ensures _lemma_r) =
      lemma_op_eq2_m_witness x symx y z in
    move_requires #a #_lemma_p #(fun (x:a) -> _lemma_r) _lemma symx
 in FStar.Classical.forall_to_exists _lemma_forall_to_exists

class group (a:Type0) = {
  m: monoid a;
  sym: a -> a;
  lemma_sym1: (x:a) -> Lemma (m.op x (sym x) == m.id);
  lemma_sym2: (x:a) -> Lemma (m.op (sym x) x == m.id);
}

let lemma_op_eq1 (#a:Type0) [| group a |] (x:a) (y:a) (z:a) : Lemma (requires m.op x y == m.op x z) (ensures y == z) =
  lemma_sym2 x;
  lemma_op_eq1_m_witness #a #m x (sym #a x) y z

let lemma_op_eq2 (#a:Type0) [| group a |] (x:a) (y:a) (z:a) : Lemma (requires m.op y x == m.op z x) (ensures y == z) =
  lemma_sym1 x;
  lemma_op_eq2_m_witness #a #m x (sym #a x) y z

let lemma_sym_involutive (#a:Type0) [| group a |] (x:a) : Lemma (ensures sym (sym x) == x) =
  lemma_sym1 (sym x);
  lemma_sym2 x;
  lemma_op_eq1 (sym x) (sym (sym x)) x

#reset-options
let lemma_sym_expand (#a:Type0) [| group a |] (x:a) (y:a) : Lemma (ensures sym (m.op x y) == m.op (sym y) (sym x)) =
  let m = m #a in
  lemma_sym1 (op x y);
  lemma_assoc x y ((op (sym y) (sym x)));
  lemma_assoc y (sym y) (sym x);
  lemma_sym1 y;
  lemma_id1 (sym x);
  lemma_sym1 x;
  lemma_op_eq1 (op x y) (sym (op x y)) (op (sym y) (sym x))

instance group_int : group int = {
  m = monoid_plus_int;
  sym = (fun x -> - x);
  lemma_sym1 = (fun x -> ());
  lemma_sym2 = (fun x -> ());
}

instance group_mod : (#q:pos) -> group (field q) =
  fun #q -> {
    m = monoid_plus_mod;
    sym = modular_sub #q 0;
    lemma_sym1 = (fun x -> assert_norm(x+(-x)=0));
    lemma_sym2 = (fun x -> assert_norm(x+(-x)=0));
}

class abelian_group (a:Type0) = {
  g: group a;
  lemma_swap: (x:a) -> (y:a) -> Lemma (g.m.op x y == g.m.op y x)
}

instance abelian_group_int : abelian_group int = {
  g = group_int;
  lemma_swap = (fun x y -> ());
}

instance abelian_group_mod : (#q:pos) -> abelian_group (field q) =
  fun #q -> {
    g = group_mod;
    lemma_swap = modular_add_swap_lemma;
 }


let rec repeat_op (#a:Type0) [| monoid a |] (x:a) (n:nat) : Tot a (decreases n) =
  if n=0 then id else let b = repeat_op x (n/2) in let b2 = op b b in if n%2 = 0 then b2 else op x b2

#reset-options
let rec lemma_repeat_op_succ1 (#a:Type0) [| monoid a |] (x:a) (n:nat) : Lemma (ensures repeat_op x (n+1) == op x (repeat_op x n)) (decreases n) =
  if n=0 then lemma_id1 #a id else
  if n%2 = 0 then begin
    assert(n/2 == (n+1)/2)
  end
  else begin
    assert(n/2 + 1 == (n+1)/2);
    let b1 = repeat_op x (n/2) in
    let b2 = repeat_op x ((n+1)/2) in
    lemma_repeat_op_succ1 x (n/2);
    lemma_repeat_op_succ2 x (n/2);
    assert (b2 == op x b1);
    assert (b2 == op b1 x);
    let r1 = repeat_op x n in
    let r2 = repeat_op x (n+1) in
    lemma_repeat_op_succ2 x (n-1);
    assert (r1 == op (repeat_op x (n-1)) x);
    assert (r2 == op (op x b1) (op b1 x));
    lemma_assoc x b1 (op b1 x);
    lemma_assoc b1 b1 x;
    assert (r2 == op x (op (op b1 b1) x));
    assert ((n-1)%2 = 0);
    if (n-1 = 0) then lemma_id1 #a id;
    assert (r1 == op (op b1 b1) x)
    end
and lemma_repeat_op_succ2 (#a:Type0) [| monoid a |] (x:a) (n:nat) : Lemma (ensures repeat_op x (n+1) == op (repeat_op x n) x) (decreases n) =
  if n=0 then (lemma_id1 #a id; lemma_id1 x; lemma_id2 x) else
  if n%2 = 0 then begin
  let r0 = repeat_op x (n-1) in
  let r1 = repeat_op x n in
  let r2 = repeat_op x (n+1) in
  let b0 = repeat_op x ((n-1)/2) in
  assert (r0 == op x (op b0 b0));
  let b1 = repeat_op x (n/2) in
  lemma_repeat_op_succ1 x ((n-1)/2);
  lemma_repeat_op_succ2 x ((n-1)/2);
  assert(b1 == op x b0);
  assert(b1 == op b0 x);
  assert(r2 == op x (op b1 b1));
  assert(r2 == op x (op (op x b0) (op b0 x)));
  lemma_assoc x b0 (op b0 x);
  assert(r2 == op x (op x (op b0 (op b0 x))));
  lemma_assoc b0 b0 x;
  assert(r2 == op x (op x (op (op b0 b0) x)));
  lemma_assoc x (op b0 b0) x;
  assert(r2 == op x (op (op x (op b0 b0)) x));
  assert(r2 == op x (op r0 x));
  lemma_assoc x r0 x;
  assert (r2 == op (op x r0) x);
  lemma_repeat_op_succ1 x (n-1)
  end
  else begin
    assert(n/2 + 1 == (n+1)/2);
    let b1 = repeat_op x (n/2) in
    let b2 = repeat_op x ((n+1)/2) in
    lemma_repeat_op_succ1 x (n/2);
    lemma_repeat_op_succ2 x (n/2);
    assert (b2 == op x b1);
    assert (b2 == op b1 x);
    let r1 = repeat_op x n in
    let r2 = repeat_op x (n+1) in
    lemma_repeat_op_succ2 x (n-1);
    assert (r1 == op (repeat_op x (n-1)) x);
    assert (r2 == op (op x b1) (op b1 x));
    lemma_assoc x b1 (op b1 x);
    lemma_assoc b1 b1 x;
    assert (r2 == op x (op (op b1 b1) x));
    lemma_assoc x (op b1 b1) x
    end

let lemma_repeat_op_zero (#a:Type0) [| monoid a |] (x:a) : Lemma (repeat_op x 0 == id) = ()
let rec lemma_repeat_op_one (#a:Type0) [| monoid a |] (x:a) : Lemma (repeat_op x 1 == x) =
  lemma_id1 #a id;
  lemma_id2 x

let rec lemma_repeat_op_morphism (#a:Type0) [| monoid a |] (x:a) (n:nat) (m:nat) : Lemma (ensures repeat_op x (n+m) == op (repeat_op x n) (repeat_op x m)) (decreases m) =
  if (m=0) then lemma_id2 (repeat_op x n)
  else begin
    lemma_repeat_op_morphism x (n+1) (m-1);
    lemma_repeat_op_succ2 x n;
    lemma_assoc (repeat_op x n) x (repeat_op x (m-1));
    lemma_repeat_op_succ1 x (m-1)
    end

let rec lemma_repeat_op_id (#a:Type0) [| monoid a |] (n:nat) : Lemma (ensures repeat_op #a id n == id) (decreases n) =
  if n=0 then ()
  else begin
    lemma_repeat_op_succ1 #a id (n-1);
    lemma_repeat_op_id #a (n-1);
    lemma_id1 #a id
    end
#reset-options
let rec lemma_repeat_op_sym (#a:Type0) [| monoid a |] (x:a) (y:a{op x y == id}) (n:nat) : Lemma (ensures op (repeat_op x n) (repeat_op #a y n) == id) (decreases n) =
  if n=0 then lemma_id1 #a id
  else begin
    let r = op (repeat_op x n) (repeat_op #a y n) in
    lemma_repeat_op_succ2 x (n-1);
    assert(r == op (op (repeat_op x (n-1)) x) (repeat_op #a y n));
    lemma_assoc (repeat_op x (n-1)) x (repeat_op #a y n);
    lemma_repeat_op_succ1 #a y (n-1);
    lemma_assoc x y (repeat_op #a y (n-1));
    lemma_id1 #a (repeat_op y (n-1));
    lemma_repeat_op_sym x y (n-1)
    end

#reset-options
let rec lemma_repeat_repeat_op (#a:Type0) [| monoid a |] (x:a) (n:nat) (m:nat) : Lemma (ensures repeat_op x (n*m) == repeat_op (repeat_op x n) m) (decreases m) =
  if m = 0 then ()
  else begin
    let r = repeat_op x (n*m) in
    assert (n*m = n + n*(m-1));
    lemma_repeat_op_morphism x n (n*(m-1));
    assert(r== op (repeat_op x n) (repeat_op x (n*(m-1))));
    lemma_repeat_repeat_op x n (m-1);
    assert (r == op (repeat_op x n) (repeat_op (repeat_op x n) (m-1)));
    lemma_repeat_op_succ1 (repeat_op x n) (m-1);
    assert (r == repeat_op (repeat_op x n) m)
    end

#reset-options
let lemma_simpl_repeat_op (#a:Type0) [| monoid a |] (x:a) (n:pos) (m:nat) : Lemma (requires repeat_op x n == id) (ensures repeat_op x m == repeat_op x (m%n)) =
    euclidean_division_definition m n;
    lemma_repeat_op_morphism x ((m/n)*n) (m%n);
    lemma_repeat_repeat_op x n (m/n);
    lemma_repeat_op_id #a (m/n);
    lemma_id1 (repeat_op x (m%n))

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"
let lemma_simpl_repeat_op_with_sym1 (#a:Type0) [| monoid a |] (x:a) (symx:a) (n:pos) (j:nat) (k:nat) : Lemma (requires repeat_op x n == id /\ op x symx == id) (ensures op (repeat_op x j) (repeat_op symx k) == repeat_op x ((j-k)%n)) =
  let k' = k%n in
  lemma_repeat_op_sym x symx n;
  lemma_id1 (repeat_op symx n);
  lemma_simpl_repeat_op symx n k;
  lemma_id1 (repeat_op symx k');
  lemma_repeat_op_morphism x (n-k') k';
  lemma_assoc (repeat_op x (n-k')) (repeat_op x k') (repeat_op symx k');
  lemma_repeat_op_sym x symx k';
  lemma_id2 (repeat_op x (n-k'));
  assert(repeat_op symx k == repeat_op x (n-k'));
  lemma_repeat_op_morphism x j (n-k');
  lemma_simpl_repeat_op x n (j + (n - k'));
  euclidean_division_definition k n;
  subtraction_is_distributive n k ((k/n)*n);
  modulo_addition_lemma (j-k) n (1+(k/n))

let lemma_simpl_repeat_op_with_sym2 (#a:Type0) [| monoid a |] (x:a) (symx:a) (n:pos) (j:nat) (k:nat) : Lemma (requires repeat_op x n == id /\ op symx x == id) (ensures op (repeat_op symx j) (repeat_op x k) == repeat_op x ((k-j)%n)) =
  let j' = j%n in
  lemma_repeat_op_sym symx x n;
  lemma_id2 (repeat_op symx n);
  lemma_simpl_repeat_op symx n j;
  lemma_id2 (repeat_op symx j');
  lemma_repeat_op_morphism x j' (n-j');
  lemma_assoc (repeat_op symx j') (repeat_op x j') (repeat_op x (n-j'));
  lemma_repeat_op_sym symx x j';
  lemma_id1 (repeat_op x (n-j'));
  assert(repeat_op symx j == repeat_op x (n-j'));
  lemma_repeat_op_morphism x (n-j') k;
  lemma_simpl_repeat_op x n ((n - j')+k);
  euclidean_division_definition j n;
  subtraction_is_distributive n j ((j/n)*n);
  modulo_addition_lemma (k-j) n (1+(j/n))

let rec lemma_repeat_op_swap (#a:Type0) [| monoid a |] (x:a) (y:a) (n:nat) : Lemma (requires op x y == op y x) (ensures op (repeat_op x n) y == op y (repeat_op x n)) (decreases n) =
  if n=0 then (lemma_repeat_op_zero x; lemma_id1 y; lemma_id2 y)
  else begin
    lemma_repeat_op_succ1 x (n-1);
    lemma_assoc x (repeat_op x (n-1)) y;
    lemma_repeat_op_swap #a x y (n-1);
    lemma_assoc x y (repeat_op x (n-1));
    lemma_assoc y x (repeat_op x (n-1));
    lemma_repeat_op_succ1 x (n-1)
    end
