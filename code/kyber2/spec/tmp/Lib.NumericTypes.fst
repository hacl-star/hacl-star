module Lib.NumericTypes

open Lib.Arithmetic.Group
open Lib.Arithmetic.Group.Sequence
open Lib.Arithmetic.Group.Uint_t

open Lib.Arithmetic.Ring
open Lib.Arithmetic.Ring.Sequence
open Lib.Arithmetic.Ring.Uint_t

open Lib.ModularArithmetic
open Lib.ModularArithmetic.Lemmas
open Lib.IntTypes
open Lib.Sequence

open FStar.Math.Lemmas
open FStar.Mul


noeq
type numeric_t =
  |Base : Type0 -> numeric_t
  |Vec : numeric_t -> size_nat -> numeric_t

val dim: numeric_t -> nat

let rec dim t0 = 
  match t0 with
  |Vec t _ -> 1 + dim t
  |_-> 0

let rec base_t = function
  |Base a -> a
  |Vec a len -> base_t a

type numeric (m:nat) = t:numeric_t{dim t = m}

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_universes --using_facts_from '* -FStar.Seq'"


let rec vector_ (m:nat) (t: numeric 0 -> Type0) (a:numeric m) (len:size_nat) : Type0 = 
  match a with
  |Base _ -> lseq (t a) len
  |Vec a' len' -> lseq (vector_ (m-1) t a' len') len

val interp_numeric: (#m:nat) -> (a:numeric m) -> Tot Type0 (decreases (dim a)) 
let rec interp_numeric #m = function
  |Base t -> t
  |Vec a' len -> lseq (interp_numeric #(m-1) a') len //vector_ (m-1) interp_numeric a' len

type vector_t #a len : Type0 = vector_ (dim a) interp_numeric a len

let rec id_n (#m:nat) (#a:numeric m) (#mono:monoid (base_t a)) : Tot (interp_numeric a) = 
  match a with
  |Base _ -> mono.id
  |Vec a' len -> create len (id_n #(m-1) #a' #mono)

let rec op_n (#m:nat) (#a:numeric m) (#mono:monoid (base_t a)) (x:interp_numeric a) (y:interp_numeric a) : Tot (interp_numeric a) = 
  match a with
    |Base _ -> mono.op x y
    |Vec a' len -> let t = interp_numeric #(m-1) a' in Lib.Sequence.map2 #t #t #t #len (op_n #(m-1) #a' #mono) x y

let rec lemma_assoc_n (#m:nat) (#a:numeric m) (#mono:monoid (base_t a)) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (op_n #m #a #mono (op_n #m #a #mono x y) z == op_n #m #a #mono x (op_n #m #a #mono y z)) =
  match a with
  |Base _ -> mono.lemma_assoc x y z
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let op_n = op_n #m #a #mono in
    let customprop (k:nat{k<len}) : Type0 = (index (op_n (op_n x y) z) k == index (op_n x (op_n y z)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_assoc_n #(m-1) #a' #mono (index x k) (index y k) (index z k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (op_n (op_n x y) z) (op_n x (op_n y z));
    eq_elim #t #len (op_n (op_n x y) z) (op_n x (op_n y z))
    end

let rec lemma_id1_n (#m:nat) (#a:numeric m) (#mono:monoid (base_t a)) (x:interp_numeric a) : Lemma (op_n #m #a #mono (id_n #m #a #mono) x == x) =
  match a with
  |Base _ -> mono.lemma_id1 x
  |Vec a' len -> 
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let op_n = op_n #m #a #mono in
    let id_n = id_n #m #a #mono in
    let customprop (k:nat{k<len}) : Type0 = (index (op_n id_n x) k == index x k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_id1_n #(m-1) #a' #mono (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (op_n id_n x) x;
    eq_elim #t #len (op_n id_n x) x

let rec lemma_id2_n (#m:nat) (#a:numeric m) (#mono:monoid (base_t a)) (x:interp_numeric a) : Lemma (op_n #m #a #mono x (id_n #m #a #mono) == x) =
  match a with
  |Base _ -> mono.lemma_id2 x
  |Vec a' len -> 
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let op_n = op_n #m #a #mono in
    let id_n = id_n #m #a #mono in
    let customprop (k:nat{k<len}) : Type0 = (index (op_n x id_n) k == index x k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_id2_n #(m-1) #a' #mono (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (op_n x id_n) x;
    eq_elim #t #len (op_n x id_n) x

instance monoid_numeric_t: (a:numeric_t) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] m:monoid (base_t a)) -> monoid (interp_numeric #(dim a) a) =
  fun a #m -> {
    id = id_n #(dim a) #a #m;
    op = op_n #(dim a) #a #m;
    lemma_assoc = lemma_assoc_n #(dim a) #a #m;
    lemma_id1 = lemma_id1_n #(dim a) #a #m;
    lemma_id2 = lemma_id2_n #(dim a) #a #m;
  }

let rec sym_n (#m:nat) (#a:numeric m) (#g:group (base_t a)) (x:interp_numeric a) : Tot (interp_numeric a) = 
  match a with
    |Base _ -> g.sym x
    |Vec a' len -> let t = interp_numeric #(m-1) a' in Lib.Sequence.map #t #t #len (sym_n #(m-1) #a' #g) x

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_universes --using_facts_from '* -FStar.Seq'"

let rec lemma_sym1_n (#m:nat) (#a:numeric m) (#g:group (base_t a)) (x:interp_numeric a) : Lemma (op_n #m #a #g.m x (sym_n #m #a #g x) == id_n #m #a #g.m) =
  match a with
  |Base _ -> g.lemma_sym1 x
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let sym_n = sym_n #m #a #g in
    let op_n = op_n #m #a #g.m in
    let id_n = id_n #m #a #g.m in
    let customprop (k:nat{k<len}) : Type0 = ( index (op_n x (sym_n x)) k == index id_n k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_sym1_n #(m-1) #a' #g (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (op_n x (sym_n x)) id_n;
    eq_elim #t #len (op_n x (sym_n x)) id_n
    end

let rec lemma_sym2_n (#m:nat) (#a:numeric m) (#g:group (base_t a)) (x:interp_numeric a) : Lemma (op_n #m #a #g.m (sym_n #m #a #g x) x == id_n #m #a #g.m) =
  match a with
  |Base _ -> g.lemma_sym2 x
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let sym_n = sym_n #m #a #g in
    let op_n = op_n #m #a #g.m in
    let id_n = id_n #m #a #g.m in
    let customprop (k:nat{k<len}) : Type0 = ( index (op_n (sym_n x) x) k == index id_n k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_sym2_n #(m-1) #a' #g (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (op_n (sym_n x) x) id_n;
    eq_elim #t #len (op_n (sym_n x) x) id_n
    end

instance group_numeric_t: (a:numeric_t) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] g:group (base_t a)) -> group (interp_numeric #(dim a) a) =
  fun a #g -> {
    m = monoid_numeric_t a #g.m;
    sym = sym_n #(dim a) #a #g;
    lemma_sym1 = lemma_sym1_n #(dim a) #a #g;
    lemma_sym2 = lemma_sym2_n #(dim a) #a #g;
}

let rec lemma_swap_n (#m:nat) (#a:numeric m) (#ag:abelian_group (base_t a)) (x:interp_numeric a) (y:interp_numeric a) : Lemma (op_n #m #a #ag.g.m x y == op_n #m #a #ag.g.m y x) =
  match a with
  |Base _ -> ag.lemma_swap x y
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let op_n = op_n #m #a #ag.g.m in
    let customprop (k:nat{k<len}) : Type0 = (index (op_n x y) k == index (op_n y x) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_swap_n #(m-1) #a' #ag (index x k) (index y k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (op_n x y) (op_n y x);
    eq_elim #t #len (op_n x y) (op_n y x)
    end

instance abelian_group_numeric_t: (a:numeric_t) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] ag:abelian_group (base_t a)) -> abelian_group (interp_numeric #(dim a) a) =
  fun a #ag -> {
    g = group_numeric_t a #ag.g;
    lemma_swap = lemma_swap_n #(dim a) #a #ag;
  }

let plus_n (#m:nat) (#a:numeric m) [| ring (base_t a) |] = op_n #m #a #add_ag.g.m
let mul_n (#m:nat) (#a:numeric m) [| ring (base_t a) |] = op_n #m #a #mul_m

let rec lemma_distr_left_n (#m:nat) (#a:numeric m) (#r:ring (base_t a)) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (let plus_n = plus_n #m #a #r in let mul_n = mul_n #m #a #r in mul_n x (plus_n y z) == plus_n (mul_n x y) (mul_n x z)) =
  match a with
  |Base _ -> r.lemma_distr_left x y z
  |Vec a' len ->
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let plus_n = plus_n #m #a #r in
    let mul_n = mul_n #m #a #r in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_n x (plus_n y z)) k == index (plus_n (mul_n x y) (mul_n x z)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_distr_left_n #(m-1) #a' #r (index x k) (index y k) (index z k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_n x (plus_n y z)) (plus_n (mul_n x y) (mul_n x z));
    eq_elim #t #len (mul_n x (plus_n y z)) (plus_n (mul_n x y) (mul_n x z))
  
let rec lemma_distr_right_n (#m:nat) (#a:numeric m) (#r:ring (base_t a)) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (let plus_n = plus_n #m #a #r in let mul_n = mul_n #m #a #r in mul_n (plus_n y z) x == plus_n (mul_n y x) (mul_n z x)) =
  match a with
  |Base _ -> r.lemma_distr_right x y z
  |Vec a' len ->
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let plus_n = plus_n #m #a #r in
    let mul_n = mul_n #m #a #r in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_n (plus_n y z) x) k == index (plus_n (mul_n y x) (mul_n z x)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_distr_right_n #(m-1) #a' #r (index x k) (index y k) (index z k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_n (plus_n y z) x) (plus_n (mul_n y x) (mul_n z x));
    eq_elim #t #len (mul_n (plus_n y z) x) (plus_n (mul_n y x) (mul_n z x))

instance ring_numeric_t: (a:numeric_t) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] r: ring (base_t a)) -> ring (interp_numeric #(dim a) a) =
  fun a #r -> {
    add_ag = abelian_group_numeric_t a #r.add_ag;
    mul_m = monoid_numeric_t a #r.mul_m;
    lemma_distr_left = lemma_distr_left_n #(dim a) #a #r;
    lemma_distr_right = lemma_distr_right_n #(dim a) #a #r;
  }
  
let rec lemma_mul_swap_n (#m:nat) (#a:numeric m) (#cr:commutative_ring (base_t a)) (x:interp_numeric a) (y:interp_numeric a) : Lemma (mul_n #m #a #cr.r x y == mul_n #m #a #cr.r y x) =
  match a with
  |Base _ -> cr.lemma_mul_swap x y
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let mul_n = mul_n #m #a #cr.r in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_n x y) k == index (mul_n y x) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_mul_swap_n #(m-1) #a' #cr (index x k) (index y k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_n x y) (mul_n y x);
    eq_elim #t #len (mul_n x y) (mul_n y x)
    end

instance commutative_ring_numeric_t: (a:numeric_t) -> (#[FStar.Tactics.Typeclasses.tcresolve ()] cr: commutative_ring (base_t a)) -> commutative_ring (interp_numeric #(dim a) a) =
  fun a #cr -> {
    r = ring_numeric_t a #cr.r;
    lemma_mul_swap = lemma_mul_swap_n #(dim a) #a #cr;
  }

open FStar.Tactics

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_universes --using_facts_from '* -FStar.Seq'"

let rec lemma_interp_numeric_vector_t (a:numeric_t) (len:size_nat) : Lemma (ensures (let a' = Vec a len in interp_numeric #(dim a') a' == vector_t #a len)) (decreases (dim a)) =
  let a' = Vec a len in
  match a with 
  |Base b -> ()
  |Vec a'' len' -> lemma_interp_numeric_vector_t a'' len'; ()

instance monoid_vector_t: #a:numeric_t -> (#[FStar.Tactics.Typeclasses.tcresolve ()] m:monoid (base_t a)) -> #len:size_nat -> monoid (vector_t #a len) =
  fun #a #m #len -> let a' = Vec a len in lemma_interp_numeric_vector_t a len; monoid_numeric_t a' #m

instance group_vector_t: #a:numeric_t -> (#[FStar.Tactics.Typeclasses.tcresolve ()] g:group (base_t a)) -> #len:size_nat -> group (vector_t #a len) =
  fun #a #g #len -> let a' = Vec a len in lemma_interp_numeric_vector_t a len; group_numeric_t a' #g

instance abelian_group_vector_t: #a:numeric_t -> (#[FStar.Tactics.Typeclasses.tcresolve ()] ag:abelian_group (base_t a)) -> #len:size_nat -> abelian_group (vector_t #a len) =
  fun #a #ag #len -> let a' = Vec a len in lemma_interp_numeric_vector_t a len; abelian_group_numeric_t a' #ag

instance ring_vector_t: #a:numeric_t -> (#[FStar.Tactics.Typeclasses.tcresolve ()] r:ring (base_t a)) -> #len:size_nat -> ring (vector_t #a len) =
  fun #a #r #len -> let a' = Vec a len in lemma_interp_numeric_vector_t a len; ring_numeric_t a' #r

instance commutative_ring_vector_t: #a:numeric_t -> (#[FStar.Tactics.Typeclasses.tcresolve ()] cr:commutative_ring (base_t a)) -> #len:size_nat -> commutative_ring (vector_t #a len) =
  fun #a #cr #len -> let a' = Vec a len in lemma_interp_numeric_vector_t a len; commutative_ring_numeric_t a' #cr
  
let v = Vec (Base int) 3
let v2 = Vec (Vec (Base (sec_int_t U32)) 4) 2
let r = ring_numeric_t v2 #(ring_uint_t #U32 #SEC)


(*type numeric_t =
  |Int : inttype -> numeric_t //machine integers
  |Unbound : unit -> numeric_t // integers
  |Mod : pos -> numeric_t // Zq
  |Vec : numeric_t -> size_nat -> numeric_t

val dim: numeric_t -> nat
let rec dim t0 = 
  match t0 with
  |Vec t _ -> 1 + dim t
  |_-> 0

type numeric (m:nat) = t:numeric_t{dim t = m}

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_universes --using_facts_from '* -FStar.Seq'"


let rec vector_ (m:nat) (t: numeric 0 -> Type0) (a:numeric m) (len:size_nat) : Type0 = 
  match a with
  |Int _ |Unbound _ |Mod _ -> lseq (t a) len
  |Vec a' len' -> lseq (vector_ (m-1) t a' len') len

val interp_numeric: (#m:nat) -> (a:numeric m) -> Tot Type0 (decreases (dim a)) 
let rec interp_numeric #m = function
  |Int t -> Lib.IntTypes.uint_t t PUB
  |Unbound _ -> int
  |Mod q -> field q
  |Vec a' len -> vector_ (m-1) interp_numeric a' len

type vector_t #m #a #len = vector_ m interp_numeric a len
*)
