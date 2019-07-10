module Lib.NumericTypes

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
  |Base : a:Type0 -> #r:ring a -> numeric_t
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
  |Base _ -> lseq (t a) len
  |Vec a' len' -> lseq (vector_ (m-1) t a' len') len

val interp_numeric: (#m:nat) -> (a:numeric m) -> Tot Type0 (decreases (dim a)) 
let rec interp_numeric #m = function
  |Base t -> t
  |Vec a' len -> (*lseq (interp_numeric #(m-1) a') len*)vector_ (m-1) interp_numeric a' len

type vector_t #m #a #len : Type0 = vector_ m interp_numeric a len

let rec zero_nv (#m:nat) (#a:numeric m) : Tot (interp_numeric a) = 
  match a with
  |Base _ #r -> r.zero 
  |Vec a' len -> create len (zero_nv #(m-1) #a')
  

let rec one_nv (#m:nat) (#a:numeric m) : Tot (interp_numeric a) =
  match a with
    |Base _ #r -> r.one
    |Vec a' len -> create len (one_nv #(m-1) #a')

let rec plus_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) : Tot (interp_numeric a) = 
  match a with
    |Base _ #r -> r.plus x y
    |Vec a' len -> let t = interp_numeric #(m-1) a' in Lib.Sequence.map2 #t #t #t #len (plus_nv #(m-1) #a') x y

let rec minus_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) : Tot (interp_numeric a) = 
  match a with
    |Base _ #r -> r.minus x y
    |Vec a' len -> let t = interp_numeric #(m-1) a' in Lib.Sequence.map2 #t #t #t #len (minus_nv #(m-1) #a') x y

let rec opp_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Tot (interp_numeric a) = 
  match a with
    |Base _ #r -> r.opp x
    |Vec a' len -> let t = interp_numeric #(m-1) a' in Lib.Sequence.map #t #t #len (opp_nv #(m-1) #a') x

let rec mul_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) : Tot (interp_numeric a) = 
  match a with
    |Base _ #r -> r.mul x y
    |Vec a' len -> let t = interp_numeric #(m-1) a' in Lib.Sequence.map2 #t #t #t #len (mul_nv #(m-1) #a') x y

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_universes --using_facts_from '* -FStar.Seq'"

let rec lemma_plus_assoc_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (plus_nv (plus_nv x y) z == plus_nv x (plus_nv y z)) =
  match a with
  |Base _ #r -> r.lemma_plus_assoc x y z
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (plus_nv (plus_nv x y) z) k == index (plus_nv x (plus_nv y z)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_plus_assoc_nv #(m-1) #a' (index x k) (index y k) (index z k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (plus_nv (plus_nv x y) z) (plus_nv x (plus_nv y z));
    eq_elim #t #len (plus_nv (plus_nv x y) z) (plus_nv x (plus_nv y z))
    end
  
let rec lemma_plus_swap_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) : Lemma (plus_nv x y == plus_nv y x) =
  match a with
  |Base _ #r -> r.lemma_plus_swap x y
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (plus_nv x y) k == index (plus_nv y x) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_plus_swap_nv #(m-1) #a' (index x k) (index y k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (plus_nv x y) (plus_nv y x);
    eq_elim #t #len (plus_nv x y) (plus_nv y x)
    end
    
let rec lemma_plus_inv1_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Lemma (plus_nv x (opp_nv x) == zero_nv) =
  match a with
  |Base _ #r -> r.lemma_plus_inv1 x
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = ( index (plus_nv x (opp_nv x)) k == index (zero_nv #m #a) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_plus_inv1_nv #(m-1) #a' (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (plus_nv x (opp_nv x)) (zero_nv #m #a);
    eq_elim #t #len (plus_nv x (opp_nv x)) (zero_nv #m #a)
    end


let lemma_plus_inv2_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Lemma (plus_nv (opp_nv x) x == zero_nv) =
  lemma_plus_swap_nv (opp_nv x) x;
  lemma_plus_inv1_nv x

let rec lemma_mul_assoc_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (mul_nv (mul_nv x y) z == mul_nv x (mul_nv y z)) =
  match a with
  |Base _ #r -> r.lemma_mul_assoc x y z
  |Vec a' len -> begin
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_nv (mul_nv x y) z) k == index (mul_nv x (mul_nv y z)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_mul_assoc_nv #(m-1) #a' (index x k) (index y k) (index z k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_nv (mul_nv x y) z) (mul_nv x (mul_nv y z));
    eq_elim #t #len (mul_nv (mul_nv x y) z) (mul_nv x (mul_nv y z))
    end

let rec lemma_distr_left_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (mul_nv x (plus_nv y z) == plus_nv (mul_nv x y) (mul_nv x z)) =
  match a with
  |Base _ #r -> r.lemma_distr_left x y z
  |Vec a' len ->
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_nv x (plus_nv y z)) k == index (plus_nv (mul_nv x y) (mul_nv x z)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_distr_left_nv #(m-1) #a' (index x k) (index y k) (index z k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_nv x (plus_nv y z)) (plus_nv (mul_nv x y) (mul_nv x z));
    eq_elim #t #len (mul_nv x (plus_nv y z)) (plus_nv (mul_nv x y) (mul_nv x z))
  
let rec lemma_distr_right_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) (y:interp_numeric a) (z:interp_numeric a) : Lemma (mul_nv (plus_nv y z) x == plus_nv (mul_nv y x) (mul_nv z x)) =
  match a with
  |Base _ #r -> r.lemma_distr_right x y z
  |Vec a' len -> 
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_nv (plus_nv y z) x) k == index (plus_nv (mul_nv y x) (mul_nv z x)) k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_distr_right_nv #(m-1) #a' (index x k) (index y k) (index z k) in
  FStar.Classical.forall_intro customlemma;
  eq_intro #t #len (mul_nv (plus_nv y z) x) (plus_nv (mul_nv y x) (mul_nv z x));
  eq_elim #t #len (mul_nv (plus_nv y z) x) (plus_nv (mul_nv y x) (mul_nv z x))
  
let rec lemma_zero1_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Lemma (plus_nv zero_nv x == x) =
  match a with
  |Base _ #r -> r.lemma_zero1 x
  |Vec a' len ->
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (plus_nv zero_nv x) k == index x k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_zero1_nv #(m-1) #a' (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (plus_nv zero_nv x) x;
    eq_elim #t #len (plus_nv zero_nv x) x

let lemma_zero2_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Lemma (plus_nv x zero_nv == x) =
  lemma_plus_swap_nv zero_nv x;
  lemma_zero1_nv x
  
let rec lemma_one1_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Lemma (mul_nv one_nv x == x) =
  match a with
  |Base _ #r -> r.lemma_one1 x
  |Vec a' len -> 
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_nv one_nv x) k == index x k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_one1_nv #(m-1) #a' (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_nv one_nv x) x;
    eq_elim #t #len (mul_nv one_nv x) x

let rec lemma_one2_nv (#m:nat) (#a:numeric m) (x:interp_numeric a) : Lemma (mul_nv x one_nv == x) =
  match a with
  |Base _ #r -> r.lemma_one2 x
  |Vec a' len -> 
    let t = interp_numeric #(m-1) a' in
    let index = index #t #len in
    let customprop (k:nat{k<len}) : Type0 = (index (mul_nv x one_nv) k == index x k) in
    let customlemma (k:nat{k<len}) : Lemma (customprop k) =
      lemma_one2_nv #(m-1) #a' (index x k) in
    FStar.Classical.forall_intro customlemma;
    eq_intro #t #len (mul_nv x one_nv) x;
    eq_elim #t #len (mul_nv x one_nv) x

instance ring_numeric: (a:numeric_t) -> ring (interp_numeric #(dim a) a) =
  fun a ->
    {
    zero = zero_nv;
    one = one_nv;
    plus = plus_nv;
    minus = minus_nv;
    mul = mul_nv;
    opp = opp_nv;
    lemma_plus_assoc = lemma_plus_assoc_nv;
    lemma_plus_swap = lemma_plus_swap_nv;
    lemma_plus_inv1 = lemma_plus_inv1_nv;
    lemma_plus_inv2 = lemma_plus_inv2_nv;
    lemma_mul_assoc = lemma_mul_assoc_nv;
    lemma_distr_left = lemma_distr_left_nv;
    lemma_distr_right = lemma_distr_right_nv;
    lemma_zero1 = lemma_zero1_nv;
    lemma_zero2 = lemma_zero2_nv;
    lemma_one1 = lemma_one1_nv;
    lemma_one2 = lemma_one2_nv;
}

open FStar.Tactics

#reset-options "--z3rlimit 300 --max_fuel 2 --max_ifuel 2 --print_universes --using_facts_from '* -FStar.Seq'"

let rec lemma_interp_numeric_vector_t (a:numeric_t) (len:size_nat) : Lemma (ensures (let a' = Vec a len in interp_numeric #(dim a') a' == vector_t #(dim a) #a #len)) (decreases (dim a)) =
  let a' = Vec a len in
  match a with 
  |Base b -> ()
  |Vec a'' len' -> lemma_interp_numeric_vector_t a'' len'; ()

instance ring_vector_t: #a:numeric_t -> #len:size_nat -> ring (vector_t #(dim a) #a #len) =
  fun #a #len -> let a' = Vec a len in lemma_interp_numeric_vector_t a len; ring_numeric(a')
  
let v = Vec (Base int #ring_int) 3
let v2 = Vec (Vec (Base (sec_int_t U32) #ring_uint_t) 4) 2
let r = ring_numeric v2
let v2' = vector_t #1 #(Vec (Base (sec_int_t U32) #ring_uint_t) 4) #2
let r' () = assert_norm(interp_numeric #(dim v2) v2 == v2')


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
