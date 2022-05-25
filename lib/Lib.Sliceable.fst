module Lib.Sliceable

open FStar.UInt
//open FStar.Tactics

module Seq = Lib.Sequence
module B = Lib.Buffer
module IT = Lib.IntTypes

#set-options "--fuel 0 --ifuel 0"

(*** Helper functions ***)

let (^) (a b:bool) : bool = (a && (not b)) || ((not a) && b)

private val offset (#a:Type) (#m:IT.size_nat) (f:(i:nat{i<m}) -> a) (off:nat) (i:nat{i<m-off}) : a
let offset f off i = f (i+off)

(*** xN and xNxM ***)

noeq type sig (n:IT.size_nat) =
{ t:Type0
; v: t -> (i:nat{i<n}) -> bool
; mk: (i:nat{i<n} -> bool) -> t
; mk_def: f:(i:nat{i<n} -> bool) -> i:nat{i<n} -> Lemma (v (mk f) i == f i)
; ones_: t
; zeros_: t
; and_: t -> t -> t
; xor_: t -> t -> t
; or_: t -> t -> t
; not_: t -> t
; ones_spec: i:nat{i<n} -> Lemma (v ones_ i == true)
; zeros_spec: i:nat{i<n} -> Lemma (v zeros_ i == false)
; and_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (and_ x y) i == (v x i && v y i))
; xor_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (xor_ x y) i == (v x i ^ v y i))
; or_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (or_ x y) i == (v x i || v y i))
; not_spec: x:t -> i:nat{i<n} -> Lemma (v (not_ x) i == not(v x i))
}

val xN_mk_def (#n:IT.size_nat) (xN:sig n) (f:(i:nat{i<n} -> bool)) (i:nat{i<n}) :
  Lemma (xN.v (xN.mk f) i == f i)
  [SMTPat (xN.v (xN.mk f) i)]

val xN_ones_spec (#n:IT.size_nat) (xN:sig n) (i:nat{i<n}) :
  Lemma (xN.v xN.ones_ i == true)
  [SMTPat (xN.v xN.ones_ i)]

val xN_zeros_spec (#n:IT.size_nat) (xN:sig n) (i:nat{i<n}) :
  Lemma (xN.v xN.zeros_ i == false)
  [SMTPat (xN.v xN.zeros_ i)]

val xN_and_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.and_ x y) i == (xN.v x i && xN.v y i))
  [SMTPat (xN.v (xN.and_ x y) i)]

val xN_xor_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.xor_ x y) i == (xN.v x i ^ xN.v y i))
  [SMTPat (xN.v (xN.xor_ x y) i)]

val xN_or_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.or_ x y) i == (xN.v x i || xN.v y i))
  [SMTPat (xN.v (xN.or_ x y) i)]

val xN_not_spec (#n:IT.size_nat) (xN:sig n) (x:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.not_ x) i == not (xN.v x i))
  [SMTPat (xN.v (xN.not_ x) i)]

let xN_mk_def xN f i = xN.mk_def f i
let xN_ones_spec xN i = xN.ones_spec i
let xN_zeros_spec xN i = xN.zeros_spec i
let xN_and_spec xN x y i = xN.and_spec x y i
let xN_xor_spec xN x y i = xN.xor_spec x y i
let xN_or_spec xN x y i = xN.or_spec x y i
let xN_not_spec xN x i = xN.not_spec x i

val xNxM (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat) : Type0
#push-options "--fuel 1 --ifuel 1"
let xNxM xN m = Seq.lseq xN.t m
#pop-options

val index (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (x:xNxM xN m) (i:nat{i<m}) : xN.t
#push-options "--ifuel 1 --fuel 1"
let rec index #n #xN #m x i = Seq.index x i
#pop-options

val xNxM_mk (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat) (f:(i:nat{i<m} -> xN.t)) : xNxM xN m
#push-options "--fuel 1"
let rec xNxM_mk xN m f = Seq.createi m f
#pop-options

val xNxM_mk_def (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat) (f:(i:nat{i<m} -> xN.t)) (i:nat{i<m}) :
  Lemma (index (xNxM_mk xN m f) i == f i)
  [SMTPat (index (xNxM_mk xN m f) i)]
#push-options "--fuel 1"
let rec xNxM_mk_def xN m f i = ()
#pop-options

val xNxM_eq_intro (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (x y:xNxM xN m) :
  Lemma
    (requires forall (i:nat{i<m}). index x i == index y i)
    (ensures x == y)
#push-options "--fuel 1"
let rec xNxM_eq_intro #n #xN #m x y =
  assert(forall (i:nat{i<m}). Seq.index x i == Seq.index y i);
  Seq.eq_intro x y
#pop-options

val xN_rest (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat{m<=n}) : sig m
let xN_rest (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat{m<=n}) : sig m =
{ t = xN.t
; v = xN.v
; mk = (fun f -> xN.mk (fun i -> if i < m then f i else false))
; mk_def = (fun f i -> xN.mk_def (fun i -> if i < m then f i else false) i)
; ones_ = xN.ones_
; zeros_ = xN.zeros_
; and_ = xN.and_
; xor_ = xN.xor_
; or_ = xN.or_
; not_ = xN.not_
; ones_spec = xN.ones_spec
; zeros_spec = xN.zeros_spec
; and_spec = xN.and_spec
; xor_spec = xN.xor_spec
; or_spec = xN.or_spec
; not_spec = xN.not_spec
}

(*** u1 and u1xM ***)

let u1 : sig 1 =
{ t = bool
; v = (fun x 0 -> x)
; mk = (fun f -> f 0)
; mk_def = (fun f i -> ())
; ones_ = true
; zeros_ = false
; and_ = (fun x y -> x && y)
; xor_ = (fun x y -> x ^ y)
; or_ = (fun x y -> x || y)
; not_ = (fun x -> not x)
; ones_spec = (fun i -> ())
; zeros_spec = (fun i -> ())
; and_spec = (fun x y i -> ())
; xor_spec = (fun x y i -> ())
; or_spec = (fun x y i -> ())
; not_spec = (fun x i -> ())
}

val u1_of_bool (b:bool) : u1.t
let u1_of_bool b = u1.mk (fun 0 -> b)

val u1_of_bool_def (b:bool) : Lemma (u1.v (u1_of_bool b) 0 == b) [SMTPat (u1.v (u1_of_bool b) 0)]
let u1_of_bool_def b = ()

let u1xM (m:IT.size_nat) : Type0 = xNxM u1 m

val u1xM_mk (m:IT.size_nat) (f:(i:nat{i<m} -> bool)) : u1xM m
let u1xM_mk m f = xNxM_mk _ _ (fun i -> u1_of_bool (f i))

val u1xM_eq (#m:IT.size_nat) (a b:u1xM m) : bool
let u1xM_eq a b = Seq.for_all2 (fun x y -> x = y) a b

val u1xM_eq_lemma (#m:IT.size_nat) (a b:u1xM m) : Lemma (requires u1xM_eq a b) (ensures a == b)
let u1xM_eq_lemma a b = admit ()


val column (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (j:nat{j<n}) (x:xNxM xN m) : u1xM m
let column j x =
  let aux1 i k = (_).v (index x i) j in
  let aux2 i = (_).mk (aux1 i) in
  xNxM_mk _ _ aux2

val line (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (i:nat{i<m}) (x:xNxM xN m) : u1xM n
let line i x =
  let aux1 j k = (_).v (index x i) j in
  let aux2 j = (_).mk (aux1 j) in
  xNxM_mk _ _ aux2

val column_def (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (j:nat{j<n}) (x:xNxM xN m) (i:nat{i<m}) :
  Lemma ((_).v (index (column j x) i) 0 == (_).v (index x i) j)
  [SMTPat ((_).v (index (column j x) i) 0)]
let column_def j x i = ()

val line_def (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (i:nat{i<m}) (x:xNxM xN m) (j:nat{j<n}) :
  Lemma ((_).v (index (line i x) j) 0 == (_).v (index x i) j)
  [SMTPat ((_).v (index (line i x) j) 0)]
let line_def i x j = ()

val column_lemma (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (x:xNxM xN m) (i:nat{i<m}) (j:nat{j<n}) :
  Lemma ( u1.v (index (column j x) i) 0 == xN.v (index x i) j )
  [SMTPat (u1.v (index (column j x) i) 0)]
let column_lemma x i j = ()

val column_column (#m:IT.size_nat) (x:u1xM m) :
  Lemma (column 0 x == x)
  [SMTPat (column 0 x)]
let column_column x = xNxM_eq_intro (column 0 x) x

(*** Sliceability ***)

val sliceable (#m #m':IT.size_nat) (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m')) : Type0
let sliceable #m #m' f =
  forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
  ( column j (f x) == f (column j x))

val sliceable_intro
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (pr:(#n:IT.size_nat -> #xN:sig n -> x:xNxM xN m -> j:nat{j<n} -> Lemma (column j (f x) == f (column j x))))
  : Lemma (sliceable f)
let sliceable_intro f pr =
  admit ()

val sliceable_def
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  : Lemma (forall (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (j:nat{j<n}). column j (f x) == f (column j x))
    [SMTPat (sliceable f)]
let sliceable_def f = ()

val sliceable_feq
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  (g:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  : Lemma
    (requires forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m). f x == g x)
    (ensures sliceable g)
let sliceable_feq f g = ()

val reduce_output
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (m'':IT.size_nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  : #n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m''
let reduce_output f m'' r x = xNxM_mk _ _ (fun i -> index (f x) (r i))

val reduce_output_def
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (m'':IT.size_nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m''})
  : Lemma (index (reduce_output f m'' r x) i == index (f x) (r i))
  [SMTPat (index (reduce_output f m'' r x) i)]
let reduce_output_def f m'' r x i = ()

val reduce_output_sliceable
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  (m'':IT.size_nat{m''<=m'}) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  : Lemma (sliceable (reduce_output f m'' r))
  [SMTPat (sliceable (reduce_output f m'' r))]
let reduce_output_sliceable f m'' r =
  sliceable_intro (reduce_output f m'' r)
    (fun x j -> xNxM_eq_intro (reduce_output f m'' r (column j x)) (column j (reduce_output f m'' r x)))

(*** Circuits ***)

type gate (m:nat) (c:nat) =
| Zeros
| Ones
| Input : (i:nat{i<m}) -> gate m c
| Xor : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| And : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Or : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Not : (a:nat{a<c}) -> gate m c

type circuit (m p:nat) = (i:nat{i<p}) -> gate m i

val circuit_def (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) : xN.t
#push-options "--ifuel 1"
let rec circuit_def circ x i =
  match circ i with
  | Input j -> index x j
  | Ones -> (_).ones_
  | Zeros -> (_).zeros_
  | Xor a b -> (_).xor_ (circuit_def circ x a) (circuit_def circ x b)
  | And a b -> (_).and_ (circuit_def circ x a) (circuit_def circ x b)
  | Or a b -> (_).or_ (circuit_def circ x a) (circuit_def circ x b)
  | Not a -> (_).not_ (circuit_def circ x a)
#pop-options

val circuit_def_lemma (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'-1}) :
  Lemma (circuit_def #_ #(m'-1) circ x i == circuit_def #_ #m' circ x i)
  [SMTPat (circuit_def #m #m' circ x i)]
#push-options "--fuel 1 --ifuel 1"
let rec circuit_def_lemma circ x i =
  match circ i with
  | Input j -> ()
  | Ones -> ()
  | Zeros -> ()
  | Xor a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | And a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Or a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Not a -> circuit_def_lemma circ x a
#pop-options

val circuit_spec (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) : xNxM xN m'
let circuit_spec circ x = xNxM_mk _ _ (circuit_def circ x)

val circuit_spec_lemma (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) :
  Lemma (index (circuit_spec circ x) i == circuit_def circ x i)
  [SMTPat (index (circuit_spec circ x) i)]
let circuit_spec_lemma circ x i = ()

val circuit_spec' (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) : (y:xNxM xN m'{y == circuit_spec circ x})
#push-options "--fuel 1 --ifuel 1"
let rec circuit_spec' #m #m' circ #n #xN x = admit ()
#pop-options

private val sliceable_circuit_lemma
  (#m #m':IT.size_nat)
  (circ:circuit m m')
  (#n:IT.size_nat)
  (#xN:sig n)
  (x:xNxM xN m)
  (i:nat{i<m'})
  (j:nat{j<n})
  : Lemma ( xN.v (circuit_def circ x i) j == u1.v (circuit_def circ (column j x) i) 0 )
#push-options "--fuel 1 --ifuel 1"
let rec sliceable_circuit_lemma circ x i j = match circ i with
  | Ones -> ()
  | Zeros -> ()
  | Input _ -> ()
  | Xor a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | And a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Or a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Not a -> sliceable_circuit_lemma circ x a j
#pop-options

val sliceable_circuit (#m #m':IT.size_nat) (circ:circuit m m') :
  Lemma (sliceable (circuit_spec circ))
  [SMTPat (sliceable (circuit_spec circ))]
let sliceable_circuit circ =
  sliceable_intro (circuit_spec circ) (fun x j ->
    xNxM_eq_intro (FStar.Classical.forall_intro (fun i -> sliceable_circuit_lemma circ x i j);
    circuit_spec circ (column j x)) (column j (circuit_spec circ x))
  )


open FStar.HyperStack
open FStar.HyperStack.All


inline_for_extraction noextract
val circuit_lowstar_aux (#m:IT.size_nat) (#m':IT.size_nat) (circ:circuit m m') (cur:nat{cur<=m'}) (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m)
  (input:B.lbuffer xN.t (IT.size m)) (output:B.lbuffer xN.t (IT.size m')) :
  Stack unit
  (requires (fun h ->
    B.live h input /\ B.live h output
    /\ B.disjoint input output
    /\ (forall (j:nat{j<m}). B.get h input j == index x j)
  ))
  (ensures  (fun h0 _ h1 ->
    B.modifies1 output h0 h1
    /\ (forall(j:nat{j<cur}). B.get h1 output j == circuit_def circ x j)
  ))
#push-options "--fuel 1 --ifuel 1"
inline_for_extraction noextract
let rec circuit_lowstar_aux #m #m' circ cur #_ #xN x input output =
  if cur = 0 then
    ()
  else (
    circuit_lowstar_aux circ (cur-1) x input output;
    let g : gate m (cur-1) = circ (cur-1) in
    let (v:xN.t{v == circuit_def circ x (cur-1)}) = match g with
      | Zeros -> xN.zeros_ 
      | Ones -> xN.ones_
      | Input i -> B.index input (IT.size i)
      | Xor a b -> xN.xor_ (B.index output (IT.size a)) (B.index output (IT.size b))
      | And a b -> xN.and_ (B.index output (IT.size a)) (B.index output (IT.size b))
      | Or a b -> xN.or_ (B.index output (IT.size a)) (B.index output (IT.size b))
      | Not a -> xN.not_ (B.index output (IT.size a))
     in
     B.upd output (IT.size (cur-1)) v
  )
#pop-options

inline_for_extraction noextract
val circuit_lowstar (#m:IT.size_nat{m>0}) (#m':IT.size_nat{m'>0}) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m)
  (input:B.lbuffer xN.t (IT.size m)) (output:B.lbuffer xN.t (IT.size m')) :
Stack unit
  (requires (fun h ->
    B.live h input /\ B.live h output
    /\ B.disjoint input output
    /\ (forall (j:nat{j<m}). B.get h input j == index x j))
  )
  (ensures  (fun h0 _ h1 -> forall(j:nat{j<m'}). B.get h1 output j == circuit_def circ x j))
inline_for_extraction noextract
let circuit_lowstar #m #m' circ #_ #_ x input output =
  circuit_lowstar_aux circ m' x input output

(*** of_uint and to_uint ***)

val to_uint (#m:IT.size_nat{m>0}) (x:u1xM m) : (p:uint_t m{p == FStar.UInt.from_vec (FStar.Seq.init m (index x))})
let to_uint #m x =
  let rec aux (j:nat{j<=m})
    : (p:uint_t j{p == FStar.UInt.from_vec (FStar.Seq.init j (index x))})
    =
    if j = 0 then
      0
    else (
      let r = Prims.op_Multiply 2 (aux (j-1)) + (if index x (j-1) then 1 else 0) in
      FStar.Math.Lemmas.pow2_plus 1 (j-1);
      let r : uint_t j = r in
      let v = FStar.Seq.init j (index x) in
      assume (r == FStar.UInt.from_vec (FStar.Seq.init j (index x)));
      r
    )
  in
  aux m

val of_uint (#m:IT.size_nat{m>0}) (p:uint_t m) : (x:u1xM m{x == u1xM_mk _ (FStar.UInt.nth p)})
let of_uint #m p =
  let aux (q:uint_t m) (i:nat{i<m}) : (r:bool{r == FStar.UInt.nth p i}) =
    admit ();
    q / (pow2 i) % 2 = 1
  in
  let x = u1xM_mk _ (aux p) in
  xNxM_eq_intro x (u1xM_mk _ (FStar.UInt.nth p));
  x

val to_uint_of_uint (#m:IT.size_nat{m>0}) (p:uint_t m) :
  Lemma (to_uint (of_uint p) == p)
  [SMTPat (to_uint (of_uint p))]
let to_uint_of_uint #m p =
  if m = 0 then
    ()
  else
    FStar.UInt.nth_lemma (to_uint (of_uint p)) p

val of_uint_to_uint (#m:IT.size_nat{m>0}) (x:u1xM m) :
  Lemma (of_uint (to_uint x) == x)
  [SMTPat (of_uint (to_uint x))]
let of_uint_to_uint x = xNxM_eq_intro (of_uint (to_uint x)) x

val to_uint_spec (#m:IT.size_nat{m>0}) (x:u1xM m) : Lemma (to_uint x == FStar.UInt.from_vec (FStar.Seq.init m (index x)))
let to_uint_spec x = ()

val of_uint_spec (#m:IT.size_nat{m>0}) (p:uint_t m) : Lemma (of_uint p == u1xM_mk _ (FStar.UInt.nth p))
let of_uint_spec p = ()

(*** Bruteforce lemmas and tactics ***)

val forall_uint_lemma (#m:IT.size_nat{m>0}) (phi:u1xM m -> Type0) :
  Lemma
    (requires forall (i:uint_t m). phi (of_uint i))
    (ensures forall x. phi x)
let forall_uint_lemma phi =
  FStar.Classical.forall_intro (fun x -> of_uint_to_uint x <: Lemma (phi x))

let bruteforce_aux (n:nat) (phi:(i:uint_t n -> bool)) :
  Pure
    bool
    (requires True)
    (fun r -> if r then forall (i:uint_t n). phi i else True)
  =
  let rec foo (n:nat) (phi:(i:nat{i<n} -> bool)) :
    Pure
      bool
      (requires True)
      (ensures fun r -> if r then forall (i:nat{i<n}). phi i else True)
    = if n = 0 then true else phi (n-1) && foo (n-1) phi
  in
  foo (pow2 n) phi

val bruteforce
  (#m:IT.size_nat{m>0}) (#m':IT.size_nat{m'>0})
  (impl:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (spec:(uint_t m -> uint_t m'))
  : Pure
    bool
    (requires sliceable impl)
    (ensures fun r ->
      if r then
        forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
        column j (impl x) == of_uint (spec (to_uint (column j x)))
      else
        True
    )
let bruteforce #m #m' impl spec =
  let phi0 (x:u1xM m) : Type0 = impl x == (of_uint (spec (to_uint x)) <: u1xM m') in
  let phi1 (i:uint_t m) : bool = u1xM_eq (impl (of_uint i)) (of_uint (spec i) <: u1xM m') in
  let r = bruteforce_aux m phi1 in
  if r then (
    FStar.Classical.forall_intro (fun (i:uint_t m) ->
      u1xM_eq_lemma (impl (of_uint i)) (of_uint (spec i) <: u1xM m')
      <: Lemma (impl (of_uint i) == (of_uint (spec i) <: u1xM m'))
    );
    forall_uint_lemma phi0;
    true
  ) else false

//val nat_ind
//  (n:pos)
//  (phi:((i:nat{i<n}) -> Type))
//  (_:squash (phi (n-1)))
//  (_:squash (forall (i:nat{i<n-1}). phi i))
//  : Lemma (forall (i:nat{i<n}). phi i)
//let nat_ind n phi _ _ = ()

//val bool_ind
//  (phi:(bool -> Type))
//  (_:squash (phi true))
//  (_:squash (phi false))
//  : Lemma (forall b. phi b)
//let bool_ind phi _ _ = ()

//val nat_less_zero (phi : (i:nat{i<0}) -> Type) : Lemma (forall i. phi i)
//let nat_less_zero phi = ()

//val bruteforce_nat (n:IT.size_nat) (tac:unit -> Tac unit) : Tac unit
//let bruteforce_nat n tac =
//  let _ = repeatn n (fun _ -> apply_lemma (`nat_ind); tac ()) in
//  apply_lemma (`nat_less_zero)

//val bruteforce_bool (n:IT.size_nat) (tac:unit -> Tac unit) : Tac unit
//let bruteforce_bool n tac =
//  let _ = repeatn n (fun _ -> iterAll (fun _ -> apply_lemma (`bool_ind))) in
//  iterAll tac
