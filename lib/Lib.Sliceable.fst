module Lib.Sliceable

open FStar.UInt
//open FStar.Tactics

#set-options "--fuel 0 --ifuel 0"

(*** Helper functions ***)

let (^) (a b:bool) : bool = (a && (not b)) || ((not a) && b)

private val offset (#a:Type) (#m:nat) (f:(i:nat{i<m}) -> a) (off:nat) (i:nat{i<m-off}) : a
let offset f off i = f (i+off)

(*** xN and xNxM ***)

noeq type sig (n:nat) =
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

val xN_mk_def (#n:nat) (xN:sig n) (f:(i:nat{i<n} -> bool)) (i:nat{i<n}) :
  Lemma (xN.v (xN.mk f) i == f i)
  [SMTPat (xN.v (xN.mk f) i)]

val xN_ones_spec (#n:nat) (xN:sig n) (i:nat{i<n}) :
  Lemma (xN.v xN.ones_ i == true)
  [SMTPat (xN.v xN.ones_ i)]

val xN_zeros_spec (#n:nat) (xN:sig n) (i:nat{i<n}) :
  Lemma (xN.v xN.zeros_ i == false)
  [SMTPat (xN.v xN.zeros_ i)]

val xN_and_spec (#n:nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.and_ x y) i == (xN.v x i && xN.v y i))
  [SMTPat (xN.v (xN.and_ x y) i)]

val xN_xor_spec (#n:nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.xor_ x y) i == (xN.v x i ^ xN.v y i))
  [SMTPat (xN.v (xN.xor_ x y) i)]

val xN_or_spec (#n:nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.or_ x y) i == (xN.v x i || xN.v y i))
  [SMTPat (xN.v (xN.or_ x y) i)]

val xN_not_spec (#n:nat) (xN:sig n) (x:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.not_ x) i == not (xN.v x i))
  [SMTPat (xN.v (xN.not_ x) i)]

let xN_mk_def xN f i = xN.mk_def f i
let xN_ones_spec xN i = xN.ones_spec i
let xN_zeros_spec xN i = xN.zeros_spec i
let xN_and_spec xN x y i = xN.and_spec x y i
let xN_xor_spec xN x y i = xN.xor_spec x y i
let xN_or_spec xN x y i = xN.or_spec x y i
let xN_not_spec xN x i = xN.not_spec x i

val xNxM (#n:nat) (xN:sig n) (m:nat) : Type0
#push-options "--fuel 1 --ifuel 1"
let rec xNxM xN m = if m = 0 then unit else xN.t * xNxM xN (m-1)
#pop-options

val index (#n:nat) (#xN:sig n) (#m:nat) (x:xNxM xN m) (i:nat{i<m}) : xN.t
#push-options "--ifuel 1 --fuel 1"
let rec index #n #xN #m x i =
if m = 0 then
  ()
else
  let (u, v) : xN.t * xNxM xN (m-1) = x in
  if i = m-1 then
    u
  else
    index v i
#pop-options

val xNxM_mk (#n:nat) (xN:sig n) (m:nat) (f:(i:nat{i<m} -> xN.t)) : xNxM xN m
#push-options "--fuel 1"
let rec xNxM_mk xN m f =
  if m = 0 then () else (f (m-1), xNxM_mk xN (m-1) f)
#pop-options

val xNxM_mk_def (#n:nat) (xN:sig n) (m:nat) (f:(i:nat{i<m} -> xN.t)) (i:nat{i<m}) :
  Lemma (index (xNxM_mk xN m f) i == f i)
  [SMTPat (index (xNxM_mk xN m f) i)]
#push-options "--fuel 1"
let rec xNxM_mk_def xN m f i =
  if m = 0 then
    ()
  else if i = m-1 then
    ()
  else
    xNxM_mk_def xN (m-1) f i
#pop-options

val xNxM_eq_intro (#n:nat) (#xN:sig n) (#m:nat) (x y:xNxM xN m) :
  Lemma
    (requires forall (i:nat{i<m}). index x i == index y i)
    (ensures x == y)
#push-options "--fuel 1"
let rec xNxM_eq_intro #n #xN #m x y =
  if m = 0 then
    ()
  else
    let (a, u) : xN.t * xNxM xN (m-1) = x in
    let (b, v) : xN.t * xNxM xN (m-1) = y in
    assert (forall (i:nat{i<m-1}). index u i == index x i);
    xNxM_eq_intro u v;
    //assert (index x (m-1) == a);
    assert (index y (m-1) == b)
#pop-options

val xN_rest (#n:nat) (xN:sig n) (m:nat{m<=n}) : sig m
let xN_rest (#n:nat) (xN:sig n) (m:nat{m<=n}) : sig m =
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

val xN_concat (#n:nat) (xN:sig n) (#m:nat) (xM:sig m) : sig (n+m)
#push-options "--fuel 1 --ifuel 1"
let xN_concat (#n:nat) (xN:sig n) (#m:nat) (xM:sig m) : sig (n+m) =
{ t = xN.t * xM.t
; v = (fun (x, y) i -> if i < n then xN.v x i else xM.v y (i-n))
; mk = (fun f -> (xN.mk f), xM.mk (offset #_ #(n+m) f n))
; mk_def = (fun f i -> if i < n then xN.mk_def f i else xM.mk_def (offset #_ #(n+m) f n) (i-n))
; ones_ = (xN.ones_, xM.ones_)
; zeros_ = (xN.zeros_, xM.zeros_)
; and_ = (fun (x1, y1) (x2, y2) -> (xN.and_ x1 x2, xM.and_ y1 y2))
; xor_ = (fun (x1, y1) (x2, y2) -> (xN.xor_ x1 x2, xM.xor_ y1 y2))
; or_ = (fun (x1, y1) (x2, y2) -> (xN.or_ x1 x2, xM.or_ y1 y2))
; not_ = (fun (x, y) -> (xN.not_ x, xM.not_ y))
; ones_spec = (fun i -> if i < n then xN.ones_spec i else xM.ones_spec (i-n))
; zeros_spec = (fun i -> if i < n then xN.zeros_spec i else xM.zeros_spec (i-n))
; and_spec = (fun (x1, y1) (x2, y2) i -> if i < n then xN.and_spec x1 x2 i else xM.and_spec y1 y2 (i-n))
; xor_spec = (fun (x1, y1) (x2, y2) i -> if i < n then xN.xor_spec x1 x2 i else xM.xor_spec y1 y2 (i-n))
; or_spec = (fun (x1, y1) (x2, y2) i -> if i < n then xN.or_spec x1 x2 i else xM.or_spec y1 y2 (i-n))
; not_spec = (fun (x, y) i -> if i < n then xN.not_spec x i else xM.not_spec y (i-n))
}
#pop-options

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

let u1xM (m:nat) : Type0 = xNxM u1 m

val u1xM_eq (#m:nat) (a b:u1xM m) : bool
#push-options "--fuel 1 --ifuel 1"
let rec u1xM_eq #m a b =
  if m = 0 then
    true
  else
    let (x1, y1) = a <: u1.t * u1xM (m-1) in
    let (x2, y2) = b <: u1.t * u1xM (m-1) in
    if x1 = x2 then u1xM_eq y1 y2 else false
#pop-options

val u1xM_eq_lemma (#m:nat) (a b:u1xM m) : Lemma (requires u1xM_eq a b) (ensures a == b)
#push-options "--fuel 1 --ifuel 1"
let rec u1xM_eq_lemma #m a b =
  if m = 0 then
    ()
  else
    let (x1, y1) = a <: u1.t * u1xM (m-1) in
    let (x2, y2) = b <: u1.t * u1xM (m-1) in
    u1xM_eq_lemma y1 y2
#pop-options

val u1xM_mk (m:nat) (f:(i:nat{i<m} -> bool)) : u1xM m
let u1xM_mk m f = xNxM_mk _ _ (fun i -> u1_of_bool (f i))

val column (#n:nat) (#xN:sig n) (#m:nat) (j:nat{j<n}) (x:xNxM xN m) : u1xM m
let column j x =
  let aux1 i k = (_).v (index x i) j in
  let aux2 i = (_).mk (aux1 i) in
  xNxM_mk _ _ aux2

val line (#n:nat) (#xN:sig n) (#m:nat) (i:nat{i<m}) (x:xNxM xN m) : u1xM n
let line i x =
  let aux1 j k = (_).v (index x i) j in
  let aux2 j = (_).mk (aux1 j) in
  xNxM_mk _ _ aux2

val column_def (#n:nat) (#xN:sig n) (#m:nat) (j:nat{j<n}) (x:xNxM xN m) (i:nat{i<m}) :
  Lemma ((_).v (index (column j x) i) 0 == (_).v (index x i) j)
  [SMTPat ((_).v (index (column j x) i) 0)]
let column_def j x i = ()

val line_def (#n:nat) (#xN:sig n) (#m:nat) (i:nat{i<m}) (x:xNxM xN m) (j:nat{j<n}) :
  Lemma ((_).v (index (line i x) j) 0 == (_).v (index x i) j)
  [SMTPat ((_).v (index (line i x) j) 0)]
let line_def i x j = ()

val column_lemma (#n:nat) (#xN:sig n) (#m:nat) (x:xNxM xN m) (i:nat{i<m}) (j:nat{j<n}) :
  Lemma ( u1.v (index (column j x) i) 0 == xN.v (index x i) j )
  [SMTPat (u1.v (index (column j x) i) 0)]
let column_lemma x i j = ()

val column_column (#m:nat) (x:u1xM m) :
  Lemma (column 0 x == x)
  [SMTPat (column 0 x)]
let column_column x = xNxM_eq_intro (column 0 x) x

(*** Sliceability ***)

val sliceable (#m #m':nat) (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m')) : Type0
let sliceable #m #m' f =
  forall (n:nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
  ( column j (f x) == f (column j x))

val sliceable_intro
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (pr:(#n:nat -> #xN:sig n -> x:xNxM xN m -> j:nat{j<n} -> Lemma (column j (f x) == f (column j x))))
  : Lemma (sliceable f)
let sliceable_intro f pr =
  FStar.Classical.forall_intro_2 (fun (n:nat) (xN:sig n) ->
    FStar.Classical.forall_intro_2 (fun (x:xNxM xN _) (j:nat{j<n}) ->
      pr x j
    )
  )

val sliceable_def
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  : Lemma (forall (#n:nat) (#xN:sig n) (x:xNxM xN m) (j:nat{j<n}). column j (f x) == f (column j x))
    [SMTPat (sliceable f)]
let sliceable_def f = ()

val sliceable_feq
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  (g:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  : Lemma
    (requires forall (n:nat) (xN:sig n) (x:xNxM xN m). f x == g x)
    (ensures sliceable g)
let sliceable_feq f g = ()

val reduce_output
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (m'':nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  : #n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m''
let reduce_output f m'' r x = xNxM_mk _ _ (fun i -> index (f x) (r i))

val reduce_output_def
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (m'':nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  (#n:nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m''})
  : Lemma (index (reduce_output f m'' r x) i == index (f x) (r i))
  [SMTPat (index (reduce_output f m'' r x) i)]
let reduce_output_def f m'' r x i = ()

val reduce_output_sliceable
  (#m #m':nat)
  (f:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable f})
  (m'':nat{m''<=m'}) (r:(i:nat{i<m''} -> j:nat{j<m'}))
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

val circuit_def (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) : xN.t
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

val circuit_def_lemma (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'-1}) :
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

val circuit_spec (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) : xNxM xN m'
let circuit_spec circ x = xNxM_mk _ _ (circuit_def circ x)

val circuit_spec_lemma (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) :
  Lemma (index (circuit_spec circ x) i == circuit_def circ x i)
  [SMTPat (index (circuit_spec circ x) i)]
let circuit_spec_lemma circ x i = ()

val circuit_spec' (#m #m':nat) (circ:circuit m m') (#n:nat) (#xN:sig n) (x:xNxM xN m) : (y:xNxM xN m'{y == circuit_spec circ x})
#push-options "--fuel 1 --ifuel 1"
let rec circuit_spec' #m #m' circ #n #xN x =
  if m' = 0 then
    ()
  else (
    let _ : (i:nat{i<m'}) = m'-1 in
    let y : xNxM xN (m'-1) = circuit_spec' #_ #(m'-1) circ x in
    let w : (w:xN.t{w == circuit_def circ x (m'-1)}) =
      match circ (m'-1) with
      | Input j -> index x j
      | Ones -> (_).ones_
      | Zeros -> (_).zeros_
      | Xor a b -> (_).xor_ (index y a) (index y b)
      | And a b -> (_).and_ (index y a) (index y b)
      | Or a b -> (_).or_ (index y a) (index y b)
      | Not a -> (_).not_ (index y a)
    in
    let z : xNxM xN m' = ((w <: xN.t), y) in
    xNxM_eq_intro z (circuit_spec circ x);
    z
  )
#pop-options

private val sliceable_circuit_lemma
  (#m #m':nat)
  (circ:circuit m m')
  (#n:nat)
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

val sliceable_circuit (#m #m':nat) (circ:circuit m m') :
  Lemma (sliceable (circuit_spec circ))
  [SMTPat (sliceable (circuit_spec circ))]
let sliceable_circuit circ =
  sliceable_intro (circuit_spec circ) (fun x j ->
    xNxM_eq_intro (FStar.Classical.forall_intro (fun i -> sliceable_circuit_lemma circ x i j);
    circuit_spec circ (column j x)) (column j (circuit_spec circ x))
  )

(*** of_uint and to_uint ***)

val to_uint_spec (#m:nat) (x:u1xM m) : uint_t m
let to_uint_spec #m x = FStar.UInt.from_vec (FStar.Seq.init m (index x))

val of_uint_spec (#m:nat) (p:uint_t m) : u1xM m
#push-options "--fuel 1"
let of_uint_spec #m p =
  if m = 0 then
    ()
  else
    u1xM_mk _ (FStar.UInt.nth p)
#pop-options

val to_uint (#m:nat) (x:u1xM m) : (p:uint_t m{p == to_uint_spec x})
let to_uint #m x =
  let rec aux (j:nat{j<=m})
    : (p:uint_t j{p == FStar.UInt.from_vec (FStar.Seq.init j (index x))})
    =
    if j = 0 then
      0
    else (
      let r = Prims.op_Multiply 2 (aux (j-1)) + (if index x (j-1) then 1 else 0) in
      assume (r <= pow2 j - 1);
      let r : uint_t j = r in
      let v = FStar.Seq.init j (index x) in
      assume (r == FStar.UInt.from_vec (FStar.Seq.init j (index x)));
      r
    )
  in
  aux m

val of_uint (#m:nat) (p:uint_t m) : (x:u1xM m{x == of_uint_spec p})
let of_uint #m p =
  let aux (q:uint_t m) (i:nat{i<m}) : (r:bool{r == FStar.UInt.nth p i}) =
    admit ();
    q / (pow2 i) % 2 = 1
  in
  let x = u1xM_mk _ (aux p) in
  xNxM_eq_intro x (of_uint_spec p);
  x

val to_uint_of_uint (#m:nat) (p:uint_t m) :
  Lemma (to_uint (of_uint p) == p)
  [SMTPat (to_uint (of_uint p))]
let to_uint_of_uint #m p =
  if m = 0 then
    ()
  else
    FStar.UInt.nth_lemma (to_uint (of_uint p)) p

val of_uint_to_uint (#m:nat) (x:u1xM m) :
  Lemma (of_uint (to_uint x) == x)
  [SMTPat (of_uint (to_uint x))]
let of_uint_to_uint x = xNxM_eq_intro (of_uint (to_uint x)) x

(*** Bruteforce lemmas and tactics ***)

val forall_uint_lemma (#m:nat) (phi:u1xM m -> Type0) :
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

#push-options "--fuel 1 --ifuel 1"
let bruteforce
  (#m #m':nat)
  (impl:(#n:nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (spec:(uint_t m -> uint_t m'))
  : Pure
    bool
    (requires sliceable impl)
    (ensures fun r ->
      if r then
        forall (n:nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
        column j (impl x) == of_uint (spec (to_uint (column j x)))
      else
        True
    )
  =
  let phi0 (x:u1xM m) : Type0 = impl x == of_uint (spec (to_uint x)) in
  let phi1 (i:uint_t m) : bool = u1xM_eq (impl (of_uint i)) (of_uint (spec i)) in
  let r = bruteforce_aux m phi1 in
  if r then (
    FStar.Classical.forall_intro (fun (i:uint_t m) ->
      u1xM_eq_lemma (impl (of_uint i)) (of_uint (spec i))
      <: Lemma (impl (of_uint i) == of_uint (spec i))
    );
    forall_uint_lemma phi0;
    true
  ) else false
#pop-options

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

//val bruteforce_nat (n:nat) (tac:unit -> Tac unit) : Tac unit
//let bruteforce_nat n tac =
//  let _ = repeatn n (fun _ -> apply_lemma (`nat_ind); tac ()) in
//  apply_lemma (`nat_less_zero)

//val bruteforce_bool (n:nat) (tac:unit -> Tac unit) : Tac unit
//let bruteforce_bool n tac =
//  let _ = repeatn n (fun _ -> iterAll (fun _ -> apply_lemma (`bool_ind))) in
//  iterAll tac
