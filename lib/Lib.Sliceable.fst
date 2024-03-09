module Lib.Sliceable

open FStar.UInt
//open FStar.Tactics

module Seq = Lib.Sequence
module B = Lib.Buffer
module IT = Lib.IntTypes

#set-options "--fuel 1 --ifuel 1"

(*** Helper functions ***)

inline_for_extraction noextract
let (^) (a b:bool) : bool = (a && (not b)) || ((not a) && b)

inline_for_extraction noextract
private val offset (#a:Type) (#m:IT.size_nat) (f:(i:nat{i<m}) -> a) (off:nat) (i:nat{i<m-off}) : a
inline_for_extraction noextract
private let offset f off i = f (i+off)

(*** xN and xNxM ***)

inline_for_extraction noextract
noeq type sig (n:IT.size_nat) =
{ t:Type0
; v: t -> (i:nat{i<n}) -> bool
; mk: (i:nat{i<n} -> bool) -> t
; mk_def: f:(i:nat{i<n} -> bool) -> i:nat{i<n} -> Lemma (v (mk f) i == f i)
; ones_: t
; zeros_: t
; and_: t -> t -> t
; xor_: t -> t -> t
; xnor_: t -> t -> t
; or_: t -> t -> t
; not_: t -> t
; ones_spec: i:nat{i<n} -> Lemma (v ones_ i == true)
; zeros_spec: i:nat{i<n} -> Lemma (v zeros_ i == false)
; and_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (and_ x y) i == (v x i && v y i))
; xor_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (xor_ x y) i == (v x i ^ v y i))
; xnor_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (xnor_ x y) i == (not(v x i) && not(v y i) || v x i && v y i))
; or_spec: x:t -> y:t -> i:nat{i<n} -> Lemma (v (or_ x y) i == (v x i || v y i))
; not_spec: x:t -> i:nat{i<n} -> Lemma (v (not_ x) i == not(v x i))
}

val xN_mk_def (#n:IT.size_nat) (xN:sig n) (f:(i:nat{i<n} -> bool)) (i:nat{i<n}) :
  Lemma (xN.v (xN.mk f) i == f i)
  [SMTPat (xN.v (xN.mk f) i)]
let xN_mk_def xN f i = xN.mk_def f i

val xN_ones_spec (#n:IT.size_nat) (xN:sig n) (i:nat{i<n}) :
  Lemma (xN.v xN.ones_ i == true)
  [SMTPat (xN.v xN.ones_ i)]
let xN_ones_spec xN i = xN.ones_spec i

val xN_zeros_spec (#n:IT.size_nat) (xN:sig n) (i:nat{i<n}) :
  Lemma (xN.v xN.zeros_ i == false)
  [SMTPat (xN.v xN.zeros_ i)]
let xN_zeros_spec xN i = xN.zeros_spec i

val xN_and_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.and_ x y) i == (xN.v x i && xN.v y i))
  [SMTPat (xN.v (xN.and_ x y) i)]
let xN_and_spec xN x y i = xN.and_spec x y i

val xN_xor_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.xor_ x y) i == (xN.v x i ^ xN.v y i))
  [SMTPat (xN.v (xN.xor_ x y) i)]
let xN_xor_spec xN x y i = xN.xor_spec x y i

val xN_xnor_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.xnor_ x y) i == (not(xN.v x i) && not(xN.v y i) || xN.v x i && xN.v y i))
  [SMTPat (xN.v (xN.xnor_ x y) i)]
let xN_xnor_spec xN x y i = xN.xnor_spec x y i

val xN_or_spec (#n:IT.size_nat) (xN:sig n) (x y:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.or_ x y) i == (xN.v x i || xN.v y i))
  [SMTPat (xN.v (xN.or_ x y) i)]
let xN_or_spec xN x y i = xN.or_spec x y i

val xN_not_spec (#n:IT.size_nat) (xN:sig n) (x:xN.t) (i:nat{i<n}) :
  Lemma (xN.v (xN.not_ x) i == not (xN.v x i))
  [SMTPat (xN.v (xN.not_ x) i)]
let xN_not_spec xN x i = xN.not_spec x i

inline_for_extraction noextract
val xNxM (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat) : Type0
inline_for_extraction noextract
let xNxM xN m = Seq.lseq xN.t m

inline_for_extraction noextract
val index (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (x:xNxM xN m) (i:nat{i<m}) : xN.t
inline_for_extraction noextract
let index #n #xN #m x i = Seq.index x i

inline_for_extraction noextract
val xNxM_mk (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat) (f:(i:nat{i<m} -> xN.t)) : xNxM xN m
inline_for_extraction noextract
let xNxM_mk xN m f = Seq.createi m f

val xNxM_mk_def (#n:IT.size_nat) (xN:sig n) (m:IT.size_nat) (f:(i:nat{i<m} -> xN.t)) (i:nat{i<m}) :
  Lemma (index (xNxM_mk xN m f) i == f i)
  [SMTPat (index (xNxM_mk xN m f) i)]
let xNxM_mk_def xN m f i = ()

val xNxM_eq_intro (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (x y:xNxM xN m) :
  Lemma
    (requires forall (i:nat{i<m}). index x i == index y i)
    (ensures x == y)
let xNxM_eq_intro #n #xN #m x y =
  assert (forall (i:nat{i<m}). Seq.index x i == Seq.index y i);
  Seq.eq_intro x y

(*** u1 and u1xM ***)

inline_for_extraction noextract
let u1 : sig 1 =
{ t = bool
; v = (fun x 0 -> x)
; mk = (fun f -> f 0)
; mk_def = (fun f i -> ())
; ones_ = true
; zeros_ = false
; and_ = (fun x y -> x && y)
; xor_ = (fun x y -> x ^ y)
; xnor_ = (fun x y -> not x && not y || x && y)
; or_ = (fun x y -> x || y)
; not_ = (fun x -> not x)
; ones_spec = (fun i -> ())
; zeros_spec = (fun i -> ())
; and_spec = (fun x y i -> ())
; xor_spec = (fun x y i -> ())
; xnor_spec = (fun x y i -> ())
; or_spec = (fun x y i -> ())
; not_spec = (fun x i -> ())
}

inline_for_extraction noextract
val u1_of_bool (b:bool) : u1.t
inline_for_extraction noextract
let u1_of_bool b = u1.mk (fun 0 -> b)

val u1_of_bool_def (b:bool) : Lemma (u1.v (u1_of_bool b) 0 == b) [SMTPat (u1.v (u1_of_bool b) 0)]
let u1_of_bool_def b = ()

inline_for_extraction noextract
let u1xM (m:IT.size_nat) : Type0 = xNxM u1 m

inline_for_extraction noextract
val u1xM_mk (m:IT.size_nat) (f:(i:nat{i<m} -> bool)) : u1xM m
inline_for_extraction noextract
let u1xM_mk m f = xNxM_mk _ _ (fun i -> u1_of_bool (f i))

inline_for_extraction noextract
val u1xM_eq (#m:IT.size_nat) (a b:u1xM m) : bool
inline_for_extraction noextract
let u1xM_eq a b = Seq.for_all2 (fun x y -> x = y) a b

val u1xM_eq_lemma (#m:IT.size_nat) (a b:u1xM m) : Lemma (requires u1xM_eq a b) (ensures a == b)
let u1xM_eq_lemma a b = admit ()


inline_for_extraction noextract
val column (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (j:nat{j<n}) (x:xNxM xN m) : u1xM m
inline_for_extraction noextract
let column j x =
  let aux1 i k = (_).v (index x i) j in
  let aux2 i = (_).mk (aux1 i) in
  xNxM_mk _ _ aux2

inline_for_extraction noextract
val line (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (i:nat{i<m}) (x:xNxM xN m) : u1xM n
inline_for_extraction noextract
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

inline_for_extraction noextract
val sliceable (#m #m':IT.size_nat) (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m')) : Type0
inline_for_extraction noextract
let sliceable #m #m' f =
  forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
  ( column j (f x) == f (column j x))

val sliceable_intro
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (pr:(#n:IT.size_nat -> #xN:sig n -> x:xNxM xN m -> j:nat{j<n} -> Lemma (column j (f x) == f (column j x))))
  : Lemma (sliceable f)
let sliceable_intro #m #m' f pr =
  FStar.Classical.forall_intro_2 (
    fun (n:IT.size_nat) (xN:sig n) ->
      FStar.Classical.forall_intro_2 (
        fun (x:xNxM xN m) (j:nat{j<n}) ->
          pr x j
          <: Lemma (column j (f x) == f (column j x))
      ) <: Lemma (forall (x:xNxM xN m) (j:nat{j<n}). column j (f x) == f (column j x))
  )

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

inline_for_extraction noextract
val reduce_output
  (#m #m':IT.size_nat)
  (f:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'))
  (m'':IT.size_nat) (r:(i:nat{i<m''} -> j:nat{j<m'}))
  : #n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m''
inline_for_extraction noextract
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

inline_for_extraction noextract
let xNx8_mk (#n:IT.size_nat) (#xN:sig n)
  (x0 x1 x2 x3 x4 x5 x6 x7:xN.t) : xNxM xN 8 =
  xNxM_mk _ _ (fun i -> match i with
  | 0 -> x0
  | 1 -> x1
  | 2 -> x2
  | 3 -> x3
  | 4 -> x4
  | 5 -> x5
  | 6 -> x6
  | 7 -> x7
  )

(*** Circuits ***)

inline_for_extraction noextract
type gate (m:nat) (c:nat) =
| Zeros
| Ones
| Input : (i:nat{i<m}) -> gate m c
| Xor : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Xnor : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| And : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Or : (a:nat{a<c}) -> (b:nat{b<c}) -> gate m c
| Not : (a:nat{a<c}) -> gate m c

inline_for_extraction noextract
type circuit (m p:nat) = (i:nat{i<p}) -> gate m i

inline_for_extraction noextract
val circuit_def (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) : xN.t
inline_for_extraction noextract
let rec circuit_def circ x i =
  match circ i with
  | Input j -> index x j
  | Ones -> (_).ones_
  | Zeros -> (_).zeros_
  | Xor a b -> (_).xor_ (circuit_def circ x a) (circuit_def circ x b)
  | Xnor a b -> (_).xnor_ (circuit_def circ x a) (circuit_def circ x b)
  | And a b -> (_).and_ (circuit_def circ x a) (circuit_def circ x b)
  | Or a b -> (_).or_ (circuit_def circ x a) (circuit_def circ x b)
  | Not a -> (_).not_ (circuit_def circ x a)


val circuit_def_lemma (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'-1}) :
  Lemma (circuit_def #_ #(m'-1) circ x i == circuit_def #_ #m' circ x i)
  [SMTPat (circuit_def #m #m' circ x i)]
let rec circuit_def_lemma circ x i =
  match circ i with
  | Input j -> ()
  | Ones -> ()
  | Zeros -> ()
  | Xor a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Xnor a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | And a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Or a b -> circuit_def_lemma circ x a; circuit_def_lemma circ x b
  | Not a -> circuit_def_lemma circ x a

inline_for_extraction noextract
let circuit_spec_upd (#m #m':IT.size_nat) (circ:circuit m m')
  (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (cur:nat{cur<m'})
  (y:xNxM xN m'{forall (i:nat{i<cur}). index y i == circuit_def circ x i}) :
  (z:xNxM xN m'{forall (i:nat{i<=cur}). index z i == circuit_def circ x i})
  =
  Seq.upd y cur (
    let g = circ cur in
    match g with
    | Input i -> index x i
    | Zeros -> (_).zeros_
    | Ones -> (_).ones_
    | Xor a b -> (_).xor_ (index y a) (index y b)
    | Xnor a b -> (_).xnor_ (index y a) (index y b)
    | And a b -> (_).and_ (index y a) (index y b)
    | Or a b -> (_).or_ (index y a) (index y b)
    | Not a -> (_).not_ (index y a)
  )

[@@(strict_on_arguments [5;7])]
inline_for_extraction noextract
let rec circuit_spec_aux (#m #m':IT.size_nat) (circ:circuit m m')
  (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (cur:nat{cur<=m'})
  (y:xNxM xN m'{forall (i:nat{i<cur}). index y i == circuit_def circ x i}) :
  Tot
    (z:xNxM xN m'{forall (i:nat{i<m'}). index z i == circuit_def circ x i})
    (decreases m'-cur)
  =
  if cur = m' then
    y
  else
    circuit_spec_aux circ x (cur+1) (circuit_spec_upd circ x cur y)

inline_for_extraction noextract
val circuit_spec (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) :
    (y:xNxM xN m'{forall (i:nat{i<m'}). index y i == circuit_def circ x i})
inline_for_extraction noextract
let circuit_spec circ x = circuit_spec_aux circ x 0 (xNxM_mk _ _ (fun _ -> (_).zeros_))

val circuit_spec_lemma (#m #m':IT.size_nat) (circ:circuit m m') (#n:IT.size_nat) (#xN:sig n) (x:xNxM xN m) (i:nat{i<m'}) :
  Lemma (index (circuit_spec circ x) i == circuit_def circ x i)
  [SMTPat (index (circuit_spec circ x) i)]
let circuit_spec_lemma circ x i = ()

private val sliceable_circuit_lemma
  (#m #m':IT.size_nat)
  (circ:circuit m m')
  (#n:IT.size_nat)
  (#xN:sig n)
  (x:xNxM xN m)
  (i:nat{i<m'})
  (j:nat{j<n})
  : Lemma ( xN.v (circuit_def circ x i) j == u1.v (circuit_def circ (column j x) i) 0 )
let rec sliceable_circuit_lemma circ x i j =
match circ i with
  | Ones -> ()
  | Zeros -> ()
  | Input _ -> ()
  | Xor a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Xnor a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | And a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Or a b -> sliceable_circuit_lemma circ x a j; sliceable_circuit_lemma circ x b j
  | Not a -> sliceable_circuit_lemma circ x a j

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

val xNxM_of_lbuffer (#n:IT.size_nat) (#xN:sig n) (#m:IT.size_nat) (h:mem) (b:B.lbuffer xN.t (IT.size m)) : GTot (xNxM xN m)
let xNxM_of_lbuffer #n #xN #m h b = B.as_seq h b

irreducible let reduce_attr : unit = ()

unfold
let normal (#a:Type) (x:a) : a =
 Pervasives.norm [
      delta_attr [`%reduce_attr];
      iota; zeta; primops; simplify]
    x

[@@reduce_attr]
inline_for_extraction noextract
val circuit_lowstar_aux (#m:IT.size_nat) (#m':IT.size_nat) (circ:circuit m m')
  (#n:IT.size_nat) (xN:sig n)
  (cur:nat{cur<=m'}) :
    (input:B.lbuffer xN.t (IT.size m)) ->
    (output:B.lbuffer xN.t (IT.size m')) ->
      Stack unit
      (requires (fun h ->
        B.live h input /\ B.live h output
        /\ B.disjoint input output
      ))
      (ensures  (fun h0 _ h1 ->
        B.modifies1 output h0 h1
        /\ (forall(j:nat{j<cur}). B.get h1 output j == circuit_def circ (xNxM_of_lbuffer h0 input) j)
      ))

#push-options "--z3rlimit 40"
inline_for_extraction noextract
let rec circuit_lowstar_aux #m #m' circ #n xN cur =
  if cur = 0 then

(fun _ _ -> ())
  else (
    let rec_call = circuit_lowstar_aux circ xN (cur-1) in
    let g : gate m (cur-1) = circ (cur-1) in
    match g with
      | Zeros ->    (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) xN.zeros_)
      | Ones ->     (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) xN.ones_)
      | Input i ->  (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) (B.index input (IT.size i)))
      | Xor a b ->  (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) (xN.xor_ (B.index output (IT.size a)) (B.index output (IT.size b))))
      | Xnor a b -> (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) (xN.xnor_ (B.index output (IT.size a)) (B.index output (IT.size b))))
      | And a b ->  (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) (xN.and_ (B.index output (IT.size a)) (B.index output (IT.size b))))
      | Or a b ->   (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) (xN.or_ (B.index output (IT.size a)) (B.index output (IT.size b))))
      | Not a ->    (fun input output -> rec_call input output; B.upd output (IT.size (cur-1)) (xN.not_ (B.index output (IT.size a))))
  )
#pop-options

inline_for_extraction noextract
val circuit_lowstar (#m #m':IT.size_nat) (circ:circuit m m')
  (#n:IT.size_nat) (xN:sig n) :
  Tot (
    (input:B.lbuffer xN.t (IT.size m)) ->
    (output:B.lbuffer xN.t (IT.size m')) ->
    Stack unit
      (requires (fun h ->
        B.live h input /\ B.live h output
        /\ B.disjoint input output
      ))
      (ensures  (fun h0 _ h1 ->
        (xNxM_of_lbuffer h1 output == circuit_spec circ (xNxM_of_lbuffer h0 input))
        /\ B.modifies1 output h0 h1
      ))
  )

inline_for_extraction noextract
let circuit_lowstar #m #m' circ #n xN input output =
  let h0 = get () in
  let r = normal (circuit_lowstar_aux circ xN m') input output in
  let h1 = get () in
  xNxM_eq_intro (xNxM_of_lbuffer h1 output) (circuit_spec circ (xNxM_of_lbuffer h0 input))

inline_for_extraction noextract
val reduce_output_lowstar
  (#m #m':(m:IT.size_nat{m>0}))
  (spec:((#n:IT.size_nat) -> (#xN:sig n) -> xNxM xN m -> xNxM xN m'))
  (#n:IT.size_nat) (xN:sig n)
  (impl:(
    (input:B.lbuffer xN.t (IT.size m)) ->
    (output:B.lbuffer xN.t (IT.size m')) ->
    Stack unit
      (requires (fun h ->
        B.live h input /\ B.live h output
        /\ B.disjoint input output
      ))
      (ensures  (fun h0 _ h1 ->
        (xNxM_of_lbuffer h1 output == spec (xNxM_of_lbuffer h0 input))
        /\ B.modifies1 output h0 h1
      ))
  ))
  (m'':IT.size_nat{m''>0})
  (r:((i:nat{i<m''}) -> (j:nat{j<m'})))
  :
  Tot (
    (input:B.lbuffer xN.t (IT.size m)) ->
    (output:B.lbuffer xN.t (IT.size m'')) ->
    Stack unit
      (requires (fun h ->
        B.live h input /\  B.live h output
        /\ B.disjoint input output
      ))
      (ensures  (fun h0 _ h1 ->
        (xNxM_of_lbuffer h1 output == reduce_output spec m'' r (xNxM_of_lbuffer h0 input))
        /\ B.modifies1 output h0 h1
      ))
  )

inline_for_extraction noextract
let reduce_output_lowstar #m #m' spec xN impl m'' r =
  normal (
    fun (input:B.lbuffer xN.t (IT.size m)) (output:B.lbuffer xN.t (IT.size m'')) ->
    let h0 = get () in
    push_frame ();
    let tmp : B.lbuffer xN.t (IT.size m') = B.create (IT.size m') (xN.zeros_) in
    impl input tmp;
    let h1 = get () in
    let rec aux (i:nat{i<=m''}) : Stack unit
      (requires fun h0 -> B.live h0 output /\ B.live h0 tmp)
      (ensures fun h0 _ h1 ->
        B.modifies1 output h0 h1 /\ B.live h1 output /\ B.live h1 tmp /\
        (forall (j:nat{j<i}). B.get h1 output j == B.get h0 tmp (r j))
        )
      =
      if i = 0 then
        ()
      else (
        aux (i-1);
        let o = B.index tmp (IT.size (r (i-1))) in
        B.upd #_ #(IT.size m'') output (IT.size (i-1)) o
      )
    in
    aux m'';
    let h2 = get () in
    xNxM_eq_intro (xNxM_of_lbuffer h2 output) (reduce_output spec m'' r (xNxM_of_lbuffer h0 input));
    pop_frame();
    ()
  )


(*** of_uint and to_uint ***)

inline_for_extraction noextract
val to_uint (#m:IT.size_nat{m>0}) (x:u1xM m) : uint_t m
inline_for_extraction noextract
let to_uint #m x = FStar.UInt.from_vec (FStar.Seq.init m (index x))

inline_for_extraction noextract
val of_uint (#m:IT.size_nat{m>0}) (p:uint_t m) : u1xM m
inline_for_extraction noextract
let of_uint #m p = u1xM_mk _ (FStar.UInt.nth p)

val to_uint_of_uint (#m:IT.size_nat{m>0}) (p:uint_t m) :
  Lemma (to_uint (of_uint p) == p)
  [SMTPat (to_uint (of_uint p))]
let to_uint_of_uint #m p = FStar.UInt.nth_lemma (to_uint (of_uint p)) p

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

inline_for_extraction noextract
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

inline_for_extraction noextract
val bruteforce
  (#m:IT.size_nat{m>0}) (#m':IT.size_nat{m'>0})
  (impl:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable impl})
  (spec:(uint_t m -> uint_t m'))
  : (r:bool{
      if r then
        forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
        column j (impl x) == of_uint (spec (to_uint (column j x)))
      else
        True
    })
inline_for_extraction noextract
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

let bruteforce_lemma
  (#m:IT.size_nat{m>0}) (#m':IT.size_nat{m'>0})
  (impl:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable impl})
  (spec:(uint_t m -> uint_t m')) :
  Lemma
    (requires bruteforce impl spec == true)
    (ensures
      forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
      column j (impl x) == of_uint (spec (to_uint (column j x)))
    ) =
  ()

(*** Bruteforce lemmas and tactics using reveresed bit order ***)

let rec rev_vec (#n:nat) (vec: FStar.Seq.seq bool {FStar.Seq.length vec = n}) : 
    (v: FStar.Seq.seq bool {FStar.Seq.length v = n /\
      (forall (i:nat{i < n}). FStar.Seq.index v (n - i - 1) = FStar.Seq.index vec i)}) 
  =
  admit();
  if n = 0 then FStar.Seq.empty #bool
  else if n = 1 then FStar.Seq.create 1 (FStar.Seq.index vec 0)
  else FStar.Seq.append (rev_vec #(n - 1) (FStar.Seq.slice vec 1 n)) (FStar.Seq.create 1 (FStar.Seq.index vec 0))

inline_for_extraction noextract
val to_uint_rev (#m:IT.size_nat{m>0}) (x:u1xM m) : uint_t m
inline_for_extraction noextract
let to_uint_rev #m x = from_vec (rev_vec #m (FStar.Seq.init m (FStar.Seq.index x)))

inline_for_extraction noextract
val of_uint_rev (#m:IT.size_nat{m>0}) (p:uint_t m) : u1xM m
inline_for_extraction noextract
let of_uint_rev #m p = u1xM_mk _ (FStar.Seq.index (rev_vec #m (to_vec p)))

val of_uint_to_uint_rev (#m:IT.size_nat{m>0}) (x:u1xM m) :
  Lemma (of_uint_rev (to_uint_rev x) == x)
  [SMTPat (of_uint_rev (to_uint_rev x))]
let of_uint_to_uint_rev x = xNxM_eq_intro (of_uint_rev (to_uint_rev x)) x

val forall_uint_rev_lemma (#m:IT.size_nat{m>0}) (phi:u1xM m -> Type0) :
  Lemma
    (requires forall (i:uint_t m). phi (of_uint_rev i))
    (ensures forall x. phi x)
let forall_uint_rev_lemma phi =
  FStar.Classical.forall_intro (fun x -> of_uint_to_uint_rev x <: Lemma (phi x))

inline_for_extraction noextract
val bruteforce_rev
  (#m:IT.size_nat{m>0}) (#m':IT.size_nat{m'>0})
  (impl:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable impl})
  (spec:(uint_t m -> uint_t m'))
  : (r:bool{
      if r then
        forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
        column j (impl x) == of_uint_rev (spec (to_uint_rev (column j x)))
      else
        True
    })
inline_for_extraction noextract
let bruteforce_rev #m #m' impl spec =
  let phi0 (x:u1xM m) : Type0 = impl x == (of_uint_rev (spec (to_uint_rev x)) <: u1xM m') in
  let phi1 (i:uint_t m) : bool = u1xM_eq (impl (of_uint_rev i)) (of_uint_rev (spec i) <: u1xM m') in
  let r = bruteforce_aux m phi1 in
  if r then (
    FStar.Classical.forall_intro (fun (i:uint_t m) ->
      u1xM_eq_lemma (impl (of_uint_rev i)) (of_uint_rev (spec i) <: u1xM m')
      <: Lemma (impl (of_uint_rev i) == (of_uint_rev (spec i) <: u1xM m'))
    );
    forall_uint_rev_lemma phi0;
    true
  ) else false

let bruteforce_rev_lemma
  (#m:IT.size_nat{m>0}) (#m':IT.size_nat{m'>0})
  (impl:(#n:IT.size_nat -> #xN:sig n -> xNxM xN m -> xNxM xN m'){sliceable impl})
  (spec:(uint_t m -> uint_t m')) :
  Lemma
    (requires bruteforce_rev impl spec == true)
    (ensures
      forall (n:IT.size_nat) (xN:sig n) (x:xNxM xN m) (j:nat{j<n}).
      column j (impl x) == of_uint_rev (spec (to_uint_rev (column j x)))
    ) =
  ()

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

(*** Bitmaps ***)

inline_for_extraction noextract
val uN (t:IT.inttype{IT.unsigned t}) (l:IT.secrecy_level) : (xN:sig (IT.bits t){xN.t == IT.int_t t l})
inline_for_extraction noextract
let uN t l =
{ t = IT.int_t t l
; v = (fun x i -> FStar.UInt.nth #(IT.bits t) (IT.v x) i)
; mk = (fun f -> IT.mk_int (UInt.from_vec #(IT.bits t) (FStar.Seq.init (IT.bits t) f)))
; mk_def = (fun f i -> ())
; ones_ = IT.ones t l
; zeros_ = IT.zeros t l
; and_ = IT.logand
; xor_ = IT.logxor
; xnor_ = (fun x y -> IT.logor (IT.logand (IT.lognot x) (IT.lognot y)) (IT.logand x y))
; or_ = IT.logor
; not_ = IT.lognot
; zeros_spec = (fun i -> UInt.zero_nth_lemma #(IT.bits t) i)
; ones_spec = (fun i -> UInt.ones_nth_lemma #(IT.bits t) i)
; and_spec = (fun x y i -> IT.logand_spec x y)
; xor_spec = (fun x y i -> IT.logxor_spec x y)
; xnor_spec = (fun x y i ->
    IT.lognot_spec x; IT.lognot_spec y;
    IT.logand_spec x y; IT.logand_spec (IT.lognot x) (IT.lognot y);
    IT.logor_spec (IT.logand (IT.lognot x) (IT.lognot y)) (IT.logand x y)
  )
; or_spec = (fun x y i -> IT.logor_spec x y)
; not_spec = (fun x i -> IT.lognot_spec x)
}

inline_for_extraction noextract
val uN_eq
  (#t1 #t2:(t:IT.inttype{IT.unsigned t})) (#l:IT.secrecy_level)
  (x:(uN t1 l).t) (y:(uN t2 l).t) : Type0
inline_for_extraction noextract
let uN_eq x y = forall i. (_).v x i == (_).v y i

inline_for_extraction noextract
val uN_shift_left
  (#t:IT.inttype{IT.unsigned t}) (#l:IT.secrecy_level)
  (x:(uN t l).t) (k:nat{k<IT.bits t}) :
  Pure (uN t l).t
    (requires True)
    (ensures fun y -> forall (i:nat{i<IT.bits t-k}). (_).v y i == (_).v x (i+k))
inline_for_extraction noextract
let uN_shift_left #t #l x k =
  let y : (uN t l).t = IT.shift_left #t #l x (IT.size k) in
  let aux (i:nat{i<IT.bits t-k}) : Lemma ((_).v y i == (_).v x (i+k)) =
    if IT.bits t=0 then
      ()
    else
      FStar.UInt.shift_left_lemma_2 #(IT.bits t) (IT.v #t #l x) k i
  in
  FStar.Classical.forall_intro aux;
  y

inline_for_extraction noextract
val uN_shift_right
  (#t:IT.inttype{IT.unsigned t}) (#l:IT.secrecy_level) (#n:nat{n<=IT.bits t})
  (x:(uN t l).t) (k:nat{k<IT.bits t}) :
  Pure (uN t l).t
    (requires True)
    (ensures fun y -> forall (i:nat{i<n}). (_).v y i == (if i<k then false else (_).v x (i-k)))
inline_for_extraction noextract
let uN_shift_right #t #l #n x k =
  let y : (uN t l).t = IT.shift_right #t #l x (IT.size k) in
  let aux (i:nat{i<n}) : Lemma ((_).v y i == (if i<k then false else (_).v x (i-k))) =
    if n=0 then (
      ()
    ) else if i<k then (
      FStar.UInt.shift_right_lemma_1 #(IT.bits t) (IT.v #t #l x) k i
    ) else (
      FStar.UInt.shift_right_lemma_2 #(IT.bits t) (IT.v #t #l x) k i
    )
  in
  FStar.Classical.forall_intro aux;
  y

inline_for_extraction noextract
let uNxM (t:IT.inttype{IT.unsigned t}) (l:IT.secrecy_level) (m:IT.size_nat) : Type0 =
  xNxM (uN t l) m

inline_for_extraction noextract
let uNx8 (t:IT.inttype{IT.unsigned t}) (l:IT.secrecy_level) : Type0 =
  xNxM (uN t l) 8

inline_for_extraction noextract
let uNx8_mk (#t:IT.inttype{IT.unsigned t}) (#l:IT.secrecy_level)
  (u0 u1 u2 u3 u4 u5 u6 u7:(uN t l).t) : uNx8 t l =
  xNx8_mk u0 u1 u2 u3 u4 u5 u6 u7
