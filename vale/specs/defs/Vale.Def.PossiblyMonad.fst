module Vale.Def.PossiblyMonad

/// Similar to the [maybe] monad in Haskell (which is like the
/// [option] type in F* and OCaml), but instead, we also store the
/// reason for the error when the error occurs.

type possibly 'a =
  | Ok : v:'a -> possibly 'a
  | Err : reason:string -> possibly 'a

unfold let return (#a:Type) (x:a) : possibly a =
  Ok x

unfold let bind (#a #b:Type) (x:possibly a) (f:a -> possibly b) : possibly b =
  match x with
  | Err s -> Err s
  | Ok x' -> f x'

unfold let fail_with (#a:Type) (s:string) : possibly a = Err s

unfold let unimplemented (#a:Type) (s:string) : possibly a = fail_with ("Unimplemented: " ^ s)

(** Allows moving to a "looser" monad type, always *)
unfold
let loosen (#t1:Type) (#t2:Type{t1 `subtype_of` t2})
    (x:possibly t1) : possibly t2 =
  match x with
  | Ok x' -> Ok x'
  | Err s -> Err s

(** Allows moving to a "tighter" monad type, as long as the monad is
    guaranteed statically to be within this tighter type *)
unfold
let tighten (#t1:Type) (#t2:Type{t2 `subtype_of` t1})
    (x:possibly t1{Ok? x ==> Ok?.v x `has_type` t2}) : possibly t2 =
  match x with
  | Ok x' -> Ok x'
  | Err s -> Err s

(** [pbool] is a type that can be used instead of [bool] to hold on to
    a reason whenever it is [false]. To convert from a [pbool] to a
    bool, see [!!]. *)
unfold
type pbool = possibly unit

(** [!!x] coerces a [pbool] into a [bool] by discarding any reason it
    holds on to and instead uses it solely as a boolean. *)
unfold
let (!!) (x:pbool) : bool = Ok? x

(** [ttrue] is just the same as [true] but for a [pbool] *)
unfold
let ttrue : pbool = Ok ()

(** [ffalse] is the same as [false] but is for a [pbool] and thus requires a reason for being false. *)
unfold
let ffalse (reason:string) : pbool = Err reason

(** [b /- r] is the same as [b] but as a [pbool] that is set to reason [r] if [b] is false. *)
unfold
let (/-) (b:bool) (reason:string) : pbool =
  if b then
    ttrue
  else
    ffalse reason

(** [p /+> r] is the same as [p] but also appends [r] to the reason if it was false. *)
unfold
let (/+>) (p:pbool) (r:string) : pbool =
  match p with
  | Ok () -> Ok ()
  | Err rr -> Err (rr ^ r)

(** [p /+< r] is the same as [p] but also prepends [r] to the reason if it was false. *)
unfold
let (/+<) (p:pbool) (r:string) : pbool =
  match p with
  | Ok () -> Ok ()
  | Err rr -> Err (r ^ rr)

(** [&&.] is a short-circuiting logical-and. *)
let (&&.) (x y:pbool) : pbool =
  match x with
  | Ok () -> y
  | Err reason -> Err reason

(** [ ||. ] is a short-circuiting logical-or *)
let ( ||. ) (x y:pbool) : pbool =
  match x with
  | Ok () -> Ok ()
  | Err rx -> y /+< (rx ^ " and ")

(** [for_all f l] runs [f] on all the elements of [l] and performs a
    short-circuit logical-and of all the results *)
let rec for_all (f : 'a -> pbool) (l : list 'a) : pbool =
  match l with
  | [] -> ttrue
  | x :: xs -> f x &&. for_all f xs

(** Change from a [forall] to a [for_all] *)
let rec lemma_for_all_intro (f : 'a -> pbool) (l : list 'a) :
  Lemma
    (requires (forall x. {:pattern (x `List.Tot.memP` l)} (x `List.Tot.memP` l) ==> !!(f x)))
    (ensures !!(for_all f l)) =
  let open FStar.List.Tot in
  let aux l x :
    Lemma
      (requires (x `memP` l ==> !!(f x)))
      (ensures (Cons? l /\ x `memP` tl l ==> !!(f x))) = () in
  match l with
  | [] -> ()
  | x :: xs ->
    FStar.Classical.forall_intro (FStar.Classical.move_requires (aux l));
    lemma_for_all_intro f xs

(** Change from a [for_all] to a [forall] *)
let rec lemma_for_all_elim (f : 'a -> pbool) (l : list 'a) :
  Lemma
    (requires !!(for_all f l))
    (ensures (forall x. {:pattern (x `List.Tot.memP` l)} (x `List.Tot.memP` l) ==> !!(f x))) =
  match l with
  | [] -> ()
  | x :: xs ->
    lemma_for_all_elim f xs
