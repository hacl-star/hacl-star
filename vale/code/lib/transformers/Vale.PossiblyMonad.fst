module Vale.PossiblyMonad

/// Similar to the [maybe] monad in Haskell (which is like the
/// [option] type in F* and OCaml), but instead, we also store the
/// reason for the error when the error occurs.

type possibly 'a =
  | Ok of 'a
  | Err of string

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
    (x:possibly t1{Ok? x ==> Ok?._0 x `has_type` t2}) : possibly t2 =
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
let (!!) (x:pbool) = Ok? x
