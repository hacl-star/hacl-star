module Vale.Def.Opaque_s
open FStar.Mul

(*
Example usage:

// Defining an opaque function f:
let f_def (x y:int) : int =
  x + y
[@"opaque_to_smt"] let f = opaque_make f_def
irreducible let f_reveal = opaque_revealer (`%f) f f_def

// By default, f is opaque to both the normalizer/typechecker and the SMT solver:
assert (f 2 3 == 5) // should fail
assert_norm (f 2 3 == 5) // should fail

// Revealing f makes it transparent
f_reveal ();
assert (f 2 3 == 5) // should succeed

// You can also reveal f applied to specific arguments:
opaque_assert (`%f) f f_def (f 2 3 == f_def 2 3);
assert (f 2 3 == 5) // should succeed
assert (f 2 4 == 6) // should fail

// You can also reveal specific properties of f:
opaque_assert (`%f) f f_def (f 2 3 >= 5);
assert (f 2 3 >= 5) // should succeed
assert (f 2 3 == 5) // should fail

Notes:
- the "opaque_to_smt" hides f_def from the SMT solver
- the opaque_make function prevents the type checker from running out of memory in pathological cases (see expand_key_def)
- the delta_only [s] prevents the normalizer from running out of memory in pathological cases (see gcm_encrypt_LE)
*)

val opaque_make (#a:Type) (x:a) : a

val opaque_reveal (#a:Type) (s:string) (x1 x2:a) : Lemma
  (requires norm [delta_only [s]] (x1 == opaque_make x2))
  (ensures x1 == x2)

val opaque_assert (#a:Type) (s:string) (x1 x2:a) (p:Type0) : Lemma
  (requires norm [delta_only [s]] (x1 == opaque_make x2) /\ (x1 == x2 ==> p))
  (ensures p)

val opaque_revealer (#a:Type) (s:string) (x1 x2:a) : Pure (unit -> Lemma (x1 == x2))
  (requires norm [delta_only [s]] (x1 == opaque_make x2))
  (ensures fun _ -> True)
