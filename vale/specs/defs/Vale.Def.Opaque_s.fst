module Vale.Def.Opaque_s
open FStar.Mul

let opaque_make #a x = x

let opaque_reveal #a s x1 x2 =
  norm_spec [delta_only [s]] (x1 == opaque_make x2)

let opaque_assert #a s x1 x2 p =
  norm_spec [delta_only [s]] (x1 == opaque_make x2)

let opaque_revealer #a s x1 x2 =
  fun () -> opaque_reveal s x1 x2
