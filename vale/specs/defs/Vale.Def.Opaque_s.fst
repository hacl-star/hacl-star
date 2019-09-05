module Vale.Def.Opaque_s
open FStar.Mul

let make_opaque (#a:Type) (x:a) = x
let reveal_opaque (#a:Type) (x:a)  = ()
