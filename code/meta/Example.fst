module Example

open FStar.Mul

#set-options "--print_bound_var_types"

%splice[
  times_four_inline;
  times_sixteen_inline;
  times_sixteen'_inline
] (MetaInterface.specialize [ `Client.times_sixteen; `Client.times_sixteen' ])

let add: Interface.add_st = fun x y -> x + y
let mul: Interface.mul_st = fun x y -> x * y
let times_four = times_four_inline add
let times_sixteen = times_sixteen_inline times_four
let times_sixteen' = times_sixteen'_inline times_four mul
