module Example

open FStar.Mul

#set-options "--print_bound_var_types"

%splice[] (MetaInterface.specialize [ `Client.times_sixteen; `Client.times_sixteen' ])

let add: Interface.add_st = fun x y -> x + y
let mul: Interface.mul_st = fun x y -> x * y
let times_four = Client.times_four_inline add
let times_sixteen = Client.times_sixteen_inline times_four
let times_sixteen' = Client.times_sixteen'_inline times_four mul
