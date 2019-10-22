module Example

module I = Interface

open FStar.Mul

#set-options "--z3rlimit 200 --max_fuel 0 --max_ifuel 0"

// Somehow miraculously, this works.
%splice[
  double_round_inline;
  chacha20_core_inline;
  chacha20_init_inline;
  chacha20_encrypt_inline;
  chacha20_decrypt_inline
] (MetaInterface.specialize [
  `Hacl.Impl.Chacha20.Vec.chacha20_encrypt;
  `Hacl.Impl.Chacha20.Vec.chacha20_decrypt
])

let double_round_32 = double_round_inline #1
let chacha20_core_32 = chacha20_core_inline #1 double_round_32
let chacha20_init_32 = chacha20_init_inline #1
let chacha20_encrypt_32 = chacha20_encrypt_inline #1 chacha20_init_32 chacha20_core_32
let chacha20_decrypt_32 = chacha20_decrypt_inline #1 chacha20_init_32 chacha20_core_32

// Now on to the bugs -- on a smaller example.

#set-options "--print_bound_var_types --print_implicits --print_full_names"

// This is what comes out of the tactic.
(*
let times_two_inline_t =
  fun (#w2285: Interface.w) -> x2286: Interface.word w2285 -> Prims.Tot (Interface.word w2285)

let times_two_inline:
    #w2392: Interface.w
  -> Prims.Tot
    (arg_Interface_add2393: (fun (#w2394: Interface.w) -> Interface.add_st w2394) #w2392
        -> Prims.Tot (times_two_inline_t #w2392))
=
      fun
  (#w2365: Interface.w)
  (arg_Interface_add2366: (fun (#w2368: Interface.w) -> Interface.add_st w2368) #w2365)
  (x2367: Interface.word w2365)
  ->
  arg_Interface_add2366 x2367 x2367

let times_four_inline_t = fun (#w3040: Interface.w) -> x3041: Interface.word w3040 -> Prims.Tot (Interface.word w3040)

let times_four_inline:   #w3147: Interface.w
  -> Prims.Tot
    (arg_Interface_add3148: (fun (#w3149: Interface.w) -> Interface.add_st w3149) #w3147
        -> Prims.Tot (times_four_inline_t #w3147))
=
  fun
  (#w3120: Interface.w)
  (arg_Interface_add3121: (fun (#w3123: Interface.w) -> Interface.add_st w3123) #w3120)
  (x3122: Interface.word w3120)
  ->
  times_two_inline #w3120
    arg_Interface_add3121
    (times_two_inline #w3120 arg_Interface_add3121 x3122)

let times_sixteen_inline_t = fun (#w3675: Interface.w) -> x3676: Interface.word w3675 -> Prims.Tot (Interface.word w3675)
let times_sixteen_inline:
#w3740: Interface.w
  -> Prims.Tot
    (arg_Client_times_four3741: times_four_inline_t #w3740
        -> Prims.Tot (times_sixteen_inline_t #w3740))
=
fun
  (#w3742: Interface.w)
  (arg_Client_times_four3743: times_four_inline_t #w3742)
  (x3744: Interface.word w3742)
  ->
  arg_Client_times_four3743 (arg_Client_times_four3743 x3744)

let four_inline_t = fun (#w6290: Interface.w) -> Interface.word w6290
let four_inline:
    #w6354: Interface.w -> Prims.Tot (four_inline_t #w6354)
    =
    fun (#w6355: Interface.w) ->
  if Prims.op_Equality #Interface.w w6355 (Interface.W32)
  then 4ul
  else 4UL

let times_four'_inline_t = fun (#w7062: Interface.w) -> x7063: Interface.word w7062 -> Prims.Tot (Interface.word w7062)
let times_four'_inline:
  #w7127: Interface.w
  -> Prims.Tot
    (arg_Interface_mul7128: (fun (#w7129: Interface.w) -> Interface.mul_st w7129) #w7127
        -> Prims.Tot (times_four'_inline_t #w7127))
  =
  fun
  (#w7130: Interface.w)
  (arg_Interface_mul7131: (fun (#w7133: Interface.w) -> Interface.mul_st w7133) #w7130)
  (x7132: Interface.word w7130)
  ->
  arg_Interface_mul7131 (four_inline #w7130) x7132

let times_sixteen'_inline_t = fun (#w7808: Interface.w) -> x7809: Interface.word w7808 -> Prims.Tot (Interface.word w7808)
let times_sixteen'_inline:
#w7873: Interface.w
  -> Prims.Tot
    (arg_Client_times_four7874: times_four_inline_t #w7873
        -> Prims.Tot
          (arg_Interface_mul7875: (fun (#w7876: Interface.w) -> Interface.mul_st w7876) #w7873
              -> Prims.Tot (times_sixteen'_inline_t #w7873)))
=
fun
  (#w7877: Interface.w)
  (arg_Client_times_four7878: times_four_inline_t #w7877)
  (arg_Interface_mul7879: (fun (#w7881: Interface.w) -> Interface.mul_st w7881) #w7877)
  (x7880: Interface.word w7877)
  ->
  arg_Client_times_four7878 (times_four'_inline #w7877 arg_Interface_mul7879 x7880)

*)

let _: squash (inversion I.w) = allow_inversion I.w

#set-options "--max_fuel 0 --max_ifuel 0"

// BUG: this is what the tactic generates (see debug output)

let four_inline_t': #w1639: Interface.w -> Prims.Tot Type0 = fun (#w1640: Interface.w) -> Interface.word w1640
let four_inline': #w1700: Interface.w -> Prims.Tot (four_inline_t' #w1700) =
fun (#w1701: Interface.w) ->
  if Prims.op_Equality #Interface.w w1701 (Interface.W32)
  then 4ul
  else 4UL

let u1 = ()

// But when trying to actually call the tactic, I get:
//   Expected type "Example.four_inline_t #w1870"; but "FStar.UInt32.__uint_to_t
//     4" has type "FStar.UInt32.t"
// There seems to be a proof obligation emitted to Z3 when splicing; I don't
// understand what the query is, and why it shows up.
//
// Note that the problem is somewhere in the definition of four_inline since
// commenting out line 172 of the tactic fixes the problem.
%splice[
  //times_four_inline;
  //times_sixteen_inline;
  //times_sixteen'_inline
] (MetaInterface.specialize [ `Client.four ])
//] (MetaInterface.specialize [ `Client.times_sixteen; `Client.times_sixteen' ])

let add: I.add_st I.W32 = FStar.UInt32.add_mod
let mul: I.mul_st I.W32 = FStar.UInt32.mul_mod
// let times_four = times_four_inline add
// let times_sixteen = times_sixteen_inline times_four
// let times_sixteen' = times_sixteen'_inline times_four mul
