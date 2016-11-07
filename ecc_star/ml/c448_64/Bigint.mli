open Prims
open Stdint
open UInt

type template = int -> int
type template_const = template
type 'a biginteger = | Bigint of 'a array * template

type bigint = limb biginteger
type bigint_wide = wide biginteger
type serialized = Uint8.t biginteger

val getRef: 'a biginteger -> 'a array
val getTemplate: 'b -> 'a biginteger -> template

val create_limb: int -> bigint
val create_wide: int -> bigint_wide
val create_wide_templ: int -> template -> bigint_wide
                          
val index_byte: serialized -> int -> uint8
val index_limb: bigint -> int -> limb
val index_wide: bigint_wide -> int -> wide

val upd_byte: serialized -> int -> uint8 -> unit
val upd_limb: bigint -> int -> limb -> unit
val upd_wide: bigint_wide -> int -> wide -> unit

val blit: int -> 'a biginteger -> 'a biginteger -> int -> unit
val blit_limb: bigint -> bigint -> int -> unit
val blit_wide: bigint_wide -> bigint_wide -> int -> unit                                              

val print_bigint': bigint -> unit
val print_bigint: bigint -> unit
