module Spec.Frodo.Random

open Lib.IntTypes
open Lib.Sequence

//val randombytes_init_: entropy_input:lseq uint8 48 -> unit

val randombytes_: len:size_nat -> res:lseq uint8 len
let randombytes_ len = create len (u8 0) //Just to extract the spec
