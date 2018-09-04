module Spec.Frodo.Random

open Lib.IntTypes
open Lib.Sequence

let state_t = seq uint8

assume val randombytes_init_: entropy_input:lseq uint8 48 -> state_t

assume val randombytes_: state:state_t -> len:size_nat -> (lseq uint8 len * state_t)
