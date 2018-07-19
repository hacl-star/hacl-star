module Spec.Random

open Lib.IntTypes
open Lib.ByteSequence

assume val write: len:size_nat -> lbytes len -> Tot unit
assume val gen: len:size_nat -> Tot (lbytes len)

