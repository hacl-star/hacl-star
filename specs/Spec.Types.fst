module Spec.Types

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq

type lbytes (s:size_t) = intseq U8 s
