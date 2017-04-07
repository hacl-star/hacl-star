module Spec.Sha512

open FStar.Mul

open Spec.SHA2.Core

let sha512 input = hash' input
