module Hacl.Spec.Bignum.Fsquare

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open Hacl.Bignum.Constants
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint

val fsquare_pre: s:seqelem -> GTot Type0

val fsquare_spec: s:seqelem{fsquare_pre s} -> Tot (s':seqelem{fsquare_pre s'})

let rec fsquare_times_tot (s:seqelem{fsquare_pre s}) (n:pos) : Tot (s':seqelem{fsquare_pre s'})
  (decreases n)
  =
  if n = 1 then (fsquare_spec s)
  else (cut (n > 1);
    let s' = fsquare_spec s in
    let s'' = fsquare_times_tot s' (n-1) in s'')
