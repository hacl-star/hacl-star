module Lib.Arithmetic.SumsBuffer

open Lib.IntTypes
open Lib.Buffer

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring

open FStar.Tactics.Typeclasses
open FStar.HyperStack.All

module Buf = Lib.Buffer
module Seq = Lib.Sequence

inline_for_extraction
val sum_n:
  #a:Type0
  -> #[tcresolve ()] m: monoid a
  -> #n:size_t
  -> l:lbuffer a n
  -> Stack a (requires fun h -> live h l) (ensures fun h0 s h1 -> modifies0 h0 h1 /\ s == Lib.Arithmetic.Sums.sum_n h0.[|l|]) (decreases (v n))
