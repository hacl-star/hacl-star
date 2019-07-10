module Lib.Arithmetic.SumsBuffer

open FStar.Tactics.Typeclasses

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring


open FStar.HyperStack.All

module ST = FStar.HyperStack.ST
module Buf = Lib.Buffer
module Seq = Lib.Sequence

#reset-options "--z3rlimit 200 --max_fuel 1 --max_ifuel 1"


let sum_n #a [|monoid a|] #n l =
  let h = ST.get () in
  if (v n = 0) then (Lib.Arithmetic.Sums.sum_n_zero_elements_is_id h.[|l|]; id)
  else begin
  as_seq_gsub h l (size 1) (n -! (size 1));
  let s = sum_n (Buf.sub l (size 1) (n-! (size 1))) in
  Lib.Arithmetic.Sums.sum_n_simple_lemma1 h.[|l|];
  op #a l.(size 0) s end
