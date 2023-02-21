module Spec.SHA3.Equivalence

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open FStar.Mul
open Lib.LoopCombinators

open Spec.SHA3.Constants
open Spec.SHA3

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

let state_chi_inner (y:index) (s:state) : Tot state =
  let v0  = get s 0 y ^. ((lognot (get s 1 y)) &. get s 2 y) in
  let v1  = get s 1 y ^. ((lognot (get s 2 y)) &. get s 3 y) in
  let v2  = get s 2 y ^. ((lognot (get s 3 y)) &. get s 4 y) in
  let v3  = get s 3 y ^. ((lognot (get s 4 y)) &. get s 0 y) in
  let v4  = get s 4 y ^. ((lognot (get s 0 y)) &. get s 1 y) in
  let s = set s 0 y v0 in
  let s = set s 1 y v1 in
  let s = set s 2 y v2 in
  let s = set s 3 y v3 in
  let s = set s 4 y v4 in
  s

let state_chi (s_pi_rho:state) : Tot state  =
  repeati 5 state_chi_inner s_pi_rho

let state_chi_inner_equivalence0 (st_old:state) (y:index) (st:state) :
  Lemma (requires (forall y'. (y' >= y /\ y' < 5) ==>
                   get st_old 0 y' == get st 0 y' /\
                   get st_old 1 y' == get st 1 y' /\
                   get st_old 2 y' == get st 2 y' /\
                   get st_old 3 y' == get st 3 y' /\
                   get st_old 4 y' == get st 4 y'))
        (ensures  (let st_new = state_chi_inner1 st_old y st in
                   st_new == state_chi_inner y st)) =
         Lib.LoopCombinators.eq_repeati0 5 (state_chi_inner0 st_old y) st;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner0 st_old y) st 0;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner0 st_old y) st 1;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner0 st_old y) st 2;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner0 st_old y) st 3;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner0 st_old y) st 4;
         assert (repeati 5 (state_chi_inner0 st_old y) st ==
                 state_chi_inner0 st_old y 4 (state_chi_inner0 st_old y 3 (state_chi_inner0 st_old y 2 (state_chi_inner0 st_old y 1 (state_chi_inner0 st_old y 0 st)))));
         
         ()

let state_chi_inner_equivalence1 (st_old:state) (y:index) (st_new:state) :
  Lemma (requires (st_new == state_chi_inner y st_old))
        (ensures (  (forall y'. (y' < 5 /\ y' > y) ==>
                    (get st_new 0 y' == get st_old 0 y' /\
                     get st_new 1 y' == get st_old 1 y' /\
                     get st_new 2 y' == get st_old 2 y' /\
                     get st_new 3 y' == get st_old 3 y' /\
                     get st_new 4 y' == get st_old 4 y')))) = ()

#push-options "--z3rlimit 50"
let state_chi_equivalence (st_old:state) :
  Lemma (state_chi st_old == Spec.SHA3.state_chi st_old) =
         Lib.LoopCombinators.eq_repeati0 5 (state_chi_inner1 st_old) st_old;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner1 st_old) st_old 0;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner1 st_old) st_old 1;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner1 st_old) st_old 2;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner1 st_old) st_old 3;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner1 st_old) st_old 4;
         Lib.LoopCombinators.eq_repeati0 5 (state_chi_inner) st_old;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner) st_old 0;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner) st_old 1;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner) st_old 2;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner) st_old 3;
         Lib.LoopCombinators.unfold_repeati 5 (state_chi_inner) st_old 4;
         let st1 = state_chi_inner1 st_old 0 st_old in
         let st2 = state_chi_inner1 st_old 1 st1 in
         let st3 = state_chi_inner1 st_old 2 st2 in
         let st4 = state_chi_inner1 st_old 3 st3 in
         let st5 = state_chi_inner1 st_old 4 st4 in
         let st1' = state_chi_inner 0 st_old in
         let st2' = state_chi_inner 1 st1' in
         let st3' = state_chi_inner 2 st2' in
         let st4' = state_chi_inner 3 st3' in
         let st5' = state_chi_inner 4 st4' in
         state_chi_inner_equivalence0 st_old 0 st_old;
         assert(st1 == st1');
         state_chi_inner_equivalence1 st_old 0 st1;
         state_chi_inner_equivalence0 st_old 1 st1;
         assert(st2 == st2');
         state_chi_inner_equivalence1 st1' 1 st2';
         state_chi_inner_equivalence0 st_old 2 st2;
         assert(st3 == st3');
         state_chi_inner_equivalence1 st2 2 st3;
         state_chi_inner_equivalence0 st_old 3 st3;
         assert(st4 == st4');
         state_chi_inner_equivalence1 st3 3 st4;
         state_chi_inner_equivalence0 st_old 4 st4;
         assert(st5 == st5');
         state_chi_inner_equivalence1 st4 4 st5;
         ()
#pop-options


