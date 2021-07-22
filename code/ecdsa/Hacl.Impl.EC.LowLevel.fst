module Hacl.Impl.EC.LowLevel

open Lib.Buffer
module T = FStar.Tactics

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(* To debug in the interactive mode, uncomment the below friend declarations:
   by friending those modules, we can unfold the definitions inside while in
   interactive mode (otherwise this would only be permitted at extraction time)
*)
(*
friend Hacl.Bignum
friend Lib.Buffer
friend Lib.Loops
friend Lib.IntTypes
*)

let mul #c f r out =
  let h0 = ST.get() in
  [@inline_let]
  let len = Spec.ECC.Curves.getCoordinateLenU64 c in
  Hacl.Bignum.bn_mul len len f r out;
  Hacl.Spec.Bignum.bn_mul_lemma (as_seq h0 f) (as_seq h0 r)

noextract
let all_loops_are_constant extra (): T.Tac unit =
  Tactics.norm [ primops; iota; simplify; delta_only ([
    `%Lib.Loops.for;
    `%Lib.Buffer.loop1;
    `%C.Loops.for;
    `%Lib.IntTypes.size;
    `%Lib.IntTypes.uint;
    `%Lib.IntTypes.mk_int;
    `%Lib.IntTypes.v;
    `%FStar.UInt32.op_Plus_Hat;
    `%Spec.ECC.Curves.getCoordinateLenU64;
    `%Lib.IntTypes.div;
    `%Lib.IntTypes.mul;
    `%Lib.IntTypes.add;
    "FStar.UInt32.__uint_to_t";
  ] @ extra); delta_qualifier [
    // Unfold the definitions tagged as `inline_for_extraction`
    "inline_for_extraction";
    // Unfold the definitions tagged as `unfold`
    "unfold";
    // Inline the `inline_let` bindings
    "pure_subterms_within_computations"
  ]; zeta ];
  T.dump "after norm";
  T.trefl ()

(* To debug the following, use `postprocess_with` instead
   of `postprocess_for_extraction_with`. This way you can
   interactively see the result of the normalization process.
   Of course, this only works if the proper modules have
   been friended before *)
[@@ Tactics.postprocess_for_extraction_with
  (all_loops_are_constant [
    `%Hacl.Bignum.bn_mul;
    `%Hacl.Bignum.Multiplication.bn_mul;
    `%mul
  ]) ]
let mul_p256 f r out =
  mul #P256 f r out
