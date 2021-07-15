module Hacl.Impl.EC.LowLevel

open Lib.Buffer
module T = FStar.Tactics

#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(* To debug in the interactive mode, uncomment this *)
friend Hacl.Bignum
friend Lib.Buffer
friend Lib.Loops
friend Lib.IntTypes

#set-options "--admit_smt_queries true"

let mul #c f r out =
  let h0 = ST.get() in
  [@inline_let]
  let len = Spec.ECC.Curves.getCoordinateLenU64 c in
  Hacl.Bignum.bn_mul len len f r out;
//  Hacl.Bignum.bn_mul (Spec.ECC.Curves.getCoordinateLenU64 c) (Spec.ECC.Curves.getCoordinateLenU64 c) f r out;
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
    "inline_for_extraction";
    "unfold";
    "pure_subterms_within_computations"
  ]; zeta ];
  T.dump "after norm";
  T.trefl ()

(* TODO: replace with postprocess_for_extraction_with once done *)

[@@ Tactics.postprocess_for_extraction_with
  (all_loops_are_constant [
    `%Hacl.Bignum.bn_mul;
    `%Hacl.Bignum.Multiplication.bn_mul;
    `%mul
  ]) ]
let mul_p256 f r out =
  mul #P256 f r out

(* For the "OCaml code contains calls to norm" bug, see
Hacl.Impl.EC.LowLevel.fst_bug and instructions in there *)
