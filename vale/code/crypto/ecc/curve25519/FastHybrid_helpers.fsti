module FastHybrid_helpers

open Words_s
open Types_s
open FStar.Mul
open FStar.Tactics
open CanonCommSemiring
open Fast_defs

let int_canon = fun _ -> canon_semiring int_cr //; dump "Final"

(*
open X64.Vale.Decls
open X64.Machine_s
let get_reg (to:tainted_operand{TReg? to}) : reg = TReg?.r to
*)
(*
unfold let p:nat = 57896044618658097711785492504343953926634992332820282019728792003956564819949 //(pow2 255) - 19

#reset-options "--z3rlimit 300 --max_fuel 0 --max_ifuel 0"
let test (a:nat) 
         (a0 a1 a2 a3:nat64)
         (a0' a1' a2' a3':nat64)
         (c:nat64) (b:bit) : Lemma
  (requires a == pow2_four a0 a1 a2 a3 /\ 
            pow2_five a0' a1' a2' a3' b == a + c * 38 /\
            True)
  (ensures (pow2_four (a0' + b * 38) a1' a2' a3') % p = (a + c) % p)
  =
  assert_norm (pow2_256 % p == 38);
  //admit();
  ()
*)
