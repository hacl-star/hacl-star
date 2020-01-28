module Hacl.Impl.Curve25519.Field64.Vale

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
open FStar.Calc

friend Lib.Buffer
friend Lib.IntTypes

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul

open Lib.Sequence
open Lib.IntTypes
open Lib.Buffer

module B = Lib.Buffer
module S = Hacl.Spec.Curve25519.Field64.Definition
module P = Spec.Curve25519

module FA = Vale.Wrapper.X64.Fadd

module F64 = Hacl.Impl.Curve25519.Field64

/// We are trying to connect HACL* abstractions with regular F* libraries, so in
/// addition to ``friend``'ing ``Lib.*``, we also write a couple lemmas that we
/// prove via normalization to facilitate the job of proving that calling the
/// Vale interop signatures faithfully implements the required HACL* signature.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 300 --z3refresh"

let buffer_is_buffer a len: Lemma
  (ensures (lbuffer a len == b:B.buffer a{B.length b == UInt32.v len}))
  [ SMTPat (lbuffer a len) ]
=
  assert_norm (lbuffer a len == b:B.buffer a{B.length b == UInt32.v len})

let as_nat_is_as_nat (b:lbuffer uint64 4ul) (h:HS.mem): Lemma
  (ensures (FA.as_nat b h == F64.as_nat h b))
  [ SMTPat (as_nat h b) ]
=
  ()

let _: squash (Vale.Curve25519.Fast_defs.prime = Spec.Curve25519.prime) =
  assert_norm (Vale.Curve25519.Fast_defs.prime = Spec.Curve25519.prime)

// This one only goes through in a reasonable amount of rlimit thanks to
// ``as_nat_is_as_nat`` and ``buffer_is_buffer`` above.
[@ CInline]
let add_scalar out f1 f2 =
  if EverCrypt.TargetConfig.gcc then//
    Vale.Inline.X64.Fadd_inline.add_scalar out f1 f2
  else
    Vale.Wrapper.X64.Fadd.add_scalar_e out f1 f2

// Spec discrepancy. Need to call the right lemma from FStar.Math.Lemmas.
#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 400"
[@ CInline]
let fadd out f1 f2 =
  let h0 = ST.get () in
  let aux () : Lemma (P.fadd (F64.fevalh h0 f1) (F64.fevalh h0 f2) == (FA.as_nat f1 h0 + FA.as_nat f2 h0) % Vale.Curve25519.Fast_defs.prime) =
    let a = P.fadd (F64.fevalh h0 f1) (F64.fevalh h0 f2) in
    let a1 = (as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime + as_nat h0 f2 % Vale.Curve25519.Fast_defs.prime) % Vale.Curve25519.Fast_defs.prime in
    let a2 = (as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime + as_nat h0 f2) % Vale.Curve25519.Fast_defs.prime in
    let a3 = (as_nat h0 f1 + as_nat h0 f2) % Vale.Curve25519.Fast_defs.prime in
    let b = (FA.as_nat f1 h0 + FA.as_nat f2 h0) % Vale.Curve25519.Fast_defs.prime in
    calc (==) {
      a;
      == {  FStar.Math.Lemmas.modulo_distributivity
    (as_nat h0 f1) (as_nat h0 f2) Vale.Curve25519.Fast_defs.prime }
      a1;
      == {  FStar.Math.Lemmas.lemma_mod_add_distr (as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime)
      (as_nat h0 f2) Vale.Curve25519.Fast_defs.prime }
      a2;
      == { FStar.Math.Lemmas.lemma_mod_add_distr (as_nat h0 f2) (as_nat h0 f1) Vale.Curve25519.Fast_defs.prime }
      a3;
      == { }
      b;
    }
  in aux();
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fadd_inline.fadd out f1 f2
  else
    Vale.Wrapper.X64.Fadd.fadd_e out f1 f2
#pop-options

[@ CInline]
let fsub out f1 f2 =
  let h0 = ST.get() in
  let aux () : Lemma (P.fsub (F64.fevalh h0 f1) (F64.fevalh h0 f2) == (FA.as_nat f1 h0 - FA.as_nat f2 h0) % Vale.Curve25519.Fast_defs.prime) =
    let a = P.fsub (F64.fevalh h0 f1) (F64.fevalh h0 f2) in
    let a1 = (as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime - as_nat h0 f2 % Vale.Curve25519.Fast_defs.prime) % Vale.Curve25519.Fast_defs.prime in
    let a2 = (as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime - as_nat h0 f2) % Vale.Curve25519.Fast_defs.prime in
    let a3 = (as_nat h0 f1 - as_nat h0 f2) % Vale.Curve25519.Fast_defs.prime in
    let b = (FA.as_nat f1 h0 - FA.as_nat f2 h0) % Vale.Curve25519.Fast_defs.prime in
    calc (==) {
      a;
      == { }
      a1;
      == { FStar.Math.Lemmas.lemma_mod_sub_distr (as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime) (as_nat h0 f2)
        Vale.Curve25519.Fast_defs.prime }
      a2;
      == { FStar.Math.Lemmas.lemma_mod_add_distr (- as_nat h0 f2) (as_nat h0 f1) Vale.Curve25519.Fast_defs.prime }
      a3;
      == { }
      b;
    }
  in aux();
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fadd_inline.fsub out f1 f2
  else
    Vale.Wrapper.X64.Fsub.fsub_e out f1 f2

#push-options "--z3rlimit 200"
let lemma_fmul_equiv (h0:HS.mem) (f1 f2:F64.u256) : Lemma
  (P.fmul (F64.fevalh h0 f1) (F64.fevalh h0 f2) == (FA.as_nat f1 h0 * FA.as_nat f2 h0) % Vale.Curve25519.Fast_defs.prime)
  = let a = P.fmul (F64.fevalh h0 f1) (F64.fevalh h0 f2) in
    let a1 = ((F64.as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime) * (F64.as_nat h0 f2 % Vale.Curve25519.Fast_defs.prime)) % Vale.Curve25519.Fast_defs.prime in
    let a2 = ((F64.as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime) * F64.as_nat h0 f2) % Vale.Curve25519.Fast_defs.prime in
    let a3 = (F64.as_nat h0 f1 * F64.as_nat h0 f2) % Vale.Curve25519.Fast_defs.prime in
    let b = (FA.as_nat f1 h0 * FA.as_nat f2 h0) % Vale.Curve25519.Fast_defs.prime in
    calc (==) {
      a;
      == { }
      a1;
      == { FStar.Math.Lemmas.lemma_mod_mul_distr_r (F64.as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime) (F64.as_nat h0 f2) Vale.Curve25519.Fast_defs.prime }
      a2;
      == { FStar.Math.Lemmas.lemma_mod_mul_distr_l (F64.as_nat h0 f1) (F64.as_nat h0 f2) Vale.Curve25519.Fast_defs.prime }
      a3;
      == { }
      b;
    }
#pop-options

[@ CInline]
let fmul out f1 f2 tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 f1 f2;
  if EverCrypt.TargetConfig.gcc then (
    assert (disjoint f1 (gsub tmp 0ul 8ul));
    assert (disjoint f2 (gsub tmp 0ul 8ul));
    Vale.Inline.X64.Fmul_inline.fmul out f1 f2 (sub tmp 0ul 8ul)
  ) else
    Vale.Wrapper.X64.Fmul.fmul_e (sub tmp 0ul 8ul) f1 out f2

[@ CInline]
let fmul2 out f1 f2 tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 (gsub f1 0ul 4ul) (gsub f2 0ul 4ul);
  lemma_fmul_equiv h0 (gsub f1 4ul 4ul) (gsub f2 4ul 4ul);
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fmul_inline.fmul2 out f1 f2 tmp
  else
    Vale.Wrapper.X64.Fmul.fmul2_e tmp f1 out f2

[@ CInline]
let fmul_scalar out f1 f2 =
  let h0 = ST.get() in
  let aux () : Lemma (P.fmul (F64.fevalh h0 f1) (v f2) == (FA.as_nat f1 h0 * v f2) % Vale.Curve25519.Fast_defs.prime) =
    let a = P.fmul (F64.fevalh h0 f1) (v f2) in
    let a1 =  ((F64.as_nat h0 f1 % Vale.Curve25519.Fast_defs.prime) * v f2) % Vale.Curve25519.Fast_defs.prime in
    let a2 = (F64.as_nat h0 f1 * v f2) % Vale.Curve25519.Fast_defs.prime in
    let b = (FA.as_nat f1 h0 * v f2) % Vale.Curve25519.Fast_defs.prime in
    calc (==) {
      a;
      == { }
      a1;
      == { FStar.Math.Lemmas.lemma_mod_mul_distr_l (F64.as_nat h0 f1) (v f2) Vale.Curve25519.Fast_defs.prime }
      a2;
      == { }
      b;
    }
  in aux();
  assert_norm (pow2 17 = 131072);
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fmul_inline.fmul_scalar out f1 f2
  else
    Vale.Wrapper.X64.Fmul.fmul_scalar_e out f1 f2

[@ CInline]
let fsqr out f1 tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 f1 f1;
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fsqr_inline.fsqr out f1 tmp
  else
    Vale.Wrapper.X64.Fsqr.fsqr_e tmp f1 out

[@ CInline]
let fsqr2 out f tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 (gsub f 0ul 4ul) (gsub f 0ul 4ul);
  lemma_fmul_equiv h0 (gsub f 4ul 4ul) (gsub f 4ul 4ul);
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fsqr_inline.fsqr2 out f tmp
  else
    Vale.Wrapper.X64.Fsqr.fsqr2_e tmp f out

[@ CInline]
let cswap2 bit p1 p2 =
  let h0 = ST.get() in
  if EverCrypt.TargetConfig.gcc then
    Vale.Inline.X64.Fswap_inline.cswap2 bit p1 p2
  else
    Vale.Wrapper.X64.Fswap.cswap2_e bit p1 p2;
  let h1 = ST.get() in
  // Seq.equal is swapped in the interop wrappers, so the SMTPat is not matching:
  // We have Seq.equal s1 s2 but are trying to prove s2 == s1
  let aux1 () : Lemma
    (requires v bit == 1)
    (ensures as_seq h1 p1 == as_seq h0 p2 /\ as_seq h1 p2 == as_seq h0 p1)
    = Seq.lemma_eq_elim (B.as_seq h0 p2) (B.as_seq h1 p1);
      Seq.lemma_eq_elim (B.as_seq h0 p1) (B.as_seq h1 p2)
  in let aux2 () : Lemma
    (requires v bit == 0)
    (ensures as_seq h1 p1 == as_seq h0 p1 /\ as_seq h1 p2 == as_seq h0 p2)
    = Seq.lemma_eq_elim (B.as_seq h0 p1) (B.as_seq h1 p1);
      Seq.lemma_eq_elim (B.as_seq h0 p2) (B.as_seq h1 p2)
  in
  Classical.move_requires aux1 ();
  Classical.move_requires aux2 ()
