module Hacl.Impl.Curve25519.Field64.Core

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
open FStar.Calc

friend Lib.Buffer
friend Lib.IntTypes

module FA = Fadd_stdcalls

/// We are trying to connect HACL* abstractions with regular F* libraries, so in
/// addition to ``friend``'ing ``Lib.*``, we also write a couple lemmas that we
/// prove via normalization to facilitate the job of proving that calling the
/// Vale interop signatures faithfully implements the required HACL* signature.

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

let buffer_is_buffer a len: Lemma
  (ensures (lbuffer a len == b:B.buffer a{B.length b == UInt32.v len}))
  [ SMTPat (lbuffer a len) ]
=
  assert_norm (lbuffer a len == b:B.buffer a{B.length b == UInt32.v len})

let as_nat_is_as_nat (b:lbuffer uint64 4ul) (h:HS.mem): Lemma
  (ensures (FA.as_nat b h == as_nat h b))
  [ SMTPat (as_nat h b) ]
=
  ()

let _: squash (Fast_defs.prime = Spec.Curve25519.prime) =
  assert_norm (Fast_defs.prime = Spec.Curve25519.prime)

// This one only goes through in a reasonable amount of rlimit thanks to
// ``as_nat_is_as_nat`` and ``buffer_is_buffer`` above.
[@ CInline]
let add1 out f1 f2 =
  if EverCrypt.TargetConfig.gcc then
    Fadd_inline.add1_inline out f1 f2
  else
    Fadd_stdcalls.add1 out f1 f2

// Spec discrepancy. Need to call the right lemma from FStar.Math.Lemmas.
[@ CInline]
let fadd out f1 f2 =
  let h0 = ST.get () in
  FStar.Math.Lemmas.modulo_distributivity
    (FA.as_nat f1 h0) (FA.as_nat f2 h0) Fast_defs.prime;
  if EverCrypt.TargetConfig.gcc then
    Fadd_inline.fadd_inline out f1 f2
  else
    Fadd_stdcalls.fadd out f1 f2

[@ CInline]
let fsub out f1 f2 =
  let h0 = ST.get() in
  let aux () : Lemma (P.fsub (fevalh h0 f1) (fevalh h0 f2) == (FA.as_nat f1 h0 - FA.as_nat f2 h0) % Fast_defs.prime) =
    let a = P.fsub (fevalh h0 f1) (fevalh h0 f2) in
    let a1 = (as_nat h0 f1 % Fast_defs.prime - as_nat h0 f2 % Fast_defs.prime) % Fast_defs.prime in
    let a2 = (as_nat h0 f1 % Fast_defs.prime - as_nat h0 f2) % Fast_defs.prime in
    let a3 = (as_nat h0 f1 - as_nat h0 f2) % Fast_defs.prime in
    let b = (FA.as_nat f1 h0 - FA.as_nat f2 h0) % Fast_defs.prime in
    calc (==) {
      a;
      == { }
      a1;
      == { FStar.Math.Lemmas.lemma_mod_sub_distr (as_nat h0 f1 % Fast_defs.prime) (as_nat h0 f2)
        Fast_defs.prime }
      a2;
      == { FStar.Math.Lemmas.lemma_mod_add_distr (- as_nat h0 f2) (as_nat h0 f1) Fast_defs.prime }
      a3;
      == { }
      b;
    }
  in aux();
  if EverCrypt.TargetConfig.gcc then
    Fadd_inline.fsub_inline out f1 f2
  else
    Fsub_stdcalls.fsub out f1 f2

let lemma_fmul_equiv (h0:HS.mem) (f1 f2:u256) : Lemma 
  (P.fmul (fevalh h0 f1) (fevalh h0 f2) == (FA.as_nat f1 h0 * FA.as_nat f2 h0) % Fast_defs.prime)
  = let a = P.fmul (fevalh h0 f1) (fevalh h0 f2) in
    let a1 = ((as_nat h0 f1 % Fast_defs.prime) * (as_nat h0 f2 % Fast_defs.prime)) % Fast_defs.prime in
    let a2 = ((as_nat h0 f1 % Fast_defs.prime) * as_nat h0 f2) % Fast_defs.prime in
    let a3 = (as_nat h0 f1 * as_nat h0 f2) % Fast_defs.prime in
    let b = (FA.as_nat f1 h0 * FA.as_nat f2 h0) % Fast_defs.prime in
    calc (==) {
      a;
      == { }
      a1;
      == { FStar.Math.Lemmas.lemma_mod_mul_distr_r (as_nat h0 f1 % Fast_defs.prime) (as_nat h0 f2) Fast_defs.prime }
      a2;
      == { FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat h0 f1) (as_nat h0 f2) Fast_defs.prime }
      a3;
      == { }
      b;
    }

[@ CInline]
let fmul out f1 f2 tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 f1 f2;
  if EverCrypt.TargetConfig.gcc then
    Fmul_inline.fmul_inline (sub tmp 0ul 8ul) f1 out f2
  else
    Fmul_stdcalls.fmul (sub tmp 0ul 8ul) f1 out f2

[@ CInline]
let fmul2 out f1 f2 tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 (gsub f1 0ul 4ul) (gsub f2 0ul 4ul);
  lemma_fmul_equiv h0 (gsub f1 4ul 4ul) (gsub f2 4ul 4ul);
  if EverCrypt.TargetConfig.gcc then
    Fmul_inline.fmul2_inline tmp f1 out f2
  else
    Fmul_stdcalls.fmul2 tmp f1 out f2

[@ CInline]
let fmul1 out f1 f2 =
  let h0 = ST.get() in
  let aux () : Lemma (P.fmul (fevalh h0 f1) (v f2) == (FA.as_nat f1 h0 * v f2) % Fast_defs.prime) =
    let a = P.fmul (fevalh h0 f1) (v f2) in
    let a1 =  ((as_nat h0 f1 % Fast_defs.prime) * v f2) % Fast_defs.prime in
    let a2 = (as_nat h0 f1 * v f2) % Fast_defs.prime in
    let b = (FA.as_nat f1 h0 * v f2) % Fast_defs.prime in
    calc (==) {
      a;
      == { }
      a1;
      == { FStar.Math.Lemmas.lemma_mod_mul_distr_l (as_nat h0 f1) (v f2) Fast_defs.prime }
      a2;
      == { }
      b;
    }
  in aux();
  assert_norm (pow2 17 = 131072);
  if EverCrypt.TargetConfig.gcc then
    Fmul_inline.fmul1_inline out f1 f2
  else
    Fmul_stdcalls.fmul1 out f1 f2

[@ CInline]
let fsqr out f1 tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 f1 f1;
  if EverCrypt.TargetConfig.gcc then
    Fsqr_inline.fsqr_inline tmp f1 out
  else
    Fsqr_stdcalls.fsqr tmp f1 out

[@ CInline]
let fsqr2 out f tmp =
  let h0 = ST.get() in
  lemma_fmul_equiv h0 (gsub f 0ul 4ul) (gsub f 0ul 4ul);
  lemma_fmul_equiv h0 (gsub f 4ul 4ul) (gsub f 4ul 4ul);
  if EverCrypt.TargetConfig.gcc then
    Fsqr_inline.fsqr2_inline tmp f out
  else
    Fsqr_stdcalls.fsqr2 tmp f out

[@ CInline]
let cswap2 bit p1 p2 =
  let h0 = ST.get() in
  if EverCrypt.TargetConfig.gcc then
    Fswap_inline.cswap2_inline p1 p2 bit
  else
    Fswap_stdcalls.cswap2 p1 p2 bit;
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
