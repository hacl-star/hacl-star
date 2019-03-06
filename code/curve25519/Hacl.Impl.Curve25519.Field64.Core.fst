module Hacl.Impl.Curve25519.Field64.Core

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

friend Lib.Buffer
friend Lib.IntTypes

// TODO: this precondition needs to be threaded throughout the entire call-graph
// as opposed to assumed in scope here.

let _: squash (X64.CPU_Features_s.adx_enabled /\ X64.CPU_Features_s.bmi2_enabled) =
  admit ()

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
  (ensures (Fadd_stdcalls.as_nat b h == as_nat h b))
  [ SMTPat (as_nat h b) ]
=
  ()

let _: squash (Fast_defs.prime = Spec.Curve25519.prime) =
  assert_norm (Fast_defs.prime = Spec.Curve25519.prime)

// This one only goes through in a reasonable amount of rlimit thanks to
// ``as_nat_is_as_nat`` and ``buffer_is_buffer`` above.
[@ CInline]
let add1 out f1 f2 =
  Fadd_stdcalls.add1 out f1 f2

// Spec discrepancy. Need to call the right lemma from FStar.Math.Lemmas.
[@ CInline]
let fadd out f1 f2 =
  let h0 = ST.get () in
  Fadd_stdcalls.fadd out f1 f2;
  let h1 = ST.get () in
  let open Fadd_stdcalls in
  FStar.Math.Lemmas.modulo_distributivity
    (as_nat f1 h0) (as_nat f2 h0) Fast_defs.prime

[@ CInline]
let fsub out f1 f2 =
  admit ();
  Fsub_stdcalls.fsub out f1 f2

[@ CInline]
let fmul out f1 f2 tmp =
  admit ();
  Fmul_stdcalls.fmul tmp f1 out f2

[@ CInline]
let fmul2 out f1 f2 tmp =
  admit ();
  Fmul_stdcalls.fmul2 tmp f1 out f2

[@ CInline]
let fmul1 out f1 f2 =
  admit ();
  Fmul_stdcalls.fmul1 out f1 f2

[@ CInline]
let fsqr out f1 tmp =
  admit ();
  Fsqr_stdcalls.fsqr tmp f1 out

[@ CInline]
let fsqr2 out f tmp =
  admit ();
  Fsqr_stdcalls.fsqr2 tmp f out

[@ CInline]
let cswap2 bit p1 p2 =
  admit ();
  Fswap_stdcalls.cswap2 p1 p2 bit
