module Hacl.Impl.Load51

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Buffer
open FStar.Old.Endianness

open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Endianness
open Hacl.UInt64


#reset-options "--max_fuel 0 --z3rlimit 100"

let load_51 output input =
  Hacl.EC.Format.fexpand output input;
  let h = ST.get() in
  Hacl.Bignum25519.lemma_reveal_seval (as_seq h output);
  Hacl.Bignum25519.lemma_intro_red_51 (as_seq h output);
  Hacl.Spec.Bignum.Modulo.lemma_seval_5 (as_seq h output)
