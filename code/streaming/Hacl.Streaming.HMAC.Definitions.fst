module Hacl.Streaming.HMAC.Definitions

/// Helper definitions with an interface so as to friend Spec.Agile.HMAC

open FStar.HyperStack.ST
open LowStar.BufferOps

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost
module S = FStar.Seq
module D = Hacl.Hash.Definitions

open Hacl.Agile.Hash
open Hacl.Streaming.Interface

let _sync_decl = ()

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

friend Spec.Agile.HMAC
friend Spec.HMAC.Incremental
friend Hacl.HMAC

noextract inline_for_extraction
val alloca_block: (i: G.erased impl) ->
  ST.StackInline (b:B.buffer uint8)
    (requires (fun h ->
      HS.is_stack_region (HS.get_tip h)))
    (ensures (fun h0 s h1 ->
      M.(modifies M.loc_none h0 h1) /\
      B.frameOf s == HS.get_tip h0 /\
      B.length s == Spec.Agile.Hash.block_length (alg_of_impl i) /\
      B.as_seq h1 s == Seq.create (Spec.Agile.Hash.block_length (alg_of_impl i)) (Lib.IntTypes.u8 0) /\
      B.live h1 s /\
      B.fresh_loc (M.loc_buffer s) h0 h1))

// This extracts in C without a VLA.
let alloca_block i =
  let b = B.alloca (Lib.IntTypes.u8 0) 168ul in
  assert (D.block_len (alg_of_impl i) `FStar.UInt32.lte` 168ul);
  let r = B.sub b 0ul (D.block_len (alg_of_impl i)) in
  let h = ST.get () in
  assert (B.as_seq h r `S.equal` S.create (Spec.Agile.Hash.block_length (alg_of_impl i)) (Lib.IntTypes.u8 0));
  r

// TODO: copy-paste from Hacl.HMAC
inline_for_extraction noextract
let wrap_key (impl: impl): Hacl.HMAC.wrap_key_st (alg_of_impl impl) =
fun output key len ->
  [@inline_let]
  let a = alg_of_impl impl in
  [@inline_let] //18-08-02 does *not* prevents unused-but-set-variable warning in C
  let i = Hacl.HMAC.helper_smtpat a len in
  let nkey = B.sub output 0ul i in
  let zeroes = B.sub output i (D.block_len a `FStar.UInt32.sub` i) in
  (**) assert B.(loc_disjoint (loc_buffer nkey) (loc_buffer zeroes));
  (**) let h0 = ST.get () in
  (**) assert (Seq.equal (B.as_seq h0 zeroes) (Seq.create (UInt32.v (D.block_len a `FStar.UInt32.sub` i)) (Lib.IntTypes.u8 0)));
  if len `FStar.UInt32.lte` D.block_len a then begin
    B.blit key 0ul nkey 0ul len;
    let h1 = ST.get () in
    (**) assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    (**) assert (Seq.equal (B.as_seq h1 nkey) (B.as_seq h0 key));
    (**) assert (Seq.equal (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    (**) Seq.lemma_eq_elim (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    (**) assert (B.as_seq h1 output == Spec.Agile.HMAC.wrap a (B.as_seq h0 key))
  end else begin
    Hacl.Agile.Hash.hash impl nkey key len;
    (**) let h1 = ST.get () in
    (**) assert (Seq.equal (B.as_seq h1 zeroes) (B.as_seq h0 zeroes));
    (**) assert (Seq.equal (B.as_seq h1 nkey) (Spec.Agile.Hash.hash a (B.as_seq h0 key)));
    (**) assert (Seq.equal (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes)));
    (**) Seq.lemma_eq_elim (B.as_seq h1 output) (S.append (B.as_seq h1 nkey) (B.as_seq h1 zeroes));
    (**) assert (B.as_seq h1 output == Spec.Agile.HMAC.wrap a (B.as_seq h0 key))
  end

let init (i: G.erased index) k buf s =
  push_frame ();
  admit ();
  let i = Hacl.Agile.Hash.impl_of_state (dfst i) s in
  let block = alloca_block i in
  let k, k_len = k in
  wrap_key i block k !*k_len;
  pop_frame ()
