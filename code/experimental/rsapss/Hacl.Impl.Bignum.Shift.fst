module Hacl.Impl.Bignum.Shift

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.Loops

open Hacl.Impl.Bignum.Core
open Hacl.Impl.Bignum.Comparison
open Hacl.Impl.Bignum.Addition



inline_for_extraction
let bn_tbit = u64 0x8000000000000000

inline_for_extraction
val bn_lshift1_:
     #aLen:bn_len
  -> a:lbignum aLen
  -> carry:lbignum 1ul
  -> res:lbignum aLen
  -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ live h carry))
    (ensures (fun h0 _ h1 -> modifies2 carry res h0 h1 /\
                             live h1 a /\ live h1 res /\ live h1 carry))
let bn_lshift1_ #aLen a carry res =
  let h0 = FStar.HyperStack.ST.get() in
  let inv h _ = live h a /\ live h carry /\ live h res /\ modifies2 carry res h0 h in
  for 0ul aLen inv
  (fun i ->
    let tmp = a.(i) in
    res.(i) <- (shift_left tmp 1ul) |. carry.(0ul);
    carry.(size 0) <- if (eq_u64 (logand #U64 tmp bn_tbit) bn_tbit) then u64 1 else u64 0)

// res = a << 1
val bn_lshift1:
     #aLen:bn_len
  -> a:lbignum aLen
  -> res:lbignum aLen
  -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> modifies1 res h0 h1 /\ live h1 a /\ live h1 res))
[@ "c_inline"]
let bn_lshift1 #aLen a res =
  push_frame();
  let h0 = FStar.HyperStack.ST.get () in
  let carry = create 1ul (uint 0) in
  bn_lshift1_ a carry res;
  pop_frame()

inline_for_extraction
val bn_pow2_mod_n_:
     #aLen:bn_len
  -> #rLen:bn_len{v aLen < v rLen}
  -> a:lbignum aLen
  -> p:size_t
  -> res:lbignum rLen
  -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> modifies1 res h0 h1))
let bn_pow2_mod_n_ #aLen #rLen a p res =
  push_frame ();
  let carry = create 1ul (uint 0) in
  let h0 = FStar.HyperStack.ST.get() in
  let inv h _ = live h carry /\ live h a /\ live h res /\ modifies2 res carry h0 h in
  for 0ul p inv
  (fun i ->
    carry.(size 0) <- uint 0;
    bn_lshift1_ res carry res;
    (if not (bn_is_less res a) then
      let _ = bn_sub res a res in ()));
  pop_frame ()

// res = (2 ^ p) % a
val bn_pow2_mod_n:
     #aLen:bn_len{v aLen + 1 < max_size_t}
  -> aBits:size_t{v aBits / 64 <= v aLen}
  -> a:lbignum aLen
  -> p:size_t
  -> res:lbignum aLen
  -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint res a))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 res /\ modifies1 res h0 h1))
[@ "c_inline"]
let bn_pow2_mod_n #aLen aBits a p res =
  push_frame();

  let rLen = aLen +. 1ul in
  let tmp = create rLen (u64 0) in

  // Simple version. It is all very ineffective anyway, so I'll leave
  // optimisations for later.
  bn_set_bit tmp 0ul;
  bn_pow2_mod_n_ a p tmp;

  // Faster version
  //if aBits >. 64ul && aBits <. p
  //then begin
  //  bn_set_bit tmp aBits;
  //  //let _ = bn_sub tmp a tmp in
  //  bn_pow2_mod_n_ a (p -. aBits) tmp
  //end else begin
  // // unoptimised version here
  //end;

  let tmp' = sub tmp 0ul aLen in
  copy res tmp';

  pop_frame()
