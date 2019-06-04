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
open Hacl.Spec.Bignum



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
  let carry = create 1ul (uint 0) in
  bn_lshift1_ a carry res;
  pop_frame()


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0"

val bn_lshift_:
     #aLen:bn_len
  -> #n:size_t { v aLen + (v n / 64) + 1 < max_size_t }
  -> a:lbignum aLen
  -> nw:size_t { v nw = v n / 64}
  -> lb:size_t{ v lb = v n % 64 /\ v lb > 0 /\ v lb < 64}
  -> res:lbignum (aLen +. (n /. 64ul) +. 1ul)
  -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint a res))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 res /\ modifies1 res h0 h1))
let bn_lshift_ #aLen #n a nw lb res =
  let h0 = FStar.HyperStack.ST.get () in
  let inv h _ = live h a /\ live h res /\ modifies1 res h0 h in
  for 0ul aLen inv (fun i ->
    let count = aLen -! i in
    let ind = nw +! count in
    let tmp = res.(ind) in
    let t1 = a.(count -. 1ul) in
    let rb = 64ul -. lb in
    res.(ind) <- tmp |. (t1 >>. rb);
    res.(ind -. 1ul) <- t1 <<. lb)

(* res = a << n *)
val bn_lshift:
     #aLen:bn_len
  -> a:lbignum aLen
  -> n:size_t { v aLen + (v n / 64) + 1 < max_size_t }
  -> res:lbignum (aLen +. (n /. 64ul) +. 1ul)
  -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ disjoint a res))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 res /\ modifies1 res h0 h1))
let bn_lshift #aLen a n res =
    let nw = n /. 64ul in
    let resLen = aLen +. nw +. 1ul in
    let lb = n %. 64ul in
    if lb =. 0ul
    then begin
      // Set the result
      copy (sub res nw aLen) a;
      // Clear all the other res' bits
      memset (sub res 0ul nw) (uint 0) nw;
      res.(resLen -. 1ul) <- uint 0
    end else bn_lshift_ a nw lb res


val bn_rshift1_:
     #aLen:bn_len
  -> a:lbignum aLen
  -> carry:lbignum 1ul
  -> res:lbignum aLen
  -> Stack unit
    (requires (fun h -> live h a /\ live h res /\ live h carry))
    (ensures (fun h0 _ h1 ->
     modifies2 carry res h0 h1 /\
     live h1 a /\ live h1 res /\ live h1 carry))
let bn_rshift1_ #aLen a carry res =
  let h0 = FStar.HyperStack.ST.get () in
  let inv h _ = live h a /\ live h res /\ modifies2 carry res h0 h in
  for 0ul aLen inv (fun i ->
    let ind = aLen -! i -! 1ul in
    let tmp:uint64 = a.(ind) in
    res.(ind) <- (tmp >>. 1ul) |. carry.(0ul);
    carry.(0ul) <- if eq_u64 (tmp &. uint 1) (uint 1) then bn_tbit else uint 0)

(* res = a >> 1 *)
val bn_rshift1:
     #aLen:bn_len
  -> a:lbignum aLen
  -> res:lbignum aLen
  -> Stack unit
    (requires (fun h -> live h a /\ live h res))
    (ensures (fun h0 _ h1 -> modifies1 res h0 h1 /\ live h1 a /\ live h1 res))
let bn_rshift1 #aLen a res =
  push_frame();
  let carry = create 1ul (uint 0) in
  bn_rshift1_ a carry res;
  pop_frame()


#reset-options

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
