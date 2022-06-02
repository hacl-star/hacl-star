module Hacl.Impl.EC.Masking

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.EC.Definition
open Lib.Loops

open Spec.ECC
open Spec.ECC.Curves
open Hacl.EC.Lemmas


#set-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction noextract
val copy_conditional_u64: x: uint64 -> out: lbuffer uint64 (size 1) 
  -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1}  -> 
  Stack unit 
  (requires fun h -> live h out)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    let out1 = Lib.Sequence.index (as_seq h1 out) 0 in 
    let out0 = Lib.Sequence.index (as_seq h0 out) 0 in 
    if v mask = 0 then v out0 == v out1 else v out1 == v x))

let copy_conditional_u64 x out mask = 
  let out_0 = index out (size 0) in 
  let r_0 = logxor out_0 (logand mask (logxor out_0 x)) in 
  lemma_xor_copy_cond out_0 x mask;
  upd out (size 0) r_0
  
(*
 #buf_type: buftype
  -> p: point c -> q: point c 
  -> tempBuffer: lbuffer uint64 (size 17 *! getCoordinateLenU64 c) 
  -> scalar: lbuffer_t buf_type uint8 (getScalarLenBytes c)
*)


inline_for_extraction noextract
val copy_conditional_: #c: curve -> #buf_type: buftype
  -> out: felem c
  -> x: lbuffer_t buf_type uint64 (getCoordinateLenU64 c)
  -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x /\ disjoint x out)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    if uint_v mask = 0 then as_nat c h1 out == lseq_as_nat (as_seq h0 out) else as_nat c h1 out == lseq_as_nat (as_seq h0 x))) 


let copy_conditional_ #c out x mask = 
  let h0 = ST.get() in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    live h x /\ live h out /\ modifies (loc out) h0 h /\ (
    forall (j: nat {j >= i && j < v (getCoordinateLenU64 c)}).
    let y_i = Lib.Sequence.index (as_seq h out) j in 
    let y_0 = Lib.Sequence.index (as_seq h0 out) j in 
    uint_v y_i == uint_v y_0) /\ (
    
    forall (j: nat {j < i}).
    let x_i = Lib.Sequence.index (as_seq h0 x) j in 
    let y_i = Lib.Sequence.index (as_seq h0 out) j in 
    let r_i = Lib.Sequence.index (as_seq h out) j in 
    if uint_v mask = 0 then 
      uint_v r_i == uint_v y_i
    else
      uint_v r_i == uint_v x_i) in   
  for 0ul len inv (fun i -> 
    let h_ = ST.get() in 
    let x_i = index x i in 
    let out_i = index out i in 
    let r_i = logxor out_i (logand mask (logxor out_i x_i)) in 
        lemma_xor_copy_cond out_i x_i mask; 
    upd out i r_i
  );
  let h1 = ST.get() in 
  
  if v mask = 0 then begin
    Lib.Sequence.eq_intro (as_seq h0 out) (as_seq h1 out);
    lemma_lseq_as_seq_as_forall_lr (as_seq h0 out) (as_seq h1 out) (v (getCoordinateLenU64 c)) end
  else begin
    Lib.Sequence.eq_intro (as_seq h0 x) (as_seq h1 out);
    lemma_lseq_as_seq_as_forall_lr (as_seq h0 x) (as_seq h1 out) (v (getCoordinateLenU64 c)) end


[@CInline]
let copy_conditional_p256_l = copy_conditional_ #P256 #MUT
[@CInline]
let copy_conditional_p384_l = copy_conditional_ #P384 #MUT
(*
[@CInline]
let copy_conditional_generic_l = copy_conditional_ #Default #MUT *)

[@CInline]
let copy_conditional_p256_i = copy_conditional_ #P256 #IMMUT
[@CInline]
let copy_conditional_p384_i = copy_conditional_ #P384 #IMMUT
(*
[@CInline]
let copy_conditional_generic_i = copy_conditional_ #Default #IMMUT
*)


[@CInline]
let copy_conditional_p256_c = copy_conditional_ #P256 #CONST
[@CInline]
let copy_conditional_p384_c = copy_conditional_ #P384 #CONST
(* 
[@CInline]
let copy_conditional_generic_c = copy_conditional_ #Default #CONST
*)

inline_for_extraction noextract
val copy_conditional: #c: curve -> #buf_type: buftype
  -> out: felem c
  -> x: lbuffer_t buf_type uint64 (getCoordinateLenU64 c)
  -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} -> Stack unit 
  (requires fun h -> live h out /\ live h x /\ disjoint x out)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ (
    if uint_v mask = 0 then as_nat c h1 out == lseq_as_nat (as_seq h0 out) else as_nat c h1 out == lseq_as_nat (as_seq h0 x))) 

let copy_conditional #c #b out x mask = 
  match c with 
    |P256 -> begin
      match b with 
	|MUT -> copy_conditional_p256_l out x mask
	|IMMUT -> copy_conditional_p256_i out x mask
	|CONST -> copy_conditional_p256_c out x mask end
    |P384 -> begin
      match b with 
	|MUT -> copy_conditional_p384_l out x mask
	|IMMUT -> copy_conditional_p384_i out x mask
	|CONST -> copy_conditional_p384_c out x mask end
    (*|Default -> begin
      match b with 
	|MUT -> copy_conditional_generic_l out x mask
	|IMMUT -> copy_conditional_generic_i out x mask
	|CONST -> copy_conditional_generic_c out x mask end *)


val copy_point_conditional: #c: curve -> out: point c -> x: point c 
  -> mask: uint64{uint_v mask = 0 \/ uint_v mask = pow2 64 - 1} 
  -> Stack unit 
  (requires fun h -> live h out /\ live h x /\ disjoint x out /\ point_eval c h out /\ point_eval c h x)
  (ensures fun h0 _ h1 -> modifies (loc out) h0 h1 /\ point_eval c h1 out /\ (
    let p = point_as_nat c h0 x in 
    let out_0 = point_as_nat c h0 out in 
    if uint_v mask = 0 then point_as_nat c h1 out == out_0 else point_as_nat c h1 out == p)) 

let copy_point_conditional #c out p mask = 
  [@inline_let]
  let len = getCoordinateLenU64 c in 
  
  let p_x = sub p (size 0) len in 
  let p_y = sub p len len in 
  let p_z = sub p (size 2 *! len) len in   

  let out_x = sub out (size 0) len in 
  let out_y = sub out len len in 
  let out_z = sub out (size 2 *! len) len in   

  copy_conditional #c out_x p_x mask;
  copy_conditional #c out_y p_y mask;
  copy_conditional #c out_z p_z mask



inline_for_extraction noextract
val cmovznz4_: #c: curve -> cin: uint64 -> x: felem c -> y: felem c -> result: felem c ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ (
    if uint_v cin = 0 then as_nat c h1 result == as_nat c h0 x 
    else as_nat c h1 result == as_nat c h0 y))

let cmovznz4_ #c cin x y r =
  let h0 = ST.get() in
  let mask = neq_mask cin (u64 0) in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v (getCoordinateLenU64 c)}) = 
    live h x /\ live h y /\ modifies (loc r) h0 h /\ (
    forall (j: nat {j >= i && j < v (getCoordinateLenU64 c)}).
    let y_i = Lib.Sequence.index (as_seq h y) j in 
    let y_0 = Lib.Sequence.index (as_seq h0 y) j in 
    uint_v y_i == uint_v y_0) /\ (
    
    forall (j: nat {j < i}).
    let x_i = Lib.Sequence.index (as_seq h0 x) j in 
    let y_i = Lib.Sequence.index (as_seq h0 y) j in 
    let r_i = Lib.Sequence.index (as_seq h r) j in 
    if uint_v cin = 0 then 
      uint_v r_i == uint_v x_i
    else
      uint_v r_i == uint_v y_i) in 
  for 0ul len inv (fun i -> 
    let h_ = ST.get() in 
    let x_i = index x i in 
    let y_i = index y i in 
    let r_i = logor (logand y_i mask) (logand x_i (lognot mask)) in 
    upd r i r_i;
    cmovznz4_lemma cin (Seq.index (as_seq h0 x) (v i)) (Seq.index (as_seq h0 y) (v i)));

  let h1 = ST.get() in 
  if v cin = 0 then begin
    Lib.Sequence.eq_intro (as_seq h0 x) (as_seq h1 r);
    lemma_lseq_as_seq_as_forall_lr (as_seq h0 x) (as_seq h1 r) (v (getCoordinateLenU64 c)) end
  else begin
    Lib.Sequence.eq_intro (as_seq h0 y) (as_seq h1 r);
    lemma_lseq_as_seq_as_forall_lr (as_seq h0 y) (as_seq h1 r) (v (getCoordinateLenU64 c)) end

[@CInline]
let cmovznz4_p256 = cmovznz4_ #P256
[@CInline]
let cmovznz4_p384 = cmovznz4_ #P384
(*
[@CInline]
let cmovznz4_generic = cmovznz4_ #Default

*)

inline_for_extraction noextract
val cmovznz4: #c: curve -> cin: uint64 -> x: felem c -> y: felem c -> result: felem c ->
  Stack unit
  (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ (
    if uint_v cin = 0 then as_nat c h1 result == as_nat c h0 x 
    else as_nat c h1 result == as_nat c h0 y))

let cmovznz4 #c cin x y result = 
  match c with 
  |P256 -> cmovznz4_p256 cin x y result
  |P384 -> cmovznz4_p384 cin x y result (*
  |Default -> cmovznz4_generic cin x y result *)


inline_for_extraction noextract
val eq_u64_CT: a: uint64 -> b: uint64 -> Tot (r: uint64 {if uint_v a = uint_v b then uint_v r == pow2 64 - 1 else uint_v r == 0})

let eq_u64_CT a b = 
  eq_mask_lemma a b;
  eq_mask a b


val eq0_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0})

val eq1_u64: a: uint64 -> Tot (r: uint64 {if uint_v a = 0 then uint_v r == 0 else uint_v r == pow2 64 - 1})

let eq0_u64 a =
  eq_mask_lemma a (u64 0);
  eq_mask a (u64 0)


let eq1_u64 a =
  neq_mask_lemma a (u64 0);
  neq_mask a (u64 0)


inline_for_extraction noextract
val isZero_uint64_CT: #c: curve -> #buf_type: buftype -> f: lbuffer_t buf_type uint64 (getCoordinateLenU64 c) -> Stack uint64
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if lseq_as_nat (as_seq h0 f) = 0 then uint_v r == pow2 64 - 1 else uint_v r == 0))
    

let isZero_uint64_CT #c f =
  push_frame();
  let h0 = ST.get() in 
  let tmp = create (size 1) (u64 18446744073709551615) in
  
  let len = getCoordinateLenU64 c in 
  let inv h (i: nat { i <= uint_v len}) = 
    live h f /\ live h tmp /\ modifies (loc tmp) h0 h /\ (
      let tmp = uint_v (Lib.Sequence.index (as_seq h tmp) 0) in (
      forall (j: nat {j < i}). v (Lib.Sequence.index (as_seq h0 f) j) == 0) <==>
      tmp == ones_v U64) /\ (
      let tmp = uint_v (Lib.Sequence.index (as_seq h tmp) 0) in 
      ~ (forall (j: nat {j < i}). v (Lib.Sequence.index (as_seq h0 f) j) == 0) <==>
      tmp == 0) in

  for 0ul len inv (fun i -> 
    let h0 = ST.get() in 
    assert(let tmp = uint_v (Lib.Sequence.index (as_seq h0 tmp) 0) in tmp == (ones_v U64) <==> 
      (forall (j: nat {j < (v i)}). v (Lib.Sequence.index (as_seq h0 f) j) == 0));

    let a_i = index f i in 
    let r_i = eq_mask a_i (u64 0) in 
    let tmp0 = index tmp (size 0) in 
    assert(if v a_i = 0 then v r_i == ones_v U64 else v r_i == 0);
    upd tmp (size 0) (logand r_i tmp0);
    logand_lemma r_i tmp0;

    let h1 = ST.get() in 
    let tmp1 = index tmp (size 0) in 
    assert(let tmp = uint_v (Lib.Sequence.index (as_seq h1 tmp) 0) in 
      tmp == (ones_v U64) <==> (forall (j: nat {j < (v i + 1)}). v (Lib.Sequence.index (as_seq h0 f) j) == 0)));

  let r = index tmp (size 0) in 
  let h1 = ST.get() in 
  lseq_as_nat_zero (as_seq h0 f);
  pop_frame();
  r

inline_for_extraction noextract
val isZero_uint64_nCT: #c: curve -> f: felem c -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ r = (as_nat c h0 f = 0))

let isZero_uint64_nCT f =
  let f = isZero_uint64_CT f in 
  Hacl.Impl.EC.LowLevel.RawCmp.eq_u64_nCT f (u64 0xffffffffffffffff)


inline_for_extraction noextract
val cmp_felem_felem_u64: #c: curve -> a: felem c -> b: felem c -> Stack uint64
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\
    (if as_nat c h0 a = as_nat c h0 b then uint_v r == pow2 64 - 1 else uint_v r = 0))

let cmp_felem_felem_u64 #c a b =
  push_frame();
  let h0 = ST.get() in 
  let tmp = create (size 1) (u64 0) in 
  upd tmp (size 0) (u64 18446744073709551615);
    
  let len = getCoordinateLenU64 c in 
  
  let inv h (i: nat { i <= uint_v len}) = live h a /\ live h b /\ live h tmp /\  modifies (loc tmp) h0 h /\ (
    let tmp = v (Lib.Sequence.index (as_seq h tmp) 0) in (
    forall (j: nat {j < i}). v (Lib.Sequence.index (as_seq h0 a) j) == 
      v (Lib.Sequence.index (as_seq h0 b) j)) <==> tmp == ones_v U64) /\ (
    let tmp = v (Lib.Sequence.index (as_seq h tmp) 0) in ( 
      ~ (forall (j: nat {j < i}).
	v (Lib.Sequence.index (as_seq h0 a) j) == v (Lib.Sequence.index (as_seq h0 b) j)) <==> tmp == 0)) in    
  for 0ul len inv (fun i -> 
    let h0 = ST.get() in 
    assert(let tmp = v (Lib.Sequence.index (as_seq h0 tmp) 0) in 
    tmp == ones_v U64 <==> (forall (j: nat {j < v i}). 
      v (Lib.Sequence.index (as_seq h0 a) j) == v (Lib.Sequence.index (as_seq h0 b) j)));
    
    let a_i = index a i in 
    let b_i = index b i in 
    let r_i = eq_mask a_i b_i in 
    let tmp0 = index tmp (size 0) in 

    logand_lemma r_i tmp0;
    upd tmp (size 0) (logand r_i tmp0);
    
    let h1 = ST.get() in 

    assert(let tmp = v (Lib.Sequence.index (as_seq h1 tmp) 0) in 
      tmp == ones_v U64 <==> (forall (j: nat {j < v i + 1}). 
	v (Lib.Sequence.index (as_seq h0 a) j) == v (Lib.Sequence.index (as_seq h0 b) j)))
    );

  let r = index tmp (size 0) in 

  lemma_lseq_as_seq_as_forall_lr (as_seq h0 a) (as_seq h0 b) (v (getCoordinateLenU64 c));
  assert(as_nat c h0 a == as_nat c h0 b <==> v r == ones_v U64);
  pop_frame(); 
  r


inline_for_extraction noextract
val cmp_felem_felem_bool_: #c: curve -> a: felem c -> b: felem c -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    if as_nat c h0 a = as_nat c h0 b then r == true else r == false))

let cmp_felem_felem_bool_ #c a b = 
  let r = lognot (cmp_felem_felem_u64 a b) in
    lognot_lemma (cmp_felem_felem_u64 a b);   
  Hacl.Impl.EC.LowLevel.RawCmp.unsafe_bool_of_u64 r

[@CInline]
let cmp_felem_felem_bool_p256 = cmp_felem_felem_bool_ #P256
[@CInline]
let cmp_felem_felem_bool_p384 = cmp_felem_felem_bool_ #P384

(*
[@CInline]
let cmp_felem_felem_bool_generic = cmp_felem_felem_bool_ #Default
*)


inline_for_extraction noextract
val cmp_felem_felem_bool: #c: curve -> a: felem c -> b: felem c -> Stack bool
  (requires fun h -> live h a /\ live h b)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (
    if as_nat c h0 a = as_nat c h0 b then r == true else r == false))

let cmp_felem_felem_bool #c a b = 
  match c with 
  |P256 -> cmp_felem_felem_bool_p256 a b 
  |P384 -> cmp_felem_felem_bool_p384 a b 
  (* |Default -> cmp_felem_felem_bool_generic a b *)


inline_for_extraction noextract
val cmovznz01: #t:inttype{unsigned t} -> #l:secrecy_level -> a: uint_t t l 
  -> b: uint_t t l -> mask: uint_t t l {uint_v mask = 0 \/ uint_v mask = 1} -> 
  Tot (r: uint_t t l {if uint_v mask = 0 then uint_v r = v a else uint_v r = v b} )

let cmovznz01 a b mask = 
  admit();
  let mask = (u64 0) -. mask in 
  admit();
  lemma_xor_copy_cond a b mask;
  logxor a (logand mask (logxor a b))
