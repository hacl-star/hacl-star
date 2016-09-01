module Hacl.EC.Curve25519.Bignum

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open Hacl.UInt64
open Hacl.SBuffer
open Math.Lib
open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint


#reset-options "--initial_fuel 0 --max_fuel 0"

(* Module abbreviations *)
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

val copy_to_bigint': output:bigint -> input:bigint_wide{disjoint input output} -> idx:u32 -> len:u32 ->
  ctr:u32{U32.v ctr <= U32.v len} -> STL unit
    (requires (fun h -> live h output /\ live h input /\ U32.v idx+U32.v len <= length output /\ U32.v idx+U32.v len<=length input))
      (* /\ (forall (i:nat). {:pattern (vv (get h input i))} (i >= w idx /\ i < w idx+w len) ==> vv (get h input i) < pow2 platform_size) *)
      (* /\ (forall (i:nat). i < w ctr ==> v (get h output (w idx+i)) = vv (get h input (w idx+i))) )) *)
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
    (* live h0 output /\ live h1 output *)
    (*   /\ (forall (i:nat). i < w len ==> v (get h1 output (w idx+i)) = vv (get h0 input (w idx+i))) *)
    (*   /\ modifies_1 output h0 h1 )) *)
let rec copy_to_bigint' output b idx len ctr =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  if U32 (len =^ ctr) then ()
  else begin
    let bi = b.(U32 (idx +^ ctr)) in
    let cast = Hacl.Cast.sint128_to_sint64 bi in
    (* cast_lemma_1 bi; *)
    (* cut (v cast = vv bi /\ True);  *)
    output.(U32 (idx +^ ctr)) <- cast;
    (* let h1 = HST.get() in *)
    (* no_upd_lemma h0 h1 b (only output);  *)
    (* upd_lemma h0 h1 output (idx+|ctr) cast;  *)
    copy_to_bigint' output b idx len (U32 (ctr +^ 1ul))
  end

val copy_to_bigint:
  output:bigint ->
  input:bigint_wide{disjoint input output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input
      (* /\ norm_wide h input *)
    ))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1
      (* norm h1 output /\ norm_wide h0 input  *)
      (* /\ modifies_1 output h0 h1 *)
      (* /\ eval_wide h0 input norm_length % reveal prime = eval h1 output norm_length % reveal prime *)
      (* /\ valueOf h1 output = valueOf_wide h0 input *)
    ))
let copy_to_bigint output b =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  (* norm_bigint_lemma_1 h0 b; *)
  copy_to_bigint' output b 0ul nlength 0ul(* ;  *)
  (* let h1 = HST.get() in *)
  (* cut (forall (i:nat). i < norm_length ==> v (get h1 output (0+i)) = vv (get h0 b (0+i)));  *)
  (* cut (forall (i:nat). i < norm_length ==> v (get h1 output i) = vv (get h0 b i)); *)
  (* (\* eval_eq_lemma h0 h1 b output norm_length; *\) *)
  (* cut (eval_wide h0 b norm_length % reveal prime = eval h1 output norm_length % reveal prime /\ True);  *)
  (* cut (norm h1 output); cut(norm_wide h0 b); *)
  (* cut (valueOf_wide h0 b = valueOf h1 output /\ True);  *)
  (* cut (modifies_1 output h0 h1) *)

val copy_to_bigint_wide': output:bigint_wide -> input:bigint{disjoint input output} -> idx:u32 ->
  len:u32 -> ctr:u32{U32.v ctr <= U32.v len} -> Stack unit
    (requires (fun h -> live h output /\ live h input /\ U32.v idx+U32.v len <= length output /\ U32.v idx+U32.v len<=length input
      (* /\ (forall (i:nat). i < w ctr ==> vv (get h output (w idx+i)) = v (get h input (w idx+i))) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1
      (* /\ live h0 output /\ live h1 output *)
      (* /\ (forall (i:nat). i < w len ==> vv (get h1 output (w idx+i)) = v (get h0 input (w idx+i))) *)
      (* /\ modifies_1 output h0 h1 *)
    ))
let rec copy_to_bigint_wide' output b idx len ctr =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  if U32 (len =^ ctr) then ()
  else begin
    let bi = b.(U32 (idx +^ ctr)) in
    let cast = Hacl.Cast.sint64_to_sint128 bi in
    (* cut (vv cast = v bi /\ True); *)
    output.(U32 (idx +^ ctr)) <- cast;
    (* let h1 = HST.get() in *)
    (* no_upd_lemma h0 h1 b (only output); *)
    (* upd_lemma h0 h1 output (idx+|ctr) cast; *)
    copy_to_bigint_wide' output b idx len (U32 (ctr +^ 1ul))
  end

val copy_to_bigint_wide: output:bigint_wide -> input:bigint{disjoint input output} -> Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1
      (* live h0 output /\ live h1 output *)
      (* /\ (forall (i:nat). i < norm_length ==> vv (get h1 output (i)) = v (get h0 input (i))) *)
      (* /\ (eq_wide_l h1 output h0 input) *)
      (* /\ (modifies_1 output h0 h1) *)
      (* /\ (length output = length output)  *)
    ))
let copy_to_bigint_wide output b =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  copy_to_bigint_wide' output b 0ul nlength 0ul(* ;  *)
  (* let h1 = HST.get() in *)
  (* cut (forall (i:nat). i < norm_length ==> vv (get h1 output (0+i)) = v (get h0 b (0+i)));  *)
  (* cut (forall (i:nat). i < norm_length ==> vv (get h1 output i) = v (get h0 b i)); *)
  (* (\* eval_eq_lemma h0 h1 b output norm_length; *\) *)
  (* cut (eval h0 b norm_length % reveal prime = eval_wide h1 output norm_length % reveal prime /\ True);  *)
  (* cut (live h1 output); cut(live h0 b) *)

val erase: b:bigint -> idx:u32 -> len:u32 -> ctr:u32{U32.v ctr <= U32.v len} -> Stack unit
    (requires (fun h -> live h b /\ length b >= U32.v idx+U32.v len
      (* /\ (forall (i:nat). {:pattern (v (get h b i))} (i>= w idx /\ i < w idx+w ctr) ==> v (get h b i) = 0) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* live h0 b /\ live h1 b /\ length b >= w idx+w len *)
      (* /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= w idx /\ i < w idx+w len) ==> v (get h1 b i) = 0) *)
      (* (\* /\ (EqSub h1 b 0 h0 b 0 idx)  *\) *)
      (* (\* /\ (EqSub h1 b (idx+len) h0 b (idx+len) (length b-(idx+len))) *\) *)
      (* /\ modifies_1 b h0 h1  *)
    ))
let rec erase b idx len ctr =
  (* let h0 = HST.get() in *)
  if U32 (len =^ ctr) then ()
  else begin
    b.(U32 (idx +^ ctr)) <- (Hacl.Cast.uint64_to_sint64 0uL);
    (* let h1 = HST.get() in *)
    (* upd_lemma h0 h1 b (idx+|ctr) 0uL; *)
    erase b idx len (U32 (ctr +^ 1ul))
  end

val erase_wide: b:bigint_wide -> idx:u32 -> len:u32 -> ctr:u32{U32.v ctr <= U32.v len} -> Stack unit
    (requires (fun h -> live h b /\ length b >= U32.v idx+U32.v len
      (* /\ (forall (i:nat). {:pattern (vv (get h b i))} (i>= w idx /\ i < w idx+w ctr) ==> vv (get h b i) = 0) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1
      (* (live h0 b) /\ (live h1 b) *)
      (* /\ (length b = length b) /\ (length b >= w idx+w len) *)
      (* /\ (forall (i:nat). {:pattern (vv (get h1 b i))} (i >= w idx /\ i < w idx+w len) ==> vv (get h1 b i) = 0) *)
      (* (\* /\ (EqSub h1 b 0 h0 b 0 idx) /\ (EqSub h1 b (idx+len) h0 b (idx+len) (length b-(idx+len))) *\) *)
      (* /\ (modifies_1 b h0 h1) *)
    ))
let rec erase_wide b idx len ctr =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  if U32 (len =^ ctr) then ()
  else begin
    b.(U32 (idx +^ ctr)) <- (Hacl.UInt128.of_string "0");
    (* let h1 = HST.get() in *)
    (* upd_lemma h0 h1 b (idx+|ctr) (Hacl.UInt128.of_string "0"); *)
    erase_wide b idx len (U32 (ctr +^ 1ul))
  end

val modulo: output:bigint -> input:bigint_wide{disjoint input output} -> Stack unit
    (requires (fun h -> live h input /\ live h output (* /\ satisfies_modulo_constraints h input *)
      /\ length input >= 2*norm_length - 1 ))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 input /\ modifies_2 output input h0 h1
    (* live h0 input /\ length input >= 2*norm_length-1 *)
    (*   /\ norm h1 output /\ live h0 input *)
    (*   /\ eval h1 output norm_length % reveal prime = eval_wide h0 input (2*norm_length-1) % reveal prime *)
      (* /\ modifies_2 output input h0 h1  *)
    ))
let modulo output b =
  (* admit(); // OK *)
  (* let h0 = HST.get() in *)
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_degree b;
  Hacl.EC.Curve25519.Bignum.Modulo.freduce_coefficients b;
  (* let h = HST.get() in *)
  (* standardized_eq_norm h b; *)
  copy_to_bigint output b

val fsum: a:bigint -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b
      (* /\(norm h a) /\ (norm h b)  *)
    ))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      (* (norm h0 a) /\ (norm h1 a) /\ (norm h0 b) *)
      (* /\ (valueOf h1 a = (valueOf h0 a ^+ valueOf h0 b)) *)
      (* /\ (modifies_1 a h0 h1) *)
    ))
let fsum a b =
  push_frame ();
  (* let h0 = HST.get() in *)
  (* standardized_eq_norm h0 a; standardized_eq_norm h0 b;  *)
  let tmp = create (Hacl.UInt128.of_string "0") (UInt32.sub (UInt32.mul nlength 2ul) 1ul) in
  Hacl.EC.Curve25519.Bignum.Fsum.fsum' a b;
  (* let h1 = HST.get() in *)
  copy_to_bigint_wide tmp a;
  (* cut (forall (i:nat). {:pattern (v (get h1 a i))} i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i)); *)
  (* let h2 = HST.get() in  *)
  (* cut (forall (i:nat). {:pattern (vv (get h2 tmp i))} i < norm_length ==> vv (get h2 tmp (0+i)) =  *)
  (* 	 v (get h1 a (0+i)));  *)
  (* cut (forall (i:nat). {:pattern (vv (get h2 tmp i))} i < norm_length ==> vv (get h2 tmp i) =  *)
  (*     v (get h0 a i) + v (get h0 b i));  *)
  (* admitP (forall (i:nat). {:pattern (vv (get h2 tmp i))} (i >= norm_length /\ i < length tmp) ==> vv (get h2 tmp i) = 0); *)
  (* Curve.Modulo.sum_satisfies_constraints h0 h2 tmp a b;  *)
  modulo a tmp;
  (* let h1 = HST.get() in *)
  (* assert(valueOf h1 a = valueOf_wide h2 tmp);  *)
  (* cut (True /\ eval h1 a norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime);  *)
  (* fsum_lemma h0 h1 a a b; *)
  (* cut(modifies_1 a h0 h1); *)
  pop_frame()

val fdifference: a:bigint -> b:bigint{disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b
      (* (norm h a) /\ (norm h b) *)
    ))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      (* (norm h0 a) /\ (norm h0 b) /\ (norm h1 a) *)
      (* /\ (valueOf h1 a = (valueOf h0 b ^- valueOf h0 a)) *)
      (* /\ (modifies_1 a h0 h1) *)
    ))
let fdifference a b =
  push_frame ();
  (* let h0 = HST.get() in *)
  (* standardized_eq_norm h0 a; standardized_eq_norm h0 b; *)
  let b' = create (Hacl.Cast.uint64_to_sint64 0uL) nlength in
  let tmp = create (Hacl.UInt128.of_string "0") (U32 (2ul *^ nlength -^ 1ul)) in
  blit b 0ul b' 0ul nlength;
  (* let b' = Bigint.copy b in  *)
  (* let h1 = HST.get() in *)
  Hacl.EC.Curve25519.Bignum.Modulo.add_big_zero b';
  (* let h2 = HST.get() in *)
  (* cut (modifies_1 b' h0 h2);  *)
  (* no_upd_lemma h0 h2 a (only b');  *)
  (* cut (norm h2 a);  *)
  Hacl.EC.Curve25519.Bignum.Fdifference.fdifference' a b';
  (* let h3 = HST.get() in *)
  (* let h4 = HST.get() in *)
  copy_to_bigint_wide tmp a;
  (* let h5 = HST.get() in  *)
  (* cut(live h5 a /\ (forall (i:nat). (i>=norm_length /\ i < length tmp) ==> vv (get h5 tmp i) = 0)); *)
  (* Curve.Modulo.difference_satisfies_constraints h2 h5 tmp b' a; *)
  modulo a tmp;
  (* let h6 = HST.get() in *)
  (* cut (True /\ eval h6 a norm_length % reveal prime = (eval h0 b norm_length - eval h0 a norm_length) % reveal prime); *)
  (* fdifference_lemma h0 h6 a b a; *)
  (* cut (modifies_1 a h0 h6); *)
  pop_frame()

val fscalar:
    res:bigint -> b:bigint{disjoint res b} -> s:s64{v s < templ 0} -> ST unit
  (requires (fun h -> live h res /\ live h b))
  (* (live h res) /\ (norm h b))) *)
  (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1
    (* (norm h0 b) /\ (live h0 b) /\ (norm h1 res) *)
    (* /\ (valueOf h1 res = (v s +* valueOf h0 b)) *)
    (* /\ (modifies_1 res h0 h1) *)
  ))
let fscalar res b s =
  push_frame ();
  (* let h0 = HST.get() in *)
  (* standardized_eq_norm h0 b;  *)
  let tmp = create (Hacl.UInt128.of_string "0") (U32 (2ul *^ nlength -^ 1ul)) in
  Hacl.EC.Curve25519.Bignum.Fscalar.scalar' tmp b s;
  (* let h = HST.get() in *)
  (* admitP(b2t(satisfies_modulo_constraints h tmp));   *)
  modulo res tmp;
  (* let h1 = HST.get() in *)
  (* admitP(True /\ (valueOf h1 res = (v s +* valueOf h0 b))); *)
  pop_frame()

val fmul: res:bigint -> a:bigint{disjoint res a} -> b:bigint{disjoint res b} -> Stack unit
    (requires (fun h -> live h res /\ live h a /\ live h b
      (* live h res /\ norm h a /\ norm h b *)
    ))
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1
      (* /\ norm h0 a /\ norm h0 b /\ norm h1 res *)
      (* /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 b)) *)
      (* /\ (modifies_1 res h0 h1)  *)
    ))
let fmul res a b =
  push_frame ();
  (* let h0 = HST.get() in *)
  (* standardized_eq_norm h0 a; standardized_eq_norm h0 b;  *)
  let tmp = create (Hacl.UInt128.of_string "0") (U32 (2ul *^ nlength -^ 1ul)) in
  (* let h1 = HST.get() in *)
  (* no_upd_lemma h0 h1 a !{}; *)
  (* no_upd_lemma h0 h1 b !{}; *)
  (* norm_lemma_2 h1 a; norm_lemma_2 h1 b;  *)
  (* norm_lemma_3 h1 a; norm_lemma_3 h1 b; *)
  Hacl.EC.Curve25519.Bignum.Fproduct.multiplication tmp a b;
  (* let h2 = HST.get() in *)
  (* Hacl.EC.Curve25519.Bignum.Modulo.mul_satisfies_constraints h1 h2 tmp a b; *)
  modulo res tmp;
  (* let h3 = HST.get() in *)
  (* cut (True /\ eval h3 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime); *)
  (* fmul_lemma h0 h3 res a b; *)
  pop_frame()

val fsquare: res:bigint -> a:bigint{disjoint res a} -> Stack unit
    (requires (fun h -> live h res  /\ live h a))
      (* (live h res) /\ (norm h a))) *)
    (ensures (fun h0 _ h1 -> live h1 res /\ modifies_1 res h0 h1))
    (*   (norm h0 a) /\ (live h0 res) /\ (norm h1 res) *)
    (*   /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 a)) *)
    (*   /\ (modifies_1 res h0 h1) *)
    (* )) *)
let fsquare res a =
  fmul res a a
