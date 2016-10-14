module Utils

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib
open FStar.Math.Lemmas
open Hacl.UInt32
open Hacl.Cast
(* open Hacl.SBuffer *)
open FStar.Buffer

(* Module abbreviations *)
(* module B  = Hacl.SBuffer *)
module B = FStar.Buffer
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module H8   = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64

let u8  = U8.t
let u32 = U32.t
let u64 = U64.t
let s8  = H8.t
let s32 = H32.t
let s64 = H64.t
let h8  = H8.t
let h32 = H32.t
let h64 = H64.t

let u8s = B.buffer H8.t
let uint32_p = B.buffer H32.t

#reset-options "--initial_fuel 0 --max_fuel 0"

(* This HAS to go in some more appropriate place *)
assume MaxUInt8 : pow2 8 = 256
assume MaxUInt32: pow2 32 = 4294967296
assume MaxUInt64: pow2 64 > pow2 32

(* 'Rotate' operators, to inline *)
let op_Greater_Greater_Greater (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in
  (a >>^ s) |^ (a <<^ (U32 (m -^ s)))
let op_Less_Less_Less (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  let (m:u32{FStar.UInt32.v m = 32}) = 32ul in
  (a <<^ s) |^ (a >>^ (U32 (m -^ s)))

val lemma_euclidian_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidian_division r b q = ()

let lemma_uint32_of_bytes (a:t) (b:t) (c:t) (d:t) : Lemma
  (requires (v a < pow2 8 /\ v b < pow2 8 /\ v c < pow2 8 /\ v d < pow2 8))
  (ensures  (v a + pow2 8 * v b < pow2 16
    /\ v a + pow2 8 * v b + pow2 16 * v c < pow2 24
    /\ v a + pow2 8 * v b + pow2 16 * v c + pow2 24 * v d < pow2 32))
  = Math.Lemmas.pow2_plus 8 8;
    lemma_euclidian_division (v a) (v b) (pow2 8);
    Math.Lemmas.pow2_plus 8 16;
    lemma_euclidian_division (v a + pow2 8 * v b) (v c) (pow2 16);
    Math.Lemmas.pow2_plus 8 24;
    lemma_euclidian_division (v a + pow2 8 * v b + pow2 16 * v c) (v d) (pow2 24)

(** Reads an unsigned int32 out of 4 bytes *)
val uint32_of_bytes: b:u8s{length b >= 4} -> Stack H32.t
  (requires (fun h -> B.live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ B.live h0 b
    /\ v r = H8 (v (get h0 b 0)
		 + pow2 8 * v (get h0 b 1)
		 + pow2 16 * v (get h0 b 2)
		 + pow2 24 * v (get h0 b 3)) ))
let uint32_of_bytes b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b0' = sint8_to_sint32 b0 in
  let b1' = sint8_to_sint32 b1 in
  let b2' = sint8_to_sint32 b2 in
  let b3' = sint8_to_sint32 b3 in
  Math.Lemmas.pow2_lt_compat 32 8;
  cut (v b0' = H8.v b0 /\ v b1' = H8.v b1 /\ v b2' = H8.v b2 /\ v b3' = H8.v b3);
  Math.Lemmas.pow2_lt_compat 16 8;
  Math.Lemmas.pow2_lt_compat 24 16;
  Math.Lemmas.pow2_lt_compat 32 24;
  Math.Lemmas.pow2_plus 8 8;
  Math.Lemmas.pow2_plus 8 16;
  Math.Lemmas.pow2_plus 8 24;
  let b1'' = b1' <<^ 8ul in
  let b2'' = b2' <<^ 16ul in
  let b3'' = b3' <<^ 24ul in
  cut (v b1'' = pow2 8 * H8.v b1 /\ v b2'' = pow2 16 * H8.v b2 /\ v b3'' = pow2 24 * H8.v b3);
  lemma_uint32_of_bytes b0' b1' b2' b3';
  b0' +^ b1'' +^ b2'' +^ b3''

#reset-options "--initial_fuel 0 -max_fuel 0 --z3timeout 20"

val bytes_of_uint32s: output:u8s -> m:B.buffer H32.t{disjoint output m} -> len:u32{U32.v len <=length output /\ U32.v len<=op_Multiply 4 (length m)} -> STL unit
  (requires (fun h -> B.live h output /\ B.live h m))
  (ensures (fun h0 _ h1 -> B.live h1 output /\ B.live h1 m /\ modifies_1 output h0 h1 ))
let rec bytes_of_uint32s output m l =
  if U32 (l >^ 0ul) then
    begin
    let rem = U32 (l %^ 4ul) in
    if U32 (rem >^ 0ul) then
      begin
      let l = U32 (l -^ rem) in
      let x = index m (U32 (l /^ 4ul)) in
      let b0 = sint32_to_sint8 (x &^ uint32_to_sint32 255ul) in
      upd output l b0;
      if UInt32.gt rem 1ul then
        begin
        let b1 = sint32_to_sint8 ((x >>^ 8ul) &^ uint32_to_sint32 255ul) in
        upd output (U32 (l +^ 1ul)) b1;
	if UInt32.gt rem 2ul then
	  begin
	  let b2 = sint32_to_sint8 ((x >>^ 16ul) &^ uint32_to_sint32 255ul) in
	  upd output (U32 (l +^ 2ul)) b2
          end
	else ()
	end
      else ();
      bytes_of_uint32s output m l
      end
    else
      begin
      let l = U32 (l -^ 4ul) in
      let x = index m (U32 (l /^ 4ul)) in
      let b0 = sint32_to_sint8 (x &^ uint32_to_sint32 255ul) in
      let b1 = sint32_to_sint8 ((x >>^ 8ul) &^ uint32_to_sint32 255ul) in
      let b2 = sint32_to_sint8 ((x >>^ 16ul) &^ uint32_to_sint32 255ul) in
      let b3 = sint32_to_sint8 ((x >>^ 24ul) &^ uint32_to_sint32 255ul) in
      upd output l b0;
      upd output (U32 (l +^ 1ul)) b1;
      upd output (U32 (l +^ 2ul)) b2;
      upd output (U32 (l +^ 3ul)) b3;
      bytes_of_uint32s output m l
      end
    end

val bytes_of_uint32: output:u8s{length output >= 4} -> m:s32 -> Stack unit
  (requires (fun h -> B.live h output))
  (ensures (fun h0 _ h1 -> B.live h1 output /\ modifies_1 output h0 h1 ))
let rec bytes_of_uint32 output x =
  let open Hacl.UInt32 in
  let mask = uint32_to_sint32 255ul in
  let b0 = sint32_to_sint8 (x &^ mask) in
  let b1 = sint32_to_sint8 ((x >>^ 8ul) &^ mask) in
  let b2 = sint32_to_sint8 ((x >>^ 16ul) &^ mask) in
  let b3 = sint32_to_sint8 ((x >>^ 24ul) &^ mask) in
  upd output 0ul b0;
  upd output 1ul b1;
  upd output 2ul b2;
  upd output 3ul b3

val xor_uint8_p_2: output:u8s -> in1:u8s{disjoint in1 output} ->
  len:u32{FStar.UInt32.v len <= length output /\ FStar.UInt32.v len <= length in1} -> STL unit
  (requires (fun h -> live h output /\ live h in1))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h1 output /\ live h1 in1
    /\ modifies_1 output h0 h1 ))
let rec xor_uint8_p_2 output in1 len =
  if U32 (len =^ 0ul) then ()
  else
    begin
      let i    = U32 (len -^ 1ul) in
      let in1i = in1.(i) in
      let oi   = output.(i) in
      let oi   = H8 (in1i ^^ oi) in
      output.(i) <- oi;
      xor_uint8_p_2 output in1 i
    end


val sum_matrixes:
  new_state:uint32_p{length new_state >= 16} ->
  old_state:uint32_p{length old_state >= 16 /\ disjoint new_state old_state} ->
  Stack unit
    (requires (fun h -> live h new_state /\ live h old_state))
    (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  let m_0 = m.(0ul) in let m0_0 = m0.(0ul) in m.(0ul) <- (m_0 +%^ m0_0);
  let m_1 = m.(1ul) in let m0_1 = m0.(1ul) in m.(1ul) <- (m_1 +%^ m0_1);
  let m_2 = m.(2ul) in let m0_2 = m0.(2ul) in m.(2ul) <- (m_2 +%^ m0_2);
  let m_3 = m.(3ul) in let m0_3 = m0.(3ul) in m.(3ul) <- (m_3 +%^ m0_3);
  let m_4 = m.(4ul) in let m0_4 = m0.(4ul) in m.(4ul) <- (m_4 +%^ m0_4);
  let m_5 = m.(5ul) in let m0_5 = m0.(5ul) in m.(5ul) <- (m_5 +%^ m0_5);
  let m_6 = m.(6ul) in let m0_6 = m0.(6ul) in m.(6ul) <- (m_6 +%^ m0_6);
  let m_7 = m.(7ul) in let m0_7 = m0.(7ul) in m.(7ul) <- (m_7 +%^ m0_7);
  let m_8 = m.(8ul) in let m0_8 = m0.(8ul) in m.(8ul) <- (m_8 +%^ m0_8);
  let m_9 = m.(9ul) in let m0_9 = m0.(9ul) in m.(9ul) <- (m_9 +%^ m0_9);
  let m_10 = m.(10ul) in let m0_10 = m0.(10ul) in m.(10ul) <- (m_10 +%^ m0_10);
  let m_11 = m.(11ul) in let m0_11 = m0.(11ul) in m.(11ul) <- (m_11 +%^ m0_11);
  let m_12 = m.(12ul) in let m0_12 = m0.(12ul) in m.(12ul) <- (m_12 +%^ m0_12);
  let m_13 = m.(13ul) in let m0_13 = m0.(13ul) in m.(13ul) <- (m_13 +%^ m0_13);
  let m_14 = m.(14ul) in let m0_14 = m0.(14ul) in m.(14ul) <- (m_14 +%^ m0_14);
  let m_15 = m.(15ul) in let m0_15 = m0.(15ul) in m.(15ul) <- (m_15 +%^ m0_15)
