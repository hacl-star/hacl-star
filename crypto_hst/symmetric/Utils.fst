module Utils

open FStar.Mul
open FStar.HyperStack
open FStar.HST
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

let u8s = B.buffer H8.t

#reset-options "--initial_fuel 0 --max_fuel 0"

(* This HAS to go in some more appropriate place *)
assume MaxUInt8 : pow2 8 = 256
assume MaxUInt32: pow2 32 = 4294967296
assume MaxUInt64: pow2 64 > pow2 32

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
