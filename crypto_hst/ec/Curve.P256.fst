module Curve.P256

open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Curve.Parameters
open Curve.Bignum
open Curve.Crecip
open Curve.Ladder

let op_Hat_Greater_Greater : s64 -> UInt32.t -> Tot s64 = Hacl.UInt64.shift_right

val format_scalar: scalar:u8s{length scalar >= 32} -> STL unit
  (requires (fun h -> live h scalar))
  (ensures  (fun h0 _ h1 -> modifies_1 scalar h0 h1 /\ live h1 scalar))
let format_scalar scalar =
  upd scalar 0ul (uint8_to_sint8 0uy)

open Hacl.UInt64

val expand: output:Curve.Bigint.bigint -> input:u8s{length input >= 32} -> STL unit
  (requires (fun h -> live h input /\ live h output))
  (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let expand output input =
  let i0 = index input 0ul in
  let i1 = index input 1ul in
  let i2 = index input 2ul in
  let i3 = index input 3ul in
  let i4 = index input 4ul in
  let i5 = index input 5ul in
  let i6 = index input 6ul in
  let i7 = index input 7ul in
  let i8 = index input 8ul in
  let i9 = index input 9ul in
  let i10 = index input 10ul in
  let i11 = index input 11ul in
  let i12 = index input 12ul in
  let i13 = index input 13ul in
  let i14 = index input 14ul in
  let i15 = index input 15ul in
  let i16 = index input 16ul in
  let i17 = index input 17ul in
  let i18 = index input 18ul in
  let i19 = index input 19ul in
  let i20 = index input 20ul in
  let i21 = index input 21ul in
  let i22 = index input 22ul in
  let i23 = index input 23ul in
  let i24 = index input 24ul in
  let i25 = index input 25ul in
  let i26 = index input 26ul in
  let i27 = index input 27ul in
  let i28 = index input 28ul in
  let i29 = index input 29ul in
  let i30 = index input 30ul in
  let i31 = index input 31ul in
  let i0 = (sint8_to_sint64 i0) in
  let i1 = (sint8_to_sint64 (i1)) in
  let i2 = (sint8_to_sint64 (i2)) in
  let i3 = (sint8_to_sint64 (i3)) in
  let i4 = (sint8_to_sint64 (i4)) in
  let i5 = (sint8_to_sint64 (i5)) in
  let i6 = (sint8_to_sint64 (i6)) in
  let i7 = (sint8_to_sint64 (i7)) in
  let i8 = (sint8_to_sint64 (i8)) in
  let i9 = (sint8_to_sint64 (i9)) in
  let i10 = (sint8_to_sint64 (i10)) in
  let i11 = (sint8_to_sint64 (i11)) in
  let i12 = (sint8_to_sint64 (i12)) in
  let i13 = (sint8_to_sint64 (i13)) in
  let i14 = (sint8_to_sint64 (i14)) in
  let i15 = (sint8_to_sint64 (i15)) in
  let i16 = (sint8_to_sint64 (i16)) in
  let i17 = (sint8_to_sint64 (i17)) in
  let i18 = (sint8_to_sint64 (i18)) in
  let i19 = (sint8_to_sint64 (i19)) in
  let i20 = (sint8_to_sint64 (i20)) in
  let i21 = (sint8_to_sint64 (i21)) in
  let i22 = (sint8_to_sint64 (i22)) in
  let i23 = (sint8_to_sint64 (i23)) in
  let i24 = (sint8_to_sint64 (i24)) in
  let i25 = (sint8_to_sint64 (i25)) in
  let i26 = (sint8_to_sint64 (i26)) in
  let i27 = (sint8_to_sint64 (i27)) in
  let i28 = (sint8_to_sint64 (i28)) in
  let i29 = (sint8_to_sint64 (i29)) in
  let i30 = (sint8_to_sint64 (i30)) in
  let i31 = (sint8_to_sint64 (i31)) in
  let o0 = i0 +^ (i1 <<^ 8ul) +^ (i2 <<^ 16ul) +^ (i3 <<^ 24ul) in
  let o1 = i4 +^ (i5 <<^ 8ul) +^ (i6 <<^ 16ul) +^ (i7 <<^ 24ul) in
  let o2 = i8 +^ (i9 <<^ 8ul) +^ (i10 <<^ 16ul) +^ (i11 <<^ 24ul) in
  let o3 = i12 +^ (i13 <<^ 8ul) +^ (i14 <<^ 16ul) +^ (i15 <<^ 24ul) in
  let o4 = i16 +^ (i17 <<^ 8ul) +^ (i18 <<^ 16ul) +^ (i19 <<^ 24ul) in
  let o5 = i20 +^ (i21 <<^ 8ul) +^ (i22 <<^ 16ul) +^ (i23 <<^ 24ul) in
  let o6 = i24 +^ (i25 <<^ 8ul) +^ (i26 <<^ 16ul) +^ (i27 <<^ 24ul) in
  let o7 = i28 +^ (i29 <<^ 8ul) +^ (i30 <<^ 16ul) +^ (i31 <<^ 24ul) in
  upd output 0ul o0;
  upd output 1ul o1;
  upd output 2ul o2;
  upd output 3ul o3;
  upd output 4ul o4; 
  upd output 5ul o5;
  upd output 6ul o6;
  upd output 7ul o7;
  () // Without this unit the extraction to OCaml breaks

val contract: output:u8s{length output >= 32} -> input:Curve.Bigint.bigint{disjoint output input}  -> STL unit
  (requires (fun h -> live h input /\ live h output))
  (ensures  (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let contract output input =
  let i0 = index input 0ul in
  let i1 = index input 1ul in
  let i2 = index input 2ul in
  let i3 = index input 3ul in
  let i4 = index input 4ul in
  let i5 = index input 5ul in
  let i6 = index input 6ul in
  let i7 = index input 7ul in
  upd output 0ul (sint64_to_sint8 (i0 ^>> 0ul));
  upd output 1ul (sint64_to_sint8 (i0 ^>> 8ul));
  upd output 2ul (sint64_to_sint8 (i0 ^>> 16ul));
  upd output 3ul (sint64_to_sint8 (i0 ^>> 24ul));

  upd output 4ul (sint64_to_sint8 (i1 ^>> 0ul));
  upd output 5ul (sint64_to_sint8 (i1 ^>> 8ul));
  upd output 6ul (sint64_to_sint8 (i1 ^>> 16ul));
  upd output 7ul (sint64_to_sint8 (i1 ^>> 24ul));

  upd output 8ul (sint64_to_sint8 (i2 ^>> 0ul));
  upd output 9ul (sint64_to_sint8 (i2 ^>> 8ul));
  upd output 10ul (sint64_to_sint8 (i2 ^>> 16ul));
  upd output 11ul (sint64_to_sint8 (i2 ^>> 24ul));

  upd output 12ul (sint64_to_sint8 (i3 ^>> 0ul));
  upd output 13ul (sint64_to_sint8 (i3 ^>> 8ul));
  upd output 14ul (sint64_to_sint8 (i3 ^>> 16ul));
  upd output 15ul (sint64_to_sint8 (i3 ^>> 24ul));

  upd output 16ul (sint64_to_sint8 (i4 ^>> 0ul));
  upd output 17ul (sint64_to_sint8 (i4 ^>> 8ul));
  upd output 18ul (sint64_to_sint8 (i4 ^>> 16ul));
  upd output 19ul (sint64_to_sint8 (i4 ^>> 24ul));

  upd output 20ul (sint64_to_sint8 (i5 ^>> 0ul));
  upd output 21ul (sint64_to_sint8 (i5 ^>> 8ul));
  upd output 22ul (sint64_to_sint8 (i5 ^>> 16ul));
  upd output 23ul (sint64_to_sint8 (i5 ^>> 24ul));

  upd output 24ul (sint64_to_sint8 (i6 ^>> 0ul));
  upd output 25ul (sint64_to_sint8 (i6 ^>> 8ul));
  upd output 26ul (sint64_to_sint8 (i6 ^>> 16ul));
  upd output 27ul (sint64_to_sint8 (i6 ^>> 24ul));

  upd output 28ul (sint64_to_sint8 (i7 ^>> 0ul));
  upd output 29ul (sint64_to_sint8 (i7 ^>> 8ul));
  upd output 30ul (sint64_to_sint8 (i7 ^>> 16ul));
  upd output 31ul (sint64_to_sint8 (i7 ^>> 24ul));
  ()

val exp: output:u8s{length output >= 64} -> q_x:u8s{length q_x >= 32 /\ disjoint q_x output} ->
  q_y:u8s{length q_y >= 32 /\ disjoint q_y output} ->
  pk:u8s{length pk >= 32 /\ disjoint pk output} -> STL unit
  (requires (fun h -> live h output /\ live h q_x /\ live h pk))
  (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let exp output q_x q_y scalar =
  push_frame();

  (* Allocate *)
  let zero = uint64_to_sint64 0uL in
  let one  = uint64_to_sint64 1uL in
  
  let qx = create zero nlength in
  let qy = create zero nlength in
  let qz = create zero nlength in
  let resx = create zero nlength in
  let resy = create zero nlength in
  let resz = create zero nlength in
  let zrecip = create zero nlength in
  let zrecip2 = create zero nlength in
  let zrecip3 = create zero nlength in
    
  (* Format scalar *)
  format_scalar scalar;

  (* Create basepoint *)
  expand qx q_x;
  expand qy q_y;
  upd qz 0ul one;
  let basepoint = Curve.Point.Point qx qy qz in

  (* Point to store the result *)
  let res = Curve.Point.Point resx resy resz in

  (* Ladder *)
  montgomery_ladder res scalar basepoint;

  (* Get the affine coordinates back *)
  crecip' zrecip (Curve.Point.get_z res);
  fsquare zrecip2 zrecip;
  fmul zrecip3 zrecip zrecip2;
  fmul qx resx zrecip2;
  fmul qy resy zrecip3;
  let x = Hacl.SBuffer.sub output 0ul 32ul in
  let y = Hacl.SBuffer.sub output 32ul 32ul in
  contract x qx;
  contract y qy;
  pop_frame()
