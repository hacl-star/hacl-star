module Curve.Curve448

open FStar.HST
open Hacl.UInt8
open Hacl.Cast
open Hacl.SBuffer
open Curve.Parameters
open Curve.Bignum
open Curve.Crecip
open Curve.Ladder

#set-options "--lax"

let op_Hat_Greater_Greater : s64 -> UInt32.t -> Tot s64 = Hacl.UInt64.shift_right

val format_scalar: scalar:u8s{length scalar >= 32} -> STL unit
  (requires (fun h -> live h scalar))
  (ensures  (fun h0 _ h1 -> modifies_1 scalar h0 h1 /\ live h1 scalar))
let format_scalar scalar =
  upd scalar 0ul ((index scalar 0ul) &^ (uint8_to_sint8 252uy));
  upd scalar 55ul ((index scalar 55ul) |^ (uint8_to_sint8 128uy))

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
  let i32 = index input 32ul in
  let i33 = index input 33ul in
  let i34 = index input 34ul in
  let i35 = index input 35ul in
  let i36 = index input 36ul in
  let i37 = index input 37ul in
  let i38 = index input 38ul in
  let i39 = index input 39ul in
  let i40 = index input 40ul in
  let i41 = index input 41ul in
  let i42 = index input 42ul in
  let i43 = index input 43ul in
  let i44 = index input 44ul in
  let i45 = index input 45ul in
  let i46 = index input 46ul in
  let i47 = index input 47ul in
  let i48 = index input 48ul in
  let i49 = index input 49ul in
  let i50 = index input 50ul in
  let i51 = index input 51ul in
  let i52 = index input 52ul in
  let i53 = index input 53ul in
  let i54 = index input 54ul in
  let i55 = index input 55ul in
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
  let i32 = (sint8_to_sint64 (i32)) in
  let i33 = (sint8_to_sint64 (i33)) in
  let i34 = (sint8_to_sint64 (i34)) in
  let i35 = (sint8_to_sint64 (i35)) in
  let i36 = (sint8_to_sint64 (i36)) in
  let i37 = (sint8_to_sint64 (i37)) in
  let i38 = (sint8_to_sint64 (i38)) in
  let i39 = (sint8_to_sint64 (i39)) in
  let i40 = (sint8_to_sint64 (i40)) in
  let i41 = (sint8_to_sint64 (i41)) in
  let i42 = (sint8_to_sint64 (i42)) in
  let i43 = (sint8_to_sint64 (i43)) in
  let i44 = (sint8_to_sint64 (i44)) in
  let i45 = (sint8_to_sint64 (i45)) in
  let i46 = (sint8_to_sint64 (i46)) in
  let i47 = (sint8_to_sint64 (i47)) in
  let i48 = (sint8_to_sint64 (i48)) in
  let i49 = (sint8_to_sint64 (i49)) in
  let i50 = (sint8_to_sint64 (i50)) in
  let i51 = (sint8_to_sint64 (i51)) in
  let i52 = (sint8_to_sint64 (i52)) in
  let i53 = (sint8_to_sint64 (i53)) in
  let i54 = (sint8_to_sint64 (i54)) in
  let i55 = (sint8_to_sint64 (i55)) in
  let o0 = (i0 +^ (i1 <<^ 8ul) +^ (i2 <<^ 16ul) +^ (i3 <<^ 24ul)
  	   +^ (i4 <<^ 32ul) +^ (i5 <<^ 40ul) +^ ((i6 <<^ 48ul))) in
  let o1 = (i7 +^ (i8 <<^ 8ul) +^ (i9 <<^ 16ul) +^ (i10 <<^ 24ul)
  	   +^ (i11 <<^ 32ul) +^ (i12 <<^ 40ul) +^ ((i13 <<^ 48ul))) in
  let o2 = (i14 +^ (i15 <<^ 8ul) +^ (i16 <<^ 16ul) +^ (i17 <<^ 24ul)
  	   +^ (i18 <<^ 32ul) +^ (i19 <<^ 40ul) +^ ((i20 <<^ 48ul))) in
  let o3 = (i21 +^ (i22 <<^ 8ul) +^ (i23 <<^ 16ul) +^ (i24 <<^ 24ul)
  	   +^ (i25 <<^ 32ul) +^ (i26 <<^ 40ul) +^ ((i27 <<^ 48ul))) in
  let o4 = (i28 +^ (i29 <<^ 8ul) +^ (i30 <<^ 16ul) +^ (i31 <<^ 24ul)
  	   +^ (i32 <<^ 32ul) +^ (i33 <<^ 40ul) +^ ((i34 <<^ 48ul))) in
  let o5 = (i35 +^ (i36 <<^ 8ul) +^ (i37 <<^ 16ul) +^ (i38 <<^ 24ul)
  	   +^ (i39 <<^ 32ul) +^ (i40 <<^ 40ul) +^ ((i41 <<^ 48ul))) in
  let o6 = (i42 +^ (i43 <<^ 8ul) +^ (i44 <<^ 16ul) +^ (i45 <<^ 24ul)
  	   +^ (i46 <<^ 32ul) +^ (i47 <<^ 40ul) +^ ((i48 <<^ 48ul))) in
  let o7 = (i49 +^ (i50 <<^ 8ul) +^ (i51 <<^ 16ul) +^ (i52 <<^ 24ul)
  	   +^ (i53 <<^ 32ul) +^ (i54 <<^ 40ul) +^ ((i55 <<^ 48ul))) in
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
  upd output 4ul (sint64_to_sint8 (i0 ^>> 32ul));
  upd output 5ul (sint64_to_sint8 (i0 ^>> 40ul));
  upd output 6ul (sint64_to_sint8 (i0 ^>> 48ul));
  
  upd output 7ul (sint64_to_sint8 (i1 ^>> 0ul));
  upd output 8ul (sint64_to_sint8 (i1 ^>> 8ul));
  upd output 9ul (sint64_to_sint8 (i1 ^>> 16ul));
  upd output 10ul (sint64_to_sint8 (i1 ^>> 24ul));
  upd output 11ul (sint64_to_sint8 (i1 ^>> 32ul));
  upd output 12ul (sint64_to_sint8 (i1 ^>> 40ul));
  upd output 13ul (sint64_to_sint8 (i1 ^>> 48ul));

  upd output 14ul (sint64_to_sint8 (i2 ^>> 0ul));
  upd output 15ul (sint64_to_sint8 (i2 ^>> 8ul));
  upd output 16ul (sint64_to_sint8 (i2 ^>> 16ul));
  upd output 17ul (sint64_to_sint8 (i2 ^>> 24ul));
  upd output 18ul (sint64_to_sint8 (i2 ^>> 32ul));
  upd output 19ul (sint64_to_sint8 (i2 ^>> 40ul));
  upd output 20ul (sint64_to_sint8 (i2 ^>> 48ul));

  upd output 21ul (sint64_to_sint8 (i3 ^>> 0ul));
  upd output 22ul (sint64_to_sint8 (i3 ^>> 8ul));
  upd output 23ul (sint64_to_sint8 (i3 ^>> 16ul));
  upd output 24ul (sint64_to_sint8 (i3 ^>> 24ul));
  upd output 25ul (sint64_to_sint8 (i3 ^>> 32ul));
  upd output 26ul (sint64_to_sint8 (i3 ^>> 40ul));
  upd output 27ul (sint64_to_sint8 (i3 ^>> 48ul));

  upd output 28ul (sint64_to_sint8 (i4 ^>> 0ul));
  upd output 29ul (sint64_to_sint8 (i4 ^>> 8ul));
  upd output 30ul (sint64_to_sint8 (i4 ^>> 16ul));
  upd output 31ul (sint64_to_sint8 (i4 ^>> 24ul));
  upd output 32ul (sint64_to_sint8 (i4 ^>> 32ul));
  upd output 33ul (sint64_to_sint8 (i4 ^>> 40ul));
  upd output 34ul (sint64_to_sint8 (i4 ^>> 48ul));

  upd output 35ul (sint64_to_sint8 (i5 ^>> 0ul));
  upd output 36ul (sint64_to_sint8 (i5 ^>> 8ul));
  upd output 37ul (sint64_to_sint8 (i5 ^>> 16ul));
  upd output 38ul (sint64_to_sint8 (i5 ^>> 24ul));
  upd output 39ul (sint64_to_sint8 (i5 ^>> 32ul));
  upd output 40ul (sint64_to_sint8 (i5 ^>> 40ul));
  upd output 41ul (sint64_to_sint8 (i5 ^>> 48ul));

  upd output 42ul (sint64_to_sint8 (i6 ^>> 0ul));
  upd output 43ul (sint64_to_sint8 (i6 ^>> 8ul));
  upd output 44ul (sint64_to_sint8 (i6 ^>> 16ul));
  upd output 45ul (sint64_to_sint8 (i6 ^>> 24ul));
  upd output 46ul (sint64_to_sint8 (i6 ^>> 32ul));
  upd output 47ul (sint64_to_sint8 (i6 ^>> 40ul));
  upd output 48ul (sint64_to_sint8 (i6 ^>> 48ul));

  upd output 49ul (sint64_to_sint8 (i7 ^>> 0ul));
  upd output 50ul (sint64_to_sint8 (i7 ^>> 8ul));
  upd output 51ul (sint64_to_sint8 (i7 ^>> 16ul));
  upd output 52ul (sint64_to_sint8 (i7 ^>> 24ul));
  upd output 53ul (sint64_to_sint8 (i7 ^>> 32ul));
  upd output 54ul (sint64_to_sint8 (i7 ^>> 40ul));
  upd output 55ul (sint64_to_sint8 (i7 ^>> 48ul));
  ()

val exp: output:u8s{length output >= bytes_length} -> q_x:u8s{length q_x >= bytes_length /\ disjoint q_x output} ->
  pk:u8s{length pk >= bytes_length /\ disjoint pk output} -> STL unit
  (requires (fun h -> live h output /\ live h q_x /\ live h pk))
  (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
let exp output q_x scalar =
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
    
  (* Format scalar *)
  format_scalar scalar;

  (* Create basepoint *)
  expand qx q_x;
  upd qz 0ul one;
  let basepoint = Curve.Point.Point qx qy qz in

  (* Point to store the result *)
  let res = Curve.Point.Point resx resy resz in

  (* Ladder *)
  montgomery_ladder res scalar basepoint;

  (* Get the affine coordinates back *)
  crecip' zrecip (Curve.Point.get_z res);
  fmul resy resx zrecip;
  contract output resy;

  pop_frame()
