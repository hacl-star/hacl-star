module Seq.Create

module ST = FStar.HyperStack.ST

open FStar.Seq


#set-options "--max_fuel 0 --z3rlimit 500"


private let op_String_Assignment = upd

abstract val create_1: #a:Type -> s0:a -> Tot (s:seq a{length s = 1 /\ index s 0 == s0})
let create_1 #a s0 =
  let s = create 1 s0 in s

abstract val create_2: #a:Type -> s0:a -> s1:a -> Tot (s:seq a{length s = 2 /\ index s 0 == s0 /\ index s 1 == s1})
let create_2 #a s0 s1 =
  let s = create 2 s0 in
  let s = s.[1] <- s1 in s

abstract val create_3: #a:Type -> s0:a -> s1:a -> s2:a -> Tot (s:seq a{length s = 3 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2})
let create_3 #a s0 s1 s2 =
  let s = create 3 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in s

abstract val create_4: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a ->
  Tot (s:seq a{length s = 4 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3})
let create_4 #a s0 s1 s2 s3 =
  let s = create 4 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in s

abstract val create_5: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a -> s4:a ->
  Tot (s:seq a{length s = 5 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3  /\ index s 4 == s4})
let create_5 #a s0 s1 s2 s3 s4 =
  let s = create 5 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in s

abstract val create_6: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a ->
  Tot (s:seq a{length s = 6 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3  /\ index s 4 == s4 /\ index s 5 == s5})
let create_6 #a s0 s1 s2 s3 s4 s5 =
  let s = create 6 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in s

abstract val create_7: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a ->
  Tot (s:seq a{length s = 7 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3  /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6})
let create_7 #a s0 s1 s2 s3 s4 s5 s6 =
  let s = create 7 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in s

abstract val create_8: #a:Type -> s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  Tot (s:seq a{length s = 8 /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3  /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7})
let create_8 #a s0 s1 s2 s3 s4 s5 s6 s7 =
  let s = create 8 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in s

#set-options "--max_fuel 0 --z3rlimit 20"

abstract val create_9: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a -> s8:a ->
  Tot (s:seq a{length s = 9
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8})
let create_9 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 =
  let s = create 9 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in s

abstract val create_10: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a ->
  Tot (s:seq a{length s = 10
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9})
let create_10 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 =
  let s = create 10 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in s

abstract val create_11: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a ->
  Tot (s:seq a{length s = 11
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10})
let create_11 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10  =
  let s = create 11 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in s

abstract val create_12: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a -> s11:a ->
  Tot (s:seq a{length s = 12
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10 /\ index s 11 == s11})
let create_12 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 =
  let s = create 12 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in
  let s = s.[11] <- s11 in s

abstract val create_13: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a -> s11:a -> s12:a ->
  Tot (s:seq a{length s = 13
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10 /\ index s 11 == s11
    /\ index s 12 == s12})
let create_13 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 =
  let s = create 13 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in
  let s = s.[11] <- s11 in
  let s = s.[12] <- s12 in s

abstract val create_14: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a -> s11:a -> s12:a -> s13:a ->
  Tot (s:seq a{length s = 14
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10 /\ index s 11 == s11
    /\ index s 12 == s12 /\ index s 13 == s13})
let create_14 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 =
  let s = create 14 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in
  let s = s.[11] <- s11 in
  let s = s.[12] <- s12 in
  let s = s.[13] <- s13 in s

abstract val create_15: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a -> s11:a -> s12:a -> s13:a -> s14:a ->
  Tot (s:seq a{length s = 15
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10 /\ index s 11 == s11
    /\ index s 12 == s12 /\ index s 13 == s13 /\ index s 14 == s14})
let create_15 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 =
  let s = create 15 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in
  let s = s.[11] <- s11 in
  let s = s.[12] <- s12 in
  let s = s.[13] <- s13 in
  let s = s.[14] <- s14 in s

abstract val create_16: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a -> s10:a -> s11:a -> s12:a -> s13:a -> s14:a -> s15:a ->
  Tot (s:seq a{length s = 16
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9 /\ index s 10 == s10 /\ index s 11 == s11
    /\ index s 12 == s12 /\ index s 13 == s13 /\ index s 14 == s14 /\ index s 15 == s15})
let create_16 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =
  let s = create 16 s0 in
  let s = s.[1] <- s1 in
  let s = s.[2] <- s2 in
  let s = s.[3] <- s3 in
  let s = s.[4] <- s4 in
  let s = s.[5] <- s5 in
  let s = s.[6] <- s6 in
  let s = s.[7] <- s7 in
  let s = s.[8] <- s8 in
  let s = s.[9] <- s9 in
  let s = s.[10] <- s10 in
  let s = s.[11] <- s11 in
  let s = s.[12] <- s12 in
  let s = s.[13] <- s13 in
  let s = s.[14] <- s14 in
  let s = s.[15] <- s15 in s


#reset-options "--max_fuel 0 --z3rlimit 100"

abstract val create_32: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a ->
  s10:a -> s11:a -> s12:a -> s13:a -> s14:a -> s15:a -> s16:a -> s17:a ->
  s18:a -> s19:a ->
  s20:a -> s21:a -> s22:a -> s23:a -> s24:a -> s25:a -> s26:a -> s27:a ->
  s28:a -> s29:a ->
  s30:a -> s31:a ->
  Tot (s:seq a{length s = 32
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9
    /\ index s 10 == s10 /\ index s 11 == s11 /\ index s 12 == s12 /\ index s 13 == s13
    /\ index s 14 == s14 /\ index s 15 == s15 /\ index s 16 == s16 /\ index s 17 == s17
    /\ index s 18 == s18 /\ index s 19 == s19
    /\ index s 20 == s20 /\ index s 21 == s21 /\ index s 22 == s22 /\ index s 23 == s23
    /\ index s 24 == s24 /\ index s 25 == s25 /\ index s 26 == s26 /\ index s 27 == s27
    /\ index s 28 == s28 /\ index s 29 == s29
    /\ index s 30 == s30 /\ index s 31 == s31})

let create_32 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31
 =
  let sfirst = create_16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 in
  let ssecond = create_16 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 in
  sfirst @| ssecond

abstract val create_64: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a ->
  s10:a -> s11:a -> s12:a -> s13:a -> s14:a -> s15:a -> s16:a -> s17:a ->
  s18:a -> s19:a ->
  s20:a -> s21:a -> s22:a -> s23:a -> s24:a -> s25:a -> s26:a -> s27:a ->
  s28:a -> s29:a ->
  s30:a -> s31:a -> s32:a -> s33:a -> s34:a -> s35:a -> s36:a -> s37:a ->
  s38:a -> s39:a ->
  s40:a -> s41:a -> s42:a -> s43:a -> s44:a -> s45:a -> s46:a -> s47:a ->
  s48:a -> s49:a ->
  s50:a -> s51:a -> s52:a -> s53:a -> s54:a -> s55:a -> s56:a -> s57:a ->
  s58:a -> s59:a ->
  s60:a -> s61:a -> s62:a -> s63:a ->
  Tot (s:seq a{length s = 64
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9
    /\ index s 10 == s10 /\ index s 11 == s11 /\ index s 12 == s12 /\ index s 13 == s13
    /\ index s 14 == s14 /\ index s 15 == s15 /\ index s 16 == s16 /\ index s 17 == s17
    /\ index s 18 == s18 /\ index s 19 == s19
    /\ index s 20 == s20 /\ index s 21 == s21 /\ index s 22 == s22 /\ index s 23 == s23
    /\ index s 24 == s24 /\ index s 25 == s25 /\ index s 26 == s26 /\ index s 27 == s27
    /\ index s 28 == s28 /\ index s 29 == s29
    /\ index s 30 == s30 /\ index s 31 == s31 /\ index s 32 == s32 /\ index s 33 == s33
    /\ index s 34 == s34 /\ index s 35 == s35 /\ index s 36 == s36 /\ index s 37 == s37
    /\ index s 38 == s38 /\ index s 39 == s39
    /\ index s 40 == s40 /\ index s 41 == s41 /\ index s 42 == s42 /\ index s 43 == s43
    /\ index s 44 == s44 /\ index s 45 == s45 /\ index s 46 == s46 /\ index s 47 == s47
    /\ index s 48 == s48 /\ index s 49 == s49
    /\ index s 50 == s50 /\ index s 51 == s51 /\ index s 52 == s52 /\ index s 53 == s53
    /\ index s 54 == s54 /\ index s 55 == s55 /\ index s 56 == s56 /\ index s 57 == s57
    /\ index s 58 == s58 /\ index s 59 == s59
    /\ index s 60 == s60 /\ index s 61 == s61 /\ index s 62 == s62 /\ index s 63 == s63})

let create_64 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63
 =
  let sfirst = create_32 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 in
  let ssecond = create_32 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63 in
  sfirst @| ssecond

abstract val create_80: #a:Type ->
  s0:a -> s1:a -> s2:a -> s3:a -> s4:a -> s5:a -> s6:a -> s7:a ->
  s8:a -> s9:a ->
  s10:a -> s11:a -> s12:a -> s13:a -> s14:a -> s15:a -> s16:a -> s17:a ->
  s18:a -> s19:a ->
  s20:a -> s21:a -> s22:a -> s23:a -> s24:a -> s25:a -> s26:a -> s27:a ->
  s28:a -> s29:a ->
  s30:a -> s31:a -> s32:a -> s33:a -> s34:a -> s35:a -> s36:a -> s37:a ->
  s38:a -> s39:a ->
  s40:a -> s41:a -> s42:a -> s43:a -> s44:a -> s45:a -> s46:a -> s47:a ->
  s48:a -> s49:a ->
  s50:a -> s51:a -> s52:a -> s53:a -> s54:a -> s55:a -> s56:a -> s57:a ->
  s58:a -> s59:a ->
  s60:a -> s61:a -> s62:a -> s63:a -> s64:a -> s65:a -> s66:a -> s67:a ->
  s68:a -> s69:a ->
  s70:a -> s71:a -> s72:a -> s73:a -> s74:a -> s75:a -> s76:a -> s77:a ->
  s78:a -> s79:a ->
  Tot (s:seq a{length s = 80
    /\ index s 0 == s0 /\ index s 1 == s1 /\ index s 2 == s2 /\ index s 3 == s3
    /\ index s 4 == s4 /\ index s 5 == s5 /\ index s 6 == s6 /\ index s 7 == s7
    /\ index s 8 == s8 /\ index s 9 == s9
    /\ index s 10 == s10 /\ index s 11 == s11 /\ index s 12 == s12 /\ index s 13 == s13
    /\ index s 14 == s14 /\ index s 15 == s15 /\ index s 16 == s16 /\ index s 17 == s17
    /\ index s 18 == s18 /\ index s 19 == s19
    /\ index s 20 == s20 /\ index s 21 == s21 /\ index s 22 == s22 /\ index s 23 == s23
    /\ index s 24 == s24 /\ index s 25 == s25 /\ index s 26 == s26 /\ index s 27 == s27
    /\ index s 28 == s28 /\ index s 29 == s29
    /\ index s 30 == s30 /\ index s 31 == s31 /\ index s 32 == s32 /\ index s 33 == s33
    /\ index s 34 == s34 /\ index s 35 == s35 /\ index s 36 == s36 /\ index s 37 == s37
    /\ index s 38 == s38 /\ index s 39 == s39
    /\ index s 40 == s40 /\ index s 41 == s41 /\ index s 42 == s42 /\ index s 43 == s43
    /\ index s 44 == s44 /\ index s 45 == s45 /\ index s 46 == s46 /\ index s 47 == s47
    /\ index s 48 == s48 /\ index s 49 == s49
    /\ index s 50 == s50 /\ index s 51 == s51 /\ index s 52 == s52 /\ index s 53 == s53
    /\ index s 54 == s54 /\ index s 55 == s55 /\ index s 56 == s56 /\ index s 57 == s57
    /\ index s 58 == s58 /\ index s 59 == s59
    /\ index s 60 == s60 /\ index s 61 == s61 /\ index s 62 == s62 /\ index s 63 == s63
    /\ index s 64 == s64 /\ index s 65 == s65 /\ index s 66 == s66 /\ index s 67 == s67
    /\ index s 68 == s68 /\ index s 69 == s69
    /\ index s 70 == s70 /\ index s 71 == s71 /\ index s 72 == s72 /\ index s 73 == s73
    /\ index s 74 == s74 /\ index s 75 == s75 /\ index s 76 == s76 /\ index s 77 == s77
    /\ index s 78 == s78 /\ index s 79 == s79})

let create_80 #a s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63 s64 s65 s66 s67 s68 s69 s70 s71 s72 s73 s74 s75 s76 s77 s78 s79 =
  let s' = create_64 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63 in
  let s'' = create_16 s64 s65 s66 s67 s68 s69 s70 s71 s72 s73 s74 s75 s76 s77 s78 s79 in
  s' @| s''
