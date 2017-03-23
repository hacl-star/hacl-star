module Seq.Create

open FStar.Seq

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

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

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
