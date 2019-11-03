module Spec.Frodo.Pack

open FStar.Mul

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.Matrix

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

#reset-options "--z3rlimit 100 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar +FStar.Pervasives +FStar.UInt -Spec +Spec.Frodo +Spec.Frodo.Params +Spec.Matrix'"

/// Pack

val frodo_pack8:
    d:size_nat{d <= 16}
  -> a:lseq uint16 8
  -> lbytes d
let frodo_pack8 d a =
  let maskd = to_u16 (u32 1 <<. size d) -. u16 1 in
  let a0 = Seq.index a 0 &. maskd in
  let a1 = Seq.index a 1 &. maskd in
  let a2 = Seq.index a 2 &. maskd in
  let a3 = Seq.index a 3 &. maskd in
  let a4 = Seq.index a 4 &. maskd in
  let a5 = Seq.index a 5 &. maskd in
  let a6 = Seq.index a 6 &. maskd in
  let a7 = Seq.index a 7 &. maskd in
  let templong =
       to_u128 a0 <<. size (7 * d)
    |. to_u128 a1 <<. size (6 * d)
    |. to_u128 a2 <<. size (5 * d)
    |. to_u128 a3 <<. size (4 * d)
    |. to_u128 a4 <<. size (3 * d)
    |. to_u128 a5 <<. size (2 * d)
    |. to_u128 a6 <<. size (1 * d)
    |. to_u128 a7 <<. size (0 * d)
  in
  let v16 = uint_to_bytes_be templong in
  Seq.sub v16 (16 - d) d

val frodo_pack_state:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ (n1 * n2) % 8 = 0}
  -> d:size_nat{d * ((n1 * n2) / 8) <= max_size_t /\ d <= 16}
  -> i:size_nat{i <= (n1 * n2) / 8}
  -> Type0
let frodo_pack_state #n1 #n2 d i = lseq uint8 (d * i)

val frodo_pack_inner:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ (n1 * n2) % 8 = 0}
  -> d:size_nat{d * ((n1 * n2) / 8) <= max_size_t /\ d <= 16}
  -> a:matrix n1 n2
  -> i:size_nat{i < (n1 * n2) / 8}
  -> frodo_pack_state #n1 #n2 d i
  -> frodo_pack_state #n1 #n2 d (i + 1)
let frodo_pack_inner #n1 #n2 d a i s =
  s @| frodo_pack8 d (Seq.sub a (8 * i) 8)

val frodo_pack:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ (n1 * n2) % 8 = 0}
  -> d:size_nat{d * ((n1 * n2) / 8) <= max_size_t /\ d <= 16}
  -> a:matrix n1 n2
  -> res:lbytes (d * ((n1 * n2) / 8))
let frodo_pack #n1 #n2 d a =
  Loops.repeat_gen ((n1 * n2) / 8)
    (frodo_pack_state #n1 #n2 d)
    (frodo_pack_inner #n1 #n2 d a)
    (Seq.create 0 (u8 0))

/// Unpack

val frodo_unpack8:
    d:size_nat{d <= 16}
  -> b:lbytes d
  -> lseq uint16 8
let frodo_unpack8 d b =
  let maskd = to_u16 (u32 1 <<. size d) -. u16 1 in
  let v16 = Seq.create 16 (u8 0) in
  let src = update_sub v16 (16 - d) d b in
  let templong: uint_t U128 SEC = uint_from_bytes_be src in
  let res = Seq.create 8 (u16 0) in
  let res = res.[0] <- to_u16 (templong >>. size (7 * d)) &. maskd in
  let res = res.[1] <- to_u16 (templong >>. size (6 * d)) &. maskd in
  let res = res.[2] <- to_u16 (templong >>. size (5 * d)) &. maskd in
  let res = res.[3] <- to_u16 (templong >>. size (4 * d)) &. maskd in
  let res = res.[4] <- to_u16 (templong >>. size (3 * d)) &. maskd in
  let res = res.[5] <- to_u16 (templong >>. size (2 * d)) &. maskd in
  let res = res.[6] <- to_u16 (templong >>. size (1 * d)) &. maskd in
  let res = res.[7] <- to_u16 (templong >>. size (0 * d)) &. maskd in
  res

val frodo_unpack_state:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ (n1 * n2) % 8 = 0}
  -> i:size_nat{i <= (n1 * n2) / 8}
  -> Type0
let frodo_unpack_state #n1 #n2 i = lseq uint16 (8 * i)

val frodo_unpack_inner:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ (n1 * n2) % 8 = 0}
  -> d:size_nat{d * ((n1 * n2) / 8) <= max_size_t /\ d <= 16}
  -> b:lbytes (d * ((n1 * n2) / 8))
  -> i:size_nat{i < (n1 * n2) / 8}
  -> frodo_unpack_state #n1 #n2 i
  -> frodo_unpack_state #n1 #n2 (i + 1)
let frodo_unpack_inner #n1 #n2 d b i s =
  s @| frodo_unpack8 d (Seq.sub b (d * i) d)

val frodo_unpack:
    #n1:size_nat
  -> #n2:size_nat{n1 * n2 <= max_size_t /\ (n1 * n2) % 8 = 0}
  -> d:size_nat{d * ((n1 * n2) / 8) <= max_size_t /\ d <= 16}
  -> lbytes (d * ((n1 * n2) / 8))
  -> matrix n1 n2
let frodo_unpack #n1 #n2 d b =
  Loops.repeat_gen ((n1 * n2) / 8)
    (frodo_unpack_state #n1 #n2)
    (frodo_unpack_inner #n1 #n2 d b)
    FStar.Seq.empty
