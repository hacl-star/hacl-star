module Hacl.Policies

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack.ST
open FStar.Buffer

open Hacl.Types

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module H8  = Hacl.UInt8
module H32  = Hacl.UInt32
module H64  = Hacl.UInt64
module H128  = Hacl.UInt128

assume new type declassifiable (x:uint8_p)

assume val declassify_u8: x:H8.t -> Tot (y:U8.t{H8.v x = U8.v y})
assume val declassify_u32: x:H32.t -> Tot (y:U32.t{H32.v x = U32.v y})
assume val declassify_u64: x:H64.t -> Tot (y:U64.t{H64.v x = U64.v y})
assume val declassify_u128: x:H128.t -> Tot (y:U128.t{H128.v x = U128.v y})


assume val leak_byte:
  b:uint8_p{declassifiable b} ->
  n:u32{U32.v n < length b} ->
  Stack u8
    (requires (fun h -> live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ U8.v z = H8.v (get h0 b (U32.v n))))

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 50"

val cmp_bytes_:
  b1:uint8_p{declassifiable b1} ->
  b2:uint8_p{declassifiable b2} ->
  len:u32{U32.v len <= length b1 /\ U32.v len <= length b2} ->
  tmp:u8{tmp == 0uy \/ tmp == 255uy} ->
  Stack u8
    (requires (fun h -> live h b1 /\ live h b2))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      (z == 255uy ==> tmp == 255uy /\ equal h0 (sub b1 0ul len) h0 (sub b2 0ul len)) ))
let rec cmp_bytes_ b1 b2 len tmp =
  UInt.logand_lemma_1 #8 255;
  UInt.logand_lemma_2 #8 255;
  UInt.logand_lemma_1 #8 0;
  UInt.logand_lemma_2 #8 0;
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then tmp
  else
    let i = U32.(len -^ 1ul) in
    let bi1 = leak_byte b1 i in
    let bi2 = leak_byte b2 i in
    let z = cmp_bytes_ b1 b2 i U8.(eq_mask bi1 bi2 &^ tmp) in
    if U8.v z = 255 then
      begin
      let s1  = as_seq h0 (sub b1 0ul len) in
      let s2  = as_seq h0 (sub b2 0ul len) in
      let s1' = as_seq h0 (sub b1 0ul i) in
      let s2' = as_seq h0 (sub b2 0ul i) in
      assert (forall (j:nat{j < U32.v i}).{:pattern (Seq.index s1 j); (Seq.index s2 j)}
        Seq.index s1 j == Seq.index s1' j /\ Seq.index s2 j == Seq.index s2' j);
      Seq.lemma_eq_intro s1 s2
      end;
    z

val cmp_bytes:
  b1:uint8_p{declassifiable b1} ->
  b2:uint8_p{declassifiable b2} ->
  len:u32{U32.v len <= length b1 /\ U32.v len <= length b2} ->
  Stack u8
    (requires (fun h -> live h b1 /\ live h b2))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      (z == 0uy ==> equal h0 (sub b1 0ul len) h0 (sub b2 0ul len))))
let cmp_bytes b1 b2 len =
  let z = cmp_bytes_ b1 b2 len 255uy in
  UInt.lognot_lemma_1 #8;
  UInt.lognot_self #8 (U8.v z);
  U8.lognot z
