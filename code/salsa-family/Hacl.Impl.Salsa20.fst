module Hacl.Impl.Salsa20

open FStar.Mul
open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.Cast
open Hacl.UInt32
open Hacl.Spec.Endianness
open Hacl.Endianness
open Spec.Salsa20
open C.Loops


module Spec = Spec.Salsa20

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_p = buffer H8.t

type state = b:Buffer.buffer h32{length b = 16}

private inline_for_extraction let op_Less_Less_Less (a:h32) (s:u32{U32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val lemma_uint32s_from_le_bytes: h:mem -> output:buffer H32.t{live h output} ->
  h':mem -> input:uint8_p{live h' input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input /\ U32.v len > 0} ->
  Lemma
    (requires (H32.v (Seq.index (as_seq h output) 0) =
        U32.v (Spec.Lib.uint32_from_le (reveal_sbytes (as_seq h' (Buffer.sub input 0ul 4ul))))
      /\ reveal_h32s (as_seq h (Buffer.offset output 1ul)) == 
        Spec.Lib.uint32s_from_le (UInt32.v len - 1) (reveal_sbytes (as_seq h' (Buffer.offset input 4ul)))))
    (ensures (reveal_h32s (as_seq h output)
      == Spec.Lib.uint32s_from_le (U32.v len) (reveal_sbytes ((as_seq h' input)))))
let lemma_uint32s_from_le_bytes h output h' input len =
  let i' = reveal_sbytes (as_seq h' input) in
  Spec.Lib.lemma_uint32s_from_le_def_1 (U32.v len) i';
  Seq.lemma_eq_intro (as_seq h' (Buffer.sub input 0ul 4ul)) (Seq.slice (as_seq h' input) 0 4);
  Seq.lemma_eq_intro (as_seq h' (Buffer.offset input 4ul)) (Seq.slice (as_seq h' input) 4 (length input));
  Seq.lemma_eq_intro (as_seq h (Buffer.offset output 1ul)) (Seq.slice (as_seq h output) 1 (length output));
  cut (Seq.index (Spec.Lib.uint32s_from_le (U32.v len) i') 0 == Spec.Lib.uint32_from_le (Seq.slice i' 0 4));
  Seq.lemma_eq_intro (reveal_h32s (as_seq h output)) (Spec.Lib.uint32s_from_le (U32.v len) i')


private val lemma_uint32s_from_le_bytes': h:mem -> h':mem -> output:buffer H32.t{live h output /\ live h' output /\ length output > 0} -> Lemma
  (requires (modifies_1 (Buffer.offset output 1ul) h h'))
  (ensures (Seq.index (as_seq h output) 0 == Seq.index (as_seq h' output) 0))
private let lemma_uint32s_from_le_bytes' h h' output =
  let output' = Buffer.sub output 0ul 1ul in
  let output'' = Buffer.offset output 1ul in
  no_upd_lemma_1 h h' output'' output';
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 1) (as_seq h output');
  Seq.lemma_eq_intro (Seq.append (as_seq h' output') (as_seq h' output'')) (as_seq h' output)


[@ "c_inline"]
val uint32s_from_le_bytes:
  output:buffer H32.t ->
  input:uint8_p{disjoint output input} ->
  len:U32.t{length output = U32.v len /\ 4 * U32.v len = length input} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_h32s (as_seq h1 output) in
       let i = reveal_sbytes (as_seq h0 input) in
       o == Spec.Lib.uint32s_from_le (U32.v len) i)))
[@ "c_inline"]
let rec uint32s_from_le_bytes output input len =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
    Spec.Lib.lemma_uint32s_from_le_def_0 0 (reveal_sbytes (as_seq h0 input));
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  )
  else (
    cut (U32.v len > 0);
    output.(0ul) <- hload32_le (Buffer.sub input 0ul 4ul);
    let h = ST.get() in
    let output' = Buffer.offset output 1ul in
    let input'  = Buffer.offset input 4ul in
    uint32s_from_le_bytes output' input' U32.(len -^ 1ul);
    let h1 = ST.get() in
    lemma_uint32s_from_le_bytes' h h1 output;
    lemma_uint32s_from_le_bytes h1 output h0 input len
  )


private val lemma_uint32s_to_le_bytes: h:mem -> output:uint8_p{live h output} ->
  h':mem -> input:buffer H32.t{live h' input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output /\ U32.v len > 0} ->
  Lemma
    (requires (Seq.slice (reveal_sbytes (as_seq h output)) 0 4 = Spec.Lib.uint32_to_le (Seq.index (reveal_h32s (as_seq h' input)) 0)
      /\ reveal_sbytes (as_seq h (Buffer.offset output 4ul)) == Spec.Lib.uint32s_to_le (UInt32.v len - 1) (reveal_h32s (as_seq h' (Buffer.offset input 1ul)))))
    (ensures (reveal_sbytes (as_seq h output) == Spec.Lib.uint32s_to_le (U32.v len) (reveal_h32s ((as_seq h' input)))))
let lemma_uint32s_to_le_bytes h output h' input len =
  let i' = reveal_h32s (as_seq h' input) in
  Spec.Lib.lemma_uint32s_to_le_def_1 (U32.v len) i';
  Seq.lemma_eq_intro (as_seq h (Buffer.sub output 0ul 4ul)) (Seq.slice (as_seq h output) 0 4);
  Seq.lemma_eq_intro (as_seq h (Buffer.offset output 4ul)) (Seq.slice (as_seq h output) 4 (length output));
  Seq.lemma_eq_intro (as_seq h' (Buffer.offset input 1ul)) (Seq.slice (as_seq h' input) 1 (length input));
  Seq.lemma_eq_intro (Seq.slice (Spec.Lib.uint32s_to_le (U32.v len) i') 0 4)
                     (Spec.Lib.uint32_to_le (Seq.index i' 0));
  Seq.lemma_eq_intro (reveal_sbytes (as_seq h output)) (Spec.Lib.uint32s_to_le (U32.v len) i')


private val lemma_uint32s_to_le_bytes': h:mem -> h':mem -> output:uint8_p{live h output /\ live h' output /\ length output >= 4} -> Lemma
  (requires (modifies_1 (Buffer.offset output 4ul) h h'))
  (ensures (Seq.slice (as_seq h output) 0 4 == Seq.slice (as_seq h' output) 0 4))
private let lemma_uint32s_to_le_bytes' h h' output =
  let output' = Buffer.sub output 0ul 4ul in
  let output'' = Buffer.offset output 4ul in
  no_upd_lemma_1 h h' output'' output';
  Seq.lemma_eq_intro (Seq.slice (as_seq h output) 0 4) (as_seq h output')


[@ "c_inline"]
val uint32s_to_le_bytes:
  output:uint8_p ->
  input:buffer H32.t{disjoint output input} ->
  len:U32.t{length input = U32.v len /\ 4 * U32.v len = length output} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h0 input /\ modifies_1 output h0 h1 /\
      (let o = reveal_sbytes (as_seq h1 output) in
       let i = reveal_h32s (as_seq h0 input) in
       o == Spec.Lib.uint32s_to_le (U32.v len) i)))
[@ "c_inline"]
let rec uint32s_to_le_bytes output input len =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
    Spec.Lib.lemma_uint32s_to_le_def_0 0 (reveal_h32s (as_seq h0 input));
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  )
  else (
    cut (U32.v len > 0);
    let hd = input.(0ul) in
    hstore32_le (Buffer.sub output 0ul 4ul) hd;
    let h = ST.get() in
    FStar.Endianness.lemma_little_endian_inj (Seq.slice (reveal_sbytes (as_seq h output)) 0 4)
                                             (Spec.Lib.uint32_to_le (h32_to_u32 hd));
    cut (Seq.slice (reveal_sbytes (as_seq h output)) 0 4 == Spec.Lib.uint32_to_le (h32_to_u32 hd));
    let output' = Buffer.offset output 4ul in
    let input'  = Buffer.offset input 1ul in
    uint32s_to_le_bytes output' input' U32.(len -^ 1ul);
    let h1 = ST.get() in
    lemma_uint32s_to_le_bytes' h h1 output;
    lemma_uint32s_to_le_bytes h1 output h0 input len
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 400"

[@ "substitute"]
val upd_16:
  st:state ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  v8:H32.t -> v9:H32.t -> v10:H32.t -> v11:H32.t -> v12:H32.t -> v13:H32.t -> v14:H32.t -> v15:H32.t ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1
      /\ (let s = as_seq h1 st in
         Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
         Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7 /\
         Seq.index s 8 == v8 /\ Seq.index s 9 == v9 /\ Seq.index s 10 == v10 /\ Seq.index s 11 == v11 /\
         Seq.index s 12 == v12 /\ Seq.index s 13 == v13 /\ Seq.index s 14 == v14 /\ Seq.index s 15 == v15)
     ))
[@ "substitute"]
let upd_16 st v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  st.(0ul) <- v0;
  st.(1ul) <- v1;
  st.(2ul) <- v2;
  st.(3ul) <- v3;
  st.(4ul) <- v4;
  st.(5ul) <- v5;
  st.(6ul) <- v6;
  st.(7ul) <- v7;
  st.(8ul) <- v8;
  st.(9ul) <- v9;
  st.(10ul) <- v10;
  st.(11ul) <- v11;
  st.(12ul) <- v12;
  st.(13ul) <- v13;
  st.(14ul) <- v14;
  st.(15ul) <- v15


#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"

private val lemma_seq_of_list: (#a:Type) -> (l:list a) -> Lemma
  (forall (i:nat). {:pattern (Seq.index (Seq.seq_of_list l) i)} i < List.Tot.length l
             ==> Seq.index (Seq.seq_of_list l) i == List.Tot.index l i)
let rec lemma_seq_of_list #a l =
  match l with
  | [] -> Seq.lemma_eq_intro (Seq.seq_of_list l) Seq.createEmpty
  | hd::tl -> (
    lemma_seq_of_list #a tl;
    Seq.lemma_eq_intro (Seq.seq_of_list l) (Seq.cons hd (Seq.seq_of_list tl))
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


private val lemma_create_16:
  s:Seq.seq H32.t{Seq.length s = 16} ->
  v0:H32.t -> v1:H32.t -> v2:H32.t -> v3:H32.t -> v4:H32.t -> v5:H32.t -> v6:H32.t -> v7:H32.t ->
  v8:H32.t -> v9:H32.t -> v10:H32.t -> v11:H32.t -> v12:H32.t -> v13:H32.t -> v14:H32.t -> v15:H32.t ->
  Lemma (requires (
       Seq.index s 0 == v0 /\ Seq.index s 1 == v1 /\ Seq.index s 2 == v2 /\ Seq.index s 3 == v3 /\
       Seq.index s 4 == v4 /\ Seq.index s 5 == v5 /\ Seq.index s 6 == v6 /\ Seq.index s 7 == v7 /\
       Seq.index s 8 == v8 /\ Seq.index s 9 == v9 /\ Seq.index s 10 == v10 /\ Seq.index s 11 == v11 /\
       Seq.index s 12 == v12 /\ Seq.index s 13 == v13 /\ Seq.index s 14 == v14 /\ Seq.index s 15 == v15))
        (ensures (s == Seq.seq_of_list ([v0; v1; v2; v3; v4; v5; v6; v7;
                                         v8; v9; v10; v11; v12; v13; v14; v15])))
let lemma_create_16 s v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
  assert_norm(List.Tot.length [v0; v1; v2; v3; v4; v5; v6; v7;
                                         v8; v9; v10; v11; v12; v13; v14; v15] = 16);
  let s' = Seq.seq_of_list ([v0; v1; v2; v3; v4; v5; v6; v7;
                                         v8; v9; v10; v11; v12; v13; v14; v15]) in
  lemma_seq_of_list [v0; v1; v2; v3; v4; v5; v6; v7;
                                         v8; v9; v10; v11; v12; v13; v14; v15];
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 0 = v0);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 1 = v1);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 2 = v2);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 3 = v3);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 4 = v4);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 5 = v5);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 6 = v6);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 7 = v7);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 8 = v8);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 9 = v9);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 10 = v10);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 11 = v11);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 12 = v12);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 13 = v13);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 14 = v14);
  assert_norm(List.Tot.index [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15] 15 = v15);
  Seq.lemma_eq_intro (Seq.seq_of_list [v0; v1; v2; v3; v4; v5; v6; v7;
                                         v8; v9; v10; v11; v12; v13; v14; v15]) s


[@ "c_inline"]
val setup:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 8 /\ disjoint st n} ->
  c:UInt64.t ->
  Stack unit
    (requires (fun h -> live h st /\ live h k /\ live h n))
    (ensures (fun h0 _ h1 -> live h0 k /\ live h0 n /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h1 st) in
         let k = reveal_sbytes (as_seq h0 k) in
         let n = reveal_sbytes (as_seq h0 n) in
         s == setup k n (UInt64.v c))))
[@ "c_inline"]
let setup st k n c =
  let h0 = ST.get() in
  push_frame();
  let tmp = Buffer.create (uint32_to_sint32 0ul) 10ul in
  let k'  = Buffer.sub tmp 0ul 8ul in
  let n'  = Buffer.sub tmp 8ul 2ul in
  uint32s_from_le_bytes k' k 8ul;
  uint32s_from_le_bytes n' n 2ul;
  let c0 = uint32_to_sint32 (FStar.Int.Cast.uint64_to_uint32 c) in
  let c1 = uint32_to_sint32 (FStar.Int.Cast.uint64_to_uint32 FStar.UInt64.(c >>^ 32ul)) in
  let k0 = k'.(0ul) in
  let k1 = k'.(1ul) in
  let k2 = k'.(2ul) in
  let k3 = k'.(3ul) in
  let k4 = k'.(4ul) in
  let k5 = k'.(5ul) in
  let k6 = k'.(6ul) in
  let k7 = k'.(7ul) in
  let n0 = n'.(0ul) in
  let n1 = n'.(1ul) in
  let h0 = ST.get() in
  upd_16  st (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0 c1
            (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3);
  let h = ST.get() in
  lemma_create_16 (as_seq h st) (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0 c1
            (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3);
  pop_frame()


let idx = a:U32.t{U32.v a < 16}

[@ "c_inline"]
val line:
  st:state ->
  a:idx -> b:idx -> d:idx -> s:U32.t{U32.v s < 32} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1 /\ live h0 st
      /\ (let st1 = reveal_h32s (as_seq h1 st) in
         let st0 = reveal_h32s (as_seq h0 st) in
         st1 == line (U32.v a) (U32.v b) (U32.v d) s st0)))
[@ "c_inline"]
let line st a b d s =
  let sa = st.(a) in let sb = st.(b) in let sd = st.(d) in
  let sbd = sb +%^ sd in
  let sbds = sbd <<< s in
  st.(a) <- (sa ^^ sbds)


[@ "c_inline"]
val quarter_round:
  st:state ->
  a:idx -> b:idx -> c:idx -> d:idx ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == quarter_round (U32.v a) (U32.v b) (U32.v c) (U32.v d) s)))
[@ "c_inline"]
let quarter_round st a b c d =
  line st b a d 7ul;
  line st c b a 9ul;
  line st d c b 13ul;
  line st a d c 18ul


[@ "substitute"]
val column_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == column_round s)))
[@ "substitute"]
let column_round st =
  quarter_round st 0ul  4ul  8ul  12ul;
  quarter_round st 5ul  9ul  13ul 1ul;
  quarter_round st 10ul 14ul 2ul  6ul;
  quarter_round st 15ul 3ul  7ul  11ul


[@ "substitute"]
val row_round:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == row_round s)))
[@ "substitute"]
let row_round st =
  quarter_round st 0ul  1ul   2ul  3ul;
  quarter_round st 5ul  6ul   7ul  4ul;
  quarter_round st 10ul 11ul 8ul  9ul;
  quarter_round st 15ul 12ul 13ul 14ul


[@ "c_inline"]
val double_round:
  st:buffer H32.t{length st = 16} ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == double_round s)))
[@ "c_inline"]
let double_round st =
    column_round st;
    row_round st



unfold let double_round' (b:Seq.seq H32.t{Seq.length b = 16}) : Tot (b':Seq.seq H32.t{Seq.length b' = Seq.length b /\ reveal_h32s b' == Spec.Salsa20.double_round (reveal_h32s b)}) =
  let f (s:Seq.seq U32.t{Seq.length s = 16}) : Tot (s':Seq.seq U32.t{Seq.length s' = 16}) = Spec.Salsa20.double_round s in
  lift_32 #(fun s -> Seq.length s = 16) f b


#reset-options "--initial_fuel 0 --max_fuel 1 --z3rlimit 100"

[@ "c_inline"]
val rounds:
  st:state ->
  Stack unit
    (requires (fun h -> live h st))
    (ensures (fun h0 _ h1 -> live h0 st /\ live h1 st /\ modifies_1 st h0 h1
      /\ (let s = reveal_h32s (as_seq h0 st) in let s' = reveal_h32s (as_seq h1 st) in
         s' == rounds s)))
[@ "c_inline"]
let rounds st =
  repeat #H32.t 16ul double_round' st 10ul double_round


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


[@ "c_inline"]
val sum_states:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures  (fun h0 _ h1 -> live h0 st /\ live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s1 = as_seq h1 st in let s = as_seq h0 st in let s' = as_seq h0 st' in
         s1 == seq_map2 (fun x y -> H32.(x +%^ y)) s s')))
[@ "c_inline"]
let sum_states st st' =
  in_place_map2 st st' 16ul (fun x y -> H32.(x +%^ y))


[@ "c_inline"]
val copy_state:
  st:state ->
  st':state{disjoint st st'} ->
  Stack unit
    (requires (fun h -> live h st /\ live h st'))
    (ensures (fun h0 _ h1 -> live h1 st /\ live h0 st' /\ modifies_1 st h0 h1
      /\ (let s = as_seq h0 st' in let s' = as_seq h1 st in s' == s)))
[@ "c_inline"]
let copy_state st st' =
  Buffer.blit st' 0ul st 0ul 16ul;
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h st) (Seq.slice (as_seq h st) 0 16);
  Seq.lemma_eq_intro (as_seq h st') (Seq.slice (as_seq h st') 0 16);
  Seq.lemma_eq_intro (as_seq h st) (as_seq h st')


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


type log_t_ = | MkLog: k:Spec.key -> n:Spec.nonce -> (* c:Spec.counter -> *) log_t_
type log_t = Ghost.erased log_t_


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

inline_for_extraction
let u64_of_u32s (low:U32.t) (high:U32.t) : Tot (x:UInt64.t{UInt64.v x = pow2 32 * UInt32.v high + UInt32.v low}) =
  let h = FStar.UInt64.(Int.Cast.uint32_to_uint64 high <<^ 32ul) in
  Math.Lemmas.modulo_lemma (UInt64.v h) (pow2 64);
  let l = (Int.Cast.uint32_to_uint64 low) in
  let c = UInt64.logor h l in
  UInt.logor_disjoint #64 (UInt64.v h) (UInt64.v l) 32;
  c


inline_for_extraction
let low32_of_u64 (x:UInt64.t) : Tot (y:UInt32.t{UInt32.v y = UInt64.v x % pow2 32}) =
  Int.Cast.uint64_to_uint32 x

inline_for_extraction
let high32_of_u64 (x:UInt64.t) : Tot (y:UInt32.t{UInt32.v y = UInt64.v x / pow2 32}) =
  let x' = FStar.UInt64.(x >>^ 32ul) in
  Math.Lemmas.lemma_div_lt (UInt64.v x) 64 32;
  Math.Lemmas.modulo_lemma (UInt64.v x / pow2 32) (pow2 32);
  Int.Cast.uint64_to_uint32 x'


(* Invariant on the state recording which block was computed last *)
let invariant (log:log_t) (h:mem) (st:state) : GTot Type0 =
  live h st /\ (let log = Ghost.reveal log in let s   = as_seq h st in
    match log with | MkLog key nonce -> reveal_h32s s == Spec.setup key nonce (UInt64.v (u64_of_u32s (h32_to_u32 (Seq.index s 8)) (h32_to_u32 (Seq.index s 9)))))


module H64 = Hacl.UInt64


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

private val lemma_invariant:
  st:Spec.state ->
  k:Spec.key -> n:Spec.nonce -> c:H64.t -> c':H64.t -> Lemma
    (requires (st == Spec.setup k n (H64.v c)))
    (ensures (let l = low32_of_u64 (h64_to_u64 c') in let h = high32_of_u64 (h64_to_u64 c') in
      Seq.upd (Seq.upd st 8 l) 9 h == Spec.setup k n (H64.v c')))
let lemma_invariant s k n c c' =
  let kk = k in
  let nn = n in
  let c = h64_to_u64 c in
  let c' = h64_to_u64 c' in
  let c0 = low32_of_u64 c in
  let c1 = high32_of_u64 c in
  let c0' = low32_of_u64 c' in
  let c1' = high32_of_u64 c' in
  let s' = intro_h32s (Seq.upd (Seq.upd s 8 c0') 9 c1') in
  let c0 = uint32_to_sint32 c0 in
  let c1 = uint32_to_sint32 c1 in
  let c0' = uint32_to_sint32 c0' in
  let c1' = uint32_to_sint32 c1' in
  let k = intro_h32s (Spec.Lib.uint32s_from_le 8 k) in
  let n = intro_h32s (Spec.Lib.uint32s_from_le 2 n) in
  let s = intro_h32s (s) in
  let k0 = Seq.index k 0 in
  let k1 = Seq.index k 1 in
  let k2 = Seq.index k 2 in
  let k3 = Seq.index k 3 in
  let k4 = Seq.index k 4 in
  let k5 = Seq.index k 5 in
  let k6 = Seq.index k 6 in
  let k7 = Seq.index k 7 in
  let n0 = Seq.index n 0 in
  let n1 = Seq.index n 1 in
  assert_norm(List.Tot.length [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] = 16);
  assert_norm(List.Tot.length [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] = 16);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 0 = (uint32_to_sint32 constant0));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 1 = k0);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 2 = k1);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 3 = k2);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 4 = k3);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 5 = (uint32_to_sint32 constant1));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 6 = n0);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 7 = n1);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 8 = c0);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 9 = c1);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 10 = (uint32_to_sint32 constant2));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 11 = k4);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 12 = k5);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 13 = k6);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 14 = k7);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 15 = (uint32_to_sint32 constant3));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 0 = (uint32_to_sint32 constant0));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 1 = k0);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 2 = k1);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 3 = k2);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 4 = k3);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 5 = (uint32_to_sint32 constant1));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 6 = n0);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 7 = n1);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 8 = c0');
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 9 = c1');
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 10 = (uint32_to_sint32 constant2));
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 11 = k4);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 12 = k5);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 13 = k6);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 14 = k7);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 15 = (uint32_to_sint32 constant3));
  lemma_seq_of_list [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)];
  cut (intro_h32s (Spec.Salsa20.setup kk nn (UInt64.v c)) == Seq.seq_of_list [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)]);
  cut (intro_h32s (Spec.Salsa20.setup kk nn (UInt64.v c')) == Seq.seq_of_list [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)]);
  lemma_seq_of_list [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)];
  lemma_create_16 s (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0 c1
            (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3);
  lemma_create_16 s' (uint32_to_sint32 constant0) k0 k1 k2 k3 (uint32_to_sint32 constant1) n0 n1 c0' c1'
            (uint32_to_sint32 constant2) k4 k5 k6 k7 (uint32_to_sint32 constant3);
  Seq.lemma_eq_intro s' (Seq.seq_of_list [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0'; c1'; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)])


private val lemma_state_counter:
  k:Spec.key -> n:Spec.nonce -> c:Spec.counter ->
  Lemma (U32.v (Seq.index (Spec.setup k n c) 8) == c % pow2 32 /\ U32.v (Seq.index (Spec.setup k n c) 9) == c / pow2 32)
let lemma_state_counter k n c =
  let c0 = low32_of_u64 (UInt64.uint_to_t c) in
  let c1 = high32_of_u64 (UInt64.uint_to_t c) in
  let c0 = uint32_to_sint32 c0 in
  let c1 = uint32_to_sint32 c1 in
  let s = Spec.setup k n c in
  let k = Spec.Lib.uint32s_from_le 8 k in
  let n = Spec.Lib.uint32s_from_le 2 n in
  let k = intro_h32s k in
  let n = intro_h32s n in
  let k0 = Seq.index k 0 in
  let k1 = Seq.index k 1 in
  let k2 = Seq.index k 2 in
  let k3 = Seq.index k 3 in
  let k4 = Seq.index k 4 in
  let k5 = Seq.index k 5 in
  let k6 = Seq.index k 6 in
  let k7 = Seq.index k 7 in
  let n0 = Seq.index n 0 in
  let n1 = Seq.index n 1 in
  assert_norm(List.Tot.length [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] = 16);
  lemma_seq_of_list [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)];
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 8 = c0);
  assert_norm(List.Tot.index [(uint32_to_sint32 constant0); k0; k1; k2; k3; (uint32_to_sint32 constant1); n0; n1; c0; c1; (uint32_to_sint32 constant2); k4; k5; k6; k7; (uint32_to_sint32 constant3)] 9 = c1)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private let lemma_u64_of_u32s (low:U32.t) (high:U32.t) : Lemma (low32_of_u64 (u64_of_u32s low high) = low /\ high32_of_u64 (u64_of_u32s low high) = high) =
  let low' = low32_of_u64 (u64_of_u32s low high) in
  cut (U32.v low' = (U32.v low + pow2 32 * U32.v high) % pow2 32);
  Math.Lemmas.lemma_mod_plus (U32.v low) (U32.v high) (pow2 32);
  Math.Lemmas.modulo_lemma (U32.v low) (pow2 32);
  cut (U32.v low' = U32.v low);
  Math.Lemmas.lemma_div_mod (UInt64.v (u64_of_u32s low high)) (pow2 32)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

[@ "c_inline"]
val salsa20_core:
  log:log_t ->
  k:state ->
  st:state{disjoint st k} ->
  ctr:UInt64.t ->
  Stack log_t
    (requires (fun h -> live h k /\ live h st /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h0 st /\ live h0 k /\ invariant log h0 st
      /\ live h1 k /\ invariant updated_log h1 st /\ modifies_2 k st h0 h1
      /\ (let key = reveal_h32s (as_seq h1 k) in
          let stv = reveal_h32s (as_seq h1 st) in
          Seq.index stv 12 == low32_of_u64 ctr /\
          Seq.index stv 13 == high32_of_u64 ctr /\
         (match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             key == salsa20_core stv /\ k == k' /\ n == n'))))
[@ "c_inline"]
let salsa20_core log k st ctr =
  let h0 = ST.get() in
  let c0 = uint32_to_sint32 (low32_of_u64 ctr) in
  let c1 = uint32_to_sint32 (high32_of_u64 ctr) in
  let h_1 = ST.get() in
  st.(8ul) <- c0;
  let h_ = ST.get() in
  cut (as_seq h_ st == Seq.upd (as_seq h_1 st) 8 (c0));
  st.(9ul) <- c1;
  let h_2 = ST.get() in
  cut (as_seq h_2 st == Seq.upd (as_seq h_ st) 9 (c1));
  cut (get h_2 st 8 == c0 /\ get h_2 st 9 == c1);
  cut (let s = as_seq h0 st in let s' = as_seq h_2 st in s' == Seq.upd (Seq.upd s 8 c0) 9 c1);
  lemma_invariant (reveal_h32s (as_seq h0 st)) (Ghost.reveal log).k (Ghost.reveal log).n (uint64_to_sint64 (u64_of_u32s (h32_to_u32 (get h0 st 8)) (h32_to_u32 (get h0 st 9)))) (uint64_to_sint64 ctr);
  lemma_u64_of_u32s (h32_to_u32 c0) (h32_to_u32 c1);
  cut (invariant log h_2 st);
  copy_state k st;
  rounds k;
  sum_states k st;
  let h_3 = ST.get() in
  let h = ST.get() in
  cut (reveal_h32s (as_seq h k) == salsa20_core (reveal_h32s (as_seq h st)));
  Ghost.elift1 (fun l -> match l with | MkLog k n -> MkLog k n) log


[@ "c_inline"]
val salsa20_block:
  log:log_t ->
  stream_block:uint8_p{length stream_block = 64} ->
  st:state{disjoint st stream_block} ->
  ctr:UInt64.t ->
  Stack log_t
    (requires (fun h -> live h stream_block /\ invariant log h st))
    (ensures  (fun h0 updated_log h1 -> live h1 stream_block /\ invariant log h0 st
      /\ invariant updated_log h1 st /\ modifies_2 stream_block st h0 h1
      /\ (let block = reveal_sbytes (as_seq h1 stream_block) in
         match Ghost.reveal log, Ghost.reveal updated_log with
         | MkLog k n, MkLog k' n' ->
             block == salsa20_block k n (UInt64.v ctr) /\ k == k' /\ n == n')))
[@ "c_inline"]
let salsa20_block log stream_block st ctr =
  let h0 = ST.get() in
  push_frame();
  let h_0 = ST.get() in
  let st' = Buffer.create (uint32_to_sint32 0ul) 16ul in
  let h_1 = ST.get() in
  no_upd_lemma_0 h_0 h_1 st;
  cut (as_seq h0 st == as_seq h_1 st);
  let log = salsa20_core log st' st ctr in
  let h_3 = ST.get() in
  uint32s_to_le_bytes stream_block st' 16ul;
  let h_4 = ST.get() in
  let h = ST.get() in
  cut (reveal_sbytes (as_seq h stream_block) == salsa20_block (Ghost.reveal log).k (Ghost.reveal log).n (UInt64.v ctr));
  cut (modifies_3_2 stream_block st h_0 h);
  pop_frame();
  log


[@ "c_inline"]
val alloc:
  unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures (fun h0 st h1 -> ~(live h0 st) /\ live h1 st /\ modifies_0 h0 h1 /\ frameOf st == h1.tip))
[@ "c_inline"]
let alloc () =
  create (uint32_to_sint32 0ul) 16ul


[@ "c_inline"]
val init:
  st:state ->
  k:uint8_p{length k = 32 /\ disjoint st k} ->
  n:uint8_p{length n = 8 /\ disjoint st n} ->
  Stack log_t
    (requires (fun h -> live h k /\ live h n /\ live h st))
    (ensures  (fun h0 log h1 -> live h1 st /\ live h0 k /\ live h0 n /\ modifies_1 st h0 h1
      /\ invariant log h1 st
      /\ (match Ghost.reveal log with MkLog k' n' -> k' == reveal_sbytes (as_seq h0 k)
          /\ n' == reveal_sbytes (as_seq h0 n))))
[@ "c_inline"]
let init st k n =
  let h0 = ST.get() in
  setup st k n 0uL;
  let h = ST.get() in
  lemma_state_counter (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) 0;
  cut (reveal_h32s (as_seq h st) == Spec.setup (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) 0);
  Ghost.elift2 (fun (k:uint8_p{length k = 32 /\ live h k}) (n:uint8_p{length n = 8 /\ live h n}) -> MkLog (reveal_sbytes (as_seq h k)) (reveal_sbytes (as_seq h n))) (Ghost.hide k) (Ghost.hide n)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_salsa20_counter_mode_1:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len <= 64 /\ U32.v len > 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr + (length input / 64) < pow2 64} -> Lemma
    (Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes (as_seq hi input))
     == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y))
                             (reveal_sbytes (as_seq hi input))
                             (Seq.slice (Spec.salsa20_block k n (UInt64.v ctr)) 0 (U32.v len)))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_salsa20_counter_mode_1 ho output hi input len k n ctr = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_salsa20_counter_mode_2:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len > 64} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr + (length input / 64) < pow2 64} -> Lemma
    (Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes (as_seq hi input))
     == (let b, plain = Seq.split (reveal_sbytes (as_seq hi input)) 64 in
         let mask = Spec.salsa20_block k n (UInt64.v ctr) in
         let eb = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) b mask in
         let cipher = Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr + 1) plain in
         Seq.append eb cipher))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_salsa20_counter_mode_2 ho output hi input len k n ctr = ()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val lemma_salsa20_counter_mode_0:
  ho:mem -> output:uint8_p{live ho output} ->
  hi:mem -> input:uint8_p{live hi input} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length input /\ U32.v len = 0} ->
  k:Spec.key -> n:Spec.nonce -> ctr:UInt64.t{UInt64.v ctr + (length input / 64) < pow2 64} -> Lemma
    (Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) (reveal_sbytes (as_seq hi input))
     == reveal_sbytes (as_seq ho output))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100"
let lemma_salsa20_counter_mode_0 ho output hi input len k n ctr =
  Seq.lemma_eq_intro (as_seq ho output) Seq.createEmpty


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val update_last:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 64 /\ U32.v len > 0} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) plain)))
let update_last output plain len log st ctr =
  let h0 = ST.get() in
  push_frame();
  let block = create (uint8_to_sint8 0uy) 64ul in
  let l = salsa20_block log block st ctr in
  let mask = Buffer.sub block 0ul len in
  map2 output plain mask len (fun x y -> H8.(x ^^ y));
  let h1 = ST.get() in
  lemma_salsa20_counter_mode_1 h1 output h0 plain len (Ghost.reveal log).k (Ghost.reveal log).n ctr;
  pop_frame();
  l


val update:
  output:uint8_p{length output = 64} ->
  plain:uint8_p{disjoint output plain /\ length plain = 64} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + 1 < pow2 64} ->
  Stack log_t
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 updated_log h1 -> live h1 output /\ live h0 plain /\ invariant updated_log h1 st
      /\ modifies_2 output st h0 h1
      /\ updated_log == log
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) plain (salsa20_cipher k n (UInt64.v ctr)))))
let update output plain log st ctr =
  let h0 = ST.get() in
  push_frame();
  let k = create (uint32_to_sint32 0ul) 16ul in
  let l = salsa20_core log k st ctr in
  let ib = create (uint32_to_sint32 0ul) 16ul in
  let ob = create (uint32_to_sint32 0ul) 16ul in
  uint32s_from_le_bytes ib plain 16ul;
  map2 ob ib k 16ul (fun x y -> H32.(x ^^ y));
  uint32s_to_le_bytes output ob 16ul;
  pop_frame();
  l


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"


val lemma_salsa20_counter_mode:
  h0:mem -> h1:mem -> h2:mem ->
  output:uint8_p{live h1 output /\ live h2 output /\ live h0 output} ->
  plain:uint8_p{live h0 plain /\ live h1 plain /\ live h2 plain} ->
  len:UInt32.t{length output = U32.v len /\ length output = length plain /\ U32.v len > 64} ->
  k:Spec.key -> n:Spec.nonce -> ctr:Spec.counter{ctr + U32.v len / 64 < pow2 64} ->
  Lemma (requires (
    (let o = reveal_sbytes (as_seq h2 (Buffer.sub output 0ul 64ul)) in
     let p = reveal_sbytes (as_seq h0 (Buffer.sub plain 0ul 64ul)) in
     let o' = reveal_sbytes (as_seq h2 (Buffer.offset output 64ul)) in
     let p' = reveal_sbytes (as_seq h0 (Buffer.offset plain 64ul)) in
     o == seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) p (salsa20_cipher k n (ctr))
     /\ o' == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (ctr + 1) p')))
     (ensures (
       (let o = reveal_sbytes (as_seq h2 output) in
        let plain = reveal_sbytes (as_seq h0 plain) in
        o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (ctr) plain)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"
let lemma_salsa20_counter_mode h0 h1 h2 output plain len k n ctr =
  cut (ctr + 1 < pow2 64);
  Seq.lemma_eq_intro (as_seq h2 (Buffer.sub output 0ul 64ul)) (Seq.slice (as_seq h2 output) 0 64);
  Seq.lemma_eq_intro (as_seq h0 (Buffer.sub plain 0ul 64ul)) (Seq.slice (as_seq h0 plain) 0 64);
  Seq.lemma_eq_intro (as_seq h2 (Buffer.offset output 64ul)) (Seq.slice (as_seq h2 output) 64 (length output));
  Seq.lemma_eq_intro (as_seq h0 (Buffer.offset plain 64ul)) (Seq.slice (as_seq h0 plain) 64 (length output));
  let b, plainn = Seq.split (reveal_sbytes (as_seq h0 plain)) 64 in
  Seq.lemma_eq_intro b (reveal_sbytes (as_seq h0 (Buffer.sub plain 0ul 64ul)));
  Seq.lemma_eq_intro plainn (reveal_sbytes (as_seq h0 (Buffer.offset plain 64ul)));
  let mask = Spec.salsa20_block k n (ctr) in
  let eb = seq_map2 (fun x y -> FStar.UInt8.(x ^^ y)) b mask in
  Seq.lemma_eq_intro eb (reveal_sbytes (as_seq h2 (Buffer.sub output 0ul 64ul)));
  let cipher = Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (ctr + 1) plainn in
  Seq.lemma_eq_intro cipher (reveal_sbytes (as_seq h2 (Buffer.offset output 64ul)));
  Seq.lemma_eq_intro (Seq.append eb cipher) (reveal_sbytes (as_seq h2 output));
  lemma_salsa20_counter_mode_2 h2 output h0 plain len k n (UInt64.uint_to_t ctr)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val salsa20_counter_mode_:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain /\ U32.v len <= 64} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) plain)))
let rec salsa20_counter_mode_ output plain len log st ctr =
  let h0 = ST.get() in
  if U32.(len =^ 0ul) then (
    lemma_salsa20_counter_mode_0 h0 output h0 plain len (Ghost.reveal log).k (Ghost.reveal log).n ctr;
    Seq.lemma_eq_intro (as_seq h0 output) Seq.createEmpty
  ) else  (
    let _ = update_last output plain len log st ctr in ()
  )

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val salsa20_counter_mode:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  log:log_t ->
  st:state{disjoint st output /\ disjoint st plain} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ invariant log h st))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h1 st
      /\ modifies_2 output st h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         match Ghost.reveal log with | MkLog k n ->
         o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n (UInt64.v ctr) plain)))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"
let rec salsa20_counter_mode output plain len log st ctr =
  let h0 = ST.get() in
  if U32.(len <=^ 64ul) then salsa20_counter_mode_ output plain len log st ctr
  else (
    let b  = Buffer.sub plain 0ul 64ul in
    let b' = Buffer.offset plain 64ul in
    let o  = Buffer.sub output 0ul 64ul in
    let o' = Buffer.offset output 64ul in
    let log' = update o b log st ctr in
    let h = ST.get() in
    let l = salsa20_counter_mode o' b' U32.(len -^ 64ul) log st FStar.UInt64.(ctr +^ 1uL) in
    let h' = ST.get() in
    cut (let o' = reveal_sbytes (as_seq h' o') in
         let b' = reveal_sbytes (as_seq h b')  in
         o' == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher
                                               (Ghost.reveal log).k (Ghost.reveal log).n
                                               (UInt64.v ctr + 1) (b'));
    no_upd_lemma_2 h0 h o st b;
    no_upd_lemma_2 h0 h o st b';
    no_upd_lemma_2 h0 h o st o';
    no_upd_lemma_2 h h' o' st b;
    no_upd_lemma_2 h h' o'  st b';
    no_upd_lemma_2 h h' o' st o;
    lemma_salsa20_counter_mode h0 h h' output plain len (Ghost.reveal log).k (Ghost.reveal log).n (UInt64.v ctr)
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val salsa20:
  output:uint8_p ->
  plain:uint8_p{disjoint output plain} ->
  len:U32.t{U32.v len = length output /\ U32.v len = length plain} ->
  key:uint8_p{length key = 32} ->
  nonce:uint8_p{length nonce = 8} ->
  ctr:UInt64.t{UInt64.v ctr + (length plain / 64) < pow2 64} ->
  Stack unit
    (requires (fun h -> live h output /\ live h plain /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h0 plain /\ live h0 key /\ live h0 nonce
      /\ modifies_1 output h0 h1
      /\ (let o = reveal_sbytes (as_seq h1 output) in
         let plain = reveal_sbytes (as_seq h0 plain) in
         let k = reveal_sbytes (as_seq h0 key) in
         let n = reveal_sbytes (as_seq h0 nonce) in
         let ctr = UInt64.v ctr in
         o == Spec.CTR.counter_mode salsa20_ctx salsa20_cipher k n ctr plain)))
let salsa20 output plain len k n ctr =
  push_frame();
  let st = alloc () in
  let l  = init st k n in
  let l' = salsa20_counter_mode output plain len l st ctr in
  pop_frame()
