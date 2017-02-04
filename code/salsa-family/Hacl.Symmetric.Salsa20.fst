module Hacl.Symmetric.Salsa20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast


let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t


#reset-options "--initial_fuel 0 --max_fuel 0"

private val lemma_max_uint32: n:nat -> Lemma
  (requires (n = 32))
  (ensures  (pow2 n = 4294967296))
  [SMTPat (pow2 n)]
private let lemma_max_uint32 n = assert_norm(pow2 32 = 4294967296)
private val lemma_max_uint64: n:nat -> Lemma
  (requires (n = 64))
  (ensures  (pow2 n = 18446744073709551616))
  [SMTPat (pow2 n)]
private let lemma_max_uint64 n = assert_norm(pow2 64 = 18446744073709551616)

[@"c_inline"]
private let rol32 (a:h32) (s:u32{FStar.UInt32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

[@"c_inline"]
private inline_for_extraction let load32_le (k:uint8_p) : Stack h32
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> h0 == h1))
  = C.load32_le k 

[@"c_inline"]
private inline_for_extraction let store32_le (k:uint8_p) (x:h32) : Stack unit
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\ live h1 k))
  = C.store32_le k x

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"

[@"c_inline"]
private inline_for_extraction val crypto_core_salsa20_quarter_round:
  ctx:buffer u32{length ctx = 16} ->
  a:u32 -> b:u32 -> c:u32 -> d:u32 ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let crypto_core_salsa20_quarter_round ctx a b c d =
  let y0 = ctx.(a) in
  let y1 = ctx.(b) in
  let y2 = ctx.(c) in
  let y3 = ctx.(d) in
  let y1 = y1 ^^ (rol32 (y0+%^y3)  7ul) in
  let y2 = y2 ^^ (rol32 (y1+%^y0)  9ul) in
  let y3 = y3 ^^ (rol32 (y2+%^y1)  13ul) in
  let y0 = y0 ^^ (rol32 (y3+%^y2)  18ul) in
  ctx.(a) <- y0;
  ctx.(b) <- y1;
  ctx.(c) <- y2;
  ctx.(d) <- y3

[@"c_inline"]
private inline_for_extraction val crypto_core_salsa20_row_round:
  ctx:buffer u32{length ctx = 16} ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let crypto_core_salsa20_row_round ctx =
  crypto_core_salsa20_quarter_round ctx 0ul 1ul 2ul 3ul;
  crypto_core_salsa20_quarter_round ctx 5ul 6ul 7ul 4ul;
  crypto_core_salsa20_quarter_round ctx 10ul 11ul 8ul 9ul;
  crypto_core_salsa20_quarter_round ctx 15ul 12ul 13ul 14ul


[@"c_inline"]
private inline_for_extraction val crypto_core_salsa20_column_round:
  ctx:buffer u32{length ctx = 16} ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let crypto_core_salsa20_column_round ctx =
  crypto_core_salsa20_quarter_round ctx 0ul 4ul 8ul 12ul;
  crypto_core_salsa20_quarter_round ctx 5ul 9ul 13ul 1ul;
  crypto_core_salsa20_quarter_round ctx 10ul 14ul 2ul 6ul;
  crypto_core_salsa20_quarter_round ctx 15ul 3ul 7ul 11ul

private val crypto_core_salsa20_double_round_10:
  ctx:buffer u32{length ctx = 16} ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
private let crypto_core_salsa20_double_round_10 ctx =
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx;
  crypto_core_salsa20_column_round ctx;
  crypto_core_salsa20_row_round ctx


private val crypto_core_salsa20:
  output:uint8_p{length output = 64} ->
  input :uint8_p{length input = 16} ->
  key   :uint8_p{length key = 32} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
private let crypto_core_salsa20 output input key =
  push_frame();
  let ctx = create 0ul 16ul in 
  ctx.(0ul)  <- uint32_to_sint32 0x61707865ul;
  ctx.(5ul)  <- uint32_to_sint32 0x3320646eul;
  ctx.(10ul) <- uint32_to_sint32 0x79622d32ul;
  ctx.(15ul) <- uint32_to_sint32 0x6b206574ul;
  ctx.(1ul)  <- load32_le(offset key 0ul);
  ctx.(2ul)  <- load32_le(offset key 4ul);
  ctx.(3ul)  <- load32_le(offset key 8ul);
  ctx.(4ul)  <- load32_le(offset key 12ul);
  ctx.(11ul) <- load32_le(offset key 16ul);
  ctx.(12ul) <- load32_le(offset key 20ul);
  ctx.(13ul) <- load32_le(offset key 24ul);
  ctx.(14ul) <- load32_le(offset key 28ul);
  ctx.(6ul)  <- load32_le(offset input 0ul);
  ctx.(7ul)  <- load32_le(offset input 4ul);
  ctx.(8ul)  <- load32_le(offset input 8ul);
  ctx.(9ul)  <- load32_le(offset input 12ul);
  let j0 = ctx.(0ul) in
  let j1 = ctx.(1ul) in
  let j2 = ctx.(2ul) in
  let j3 = ctx.(3ul) in
  let j4 = ctx.(4ul) in
  let j5 = ctx.(5ul) in
  let j6 = ctx.(6ul) in
  let j7 = ctx.(7ul) in
  let j8 = ctx.(8ul) in
  let j9 = ctx.(9ul) in
  let j10 = ctx.(10ul) in
  let j11 = ctx.(11ul) in
  let j12 = ctx.(12ul) in
  let j13 = ctx.(13ul) in
  let j14 = ctx.(14ul) in
  let j15 = ctx.(15ul) in
  (* *)
  crypto_core_salsa20_double_round_10 ctx;
  (* *)
  let x0 = ctx.(0ul) in
  let x1 = ctx.(1ul) in
  let x2 = ctx.(2ul) in
  let x3 = ctx.(3ul) in
  let x4 = ctx.(4ul) in
  let x5 = ctx.(5ul) in
  let x6 = ctx.(6ul) in
  let x7 = ctx.(7ul) in
  let x8 = ctx.(8ul) in
  let x9 = ctx.(9ul) in
  let x10 = ctx.(10ul) in
  let x11 = ctx.(11ul) in
  let x12 = ctx.(12ul) in
  let x13 = ctx.(13ul) in
  let x14 = ctx.(14ul) in
  let x15 = ctx.(15ul) in
  let x0 = x0 +%^ j0 in
  let x1 = x1 +%^ j1 in
  let x2 = x2 +%^ j2 in
  let x3 = x3 +%^ j3 in
  let x4 = x4 +%^ j4 in
  let x5 = x5 +%^ j5 in
  let x6 = x6 +%^ j6 in
  let x7 = x7 +%^ j7 in
  let x8 = x8 +%^ j8 in
  let x9 = x9 +%^ j9 in
  let x10 = x10 +%^ j10 in
  let x11 = x11 +%^ j11 in
  let x12 = x12 +%^ j12 in
  let x13 = x13 +%^ j13 in
  let x14 = x14 +%^ j14 in
  let x15 = x15 +%^ j15 in
  store32_le (offset output 0ul) x0;
  store32_le (offset output 4ul) x1;
  store32_le (offset output 8ul) x2;
  store32_le (offset output 12ul) x3;
  store32_le (offset output 16ul) x4;
  store32_le (offset output 20ul) x5;
  store32_le (offset output 24ul) x6;
  store32_le (offset output 28ul) x7;
  store32_le (offset output 32ul) x8;
  store32_le (offset output 36ul) x9;
  store32_le (offset output 40ul) x10;
  store32_le (offset output 44ul) x11;
  store32_le (offset output 48ul) x12;
  store32_le (offset output 52ul) x13;
  store32_le (offset output 56ul) x14;
  store32_le (offset output 60ul) x15;
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

module U64 = FStar.UInt64
module U32 = FStar.UInt32


[@"c_inline"]
private val xor_:
  c:uint8_p{length c >= 64} ->
  m:uint8_p{length m >= 64} ->
  block:uint8_p{length block = 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h block))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@"c_inline"]
private let xor_ c m block =
  let open Hacl.UInt128 in
  let m0 = C.load128(offset m 0ul) in
  let m1 = C.load128(offset m 16ul) in
  let m2 = C.load128(offset m 32ul) in
  let m3 = C.load128(offset m 48ul) in
  let b0 = C.load128(offset block 0ul) in
  let b1 = C.load128(offset block 16ul) in
  let b2 = C.load128(offset block 32ul) in
  let b3 = C.load128(offset block 48ul) in
  let c0 = FStar.UInt128.(m0 ^^ b0) in
  let c1 = FStar.UInt128.(m1 ^^ b1) in
  let c2 = FStar.UInt128.(m2 ^^ b2) in
  let c3 = FStar.UInt128.(m3 ^^ b3) in
  C.store128 (offset c 0ul ) c0; 
  C.store128 (offset c 16ul) c1; 
  C.store128 (offset c 32ul) c2;
  C.store128 (offset c 48ul) c3

(*
  let open Hacl.UInt8 in
  let m0 = m.(0ul) in let block0 = block.(0ul) in
  let m1 = m.(1ul) in let block1 = block.(1ul) in
  let m2 = m.(2ul) in let block2 = block.(2ul) in
  let m3 = m.(3ul) in let block3 = block.(3ul) in
  let m4 = m.(4ul) in let block4 = block.(4ul) in
  let m5 = m.(5ul) in let block5 = block.(5ul) in
  let m6 = m.(6ul) in let block6 = block.(6ul) in
  let m7 = m.(7ul) in let block7 = block.(7ul) in
  let m8 = m.(8ul) in let block8 = block.(8ul) in
  let m9 = m.(9ul) in let block9 = block.(9ul) in
  let m10 = m.(10ul) in let block10 = block.(10ul) in
  let m11 = m.(11ul) in let block11 = block.(11ul) in
  let m12 = m.(12ul) in let block12 = block.(12ul) in
  let m13 = m.(13ul) in let block13 = block.(13ul) in
  let m14 = m.(14ul) in let block14 = block.(14ul) in
  let m15 = m.(15ul) in let block15 = block.(15ul) in
  let m16 = m.(16ul) in let block16 = block.(16ul) in
  let m17 = m.(17ul) in let block17 = block.(17ul) in
  let m18 = m.(18ul) in let block18 = block.(18ul) in
  let m19 = m.(19ul) in let block19 = block.(19ul) in
  let m20 = m.(20ul) in let block20 = block.(20ul) in
  let m21 = m.(21ul) in let block21 = block.(21ul) in
  let m22 = m.(22ul) in let block22 = block.(22ul) in
  let m23 = m.(23ul) in let block23 = block.(23ul) in
  let m24 = m.(24ul) in let block24 = block.(24ul) in
  let m25 = m.(25ul) in let block25 = block.(25ul) in
  let m26 = m.(26ul) in let block26 = block.(26ul) in
  let m27 = m.(27ul) in let block27 = block.(27ul) in
  let m28 = m.(28ul) in let block28 = block.(28ul) in
  let m29 = m.(29ul) in let block29 = block.(29ul) in
  let m30 = m.(30ul) in let block30 = block.(30ul) in
  let m31 = m.(31ul) in let block31 = block.(31ul) in
  let m32 = m.(32ul) in let block32 = block.(32ul) in
  let m33 = m.(33ul) in let block33 = block.(33ul) in
  let m34 = m.(34ul) in let block34 = block.(34ul) in
  let m35 = m.(35ul) in let block35 = block.(35ul) in
  let m36 = m.(36ul) in let block36 = block.(36ul) in
  let m37 = m.(37ul) in let block37 = block.(37ul) in
  let m38 = m.(38ul) in let block38 = block.(38ul) in
  let m39 = m.(39ul) in let block39 = block.(39ul) in
  let m40 = m.(40ul) in let block40 = block.(40ul) in
  let m41 = m.(41ul) in let block41 = block.(41ul) in
  let m42 = m.(42ul) in let block42 = block.(42ul) in
  let m43 = m.(43ul) in let block43 = block.(43ul) in
  let m44 = m.(44ul) in let block44 = block.(44ul) in
  let m45 = m.(45ul) in let block45 = block.(45ul) in
  let m46 = m.(46ul) in let block46 = block.(46ul) in
  let m47 = m.(47ul) in let block47 = block.(47ul) in
  let m48 = m.(48ul) in let block48 = block.(48ul) in
  let m49 = m.(49ul) in let block49 = block.(49ul) in
  let m50 = m.(50ul) in let block50 = block.(50ul) in
  let m51 = m.(51ul) in let block51 = block.(51ul) in
  let m52 = m.(52ul) in let block52 = block.(52ul) in
  let m53 = m.(53ul) in let block53 = block.(53ul) in
  let m54 = m.(54ul) in let block54 = block.(54ul) in
  let m55 = m.(55ul) in let block55 = block.(55ul) in
  let m56 = m.(56ul) in let block56 = block.(56ul) in
  let m57 = m.(57ul) in let block57 = block.(57ul) in
  let m58 = m.(58ul) in let block58 = block.(58ul) in
  let m59 = m.(59ul) in let block59 = block.(59ul) in
  let m60 = m.(60ul) in let block60 = block.(60ul) in
  let m61 = m.(61ul) in let block61 = block.(61ul) in
  let m62 = m.(62ul) in let block62 = block.(62ul) in
  let m63 = m.(63ul) in let block63 = block.(63ul) in
  c.(0ul) <- m0 ^^ block0;
  c.(1ul) <- m1 ^^ block1;
  c.(2ul) <- m2 ^^ block2;
  c.(3ul) <- m3 ^^ block3;
  c.(4ul) <- m4 ^^ block4;
  c.(5ul) <- m5 ^^ block5;
  c.(6ul) <- m6 ^^ block6;
  c.(7ul) <- m7 ^^ block7;
  c.(8ul) <- m8 ^^ block8;
  c.(9ul) <- m9 ^^ block9;
  c.(10ul) <- m10 ^^ block10;
  c.(11ul) <- m11 ^^ block11;
  c.(12ul) <- m12 ^^ block12;
  c.(13ul) <- m13 ^^ block13;
  c.(14ul) <- m14 ^^ block14;
  c.(15ul) <- m15 ^^ block15;
  c.(16ul) <- m16 ^^ block16;
  c.(17ul) <- m17 ^^ block17;
  c.(18ul) <- m18 ^^ block18;
  c.(19ul) <- m19 ^^ block19;
  c.(20ul) <- m20 ^^ block20;
  c.(21ul) <- m21 ^^ block21;
  c.(22ul) <- m22 ^^ block22;
  c.(23ul) <- m23 ^^ block23;
  c.(24ul) <- m24 ^^ block24;
  c.(25ul) <- m25 ^^ block25;
  c.(26ul) <- m26 ^^ block26;
  c.(27ul) <- m27 ^^ block27;
  c.(28ul) <- m28 ^^ block28;
  c.(29ul) <- m29 ^^ block29;
  c.(30ul) <- m30 ^^ block30;
  c.(31ul) <- m31 ^^ block31;
  c.(32ul) <- m32 ^^ block32;
  c.(33ul) <- m33 ^^ block33;
  c.(34ul) <- m34 ^^ block34;
  c.(35ul) <- m35 ^^ block35;
  c.(36ul) <- m36 ^^ block36;
  c.(37ul) <- m37 ^^ block37;
  c.(38ul) <- m38 ^^ block38;
  c.(39ul) <- m39 ^^ block39;
  c.(40ul) <- m40 ^^ block40;
  c.(41ul) <- m41 ^^ block41;
  c.(42ul) <- m42 ^^ block42;
  c.(43ul) <- m43 ^^ block43;
  c.(44ul) <- m44 ^^ block44;
  c.(45ul) <- m45 ^^ block45;
  c.(46ul) <- m46 ^^ block46;
  c.(47ul) <- m47 ^^ block47;
  c.(48ul) <- m48 ^^ block48;
  c.(49ul) <- m49 ^^ block49;
  c.(50ul) <- m50 ^^ block50;
  c.(51ul) <- m51 ^^ block51;
  c.(52ul) <- m52 ^^ block52;
  c.(53ul) <- m53 ^^ block53;
  c.(54ul) <- m54 ^^ block54;
  c.(55ul) <- m55 ^^ block55;
  c.(56ul) <- m56 ^^ block56;
  c.(57ul) <- m57 ^^ block57;
  c.(58ul) <- m58 ^^ block58;
  c.(59ul) <- m59 ^^ block59;
  c.(60ul) <- m60 ^^ block60;
  c.(61ul) <- m61 ^^ block61;
  c.(62ul) <- m62 ^^ block62;
  c.(63ul) <- m63 ^^ block63
*)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private let lemma_modifies_3 (c:uint8_p) (input:uint8_p) (block:uint8_p) h0 h1 h2 : Lemma
  (requires (live h0 c /\ live h0 input /\ live h0 block
    /\ live h1 c /\ live h1 input /\ live h1 block
    /\ live h2 c /\ live h2 input /\ live h2 block
    /\ modifies_2 c block h0 h1 /\ modifies_1 input h1 h2))
  (ensures (modifies_3 c input block h0 h2))
  = lemma_reveal_modifies_2 c block h0 h1;
    lemma_reveal_modifies_1 input h1 h2;
    lemma_intro_modifies_3 c input block h0 h2


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private let lemma_modifies_3' (c:uint8_p) (input:uint8_p) (block:uint8_p) h0 h1 h2 : Lemma
  (requires (live h0 c /\ live h0 input /\ live h0 block
    /\ live h1 c /\ live h1 input /\ live h1 block
    /\ live h2 c /\ live h2 input /\ live h2 block
    /\ length c >= 64 /\ modifies_3 c input block h0 h1
    /\ modifies_3 (offset c 64ul) input block h1 h2))
  (ensures (modifies_3 c input block h0 h2))
  = lemma_reveal_modifies_3 c input block h0 h1;
    lemma_reveal_modifies_3 (offset c 64ul) input block h1 h2;
    lemma_intro_modifies_3 c input block h0 h2


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

[@"c_inline"]
private val crypto_stream_salsa20_xor_ic_loop:
  c:uint8_p ->
  m:uint8_p ->
  block:uint8_p{length block = 64 /\ disjoint block c} ->
  input:uint8_p{length input = 16 /\ disjoint input block /\ disjoint input c} ->
  kcopy:uint8_p{length kcopy = 32 /\ disjoint kcopy block} ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  Stack (z:FStar.UInt64.t{FStar.UInt64.v z < 64})
    (requires (fun h -> live h c /\ live h m /\ live h block /\ live h input /\ live h kcopy))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 input /\ live h1 block /\ modifies_3 c input block h0 h1))
[@"c_inline"]
private let rec crypto_stream_salsa20_xor_ic_loop c m block input kcopy mlen =
  if (FStar.UInt64.(mlen <^ 64uL)) then (
    let h = ST.get() in
    lemma_intro_modifies_3 c input block h h;
    mlen )
  else (
    let h0 = ST.get() in
    let open Hacl.UInt8 in
    crypto_core_salsa20 block input kcopy;
    let h1 = ST.get() in cut (modifies_1 block h0 h1);
    xor_ c m block;
    let h2 = ST.get() in
    (* *)
    let i8 = input.(8ul) in
    let i9 = input.(9ul) in
    let i10 = input.(10ul) in
    let i11 = input.(11ul) in
    let i12 = input.(12ul) in
    let i13 = input.(13ul) in
    let i14 = input.(14ul) in
    let i15 = input.(15ul) in
    (* *)
    let u = Hacl.UInt64.(
      sint8_to_sint64 i8
      +%^ (sint8_to_sint64 i9 <<^ 8ul)
      +%^ (sint8_to_sint64 i10 <<^ 16ul)
      +%^ (sint8_to_sint64 i11 <<^ 24ul)
      +%^ (sint8_to_sint64 i12 <<^ 32ul)
      +%^ (sint8_to_sint64 i13 <<^ 40ul)
      +%^ (sint8_to_sint64 i14 <<^ 48ul)
      +%^ (sint8_to_sint64 i15 <<^ 56ul)
      +%^ (uint64_to_sint64 1uL)
    ) in
    (* *)
    cut (modifies_2 c block h0 h2);
    input.(8ul)  <- sint64_to_sint8 u;
    input.(9ul)  <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 8ul));
    input.(10ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 16ul));
    input.(11ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 24ul));
    input.(12ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 32ul));
    input.(13ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 40ul));
    input.(14ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 48ul));
    input.(15ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 56ul));
    (* *)
    let h3 = ST.get() in
    lemma_modifies_3 c input block h0 h2 h3;
    let mlen = FStar.UInt64.(mlen -^ 64uL) in
    let c' = offset c 64ul in
    let m = offset m 64ul in
    (* *)
    let res = crypto_stream_salsa20_xor_ic_loop c' m block input kcopy mlen in
    let h4 = ST.get() in
    lemma_modifies_3' c input block h0 h3 h4;
    res
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

[@"c_inline"]
private val xor_bytes:
  x:uint8_p ->
  y:uint8_p ->
  z:uint8_p ->
  len:FStar.UInt32.t{let l = U32.v len in length x >= l /\ length y >= l /\ length z >= l} ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h z))
    (ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))
[@"c_inline"]
private let rec xor_bytes x y z len =
  if FStar.UInt32.(len =^ 0ul) then ()
  else (
    let i = FStar.UInt32.(len -^ 1ul) in
    let yi = y.(i) in let zi = z.(i) in
    x.(i) <- Hacl.UInt8.(yi ^^ zi);
    xor_bytes x y z i
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

private inline_for_extraction let mod_64 (mlen:U64.t) : Tot (z:U32.t{U32.v z = U64.v mlen % 64 /\ U32.v z <= U64.v mlen}) =
  let mlen' = U64.(mlen &^ 63uL) in
  UInt.logand_mask (U64.v mlen) 6;
  assert_norm (pow2 6 = 64);
  Math.Lemmas.euclidean_division_definition (U64.v mlen) 64;
  Math.Lemmas.nat_over_pos_is_nat (U64.v mlen) 64;
  Math.Lemmas.nat_times_nat_is_nat (U64.v mlen / 64) 64;
  cut (U64.(v mlen >= v mlen'));
  Math.Lemmas.modulo_lemma (U64.v mlen') (pow2 32);
  Int.Cast.uint64_to_uint32 mlen'


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

private let lemma_modifies_3_1 (c:uint8_p) (input:uint8_p) (block:uint8_p) h0 h1 h2 h3 : Lemma
  (requires (live h0 c /\ ~(contains h0 input) /\ ~(contains h0 block)
    /\ live h1 c /\ live h1 input /\ live h1 block
    /\ live h2 c /\ live h2 input /\ live h2 block
    /\ live h3 c /\ live h3 input /\ live h3 block
    /\ modifies_0 h0 h1 /\ modifies_3 c input block h1 h2 /\ modifies_2 c block h2 h3))
  (ensures (modifies_2_1 c h0 h3))
  = lemma_reveal_modifies_0 h0 h1;
    lemma_reveal_modifies_3 c input block h1 h2;
    lemma_reveal_modifies_2 c block h2 h3;
    lemma_intro_modifies_2_1 c h0 h3


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

[@"c_inline"]
private inline_for_extraction val crypto_stream_salsa20_xor_ic__:
  n:uint8_p{length n = 8} ->
  ic:FStar.UInt64.t ->
  k:uint8_p{length k = 32} ->
  local_state:uint8_p{length local_state = 112} ->
  Stack unit
    (requires (fun h -> live h n /\ live h k /\ live h local_state))
    (ensures  (fun h0 _ h1 -> live h1 local_state /\ modifies_1 local_state h0 h1))
[@"c_inline"]
private inline_for_extraction let crypto_stream_salsa20_xor_ic__ n ic k local_state =
  let input = Buffer.sub local_state 0ul  16ul in
  let block = Buffer.sub local_state 16ul 64ul in
  let kcopy = Buffer.sub local_state 80ul 32ul in
  let k0 = k.(0ul) in let k1 = k.(1ul) in let k2 = k.(2ul) in let k3 = k.(3ul) in
  let k4 = k.(4ul) in let k5 = k.(5ul) in let k6 = k.(6ul) in let k7 = k.(7ul) in
  let k8 = k.(8ul) in let k9 = k.(9ul) in let k10 = k.(10ul) in let k11 = k.(11ul) in
  let k12 = k.(12ul) in let k13 = k.(13ul) in let k14 = k.(14ul) in let k15 = k.(15ul) in
  let k16 = k.(16ul) in let k17 = k.(17ul) in let k18 = k.(18ul) in let k19 = k.(19ul) in
  let k20 = k.(20ul) in let k21 = k.(21ul) in let k22 = k.(22ul) in let k23 = k.(23ul) in
  let k24 = k.(24ul) in let k25 = k.(25ul) in let k26 = k.(26ul) in let k27 = k.(27ul) in
  let k28 = k.(28ul) in let k29 = k.(29ul) in let k30 = k.(30ul) in let k31 = k.(31ul) in
  let n0 = n.(0ul) in let n1 = n.(1ul) in let n2 = n.(2ul) in let n3 = n.(3ul) in
  let n4 = n.(4ul) in let n5 = n.(5ul) in let n6 = n.(6ul) in let n7 = n.(7ul) in
  kcopy.(0ul) <- k0;   kcopy.(1ul) <- k1;
  kcopy.(2ul) <- k2;   kcopy.(3ul) <- k3;
  kcopy.(4ul) <- k4;   kcopy.(5ul) <- k5;
  kcopy.(6ul) <- k6;   kcopy.(7ul) <- k7;
  kcopy.(8ul) <- k8;   kcopy.(9ul) <- k9;
  kcopy.(10ul) <- k10; kcopy.(11ul) <- k11;
  kcopy.(12ul) <- k12; kcopy.(13ul) <- k13;
  kcopy.(14ul) <- k14; kcopy.(15ul) <- k15;
  kcopy.(16ul) <- k16; kcopy.(17ul) <- k17;
  kcopy.(18ul) <- k18; kcopy.(19ul) <- k19;
  kcopy.(20ul) <- k20; kcopy.(21ul) <- k21;
  kcopy.(22ul) <- k22; kcopy.(23ul) <- k23;
  kcopy.(24ul) <- k24; kcopy.(25ul) <- k25;
  kcopy.(26ul) <- k26; kcopy.(27ul) <- k27;
  kcopy.(28ul) <- k28; kcopy.(29ul) <- k29;
  kcopy.(30ul) <- k30; kcopy.(31ul) <- k31;
  input.(0ul) <- n0;   input.(1ul) <- n1;
  input.(2ul) <- n2;   input.(3ul) <- n3;
  input.(4ul) <- n4;   input.(5ul) <- n5;
  input.(6ul) <- n6;   input.(7ul) <- n7;
  input.(8ul)  <- uint64_to_sint8 ic;
  input.(9ul)  <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 8ul));
  input.(10ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 16ul));
  input.(11ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 24ul));
  input.(12ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 32ul));
  input.(13ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 40ul));
  input.(14ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 48ul));
  input.(15ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 56ul))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

[@"c_inline"]
private inline_for_extraction val crypto_stream_salsa20_xor_ic_:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m /\ U64.v mlen > 0} ->
  n:uint8_p{length n = 8} ->
  ic:FStar.UInt64.t ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@"c_inline"]
private inline_for_extraction let crypto_stream_salsa20_xor_ic_ c m mlen n ic k =
  cut (U64.v mlen < pow2 32);
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  push_frame();
  let h0 = ST.get() in
  let zero = uint8_to_sint8 0uy in
  let local_state = create zero 112ul in
  let input = Buffer.sub local_state 0ul  16ul in
  let block = Buffer.sub local_state 16ul 64ul in
  let kcopy = Buffer.sub local_state 80ul 32ul in
  (* let k0 = k.(0ul) in let k1 = k.(1ul) in let k2 = k.(2ul) in let k3 = k.(3ul) in *)
  (* let k4 = k.(4ul) in let k5 = k.(5ul) in let k6 = k.(6ul) in let k7 = k.(7ul) in *)
  (* let k8 = k.(8ul) in let k9 = k.(9ul) in let k10 = k.(10ul) in let k11 = k.(11ul) in *)
  (* let k12 = k.(12ul) in let k13 = k.(13ul) in let k14 = k.(14ul) in let k15 = k.(15ul) in *)
  (* let k16 = k.(16ul) in let k17 = k.(17ul) in let k18 = k.(18ul) in let k19 = k.(19ul) in *)
  (* let k20 = k.(20ul) in let k21 = k.(21ul) in let k22 = k.(22ul) in let k23 = k.(23ul) in *)
  (* let k24 = k.(24ul) in let k25 = k.(25ul) in let k26 = k.(26ul) in let k27 = k.(27ul) in *)
  (* let k28 = k.(28ul) in let k29 = k.(29ul) in let k30 = k.(30ul) in let k31 = k.(31ul) in *)
  (* let n0 = n.(0ul) in let n1 = n.(1ul) in let n2 = n.(2ul) in let n3 = n.(3ul) in *)
  (* let n4 = n.(4ul) in let n5 = n.(5ul) in let n6 = n.(6ul) in let n7 = n.(7ul) in *)
  (* kcopy.(0ul) <- k0;   kcopy.(1ul) <- k1; *)
  (* kcopy.(2ul) <- k2;   kcopy.(3ul) <- k3; *)
  (* kcopy.(4ul) <- k4;   kcopy.(5ul) <- k5; *)
  (* kcopy.(6ul) <- k6;   kcopy.(7ul) <- k7; *)
  (* kcopy.(8ul) <- k8;   kcopy.(9ul) <- k9; *)
  (* kcopy.(10ul) <- k10; kcopy.(11ul) <- k11; *)
  (* kcopy.(12ul) <- k12; kcopy.(13ul) <- k13; *)
  (* kcopy.(14ul) <- k14; kcopy.(15ul) <- k15; *)
  (* kcopy.(16ul) <- k16; kcopy.(17ul) <- k17; *)
  (* kcopy.(18ul) <- k18; kcopy.(19ul) <- k19; *)
  (* kcopy.(20ul) <- k20; kcopy.(21ul) <- k21; *)
  (* kcopy.(22ul) <- k22; kcopy.(23ul) <- k23; *)
  (* kcopy.(24ul) <- k24; kcopy.(25ul) <- k25; *)
  (* kcopy.(26ul) <- k26; kcopy.(27ul) <- k27; *)
  (* kcopy.(28ul) <- k28; kcopy.(29ul) <- k29; *)
  (* kcopy.(30ul) <- k30; kcopy.(31ul) <- k31; *)
  (* input.(0ul) <- n0;   input.(1ul) <- n1; *)
  (* input.(2ul) <- n2;   input.(3ul) <- n3; *)
  (* input.(4ul) <- n4;   input.(5ul) <- n5; *)
  (* input.(6ul) <- n6;   input.(7ul) <- n7; *)
  (* input.(8ul)  <- uint64_to_sint8 ic; *)
  (* input.(9ul)  <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 8ul)); *)
  (* input.(10ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 16ul)); *)
  (* input.(11ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 24ul)); *)
  (* input.(12ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 32ul)); *)
  (* input.(13ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 40ul)); *)
  (* input.(14ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 48ul)); *)
  (* input.(15ul) <- uint64_to_sint8 (FStar.UInt64.(ic >>^ 56ul)); *)
  crypto_stream_salsa20_xor_ic__ n ic k local_state;
  let h1 = ST.get() in
  cut (modifies_0 h0 h1);
  let _ = crypto_stream_salsa20_xor_ic_loop c m block input kcopy mlen in
  let mlen' = mod_64 mlen in
  let off = U32.(Int.Cast.uint64_to_uint32 mlen -^ mlen') in
  let h2 = ST.get() in
  cut (modifies_3 c input block h1 h2);
  cut (live h2 block /\ live h2 c /\ disjoint block c);
  if U32.(mlen' >=^ 0ul) then (
    crypto_core_salsa20 block input kcopy;
    xor_bytes (offset c off) (offset m off) block (mlen')
  );
  let h3 = ST.get() in
  cut (modifies_2 c block h2 h3);
  lemma_modifies_3_1 c input block h0 h1 h2 h3;
  pop_frame()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

[@"c_inline"]
val crypto_stream_salsa20_xor_ic:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  n:uint8_p{length n = 8} ->
  ic:FStar.UInt64.t ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@"c_inline"]
let crypto_stream_salsa20_xor_ic c m mlen n ic k =
  if FStar.UInt64.(mlen =^ 0uL) then ()
  else crypto_stream_salsa20_xor_ic_ c m mlen n ic k


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

[@"c_inline"]
private val crypto_stream_salsa20_loop:
  c:uint8_p ->
  clen:FStar.UInt64.t{U64.v clen <= length c} ->
  n:uint8_p{length n = 8} ->
  k:uint8_p{length k = 32} ->
  input:uint8_p{length input = 16 /\ disjoint input c} ->
  Stack FStar.UInt64.t
    (requires (fun h -> live h c /\ live h n /\ live h k /\ live h input))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 input /\ modifies_2 c input h0 h1))
[@"c_inline"]
private let rec crypto_stream_salsa20_loop c clen n k input =
  if FStar.UInt64.(clen <^ 64uL) then clen
  else (
    crypto_core_salsa20 (Buffer.sub c 0ul 64ul) input k;
    let i8 = input.(8ul) in
    let i9 = input.(9ul) in
    let i10 = input.(10ul) in
    let i11 = input.(11ul) in
    let i12 = input.(12ul) in
    let i13 = input.(13ul) in
    let i14 = input.(14ul) in
    let i15 = input.(15ul) in
    let u = Hacl.UInt64.(
      sint8_to_sint64 i8
      +%^ (sint8_to_sint64 i9 <<^ 8ul)
      +%^ (sint8_to_sint64 i10 <<^ 16ul)
      +%^ (sint8_to_sint64 i11 <<^ 24ul)
      +%^ (sint8_to_sint64 i12 <<^ 32ul)
      +%^ (sint8_to_sint64 i13 <<^ 40ul)
      +%^ (sint8_to_sint64 i14 <<^ 48ul)
      +%^ (sint8_to_sint64 i15 <<^ 56ul)
      +%^ (uint64_to_sint64 1uL)
    ) in
    input.(8ul)  <- sint64_to_sint8 u;
    input.(9ul)  <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 8ul));
    input.(10ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 16ul));
    input.(11ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 24ul));
    input.(12ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 32ul));
    input.(13ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 40ul));
    input.(14ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 48ul));
    input.(15ul) <- sint64_to_sint8 (Hacl.UInt64.(u >>^ 56ul));
    let clen = FStar.UInt64.(clen -^ 64uL) in
    let c = offset c 64ul in
    crypto_stream_salsa20_loop c clen n k input
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"


private let lemma_modifies_4 (c:uint8_p) (input:uint8_p) (block:uint8_p) h0 h1 h2 h3 : Lemma
  (requires (live h0 c /\ ~(contains h0 input) /\ ~(contains h0 block)
    /\ live h1 c /\ live h1 input /\ live h1 block
    /\ live h2 c /\ live h2 input /\ live h2 block
    /\ modifies_0 h0 h1 /\ modifies_2 c input h1 h2 /\ modifies_2 c block h2 h3))
  (ensures (modifies_2_1 c h0 h3))
  = lemma_reveal_modifies_0 h0 h1;
    lemma_reveal_modifies_2 c input h1 h2;
    lemma_reveal_modifies_2 c block h2 h3;
    lemma_intro_modifies_2_1 c h0 h3


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
[@"c_inline"]
private val crypto_stream_salsa20_:
  n:uint8_p{length n = 8} ->
  k:uint8_p{length k = 32} ->
  local_state:uint8_p{length local_state = 112} ->
  Stack unit
    (requires (fun h -> live h n /\ live h k /\ live h local_state))
    (ensures  (fun h0 _ h1 -> live h1 local_state /\ modifies_1 local_state h0 h1))
[@"c_inline"]
private let crypto_stream_salsa20_ n k local_state =
  let zero = Hacl.Cast.uint8_to_sint8 0uy in
  let input = Buffer.sub local_state 0ul 16ul in
  let block = Buffer.sub local_state 16ul 64ul in
  let kcopy = Buffer.sub local_state 80ul 32ul in
  let k0 = k.(0ul) in let k1 = k.(1ul) in let k2 = k.(2ul) in let k3 = k.(3ul) in
  let k4 = k.(4ul) in let k5 = k.(5ul) in let k6 = k.(6ul) in let k7 = k.(7ul) in
  let k8 = k.(8ul) in let k9 = k.(9ul) in let k10 = k.(10ul) in let k11 = k.(11ul) in
  let k12 = k.(12ul) in let k13 = k.(13ul) in let k14 = k.(14ul) in let k15 = k.(15ul) in
  let k16 = k.(16ul) in let k17 = k.(17ul) in let k18 = k.(18ul) in let k19 = k.(19ul) in
  let k20 = k.(20ul) in let k21 = k.(21ul) in let k22 = k.(22ul) in let k23 = k.(23ul) in
  let k24 = k.(24ul) in let k25 = k.(25ul) in let k26 = k.(26ul) in let k27 = k.(27ul) in
  let k28 = k.(28ul) in let k29 = k.(29ul) in let k30 = k.(30ul) in let k31 = k.(31ul) in
  let n0 = n.(0ul) in let n1 = n.(1ul) in let n2 = n.(2ul) in let n3 = n.(3ul) in
  let n4 = n.(4ul) in let n5 = n.(5ul) in let n6 = n.(6ul) in let n7 = n.(7ul) in
  kcopy.(0ul) <- k0;   kcopy.(1ul) <- k1;
  kcopy.(2ul) <- k2;   kcopy.(3ul) <- k3;
  kcopy.(4ul) <- k4;   kcopy.(5ul) <- k5;
  kcopy.(6ul) <- k6;   kcopy.(7ul) <- k7;
  kcopy.(8ul) <- k8;   kcopy.(9ul) <- k9;
  kcopy.(10ul) <- k10; kcopy.(11ul) <- k11;
  kcopy.(12ul) <- k12; kcopy.(13ul) <- k13;
  kcopy.(14ul) <- k14; kcopy.(15ul) <- k15;
  kcopy.(16ul) <- k16; kcopy.(17ul) <- k17;
  kcopy.(18ul) <- k18; kcopy.(19ul) <- k19;
  kcopy.(20ul) <- k20; kcopy.(21ul) <- k21;
  kcopy.(22ul) <- k22; kcopy.(23ul) <- k23;
  kcopy.(24ul) <- k24; kcopy.(25ul) <- k25;
  kcopy.(26ul) <- k26; kcopy.(27ul) <- k27;
  kcopy.(28ul) <- k28; kcopy.(29ul) <- k29;
  kcopy.(30ul) <- k30; kcopy.(31ul) <- k31;
  input.(0ul) <- n0;   input.(1ul) <- n1;
  input.(2ul) <- n2;   input.(3ul) <- n3;
  input.(4ul) <- n4;   input.(5ul) <- n5;
  input.(6ul) <- n6;   input.(7ul) <- n7;
  input.(8ul)  <- zero;
  input.(9ul)  <- zero;
  input.(10ul) <- zero;
  input.(11ul) <- zero;
  input.(12ul) <- zero;
  input.(13ul) <- zero;
  input.(14ul) <- zero;
  input.(15ul) <- zero


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

[@"c_inline"]
val crypto_stream_salsa20:
  c:uint8_p ->
  clen:FStar.UInt64.t{U64.v clen <= length c} ->
  n:uint8_p{length n = 8} ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
[@"c_inline"]
let crypto_stream_salsa20 c clen n k =
  push_frame();
  let hh = ST.get() in
  if (FStar.UInt64.(clen =^ 0uL)) then (let h = ST.get() in lemma_intro_modifies_2_1 c h h)
  else (
    let clen' = mod_64 clen in
    Math.Lemmas.modulo_lemma (U64.v clen) (pow2 32);
    let off = U32.(Int.Cast.uint64_to_uint32 clen -^ clen') in
    let h0 = ST.get() in
    let zero = uint8_to_sint8 0uy in
    let local_state = create zero 112ul in
    let input = Buffer.sub local_state 0ul 16ul in
    let block = Buffer.sub local_state 16ul 64ul in
    let kcopy = Buffer.sub local_state 80ul 32ul in
    (* let k0 = k.(0ul) in let k1 = k.(1ul) in let k2 = k.(2ul) in let k3 = k.(3ul) in *)
    (* let k4 = k.(4ul) in let k5 = k.(5ul) in let k6 = k.(6ul) in let k7 = k.(7ul) in *)
    (* let k8 = k.(8ul) in let k9 = k.(9ul) in let k10 = k.(10ul) in let k11 = k.(11ul) in *)
    (* let k12 = k.(12ul) in let k13 = k.(13ul) in let k14 = k.(14ul) in let k15 = k.(15ul) in *)
    (* let k16 = k.(16ul) in let k17 = k.(17ul) in let k18 = k.(18ul) in let k19 = k.(19ul) in *)
    (* let k20 = k.(20ul) in let k21 = k.(21ul) in let k22 = k.(22ul) in let k23 = k.(23ul) in *)
    (* let k24 = k.(24ul) in let k25 = k.(25ul) in let k26 = k.(26ul) in let k27 = k.(27ul) in *)
    (* let k28 = k.(28ul) in let k29 = k.(29ul) in let k30 = k.(30ul) in let k31 = k.(31ul) in *)
    (* let n0 = n.(0ul) in let n1 = n.(1ul) in let n2 = n.(2ul) in let n3 = n.(3ul) in *)
    (* let n4 = n.(4ul) in let n5 = n.(5ul) in let n6 = n.(6ul) in let n7 = n.(7ul) in *)
    (* kcopy.(0ul) <- k0;   kcopy.(1ul) <- k1; *)
    (* kcopy.(2ul) <- k2;   kcopy.(3ul) <- k3; *)
    (* kcopy.(4ul) <- k4;   kcopy.(5ul) <- k5; *)
    (* kcopy.(6ul) <- k6;   kcopy.(7ul) <- k7; *)
    (* kcopy.(8ul) <- k8;   kcopy.(9ul) <- k9; *)
    (* kcopy.(10ul) <- k10; kcopy.(11ul) <- k11; *)
    (* kcopy.(12ul) <- k12; kcopy.(13ul) <- k13; *)
    (* kcopy.(14ul) <- k14; kcopy.(15ul) <- k15; *)
    (* kcopy.(16ul) <- k16; kcopy.(17ul) <- k17; *)
    (* kcopy.(18ul) <- k18; kcopy.(19ul) <- k19; *)
    (* kcopy.(20ul) <- k20; kcopy.(21ul) <- k21; *)
    (* kcopy.(22ul) <- k22; kcopy.(23ul) <- k23; *)
    (* kcopy.(24ul) <- k24; kcopy.(25ul) <- k25; *)
    (* kcopy.(26ul) <- k26; kcopy.(27ul) <- k27; *)
    (* kcopy.(28ul) <- k28; kcopy.(29ul) <- k29; *)
    (* kcopy.(30ul) <- k30; kcopy.(31ul) <- k31; *)
    (* input.(0ul) <- n0;   input.(1ul) <- n1; *)
    (* input.(2ul) <- n2;   input.(3ul) <- n3; *)
    (* input.(4ul) <- n4;   input.(5ul) <- n5; *)
    (* input.(6ul) <- n6;   input.(7ul) <- n7; *)
    (* input.(8ul)  <- zero; *)
    (* input.(9ul)  <- zero; *)
    (* input.(10ul) <- zero; *)
    (* input.(11ul) <- zero; *)
    (* input.(12ul) <- zero; *)
    (* input.(13ul) <- zero; *)
    (* input.(14ul) <- zero; *)
    (* input.(15ul) <- zero; *)
    crypto_stream_salsa20_ n k local_state;
    let h1 = ST.get() in
    cut (modifies_0 h0 h1);
    let _ = crypto_stream_salsa20_loop c clen n kcopy input in
    let h2 = ST.get() in
    cut (modifies_2 c input h1 h2);
    if U32.(clen' >=^ 0ul) then (
      crypto_core_salsa20 block input kcopy;
      blit block 0ul (offset c off) 0ul (clen');
      let h3 = ST.get() in
      cut (modifies_2 c block h2 h3)
    ) else (lemma_intro_modifies_2 c block h2 h2);
    let h3 = ST.get() in
    cut (modifies_2 c block h2 h3);
    lemma_modifies_4 c input block h0 h1 h2 h3
  );
  let hhh = ST.get() in
  cut (modifies_2_1 c hh hhh);
  pop_frame()


val crypto_stream_salsa20_xor:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  n:uint8_p{length n = 8} ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
let crypto_stream_salsa20_xor c m mlen n k =
  crypto_stream_salsa20_xor_ic c m mlen n 0uL k
