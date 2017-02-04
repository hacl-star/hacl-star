module Hacl.Symmetric.Salsa20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast


let h8 = Hacl.UInt8.t
let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t

type salsa_ctx = b:Buffer.buffer h32{length b = 16}
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
private inline_for_extraction val salsa20_quarter_round:
  ctx:salsa_ctx ->
  a:u32 -> b:u32 -> c:u32 -> d:u32 ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let salsa20_quarter_round ctx a b c d =
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
private inline_for_extraction val salsa20_row_round:
  ctx:salsa_ctx ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let salsa20_row_round ctx =
  salsa20_quarter_round ctx 0ul 1ul 2ul 3ul;
  salsa20_quarter_round ctx 5ul 6ul 7ul 4ul;
  salsa20_quarter_round ctx 10ul 11ul 8ul 9ul;
  salsa20_quarter_round ctx 15ul 12ul 13ul 14ul


[@"c_inline"]
private inline_for_extraction val salsa20_column_round:
  ctx:salsa_ctx ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private inline_for_extraction let salsa20_column_round ctx =
  salsa20_quarter_round ctx 0ul 4ul 8ul 12ul;
  salsa20_quarter_round ctx 5ul 9ul 13ul 1ul;
  salsa20_quarter_round ctx 10ul 14ul 2ul 6ul;
  salsa20_quarter_round ctx 15ul 3ul 7ul 11ul

[@"c_inline"]
private val salsa20_double_round_10:
  ctx:salsa_ctx ->
  Stack unit
    (requires (fun h -> live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx /\ live h0 ctx))
[@"c_inline"]
private let salsa20_double_round_10 ctx =
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx;
  salsa20_column_round ctx;
  salsa20_row_round ctx

[@"c_inline"]
private inline_for_extraction val salsa20_init:
  ctx   :salsa_ctx ->
  key   :uint8_p{length key = 32} ->
  n     :uint8_p{length n = 8} ->
  ic    :FStar.UInt64.t ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_1 ctx h0 h1 /\ live h1 ctx))
[@"c_inline"]
private inline_for_extraction let salsa20_init ctx key n ic =
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
  ctx.(6ul)  <- load32_le(offset n 0ul);
  ctx.(7ul)  <- load32_le(offset n 4ul);
  ctx.(8ul)  <- sint64_to_sint32 ic;
  ctx.(9ul)  <- sint64_to_sint32 Hacl.UInt64.(ic >>^ 32ul)


[@"c_inline"]
private val salsa20:
  output: salsa_ctx ->
  ctx: salsa_ctx ->
  Stack unit
    (requires (fun h -> live h output /\ live h ctx))
    (ensures  (fun h0 _ h1 -> modifies_1 output h0 h1 /\ live h1 output))
[@"c_inline"]
private let salsa20 output ctx =
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
  output.(0ul) <- j0;
  output.(1ul) <- j1;
  output.(2ul) <- j2;
  output.(3ul) <- j3;
  output.(4ul) <- j4;
  output.(5ul) <- j5;
  output.(6ul) <- j6;
  output.(7ul) <- j7;
  output.(8ul) <- j8;
  output.(9ul) <- j9;
  output.(10ul) <- j10;
  output.(11ul) <- j11;
  output.(12ul) <- j12;
  output.(13ul) <- j13;
  output.(14ul) <- j14;
  output.(15ul) <- j15;
  (* *)
  salsa20_double_round_10 output;
  (* *)
  let x0 = output.(0ul) in
  let x1 = output.(1ul) in
  let x2 = output.(2ul) in
  let x3 = output.(3ul) in
  let x4 = output.(4ul) in
  let x5 = output.(5ul) in
  let x6 = output.(6ul) in
  let x7 = output.(7ul) in
  let x8 = output.(8ul) in
  let x9 = output.(9ul) in
  let x10 = output.(10ul) in
  let x11 = output.(11ul) in
  let x12 = output.(12ul) in
  let x13 = output.(13ul) in
  let x14 = output.(14ul) in
  let x15 = output.(15ul) in
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
  output.(0ul) <- x0;
  output.(1ul) <- x1;
  output.(2ul) <- x2;
  output.(3ul) <- x3;
  output.(4ul) <- x4;
  output.(5ul) <- x5;
  output.(6ul) <- x6;
  output.(7ul) <- x7;
  output.(8ul) <- x8;
  output.(9ul) <- x9;
  output.(10ul) <- x10;
  output.(11ul) <- x11;
  output.(12ul) <- x12;
  output.(13ul) <- x13;
  output.(14ul) <- x14;
  output.(15ul) <- x15

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module H32 = Hacl.UInt32

[@"c_inline"]
private val xor_:
  c:uint8_p{length c >= 64} ->
  m:uint8_p{length m >= 64} ->
  block:salsa_ctx ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h block))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
[@"c_inline"]
private let xor_ c m b =
  let m0 = load32_le (offset m 0ul) in
  let m1 = load32_le (offset m 4ul) in
  let m2 = load32_le (offset m 8ul) in
  let m3 = load32_le (offset m 12ul) in
  let m4 = load32_le (offset m 16ul) in
  let m5 = load32_le (offset m 20ul) in
  let m6 = load32_le (offset m 24ul) in
  let m7 = load32_le (offset m 28ul) in
  let m8 = load32_le (offset m 32ul) in
  let m9 = load32_le (offset m 36ul) in
  let m10 = load32_le (offset m 40ul) in
  let m11 = load32_le (offset m 44ul) in
  let m12 = load32_le (offset m 48ul) in
  let m13 = load32_le (offset m 52ul) in
  let m14 = load32_le (offset m 56ul) in
  let m15 = load32_le (offset m 60ul) in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  let b8 = b.(8ul) in
  let b9 = b.(9ul) in
  let b10 = b.(10ul) in
  let b11 = b.(11ul) in
  let b12 = b.(12ul) in
  let b13 = b.(13ul) in
  let b14 = b.(14ul) in
  let b15 = b.(15ul) in
  let c0 = H32.(m0 ^^ b0) in
  let c1 = H32.(m1 ^^ b1) in
  let c2 = H32.(m2 ^^ b2) in
  let c3 = H32.(m3 ^^ b3) in
  let c4 = H32.(m4 ^^ b4) in
  let c5 = H32.(m5 ^^ b5) in
  let c6 = H32.(m6 ^^ b6) in
  let c7 = H32.(m7 ^^ b7) in
  let c8 = H32.(m8 ^^ b8) in
  let c9 = H32.(m9 ^^ b9) in
  let c10 = H32.(m10 ^^ b10) in
  let c11 = H32.(m11 ^^ b11) in
  let c12 = H32.(m12 ^^ b12) in
  let c13 = H32.(m13 ^^ b13) in
  let c14 = H32.(m14 ^^ b14) in
  let c15 = H32.(m15 ^^ b15) in
  store32_le (offset c 0ul ) c0;
  store32_le (offset c 4ul) c1;
  store32_le (offset c 8ul) c2;
  store32_le (offset c 12ul) c3;
  store32_le (offset c 16ul ) c4;
  store32_le (offset c 20ul) c5;
  store32_le (offset c 24ul) c6;
  store32_le (offset c 28ul) c7;
  store32_le (offset c 32ul ) c8;
  store32_le (offset c 36ul) c9;
  store32_le (offset c 40ul) c10;
  store32_le (offset c 44ul) c11;
  store32_le (offset c 48ul ) c12;
  store32_le (offset c 52ul) c13;
  store32_le (offset c 56ul) c14;
  store32_le (offset c 60ul) c15

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
private val salsa20_xor:
  c:uint8_p ->
  m:uint8_p ->
  ctx: salsa_ctx ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_1 c h0 h1))
[@"c_inline"]
private let salsa20_xor c m ctx =
  push_frame();
  let block = create 0ul 16ul in
  salsa20 block ctx;
  xor_ c m block;
  pop_frame()

[@"c_inline"]
private val crypto_stream_salsa20_xor_ic_loop:
  c:uint8_p ->
  m:uint8_p ->
  ctx: salsa_ctx ->
  ctr: UInt64.t ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  Stack (z:FStar.UInt64.t{FStar.UInt64.v z < 64})
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_2 c ctx h0 h1))
[@"c_inline"]
private let rec crypto_stream_salsa20_xor_ic_loop c m ctx ctr mlen =
  if (FStar.UInt64.(mlen <^ 64uL)) then (
    let h = ST.get() in
    mlen )
  else (
    let h0 = ST.get() in
    salsa20_xor c m ctx;    
    let h2 = ST.get() in
    (* *)
    let ctr1 = U64.(ctr +^ 1uL) in
    let sctr1 = uint64_to_sint64 ctr1 in
    ctx.(8ul)  <- sint64_to_sint32 sctr1;
    ctx.(9ul)  <- sint64_to_sint32 Hacl.UInt64.(sctr1 >>^ 32ul);
    (* *)
    let h3 = ST.get() in
    let mlen = FStar.UInt64.(mlen -^ 64uL) in
    let c' = offset c 64ul in
    let m' = offset m 64ul in
    (* *)
    crypto_stream_salsa20_xor_ic_loop c' m' ctx ctr1 mlen 
  )


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

[@"c_inline"]
private val xor_bytes:
  x:uint8_p ->
  y:uint8_p ->
  b:salsa_ctx ->
  i:FStar.UInt32.t ->
  len:FStar.UInt32.t ->
  Stack unit
    (requires (fun h -> live h x /\ live h y /\ live h b /\ 
    	      	        (let iv = U32.v (i *^ 4ul) in 
  	             	let l = U32.v len in 
		     	iv <= 16 /\ iv <= l /\ 0 <= iv /\
		     	length x >= l /\ 
		     	length y >= l)))
    (ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))
[@"c_inline"]
private let rec xor_bytes x y b i len =
  let curr:U32.t = U32.(i *^ 4ul) in
  let r :U32.t = U32.(len -^ curr) in
  if U32.(r =^ 0ul) then ()
  else (
  if U32.(r =^ 1ul) then (
    let bi = b.(i) in
    let y0 = y.(curr) in 
    let b0 = sint32_to_sint8 bi in
    x.(curr) <- Hacl.UInt8.(y0 ^^ b0)
  )
  else (
  if U32.(r =^ 2ul) then (
    let bi = b.(i) in
    let y0 = y.(curr) in 
    let y1 = y.(curr +^ 1ul) in 
    let bi = b.(i) in
    let b0 = sint32_to_sint8 bi in
    let b1 = sint32_to_sint8 H32.(bi >>^ 8ul) in
    x.(curr) <- Hacl.UInt8.(y0 ^^ b0);
    x.(curr +^ 1ul) <- Hacl.UInt8.(y0 ^^ b1)
  )
  else (
  if U32.(r =^ 3ul) then (
    let bi = b.(i) in
    let y0 = y.(curr) in 
    let y1 = y.(curr +^ 1ul) in 
    let y2 = y.(curr +^ 2ul) in 
    let b0 = sint32_to_sint8 bi in
    let b1 = sint32_to_sint8 H32.(bi >>^ 8ul) in
    let b2 = sint32_to_sint8 H32.(bi >>^ 16ul) in
    x.(curr) <- Hacl.UInt8.(y0 ^^ b0);
    x.(curr +^ 1ul) <- Hacl.UInt8.(y1 ^^ b1);
    x.(curr +^ 2ul) <- Hacl.UInt8.(y2 ^^ b2)
  )
  else (
  if U32.(r =^ 3ul) then (
    let bi = b.(i) in
    let y0 = y.(curr) in 
    let y1 = y.(curr +^ 1ul) in 
    let y2 = y.(curr +^ 2ul) in 
    let y3 = y.(curr +^ 3ul) in 
    let b0 = sint32_to_sint8 bi in
    let b1 = sint32_to_sint8 H32.(bi >>^ 8ul) in
    let b2 = sint32_to_sint8 H32.(bi >>^ 16ul) in
    let b3 = sint32_to_sint8 H32.(bi >>^ 24ul) in
    x.(curr) <- Hacl.UInt8.(y0 ^^ b0);
    x.(curr +^ 1ul) <- Hacl.UInt8.(y1 ^^ b1);
    x.(curr +^ 2ul) <- Hacl.UInt8.(y2 ^^ b2);
    x.(curr +^ 3ul) <- Hacl.UInt8.(y3 ^^ b3);
    xor_bytes x y b (i +^ 1ul) len   
  )
  ))))

[@"c_inline"]
private val salsa20_xor_partial:
  c:uint8_p ->
  m:uint8_p ->
  ctx: salsa_ctx ->
  len:u32 ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_1 c h0 h1))
[@"c_inline"]
private let salsa20_xor_partial c m ctx len =
  push_frame();
  let block = create 0ul 16ul in
  salsa20 block ctx;
  xor_bytes c m block 0ul len;
  pop_frame()




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
  let ctx = create 0ul 16ul in
  salsa20_init ctx k n ic;
  let h1 = ST.get() in
  let _ = crypto_stream_salsa20_xor_ic_loop c m ctx ic mlen in
  let mlen' = mod_64 mlen in
  let off = U32.(Int.Cast.uint64_to_uint32 mlen -^ mlen') in
  let h2 = ST.get() in
  if U32.(mlen' >=^ 0ul) then (
    salsa20_xor_partial (offset c off) (offset m off) ctx (mlen')
  );
  let h3 = ST.get() in
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


[@"c_inline"]
private val salsa20_store:
  c:uint8_p ->
  ctx: salsa_ctx ->
  Stack unit
    (requires (fun h -> live h c /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_1 c h0 h1))
[@"c_inline"]
private let salsa20_store c ctx =
  push_frame();
  let b = create 0ul 16ul in
  salsa20 b ctx;
  store32_le (offset c 0ul) b.(0ul);
  store32_le (offset c 4ul) b.(1ul);
  store32_le (offset c 8ul) b.(2ul);
  store32_le (offset c 12ul) b.(3ul);
  store32_le (offset c 16ul) b.(4ul);
  store32_le (offset c 20ul) b.(5ul);
  store32_le (offset c 24ul) b.(6ul);
  store32_le (offset c 28ul) b.(7ul);
  store32_le (offset c 32ul) b.(8ul);
  store32_le (offset c 36ul) b.(9ul);
  store32_le (offset c 40ul) b.(10ul);
  store32_le (offset c 44ul) b.(11ul);
  store32_le (offset c 48ul) b.(12ul);
  store32_le (offset c 52ul) b.(13ul);
  store32_le (offset c 56ul) b.(14ul);
  store32_le (offset c 60ul) b.(15ul);
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

[@"c_inline"]
private val crypto_stream_salsa20_loop:
  c:uint8_p ->
  clen:FStar.UInt64.t{U64.v clen <= length c} ->
  ctx: salsa_ctx ->
  ctr: FStar.UInt64.t ->
  Stack FStar.UInt64.t
    (requires (fun h -> live h c /\ live h ctx /\ disjoint c ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_2 c ctx h0 h1))
[@"c_inline"]
private let rec crypto_stream_salsa20_loop c clen ctx ctr = 
  if FStar.UInt64.(clen <^ 64uL) then clen
  else (
    salsa20_store c ctx;

    let ctr1 = U64.(ctr +^ 1uL) in
    let sctr1 = uint64_to_sint64 ctr1 in
    ctx.(8ul)  <- sint64_to_sint32 sctr1;
    ctx.(9ul)  <- sint64_to_sint32 Hacl.UInt64.(sctr1 >>^ 32ul);
    let clen = FStar.UInt64.(clen -^ 64uL) in
    let c = offset c 64ul in
    crypto_stream_salsa20_loop c clen ctx ctr1
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



[@"c_inline"]
private val store_bytes:
  x:uint8_p ->
  b:salsa_ctx ->
  i:FStar.UInt32.t ->
  len:FStar.UInt32.t ->
  Stack unit
    (requires (fun h -> live h x /\ live h b /\ 
    	      	        (let iv = U32.v (i *^ 4ul) in 
  	             	let l = U32.v len in 
		     	iv <= 16 /\ iv <= l /\ 0 <= iv /\
		     	length x >= l)))
    (ensures  (fun h0 _ h1 -> live h1 x /\ modifies_1 x h0 h1))
[@"c_inline"]
private let rec store_bytes x b i len =
  let curr:U32.t = U32.(i *^ 4ul) in
  let r :U32.t = U32.(len -^ curr) in
  if U32.(r =^ 0ul) then ()
  else (
  if U32.(r =^ 1ul) then (
    let bi = b.(i) in
    let b0 = sint32_to_sint8 bi in
    x.(curr) <- b0
  )
  else (
  if U32.(r =^ 2ul) then (
    let bi = b.(i) in
    let b0 = sint32_to_sint8 bi in
    let b1 = sint32_to_sint8 H32.(bi >>^ 8ul) in
    x.(curr) <- b0;
    x.(curr +^ 1ul) <- b1
  )
  else (
  if U32.(r =^ 3ul) then (
    let bi = b.(i) in
    let b0 = sint32_to_sint8 bi in
    let b1 = sint32_to_sint8 H32.(bi >>^ 8ul) in
    let b2 = sint32_to_sint8 H32.(bi >>^ 16ul) in
    x.(curr) <- b0;
    x.(curr +^ 1ul) <- b1;
    x.(curr +^ 2ul) <- b2
  )
  else (
  if U32.(r =^ 3ul) then (
    let bi = b.(i) in
    let b0 = sint32_to_sint8 bi in
    let b1 = sint32_to_sint8 H32.(bi >>^ 8ul) in
    let b2 = sint32_to_sint8 H32.(bi >>^ 16ul) in
    let b3 = sint32_to_sint8 H32.(bi >>^ 24ul) in
    x.(curr) <- b0;
    x.(curr +^ 1ul) <- b1;
    x.(curr +^ 2ul) <- b2;
    x.(curr +^ 3ul) <- b3;
    store_bytes x b (i +^ 1ul) len   
  )
  ))))

[@"c_inline"]
private val salsa20_store_partial:
  c:uint8_p ->
  ctx: salsa_ctx ->
  len: UInt32.t ->
  Stack unit
    (requires (fun h -> live h c /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ live h1 ctx /\ modifies_1 c h0 h1))
[@"c_inline"]
private let salsa20_store_partial c ctx len =
  push_frame();
  let b = create 0ul 16ul in
  salsa20 b ctx;
  store_bytes c b 0ul len;
  pop_frame()

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
    let ctx = create 0ul 16ul in
    salsa20_init ctx k n 0uL;
    let h1 = ST.get() in
    let _ = crypto_stream_salsa20_loop c clen ctx 0uL in
    let h2 = ST.get() in
    if U32.(clen' >=^ 0ul) then (
      salsa20_store_partial (offset c off) ctx clen'
    ) else ()
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
