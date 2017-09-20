module Hacl.Spec.Symmetric.Chacha20

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Seq
open Hacl.Cast
open Hacl.UInt32

module U32 = FStar.UInt32
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32

let u32 = U32.t
let h32 = H32.t
let uint8_s = seq H8.t

type chacha_sctx = b:seq h32{length b = 16}

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"


val lemma_max_uint32: n:nat ->
  Lemma (requires (n = 32))
        (ensures (pow2 n = 4294967296))
        [SMTPat (pow2 n)]
let lemma_max_uint32 n = assert_norm (pow2 32 = 4294967296)


inline_for_extraction let op_Less_Less_Less (a:h32) (s:u32{U32.v s <= 32}) : Tot h32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32.(32ul -^ s)))


let load32_le_spec (k:uint8_s{length k >= 4}) : Tot h32
  = let k0 = Seq.index k 0 in
    let k1 = Seq.index k 1 in
    let k2 = Seq.index k 2 in
    let k3 = Seq.index k 3 in
    let z = sint8_to_sint32 k0
            |^ (sint8_to_sint32 k1 <<^ 8ul)
            |^ (sint8_to_sint32 k2 <<^ 16ul)
            |^ (sint8_to_sint32 k3 <<^ 24ul) in
    z


let store32_le_spec (s:uint8_s{length s = 4}) (x:h32) : Tot (s':uint8_s{length s' = 4})
  = let s = Seq.upd s 0 (sint32_to_sint8 x) in
    let s = Seq.upd s 1 (sint32_to_sint8 (x >>^ 8ul)) in
    let s = Seq.upd s 2 (sint32_to_sint8 (x >>^ 16ul)) in
    let s = Seq.upd s 3 (sint32_to_sint8 (x >>^ 24ul)) in
    s


unfold let slice_4 (s:uint8_s{length s = 32}) (n:nat{n <= 28 }) : Tot (s':uint8_s{length s' = 4})
  = slice s n (n+4)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val chacha_keysetup_spec: ctx:chacha_sctx -> k:uint8_s{length k = 32} -> Tot chacha_sctx
let chacha_keysetup_spec ctx k =
    let ctx = Seq.upd ctx 0 (uint32_to_sint32 0x61707865ul) in
    let ctx = Seq.upd ctx 1 (uint32_to_sint32 0x3320646eul) in
    let ctx = Seq.upd ctx 2 (uint32_to_sint32 0x79622d32ul) in
    let ctx = Seq.upd ctx 3 (uint32_to_sint32 0x6b206574ul) in
    let ctx = Seq.upd ctx 4 (load32_le_spec (slice_4 k 0)) in
    let ctx = Seq.upd ctx 5 (load32_le_spec (slice_4 k 4)) in
    let ctx = Seq.upd ctx 6 (load32_le_spec (slice_4 k 8)) in
    let ctx = Seq.upd ctx 7 (load32_le_spec (slice_4 k 12)) in
    let ctx = Seq.upd ctx 8 (load32_le_spec (slice_4 k 16)) in
    let ctx = Seq.upd ctx 9 (load32_le_spec (slice_4 k 20)) in
    let ctx = Seq.upd ctx 10 (load32_le_spec (slice_4 k 24)) in
    let ctx = Seq.upd ctx 11 (load32_le_spec (slice_4 k 28)) in
    ctx


val chacha_ietf_ivsetup_spec: ctx:chacha_sctx -> k:uint8_s{length k = 12} -> counter:u32 -> Tot chacha_sctx
let chacha_ietf_ivsetup_spec ctx iv counter =
  let ctx = Seq.upd ctx 12 (uint32_to_sint32 counter) in
  let ctx = Seq.upd ctx 13 (load32_le_spec (slice iv 0 4)) in
  let ctx = Seq.upd ctx 14 (load32_le_spec (slice iv 4 8)) in
  let ctx = Seq.upd ctx 15 (load32_le_spec (slice iv 8 12)) in
  ctx


let seq_upd_16 (s:chacha_sctx) (s0:h32) (s1:h32) (s2:h32) (s3:h32) (s4:h32) (s5:h32) (s6:h32) (s7:h32) (s8:h32) (s9:h32) (s10:h32) (s11:h32) (s12:h32) (s13:h32) (s14:h32) (s15:h32) : Tot chacha_sctx =
    let s = Seq.upd s 0 s0 in
    let s = Seq.upd s 1 s1 in
    let s = Seq.upd s 2 s2 in
    let s = Seq.upd s 3 s3 in
    let s = Seq.upd s 4 s4 in
    let s = Seq.upd s 5 s5 in
    let s = Seq.upd s 6 s6 in
    let s = Seq.upd s 7 s7 in
    let s = Seq.upd s 8 s8 in
    let s = Seq.upd s 9 s9 in
    let s = Seq.upd s 10 s10 in
    let s = Seq.upd s 11 s11 in
    let s = Seq.upd s 12 s12 in
    let s = Seq.upd s 13 s13 in
    let s = Seq.upd s 14 s14 in
    let s = Seq.upd s 15 s15 in
    s


val chacha_encrypt_bytes_round_spec: ctx:chacha_sctx -> Tot chacha_sctx
let chacha_encrypt_bytes_round_spec ctx =
  let x0 = Seq.index ctx 0 in
  let x1 = Seq.index ctx 1 in
  let x2 = Seq.index ctx 2 in
  let x3 = Seq.index ctx 3 in
  let x4 = Seq.index ctx 4 in
  let x5 = Seq.index ctx 5 in
  let x6 = Seq.index ctx 6 in
  let x7 = Seq.index ctx 7 in
  let x8 = Seq.index ctx 8 in
  let x9 = Seq.index ctx 9 in
  let x10 = Seq.index ctx 10 in
  let x11 = Seq.index ctx 11 in
  let x12 = Seq.index ctx 12 in
  let x13 = Seq.index ctx 13 in
  let x14 = Seq.index ctx 14 in
  let x15 = Seq.index ctx 15 in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  seq_upd_16 ctx x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15


val chacha_encrypt_bytes_rounds_spec: ctx:chacha_sctx -> Tot chacha_sctx
let chacha_encrypt_bytes_rounds_spec ctx =
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  let ctx = chacha_encrypt_bytes_round_spec ctx in
  ctx



val chacha_encrypt_bytes_store_spec:
  c:uint8_s{length c = 64} ->
  x0:h32 -> x1:h32 -> x2:h32 -> x3:h32 -> x4:h32 -> x5:h32 -> x6:h32 -> x7:h32 ->
  x8:h32 -> x9:h32 -> x10:h32 -> x11:h32 -> x12:h32 -> x13:h32 -> x14:h32 -> x15:h32 ->
  Tot (c':uint8_s{length c' = 64})
let chacha_encrypt_bytes_store_spec c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
  let c0 = store32_le_spec (slice c 0 4) x0 in
  let c1 = store32_le_spec  (slice c 4 8) x1 in
  let c2 = store32_le_spec (slice c 8 12) x2 in
  let c3 = store32_le_spec (slice c 12 16) x3 in
  let c4 = store32_le_spec (slice c 16 20) x4 in
  let c5 = store32_le_spec (slice c 20 24) x5 in
  let c6 = store32_le_spec (slice c 24 28) x6 in
  let c7 = store32_le_spec (slice c 28 32) x7 in
  let c8 = store32_le_spec (slice c 32 36) x8 in
  let c9 = store32_le_spec (slice c 36 40) x9 in
  let c10 = store32_le_spec (slice c 40 44) x10 in
  let c11 = store32_le_spec (slice c 44 48) x11 in
  let c12 = store32_le_spec (slice c 48 52) x12 in
  let c13 = store32_le_spec (slice c 52 56) x13 in
  let c14 = store32_le_spec (slice c 56 60) x14 in
  let c15 = store32_le_spec (slice c 60 64) x15 in
  c0 @| c1 @| c2 @| c3 @| c4 @| c5 @| c6 @| c7 @| c8 @| c9 @| c10 @| c11 @| c12 @| c13 @| c14 @| c15


#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

val chacha_encrypt_bytes_core_spec: ctx:chacha_sctx -> m:uint8_s{length m = 64} -> c:uint8_s{length c = 64} -> Tot (s':uint8_s{length s' = 64})
let chacha_encrypt_bytes_core_spec ctx m c =
  let tmp = chacha_encrypt_bytes_rounds_spec ctx in
  let j0 = Seq.index ctx 0 in
  let j1 = Seq.index ctx 1 in
  let j2 = Seq.index ctx 2 in
  let j3 = Seq.index ctx 3 in
  let j4 = Seq.index ctx 4 in
  let j5 = Seq.index ctx 5 in
  let j6 = Seq.index ctx 6 in
  let j7 = Seq.index ctx 7 in
  let j8 = Seq.index ctx 8 in
  let j9 = Seq.index ctx 9 in
  let j10 = Seq.index ctx 10 in
  let j11 = Seq.index ctx 11 in
  let j12 = Seq.index ctx 12 in
  let j13 = Seq.index ctx 13 in
  let j14 = Seq.index ctx 14 in
  let j15 = Seq.index ctx 15 in
  let x0 = Seq.index tmp 0 in
  let x1 = Seq.index tmp 1 in
  let x2 = Seq.index tmp 2 in
  let x3 = Seq.index tmp 3 in
  let x4 = Seq.index tmp 4 in
  let x5 = Seq.index tmp 5 in
  let x6 = Seq.index tmp 6 in
  let x7 = Seq.index tmp 7 in
  let x8 = Seq.index tmp 8 in
  let x9 = Seq.index tmp 9 in
  let x10 = Seq.index tmp 10 in
  let x11 = Seq.index tmp 11 in
  let x12 = Seq.index tmp 12 in
  let x13 = Seq.index tmp 13 in
  let x14 = Seq.index tmp 14 in
  let x15 = Seq.index tmp 15 in
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
  let m0 = load32_le_spec (slice m 0 4) in
  let m1 = load32_le_spec (slice m 4 8) in
  let m2 = load32_le_spec (slice m 8 12) in
  let m3 = load32_le_spec (slice m 12 16) in
  let m4 = load32_le_spec (slice m 16 20) in
  let m5 = load32_le_spec (slice m 20 24) in
  let m6 = load32_le_spec (slice m 24 28) in
  let m7 = load32_le_spec (slice m 28 32) in
  let m8 = load32_le_spec (slice m 32 36) in
  let m9 = load32_le_spec (slice m 36 40) in
  let m10 = load32_le_spec (slice m 40 44) in
  let m11 = load32_le_spec (slice m 44 48) in
  let m12 = load32_le_spec (slice m 48 52) in
  let m13 = load32_le_spec (slice m 52 56) in
  let m14 = load32_le_spec (slice m 56 60) in
  let m15 = load32_le_spec(slice m 60 64) in
  let x0 = x0 ^^ m0 in
  let x1 = x1 ^^ m1 in
  let x2 = x2 ^^ m2 in
  let x3 = x3 ^^ m3 in
  let x4 = x4 ^^ m4 in
  let x5 = x5 ^^ m5 in
  let x6 = x6 ^^ m6 in
  let x7 = x7 ^^ m7 in
  let x8 = x8 ^^ m8 in
  let x9 = x9 ^^ m9 in
  let x10 = x10 ^^ m10 in
  let x11 = x11 ^^ m11 in
  let x12 = x12 ^^ m12 in
  let x13 = x13 ^^ m13 in
  let x14 = x14 ^^ m14 in
  let x15 = x15 ^^ m15 in
  chacha_encrypt_bytes_store_spec c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15


(* val chacha_encrypt_bytes_loop: *)
(*   ctx:chacha_ctx -> *)
(*   m:uint8_p -> *)
(*   c:uint8_p{disjoint ctx c} -> *)
(*   len:U32.t{U32.v len <= length m /\ U32.v len <= length c} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h c /\ live h m /\ live h ctx)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1)) *)
(* let rec chacha_encrypt_bytes_loop ctx m c len = *)
(*   if FStar.UInt32.(len <^ 64ul) then () *)
(*   else ( *)
(*     chacha_encrypt_bytes_core ctx m c; *)
(*     let ctr = ctx.(12ul) in *)
(*     let one = uint32_to_sint32 1ul in *)
(*     ctx.(12ul) <- H32.(ctr +%^ one); *)
(*     chacha_encrypt_bytes_loop ctx (offset m 64ul) (offset c 64ul) (FStar.UInt32.(len -^ 64ul)) *)
(*   ) *)


(* val chacha_encrypt_bytes_finish: *)
(*   ctx:chacha_ctx -> *)
(*   m:uint8_p -> *)
(*   c:uint8_p{disjoint ctx c} -> *)
(*   len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c /\ U32.v len < 64} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h c /\ live h m /\ live h ctx)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1)) *)
(* let chacha_encrypt_bytes_finish ctx m c len = *)
(*   let hinit = ST.get() in *)
(*   push_frame(); *)
(*   let h0 = ST.get() in *)
(*   let zero = uint8_to_sint8 0uy in *)
(*   let tmp = create zero 64ul in *)
(*   let h0' = ST.get() in *)
(*   blit m 0ul tmp 0ul len; *)
(*   let h1 = ST.get() in *)
(*   chacha_encrypt_bytes_core ctx tmp tmp; *)
(*   let h2 = ST.get() in *)
(*   blit tmp 0ul c 0ul len; *)
(*   let h3 = ST.get() in *)
(*   lemma_modifies_2_1'' ctx c h0 h2 h3; *)
(*   pop_frame(); *)
(*   let hfin = ST.get() in *)
(*   () *)


(* val chacha_encrypt_bytes: *)
(*   ctx:chacha_ctx -> *)
(*   m:uint8_p -> *)
(*   c:uint8_p{disjoint ctx c} -> *)
(*   len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h c /\ live h m /\ live h ctx)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1)) *)
(* let rec chacha_encrypt_bytes ctx m c len = *)
(*   chacha_encrypt_bytes_loop ctx m c len; *)
(*   UInt.logand_mask (U32.v len) 6; *)
(*   assert_norm(pow2 6 = 64); *)
(*   Math.Lemmas.euclidean_division_definition (U32.v len) 64; *)
(*   let rema = U32.(len &^ 63ul) in // % 64 *)
(*   let q   = U32.(len >>^ 6ul) in // / 64 *)
(*   if FStar.UInt32.(rema >=^ 0ul) then ( *)
(*     let m = offset m (U32.(len -^ rema)) in *)
(*     let c = offset c (U32.(len -^ rema)) in *)
(*     chacha_encrypt_bytes_finish ctx m c rema) *)
