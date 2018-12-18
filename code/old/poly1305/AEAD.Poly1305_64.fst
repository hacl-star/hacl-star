module AEAD.Poly1305_64

open FStar.HyperStack.All

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.Mul
open FStar.HyperStack.ST
open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
let reveal = FStar.Ghost.reveal
open FStar.Endianness
open FStar.Buffer
open Hacl.Cast
open Spec.Chacha20Poly1305
open Hacl.Spec.Endianness


module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module I = Hacl.Impl.Poly1305_64
module S = Hacl.Spec.Poly1305_64
module Poly = Hacl.Standalone.Poly1305_64


#reset-options "--max_fuel 0 --z3rlimit 100"

let mk_state r acc = I.mk_state r acc

val pad_16_bytes:
  input:uint8_p ->
  len:U32.t{length input = U32.v len /\ U32.v len < 16 /\ U32.v len > 0} ->
  StackInline (uint8_p)
    (requires (fun h -> live h input))
    (ensures (fun h0 output h1 -> live h0 input /\ live h1 output /\ frameOf output = HS.get_tip h1
      /\ modifies_0 h0 h1 /\ length output = 16 /\ output `unused_in` h0
      /\ (let o = reveal_sbytes (as_seq h1 output) in let i = reveal_sbytes (as_seq h0 input) in
         o == Spec.Chacha20Poly1305.pad_16 i)))
let pad_16_bytes input len =
  (**) let h0 = ST.get() in
  let b = Buffer.create (uint8_to_sint8 0uy) 16ul in
  (**) let h1 = ST.get() in
  Buffer.blit input 0ul b 0ul len;
  (**) let h = ST.get() in
  (**) lemma_modifies_0_1' b h0 h1 h;
  (**) no_upd_lemma_0 h0 h input;
  (**) Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 (U32.v len));
  (**) Seq.lemma_eq_intro (Seq.slice (as_seq h b) (U32.v len) 16) (Seq.create (16 - U32.v len) (uint8_to_sint8 0uy));
  (**) Seq.lemma_eq_intro (reveal_sbytes (as_seq h b)) (Spec.Chacha20Poly1305.pad_16 (reveal_sbytes (as_seq h0 input)));
  b


private let lemma_div (x:nat) : Lemma (16 * (x / 16) <= x /\ 16 * (x / 16) >= 0) =
  Math.Lemmas.lemma_div_mod x 16

inline_for_extraction
let mul_div_16 (len:U32.t) : Tot (len':U32.t{U32.v len' = 16 * (U32.v len / 16)}) =
  lemma_div (U32.v len); Math.Lemmas.lemma_div_mod (U32.v len) 16;
  assert_norm(pow2 4 = 16);
  U32.(16ul *^ (len >>^ 4ul))


private let lemma_pad_last_modifies (h:mem) (acc:buffer Hacl.UInt64.t) : Lemma
  (modifies_1 acc h h) = lemma_intro_modifies_1 acc h h


private val pad_16_block: x:word{Seq.length x < 16 /\ Seq.length x > 0} -> Tot (lbytes 16)
let pad_16_block x = Spec.Chacha20Poly1305.pad_16 x


private val pad_last_spec:
  st:S.poly1305_state_{Hacl.Spe.Poly1305_64.invariant st} ->
  m:word{Seq.length m < 16 /\ Seq.length m > 0} ->
  GTot (st':S.poly1305_state_{Hacl.Spe.Poly1305_64.invariant st'
    /\ (let log  = S.MkState?.log st  in
       let log' = S.MkState?.log st'  in
       let m    = pad_16_block m in log' == Seq.cons m log)})
let pad_last_spec st m =
  let acc = S.MkState?.h st in
  let r   = S.MkState?.r st in
  let log = S.MkState?.log st in
  let m_16 = pad_16_block m in
  let st' = Hacl.Spe.Poly1305_64.poly1305_update_spec st (intro_sbytes (m_16)) in
  let acc' = S.MkState?.h st' in
  let r' = S.MkState?.r st' in
  let log' = S.MkState?.log st' in
  cut (log' == Seq.cons (m_16) log);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval r) (pow2 130 - 5);
  assert_norm (pow2 128 + pow2 128 < pow2 130 - 5); lemma_little_endian_is_bounded m_16;
  let b : Spec.Poly1305.elem = little_endian m_16 + pow2 128 in
  let b' = Spec.Poly1305.encode m_16 in
  Math.Lemmas.modulo_lemma b (pow2 130 - 5);
  cut (S.selem r = S.selem r');
  cut (S.selem acc' = Spec.Poly1305.((S.selem acc +@ b) *@ S.selem r));
  cut (S.selem acc' = Spec.Poly1305.((S.selem acc +@ encode m_16) *@ S.selem r));
  Hacl.Spe.Poly1305_64.lemma_poly1305_blocks_spec_1 (intro_sbytes m_16) log log' (S.selem acc) (Hacl.Spec.Bignum.Bigint.seval r) (S.selem acc');
  st'



val pad_last:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.h) input} ->
  len:U32.t{U32.v len = length input /\ U32.v len < 16} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input
      /\ (let r = as_seq h I.(st.r) in
         let acc = as_seq h I.(st.h) in
         let log = reveal log in
         Hacl.Spe.Poly1305_64.invariant (Hacl.Spec.Poly1305_64.MkState r acc log))
    ))
    (ensures (fun h0 updated_log h1 -> I.live_st h0 st /\ I.live_st h1 st /\ live h0 input
      /\ modifies_1 I.(st.h) h0 h1
      /\ (let r = as_seq h0 I.(st.r) in
         let acc = as_seq h0 I.(st.h) in
         let log = reveal log in
         let acc' = as_seq h1 I.(st.h) in
         let log' = reveal updated_log in
         let m    = reveal_sbytes (as_seq h0 input) in
         Hacl.Spe.Poly1305_64.invariant (Hacl.Spec.Poly1305_64.MkState r acc log)
         /\ Hacl.Spe.Poly1305_64.invariant (Hacl.Spec.Poly1305_64.MkState r acc' log')
         /\ (if U32.v len = 0 then log' == log
           else (let m = pad_16 m in Seq.length m = 16 /\ log' == Seq.cons m log)))
    ))
#reset-options "--max_fuel 0 --z3rlimit 400"
let pad_last log st input len =
  (**) let hinit = ST.get() in
  push_frame();
  (**) assert (U32.v len >= 0 /\ U32.v len < 16);
  (**) let h0 = ST.get() in
  let l =
  if U32.(len =^ 0ul) then (
    let h0 = ST.get() in
    // lemma_pad_last_modifies h0 I.(st.h);
    (**) lemma_modifies_sub_0 h0 h0;
    (**) lemma_modifies_sub_2_1 h0 h0 I.(st.h);
    log
  ) else (
    cut (U32.v len <> 0);
    cut (U32.v len < 16);
    cut (U32.v len > 0 /\ U32.v len < 16);
    let h0 = ST.get() in
    let b = pad_16_bytes input len in
    let h = ST.get() in
    Seq.lemma_eq_intro (as_seq h b) (Seq.slice (as_seq h b) 0 16);
    Hacl.Standalone.Poly1305_64.lemma_poly1305_blocks_spec_1 (S.MkState (as_seq h0 I.(st.r)) (as_seq h0 I.(st.h)) (reveal log)) (as_seq h b) 1uL;
    let l = I.poly1305_update log st b in
    let h1 = ST.get() in
    (**) lemma_modifies_0_1 I.(st.h) h0 h h1;
    l
  ) in
  (**) let h1 = ST.get() in
  pop_frame();
  (**) let hfin = ST.get() in
  (**) modifies_popped_1 I.(st.h) hinit h0 h1 hfin;
  l


#reset-options "--max_fuel 0 --z3rlimit 100"

private val lemma_pad_16_:
  s:Seq.seq U8.t{Seq.length s % 16 = 0 /\ Seq.length s < pow2 32} ->
  Lemma (Spec.Poly1305.encode_bytes (pad_16 s) == Spec.Poly1305.encode_bytes s)
let lemma_pad_16_ s =
  Seq.lemma_eq_intro (Spec.Poly1305.encode_bytes (pad_16 s)) (Spec.Poly1305.encode_bytes (pad_16 s))


private val lemma_pad_16:
  h:mem ->
  b:uint8_p{live h b} ->
  len_16:U32.t{U32.v len_16 = 16 * (length b / 16)} ->
  rem_16:U32.t{U32.v rem_16 = length b % 16} ->
  Lemma (
    U32.v len_16 <= length b /\ U32.v rem_16 + U32.v len_16 = length b /\
    (let x = reveal_sbytes (as_seq h (Buffer.sub b 0ul len_16)) in
     let y = reveal_sbytes (as_seq h (Buffer.sub b len_16 rem_16)) in
     let b = reveal_sbytes (as_seq h b) in
     if U32.v rem_16 = 0 then Spec.Poly1305.encode_bytes (pad_16 b) == Spec.Poly1305.encode_bytes x
     else (Seq.length (pad_16 y) = 16
           /\ Spec.Poly1305.encode_bytes (pad_16 b) == Seq.cons (pad_16 y) (Spec.Poly1305.encode_bytes x))))
let lemma_pad_16 h b len_16 rem_16 =
  Math.Lemmas.lemma_div_mod (length b) 16;
  Seq.lemma_eq_intro (Seq.slice (as_seq h b) 0 (U32.v len_16)) (as_seq h (Buffer.sub b 0ul len_16));
  Seq.lemma_eq_intro (Seq.slice (as_seq h b) (U32.v len_16) (length b)) (as_seq h (Buffer.sub b len_16 rem_16));
  Hacl.Spec.Poly1305_64.Lemmas1.lemma_pad_16 (reveal_sbytes (as_seq h b)) (U32.v len_16) (U32.v rem_16)


#reset-options "--max_fuel 0 --z3rlimit 200"

let poly1305_blocks_init st input len k =
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 15ul)  in
  (**) assert_norm(pow2 4 = 16);
  (**) UInt.logand_mask (U32.v len) 4;
  (**) Math.Lemmas.lemma_div_mod (U32.v len) 16;
  (**) lemma_div (U32.v len);
  let kr = Buffer.sub k 0ul 16ul in
  let len' = mul_div_16 len in
  let part_input = Buffer.sub input 0ul len' in
  let last_block = Buffer.offset input len' in
  (**) assert (length last_block = U32.v rem_16);
  (**) let h0 = ST.get() in
  (**) lemma_disjoint_sub input part_input I.(st.h);
  (**) lemma_disjoint_sub input part_input I.(st.r);
  (**) lemma_disjoint_sub input last_block I.(st.h);
  (**) lemma_disjoint_sub input last_block I.(st.r);
  let l = Poly.poly1305_partial st part_input (Int.Cast.uint32_to_uint64 len_16) kr in
  (**) let h1 = ST.get() in
  (**) lemma_modifies_2_comm I.(st.h) I.(st.r) h0 h1;
  let l' = pad_last l st last_block rem_16 in
  (**) let h2 = ST.get() in
  (**) lemma_modifies_2_1' I.(st.h) I.(st.r) h0 h1 h2;
  (**) lemma_modifies_2_comm I.(st.h) I.(st.r) h0 h2;
  (**) lemma_pad_16 h0 input len' rem_16;
  l'


#reset-options "--max_fuel 0 --z3rlimit 500"

let poly1305_blocks_continue log st input len =
  let len_16 = U32.(len >>^ 4ul) in
  let rem_16 = U32.(len &^ 15ul)  in
  assert_norm(pow2 4 = 16);
  UInt.logand_mask (U32.v len) 4;
  Math.Lemmas.lemma_div_mod (U32.v len) 16;
  lemma_div (U32.v len);
  let len' = mul_div_16 len in
  let part_input = Buffer.sub input 0ul len' in
  let last_block = Buffer.offset input len' in
  (**) lemma_disjoint_sub input part_input I.(st.h);
  (**) lemma_disjoint_sub input part_input I.(st.r);
  (**) lemma_disjoint_sub input last_block I.(st.h);
  (**) lemma_disjoint_sub input last_block I.(st.r);
  let h0 = ST.get() in
  let l = Hacl.Standalone.Poly1305_64.poly1305_blocks log st part_input (Int.Cast.uint32_to_uint64 len_16) in
  let h1 = ST.get() in
  let l' = pad_last l st last_block rem_16 in
  let h2 = ST.get() in
  lemma_pad_16 h0 input len' rem_16;
  Seq.lemma_eq_intro (Seq.append (Spec.Poly1305.encode_bytes (pad_16 (reveal_sbytes (as_seq h0 input))))
                                 (reveal log))
                     (reveal l');
  l'


[@ Substitute]
val poly1305_blocks_finish_:
  log:I.log_t ->
  st:I.poly1305_state ->
  input:uint8_p{disjoint I.(st.h) input /\ length input = 16} ->
  Stack I.log_t
    (requires (fun h -> I.live_st h st /\ live h input
      /\ (let r = as_seq h I.(st.r) in
         let acc = as_seq h I.(st.h) in
         let log = reveal log in
         Hacl.Spe.Poly1305_64.invariant (Hacl.Spec.Poly1305_64.MkState r acc log))
    ))
    (ensures (fun h0 log' h1 -> I.live_st h0 st /\ live h0 input /\ modifies_1 I.(st.h) h0 h1
      /\ I.live_st h1 st
      /\ (let r    = as_seq h0 I.(st.r) in
         let acc  = as_seq h0 I.(st.h) in
         let acc' = as_seq h1 I.(st.h) in
         let log  = reveal log         in
         let log' = reveal log'        in
         let m    = reveal_sbytes (as_seq h0 input)    in
         Hacl.Spe.Poly1305_64.invariant (Hacl.Spec.Poly1305_64.MkState r acc log)
         /\ Hacl.Spe.Poly1305_64.invariant (Hacl.Spec.Poly1305_64.MkState r acc' log')
         /\ log' == Seq.cons m log
         /\ Hacl.Spec.Bignum.Bigint.seval acc' < pow2 130 - 5
         /\ Hacl.Spec.Bignum.AddAndMultiply.bounds acc' S.p44 S.p44 S.p42)
    ))
#reset-options "--max_fuel 0 --z3rlimit 1000"
[@ Substitute]
let poly1305_blocks_finish_ log st input =
  let h = ST.get() in
  Seq.lemma_eq_intro (as_seq h input) (Seq.slice (as_seq h input) 0 16);
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval (as_seq h I.(st.r))) (pow2 130 - 5);
  Hacl.Standalone.Poly1305_64.lemma_poly1305_blocks_spec_1 (S.MkState (as_seq h I.(st.r)) (as_seq h I.(st.h)) (reveal log)) (as_seq h input) 1uL;
  let log' = I.poly1305_update log st input in
  Hacl.Spe.Poly1305_64.poly_def_1 (reveal log') (Hacl.Spec.Bignum.Bigint.seval (as_seq h I.(st.r)));
  cut (reveal log' == Seq.cons (reveal_sbytes (as_seq h input)) (reveal log));
  I.poly1305_update_last log' st (Buffer.offset input 16ul) 0uL;
  log'


#reset-options "--max_fuel 0 --z3rlimit 100"

let poly1305_blocks_finish log st input mac key_s =
  let h = ST.get() in
  let _ = poly1305_blocks_finish_ log st input in
  let h' = ST.get() in
  Math.Lemmas.modulo_lemma (Hacl.Spec.Bignum.Bigint.seval (as_seq h' I.(st.h))) (pow2 130 - 5);
  cut (Hacl.Spec.Bignum.Bigint.seval (as_seq h' I.(st.h)) = Spec.Poly1305.poly (Seq.cons (reveal_sbytes (as_seq h input)) (reveal log)) (Hacl.Spec.Bignum.Bigint.seval (as_seq h I.(st.r))));
  I.poly1305_finish st mac key_s
