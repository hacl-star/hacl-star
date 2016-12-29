module Hacl.MAC.Poly1305_64

open FStar.Mul
open FStar.ST
open FStar.Buffer
open FStar.Ghost
open FStar.SeqProperties
open FStar.HyperStack

open Hacl.Cast
open Hacl.Bignum.Parameters
open Hacl.Spec.Bignum.Bigint
open Hacl.Spec.Bignum.AddAndMultiply
open Hacl.Bignum.AddAndMultiply

module H8   = Hacl.UInt8
module Limb = Hacl.Bignum.Limb
module Wide = Hacl.Bignum.Wide
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

inline_for_extraction let log_t = unit

inline_for_extraction let bigint = felem
inline_for_extraction let uint8_p = buffer Hacl.UInt8.t

let elemB : Type0 = b:felem

let wordB = b:uint8_p{length b <= 16}
let wordB_16 = b:uint8_p{length b = 16}

noeq type poly1305_state = | MkState: r:bigint -> h:bigint -> poly1305_state

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val load64_le:
  b:uint8_p{length b = 8} ->
  Stack limb
    (requires (fun h -> live h b))
    (ensures  (fun h0 r h1 -> h0 == h1 /\ live h0 b
      (* /\ Limb.v r = little_endian (as_seq h0 b) *)
      ))
let load64_le b =
  let h = ST.get() in
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  cut (b0 == get h b 0);
  cut (b1 == get h b 1);
  cut (b2 == get h b 2);
  cut (b3 == get h b 3);
  cut (b4 == get h b 4);
  cut (b5 == get h b 5);
  cut (b6 == get h b 6);
  cut (b7 == get h b 7);
  (* lemma_little_endian_8 h b; *)
  (* lemma_load64_le b0 b1 b2 b3 b4 b5 b6 b7; *)
  Limb.(
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )


val store64_le:
  b:uint8_p{length b = 8} ->
  z:Limb.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      (* /\ Limb.v z = little_endian (as_seq h1 b) *)
      ))
let store64_le b z =
  let open Hacl.UInt64 in
  let b0 = sint64_to_sint8 z in
  let b1 = sint64_to_sint8 (z >>^ 8ul) in
  let b2 = sint64_to_sint8 (z >>^ 16ul) in
  let b3 = sint64_to_sint8 (z >>^ 24ul) in
  let b4 = sint64_to_sint8 (z >>^ 32ul) in
  let b5 = sint64_to_sint8 (z >>^ 40ul) in
  let b6 = sint64_to_sint8 (z >>^ 48ul) in
  let b7 = sint64_to_sint8 (z >>^ 56ul) in
  b.(0ul) <- b0;
  b.(1ul) <- b1;
  b.(2ul) <- b2;
  b.(3ul) <- b3;
  b.(4ul) <- b4;
  b.(5ul) <- b5;
  b.(6ul) <- b6;
  b.(7ul) <- b7;
  let h1 = ST.get() in
  cut (b0 == get h1 b 0);
  cut (b1 == get h1 b 1);
  cut (b2 == get h1 b 2);
  cut (b3 == get h1 b 3);
  cut (b4 == get h1 b 4);
  cut (b5 == get h1 b 5);
  cut (b6 == get h1 b 6);
  cut (b7 == get h1 b 7);
  (* lemma_little_endian_8 h1 b; *)
  (* lemma_store64_le_ z; *)
  ()


val sel_word:
  h:mem ->
  b:wordB{live h b} ->
  GTot (s:Seq.seq H8.t{Seq.length s = length b
    /\ (forall (i:nat). {:pattern (Seq.index s i)}
      i < Seq.length s ==> H8.v (Seq.index s i) == H8.v (get h b i))})
let sel_word h b = as_seq h b

(* (\** From the current memory state, returns the field element corresponding to a elemB *\) *)
(* val sel_elem: h:mem -> b:elemB{live h b} -> GTot elem *)
(* let sel_elem h b = eval h b % p_1305 *)

(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo) *)
val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
let sel_int h b = eval h b


let live_st m (st:poly1305_state) : Type0 =
  live m st.h /\ live m st.r /\ disjoint st.h st.r

(* let acc_inv h (log:log_t) (st:poly1305_state) : Type0 = *)
(*   live_st h st /\ sel_elem h st.h == poly' (Ghost.reveal log) (sel_elem h st.r) *)


(* let limb_44 = x:limb{Limb.v x < pow2 44} *)
(* let limb_45 = x:limb{Limb.v x < pow2 45} *)
(* let limb_44_20 = x:limb{Limb.v x < 20 * pow2 44} *)


#reset-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

val mk_mask: nbits:U32.t{U32.v nbits < 64} -> Tot (z:limb{Limb.v z = pow2 (U32.v nbits) - 1})
let mk_mask nbits =
  Math.Lemmas.pow2_lt_compat 64 (U32.v nbits);
  cut( (1*pow2 (U32.v nbits)) % pow2 64 = pow2 (U32.v nbits));
  let one = uint64_to_sint64 1uL in
  Limb.((one <<^ nbits) -^ one)


(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


#reset-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1"

private val to_vec_lt_pow2: #n:nat -> a:UInt.uint_t n -> m:nat -> i:nat{i < n - m} ->
  Lemma (requires (a < pow2 m))
        (ensures  (Seq.index (UInt.to_vec a) i == false))
        [SMTPat (Seq.index (UInt.to_vec #n a) i); SMTPatT (a < pow2 m)]
let rec to_vec_lt_pow2 #n a m i =
  if n = 0 then ()
  else
    if m = 0 then
      assert (a == UInt.zero n)
    else
      begin
      Seq.lemma_index_app1 (UInt.to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
      assert (Seq.index (UInt.to_vec a) i == Seq.index (UInt.to_vec #(n - 1) (a / 2)) i);
      to_vec_lt_pow2 #(n - 1) (a / 2) (m - 1) i
      end

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

assume val lemma_logand_lt: #n:pos -> a:UInt.uint_t n -> m:pos{m < n} -> b:UInt.uint_t n{b < pow2 m} ->
  Lemma (pow2 m < pow2 n /\ UInt.logand #n a b < pow2 m)

val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r /\ live h0 key
      /\ red_44 (as_seq h1 r)
      (* /\ sel_elem h1 r = Hacl.Symmetric.Poly1305_64.FC.Spec.clamp (sel_word h0 (sub key 0ul 16ul)) *)
    ))
let poly1305_encode_r r key =
  let t0 = load64_le(sub key 0ul 8ul) in
  let t1 = load64_le(sub key 8ul 8ul) in
  let open Hacl.Bignum.Limb in
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 42 = 0x40000000000);
  let r0 = ( t0                           ) &^ uint64_to_limb 0xffc0fffffffuL in
  let r1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_limb 0xfffffc0ffffuL in
  let r2 = ((t1 >>^ 24ul)                 ) &^ uint64_to_limb 0x00ffffffc0fuL in
  r.(0ul) <- r0;
  r.(1ul) <- r1;
  r.(2ul) <- r2;
  lemma_logand_lt #64 (v t0) 44 0xffc0fffffff;
  lemma_logand_lt #64 (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44 0xfffffc0ffff;
  lemma_logand_lt #64 (v (t1 >>^ 24ul)) 42 0x00ffffffc0f


inline_for_extraction let mask_42 : p:Hacl.Bignum.Limb.t{v p = pow2 42 - 1} = assert_norm(pow2 42 - 1 = 0x3ffffffffff); assert_norm(pow2 64 = 0x10000000000000000); uint64_to_limb 0x3ffffffffffuL
  
inline_for_extraction let mask_44 : p:Hacl.Bignum.Limb.t{v p = pow2 44 - 1} = assert_norm(pow2 44 - 1 = 0xfffffffffff);
  assert_norm (pow2 64 = 0x10000000000000000); uint64_to_limb 0xfffffffffffuL


val toField:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      /\ red_44 (as_seq h1 b)
      /\ v (Seq.index (as_seq h1 b) 2) < pow2 40))
let toField b m =
  (* Load block values *)
  let t0 = load64_le (Buffer.sub m 0ul 8ul) in
  let t1 = load64_le (Buffer.sub m 8ul 8ul) in
  let open Hacl.UInt64 in  
  UInt.logand_mask (v t0) 44;
  UInt.logand_mask (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44;
  Math.Lemmas.lemma_div_lt (v t1) 64 24;
  Math.Lemmas.pow2_lt_compat 44 40;
  let t_0 = t0 &^ mask_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_44 in
  let t_2 = (t1 >>^ 24ul) in
  b.(0ul) <- t_0;
  b.(1ul) <- t_1;
  b.(2ul) <- t_2


val toField_plus_2_128:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b
      /\ red_44 (as_seq h1 b)))
let toField_plus_2_128 b m =
  toField b m;
  let b2 = b.(2ul) in
  let open Hacl.Bignum.Limb in
  assert_norm (pow2 40 = 0x10000000000);
  UInt.logor_disjoint (0x10000000000) (v b2) 40;
  assert_norm (pow2 40 + pow2 40 < pow2 44);
  let b2' = uint64_to_limb 0x10000000000uL |^ b2 in
  b.(2ul) <- b2'


val toField_plus:
  len:U32.t{U32.v len < 16} ->
  b:bigint ->
  m:wordB{length m = U32.v len} ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let toField_plus len b m' =
  (* Load block values *)
  push_frame();
  let m = create (uint8_to_sint8 0uy) 16ul in
  blit m' 0ul m 0ul len;
  toField b m;
  let b2 = b.(2ul) in
  let open Hacl.Bignum.Limb in
  let b2 = b2 |^ (uint64_to_sint64 1uL <<^ (U32.(24ul+^ len))) in
  b.(2ul) <- b2;
  pop_frame()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"


val poly1305_finish:
  mac:uint8_p ->
  acc:felem ->
  key_s:uint8_p{length key_s = 16} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h acc /\ live h key_s /\ red_45 (as_seq h acc)))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ live h1 acc
      /\ modifies_2 mac acc h0 h1))
let poly1305_finish mac acc key_s =
  push_frame();
  let tmp = create limb_zero clen in
  (* Full carry pass *)
  Math.Lemmas.pow2_lt_compat 63 44;
  Hacl.Bignum.Fproduct.carry_limb_ acc 0ul;
  let h1 = ST.get() in
  assume (v (Seq.index (as_seq h1 acc) 2) < pow2 45 + pow2 20);
  assert_norm(pow2 45 + pow2 20 = 0x200000000000 + 0x100000);
  assert_norm(pow2 42 = 0x40000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 64 = 0x10000000000000000);
  Hacl.Bignum.Modulo.carry_top acc;
  Hacl.Bignum.Fproduct.carry_0_to_1 acc;
  (* Adding 2nd part of the key (one time pad) *)
  toField tmp key_s;
  Hacl.Bignum.Fsum.fsum_ acc tmp clen;
  (* Last carry and truncation *)
  Hacl.Bignum.Fproduct.carry_limb_ acc 0ul;
  let h0 = acc.(0ul) in
  let h1 = acc.(1ul) in
  let h2 = acc.(2ul) in
  let open Hacl.Bignum.Limb in
  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ ((h2 &^ mask_42) <<^ 24ul) in
  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  pop_frame()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_start:
  a:elemB ->
  Stack unit
    (requires (fun h -> live h a))
    (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
      /\ red_45 (as_seq h1 a)
      /\ sel_int h1 a = 0
      ))
let poly1305_start a =
  (* Zeroing the accumulator *)
  a.(0ul) <- limb_zero;
  a.(1ul) <- limb_zero;
  a.(2ul) <- limb_zero;
  let h = ST.get() in
  lemma_seval_def (as_seq h a) 3;
  lemma_seval_def (as_seq h a) 2;
  lemma_seval_def (as_seq h a) 1;
  lemma_seval_def (as_seq h a) 0

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val poly1305_init:
  r:elemB ->
  s:wordB_16{disjoint r s} ->
  key:uint8_p{length key = 32 /\ disjoint s key /\ disjoint key r} ->
  Stack unit
    (requires (fun h -> live h r /\ live h s /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_2 r s h0 h1 /\ live h1 r /\ live h1 s
      /\ red_44 (as_seq h1 r)))
let poly1305_init r s key =
  let t0 = load64_le(sub key 0ul 8ul) in
  let t1 = load64_le(sub key 8ul 8ul) in
  let open Hacl.UInt64 in
  assert_norm(pow2 64 = 0x10000000000000000);
  assert_norm(pow2 44 = 0x100000000000);
  assert_norm(pow2 42 = 0x40000000000);
  r.(0ul) <- ( t0                           ) &^ uint64_to_sint64 0xffc0fffffffuL;
  r.(1ul) <- ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_sint64 0xfffffc0ffffuL;
  r.(2ul) <- ((t1 >>^ 24ul)                 ) &^ uint64_to_sint64 0x00ffffffc0fuL;
  lemma_logand_lt #64 (v t0) 44 0xffc0fffffff;
  lemma_logand_lt #64 (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44 0xfffffc0ffff;
  lemma_logand_lt #64 (v (t1 >>^ 24ul)) 42 0x00ffffffc0f;
  blit key 16ul s 0ul 16ul


(* ******************* *)
(* Fast implementation *)
(* ******************* *)


val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key /\ red_45 (as_seq h st.h) /\ disjoint st.r key
      /\ disjoint st.h key))
    (ensures  (fun h0 log h1 -> modifies_2 st.r st.h h0 h1
      /\ live h1 st.r /\ live h1 st.h /\ red_44 (as_seq h1 st.r) /\ red_45 (as_seq h1 st.h)
      (* /\ acc_inv h1 log st *)
      ))
let poly1305_init_ st key =
  poly1305_encode_r st.r (sub key 0ul 16ul);
  poly1305_start st.h


val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m >= 16} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint m st.h /\ disjoint m st.r
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      (* /\ acc_inv h current_log st *)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st
      /\ red_45 (as_seq h1 st.h)
      (* /\ acc_inv h1 updated_log st *)
      (* /\ (reveal updated_log) == *)
      (*     SeqProperties.snoc (reveal current_log) (encode (sel_word h1 (Buffer.sub m 0ul 16ul))) *)
      (* /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r) *)
      ))
let poly1305_update log st m =
  push_frame();
  let tmp = create limb_zero clen in
  let acc = st.h in
  let r   = st.r in
  toField_plus_2_128 tmp (sub m 0ul 16ul);
  add_and_multiply acc tmp r;
  let new_log = (* elift1 (fun l -> SeqProperties.snoc l (eval_3_limbs h0 h1 h2)) log in *) () in
  pop_frame();
  new_log


val poly1305_blocks:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len <= length m} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m /\ disjoint st.r m /\ disjoint st.h m
      /\ red_45 (as_seq h st.h)
      /\ red_44 (as_seq h st.r)
      (* /\ acc_inv h current_log st *)
      ))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st
      /\ red_45 (as_seq h1 st.h)
      (* /\ acc_inv h1 updated_log st *)
      (* /\ (reveal updated_log) == *)
      (*     encode_pad (reveal current_log) (as_seq h0 (Buffer.sub m 0ul (Int.Cast.uint64_to_uint32 len))) *)
      (* /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r) *)
      ))
let rec poly1305_blocks log st m len =
  let m0 = ST.get() in
  if U64.(len <^ 16uL) then (
    (* log *)
    ()
  )
  else (
    let new_log = poly1305_update log st m in
    let len = U64.(len -^ 16uL) in
    let m   = offset m 16ul in
    poly1305_blocks new_log st m len
  )


val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p ->
  m:uint8_p ->
  len:U64.t{U64.v len < pow2 32 /\ U64.v len <= length m} ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun h -> (* acc_inv h log st *)live_st h st /\ live h mac /\ live h m /\ live h key_s
      /\ disjoint st.h mac
      /\ red_44 (as_seq h st.r) /\ red_45 (as_seq h st.h)))
    (ensures  (fun h0 updated_log h1 -> modifies_2 st.h mac h0 h1
      /\ live h1 st.h /\ live h1 mac
      (* /\ acc_inv h1 updated_log st *)
      ))
let poly1305_finish_ log st mac m len key_s =
  push_frame();
  let tmp   = create limb_zero clen in
  let rem' = U64.(len &^ 0xfuL) in
  assert_norm(pow2 4 - 1 = 0xf);
  UInt.logand_mask (U64.v len) 4;
  if U64.(rem' =^ 0uL) then ()
  else (
    let zero = uint8_to_sint8 0uy in
    let block = create zero 16ul in
    let i = FStar.Int.Cast.uint64_to_uint32 rem' in
    Math.Lemmas.modulo_lemma (U64.v len - U64.v rem') (pow2 32);
    blit m (FStar.Int.Cast.uint64_to_uint32 (U64.(len -^ rem'))) block 0ul i;
    block.(i) <- uint8_to_sint8 1uy;
    toField tmp block;
    add_and_multiply st.h tmp st.r
    );
  Hacl.Bignum.Fproduct.carry_limb_ st.h 0ul;
  Hacl.Bignum.Modulo.carry_top st.h;
  Hacl.Bignum.Fproduct.carry_0_to_1 st.h;
  toField tmp key_s;
  Hacl.Bignum.Fsum.fsum_ st.h tmp clen;
  Hacl.Bignum.Fproduct.carry_limb_ st.h 0ul;
  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let open Hacl.Bignum.Limb in
  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ ((h2 &^ mask_42) <<^ 24ul) in
  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  pop_frame();
  log // TODO



(* val poly1305_init_: *)
(*   st:poly1305_state -> *)
(*   key:uint8_p{length key = 32 (\* /\ disjoint st key *\)} -> *)
(*   Stack unit *)
(*     (requires (fun h -> (\* live h st /\  *\)live h key)) *)
(*     (ensures  (fun h0 _ h1 -> true(\* live h1 st /\ modifies_1 st h0 h1 *\))) *)
(* let poly1305_init_ st key = *)
(*   let r = st.r in *)
(*   let h = st.h in *)
(*   let t0 = load64_le(key) in *)
(*   let t1 = load64_le(offset key 8ul) in *)
(*   let open Hacl.UInt64 in *)
(*   r.(0ul) <- ( t0                           ) &^ uint64_to_sint64 0xffc0fffffffuL; *)
(*   r.(1ul) <- ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_sint64 0xfffffc0ffffuL; *)
(*   r.(2ul) <- ((t1 >>^ 24ul)                 ) &^ uint64_to_sint64 0x00ffffffc0fuL; *)
(*   let zero = uint64_to_sint64 0uL in *)
(*   h.(0ul) <- zero; *)
(*   h.(1ul) <- zero; *)
(*   h.(2ul) <- zero *)


(* #reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50" *)

(* val poly1305_blocks_loop: *)
(*   st:poly1305_state -> *)
(*   m:uint8_p{disjoint m st} -> *)
(*   len:U64.t{U64.v len <= length m} -> *)
(*   r0:h64 -> *)
(*   r1:h64 -> *)
(*   r2:h64 -> *)
(*   s1:h64 -> *)
(*   s2:h64 -> *)
(*   h0:h64 -> *)
(*   h1:h64 -> *)
(*   h2:h64 -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h st /\ live h m)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 (sub st 3ul 3ul) h0 h1)) *)
(* let rec poly1305_blocks_loop st m len r0 r1 r2 s1 s2 h0 h1 h2 = *)
(*   let h = sub st 3ul 3ul in *)
(*   if U64.(len <^ 16uL) then ( *)
(*     h.(0ul) <- h0; *)
(*     h.(1ul) <- h1; *)
(*     h.(2ul) <- h2 *)
(*   ) *)
(*   else ( *)
(*     let t0 = load64_le m in *)
(*     let t1 = load64_le (offset m 8ul) in *)
(*     let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in *)
(*     let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in *)
(*     let open Hacl.UInt64 in *)
(*     let h0 = h0 +%^ (t0 &^ mask_2_44) in *)
(*     let h1 = h1 +%^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) in *)
(*     let h2 = h2 +%^ (((t1 >>^ 24ul) &^ mask_2_42) |^ (uint64_to_sint64 1uL <<^ 40ul)) in *)
(*     let open Hacl.UInt128 in *)
(*     let d0 = h0 *^ r0 in *)
(*     let d  = h1 *^ s2 in *)
(*     let d0 = d0 +%^ d in *)
(*     let d  = h2 *^ s1 in *)
(*     let d0 = d0 +%^ d in *)
(*     let d1 = h0 *^ r1 in *)
(*     let d  = h1 *^ r0 in *)
(*     let d1 = d1 +%^ d in *)
(*     let d  = h2 *^ s2 in *)
(*     let d1 = d1 +%^ d in *)
(*     let d2 = h0 *^ r2 in *)
(*     let d  = h1 *^ r1 in *)
(*     let d2 = d2 +%^ d in *)
(*     let d  = h2 *^ r0 in *)
(*     let d2 = d2 +%^ d in *)
(*     let c  = sint128_to_sint64 (d0 >>^ 44ul) in *)
(*     let h0 = H64.(sint128_to_sint64 d0 &^ mask_2_44) in *)
(*     let d1 = d1 +%^ sint64_to_sint128 c in *)
(*     let c  = sint128_to_sint64 (d1 >>^ 44ul) in *)
(*     let h1 = H64.(sint128_to_sint64 d1 &^ mask_2_44) in *)
(*     let d2 = d2 +%^ sint64_to_sint128 c in *)
(*     let c  = sint128_to_sint64 (d2 >>^ 42ul) in *)
(*     let h2 = H64.(sint128_to_sint64 d2 &^ mask_2_42) in *)
(*     let open Hacl.UInt64 in *)
(*     let h0 = h0 +%^ (c *%^ uint64_to_sint64 5uL) in *)
(*     let c  = h0 >>^ 44ul in *)
(*     let h0 = h0 &^ mask_2_44 in *)
(*     let h1 = h1 +%^ c in *)
(*     let len = U64.(len -^ 16uL) in *)
(*     let m   = offset m 16ul in *)
(*     poly1305_blocks_loop st m len r0 r1 r2 s1 s2 h0 h1 h2 *)
(*   ) *)


(* val poly1305_blocks: *)
(*   st:poly1305_state -> *)
(*   m:uint8_p{disjoint m st} -> *)
(*   len:FStar.UInt64.t{U64.v len <= length m} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h m /\ live h st)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 (sub st 3ul 3ul) h0 h1)) *)
(* let poly1305_blocks st m len = *)
(*   let r = sub st 0ul 3ul in *)
(*   let h = sub st 3ul 3ul in *)
(*   let r0 = r.(0ul) in *)
(*   let r1 = r.(1ul) in *)
(*   let r2 = r.(2ul) in *)
(*   let h0 = h.(0ul) in *)
(*   let h1 = h.(1ul) in *)
(*   let h2 = h.(2ul) in *)
(*   let five = uint64_to_sint64 5uL in *)
(*   let s1 = H64.(r1 *%^ (five <<^ 2ul)) in *)
(*   let s2 = H64.(r2 *%^ (five <<^ 2ul)) in *)
(*   poly1305_blocks_loop st m len r0 r1 r2 s1 s2 h0 h1 h2; *)
(*   () *)


(* #reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50" *)


(* val poly1305_finish_: *)
(*   m:uint8_p -> *)
(*   len:U64.t{U64.v len <= length m /\ U64.v len < 16} -> *)
(*   st:poly1305_state -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h m /\ live h st)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 st /\ modifies_1 (sub st 3ul 3ul) h0 h1)) *)
(* let poly1305_finish_ m rem st = *)
(*   push_frame(); *)
(*   let r = sub st 0ul 3ul in *)
(*   let h = sub st 3ul 3ul in *)
(*   let h0 = h.(0ul) in *)
(*   let h1 = h.(1ul) in *)
(*   let h2 = h.(2ul) in *)
(*   let r0 = r.(0ul) in *)
(*   let r1 = r.(1ul) in *)
(*   let r2 = r.(2ul) in *)
(*   let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in *)
(*   let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in *)
(*   let five = uint64_to_sint64 5uL in *)
(*   let s1 = H64.(r1 *%^ (five <<^ 2ul)) in *)
(*   let s2 = H64.(r2 *%^ (five <<^ 2ul)) in *)
(*   let zero = Hacl.Cast.uint8_to_sint8 0uy in *)
(*   let block = create zero 16ul in *)
(*   let i = FStar.Int.Cast.uint64_to_uint32 rem in *)
(*   assert_norm(pow2 4 = 16); Math.Lemmas.pow2_lt_compat 32 4; *)
(*   Math.Lemmas.modulo_lemma (FStar.UInt64.v rem) (pow2 32); *)
(*   blit m 0ul block 0ul i; *)
(*   block.(i) <- uint8_to_sint8 1uy; *)
(*   let t0 = load64_le block in *)
(*   let t1 = load64_le (offset block 8ul) in *)
(*   let open Hacl.UInt64 in *)
(*   let h0 = h0 +%^ (t0 &^ mask_2_44) in *)
(*   let h1 = h1 +%^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) in *)
(*   let h2 = h2 +%^ ((t1 >>^ 24ul) &^ mask_2_42) in *)
(*   let open Hacl.UInt128 in *)
(*   let d0 = h0 *^ r0 in *)
(*   let d  = h1 *^ s2 in *)
(*   let d0 = d0 +%^ d  in *)
(*   let d  = h2 *^ s1 in *)
(*   let d0 = d0 +%^ d  in *)
(*   let d1 = h0 *^ r1 in *)
(*   let d  = h1 *^ r0 in *)
(*   let d1 = d1 +%^ d  in *)
(*   let d  = h2 *^ s2 in *)
(*   let d1 = d1 +%^ d  in *)
(*   let d2 = h0 *^ r2 in *)
(*   let d  = h1 *^ r1 in *)
(*   let d2 = d2 +%^ d  in *)
(*   let d  = h2 *^ r0 in *)
(*   let d2 = d2 +%^ d  in *)
(*   let c  = sint128_to_sint64 (d0 >>^ 44ul) in *)
(*   let h0 = H64.(sint128_to_sint64 d0 &^ mask_2_44) in *)
(*   let d1 = d1 +%^ sint64_to_sint128 c in *)
(*   let c  = sint128_to_sint64 (d1 >>^ 44ul) in *)
(*   let h1 = H64.(sint128_to_sint64 d1 &^ mask_2_44) in *)
(*   let d2 = d2 +%^ sint64_to_sint128 c in *)
(*   let c  = sint128_to_sint64 (d2 >>^ 42ul) in *)
(*   let h2 = H64.(sint128_to_sint64 d2 &^ mask_2_42) in *)
(*   let open Hacl.UInt64 in *)
(*   let h0 = h0 +%^ (c *%^ uint64_to_sint64 5uL) in *)
(*   let c  = h0 >>^ 44ul in *)
(*   let h0 = h0 &^ mask_2_44 in *)
(*   let h1 = h1 +%^ c in *)
(*   h.(0ul) <- h0; *)
(*   h.(1ul) <- h1; *)
(*   h.(2ul) <- h2; *)
(*   pop_frame() *)


(* #reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50" *)

(* val poly1305_finish__: *)
(*   mac:uint8_p{length mac = 16} -> *)
(*   key:uint8_p{length key = 32 /\ disjoint mac key} -> *)
(*   st:poly1305_state{disjoint st key} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h mac /\ live h key /\ live h st)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 st /\ live h1 mac /\ modifies_1 mac h0 h1)) *)
(* let poly1305_finish__ mac key st = *)
(*   let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in *)
(*   let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in *)
(*   let h = sub st 3ul 3ul in *)
(*   let h0 = h.(0ul) in *)
(*   let h1 = h.(1ul) in *)
(*   let h2 = h.(2ul) in *)
(*   let open Hacl.UInt64 in *)
(*   let c  = h1 >>^ 44ul in *)
(*   let h1 = h1 &^ mask_2_44 in *)
(*   let h2 = h2 +%^ c in *)
(*   let c  = h2 >>^ 42ul in *)
(*   let h2 = h2 &^ mask_2_42 in *)
(*   let h0 = h0 +%^ (c *%^ uint64_to_sint64 5uL) in *)
(*   let c  = h0 >>^ 44ul in *)
(*   let h0 = h0 &^ mask_2_44 in *)
(*   let h1 = h1 +%^ c in *)
(*   let c  = h1 >>^ 44ul in *)
(*   let h1 = h1 &^ mask_2_44 in *)
(*   let h2 = h2 +%^ c in *)
(*   let c  = h2 >>^ 42ul in *)
(*   let h2 = h2 &^ mask_2_42 in *)
(*   let h0 = h0 +%^ (c *%^ uint64_to_sint64 5uL) in *)
(*   let c  = h0 >>^ 44ul in *)
(*   let h0 = h0 &^ mask_2_44 in *)
(*   let h1 = h1 +%^ c in *)
(*   let mask = (eq_mask h0 mask_2_44) *)
(*              &^ (eq_mask h1 mask_2_44) *)
(*              &^ (gte_mask h2 (uint64_to_sint64 0x3fffffffffbuL)) in *)
(*   let h0 = h0 &^ lognot mask in *)
(*   let h1 = h1 &^ lognot mask in *)
(*   let h2 = h2 -%^ ((uint64_to_sint64 0x3fffffffffbuL) &^ mask) in *)
(*   let t0 = load64_le (offset key 16ul) in *)
(*   let t1 = load64_le (offset key 24ul) in *)
(*   let h0 = h0 +%^ (t0 &^ mask_2_44) in *)
(*   let c  = h0 >>^ 44ul in *)
(*   let h0 = h0 &^ mask_2_44 in *)
(*   let h1 = h1 +%^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) +%^ c in *)
(*   let c  = h1 >>^ 44ul in *)
(*   let h1 = h1 &^ mask_2_44 in *)
(*   let h2 = h2 +%^ ((t1 >>^ 24ul) &^ mask_2_42) +%^ c in *)
(*   let h2 = h2 &^ mask_2_42 in *)
(*   let h0 = h0 |^ (h1 <<^ 44ul) in *)
(*   let h1 = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in *)
(*   store64_le mac h0; *)
(*   store64_le (offset mac 8ul) h1; *)
(*   () *)


(* val poly1305_finish: *)
(*   mac:uint8_p{length mac = 16} -> *)
(*   m:uint8_p{disjoint m mac} -> *)
(*   len:U64.t{U64.v len <= length m} -> *)
(*   key:uint8_p{length key = 32 /\ disjoint mac key} -> *)
(*   st:poly1305_state{disjoint st key /\ disjoint st mac} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h mac /\ live h m /\ live h key /\ live h st)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 st /\ live h1 mac /\ modifies_2 mac (sub st 3ul 3ul) h0 h1)) *)
(* let poly1305_finish mac m len key st = *)
(*   let m0 = ST.get() in *)
(*   let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in *)
(*   let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in *)
(*   let remainder = U64.(len &^ 0xfuL) in *)
(*   let r = sub st 0ul 3ul in *)
(*   let h = sub st 3ul 3ul in *)
(*   if U64.(remainder =^ 0uL) then ( *)
(*     let m' = ST.get() in *)
(*     lemma_intro_modifies_1 h m0 m') *)
(*   else ( *)
(*     UInt.logand_mask (U64.v len) 4; *)
(*     assert_norm(pow2 4 = 16); *)
(*     Math.Lemmas.euclidean_division_definition (U64.v len) 16; *)
(*     assert_norm (pow2 32 = 4294967296); *)
(*     Math.Lemmas.modulo_lemma (U64.v len - U64.v remainder) (pow2 32); *)
(*     let m = offset m (Int.Cast.uint64_to_uint32 (U64.(len -^ remainder))) in *)
(*     poly1305_finish_ m remainder st *)
(*     ); *)
(*   poly1305_finish__ mac key st *)


(* val crypto_onetimeauth: *)
(*   mac:uint8_p{length mac = 16} -> *)
(*   input:uint8_p{disjoint input mac} -> *)
(*   len:U64.t{U64.v len <= length input} -> *)
(*   k:uint8_p{length k = 32 /\ disjoint k mac} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h mac /\ live h input /\ live h k)) *)
(*     (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1)) *)
(* let crypto_onetimeauth output input len k = *)
(*   push_frame(); *)
(*   let zero = uint64_to_sint64 0uL in *)
(*   let st = create zero 6ul in // 3 limbs for the key, 3 limbs for the accumulator *)
(*   poly1305_init st k; *)
(*   poly1305_blocks st input len; *)
(*   poly1305_finish output input len k st; *)
(*   pop_frame() *)


val crypto_onetimeauth:
  output:uint8_p ->
  input:uint8_p ->
  len:U64.t ->
  k:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let crypto_onetimeauth output input len k =
  push_frame();
  let zero = uint64_to_sint64 0uL in
  let r = create zero clen in
  let h = create zero clen in
  let st = MkState r h in
  (* let st = {r = r; h = h} in *)
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st key_r in
  let partial_log = poly1305_blocks init_log st input len in
  let final_log = poly1305_finish_ partial_log st output input len key_s in
  pop_frame()
