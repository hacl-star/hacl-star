module Hacl.Chacha20Poly1305

open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast
open Hacl.Spec.Endianness
open FStar.Endianness
open Hacl.Endianness

open Spec.Chacha20Poly1305

(* Module abbreviations *)
module ST = FStar.HyperStack.ST
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64


(* The following values should point to Spec.Chacha20Poly1305 *)

#reset-options "--max_fuel 0 --z3rlimit 400"

private val lemma_aead_encrypt_poly:
  h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem ->
  r:buffer Hacl.UInt64.t -> acc:buffer Hacl.UInt64.t -> mac:uint8_p ->
  Lemma (requires (live h0 mac /\ (r `unused_in` h0) /\ (acc `unused_in`h0)
    /\ live h1 mac /\ live h1 r /\ live h1 acc
    /\ live h2 mac /\ live h2 r /\ live h2 acc
    /\ live h3 mac /\ live h3 r /\ live h3 acc
    /\ live h4 mac /\ live h4 r /\ live h4 acc
    /\ modifies_0 h0 h1 /\ modifies_2 r acc h1 h2 /\ modifies_1 acc h2 h3 /\ modifies_2 mac acc h3 h4))
        (ensures (modifies_2_1 mac h0 h4))
private let lemma_aead_encrypt_poly h0 h1 h2 h3 h4 r acc mac =
  lemma_reveal_modifies_0 h0 h1;
  lemma_reveal_modifies_2 r acc h1 h2;
  lemma_reveal_modifies_1 acc h2 h3;
  lemma_reveal_modifies_2 mac acc h3 h4;
  lemma_intro_modifies_2_1 mac h0 h4


open FStar.Mul
open FStar.Endianness 

private val lemma_aead_encrypt_poly_2:
  k:Spec.Poly1305.key ->
  mac:Spec.Poly1305.tag ->
  aad:Seq.seq H8.t{Seq.length aad < pow2 32} ->
  c:Seq.seq H8.t{Seq.length c < pow2 32} ->
  lb:Spec.Poly1305.word_16 ->
  Lemma (requires (
    let r = Spec.Poly1305.encode_r (slice k 0 16) in
    let s = little_endian (slice k 16 32) in
    let c = reveal_sbytes c in
    let aad = reveal_sbytes aad in
    little_endian mac = (Spec.Poly1305.poly (Seq.cons lb (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad))) r + s) % pow2 128))
        (ensures (mac == Spec.Poly1305.poly1305 (pad_16 (reveal_sbytes aad) @| pad_16 (reveal_sbytes c) @| lb) k))
let lemma_aead_encrypt_poly_2 k mac aad c lb =
  let aad = reveal_sbytes aad in
  let c   = reveal_sbytes c   in
  Math.Lemmas.lemma_div_mod (Seq.length (pad_16 aad)) 16;
  Hacl.Spec.Poly1305_64.Lemmas1.lemma_encode_bytes_append (pad_16 aad) (pad_16 c) (Seq.length (pad_16 aad) / 16);
  cut (Spec.Poly1305.encode_bytes (pad_16 aad @| pad_16 c) == Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad));
  let s = (pad_16 aad @| pad_16 c) in
  Seq.lemma_eq_intro (pad_16 aad @| pad_16 c @| lb) ((pad_16 aad @| pad_16 c) @| lb);
  Hacl.Spec.Poly1305_64.Lemmas1.encode_bytes_append (Seq.length s) s lb;  
  cut (Seq.cons lb (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad))
    == Spec.Poly1305.encode_bytes (pad_16 aad @| pad_16 c @| lb));
  lemma_little_endian_inj (Spec.Poly1305.poly1305 (pad_16 aad @| pad_16 c @| lb) k) mac



private val aead_encrypt_poly:
  c:uint8_p ->
  mlen:u32{let len = U32.v mlen in len = length c}  ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  aad:uint8_p ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  b:uint8_p{length b >= 80 /\ disjoint b mac} ->
  Stack unit
    (requires (fun h -> live h c /\ live h mac /\ live h aad /\ live h b))
    (ensures  (fun h0 z h1 -> live h0 c /\ live h0 mac /\ live h0 aad /\ live h0 b
      /\ modifies_1 mac h0 h1 /\ live h1 mac
      /\ (let k   = reveal_sbytes (as_seq h0 (Buffer.sub b 0ul 32ul)) in
         let aad = reveal_sbytes (as_seq h0 aad) in
         let c   = reveal_sbytes (as_seq h0 c) in
         let mac = reveal_sbytes (as_seq h1 mac) in
         let lb  = reveal_sbytes (as_seq h0 (Buffer.sub b 64ul 16ul)) in
         mac == Spec.Poly1305.poly1305 (pad_16 aad @| pad_16 c @| lb) k)
    ))
#reset-options "--max_fuel 0 --z3rlimit 200"
private let aead_encrypt_poly  c mlen mac aad aadlen tmp =
  let b = Buffer.sub tmp 0ul 64ul in
  let lb = Buffer.sub tmp 64ul 16ul in
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in
  push_frame();
  let h0 = ST.get() in
  let tmp = Buffer.create (uint64_to_sint64 0uL) 6ul in
  let st = AEAD.Poly1305_64.mk_state (Buffer.sub tmp 0ul 3ul) (Buffer.sub tmp 3ul 3ul) in
  let h1 = ST.get() in
  no_upd_lemma_0 h0 h1 aad;
  no_upd_lemma_0 h0 h1 c;
  let log:log_t = AEAD.Poly1305_64.poly1305_blocks_init st aad aadlen mk in
  let h2 = ST.get() in
  assert(let aad = reveal_sbytes (as_seq h0 aad) in
         let r   = Spec.Poly1305.encode_r (reveal_sbytes (as_seq h0 (Buffer.sub mk 0ul 16ul))) in
         let acc = AEAD.Poly1305_64.selem (as_seq h2 Hacl.Impl.Poly1305_64.State.(st.h)) in
         acc     = Spec.Poly1305.poly (Spec.Poly1305.encode_bytes (pad_16 aad)) r);
  let log:log_t = AEAD.Poly1305_64.poly1305_blocks_continue log st c mlen in
  let h3 = ST.get() in
  cut (let aad = reveal_sbytes (as_seq h0 aad) in
       let r   = Spec.Poly1305.encode_r (reveal_sbytes (as_seq h0 (Buffer.sub mk 0ul 16ul))) in
       let acc = AEAD.Poly1305_64.selem (as_seq h3 Hacl.Impl.Poly1305_64.State.(st.h)) in
       let c   = reveal_sbytes (as_seq h0 c) in
       acc     = Spec.Poly1305.poly (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad)) r);
  AEAD.Poly1305_64.poly1305_blocks_finish log st lb mac key_s;
  let h4 = ST.get() in
  cut (let lb  = as_seq h0 lb in
       let c   = reveal_sbytes (as_seq h0 c) in
       let aad = reveal_sbytes (as_seq h0 aad) in
       let r   = Spec.Poly1305.encode_r (reveal_sbytes (as_seq h0 (Buffer.sub mk 0ul 16ul))) in
       let s   = hlittle_endian (as_seq h0 (Buffer.sub mk 16ul 16ul)) in
       let mac = reveal_sbytes (as_seq h4 mac) in
       little_endian mac = (Spec.Poly1305.poly (Seq.cons (reveal_sbytes lb) (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad))) r + s) % pow2 128);
  Seq.lemma_eq_intro (as_seq h0 (Buffer.sub mk 0ul 16ul)) (Seq.slice (as_seq h0 mk) 0 16);
  Seq.lemma_eq_intro (as_seq h0 (Buffer.sub mk 16ul 16ul)) (Seq.slice (as_seq h0 mk) 16 32);
  lemma_aead_encrypt_poly_2 (reveal_sbytes (as_seq h0 mk)) (reveal_sbytes (as_seq h4 mac)) (as_seq h0 aad) (as_seq h0 c) (reveal_sbytes (as_seq h0 lb));
  lemma_aead_encrypt_poly h0 h1 h2 h3 h4 Hacl.Impl.Poly1305_64.State.(st.r) Hacl.Impl.Poly1305_64.State.(st.h) mac;
  pop_frame()


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

private val lemma_aead_encrypt:
  h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem ->
  c:uint8_p -> b:uint8_p -> mac:uint8_p ->
  Lemma (requires (live h0 c /\ live h0 mac /\ (b `unused_in` h0)
    /\ live h1 c /\ live h1 mac /\ live h1 b
    /\ live h2 c /\ live h2 mac /\ live h2 b
    /\ live h3 c /\ live h3 mac /\ live h3 b
    /\ live h4 c /\ live h4 mac /\ live h4 b
    /\ modifies_0 h0 h1 /\ modifies_1 c h1 h2 /\ modifies_1 b h2 h3 /\ modifies_1 mac h3 h4))
        (ensures (modifies_3_2 c mac h0 h4))
private let lemma_aead_encrypt h0 h1 h2 h3 h4 c b mac =
  lemma_modifies_0_2 c b h0 h1 h3;
  lemma_modifies_2_1'' c mac h0 h3 h4

let encode_length lb aad_len mlen =
  let h0 = ST.get() in
  hstore64_le (Buffer.sub lb 0ul 8ul) (uint32_to_sint64 aad_len);
  let h1 = ST.get() in
  lemma_little_endian_inj (little_bytes 8ul (U32.v aad_len)) (reveal_sbytes (as_seq h1 (Buffer.sub lb 0ul 8ul)));
  hstore64_le (Buffer.sub lb 8ul 8ul) (uint32_to_sint64 mlen);
  let h2 = ST.get() in
  lemma_little_endian_inj (little_bytes 8ul (U32.v mlen)) (reveal_sbytes (as_seq h2 (Buffer.sub lb 8ul 8ul)));
  Seq.lemma_eq_intro (slice (as_seq h2 lb) 0 8) (as_seq h2 (Buffer.sub lb 0ul 8ul));
  Seq.lemma_eq_intro (slice (as_seq h2 lb) 8 16) (as_seq h2 (Buffer.sub lb 8ul 8ul));
  no_upd_lemma_1 h1 h2 (Buffer.sub lb 8ul 8ul) (Buffer.sub lb 0ul 8ul);
  lemma_eq_intro (reveal_sbytes (as_seq h2 lb)) (little_bytes 8ul (U32.v aad_len) @| little_bytes 8ul (U32.v mlen))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 300"

val aead_encrypt_:
  c:uint8_p ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  m:uint8_p{disjoint c m} ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  aad:uint8_p{disjoint aad c} ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen /\ disjoint k mac /\ disjoint k c} ->
  n:uint8_p{length n = noncelen /\ disjoint n mac /\ disjoint n c} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k /\ live h aad))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac
      /\ live h0 c /\ live h0 mac /\ live h0 m /\ live h0 n /\ live h0 k /\ live h0 aad
      /\ (let c   = reveal_sbytes (as_seq h1 c) in
         let mac = reveal_sbytes (as_seq h1 mac) in
         let k   = reveal_sbytes (as_seq h0 k) in
         let n   = reveal_sbytes (as_seq h0 n) in
         let aad' = reveal_sbytes (as_seq h0 aad) in
         let m'   = reveal_sbytes (as_seq h0 m) in
         let mackey = slice (Spec.Chacha20.chacha20_block k n 0) 0 32 in
         (* (c, mac) == aead_chacha20_poly1305_encrypt k n m' aad') *)
         c == Spec.Chacha20.chacha20_encrypt_bytes k n 1 m'
         /\ mac == Spec.Poly1305.poly1305 (pad_16 aad' @| pad_16 c @| little_bytes 8ul (length aad) @| little_bytes 8ul (length m)) mackey)
      ))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 500"
let aead_encrypt_ c mac m mlen aad aadlen k n =
  let h = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = create (uint8_to_sint8 0uy) 80ul in
  let b = Buffer.sub tmp 0ul 64ul in
  let lb = Buffer.sub tmp 64ul 16ul in
  let h0' = ST.get() in
  encode_length lb aadlen mlen;
  let h1 = ST.get() in
  lemma_modifies_0_1' tmp h0 h0' h1;
  Hacl.Chacha20.chacha20 c m mlen k n 1ul;
  let h2 = ST.get() in
  let _ =
    let m = reveal_sbytes (as_seq h0 m) in
    let c = reveal_sbytes (as_seq h2 c) in
    let k = reveal_sbytes (as_seq h0 k) in
    let n = reveal_sbytes (as_seq h0 n) in
    assert (c == Spec.Chacha20.chacha20_encrypt_bytes k n 1 m)
  in
  Hacl.Chacha20.chacha20_key_block b k n 0ul;
  let h3 = ST.get() in
  no_upd_lemma_1 h2 h3 b c;
  cut (let b = reveal_sbytes (as_seq h3 b) in let k = reveal_sbytes (as_seq h0 k) in
       let n = reveal_sbytes (as_seq h0 n) in
       b == Spec.Chacha20.chacha20_block k n 0);
  Seq.lemma_eq_intro (slice (as_seq h3 b) 0 32) (as_seq h3 (Buffer.sub b 0ul 32ul));
  Seq.lemma_eq_intro (reveal_sbytes (slice (as_seq h3 b) 0 32)) (slice (Spec.Chacha20.chacha20_block (reveal_sbytes (as_seq h0 k)) (reveal_sbytes (as_seq h0 n)) 0) 0 32);
  aead_encrypt_poly  c mlen mac aad aadlen tmp;
  cut (let aad' = reveal_sbytes (as_seq h0 aad) in let c = reveal_sbytes (as_seq h2 c) in
       let lb = reveal_sbytes (as_seq h3 lb) in
    pad_16 aad' @| pad_16 c @| little_bytes 8ul (length aad) @| little_bytes 8ul (length m)
    == pad_16 aad' @| pad_16 c @| lb);
  let h4 = ST.get() in
  lemma_aead_encrypt h0 h1 h2 h3 h4 c tmp mac;
  pop_frame();
  let h5 = ST.get() in
  modifies_popped_3_2 c mac h h0 h4 h5;
  0ul

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"
let aead_encrypt c mac m mlen aad aadlen k n =
  let z = aead_encrypt_ c mac m mlen aad aadlen k n in
  z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

private val lemma_aead_decrypt:
  h0:mem -> h1:mem -> h2:mem -> m:uint8_p ->
  Lemma (requires (live h0 m /\ modifies_0 h0 h1 /\ modifies_2_1 m h1 h2))
        (ensures (modifies_2_1 m h0 h2))
let lemma_aead_decrypt h0 h1 h2 m =
  lemma_modifies_sub_2_1 h0 h1 m;
  lemma_modifies_2_1_trans m h0 h1 h2

private val lemma_aead_decrypt_len:
  c:uint8_p ->
  mlen:u32{U32.v mlen = length c} ->
  Lemma (1 + (length c / 64) < pow2 32)
let lemma_aead_decrypt_len c mlen = ()

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"
let aead_decrypt m c mlen mac aad aadlen k n =
  let h = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp  = create (uint8_to_sint8 0uy) 96ul in
  let b    = Buffer.sub tmp 0ul 64ul in
  let lb   = Buffer.sub tmp 64ul 16ul in
  let h1 = ST.get() in
  encode_length lb aadlen mlen;
  let rmac = Buffer.sub tmp 80ul 16ul in
  let h1' = ST.get() in
  Hacl.Chacha20.chacha20_key_block b k n 0ul;
  let h2 = ST.get() in
  aead_encrypt_poly c mlen rmac aad aadlen (Buffer.sub tmp 0ul 80ul);
  let h3 = ST.get() in
  lemma_modifies_1_trans tmp h1 h1' h2;
  lemma_modifies_1_trans tmp h1 h2 h3;
  lemma_modifies_0_1' tmp h0 h1 h3;
  let result = cmp_bytes mac rmac 16ul in
  let h3' = ST.get() in
  let verify = declassify_u8 result in
  lemma_aead_decrypt_len c mlen;
  let res : u32 =
    if U8.(verify =^ 0uy) then (
      	 Hacl.Chacha20.chacha20 m c mlen k n 1ul;
	 0ul
  	 ) else 1ul in
  let h4 = ST.get() in
  lemma_modifies_0_1 m h3 h3' h4;
  lemma_aead_decrypt h0 h3 h4 m;
  pop_frame();
  let h5 = ST.get() in
  modifies_popped_1 m h h0 h4 h5;
  res
