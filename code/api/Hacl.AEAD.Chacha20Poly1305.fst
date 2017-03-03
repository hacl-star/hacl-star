module Hacl.AEAD.Chacha20Poly1305

open FStar.Seq
open FStar.HyperStack
open FStar.Buffer
open FStar.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast
open Hacl.Spec.Endianness
open Hacl.Endianness

open Spec.Chacha20Poly1305

(* Module abbreviations *)

module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64


(* The following values should point to Spec.Chacha20Poly1305 *)
let noncelen = 12
let keylen = 32
let maclen = 16

type state = Hacl.Impl.Poly1305_64.poly1305_state
inline_for_extraction let log_t = Ghost.erased (Spec.Poly1305.text)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

private val lemma_aead_encrypt_poly:
  h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem ->
  r:buffer Hacl.UInt64.t -> acc:buffer Hacl.UInt64.t -> mac:uint8_p ->
  Lemma (requires (live h0 mac /\ ~(contains h0 r) /\ ~(contains h0 acc)
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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"
open FStar.Mul

assume val lemma_encode_bytes_append: s1:Seq.seq U8.t -> s2:Seq.seq U8.t -> l:nat{l * 16 = Seq.length s1} ->
  Lemma (requires (True))
        (ensures (Spec.Poly1305.encode_bytes (s1 @| s2) == Spec.Poly1305.encode_bytes s2 @| Spec.Poly1305.encode_bytes s1))
        (* (decreases (l)) *)

assume private val encode_bytes_append: len:nat -> s:Seq.seq U8.t -> w:Spec.Poly1305.word -> Lemma
  (requires (0 < Seq.length w /\ Seq.length s == len /\ len % 16 == 0))
  (ensures  (Seq.equal (Spec.Poly1305.encode_bytes ((Seq.append s w)))
                      (Seq.cons (w) (Spec.Poly1305.encode_bytes (s)))))

open FStar.Endianness 

private val lemma_aead_encrypt_poly_2:
  k:Spec.Poly1305.key ->
  mac:Spec.Poly1305.tag ->
  aad:Seq.seq H8.t ->
  c:Seq.seq H8.t ->
  lb:Spec.Poly1305.word_16 ->
  Lemma (requires (
    let r = Spec.Poly1305.encode_r (slice k 0 16) in
    let s = hlittle_endian (slice k 16 32) in
    hlittle_endian mac = (Spec.Poly1305.poly (Seq.cons lb (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad))) r + s) % pow2 128))
        (ensures (mac == Spec.Poly1305.poly1305 (pad_16 aad @| pad_16 c @| lb) k))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
let lemma_aead_encrypt_poly_2 k mac aad c lb =
  Math.Lemmas.lemma_div_mod (Seq.length (pad_16 aad)) 16;
  lemma_encode_bytes_append (pad_16 aad) (pad_16 c) (Seq.length (pad_16 aad) / 16);
  cut (Spec.Poly1305.encode_bytes (pad_16 aad @| pad_16 c) == Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad));
  let s = (pad_16 aad @| pad_16 c) in
  Seq.lemma_eq_intro (pad_16 aad @| pad_16 c @| lb) ((pad_16 aad @| pad_16 c) @| lb);
  encode_bytes_append (Seq.length s) s lb;  
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
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
private let aead_encrypt_poly  c mlen mac aad aadlen tmp =
  let b = Buffer.sub tmp 0ul 64ul in
  let lb = Buffer.sub tmp 64ul 16ul in
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in
  push_frame();
  let h0 = ST.get() in
  let tmp = Buffer.create (uint64_to_sint64 0uL) 6ul in
  let st = Poly1305_64.mk_state (Buffer.sub tmp 0ul 3ul) (Buffer.sub tmp 3ul 3ul) in
  let h1 = ST.get() in
  let log:log_t = Poly1305_64.poly1305_blocks_init st aad aadlen mk in
  let h2 = ST.get() in
  cut (let aad = as_seq h0 aad in
       let r   = Spec.Poly1305.encode_r (as_seq h0 (Buffer.sub mk 0ul 16ul)) in
       let acc = Hacl.Spec.Poly1305_64.selem (as_seq h2 Hacl.Impl.Poly1305_64.(st.h)) in
       acc     = Spec.Poly1305.poly (Spec.Poly1305.encode_bytes (pad_16 aad)) r);
  let log:log_t = Poly1305_64.poly1305_blocks_continue log st c mlen in
  let h3 = ST.get() in
  cut (let aad = as_seq h0 aad in
       let r   = Spec.Poly1305.encode_r (as_seq h0 (Buffer.sub mk 0ul 16ul)) in
       let acc = Hacl.Spec.Poly1305_64.selem (as_seq h3 Hacl.Impl.Poly1305_64.(st.h)) in
       let c   = reveal_sbytes (as_seq h0 c) in
       acc     = Spec.Poly1305.poly (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad)) r);
  Poly1305_64.poly1305_blocks_finish log st lb mac key_s;
  let h4 = ST.get() in
  cut (let lb  = as_seq h0 lb in
       let c   = as_seq h0 c in
       let aad = as_seq h0 aad in
       let r   = Spec.Poly1305.encode_r (as_seq h0 (Buffer.sub mk 0ul 16ul)) in
       let s   = hlittle_endian (as_seq h0 (Buffer.sub mk 16ul 16ul)) in
       let mac = reveal_sbytes (as_seq h4 mac) in
       hlittle_endian mac = (Spec.Poly1305.poly (Seq.cons lb (Spec.Poly1305.encode_bytes (pad_16 c) @| Spec.Poly1305.encode_bytes (pad_16 aad))) r + s) % pow2 128);
  Seq.lemma_eq_intro (as_seq h0 (Buffer.sub mk 0ul 16ul)) (Seq.slice (as_seq h0 mk) 0 16);
  Seq.lemma_eq_intro (as_seq h0 (Buffer.sub mk 16ul 16ul)) (Seq.slice (as_seq h0 mk) 16 32);
  lemma_aead_encrypt_poly_2 (as_seq h0 mk) (as_seq h4 mac) (as_seq h0 aad) (as_seq h0 c) (as_seq h0 lb);
  lemma_aead_encrypt_poly h0 h1 h2 h3 h4 Hacl.Impl.Poly1305_64.(st.r) Hacl.Impl.Poly1305_64.(st.h) mac;
  pop_frame()



private val lemma_aead_encrypt:
  h0:mem -> h1:mem -> h2:mem -> h3:mem -> h4:mem ->
  c:uint8_p -> b:uint8_p -> mac:uint8_p ->
  Lemma (requires (live h0 c /\ live h0 mac /\ ~(contains h0 b)
    /\ live h1 c /\ live h1 mac /\ live h1 b
    /\ live h2 c /\ live h2 mac /\ live h2 b
    /\ live h3 c /\ live h3 mac /\ live h3 b
    /\ live h4 c /\ live h4 mac /\ live h4 b
    /\ modifies_0 h0 h1 /\ modifies_1 c h1 h2 /\ modifies_1 b h2 h3 /\ modifies_1 mac h3 h4))
        (ensures (modifies_3_2 c mac h0 h4))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"
private let lemma_aead_encrypt h0 h1 h2 h3 h4 c b mac =
  lemma_reveal_modifies_0 h0 h1;
  lemma_reveal_modifies_1 c h1 h2;
  lemma_reveal_modifies_1 b h2 h3;
  lemma_reveal_modifies_1 mac h3 h4;
  lemma_intro_modifies_3_2 c mac h0 h4


val aead_encrypt:
  c:uint8_p ->
  mac:uint8_p{length mac = maclen /\ disjoint mac c} ->
  m:uint8_p{disjoint c m} ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  aad:uint8_p ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen /\ disjoint k mac /\ disjoint k c} ->
  n:uint8_p{length n = noncelen /\ disjoint n mac /\ disjoint n c} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k /\ live h aad))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let aead_encrypt c mac m mlen aad aadlen k n =
  push_frame();
  let h0 = ST.get() in
  let tmp = create (uint8_to_sint8 0uy) 80ul in
  let b = Buffer.sub tmp 0ul 64ul in
  let lb = Buffer.sub tmp 64ul 16ul in
  hstore64_le (Buffer.sub lb 0ul 8ul) (uint32_to_sint64 aadlen);
  hstore64_le (Buffer.sub lb 8ul 8ul) (uint32_to_sint64 mlen);
  let h1 = ST.get() in
  Seq.lemma_eq_intro (as_seq h1 b) (as_seq h1 (Buffer.sub lb 0ul 8ul) @| as_seq h1 (Buffer.sub lb 8ul 8ul)); admit()
  cut (as_seq h1 lb == little_bytes 8ul (length aad) @| little_bytes 8ul (length c));
  admit()
  cut (modifies_0 h0 h1);
  Chacha20.chacha20 c m mlen k n 1ul;
  let h2 = ST.get() in
  Chacha20.chacha20_key_block b k n 0ul;
  let h3 = ST.get() in
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in
  aead_encrypt_poly  c mlen mac aad aadlen k n tmp;
  let h4 = ST.get() in
  lemma_aead_encrypt h0 h1 h2 h3 h4 c tmp mac;
  pop_frame();
  0ul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

private let lemma_aead_decrypt_ (h:mem) (h':mem) (m:uint8_p) : Lemma 
  (h == h' ==> modifies_1 m h h')
  = lemma_intro_modifies_1 m h h


private val lemma_aead_decrypt:
  h0:mem -> h1:mem -> h2:mem ->
  tmp:uint8_p -> m:uint8_p ->
  Lemma (requires (~(contains h0 tmp) /\ live h0 m /\ live h1 tmp /\ live h1 m /\ live h2 tmp /\ live h2 m
    /\ modifies_0 h0 h1 /\ (modifies_1 m h1 h2 \/ h1 == h2)))
        (ensures (modifies_2_1 m h0 h2))
let lemma_aead_decrypt h0 h1 h2 tmp m =
  lemma_reveal_modifies_0 h0 h1;
  lemma_aead_decrypt_ h1 h2 m;
  lemma_reveal_modifies_1 m h1 h2;
  lemma_intro_modifies_2_1 m h0 h2


val aead_decrypt:
  m:uint8_p ->
  c:uint8_p{disjoint m c} ->
  mlen:u32{let len = U32.v mlen in len = length m /\ len = length c}  ->
  mac:uint8_p{length mac = maclen /\ disjoint mac m} ->
  aad:uint8_p ->
  aadlen:u32{let len = U32.v aadlen in len = length aad}  ->
  k:uint8_p{length k = keylen /\ (* disjoint k mac /\  *)disjoint k m} ->
  n:uint8_p{length n = noncelen /\ (* disjoint n mac /\  *)disjoint n m} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k /\ live h aad))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"
let aead_decrypt m c mlen mac aad aadlen k n =
  push_frame();
  let h0 = ST.get() in
  let tmp  = create (uint8_to_sint8 0uy) 96ul in
  let b    = Buffer.sub tmp 0ul 64ul in
  let lb   = Buffer.sub tmp 64ul 16ul in
  hstore64_le (Buffer.sub lb 0ul 8ul) (uint32_to_sint64 aadlen);
  hstore64_le (Buffer.sub lb 8ul 8ul) (uint32_to_sint64 mlen);
  let rmac = Buffer.sub tmp 80ul 16ul in
  Chacha20.chacha20_key_block b k n 0ul;
  let mk = Buffer.sub b 0ul 32ul in
  let key_s = Buffer.sub mk 16ul 16ul in
  aead_encrypt_poly  c mlen rmac aad aadlen k n (Buffer.sub tmp 0ul 80ul);
  let h1 = ST.get() in
  cut (modifies_0 h0 h1);
  (* Declassication assumption on mac *)
  assume (Hacl.Policies.declassifiable mac /\ Hacl.Policies.declassifiable rmac);
  let verify = cmp_bytes mac rmac 16ul in
  let res =
    if U8.(verify =^ 0uy) then (
      	 Chacha20.chacha20 m c mlen k n 1ul;
	 0ul
  	 ) else 1ul in
  let h2 = ST.get() in
  lemma_aead_decrypt h0 h1 h2 tmp m;
  pop_frame();
  res
