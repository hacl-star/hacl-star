module Hacl.Symmetric.XSalsa20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open Hacl.UInt32
open Hacl.Cast

open Hacl.Symmetric.HSalsa20
open Hacl.Symmetric.Salsa20


let h32 = Hacl.UInt32.t
let u32 = FStar.UInt32.t
let uint8_p = buffer Hacl.UInt8.t

module U64 = FStar.UInt64
module U32 = FStar.UInt32

#reset-options "--initial_fuel 0 --max_fuel 0"

private val lemma_max_uint32: n:nat -> Lemma
  (requires (n = 32))
  (ensures  (pow2 n = 4294967296))
  [SMTPat (pow2 n)]
let lemma_max_uint32 n = assert_norm(pow2 32 = 4294967296)
private val lemma_max_uint64: n:nat -> Lemma
  (requires (n = 64))
  (ensures  (pow2 n = 18446744073709551616))
  [SMTPat (pow2 n)]
let lemma_max_uint64 n = assert_norm(pow2 64 = 18446744073709551616)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

val crypto_stream_xsalsa20:
  c:uint8_p ->
  clen:FStar.UInt64.t{U64.v clen <= length c} ->
  n:uint8_p{length n = 24} ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_stream_xsalsa20 c clen n k =
  push_frame();
  let subkey = create (uint8_to_sint8 0uy) 32ul in
  crypto_core_hsalsa20 subkey (Buffer.sub n 0ul 16ul) k;
  crypto_stream_salsa20 c clen (offset n 16ul) subkey;
  pop_frame()


val crypto_stream_xsalsa20_xor_ic:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  n:uint8_p{length n = 24} ->
  ic:FStar.UInt64.t ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
let crypto_stream_xsalsa20_xor_ic c m mlen n ic k =
  push_frame();
  let subkey = create (uint8_to_sint8 0uy) 32ul in
  crypto_core_hsalsa20 subkey (Buffer.sub n 0ul 16ul) k;
  crypto_stream_salsa20_xor_ic c m mlen (offset n 16ul) ic subkey;
  pop_frame()


val crypto_stream_xsalsa20_xor:
  c:uint8_p ->
  m:uint8_p ->
  mlen:FStar.UInt64.t{U64.v mlen <= length c /\ U64.v mlen <= length m} ->
  n:uint8_p{length n = 24} ->
  k:uint8_p{length k = 32} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_1 c h0 h1))
let crypto_stream_xsalsa20_xor c m mlen n k =
  crypto_stream_xsalsa20_xor_ic c m mlen n 0uL k
