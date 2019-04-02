module Hacl.SecretBox.ZeroPad

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer
open FStar.HyperStack.ST
open Hacl.Constants
open Hacl.Policies
open Hacl.Cast

(* Module abbreviations *)
module HS  = FStar.HyperStack
module B   = FStar.Buffer
module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

private val set_zero_bytes:
  b:uint8_p{length b >= 32} ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let set_zero_bytes b =
  let zero = uint8_to_sint8 0uy in
  b.(0ul)  <- zero; b.(1ul)  <- zero; b.(2ul)  <- zero; b.(3ul)  <- zero;
  b.(4ul)  <- zero; b.(5ul)  <- zero; b.(6ul)  <- zero; b.(7ul)  <- zero;
  b.(8ul)  <- zero; b.(9ul)  <- zero; b.(10ul) <- zero; b.(11ul) <- zero;
  b.(12ul) <- zero; b.(13ul) <- zero; b.(14ul) <- zero; b.(15ul) <- zero;
  b.(16ul) <- zero; b.(17ul) <- zero; b.(18ul) <- zero; b.(19ul) <- zero;
  b.(20ul) <- zero; b.(21ul) <- zero; b.(22ul) <- zero; b.(23ul) <- zero;
  b.(24ul) <- zero; b.(25ul) <- zero; b.(26ul) <- zero; b.(27ul) <- zero;
  b.(28ul) <- zero; b.(29ul) <- zero; b.(30ul) <- zero; b.(31ul) <- zero


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

private val lemma_crypto_secretbox_detached:
  h0:mem -> h2:mem -> h3:mem -> h4:mem -> h5:mem -> h6:mem ->
  sk:uint8_p -> mac:uint8_p -> c:uint8_p ->
  Lemma (requires ((sk `unused_in` h0) /\ live h0 mac /\ live h0 c /\ modifies_0 h0 h2
    /\ modifies_1 c h2 h3 /\ modifies_1 mac h3 h4 /\ modifies_1 c h4 h5 /\ modifies_1 sk h5 h6
    /\ live h2 sk /\ live h2 mac /\ live h2 c
    /\ live h3 sk /\ live h3 mac /\ live h3 c
    /\ live h4 sk /\ live h4 mac /\ live h4 c
    /\ live h5 sk /\ live h5 mac /\ live h5 c
    /\ live h5 sk /\ live h6 mac /\ live h6 c
    ))
        (ensures (modifies_3_2 c mac h0 h6))
private let lemma_crypto_secretbox_detached h0 h2 h3 h4 h5 h6 sk mac c =
  lemma_reveal_modifies_0 h0 h2;
  lemma_reveal_modifies_1 c h2 h3;
  lemma_reveal_modifies_1 mac h3 h4;
  lemma_reveal_modifies_1 c h4 h5;
  lemma_reveal_modifies_1 sk h5 h6;
  lemma_intro_modifies_3_2 c mac h0 h6


(* We assume that the first 32 bytes of c and m are 0s and will remain 0s *)
val crypto_secretbox_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ disjoint mac c} ->
  m:uint8_p{disjoint m c} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_secretbox_detached c mac m mlen n k =
  let mlen_ = Int.Cast.uint64_to_uint32 mlen in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let subkey = create (uint8_to_sint8 0uy) 32ul in
  let h1 = ST.get() in
  Hacl.Salsa20.hsalsa20 subkey k (sub n 0ul 16ul);
  let h2 = ST.get() in
  Hacl.Salsa20.salsa20 c m U32.(mlen_ +^ 32ul) subkey (sub n 16ul 8ul) 0uL;
  let h3 = ST.get() in
  Hacl.Poly1305_64.crypto_onetimeauth mac (sub c 32ul mlen_) mlen (sub c 0ul 32ul);
  let h4 = ST.get() in
  set_zero_bytes(c);
  let h5 = ST.get() in
  set_zero_bytes(subkey);
  let h6 = ST.get() in
  lemma_modifies_0_1' subkey h0 h1 h2;
  lemma_crypto_secretbox_detached h0 h2 h3 h4 h5 h6 subkey mac c;
  pop_frame();
  0ul


#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

private let lemma_crypto_secretbox_open_detached_decrypt (h:mem) (m:uint8_p) (subkey:uint8_p) :
  Lemma (modifies_2 m subkey h h)
  = lemma_intro_modifies_2 m subkey h h


private val crypto_secretbox_open_detached_decrypt:
  m:uint8_p ->
  c:uint8_p{disjoint c m} ->
  clen:u64{let len = U64.v clen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  subkey:uint8_p{length subkey = 32 /\ disjoint m subkey} ->
  verify:U8.t ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h n /\ live h subkey))
    (ensures (fun h0 _ h1 -> modifies_2 m subkey h0 h1 /\ live h1 m /\ live h1 subkey))
let crypto_secretbox_open_detached_decrypt m c clen n subkey verify =
    let h = ST.get() in
    let clen_ = Int.Cast.uint64_to_uint32 clen in
    if U8.(verify =^ 0uy) then (
      Hacl.Salsa20.salsa20 m c U32.(clen_ +^ 32ul) subkey (sub n 16ul 8ul) 0uL;
      set_zero_bytes subkey;
      set_zero_bytes m;
      0ul)
    else (
      lemma_crypto_secretbox_open_detached_decrypt h m subkey;
      0xfffffffful
    )


(* We assume that the first 32 bytes of m and c are 0 *)
val crypto_secretbox_open_detached:
  m:uint8_p ->
  c:uint8_p{disjoint m c} ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  clen:u64{let len = U64.v clen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h mac /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_detached m c mac clen n k =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp    = create (uint8_to_sint8 0uy) 112ul in
  let subkey = Buffer.sub tmp 0ul 32ul in
  let mackey = Buffer.sub tmp 32ul 32ul in
  let mackey' = Buffer.sub tmp 64ul 32ul in
  let cmac   = Buffer.sub tmp 96ul 16ul in
  let h1 = ST.get() in
  Hacl.Salsa20.hsalsa20 subkey k (sub n 0ul 16ul);
  let h2 = ST.get() in
  Hacl.Salsa20.salsa20 mackey mackey' 32ul subkey (sub n 16ul 8ul) 0uL;
  let h3 = ST.get() in
  let clen_ = Int.Cast.uint64_to_uint32 clen in
  Hacl.Poly1305_64.crypto_onetimeauth cmac (sub c 32ul clen_) clen mackey;
  let h4 = ST.get() in
  let result = cmp_bytes mac cmac 16ul in
  let verify = declassify_u8 result in
  let z = crypto_secretbox_open_detached_decrypt m c clen n subkey verify in
  pop_frame();
  lemma_modifies_1_trans tmp h1 h2 h3;
  lemma_modifies_1_trans tmp h1 h3 h4;
  lemma_modifies_0_1' tmp h0 h1 h4;
  z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

val crypto_secretbox_easy:
  c:uint8_p ->
  m:uint8_p{disjoint c m} ->
  mlen:u64{let len = U64.v mlen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_secretbox_easy c m mlen n k =
  push_frame ();
  let mlen_ = FStar.Int.Cast.uint64_to_uint32 mlen in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let cmac   = create (uint8_to_sint8 0uy) 16ul in
  let res = crypto_secretbox_detached c cmac m mlen n k in
  blit cmac 0ul c 16ul 16ul;
  pop_frame();
  res


val crypto_secretbox_open_easy:
  m:uint8_p ->
  c:uint8_p{disjoint m c} ->
  clen:u64{let len = U64.v clen in len + 32 = length m /\ len + 32 = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_easy m c clen n k =
  let mac = sub c 0ul 16ul in
  crypto_secretbox_open_detached m c mac U64.(clen) n k
