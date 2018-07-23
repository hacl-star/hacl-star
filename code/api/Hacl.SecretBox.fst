module Hacl.SecretBox

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

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


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

val crypto_secretbox_detached:
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES /\ disjoint mac c} ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h mac /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_2 c mac h0 h1 /\ live h1 c /\ live h1 mac))
let crypto_secretbox_detached c mac m mlen n k =
  let hinit = ST.get() in
  push_frame();
  let mlen_32 = Int.Cast.uint64_to_uint32 mlen in
  let h0 = ST.get() in
  let hsalsa_state = create (uint8_to_sint8 0uy) 96ul in
  let h0' = ST.get() in
  let subkey = sub hsalsa_state  0ul 32ul in
  let block0 = sub hsalsa_state 32ul 64ul in
  let zerobytes = 32ul in
  let zerobytes_64 = Int.Cast.uint32_to_uint64 zerobytes in
  let mlen0 =
      if (U64.(mlen >^ (64uL -^ zerobytes_64))) then U64.(64uL -^ zerobytes_64) else mlen in
  let mlen0_32 = Int.Cast.uint64_to_uint32 mlen0 in
  Math.Lemmas.modulo_lemma (U32.v mlen0_32) (pow2 32);
  blit m 0ul block0 zerobytes mlen0_32;
  Hacl.Salsa20.hsalsa20 subkey k (sub n 0ul 16ul);
  Hacl.Salsa20.salsa20 block0 block0 (U32.(mlen0_32 +^ zerobytes)) subkey (sub n 16ul 8ul) 0uL;
  let h1 = ST.get() in
  cut (modifies_1 hsalsa_state h0' h1);
  cut (modifies_0 h0 h1);
  blit block0 zerobytes c 0ul mlen0_32;
  if (U64.(mlen >^ mlen0)) then
    Hacl.Salsa20.salsa20 (offset c mlen0_32) (offset m mlen0_32) (U32.(mlen_32 -^ mlen0_32)) subkey (sub n 16ul 8ul)  1uL;
  let h2 = ST.get() in
  cut (modifies_2_1 c h0 h2);
  Hacl.Poly1305_64.crypto_onetimeauth mac c mlen (sub block0 0ul 32ul);
  let h3 = ST.get() in
  cut (modifies_3_2 c mac h0 h3);
  pop_frame();
  let hfin = ST.get() in
  0ul


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 200"

val crypto_secretbox_open_detached:
  m:uint8_p ->
  c:uint8_p ->
  mac:uint8_p{length mac = crypto_secretbox_MACBYTES} ->
  clen:u64{let len = U64.v clen in len = length m /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h m /\ live h c /\ live h mac /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_detached m c mac clen n k =
  push_frame();
  let h0 = ST.get() in
  let hsalsa_state = create (uint8_to_sint8 0uy) 112ul in
  let subkey = sub hsalsa_state 0ul 32ul in
  let block0 = sub hsalsa_state 32ul 64ul in
  let tmp_mac = sub hsalsa_state 96ul 16ul in
  let h0' = ST.get() in
  Hacl.Salsa20.hsalsa20 subkey k (sub n 0ul 16ul);
  Hacl.Salsa20.salsa20 block0 block0 32ul subkey (sub n 16ul 8ul) 0uL;
  let h1 = ST.get() in
  cut(modifies_0 h0 h1);
  Hacl.Poly1305_64.crypto_onetimeauth tmp_mac c clen (sub block0 0ul 32ul);
  let h2 = ST.get() in
  cut(modifies_0 h0 h2);
  let result = cmp_bytes mac tmp_mac 16ul in
  let verify = declassify_u8 result in
  let zerobytes = 32ul in
  let zerobytes_64 = 32uL in
  let clen0 =
    if (U64.(clen >^ (64uL -^ zerobytes_64))) then U64.(64uL -^ zerobytes_64) else clen in
  let clen0_32 = Int.Cast.uint64_to_uint32 clen0 in
  let z =
    if U8.(verify =^ 0uy) then (
      blit c 0ul block0 zerobytes clen0_32;
      Hacl.Salsa20.salsa20 block0 block0 (U32.(clen0_32 +^ zerobytes)) subkey (sub n 16ul 8ul) 0uL;
      blit block0 zerobytes m 0ul clen0_32;
      let clen_32 = Int.Cast.uint64_to_uint32 clen in
      let h3 = ST.get() in
      cut(modifies_2_1 m h0 h3);
      if (U64.(clen >^ clen0))
        then Hacl.Salsa20.salsa20 (offset m clen0_32) (offset c clen0_32) (U32.(clen_32 +^ clen0_32)) subkey (sub n 16ul 8ul) 1uL;
      let h4 = ST.get() in
      cut(modifies_2_1 m h0 h4);
      0x0ul
    )
    else 0xfffffffful in
  let h5 = ST.get() in
  cut (modifies_2_1 m h0 h5);
  pop_frame();
  z


#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 5"

val crypto_secretbox_easy:
  c:uint8_p ->
  m:uint8_p ->
  mlen:u64{let len = U64.v mlen in len <= length m /\ len + crypto_secretbox_MACBYTES <= length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 c h0 h1 /\ live h1 c))
let crypto_secretbox_easy c m mlen n k =
  let mlen_ = FStar.Int.Cast.uint64_to_uint32 mlen in
  Math.Lemmas.modulo_lemma (U64.v mlen) (pow2 32);
  let c'   = sub c 16ul mlen_ in
  let m'   = sub m 0ul mlen_ in
  let mac  = sub c 0ul 16ul in
  crypto_secretbox_detached c' mac m' mlen n k


val crypto_secretbox_open_easy:
  m:uint8_p ->
  c:uint8_p ->
  clen:u64{let len = U64.v clen in len = length m + crypto_secretbox_MACBYTES /\ len = length c}  ->
  n:uint8_p{length n = crypto_secretbox_NONCEBYTES} ->
  k:uint8_p{length k = crypto_secretbox_KEYBYTES} ->
  Stack u32
    (requires (fun h -> live h c /\ live h m /\ live h n /\ live h k))
    (ensures  (fun h0 z h1 -> modifies_1 m h0 h1 /\ live h1 m))
let crypto_secretbox_open_easy m c clen n k =
  let clen_ = FStar.Int.Cast.uint64_to_uint32 (U64.(clen -^ 16uL)) in
  Math.Lemmas.modulo_lemma (U64.(v clen - 16)) (pow2 32);
  let c'  = sub c 16ul clen_ in
  let mac = sub c 0ul 16ul in
  crypto_secretbox_open_detached m c' mac (U64.(clen -^ 16uL)) n k
