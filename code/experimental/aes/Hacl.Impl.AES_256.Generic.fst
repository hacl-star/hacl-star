module Hacl.Impl.AES_256.Generic

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.AES_128.Core


module ST = FStar.HyperStack.ST

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 20"

(* Parameters for AES-256 *)
noextract inline_for_extraction let nb =  4
noextract inline_for_extraction let nk =  8 // 4, 6, or 8 for 128/192/256
noextract inline_for_extraction let nr =  14 // 10, 12, or 14 for 128/192/256


type skey  = lbuffer uint8 32ul

unfold let ctxlen (m:m_spec) =  nlen m +. (15ul *. klen m)

unfold type keyr (m:m_spec) = lbuffer (stelem m) ((size (nr - 1)) *. klen m)
unfold type keyex (m:m_spec) = lbuffer (stelem m) (size 15 *. klen m)
unfold type aes_ctx (m:m_spec) = lbuffer (stelem m) (ctxlen m)


inline_for_extraction
val get_nonce:
    #m: m_spec
  -> ctx: aes_ctx m ->
  Stack (lbuffer (stelem m) (nlen m))
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx 0ul (nlen m)))

inline_for_extraction
let get_nonce (#m:m_spec) (ctx:aes_ctx m) = sub ctx (size 0) (nlen m)


inline_for_extraction
val get_kex:
    #m: m_spec
  -> ctx: aes_ctx m ->
  Stack (lbuffer (stelem m) (15ul *. klen m))
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx (nlen m ) (15ul *. klen m)))

inline_for_extraction
let get_kex (#m:m_spec) (ctx:aes_ctx m) = sub ctx (nlen m) (15ul *. klen m)


inline_for_extraction
val add_round_key:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let add_round_key #m st key = xor_state_key1 #m st key


inline_for_extraction
val enc_rounds:
    #m: m_spec
  -> st: state m
  -> key: keyr m
  -> n: size_t{v n < nr} ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let enc_rounds #m st key n =
  let h0 = ST.get() in
  loop_nospec #h0 n st
    (fun i -> let sub_key = sub key (i *. klen m) (klen m) in
           aes_enc #m st sub_key)


inline_for_extraction
val block_cipher:
    #m: m_spec
  -> st: state m
  -> key: keyex m
  -> n:size_t{v n == nr} ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let block_cipher #m st key n =
  let inner_rounds = n -. size 1 in
  let klen = klen m in
  let k0 = sub key (size 0) klen in
  let kr = sub key klen (inner_rounds *. klen) in
  let kn = sub key (n *. klen) klen in
  add_round_key #m st k0;
  enc_rounds #m st kr (n -. size 1);
  aes_enc_last #m st kn

// KEY EXPANSION

private val rcon: i:size_t{i <=. size 5} -> Tot uint8 (decreases (v i))
let rec rcon i =
  if i = size 0 then
    u8 0x01
  else if i = size 1 then
    u8 0x02
  else if i = size 2 then
    u8 0x04
  else if i = size 3 then
    u8 0x08
  else if i = size 4 then
    u8 0x10
  else
    u8 0x20


inline_for_extraction
val key_expansion256:
    #m: m_spec
  -> keyx: keyex m
  -> key: lbuffer uint8 32ul ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key /\ disjoint keyx key))
  (ensures (fun h0 _ h1 -> modifies1 keyx h0 h1))

#set-options "--z3rlimit 50"

let key_expansion256 #m keyx key =
  let klen = klen m in
  load_key1 (sub keyx (size 0) klen) (sub key (size 0) (size 16));
  load_key1 (sub keyx klen klen) (sub key (size 16) (size 16));
  let h0 = ST.get() in
  loop_nospec #h0 (size 6) keyx (fun i ->
    let off0 = (klen *! i *! size 2) in
    assert(i *! size 2 <=. size 10);
    let off1 = off0 +! klen in
    let off2 = off1 +! klen in
    let off3 = off2 +! klen in
    let prev0 = sub keyx off0 klen in
    let prev1 = sub keyx off1 klen in
    let next0 = sub keyx off2 klen in
    let next1 = sub keyx off3 klen in
    assert(off1 +! klen <=. off2);
    assert(off2 +! klen <=. off3);
    aes_keygen_assist #m next0 prev1 (rcon i) ;
    key_expansion_step #m next0 prev0;
    aes_keygen_assist #m next1 next0 (u8 0x00);
    key_expansion_step2 #m next1 prev1
  );
  let off0 = (klen *! size 12) in
  let off1 = off0 +! klen in
  let off2 = off1 +! klen in
  let prev0 = sub keyx off0 klen in
  let prev1 = sub keyx off1 klen in
  let next0 = sub keyx off2 klen in
  assert(off1 +! klen <=. off2);
  aes_keygen_assist #m next0 prev1 (u8 0x40);
  key_expansion_step #m next0 prev0

inline_for_extraction
val aes256_encrypt_block_generic_:
    #m: m_spec
  -> ob: lbuffer uint8 16ul
  -> ctx: aes_ctx m
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib /\ disjoint ob ctx /\ disjoint ob ib))
  (ensures (fun h0 _ h1 -> modifies1 ob h0 h1))

inline_for_extraction
let aes256_encrypt_block_generic_ #m ob ctx ib =
  push_frame();
  let kex = get_kex ctx in
  let st = create_state #m in
  load_block0 #m st ib;
  block_cipher #m st kex (size 14);
  store_block0 #m ob st;
  pop_frame()
