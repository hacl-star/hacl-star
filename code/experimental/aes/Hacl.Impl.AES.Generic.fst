module Hacl.Impl.AES.Generic

open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.AES.Core

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 50"


module ST = FStar.HyperStack.ST

module Spec = Spec.AES

(* TODO: AES-256. All the AES-256 functions below are untested and most likely wrong. *)


(* Parameters for AES-128 *)
//noextract inline_for_extraction let nb =  4
//noextract inline_for_extraction let nk =  4 // 4, 6, or 8 for 128/192/256
//noextract inline_for_extraction let nr =  10 // 10, 12, or 14 for 128/192/256

unfold type skey (v:Spec.variant) = lbuffer uint8 (size (normalize_term (Spec.key_size v)))

inline_for_extraction let nr (v:Spec.variant) = size (normalize_term (Spec.num_rounds v))

unfold let ctxlen (m:m_spec) (v:Spec.variant) =  nlen m +. ((nr v +! 1ul) *. klen m)

unfold type keyr (m:m_spec) (v:Spec.variant) = lbuffer (stelem m) ((nr v -! 1ul) *. klen m)
unfold type keyex (m:m_spec) (v:Spec.variant) = lbuffer (stelem m) ((nr v +! 1ul) *. klen m)
unfold type aes_ctx (m:m_spec) (v:Spec.variant) = lbuffer (stelem m) (ctxlen m v)

inline_for_extraction
val get_nonce:
    #m: m_spec ->
    #v: Spec.variant ->
    ctx: aes_ctx m v ->
  Stack (lbuffer (stelem m) (nlen m))
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx 0ul (nlen m)))

inline_for_extraction
let get_nonce #m #v ctx = sub ctx (size 0) (nlen m)


inline_for_extraction
val get_kex:
    #m: m_spec ->
    #v: Spec.variant ->
    ctx: aes_ctx m v ->
  Stack (keyex m v)
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx (nlen m ) ((nr v +! 1ul) *. klen m)))

inline_for_extraction
let get_kex #m #v ctx = sub ctx (nlen m) ((nr v +! 1ul) *. klen m)


inline_for_extraction
val create_ctx:
  m: m_spec ->
  v: Spec.variant ->
  StackInline (aes_ctx m v)
  (requires (fun h -> True))
  (ensures (fun h0 f h1 -> live h1 f /\
			stack_allocated f h0 h1 (Seq.create (size_v (ctxlen m v)) (elem_zero m))))

let create_ctx m v = create (ctxlen m v) (elem_zero m)

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
  -> #v: Spec.variant
  -> st: state m
  -> key: keyr m v ->
  ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let enc_rounds #m #v st key =
  let h0 = ST.get() in
  loop_nospec #h0 (nr v -! 1ul) st
    (fun i -> let sub_key = sub key (i *. klen m) (klen m) in
           aes_enc #m st sub_key)


inline_for_extraction
val block_cipher:
    #m: m_spec
  -> #v: Spec.variant
  -> st: state m
  -> key: keyex m v
  -> ST unit
  (requires (fun h -> live h st /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))

let block_cipher #m #v st key =
  let klen = klen m in
  let k0 = sub key (size 0) klen in
  let kr = sub key klen ((nr v -! 1ul) *. klen) in
  let kn = sub key (nr v *. klen) klen in
  add_round_key #m st k0;
  enc_rounds #m #v st kr;
  aes_enc_last #m st kn

#set-options "--admit_smt_queries true"

inline_for_extraction
val key_expansion128:
    #m: m_spec
  -> keyx: keyex m Spec.AES128
  -> key:lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))

[@ CInline ]
let key_expansion128 #m keyx key =
  let klen = klen m in
  load_key1 (sub keyx (size 0) klen) key;
  let h0 = ST.get() in
  (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST INSISTS ON AN IMMEDIATE RCON *)
  (* MAYBE WE SHOULD UNROLL ONLY THIS LOOP *)
  (* loop_nospec #h0 (size 10) keyx
   (fun i ->
     let prev = sub keyx i (size 1) in
     let next = sub keyx (i +. size 1) (size 1) in
     aes_keygen_assist next rcon.(i +. size 1);
     key_expansion_step #m next prev)
  *)
  let prev = sub keyx (size 0) klen in
  let next = sub keyx klen klen in
  aes_keygen_assist0 #m next prev (u8 0x01);
  key_expansion_step #m next prev;
  let prev = sub keyx klen klen in
  let next = sub keyx (size 2 *. klen) klen in
  aes_keygen_assist0 #m next prev (u8 0x02);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 2) (klen) in
  let next = sub keyx (klen *. size 3) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x04);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 3) (klen) in
  let next = sub keyx (klen *. size 4) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x08);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 4) (klen) in
  let next = sub keyx (klen *. size 5) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x10);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 5) (klen) in
  let next = sub keyx (klen *. size 6) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x20);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 6) (klen) in
  let next = sub keyx (klen *. size 7) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x40);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 7) (klen) in
  let next = sub keyx (klen *. size 8) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x80);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 8) (klen) in
  let next = sub keyx (klen *. size 9) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x1b);
  key_expansion_step #m next prev;
  let prev = sub keyx (klen *. size 9) (klen) in
  let next = sub keyx (klen *. size 10) (klen) in
  aes_keygen_assist0 #m next prev (u8 0x36);
  key_expansion_step #m next prev


inline_for_extraction
val key_expansion256:
    #m: m_spec
  -> keyx: keyex m Spec.AES256
  -> key: lbuffer uint8 32ul ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))

let key_expansion256 #m keyx key =
  let klen = klen m in
  let next0 = sub keyx (size 0) klen in
  let next1 = sub keyx klen klen in
  load_key1 next0 (sub key (size 0) (size 16));
  load_key1 next1 (sub key (size 16) (size 16));
  let h0 = ST.get() in
  (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST #M INSISTS ON AN IMMEDIATE RCON *)
  (* MAYBE WE SHOULD UNROLL ONLY THIS LOOP *)
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 2) (klen) in
  let next1 = sub keyx (klen *. size 3) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x01);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 4) (klen) in
  let next1 = sub keyx (klen *. size 5) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x02);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 6) (klen) in
  let next1 = sub keyx (klen *. size 7) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x04);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 8) (klen) in
  let next1 = sub keyx (klen *. size 9) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x08);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 10) (klen) in
  let next1 = sub keyx (klen *. size 11) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x10);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 12) (klen) in
  let next1 = sub keyx (klen *. size 13) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x20);
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1;
  let prev0 = next0 in
  let prev1 = next1 in
  let next0 = sub keyx (klen *. size 14) (klen) in
  aes_keygen_assist0 #m next0 prev1 (u8 0x40);
  key_expansion_step #m next0 prev0
(* END PATTERN *)

#set-options "--admit_smt_queries false"

inline_for_extraction
val key_expansion:
    #m: m_spec
  -> #v: Spec.variant
  -> keyx: keyex m v
  -> key: skey v ->
  ST unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))

let key_expansion #m #v keyx key =
  match v with
  | Spec.AES128 -> key_expansion128 #m keyx key
  | Spec.AES256 -> key_expansion256 #m keyx key

inline_for_extraction
val aes_init_:
    #m: m_spec
  -> #v: Spec.variant
  -> ctx: aes_ctx m v
  -> key: skey v
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes_init_ #m #v ctx key nonce =
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  key_expansion #m #v kex key ;
  load_nonce #m n nonce

(* BEGIN STANDARD PATTERN FOR AVOIDING INLINING *)
inline_for_extraction
val aes128_bitslice_init:
    ctx: aes_ctx M32 Spec.AES128
  -> key: skey Spec.AES128
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes128_bitslice_init ctx key nonce = aes_init_ #M32 #Spec.AES128 ctx key nonce

inline_for_extraction
val aes128_ni_init:
    ctx: aes_ctx MAES Spec.AES128
  -> key: skey Spec.AES128
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes128_ni_init ctx key nonce = aes_init_ #MAES #Spec.AES128 ctx key nonce

inline_for_extraction
val aes256_bitslice_init:
    ctx: aes_ctx M32 Spec.AES256
  -> key: skey Spec.AES256
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes256_bitslice_init ctx key nonce = aes_init_ #M32 #Spec.AES256 ctx key nonce

inline_for_extraction
val aes256_ni_init:
    ctx: aes_ctx MAES Spec.AES256
  -> key: skey Spec.AES256
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes256_ni_init ctx key nonce = aes_init_ #MAES #Spec.AES256 ctx key nonce

inline_for_extraction
val aes_init:
    #m: m_spec
  -> #v: Spec.variant
  -> ctx: aes_ctx m v
  -> key: skey v
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes_init #m #v ctx key nonce =
  match m,v with
  | M32,Spec.AES128 -> aes128_bitslice_init ctx key nonce
  | M32,Spec.AES256 -> aes256_bitslice_init ctx key nonce
  | MAES,Spec.AES128 -> aes128_ni_init ctx key nonce
  | MAES,Spec.AES256 -> aes256_ni_init ctx key nonce

(* END INLINING PATTERN *)

inline_for_extraction
val aes_set_nonce:
    #m: m_spec
  -> #v: Spec.variant
  -> ctx: aes_ctx m v
  -> nonce: lbuffer uint8 12ul ->
  ST unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))

let aes_set_nonce #m #v ctx nonce =
  let n = get_nonce ctx in
  load_nonce #m n nonce

inline_for_extraction
val aes_encrypt_block:
    #m: m_spec
  -> #v: Spec.variant
  -> ob: lbuffer uint8 16ul
  -> ctx: aes_ctx m v
  -> ib: lbuffer uint8 16ul ->
  ST unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
  (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1))

let aes_encrypt_block #m #v ob ctx ib =
  push_frame();
  let kex = get_kex ctx in
  let st = create_state #m in
  load_block0 #m st ib;
  block_cipher #m #v st kex;
  store_block0 #m ob st;
  pop_frame()


inline_for_extraction
val aes_key_block:
    #m: m_spec
  -> #v: Spec.variant
  -> kb: lbuffer uint8 16ul
  -> ctx: aes_ctx m v
  -> counter: size_t ->
  ST unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc kb) h0 h1))

let aes_key_block #m #v kb ctx counter =
  push_frame();
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  let st = create_state #m in
  load_state #m st n counter;
  block_cipher #m #v st kex;
  store_block0 #m kb st;
  pop_frame()


inline_for_extraction
val aes_update4:
    #m: m_spec
  -> #v: Spec.variant
  -> out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx m v
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 b h1 -> modifies (loc out) h0 h1))

let aes_update4 #m #v out inp ctx ctr =
  push_frame();
  let st = create_state #m in
  let kex = get_kex #m ctx in
  let n = get_nonce #m ctx in
  load_state #m st n ctr;
  block_cipher #m #v st kex;
  xor_block #m out st inp;
  pop_frame()


inline_for_extraction
val aes_ctr_:
    #m: m_spec
  -> #v: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx m v
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes_ctr_ #m #v len out inp ctx counter =
  push_frame();
  let blocks64 = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks64 out
    (fun i ->
      let ctr = counter +. (i *. size 4) in
      let ib = sub inp (i *. size 64) (size 64) in
      let ob = sub out (i *. size 64) (size 64) in
      aes_update4 #m #v ob ib ctx ctr);
  let rem = len %. size 64 in
  if (rem >. size 0) then (
    let ctr = counter +. (blocks64 *. size 4) in
    let ib = sub inp (blocks64 *. size 64) rem in
    let ob = sub out (blocks64 *. size 64) rem in
    let last = create 64ul (u8 0) in
    copy (sub last 0ul rem) ib;
    aes_update4 #m #v last last ctx ctr;
    copy ob (sub last 0ul rem));
  pop_frame()


(* BEGIN STANDARD PATTERN FOR AVOIDING INLINING *)
val aes128_ctr_bitslice:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx M32 Spec.AES128
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes128_ctr_bitslice len out inp ctx counter = aes_ctr_ #M32 #Spec.AES128 len out inp ctx counter

inline_for_extraction
val aes128_ctr_ni:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx MAES Spec.AES128
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes128_ctr_ni len out inp ctx counter = aes_ctr_ #MAES #Spec.AES128 len out inp ctx counter 


inline_for_extraction
val aes256_ctr_ni:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx MAES Spec.AES256
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes256_ctr_ni len out inp ctx counter = aes_ctr_ #MAES #Spec.AES256 len out inp ctx counter

val aes256_ctr_bitslice:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx M32 Spec.AES256
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes256_ctr_bitslice len out inp ctx counter = aes_ctr_ #M32 #Spec.AES256 len out inp ctx counter


inline_for_extraction
val aes_ctr:
    #m: m_spec
  -> #v: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx m v
  -> counter: size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

let aes_ctr #m #v len out inp ctx counter =
  match m,v with
  | M32,Spec.AES128 -> aes128_ctr_bitslice len out inp ctx counter
  | M32,Spec.AES256 -> aes256_ctr_bitslice len out inp ctx counter
  | MAES,Spec.AES128 -> aes128_ctr_ni len out inp ctx counter
  | MAES,Spec.AES256 -> aes256_ctr_ni len out inp ctx counter
(* END INLINING PATTERN *)


inline_for_extraction
val aes_ctr_encrypt:
    #m: m_spec
  -> #v: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey v
  -> n:lbuffer uint8 12ul
  -> counter:size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

inline_for_extraction
let aes_ctr_encrypt #m #v in_len out inp k n c =
  push_frame();
  let ctx = create_ctx m v in
  let h1 = ST.get() in
  aes_init #m #v ctx k n;
  aes_ctr #m #v in_len out inp ctx c;
  pop_frame()


inline_for_extraction
val aes_ctr_decrypt:
    #m: m_spec
  -> #v: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey v
  -> n:lbuffer uint8 12ul
  -> counter:size_t
  -> ST unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))

inline_for_extraction
let aes_ctr_decrypt #m #v in_len out inp  k n c =
  aes_ctr_encrypt #m #v in_len out inp k n c

