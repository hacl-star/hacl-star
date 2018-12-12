module Hacl.Impl.Aes.Generic

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open Lib.Buffer
open Hacl.Impl.Aes.Core


(* TODO: AES-256. All the AES-256 functions below are untested and most likely wrong. *)

(* Parameters for AES-128 *)
noextract inline_for_extraction let nb =  4
noextract inline_for_extraction let nk =  4 // 4, 6, or 8 for 128/192/256
noextract inline_for_extraction let nr =  10 // 10, 12, or 14 for 128/192/256

type skey  = lbuffer uint8 16ul
type skey256  = lbuffer uint8 32ul

unfold
type keyr (m:m_spec) =  lbuffer (stelem m) (9ul *. klen m)
unfold
type keyex (m:m_spec) = lbuffer (stelem m) (15ul *. klen m) // Saving space for AES-256

unfold
let ctxlen (m:m_spec) =  nlen m +. (15ul *. klen m)

unfold
type aes_ctx (m:m_spec) = lbuffer (stelem m) (ctxlen m) 

inline_for_extraction
val get_nonce: #m:m_spec -> ctx:aes_ctx m -> Stack (lbuffer (stelem m) (nlen m))
			 (requires (fun h -> live h ctx))
			 (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ 
				     x == gsub ctx 0ul (nlen m)))
inline_for_extraction
let get_nonce (#m:m_spec) (ctx:aes_ctx m) = sub ctx (size 0) (nlen m)

inline_for_extraction
val get_kex: #m:m_spec -> ctx:aes_ctx m -> Stack (lbuffer (stelem m) (15ul *. klen m))
			 (requires (fun h -> live h ctx))
			 (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\
				     x == gsub ctx (nlen m ) (15ul *. klen m)))
inline_for_extraction
let get_kex (#m:m_spec) (ctx:aes_ctx m) = sub ctx (nlen m) (15ul *. klen m)

inline_for_extraction
val create_ctx: m:m_spec -> StackInline (aes_ctx m)
                   (requires (fun h -> True))
		   (ensures (fun h0 f h1 -> live h1 f))
let create_ctx (m:m_spec) = create (ctxlen m ) (elem_zero m)



inline_for_extraction
val add_round_key: #m:m_spec -> st:state m -> key:key1 m -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))
let add_round_key #m st key = xor_state_key1 #m st key


inline_for_extraction
val enc_rounds: #m:m_spec -> st:state m -> key:keyr m -> n:size_t{v n <= 9} -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1))
let enc_rounds #m st key n = 
    let h0 = ST.get() in
    loop_nospec #h0 n st 
      (fun i -> 
	let sub_key = sub key (i *. klen m) (klen m) in aes_enc #m st sub_key)


inline_for_extraction
val block_cipher: #m:m_spec -> st:state m -> key:keyex m -> n:size_t{v n == 10} -> ST unit
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

#set-options "--admit_smt_queries true"
inline_for_extraction
val key_expansion128: #m:m_spec -> keyx:keyex m -> key:lbuffer uint8 16ul -> ST unit
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
       aes_keygen_assist #m next prev (u8 0x01);
       key_expansion_step #m next prev;
       let prev = sub keyx klen klen in
       let next = sub keyx (size 2 *. klen) klen in
       aes_keygen_assist #m next prev (u8 0x02);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 2) (klen) in
       let next = sub keyx (klen *. size 3) (klen) in
       aes_keygen_assist #m next prev (u8 0x04);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 3) (klen) in
       let next = sub keyx (klen *. size 4) (klen) in
       aes_keygen_assist #m next prev (u8 0x08);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 4) (klen) in
       let next = sub keyx (klen *. size 5) (klen) in
       aes_keygen_assist #m next prev (u8 0x10);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 5) (klen) in
       let next = sub keyx (klen *. size 6) (klen) in
       aes_keygen_assist #m next prev (u8 0x20);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 6) (klen) in
       let next = sub keyx (klen *. size 7) (klen) in
       aes_keygen_assist #m next prev (u8 0x40);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 7) (klen) in
       let next = sub keyx (klen *. size 8) (klen) in
       aes_keygen_assist #m next prev (u8 0x80);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 8) (klen) in
       let next = sub keyx (klen *. size 9) (klen) in
       aes_keygen_assist #m next prev (u8 0x1b);
       key_expansion_step #m next prev;
       let prev = sub keyx (klen *. size 9) (klen) in
       let next = sub keyx (klen *. size 10) (klen) in
       aes_keygen_assist #m next prev (u8 0x36);
       key_expansion_step #m next prev
       

inline_for_extraction
val key_expansion256: #m:m_spec -> keyx:keyex m -> key:lbuffer uint8 32ul -> ST unit
			     (requires (fun h -> live h keyx /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc keyx) h0 h1))
let key_expansion256 #m keyx key = 
    let klen = klen m in
    load_key1 (sub keyx (size 0) klen) (sub key (size 0) (size 16));
    load_key1 (sub keyx klen klen) (sub key (size 16) (size 16));
    let h0 = ST.get() in
    (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST #M INSISTS ON AN IMMEDIATE RCON *)
    (* MAYBE WE SHOULD UNROLL ONLY THIS LOOP *)
       let prev0 = sub keyx (size 0) (klen) in
       let prev1 = sub keyx (klen) (klen) in
       let next0 = sub keyx (klen *. size 2) (klen) in
       let next1 = sub keyx (klen *. size 3) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x01);
       key_expansion_step #m next0 prev0;
       aes_keygen_assist #m next1 next0 (u8 0x00);
       key_expansion_step2 #m next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (klen *. size 4) (klen) in
       let next1 = sub keyx (klen *. size 5) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x02);
       key_expansion_step #m next0 prev0;
       aes_keygen_assist #m next1 next0 (u8 0x00);
       key_expansion_step2 #m next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (klen *. size 6) (klen) in
       let next1 = sub keyx (klen *. size 7) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x04);
       key_expansion_step #m next0 prev0;
       aes_keygen_assist #m next1 next0 (u8 0x00);
       key_expansion_step2 #m next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (klen *. size 8) (klen) in
       let next1 = sub keyx (klen *. size 9) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x08);
       key_expansion_step #m next0 prev0;
       aes_keygen_assist #m next1 next0 (u8 0x00);
       key_expansion_step2 #m next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (klen *. size 10) (klen) in
       let next1 = sub keyx (klen *. size 11) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x10);
       key_expansion_step #m next0 prev0;
       aes_keygen_assist #m next1 next0 (u8 0x00);
       key_expansion_step2 #m next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (klen *. size 12) (klen) in
       let next1 = sub keyx (klen *. size 13) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x20);
       key_expansion_step #m next0 prev0;
       aes_keygen_assist #m next1 next0 (u8 0x00);
       key_expansion_step2 #m next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (klen *. size 14) (klen) in
       aes_keygen_assist #m next0 prev1 (u8 0x40);
       key_expansion_step #m next0 prev0
#set-options "--admit_smt_queries false"
    
inline_for_extraction
val aes128_init_: #m:m_spec -> ctx:aes_ctx m -> key:skey -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
let aes128_init_ #m ctx key nonce = 
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  key_expansion128 #m kex key ; 
  load_nonce #m n nonce

(* PATTERN FOR AVOIDING INLINING *)
val aes128_init_bitslice:  ctx:aes_ctx M32 -> key:skey -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
let aes128_init_bitslice ctx key nonce = aes128_init_ #M32 ctx key nonce			     

[@ CInline]
inline_for_extraction
val aes128_init_ni:  ctx:aes_ctx MAES -> key:skey -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
let aes128_init_ni ctx key nonce = aes128_init_ #MAES ctx key nonce			     

inline_for_extraction
val aes128_init: #m:m_spec -> ctx:aes_ctx m -> key:skey -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
let aes128_init #m ctx key nonce = 
  match m with
  | M32 -> aes128_init_bitslice ctx key nonce 
  | MAES -> aes128_init_ni ctx key nonce
(* END PATTERN *)


inline_for_extraction
val aes128_set_nonce: #m:m_spec -> ctx:aes_ctx m -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
let aes128_set_nonce #m ctx nonce = 
  let n = get_nonce ctx in
  load_nonce #m n nonce

#set-options "--admit_smt_queries true"  
inline_for_extraction
val aes256_init: #m:m_spec -> ctx:aes_ctx m -> key:skey -> nonce:lbuffer uint8 12ul -> ST unit
			     (requires (fun h -> live h ctx /\ live h nonce /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1))
let aes256_init #m ctx key nonce = 
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  key_expansion256 #m kex key ; 
  load_nonce #m n nonce
#set-options "--admit_smt_queries false"  


inline_for_extraction
val aes128_encrypt_block: #m:m_spec -> ob:lbuffer uint8 16ul -> ctx:aes_ctx m -> ib:lbuffer uint8 16ul -> ST unit
			     (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
			     (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1))
let aes128_encrypt_block #m ob ctx ib =
    push_frame();
    let kex = get_kex ctx in
    let n = get_nonce ctx in
    let st = create_state #m in
    load_block0 #m st ib;
    block_cipher #m st kex (size 10);
    store_block0 #m ob st;
    pop_frame()


inline_for_extraction
val aes128_key_block: #m:m_spec -> kb:lbuffer uint8 16ul -> ctx:aes_ctx m -> counter:size_t -> ST unit
			     (requires (fun h -> live h kb /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc kb) h0 h1))
let aes128_key_block #m kb ctx counter = 
    push_frame();
    let kex = get_kex ctx in
    let n = get_nonce ctx in
    let st = create_state #m in
    load_state #m st n counter;
    block_cipher #m st kex (size 10);
    store_block0 #m kb st;
    pop_frame()


inline_for_extraction
val aes_update4: #m:m_spec -> out:lbuffer uint8 64ul -> inp:lbuffer uint8 64ul -> ctx:aes_ctx m -> counter:size_t -> rounds:size_t{v rounds == 10} -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 b h1 -> modifies (loc out) h0 h1))
let aes_update4 #m out inp ctx ctr rounds =
  push_frame();
  let st = create_state #m in
  let kex = get_kex #m ctx in
  let n = get_nonce #m ctx in
  load_state #m st n ctr;
  block_cipher #m st kex rounds;
  xor_block #m out st inp;
  pop_frame()

inline_for_extraction
val aes_ctr_: #m:m_spec -> len:size_t -> out:lbuffer uint8 len -> inp:lbuffer uint8 len -> ctx:aes_ctx m -> counter:size_t -> rounds:size_t{v rounds == 10} -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let aes_ctr_ #m len out inp ctx counter rounds = 
  push_frame();
  let blocks64 = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks64 out 
    (fun i -> 
      let ctr = counter +. (i *. size 4) in
      let ib = sub inp (i *. size 64) (size 64) in
      let ob = sub out (i *. size 64) (size 64) in
      aes_update4 #m ob ib ctx ctr rounds);
  let rem = len %. size 64 in
  if (rem >. size 0) then (
      let ctr = counter +. (blocks64 *. size 4) in
      let ib = sub inp (blocks64 *. size 64) rem in
      let ob = sub out (blocks64 *. size 64) rem in
      let last = create 64ul (u8 0) in
      copy (sub last 0ul rem) ib;
      aes_update4 #m last last ctx ctr rounds;
      copy ob (sub last 0ul rem));
  pop_frame()


(* PATTERN FOR AVOIDING INLINING *)
val aes_ctr_bitslice: len:size_t -> out:lbuffer uint8 len -> inp:lbuffer uint8 len -> ctx:aes_ctx M32 -> counter:size_t -> rounds:size_t{v rounds == 10} -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let aes_ctr_bitslice len out inp ctx counter rounds = aes_ctr_ #M32 len out inp ctx counter rounds

inline_for_extraction
val aes_ctr_ni: len:size_t -> out:lbuffer uint8 len -> inp:lbuffer uint8 len -> ctx:aes_ctx MAES -> counter:size_t -> rounds:size_t{v rounds == 10} -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let aes_ctr_ni len out inp ctx counter rounds = aes_ctr_ #MAES len out inp ctx counter rounds

inline_for_extraction
val aes_ctr: #m:m_spec -> len:size_t -> out:lbuffer uint8 len -> inp:lbuffer uint8 len -> ctx:aes_ctx m -> counter:size_t -> rounds:size_t{v rounds == 10} -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h ctx))
			     (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1))
let aes_ctr #m len out inp ctx counter rounds = 
  match m with
  | M32 -> aes_ctr_bitslice len out inp ctx counter rounds 
  | MAES -> aes_ctr_ni len out inp ctx counter rounds
(* END PATTERN *)


inline_for_extraction
let aes128_ctr_encrypt (#m:m_spec) in_len out inp k n c = 
  push_frame();
  let ctx = create_ctx m in
  aes128_init #m ctx k n;
  aes_ctr #m in_len out inp ctx c (size 10);
  pop_frame()

inline_for_extraction
let aes128_ctr_decrypt (#m:m_spec) in_len out inp  k n c = 
  aes128_ctr_encrypt #m in_len out inp k n c

inline_for_extraction
let aes256_ctr_encrypt (#m:m_spec) in_len out inp k n c = 
  push_frame();
  let ctx = create_ctx m in
  aes256_init #m ctx k n;
  aes_ctr #m in_len out inp ctx c (size 14);
  pop_frame()

inline_for_extraction
let aes256_ctr_decrypt (#m:m_spec) inp_len out inp k n c = 
  aes256_ctr_encrypt #m inp_len out inp k n c
