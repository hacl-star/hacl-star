module Hacl.Impl.Aes.NI

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Vec128

type lbuffer a len = b:buffer a{length b == len}
type bytes = buffer FStar.UInt8.t
type lbytes l = b:bytes {length b == l} 

inline_for_extraction 
val blit: #a:Type -> src:buffer a -> start1:size_t -> dst:buffer a -> start2:size_t -> len:size_t -> ST unit
               (requires (fun h -> live h src /\ live h dst)) (ensures (fun h0 _ h1 -> live h1 src /\ live h1 dst /\ modifies (loc_buffer dst) h0 h1))
let blit #a src start1 dst start2 len = 
    blit src (Lib.RawIntTypes.size_to_UInt32 start1) dst (Lib.RawIntTypes.size_to_UInt32 start2) (Lib.RawIntTypes.size_to_UInt32 len) 

inline_for_extraction 
val load64_le: b:lbytes 8 -> ST uint64 
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let load64_le b = 
    let u = C.Endianness.load64_le b in
    Lib.RawIntTypes.u64_from_UInt64 u

inline_for_extraction 
val store64_le: b:lbytes 8 -> u:uint64 -> ST unit
               (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> live h1 b /\ modifies (loc_buffer b) h0 h1))
let store64_le b u = 
    C.Endianness.store64_le b (Lib.RawIntTypes.u64_to_UInt64 u)

inline_for_extraction
let htobe32 (u:uint32) = Lib.RawIntTypes.u32_from_UInt32 (C.Endianness.htobe32 (Lib.RawIntTypes.u32_to_UInt32 u))

inline_for_extraction 
val gcreateL: #a:Type -> l:list a -> ST (buffer a)
	      (requires (fun h -> True))
	      (ensures (fun h0 b h1 -> recallable b /\ length b == List.Tot.length l))
let gcreateL #a l = 
    gcmalloc_of_list FStar.HyperStack.root l


inline_for_extraction
val sub: #a:Type -> b:buffer a -> i:size_t -> j:size_t -> ST (buffer a) 
         (requires (fun h -> live h b)) (ensures (fun h0 _ h1 -> h0 == h1))
let sub #a b i j = Lib.RawIntTypes.(sub b (size_to_UInt32 i) (size_to_UInt32 j))

inline_for_extraction 
val loop_nospec: #h0:mem -> #a:Type -> n:size_t -> buf:buffer a -> 
		 impl:(size_t -> ST unit (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> modifies (loc_buffer buf) h0 h1 /\ live h1 buf))) -> ST unit 
         (requires (fun h -> live h buf)) (ensures (fun h0 _ h1 -> live h1 buf /\ modifies (loc_buffer buf) h0 h1))
inline_for_extraction 
let loop_nospec #h0 #a (n:size_t) (buf:buffer a) impl =
  let inv (h1:mem) (j:nat) = True in
  let f' (j:UInt32.t{0 <= UInt32.v j /\ UInt32.v j <= size_v n}) : Stack unit
      (requires (fun h -> inv h (UInt32.v j)))
      (ensures (fun h1 _ h2 -> inv h2 (UInt32.v j + 1))) =
      impl (Lib.RawIntTypes.size_from_UInt32 j) in
  C.Loops.for 0ul (Lib.RawIntTypes.size_to_UInt32 n) inv f'

inline_for_extraction
let op_Array_Assignment #a #b #c buf i v = upd #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i) v
inline_for_extraction
let op_Array_Access #a #b #c buf i  = index #a #b #c buf (Lib.RawIntTypes.size_to_UInt32 i)

(* Parameters for AES-128 *)
noextract inline_for_extraction let nb =  4
noextract inline_for_extraction let nk =  4 // 4, 6, or 8 for 128/192/256
noextract inline_for_extraction let nr =  10 // 10, 12, or 14 for 128/192/256

noextract inline_for_extraction let blocklen =  16 // 4 * nb
noextract inline_for_extraction let keylen   =  16 // 4 * nk
noextract inline_for_extraction let xkeylen  =  176 // 4 * nb * (nr + 1)

type block = lbytes blocklen
type skey  = lbytes keylen

type state = lbuffer vec128 4
type key1 =  lbuffer vec128 1
type keyr =  lbuffer vec128 9
type keyex = lbuffer vec128 11

inline_for_extraction
val aes_enc: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc st key = 
    st.(size 0) <- ni_aes_enc st.(size 0) key.(size 0);
    st.(size 1) <- ni_aes_enc st.(size 1) key.(size 0);
    st.(size 2) <- ni_aes_enc st.(size 2) key.(size 0);
    st.(size 3) <- ni_aes_enc st.(size 3) key.(size 0)

inline_for_extraction
val aes_enc_last: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc_last st key = 
    st.(size 0) <- ni_aes_enc_last st.(size 0) key.(size 0);
    st.(size 1) <- ni_aes_enc_last st.(size 1) key.(size 0);
    st.(size 2) <- ni_aes_enc_last st.(size 2) key.(size 0);
    st.(size 3) <- ni_aes_enc_last st.(size 3) key.(size 0)

inline_for_extraction
val add_round_key: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let add_round_key st key = 
    st.(size 0) <- vec128_xor st.(size 0) key.(size 0);
    st.(size 1) <- vec128_xor st.(size 1) key.(size 0);
    st.(size 2) <- vec128_xor st.(size 2) key.(size 0);
    st.(size 3) <- vec128_xor st.(size 3) key.(size 0)

val enc_rounds: st:state -> key:keyr -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let enc_rounds st key = 
    let h0 = ST.get() in
    loop_nospec #h0 (size 9) st 
      (fun i -> aes_enc st (sub key i (size 1)))


inline_for_extraction
val block_cipher: st:state -> key:keyex -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let block_cipher st key = 
    let k0 = sub key (size 0) (size 1) in
    let kr = sub key (size 1) (size 9) in
    let kn = sub key (size 10) (size 1) in
    add_round_key st k0;
    enc_rounds st kr;
    aes_enc_last st kn
   
let rcon =  gcreateL [u8(0x8d); u8(0x01); u8(0x02); u8(0x04); u8(0x08); u8(0x10); u8(0x20); u8(0x40); u8(0x80); u8(0x1b); u8(0x36)]

inline_for_extraction
val aes_keygen_assist: ok:key1 -> ik:key1 -> rcon:uint8 -> ST unit
			     (requires (fun h -> live h ok /\ live h ik))
			     (ensures (fun h0 _ h1 -> live h1 ok /\ live h1 ik /\ modifies (loc_buffer ok) h0 h1))
let aes_keygen_assist ok ik rcon = 
    ok.(size 0) <- ni_aes_keygen_assist ik.(size 0) rcon		      

inline_for_extraction 
val key_expansion_step: next:key1 -> prev:key1 -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let key_expansion_step next prev = 
    next.(size 0) <- vec128_shuffle32 next.(size 0) (vec128_shuffle32_spec (u8 3) (u8 3) (u8 3) (u8 3));
    let key = prev.(size 0) in
    let key = vec128_xor key (vec128_shift_left key (u32 32)) in
    let key = vec128_xor key (vec128_shift_left key (u32 32)) in
    let key = vec128_xor key (vec128_shift_left key (u32 32)) in
    next.(size 0) <- vec128_xor next.(size 0) key


val key_expansion: keyx:keyex -> key:skey -> ST unit
			     (requires (fun h -> live h keyx /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc_buffer keyx) h0 h1))
let key_expansion keyx key = 
    keyx.(size 0) <- vec128_load_le key;
    let h0 = ST.get() in
    (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST INSISTS ON AN IMMEDIATE RCON *)
    (* loop_nospec #h0 (size 10) keyx 
    (fun i -> 
       let prev = sub keyx i (size 1) in
       let next = sub keyx (i +. size 1) (size 1) in
       aes_keygen_assist next rcon.(i +. size 1);
       key_expansion_step next prev)
		     *)
       let prev = sub keyx (size 0) (size 1) in
       let next = sub keyx (size 1) (size 1) in
       aes_keygen_assist next prev (u8 0x01);
       key_expansion_step next prev;
       let prev = sub keyx (size 1) (size 1) in
       let next = sub keyx (size 2) (size 1) in
       aes_keygen_assist next prev (u8 0x02);
       key_expansion_step next prev;
       let prev = sub keyx (size 2) (size 1) in
       let next = sub keyx (size 3) (size 1) in
       aes_keygen_assist next prev (u8 0x04);
       key_expansion_step next prev;
       let prev = sub keyx (size 3) (size 1) in
       let next = sub keyx (size 4) (size 1) in
       aes_keygen_assist next prev (u8 0x08);
       key_expansion_step next prev;
       let prev = sub keyx (size 4) (size 1) in
       let next = sub keyx (size 5) (size 1) in
       aes_keygen_assist next prev (u8 0x10);
       key_expansion_step next prev;
       let prev = sub keyx (size 5) (size 1) in
       let next = sub keyx (size 6) (size 1) in
       aes_keygen_assist next prev (u8 0x20);
       key_expansion_step next prev;
       let prev = sub keyx (size 6) (size 1) in
       let next = sub keyx (size 7) (size 1) in
       aes_keygen_assist next prev (u8 0x40);
       key_expansion_step next prev;
       let prev = sub keyx (size 7) (size 1) in
       let next = sub keyx (size 8) (size 1) in
       aes_keygen_assist next prev (u8 0x80);
       key_expansion_step next prev;
       let prev = sub keyx (size 8) (size 1) in
       let next = sub keyx (size 9) (size 1) in
       aes_keygen_assist next prev (u8 0x1b);
       key_expansion_step next prev;
       let prev = sub keyx (size 9) (size 1) in
       let next = sub keyx (size 10) (size 1) in
       aes_keygen_assist next prev (u8 0x36);
       key_expansion_step next prev
       

inline_for_extraction
val aes128_block: st:state -> keyx:keyex -> nonce:state -> counter:size_t -> ST unit
			     (requires (fun h -> live h st /\ live h keyx /\ live h nonce))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 nonce /\ live h1 keyx /\ modifies (loc_buffer st) h0 h1))
let aes128_block st keyx nonce counter = 
    let counter0 = htobe32 (size_to_uint32 counter) in
    let counter1 = htobe32 (size_to_uint32 (counter +. size 1)) in
    let counter2 = htobe32 (size_to_uint32 (counter +. size 2)) in
    let counter3 = htobe32 (size_to_uint32 (counter +. size 3)) in
    st.(size 0) <- vec128_insert32 nonce.(size 0) counter0 (u8 3);
    st.(size 1) <- vec128_insert32 nonce.(size 0) counter1 (u8 3);
    st.(size 2) <- vec128_insert32 nonce.(size 0) counter2 (u8 3);
    st.(size 3) <- vec128_insert32 nonce.(size 0) counter3 (u8 3);
    block_cipher st keyx

val aes128_ctr: out:bytes -> inp:bytes -> len:size_t -> key:skey -> nonce:lbytes 12 -> counter:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h key /\ live h nonce))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let aes128_ctr out inp len key nonce counter = 
  push_frame();
  let kex = alloca vec128_zero 11ul in
  key_expansion kex key;
  let st = alloca vec128_zero 4ul in
  let nb = alloca 0uy 16ul in
  blit nonce (size 0) nb (size 0) (size 12);
  let nvec = alloca vec128_zero 1ul in
  nvec.(size 0) <- vec128_load_le nb;

  let blocks64 = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks64 out 
    (fun i -> 
      aes128_block st kex nvec (counter +. (i *. size 4));
      st.(size 0) <- vec128_xor st.(size 0) (vec128_load_le (sub inp (i *. size 64) (size 16)));
      st.(size 1) <- vec128_xor st.(size 1) (vec128_load_le (sub inp (size 16 +. (i *. size 64)) (size 16)));
      st.(size 2) <- vec128_xor st.(size 2) (vec128_load_le (sub inp (size 32 +. (i *. size 64)) (size 16)));
      st.(size 3) <- vec128_xor st.(size 3) (vec128_load_le (sub inp (size 48 +. (i *. size 64)) (size 16)));
      vec128_store_le (sub out (i *. size 64) (size 16)) st.(size 0);
      vec128_store_le (sub out (size 16 +. (i *. size 64)) (size 16)) st.(size 1);
      vec128_store_le (sub out (size 32 +. (i *. size 64)) (size 16)) st.(size 2);
      vec128_store_le (sub out (size 48 +. (i *. size 64)) (size 16)) st.(size 3));

  let kb = alloca 0uy 64ul in
  let rem = len %. size 64 in
  if (rem >. size 0) then (
    aes128_block st kex nvec (counter +. (blocks64 *. size 4));
    vec128_store_le (sub kb (size 0) (size 16)) st.(size 0);
    vec128_store_le (sub kb (size 16) (size 16)) st.(size 1);
    vec128_store_le (sub kb (size 32) (size 16)) st.(size 2);
    vec128_store_le (sub kb (size 48) (size 16)) st.(size 3);
    let start = blocks64 *. size 64 in
    loop_nospec #h0 rem out
	(fun j -> out.(start +. j) <- FStar.UInt8.(inp.(start +. j) ^^ kb.(j))));
  pop_frame()

let aes128_encrypt out inp in_len k n c = aes128_ctr out inp in_len k n c
let aes128_decrypt out inp in_len k n c = aes128_ctr out inp in_len k n c
