module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.Buffer.Lemmas
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Spec = Spec.Blake2s
module Lemmas = Hacl.Impl.Lemmas

///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
noextract let op_String_Access #a #len m b = as_lseq #a #len b m

(* Functions to add to the libraries *)
inline_for_extraction
val update_sub: #a:Type0 -> #len:size_nat -> #xlen:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == xlen} -> x:lbuffer a xlen ->
  Stack unit
    (requires (fun h -> live h i /\ live h x))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 i h0 h1
                         /\ h1.[i] == LSeq.update_sub #a #len h0.[i] (v start) (v n) h0.[x]))

inline_for_extraction
let update_sub #a #len #olen i start n x =
  let buf = sub i start n in
  copy buf n x

///
/// Blake2s
///

(* Define algorithm parameters *)
type working_vector = lbuffer uint32 Spec.size_block_w
type message_block_w = lbuffer uint32 Spec.size_block_w
type message_block = lbuffer uint8 Spec.size_block
type hash_state = lbuffer uint32 Spec.size_hash_w
type idx = n:size_t{size_v n < 16}
type iv_t = lbuffer uint32 Spec.size_hash_w
type sigma_elt = n:size_t{size_v n < 16}
type sigma_t = lbuffer sigma_elt 160

noeq type state = {
  hash: hash_state;
  const_iv: iv_t;
  const_sigma: sigma_t;
}


noextract val state_invariant: h:mem -> st:state -> Type0
let state_invariant h st =
    live h st.hash /\ live h st.const_iv /\ live h st.const_sigma
  /\ disjoint st.hash st.const_iv /\ disjoint st.const_iv st.hash
  /\ disjoint st.hash st.const_sigma /\ disjoint st.const_sigma st.hash
  /\ disjoint st.const_iv st.const_sigma /\ disjoint st.const_sigma st.const_iv
  /\ h.[st.const_iv] == Spec.const_iv
  /\ h.[st.const_sigma] == Spec.const_sigma


(* Definition of constants *)
inline_for_extraction val create_const_iv: unit -> StackInline iv_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1 /\
		                  as_lseq r h1 == Spec.const_iv))

inline_for_extraction let create_const_iv () =
  assert_norm(List.Tot.length Spec.list_iv = 8);
  createL Spec.list_iv


inline_for_extraction val create_const_sigma: unit -> StackInline sigma_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1 /\
		                  as_lseq r h1 == Spec.const_sigma))

inline_for_extraction let create_const_sigma () =
  assert_norm(List.Tot.length Spec.list_sigma = 160);
  createL Spec.list_sigma


(* Define algorithm functions *)
val g1: wv:working_vector -> a:idx -> b:idx -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 h0.[wv] (v a) (v b) r))
let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:idx -> b:idx -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 h0.[wv] (v a) (v b) x))
let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (add_mod #U32 wv_a wv_b) x


val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  g2 wv a b x;
  g1 wv d a Spec.r1;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r2;
  g2 wv a b y;
  g1 wv d a Spec.r3;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r4


#reset-options "--max_fuel 0 --z3rlimit 150"

val blake2_round1 : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ disjoint wv m /\ disjoint wv const_sigma
                  /\ disjoint m wv /\ disjoint const_sigma wv
                  /\ h.[const_sigma] == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_round1 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i const_sigma =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = sub #sigma_elt #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(s.(size 0))) (m.(s.(size 1)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(s.(size 2))) (m.(s.(size 3)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(s.(size 4))) (m.(s.(size 5)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(s.(size 6))) (m.(s.(size 7)))


val blake2_round2 : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ disjoint wv m /\ disjoint wv const_sigma
                  /\ disjoint m wv /\ disjoint const_sigma wv
                  /\ h.[const_sigma] == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i const_sigma =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = sub #sigma_elt #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(s.(size 8))) (m.(s.(size 9)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(s.(size 10))) (m.(s.(size 11)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(s.(size 12))) (m.(s.(size 13)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(s.(size 14))) (m.(s.(size 15)))


val blake2_round : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv
                   /\ h.[const_sigma] == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round h0.[m] (v i) h0.[wv]))

let blake2_round wv m i const_sigma =
  blake2_round1 wv m i const_sigma;
  blake2_round2 wv m i const_sigma


val blake2_compress1 : wv:working_vector ->
  s:hash_state -> m:message_block_w ->
  offset:uint64 -> flag:Spec.last_block_flag -> const_iv:iv_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv /\ live h const_iv
                     /\ h.[const_iv] == Spec.const_iv
                     /\ disjoint wv s /\ disjoint wv m /\ disjoint wv const_iv
                     /\ disjoint s wv /\ disjoint m wv /\ disjoint const_iv wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_compress1 h0.[wv] h0.[s] h0.[m] offset flag))

[@ Substitute ]
let blake2_compress1 wv s m offset flag const_iv =
  update_sub wv (size 0) (size 8) s;
  update_sub wv (size 8) (size 8) const_iv;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 32) in
  // BB. Note that using the ^. operator here would break extraction !
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


val blake2_compress2 :
  wv:working_vector -> m:message_block_w -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ h.[const_sigma] == Spec.const_sigma
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 h0.[wv] h0.[m]))


[@ Substitute ]
let blake2_compress2 wv m const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size Spec.rounds_in_f) wv
    (fun hi ->  Spec.blake2_round hi.[m])
    (fun i ->
      blake2_round wv m i const_sigma;
      Lemmas.lemma_repeati Spec.rounds_in_f (Spec.blake2_round h0.[m]) h0.[wv] (v i))


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner h0.[wv] (v i) h0.[s]))

[@ Substitute ]
let blake2_compress3_inner wv i s const_sigma =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  // BB. Note that using the ^. operator here would break extraction !
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  wv:working_vector -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma
                     /\ h.[const_sigma] == Spec.const_sigma
                     /\ disjoint wv s /\ disjoint wv const_sigma
                     /\ disjoint s wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 h0.[wv] h0.[s]))

[@ Substitute ]
let blake2_compress3 wv s const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size 8) s
    (fun hi -> Spec.blake2_compress3_inner hi.[wv])
    (fun i -> blake2_compress3_inner wv i s const_sigma;
           Lemmas.lemma_repeati 8 (Spec.blake2_compress3_inner h0.[wv]) h0.[s] (v i))


val blake2_compress :
  s:hash_state -> m:message_block_w ->
  offset:uint64 -> f:Spec.last_block_flag -> const_iv:iv_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h const_iv /\ live h const_sigma
                         /\ h.[const_sigma] == Spec.const_sigma
                         /\ h.[const_iv] == Spec.const_iv
                         /\ disjoint s m /\ disjoint s const_sigma /\ disjoint s const_iv
                         /\ disjoint m s /\ disjoint const_sigma s /\ disjoint const_iv s))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress h0.[s] h0.[m] offset f))

let blake2_compress s m offset flag const_iv const_sigma =
  (**) let hinit = ST.get () in
  alloc #hinit (size 16) (u32 0) s
  (fun h0 ->
    let s0 = h0.[s] in
    let m0 = h0.[m] in
    (fun _ sv -> sv == Spec.Blake2s.blake2_compress s0 m0 offset flag))
  (fun wv ->
    blake2_compress1 wv s m offset flag const_iv;
    blake2_compress2 wv m const_sigma;
    blake2_compress3 wv s const_sigma)

val blake2s_update_block:
    st:state
  -> dd_prev:size_t{(size_v dd_prev + 1) * Spec.size_block <= max_size_t}
  -> d:message_block ->
  Stack unit
    (requires (fun h -> state_invariant h st /\ live h d
                   /\ disjoint st.hash d /\ disjoint d st.hash))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                         /\ h1.[st.hash] == Spec.blake2s_update_block (v dd_prev) h0.[d] h0.[st.hash]))

let blake2s_update_block st dd_prev d =
  let h0 = ST.get () in
  alloc #h0 (size 16) (u32 0) st.hash
  (fun h ->
    let d0 = h.[d] in
    let s0 = h.[st.hash] in
    (fun _ sv -> sv == Spec.blake2s_update_block (v dd_prev) d0 s0))
  (fun block ->
    uints_from_bytes_le block (size Spec.size_block_w) d;
    let offset64 = to_u64 (size_to_uint32 ((dd_prev +. (size 1)) *. (size Spec.size_block))) in
    blake2_compress st.hash block offset64 false st.const_iv st.const_sigma
  )


val blake2s_mkstate: unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures  (fun h0 st h1 -> state_invariant h1 st
                          /\ h1.[st.hash] == LSeq.create Spec.size_hash_w (u32 0)))

let blake2s_mkstate () =
  {
    hash = create (size Spec.size_hash_w) (u32 0);
    const_iv = create_const_iv ();
    const_sigma = create_const_sigma ();
  }


val blake2s_init_hash:
    st:state
  -> kk:size_t{v kk <= 32}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
     (requires (fun h -> state_invariant h st))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                          /\ h1.[st.hash] == Spec.Blake2s.blake2s_init_hash h0.[st.hash] (v kk) (v nn)))

let blake2s_init_hash st kk nn =
  let s0 = st.hash.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  st.hash.(size 0) <- s0'


val blake2s_init:
  #vkk:size_t
  -> st:state
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ live h k
                   /\ disjoint st.hash k /\ disjoint k st.hash))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                         /\ h1.[st.hash] == Spec.Blake2s.blake2s_init (v kk) h0.[k] (v nn)))

[@ Substitute ]
let blake2s_init #vkk st k kk nn =
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) st.hash
  (fun h -> (fun _ sv -> sv == Spec.Blake2s.blake2s_init (v kk) h0.[k] (v nn)))
  (fun key_block ->
    copy st.hash (size Spec.size_hash_w) st.const_iv;
    blake2s_init_hash st kk nn;
    if kk =. (size 0) then ()
    else begin
      update_sub key_block (size 0) kk k;
      blake2s_update_block st (size 0) key_block end
  )


val blake2s_update_multi_iteration:
    st:state
  -> dd_prev:size_t
  -> dd:size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d:lbuffer uint8 (v dd * Spec.size_block)
  -> i:size_t{v i + 1 <= v dd} ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ live h d /\ disjoint st.hash d /\ disjoint d st.hash))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                         /\ h1.[st.hash] == Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) h0.[d] (v i) h0.[st.hash]))

[@ Substitute ]
let blake2s_update_multi_iteration st dd_prev dd d i =
  let block = sub d (i *. size Spec.size_block) (size Spec.size_block) in
  blake2s_update_block st (dd_prev +. i) block


val blake2s_update_multi:
    st: state
  -> dd_prev: size_t
  -> dd: size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d: lbuffer uint8 (size_v dd * Spec.size_block) ->
   Stack unit
     (requires (fun h -> state_invariant h st
                    /\ live h d /\ disjoint st.hash d /\ disjoint d st.hash))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                          /\ h1.[st.hash] == Spec.blake2s_update_multi (v dd_prev) (v dd) h0.[d] h0.[st.hash]))

let blake2s_update_multi st dd_prev dd d =
  (**) let h0 = ST.get () in
  loop #h0 dd st.hash
  (fun h -> Spec.Blake2s.blake2s_update_multi_iteration (v dd_prev) (v dd) h.[d])
  (fun i ->
    blake2s_update_multi_iteration st dd_prev dd d i;
    Lemmas.lemma_repeati (v dd) (Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) h0.[d]) h0.[st.hash] (v i))


val blake2s_update_last:
    #vlen: size_t
  -> st: state
  -> ll: size_t
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block /\ len == vlen}
  -> flag_key: bool ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ live h last /\ disjoint st.hash last /\ disjoint last st.hash))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                         /\ h1.[st.hash] == Spec.Blake2s.blake2s_update_last (v ll) (v len) h0.[last] flag_key h0.[st.hash]))


let blake2s_update_last #vlen st ll last len fk =
  let ll64 : uint64 = to_u64 #U32 (size_to_uint32 ll) in
  let ll_plus_block_bytes64 = ll64 +. (u64 Spec.size_block) in
  assume(ll_plus_block_bytes64 == u64 (size_v ll + Spec.size_block));
  (**) let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) st.hash
  (fun h ->
    let hash0 = h0.[st.hash] in
    let last0 = h0.[last] in
    (fun _ r -> r == Spec.Blake2s.blake2s_update_last (v ll) (v len) last0 fk hash0)
  )
  (fun last_block ->
    update_sub last_block (size 0) len last;
    (**) let h1 = ST.get () in
    alloc #h1 (size Spec.size_block_w) (u32 0) st.hash
    (fun h ->
      let hash1 = h1.[st.hash] in
      let last_block1 = h1.[last_block] in
      (fun _ r -> r == Spec.Blake2s.blake2s_update_last_block (v ll) last_block1 fk hash1)
    )
    (fun last_block_w ->
      uint32s_from_bytes_le last_block_w (size 16) last_block;
      if not fk then
        blake2_compress st.hash last_block_w ll64 true st.const_iv st.const_sigma
      else
        blake2_compress st.hash last_block_w ll_plus_block_bytes64 true st.const_iv st.const_sigma
    )
  )


val blake2s_update_last_empty:
  st: state ->
  Stack unit
    (requires (fun h -> state_invariant h st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1
                         /\ (let data = LSeq.create Spec.size_block (u8 0) in
                           h1.[st.hash] == Spec.Blake2s.blake2s_update_last (Spec.size_block) (Spec.size_block) data false h0.[st.hash])))

let blake2s_update_last_empty st =
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) st.hash
  (fun h ->
    let hash0 = h.[st.hash] in
    (fun _ r ->
      let data = LSeq.create Spec.size_block (u8 0) in
      r ==  Spec.Blake2s.blake2s_update_last (Spec.size_block) (Spec.size_block) data false hash0))
  (fun data ->
      blake2s_update_last #(size Spec.size_block) st (size Spec.size_block) data (size Spec.size_block) false
  )


val blake2s_finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> st: state
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ live h output /\ disjoint output st.hash /\ disjoint st.hash output))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2s.blake2s_finish h0.[st.hash] (v nn)))

let blake2s_finish #vnn output s nn =
  (**) let h0 = ST.get () in
  alloc #h0 (size 32) (u8 0) output
  (fun h ->
    (fun _ r -> r == Spec.Blake2s.blake2s_finish h0.[s.hash] (v nn))
  )
  (fun full ->
    uints_to_bytes_le full (size 8) s.hash;
    let final = sub full (size 0) nn in
    copy output nn final)


val blake2s2:
    #vll: size_t
  -> #vkk: size_t
  -> #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> d: lbuffer uint8 (v vll)
  -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ ll == vll} // This could be relaxed
  -> k: lbuffer uint8 (v vkk)
  -> kk: size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> live h output /\ live h d /\ live h k
                   /\ disjoint output d /\ disjoint d output
                   /\ disjoint output k /\ disjoint k output))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn)))

let blake2s2 #vll #vkk #vnn output d ll k kk nn =
  let fk = if kk =. (size 0) then false else true in
  let rem = ll %. (size Spec.size_block) in
  let nblocks = ll /. (size Spec.size_block) in
  let blocks = sub #_ #_ #(v nblocks * Spec.size_block) d (size 0) (nblocks *. (size Spec.size_block)) in
  let last = sub #_ #_ #(v rem) d (nblocks *. (size Spec.size_block)) rem in
  let st = blake2s_mkstate () in
  blake2s_init #vkk st k kk nn;
  if  ll =. (size 0) && kk =. (size 0) then blake2s_update_last_empty st
  else begin
    let nprev = if kk =. (size 0) then (size 0) else (size 1) in
    blake2s_update_multi st nprev nblocks d;
    blake2s_update_last #rem st ll last rem fk
  end;
  blake2s_finish #vnn output st nn



inline_for_extraction val mkstate:
  #h0: mem ->
  #b: Type0 ->
  #w: Type0 ->
  #wlen: size_nat ->
  write: lbuffer w wlen ->
  spec:(h:mem -> GTot(r:b -> LSeq.lseq w (wlen) -> Type)) ->
  impl:(st:state ->
        Stack b
        (requires (fun h -> state_invariant h st
		                 /\ preserves_live h0 h
		                 /\ modifies3 st.hash st.const_iv st.const_sigma h0 h))
        (ensures (fun h r h' -> preserves_live h h'
                           /\ modifies2 st.hash write h h' /\
			 spec h0 r (as_seq write h')))) ->
  Stack b
    (requires (fun h -> h == h0 /\ live h write))
    (ensures (fun h0 r h1 -> preserves_live h0 h1 /\
		          modifies1 write h0 h1 /\
		          spec h0 r (as_seq write h1)))

let mkstate #h0 #b #w #wlen write spec impl =
  admit();
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_hash_w) (u32 0) write
  (fun h -> (fun _ sv -> True))
  (fun hash ->
    let h0 = ST.get () in
    alloc_with #h0 (size 8) Spec.const_iv create_const_iv write
    (fun h -> (fun _ _ -> True))
    (fun const_iv ->
      let h0 = ST.get () in
      alloc_with #h0 (size 160) Spec.const_sigma create_const_sigma write
      (fun h -> (fun _ _ -> True))
      (fun const_sigma ->
        let st = {hash = hash; const_iv = const_iv; const_sigma = const_sigma} in
        impl st
      )
    )
  )


val blake2s:
    #vll: size_t
  -> #vkk: size_t
  -> #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> d: lbuffer uint8 (v vll)
  -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ ll == vll} // This could be relaxed
  -> k: lbuffer uint8 (v vkk)
  -> kk: size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> live h output /\ live h d /\ live h k
                   /\ disjoint output d /\ disjoint d output
                   /\ disjoint output k /\ disjoint k output))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn)))

let blake2s #vll #vkk #vnn output d ll k kk nn =
  let h0 = ST.get () in
  mkstate #h0 output
  (fun h -> (fun _ sv -> sv == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn)))
  (fun st ->
    let fk = if kk =. (size 0) then false else true in
    let rem = ll %. (size Spec.size_block) in
    let nblocks = ll /. (size Spec.size_block) in
    let blocks = sub #_ #_ #(v nblocks * Spec.size_block) d (size 0) (nblocks *. (size Spec.size_block)) in
    let last = sub #_ #_ #(v rem) d (nblocks *. (size Spec.size_block)) rem in
    blake2s_init #vkk st k kk nn;
    if ll =. (size 0) && kk =. (size 0) then blake2s_update_last_empty st
    else begin
      let nprev = if kk =. (size 0) then (size 0) else (size 1) in
      blake2s_update_multi st nprev nblocks d;
      blake2s_update_last #rem st ll last rem fk
    end;
    blake2s_finish #vnn output st nn
  )
