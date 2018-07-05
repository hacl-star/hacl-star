module Hacl.Impl.SHA2

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.Buffer.Lemmas

open Spec.SHA2

module ST = FStar.HyperStack.ST
module S = Lib.Sequence
module Spec = Spec.SHA2
module Lemmas = Hacl.Impl.Lemmas


///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
let op_String_Access #a #len m b = as_lseq #a #len b m

(* Functions to add to the libraries *)
val update_sub: #a:Type0 -> #len:size_nat -> #xlen:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == xlen} -> x:lbuffer a xlen ->
  Stack unit
    (requires (fun h -> live h i /\ live h x))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 i h0 h1
                         /\ h1.[i] == Lib.Sequence.update_sub #a #len h0.[i] (v start) (v n) h0.[x]))

[@ Substitute]
let update_sub #a #len #olen i start n x =
  let i' = sub i start n in
  copy i' n x


(* Define algorithm parameters *)
inline_for_extraction let size_hash_w : size_t = size Spec.size_hash_w
inline_for_extraction let size_block_w : size_t = size Spec.size_block_w
inline_for_extraction let size_block (p:Spec.parameters) = size (Spec.size_block p)
inline_for_extraction let max_input (p:Spec.parameters) = Spec.max_input p


(* Definition: Types for block and hash as sequences of words *)
type block_w (p:Spec.parameters) = b:lbuffer (uint_t p.wt) 16
type hash_w (p:Spec.parameters) = b:lbuffer (uint_t p.wt) Spec.size_hash_w
type ws_w (p:Spec.parameters) = b:lbuffer (uint_t p.wt) p.kSize
type iv_t (p:Spec.parameters) = b:lbuffer (uint_t p.wt) Spec.size_hash_w

unfold type kTable (p:Spec.parameters) = b:lbuffer (uint_t p.wt) p.kSize
unfold type wsTable (p:Spec.parameters) = b:lbuffer (uint_t p.wt) p.kSize


#set-options "--max_fuel 0 --z3rlimit 50"

(* Definition of the scheduling function (part 1) *)
val step_ws0: p:Spec.parameters -> b:block_w p -> i:size_t{size_v i < 16} -> s:wsTable p ->
  Stack unit
  (requires (fun h -> live h s /\ live h b))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
            /\ h1.[s] == Spec.step_ws0 p h0.[b] (v i) h0.[s]))

let step_ws0 p b i s =
  s.(i) <- b.(i)


(* Definition of the scheduling function (part 2) *)
val step_ws1: p:Spec.parameters -> i:size_t{size_v i >= 16 /\ size_v i < p.kSize} -> s:wsTable p ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                       /\ h1.[s] == Spec.step_ws1 p (v i) h0.[s]))

let step_ws1 p i s =
  let t16 = s.(i -. size 16) in
  let t15 = s.(i -. size 15) in
  let t7  = s.(i -. size 7) in
  let t2  = s.(i -. size 2) in
  let s1 = _sigma1 p t2 in
  let s0 = _sigma0 p t15 in
  s.(i) <- s1 +. (t7 +. (s0 +. t16))


(* Definition of the core scheduling function *)
val loop_ws0: p:Spec.parameters -> s:ws_w p -> b:block_w p ->
  Stack unit
  (requires (fun h -> live h s /\ live h b
                 /\ disjoint s b /\ disjoint b s))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                       /\ h1.[s] == Spec.loop_ws0 p h0.[b] h0.[s]))

let loop_ws0 p s b =
  (**) let h0 = ST.get () in
  loop #h0 (size 16) s
    (fun hi -> Spec.step_ws0 p hi.[b])
    (fun i -> step_ws0 p b i s;
           Lemmas.lemma_repeati 16 (Spec.step_ws0 p h0.[b]) h0.[s] (v i))


val loop_ws1: p:Spec.parameters -> s:ws_w p ->
  Stack unit
  (requires (fun h -> live h s))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                       /\ h1.[s] == Spec.loop_ws1 p h0.[s]))

let loop_ws1 p s =
  (**) let h0 = ST.get () in
  loop #h0 (size p.kSize -. size 16) s
    (fun hi -> Spec.step_ws1 p)
    (fun i -> step_ws1 p i s;
           Lemmas.lemma_repeati (p.kSize - 16) (Spec.step_ws1 p) h0.[s] (v i + 16))


(* Definition of the core scheduling function *)
val ws: p:Spec.parameters -> s:ws_w p -> b:block_w p ->
  Stack unit
  (requires (fun h -> live h s /\ live h b
                 /\ disjoint s b /\ disjoint b s))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                       /\ h1.[s] == Spec.ws p h0.[b]))

let ws p s b =
  loop_ws0 p s b;
  loop_ws1 p s


(* Definition of the core shuffling function *)
val shuffle_core: p:Spec.parameters -> const_kt:kTable p -> wst:wsTable p -> t:size_t{size_v t < p.kSize} -> hash:hash_w p ->
  Stack unit
  (requires (fun h -> live h const_kt /\ live h wst /\ live h hash))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hash h0 h1
                       /\ h1.[hash] == Spec.shuffle_core p h0.[wst] (v t) h0.[hash]))

let shuffle_core p kt wst t hash =
  let a0 = hash.(size 0) in
  let b0 = hash.(size 1) in
  let c0 = hash.(size 2) in
  let d0 = hash.(size 3) in
  let e0 = hash.(size 4) in
  let f0 = hash.(size 5) in
  let g0 = hash.(size 6) in
  let h0 = hash.(size 7) in

  let wst_t = wst.(t) in
  let kt_t = kt.(t) in
  let t1 = h0 +. (_Sigma1 p e0) +. ((_Ch p e0 f0 g0) +. (kt_t +. wst_t)) in
  let t2 = (_Sigma0 p a0) +. (_Maj p a0 b0 c0) in

  hash.(size 0) <- (t1 +. t2);
  hash.(size 1) <- a0;
  hash.(size 2) <- b0;
  hash.(size 3) <- c0;
  hash.(size 4) <- (d0 +. t1);
  hash.(size 5) <- e0;
  hash.(size 6) <- f0;
  hash.(size 7) <- g0


(* Definition of the full shuffling function *)
val shuffle: p:Spec.parameters -> kt:kTable p -> wst:wsTable p -> hash:hash_w p ->
  Stack unit
        (requires (fun h -> live h kt /\ live h wst /\ live h hash))
        (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 hash h0 h1
                             /\ h1.[hash] == Spec.shuffle p h0.[wst] h0.[hash]))
let shuffle p kt wst hash =
  (**) let h0 = ST.get () in
  loop #h0 (size p.kSize) hash
    (fun hi -> Spec.shuffle_core p hi.[wst])
    (fun i -> shuffle_core p kt wst i hash;
           Lemmas.lemma_repeati p.kSize (Spec.shuffle_core p h0.[wst]) h0.[hash] (v i))


(* Definition of the core compression function *)
val compress: p:Spec.parameters -> b:block_w p -> kt:kTable p -> s:hash_w p ->
  Stack unit
  (requires (fun h -> live h b /\ live h kt /\ live h s))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                       /\ h1.[s] == Spec.compress p h0.[b] h0.[s]))

let compress p b kt s =
  (**) let h0 = ST.get () in
  alloc #h0 (size p.kSize) (u32 0) s
  (fun h0 -> (fun _ sv -> True))
  (fun wst ->
    (**) let h0 = ST.get () in
    alloc #h0 (size_block p) (u8 0) s
    (fun h0 -> (fun _ sv -> True))
    (fun s1 ->
      copy s1 (size (size_hash p)) s;
      ws p wst b;
      shuffle p kt wst s1;
      map2 (size (size_hash p)) (fun x y -> x +. y) s s1
    )
  )


(* Definition of the function returning the number of padding blocks for a single input block *)
let number_blocks_padding_single (p:parameters) (len:size_t{v len <= Spec.size_block p}) : size_t =
  if len <. size_block p -. size (numbytes (lenType p)) then size 1 else size 2


val pad:
    vn:size_nat
  -> vlen:size_nat
  -> p:Spec.parameters
  -> blocks:lbuffer uint8 (2 * Spec.size_block p)
  -> n:size_t{v n = vn}
  -> last:lbuffer uint8 vlen
  -> len:size_t{v len = vlen} ->
  Stack unit
  (requires (fun h -> live h blocks /\ live h last))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 blocks h0 h1))

let pad vn vlen p blocks n last len =
  // Copy the end of the data in the final padded blocks
  let blast = sub blocks (size 0) len in
  copy blast len last;
  // Write the 0x80 byte right after the data
  upd blocks len (u8 0x80);
  // Compute the encoding for the total number bits
  let nn = cast (lenType p) n in
  let nlen = cast (lenType p) (size_to_uint32 len) in
  let n8 = cast (lenType p) (size_to_uint32 (size 8)) in
  let nsize_block = cast (lenType p) (size (Spec.size_block p)) in
  let tlen = nn *. nsize_block +. nlen in
  let tlenbits = tlen *. n8 in
  // Compute the position for the encoded length
  let nblocks = number_blocks_padding_single p len in
  let pos = nblocks *. (size (Spec.size_block p)) -. (size (numbytes (lenType p))) in
  // Encode the total length in bits at the end of the padding
  let bencoding = sub #uint8 #(2 * Spec.size_block p) #(numbytes (lenType p)) blocks pos (size (numbytes (lenType p))) in
  uint_to_bytes_be bencoding tlenbits


(* Definition of the SHA2 state *)
//let len_block_t (p:Spec.parameters) = l:size_t{uint_v l < Spec.size_block p}

noeq type state (p:Spec.parameters) = {
  hash:hash_w p;
  const_iv: hash_w p;
  const_k: ws_w p;
}


val state_invariant: h:mem -> p:Spec.parameters -> st:state p -> Type0
let state_invariant h p st =
    live h st.hash /\ live h st.const_k /\ live h st.const_iv
  /\ disjoint st.hash st.const_iv /\ disjoint st.const_iv st.hash
  /\ disjoint st.hash st.const_k /\ disjoint st.const_k st.hash
  /\ disjoint st.const_iv st.const_k /\ disjoint st.const_k st.const_iv
  /\ h.[st.const_iv] == p.h0
  /\ h.[st.const_k] == p.kTable


(* Definition of constants *)
inline_for_extraction val create_const_iv: p:Spec.parameters -> StackInline (iv_t p)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1 /\
		                  as_lseq r h1 == p.h0))

inline_for_extraction let create_const_iv p = admit() // createL p.const_iv


(* Definition of constants *)
inline_for_extraction val create_const_k: p:Spec.parameters -> StackInline (ws_w p)
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1 /\
		                  as_lseq r h1 == p.kTable))

inline_for_extraction let create_const_k p = admit() // createL p.kTable


val mkstate: p:Spec.parameters ->
  StackInline (st:state p)
    (requires (fun h -> True))
    (ensures  (fun h0 st h1 -> state_invariant h1 p st))

let mkstate p =
  {
    hash = create (size Spec.size_hash_w) (nat_to_uint #p.wt 0);
    const_iv = create_const_iv p;
    const_k = create_const_k p;
  }


(* Definition of the initialization function for convenience *)
val init:
    p:parameters
  -> st:state p ->
  Stack unit
    (requires (fun h -> state_invariant h p st))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1))

let init p st =
  copy st.hash size_hash_w st.const_iv


val update_block: p:parameters -> st:state p -> block:lbuffer uint8 (Spec.size_block p) ->
  Stack unit
  (requires (fun h -> live h st.hash /\ live h block))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1))

let update_block p st block =
  (**) let h0 = ST.get () in
  alloc #h0 size_block_w (nat_to_uint #p.wt 0) st.hash
  (fun h0 -> (fun _ sv -> True))
  (fun bw ->
    uints_from_bytes_be bw size_block_w block;
    compress p bw st.const_k st.hash
  )


val update_multi_iteration:
    p:Spec.parameters
  -> st:state p
  -> n:size_t{(v n) * Spec.size_block p <= max_size_t}
  -> b:lbuffer uint8 (v n * Spec.size_block p)
  -> i:size_t{v i + 1 <= v n} ->
  Stack unit
    (requires (fun h -> state_invariant h p st
                   /\ live h b /\ disjoint st.hash b /\ disjoint b st.hash))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1))

[@ Substitute ]
let update_multi_iteration p st n b i =
  let block = sub b (i *. (size (Spec.size_block p))) (size (Spec.size_block p)) in
  update_block p st block


val update_multi:
    p: Spec.parameters
  -> st: state p
  -> n_prev: size_t
  -> n: size_t{(v n + v n_prev) * Spec.size_block p <= max_size_t}
  -> b: lbuffer uint8 (size_v n * Spec.size_block p) ->
   Stack unit
     (requires (fun h -> state_invariant h p st
                    /\ live h b /\ disjoint st.hash b /\ disjoint b st.hash))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1))

let update_multi p st n_prev n b =
  (**) let h0 = ST.get () in
  loop #h0 n st.hash
  (fun hi -> (fun i s -> s))
  (fun i -> update_multi_iteration p st n b i)


val update_last:
    vn:size_nat
  -> vlen:size_nat
  -> p:Spec.parameters
  -> st:state p
  -> n:size_t{v n = vn}
  -> last:lbuffer uint8 vlen
  -> len:size_t{v len = vlen} ->
  Stack unit
  (requires (fun h -> live h st.hash /\ live h last))
  (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st.hash h0 h1))

let update_last vn vlen p st n last len =
  (**) let h0 = ST.get () in
  alloc #h0 (size 2 *. (size (Spec.size_block p))) (u8 0) st.hash
  (fun h0 -> (fun _ sv -> True))
  (fun blocks ->
    let nblocks = number_blocks_padding_single p len in
    pad vn vlen p blocks n last len;
    update_multi p st n nblocks blocks
  )


val finish:
    p: Spec.parameters
  -> output: lbuffer uint8 (Spec.size_hash p)
  -> st: state p ->
  Stack unit
    (requires (fun h -> state_invariant h p st
                   /\ live h output /\ disjoint output st.hash /\ disjoint st.hash output))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let finish p output s =
  (**) let h0 = ST.get () in
  alloc #h0 (size (size_hash p)) (u8 0) output
  (fun h -> (fun _ r -> True))
  (fun full ->
    uints_to_bytes_le full (size (size_hash p)) s.hash;
    update_sub output (size 0) (size (size_hash p)) full)


val sha2:
    #vlen: size_nat
  -> p:Spec.parameters
  -> output: lbuffer uint8 (Spec.size_hash p)
  -> input: lbuffer uint8 vlen
  -> len: size_t{v len <= max_input p /\ v len = vlen} ->
  Stack unit
    (requires (fun h -> live h output /\ live h input
                   /\ disjoint output input /\ disjoint input output))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let sha2 #vlen p output input len =
  let rem = len %. (size (Spec.size_block p)) in
  let nblocks = len /. (size (Spec.size_block p)) in
  let blocks = sub #uint8 #vlen #(v nblocks * (Spec.size_block p)) input (size 0) (nblocks *. (size (Spec.size_block p))) in
  let last = sub input (nblocks *. (size (Spec.size_block p))) rem in
  let st = mkstate p in
  init p st;
  update_multi p st (size 0) nblocks input;
  update_last (v nblocks) (v rem) p st len last rem;
  finish p output st
