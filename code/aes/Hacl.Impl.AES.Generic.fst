module Hacl.Impl.AES.Generic

open FStar.HyperStack
open FStar.HyperStack.All
open FStar.Mul
open Lib.IntTypes
open Lib.Buffer
open Lib.LoopCombinators

open Hacl.Impl.AES.Core
open Hacl.AES.Common
open Hacl.AES.Generic.Lemmas
open Hacl.AES.Round.Constant

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 90"


module ST = FStar.HyperStack.ST
module LSeq = Lib.Sequence
module Spec = Spec.AES
module GF = Spec.GaloisField


(* Parameters for AES-128 *)
//noextract inline_for_extraction let nb =  4
//noextract inline_for_extraction let nk =  4 // 4, 6, or 8 for 128/192/256
//noextract inline_for_extraction let nr =  10 // 10, 12, or 14 for 128/192/256

unfold type skey (v:Spec.variant) = lbuffer uint8 (size (normalize_term (Spec.key_size v)))

inline_for_extraction noextract let nr (v:Spec.variant) = size (normalize_term (Spec.num_rounds v))

unfold noextract let ctxlen (m:m_spec) (v:Spec.variant) =  nlen m +. ((nr v +! 1ul) *. klen m)

unfold type keyr (m:m_spec) (v:Spec.variant) = lbuffer (stelem m) ((nr v -! 1ul) *. klen m)
unfold type keyex (m:m_spec) (v:Spec.variant) = lbuffer (stelem m) ((nr v +! 1ul) *. klen m)
unfold type aes_ctx (m:m_spec) (v:Spec.variant) = lbuffer (stelem m) (ctxlen m v)

let rcon_seq : x:LSeq.lseq uint8 11{
  LSeq.index x 0 == u8 0x8d /\ LSeq.index x 1 == u8 0x01 /\
  LSeq.index x 2 == u8 0x02 /\ LSeq.index x 3 == u8 0x04 /\
  LSeq.index x 4 == u8 0x08 /\ LSeq.index x 5 == u8 0x10 /\
  LSeq.index x 6 == u8 0x20 /\ LSeq.index x 7 == u8 0x40 /\
  LSeq.index x 8 == u8 0x80 /\ LSeq.index x 9 == u8 0x1b /\
  LSeq.index x 10 == u8 0x36} =
  let l = [
    u8 0x8d; u8 0x01; u8 0x02; u8 0x04; u8 0x08; u8 0x10;
    u8 0x20; u8 0x40; u8 0x80; u8 0x1b; u8 0x36;
  ] in
  Seq.elim_of_list l;
  assert_norm (List.Tot.length l = 11);
  LSeq.createL l

val rcon_spec_lemma:
   i:size_nat{i < 11} ->
  Lemma (LSeq.index rcon_seq i == Spec.rcon_spec i)

let rcon_spec_lemma i =
  assert_norm (Spec.rcon_spec 0 == u8 0x8d);
  assert_norm (Spec.rcon_spec 1 == u8 0x01);
  assert_norm (Spec.rcon_spec 2 == Spec.two `GF.fmul` Spec.rcon_spec 1);
  assert_norm (Spec.rcon_spec 3 == Spec.two `GF.fmul` Spec.rcon_spec 2);
  assert_norm (Spec.rcon_spec 4 == Spec.two `GF.fmul` Spec.rcon_spec 3);
  assert_norm (Spec.rcon_spec 5 == Spec.two `GF.fmul` Spec.rcon_spec 4);
  assert_norm (Spec.rcon_spec 6 == Spec.two `GF.fmul` Spec.rcon_spec 5);
  assert_norm (Spec.rcon_spec 7 == Spec.two `GF.fmul` Spec.rcon_spec 6);
  assert_norm (Spec.rcon_spec 8 == Spec.two `GF.fmul` Spec.rcon_spec 7);
  assert_norm (Spec.rcon_spec 9 == Spec.two `GF.fmul` Spec.rcon_spec 8);
  assert_norm (Spec.rcon_spec 10 == Spec.two `GF.fmul` Spec.rcon_spec 9);
  fmul_lemma ()

inline_for_extraction noextract
val get_nonce:
    #m: m_spec ->
    #v: Spec.variant ->
    ctx: aes_ctx m v ->
  Stack (lbuffer (stelem m) (nlen m))
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx 0ul (nlen m)))

inline_for_extraction noextract
let get_nonce #m #v ctx = sub ctx (size 0) (nlen m)


inline_for_extraction noextract
val get_kex:
    #m: m_spec ->
    #v: Spec.variant ->
    ctx: aes_ctx m v ->
  Stack (keyex m v)
  (requires (fun h -> live h ctx))
  (ensures (fun h0 x h1 -> h0 == h1 /\ live h1 x /\ x == gsub ctx (nlen m) ((nr v +! 1ul) *. klen m)))

inline_for_extraction noextract
let get_kex #m #v ctx = sub ctx (nlen m) ((nr v +! 1ul) *. klen m)


inline_for_extraction noextract
val create_ctx:
  m: m_spec ->
  v: Spec.variant ->
  StackInline (aes_ctx m v)
  (requires (fun h -> True))
  (ensures (fun h0 f h1 -> live h1 f /\
			stack_allocated f h0 h1 (Seq.create (size_v (ctxlen m v)) (elem_zero m))))

let create_ctx m v = create (ctxlen m v) (elem_zero m)

inline_for_extraction noextract
val add_round_key:
    #m: m_spec
  -> st: state m
  -> key: key1 m ->
   Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1 /\
    (let st' = as_seq h0 st in
    let st'' = as_seq h1 st in
    let k = key_to_bytes m (as_seq h0 key) in
    state_to_bytes m st'' 0 == Spec.addRoundKey k (state_to_bytes m st' 0) /\
    state_to_bytes m st'' 1 == Spec.addRoundKey k (state_to_bytes m st' 1) /\
    state_to_bytes m st'' 2 == Spec.addRoundKey k (state_to_bytes m st' 2) /\
    state_to_bytes m st'' 3 == Spec.addRoundKey k (state_to_bytes m st' 3))))

let add_round_key #m st key = xor_state_key1 #m st key


inline_for_extraction noextract
val enc_round:
    m: m_spec
  -> a: Spec.variant
  -> i:size_t{v i < (Spec.num_rounds a-1)}
  -> s:state m
  -> key: keyr m a
  -> Stack unit
    (requires fun h -> live h s /\ live h key /\ disjoint s key)
    (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\ 
      (let k = key_to_bytes m (LSeq.sub (as_seq h0 key) ((v i) * v (klen m)) (v (klen m))) in
      state_to_bytes m (as_seq h1 s) 0 == Spec.aes_enc k (state_to_bytes m (as_seq h0 s) 0) /\
      state_to_bytes m (as_seq h1 s) 1 == Spec.aes_enc k (state_to_bytes m (as_seq h0 s) 1) /\
      state_to_bytes m (as_seq h1 s) 2 == Spec.aes_enc k (state_to_bytes m (as_seq h0 s) 2) /\
      state_to_bytes m (as_seq h1 s) 3 == Spec.aes_enc k (state_to_bytes m (as_seq h0 s) 3)))
let enc_round m a i s key =
  let h0 = ST.get () in
  let k = sub key (i *. klen m) (klen m) in
  assert (as_seq h0 k == LSeq.sub (as_seq h0 key) ((v i) * v (klen m)) (v (klen m)));
  aes_enc #m s k

inline_for_extraction noextract
val enc_inner:
    m: m_spec
  -> a: Spec.variant
  -> i:size_t{v i < (Spec.num_rounds a-1)}
  -> s:state m
  -> key: keyr m a
  -> Stack unit
    (requires fun h -> live h s /\ live h key /\ disjoint s key)
    (ensures  fun h0 _ h1 -> modifies (loc s) h0 h1 /\
      (let state' = (state_to_bytes m (as_seq h0 s) 0, state_to_bytes m (as_seq h0 s) 1,
        state_to_bytes m (as_seq h0 s) 2, state_to_bytes m (as_seq h0 s) 3) in
      let state'' = (state_to_bytes m (as_seq h1 s) 0, state_to_bytes m (as_seq h1 s) 1,
        state_to_bytes m (as_seq h1 s) 2, state_to_bytes m (as_seq h1 s) 3) in
      state'' == Spec.aes_enc_inner_4 a (keys_to_bytes m a (as_seq h0 key)) (v i) state'))
let enc_inner m a i s key =
  let h0 = ST.get () in
  key_to_bytes_lemma m a (as_seq h0 key) (v i);
  enc_round m a i s key

inline_for_extraction noextract
val enc_rounds128:
    #m: m_spec ->
    s:state m ->
    key: keyr m Spec.AES128 ->
  Stack unit
  (requires (fun h -> live h s /\ live h key /\ disjoint s key))
  (ensures (fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    (let state' = (state_to_bytes m (as_seq h0 s) 0, state_to_bytes m (as_seq h0 s) 1,
      state_to_bytes m (as_seq h0 s) 2, state_to_bytes m (as_seq h0 s) 3) in
    let state'' = (state_to_bytes m (as_seq h1 s) 0, state_to_bytes m (as_seq h1 s) 1,
      state_to_bytes m (as_seq h1 s) 2, state_to_bytes m (as_seq h1 s) 3) in
    state'' == Spec.aes_enc_rounds_4 Spec.AES128 (keys_to_bytes m Spec.AES128 (as_seq h0 key)) state')))

let enc_rounds128 #m s key =
  [@ inline_let]
  let refl h i : GTot (Spec.block & Spec.block & Spec.block & Spec.block) =
    state_to_bytes m (as_seq h s) 0, state_to_bytes m (as_seq h s) 1,
    state_to_bytes m (as_seq h s) 2, state_to_bytes m (as_seq h s) 3 in
  [@ inline_let]
  let footprint i = loc s in
  [@ inline_let]
  let spec h0 = Spec.aes_enc_inner_4 Spec.AES128 (keys_to_bytes m Spec.AES128 (as_seq h0 key)) in
  let h0 = ST.get () in
  loop h0 9ul (Spec.aes_enc_rounds_4_s Spec.AES128) refl footprint spec
  (fun i ->
    unfold_repeat_gen 9 (Spec.aes_enc_rounds_4_s Spec.AES128) (spec h0) (refl h0 0) (v i);
    enc_inner m Spec.AES128 i s key)

inline_for_extraction noextract
val enc_rounds256:
    #m: m_spec ->
    s:state m ->
    key: keyr m Spec.AES256 ->
  Stack unit
  (requires (fun h -> live h s /\ live h key /\ disjoint s key))
  (ensures (fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    (let state' = (state_to_bytes m (as_seq h0 s) 0, state_to_bytes m (as_seq h0 s) 1,
      state_to_bytes m (as_seq h0 s) 2, state_to_bytes m (as_seq h0 s) 3) in
    let state'' = (state_to_bytes m (as_seq h1 s) 0, state_to_bytes m (as_seq h1 s) 1,
      state_to_bytes m (as_seq h1 s) 2, state_to_bytes m (as_seq h1 s) 3) in
    state'' == Spec.aes_enc_rounds_4 Spec.AES256 (keys_to_bytes m Spec.AES256 (as_seq h0 key)) state')))

let enc_rounds256 #m s key =
  [@ inline_let]
  let refl h i : GTot (Spec.block & Spec.block & Spec.block & Spec.block) =
    state_to_bytes m (as_seq h s) 0, state_to_bytes m (as_seq h s) 1,
    state_to_bytes m (as_seq h s) 2, state_to_bytes m (as_seq h s) 3 in
  [@ inline_let]
  let footprint i = loc s in
  [@ inline_let]
  let spec h0 = Spec.aes_enc_inner_4 Spec.AES256 (keys_to_bytes m Spec.AES256 (as_seq h0 key)) in
  let h0 = ST.get () in
  loop h0 13ul (Spec.aes_enc_rounds_4_s Spec.AES256) refl footprint spec
  (fun i ->
    unfold_repeat_gen 13 (Spec.aes_enc_rounds_4_s Spec.AES256) (spec h0) (refl h0 0) (v i);
    enc_inner m Spec.AES256 i s key)

inline_for_extraction noextract
val enc_rounds:
    #m: m_spec ->
    #a: Spec.variant ->
    s:state m ->
    key: keyr m a ->
  Stack unit
  (requires (fun h -> live h s /\ live h key /\ disjoint s key))
  (ensures (fun h0 _ h1 -> modifies (loc s) h0 h1 /\
    (let state' = (state_to_bytes m (as_seq h0 s) 0, state_to_bytes m (as_seq h0 s) 1,
      state_to_bytes m (as_seq h0 s) 2, state_to_bytes m (as_seq h0 s) 3) in
    let state'' = (state_to_bytes m (as_seq h1 s) 0, state_to_bytes m (as_seq h1 s) 1,
      state_to_bytes m (as_seq h1 s) 2, state_to_bytes m (as_seq h1 s) 3) in
    state'' == Spec.aes_enc_rounds_4 a (keys_to_bytes m a (as_seq h0 key)) state')))

let enc_rounds #m #a s key =
  match a with
  | Spec.AES128 -> enc_rounds128 #m s key
  | Spec.AES256 -> enc_rounds256 #m s key


val aes_enc_loop:
  #m: m_spec
  -> #a: Spec.variant
  -> s0:LSeq.lseq uint8 16
  -> s1:LSeq.lseq uint8 16
  -> s2:LSeq.lseq uint8 16
  -> s3:LSeq.lseq uint8 16
  -> key:LSeq.lseq (stelem m) ((Spec.AES.num_rounds a-1) * v (klen m))
  -> n:nat{n <= Spec.num_rounds a-1} ->
  Lemma
   (let (s0',s1',s2',s3') =
      repeat_gen n (Spec.aes_enc_rounds_4_s a)
      (Spec.aes_enc_inner_4 a (keys_to_bytes m a key)) (s0,s1,s2,s3) in
   s0' == repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s0 /\
   s1' == repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s1 /\
   s2' == repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s2 /\
   s3' == repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s3)

let rec aes_enc_loop #m #a s0 s1 s2 s3 key n =
  if n = 0 then begin
    eq_repeat_gen0 n (Spec.aes_enc_rounds_4_s a)
      (Spec.aes_enc_inner_4 a (keys_to_bytes m a key)) (s0,s1,s2,s3);
    eq_repeati0 n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s0;
    eq_repeati0 n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s1;
    eq_repeati0 n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s2;
    eq_repeati0 n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s3;
    () end
  else begin
    aes_enc_loop #m #a s0 s1 s2 s3 key (n - 1);
    unfold_repeat_gen n (Spec.aes_enc_rounds_4_s a)
      (Spec.aes_enc_inner_4 a (keys_to_bytes m a key)) (s0,s1,s2,s3) (n - 1);
    unfold_repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s0 (n - 1);
    unfold_repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s1 (n - 1);
    unfold_repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s2 (n - 1);
    unfold_repeati n (Spec.aes_enc_inner a (keys_to_bytes m a key)) s3 (n - 1);
    () end

val aes_enc_rounds_lemma:
  #m: m_spec
  -> #a: Spec.variant
  -> s:LSeq.lseq (stelem m) (v (stlen m))
  -> key:LSeq.lseq (stelem m) ((Spec.AES.num_rounds a-1) * v (klen m)) ->
  Lemma
   (let s0 = state_to_bytes m s 0 in
   let s1 = state_to_bytes m s 1 in
   let s2 = state_to_bytes m s 2 in
   let s3 = state_to_bytes m s 3 in
   let (s0',s1',s2',s3') = Spec.aes_enc_rounds_4 a (keys_to_bytes m a key) (s0,s1,s2,s3) in
   s0' == Spec.aes_enc_rounds a (keys_to_bytes m a key) s0 /\
   s1' == Spec.aes_enc_rounds a (keys_to_bytes m a key) s1 /\
   s2' == Spec.aes_enc_rounds a (keys_to_bytes m a key) s2 /\
   s3' == Spec.aes_enc_rounds a (keys_to_bytes m a key) s3)

let aes_enc_rounds_lemma #m #a s key =
  let s0 = state_to_bytes m s 0 in
  let s1 = state_to_bytes m s 1 in
  let s2 = state_to_bytes m s 2 in
  let s3 = state_to_bytes m s 3 in
  aes_enc_loop #m #a s0 s1 s2 s3 key (Spec.num_rounds a-1)


inline_for_extraction noextract
val block_cipher:
    #m: m_spec
  -> #a: Spec.variant
  -> st: state m
  -> key: keyex m a
  -> Stack unit
  (requires (fun h -> live h st /\ live h key /\ disjoint st key))
  (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc st) h0 h1 /\
    (let k = keyx_to_bytes m a (as_seq h0 key) in
    state_to_bytes m (as_seq h1 st) 0 ==
      Spec.aes_encrypt_block a k (state_to_bytes m (as_seq h0 st) 0) /\
    state_to_bytes m (as_seq h1 st) 1 ==
      Spec.aes_encrypt_block a k (state_to_bytes m (as_seq h0 st) 1) /\
    state_to_bytes m (as_seq h1 st) 2 ==
      Spec.aes_encrypt_block a k (state_to_bytes m (as_seq h0 st) 2) /\
    state_to_bytes m (as_seq h1 st) 3 ==
      Spec.aes_encrypt_block a k (state_to_bytes m (as_seq h0 st) 3))))

let block_cipher #m #a st key =
  let h0 = ST.get() in
  let klen = klen m in
  assert (v ((nr a -! 1ul) *. klen) == v (nr a -! 1ul) * v klen);
  assert (v (nr a -! 1ul) == v (nr a) - 1);
  assert (v (nr a *. klen) == v (nr a) * v klen);
  assert (v (nr a) == Spec.num_rounds a);
  keyx_to_bytes_lemma m a (as_seq h0 key) 0;
  keys_to_bytes_lemma m a (as_seq h0 key);
  keyx_to_bytes_lemma m a (as_seq h0 key) (Spec.num_rounds a);
  assert (key_to_bytes m (LSeq.sub (as_seq h0 key) 0 (v klen)) ==
    LSeq.sub (keyx_to_bytes m a (as_seq h0 key)) 0 16);
  assert (keys_to_bytes m a (LSeq.sub (as_seq h0 key) (v klen)
    ((Spec.num_rounds a - 1) * v klen)) ==
      LSeq.sub (keyx_to_bytes m a (as_seq h0 key)) 16 ((Spec.num_rounds a-1) * 16));
  assert (key_to_bytes m (LSeq.sub (as_seq h0 key)
    (Spec.num_rounds a * (v klen)) (v klen)) ==
      LSeq.sub (keyx_to_bytes m a (as_seq h0 key)) (Spec.num_rounds a * 16) 16);
  assert (disjoint st (gsub key (size 0) klen));
  let k0 = sub key (size 0) klen in
  let kr = sub key klen ((nr a -! 1ul) *. klen) in
  let kn = sub key (nr a *. klen) klen in
  add_round_key #m st k0;
  let h1 = ST.get() in
  enc_rounds #m #a st kr;
  aes_enc_last #m st kn;
  aes_enc_rounds_lemma #m #a (as_seq h1 st) (as_seq h0 kr)


inline_for_extraction noextract
val key_expansion128_step:
    #m: m_spec
  -> keyx: keyex m Spec.AES128
  -> rcon:uint8
  -> i:size_nat{i < 10} ->
  Stack unit
  (requires (fun h -> live h keyx /\ rcon == LSeq.index rcon_seq (i+1)))
  (ensures (fun h0 _ h1 ->
    (let p = key_to_bytes m (LSeq.sub (as_seq h0 keyx) (v (klen m) * i) (v (klen m))) in
    modifies1 (gsub keyx (size (v (klen m) * (i + 1))) (klen m)) h0 h1 /\
    key_to_bytes m (LSeq.sub (as_seq h1 keyx) (v (klen m) * (i + 1)) (v (klen m))) ==
      Spec.key_expansion_step_LE p (Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p))))

let key_expansion128_step #m keyx rcon i =
  let klen = klen m in
  assert (v (klen *. size i) == v klen * i);
  assert (v (klen *. size (i + 1)) == v klen * (i + 1));
  let prev = sub keyx (klen *. size i) klen in
  let next = sub keyx (klen *. size (i + 1)) klen in
  rcon_spec_lemma (i+1);
  aes_keygen_assist0 #m next prev rcon;
  key_expansion_step #m next prev

val key_expansion128_step_lemma:
   m: m_spec
  -> l0: LSeq.lseq (stelem m) (11 * v (klen m))
  -> l1: LSeq.lseq (stelem m) (11 * v (klen m))
  -> i:size_nat{i < 10} ->
  Lemma 
  (requires (
    let l0_s = LSeq.sub l0 (v (klen m) * i) (v (klen m)) in
    let l1_s = LSeq.sub l1 (v (klen m) * (i + 1)) (v (klen m)) in
    let p = key_to_bytes m l0_s in
    key_to_bytes m l1_s ==
      Spec.key_expansion_step_LE p (Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p)))
  (ensures (
    let keyx_l0 = keyx_to_bytes m Spec.AES128 l0 in
    let keyx_l1 = keyx_to_bytes m Spec.AES128 l1 in
    let p = LSeq.sub keyx_l0 (i * 16) 16 in
    LSeq.sub keyx_l1 ((i+1) * 16) 16 ==
      Spec.key_expansion_step_LE p (Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p)
  ))

let key_expansion128_step_lemma m l0 l1 i =
  keyx_to_bytes_lemma m Spec.AES128 l0 i;
  keyx_to_bytes_lemma m Spec.AES128 l1 (i + 1)

val key_expansion128_step_helper1:
   m: m_spec
  -> keyx: keyex m Spec.AES128
  -> h0: mem
  -> h1: mem
  -> i:size_nat{i < 11} ->
  Lemma 
  (requires (live h0 keyx /\
    modifies1 (gsub keyx (size (v (klen m) * i)) (klen m)) h0 h1))
  (ensures (
    forall (j:nat{(0 <= j /\ j < i) \/ (i < j /\ j < 11)}).
      (LSeq.sub (keyx_to_bytes m Spec.AES128 (as_seq h0 keyx)) (j*16) 16 ==
        LSeq.sub (keyx_to_bytes m Spec.AES128 (as_seq h1 keyx)) (j*16) 16)))

let key_expansion128_step_helper1 m keyx h0 h1 i =
  let l0 = keyx_to_bytes m Spec.AES128 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES128 (as_seq h1 keyx) in
  let aux (j:nat{(0 <= j /\ j < i) \/ (i < j /\ j < 11)}) :
    Lemma (LSeq.sub l0 (j*16) 16 == LSeq.sub l1 (j*16) 16) =
    assert (disjoint (gsub keyx (size (v (klen m) * j)) (klen m)) 
      (gsub keyx (size (v (klen m) * i)) (klen m)));
    keyx_to_bytes_lemma m Spec.AES128 (as_seq h0 keyx) j;
    keyx_to_bytes_lemma m Spec.AES128 (as_seq h1 keyx) j in

  Classical.forall_intro aux

val key_expansion128_step_helper2:
   l0: LSeq.lseq uint8 (11 * 16)
  -> l1: LSeq.lseq uint8 (11 * 16)
  -> i:size_nat{i < 11} ->
  Lemma 
  (requires (
    forall (j:nat{(0 <= j /\ j < i) \/ (i < j /\ j < 11)}).
      (LSeq.sub l0 (j*16) 16 == LSeq.sub l1 (j*16) 16)))
  (ensures (
    LSeq.sub l0 0 (i*16) == LSeq.sub l1 0 (i*16) /\
    LSeq.sub l0 ((i*16) + 16) ((11 * 16) - (i*16) - 16) ==
      LSeq.sub l1 ((i*16) + 16) ((11 * 16) - (i*16) - 16)
  ))

let key_expansion128_step_helper2 l0 l1 i =
  assert (forall (j:nat{(0 <= j /\ j < i) \/ (i + 1 <= j /\ j < 11)}).
    (forall (k:nat{0 <= k /\ k < 16}).
      Seq.index (LSeq.sub l0 (j*16) 16) k == Seq.index (LSeq.sub l1 (j*16) 16) k));
  assert (forall (j:nat{(0 <= j /\ j < i) \/ (i + 1 <= j /\ j < 11)}).
    (forall (k:nat{0 <= k /\ k < 16}).
      Seq.index l0 ((j*16) + k) == Seq.index l1 ((j*16) + k)));
  assert (forall (j:nat{(0 <= j /\ j < i * 16) \/ ((i + 1) * 16 <= j /\ j < 11 * 16)}).
      j == (j / 16) * 16 + j % 16);
  assert (forall (j:nat{(0 <= j /\ j < (i * 16)) \/ ((i + 1) * 16 <= j /\ j < (11 * 16))}).
      LSeq.index l0 j == LSeq.index l1 j);
  LSeq.eq_intro (LSeq.sub l0 0 (i*16)) (LSeq.sub l1 0 (i*16));
  LSeq.eq_intro (LSeq.sub l0 ((i*16) + 16) ((11 * 16) - (i*16) - 16))
    (LSeq.sub l1 ((i*16) + 16) ((11 * 16) - (i*16) - 16))

inline_for_extraction noextract
val aes128_key_expansion_step:
    #m: m_spec
  -> keyx: keyex m Spec.AES128
  -> rcon:uint8
  -> i:size_nat{i < 10} ->
  Stack unit
  (requires (fun h -> live h keyx /\ rcon == LSeq.index rcon_seq (i+1)))
  (ensures (fun h0 _ h1 -> modifies1 (gsub keyx (size (v (klen m) * (i + 1))) (klen m)) h0 h1 /\
    keyx_to_bytes m Spec.AES128 (as_seq h1 keyx) ==
      Spec.aes128_key_expansion_step_LE i (keyx_to_bytes m Spec.AES128 (as_seq h0 keyx))))

[@ CInline ]
let aes128_key_expansion_step #m keyx rcon i =
  let h0 = ST.get() in
  key_expansion128_step #m keyx rcon i;
  let h1 = ST.get() in
  key_expansion128_step_lemma m (as_seq h0 keyx) (as_seq h1 keyx) i;
  let l0 = keyx_to_bytes m Spec.AES128 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES128 (as_seq h1 keyx) in
  key_expansion128_step_helper1 m keyx h0 h1 (i + 1);
  key_expansion128_step_helper2 l0 l1 (i + 1);
  let p0 = LSeq.sub l0 (i * 16) 16 in
  let p = Spec.key_expansion_step_LE p0 (Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p0) in
  LSeq.lemma_update_sub l0 ((i + 1)*16) 16 p l1

val load_key1_lemma:
   m: m_spec
  -> l: LSeq.lseq (stelem m) (11 * v (klen m))
  -> key: LSeq.lseq uint8 16 ->
  Lemma 
  (requires (
    u8_16_to_le (key_to_bytes m (LSeq.sub l 0 (v (klen m)))) == key))
  (ensures (
    LSeq.sub (keyx_to_bytes m Spec.AES128 l) 0 16 == u8_16_to_le key
  ))

let load_key1_lemma m l key =
  u8_16_to_le_lemma (key_to_bytes m (LSeq.sub l 0 (v (klen m))));
  assert (key_to_bytes m (LSeq.sub l 0 (v (klen m))) == u8_16_to_le key);
  keyx_to_bytes_lemma m Spec.AES128 l 0

inline_for_extraction noextract
val aes128_load_key1:
    #m: m_spec
  -> keyx: keyex m Spec.AES128
  -> key: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h keyx /\ live h key))
  (ensures (fun h0 _ h1 -> modifies1 (gsub keyx (size 0) (klen m)) h0 h1 /\
    keyx_to_bytes m Spec.AES128 (as_seq h1 keyx) ==
      LSeq.update_sub (keyx_to_bytes m Spec.AES128 (as_seq h0 keyx)) 0 16 (u8_16_to_le (as_seq h0 key))))

let aes128_load_key1 #m keyx key =
  let h0 = ST.get() in
  assert (v (klen m *. (size 0)) == 0);
  load_key1 (sub keyx (size 0) (klen m)) key;
  let h1 = ST.get() in
  load_key1_lemma m (as_seq h1 keyx) (as_seq h0 key);
  let l0 = keyx_to_bytes m Spec.AES128 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES128 (as_seq h1 keyx) in
  key_expansion128_step_helper1 m keyx h0 h1 0;
  key_expansion128_step_helper2 l0 l1 0;
  LSeq.lemma_update_sub l0 0 16 (u8_16_to_le (as_seq h0 key)) l1

let aes128_key_expansion_unroll (key:LSeq.lseq uint8 16) : Tot (LSeq.lseq uint8 (11 * 16)) =
  let kex = LSeq.create (11 * 16) (u8 0) in
  let kex = LSeq.update_sub kex 0 16 (u8_16_to_le key) in
  let kex = Spec.aes128_key_expansion_step_LE 0 kex in
  let kex = Spec.aes128_key_expansion_step_LE 1 kex in
  let kex = Spec.aes128_key_expansion_step_LE 2 kex in
  let kex = Spec.aes128_key_expansion_step_LE 3 kex in
  let kex = Spec.aes128_key_expansion_step_LE 4 kex in
  let kex = Spec.aes128_key_expansion_step_LE 5 kex in
  let kex = Spec.aes128_key_expansion_step_LE 6 kex in
  let kex = Spec.aes128_key_expansion_step_LE 7 kex in
  let kex = Spec.aes128_key_expansion_step_LE 8 kex in
  let kex = Spec.aes128_key_expansion_step_LE 9 kex in
  kex

val aes128_key_expansion_loop:
  key:LSeq.lseq uint8 16  ->
  Lemma
   (aes128_key_expansion_unroll key == Spec.aes128_key_expansion_LE key)

let aes128_key_expansion_loop key =
  let kex = LSeq.create (11 * 16) (u8 0) in
  let kex = LSeq.update_sub kex 0 16 (u8_16_to_le key) in
  eq_repeati0 10 Spec.aes128_key_expansion_step_LE kex;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 0;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 1;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 2;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 3;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 4;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 5;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 6;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 7;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 8;
  unfold_repeati 10 Spec.aes128_key_expansion_step_LE kex 9

val aes128_modifies1_helper_0:
   m: m_spec
  -> keyx: keyex m Spec.AES128
  -> h0: mem
  -> h1: mem ->
  Lemma 
  (requires (modifies1 (gsub keyx (size 0) (klen m)) h0 h1))
  (ensures (modifies1 keyx h0 h1))

let aes128_modifies1_helper_0 m keyx h0 h1 =
  ()

val aes128_modifies1_helper_i:
   m: m_spec
  -> keyx: keyex m Spec.AES128
  -> h0: mem
  -> h1: mem
  -> i:size_nat{i < 10} ->
  Lemma 
  (requires (modifies1 (gsub keyx (size (v (klen m) * (i + 1))) (klen m)) h0 h1))
  (ensures (modifies1 keyx h0 h1))

let aes128_modifies1_helper_i m keyx h0 h1 i =
  ()

inline_for_extraction noextract
val key_expansion128:
    #m: m_spec
  -> keyx: keyex m Spec.AES128
  -> key: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h keyx /\ live h key /\
    keyx_to_bytes m Spec.AES128 (as_seq h keyx) == LSeq.create (11 * 16) (u8 0)))
  (ensures (fun h0 _ h1 -> modifies1 keyx h0 h1 /\
    keyx_to_bytes m Spec.AES128 (as_seq h1 keyx) ==
      Spec.aes128_key_expansion_LE (as_seq h0 key)))

[@ CInline ]
let key_expansion128 #m keyx key =
  let h0_init = ST.get() in
  aes128_load_key1 keyx key;
  let h1 = ST.get() in
  aes128_modifies1_helper_0 m keyx h0_init h1;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x01) 0;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 0;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x02) 1;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 1;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x04) 2;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 2;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x08) 3;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 3;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x10) 4;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 4;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x20) 5;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 5;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x40) 6;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 6;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x80) 7;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 7;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x1b) 8;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 8;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes128_key_expansion_step keyx (u8 0x36) 9;
  let h1 = ST.get() in
  aes128_modifies1_helper_i m keyx h0 h1 9;
  aes128_key_expansion_loop (as_seq h0_init key)


inline_for_extraction noextract
val key_expansion_assist_step:
    #m: m_spec
  -> next0: key1 m
  -> next1: key1 m
  -> prev0: key1 m
  -> prev1: key1 m
  -> rcon: uint8 ->
  Stack unit
  (requires (fun h -> live h prev0 /\ live h prev1 /\
    live h next0 /\ live h next1 /\ disjoint prev0 prev1 /\
    disjoint prev0 next0 /\ disjoint prev0 next1 /\
    disjoint prev1 next0 /\ disjoint prev1 next1 /\
    disjoint next0 next1))
  (ensures  (fun h0 _ h1 -> modifies2 next0 next1 h0 h1 /\
    (let p0 = key_to_bytes m (as_seq h0 prev0) in
    let p1 = key_to_bytes m (as_seq h0 prev1) in
    let a0 = Spec.keygen_assist0 rcon p1 in
    let n0 = Spec.key_expansion_step_LE p0 a0 in
    let a1 = Spec.keygen_assist1 n0 in
    let n1 = Spec.key_expansion_step_LE p1 a1 in
    key_to_bytes m (as_seq h1 next0) == n0 /\
    key_to_bytes m (as_seq h1 next1) == n1)))

let key_expansion_assist_step #m next0 next1 prev0 prev1 rcon =
  aes_keygen_assist0 #m next0 prev1 rcon;
  key_expansion_step #m next0 prev0;
  aes_keygen_assist1 #m next1 next0;
  key_expansion_step #m next1 prev1

noextract
let ksub_256 (m:m_spec) (keyx:LSeq.lseq (stelem m) (15 * v (klen m)))
  (i:size_nat{i < 6}) (j:size_nat{j < 4}) : LSeq.lseq uint8 16 =
  key_to_bytes m (LSeq.sub keyx (v (klen m) * ((2 * i) + j)) (v (klen m)))

inline_for_extraction noextract
val key_expansion256_step:
    #m: m_spec
  -> keyx: keyex m Spec.AES256
  -> rcon: uint8
  -> i:size_nat{i < 6} ->
  Stack unit
  (requires (fun h -> live h keyx /\ rcon == LSeq.index rcon_seq (i+1)))
  (ensures (fun h0 _ h1 ->
    (let next0 = gsub keyx (size (v (klen m) * ((2 * i) + 2))) (klen m) in
    let next1 = gsub keyx (size (v (klen m) * ((2 * i) + 3))) (klen m) in
    let p0 = ksub_256 m (as_seq h0 keyx) i 0 in
    let p1 = ksub_256 m (as_seq h0 keyx) i 1 in
    let a0 = Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p1 in
    let n0 = Spec.key_expansion_step_LE p0 a0 in
    let a1 = Spec.keygen_assist1 n0 in
    let n1 = Spec.key_expansion_step_LE p1 a1 in
    modifies2 next0 next1 h0 h1 /\
    ksub_256 m (as_seq h1 keyx) i 2 == n0 /\
    ksub_256 m (as_seq h1 keyx) i 3 == n1)))

let key_expansion256_step #m keyx rcon i =
  let h0 = ST.get() in
  let klen = klen m in
  assert (v (klen *. size (2* i)) == v klen * (2* i));
  assert (v (klen *. size ((2* i) + 1)) == v klen * (2* i + 1));
  assert (v (klen *. size ((2* i) + 2)) == v klen * (2* i + 2));
  assert (v (klen *. size ((2* i) + 3)) == v klen * (2* i + 3));
  let prev0 = sub keyx (klen *. size (2* i)) klen in
  let prev1 = sub keyx (klen *. size ((2* i) + 1)) klen in
  let next0 = sub keyx (klen *. size ((2* i) + 2)) klen in
  let next1 = sub keyx (klen *. size ((2* i) + 3)) klen in
  assert (key_to_bytes m (as_seq h0 prev0) == ksub_256 m (as_seq h0 keyx) i 0);
  assert (key_to_bytes m (as_seq h0 prev1) == ksub_256 m (as_seq h0 keyx) i 1);
  rcon_spec_lemma (i+1);
  key_expansion_assist_step next0 next1 prev0 prev1 rcon;
  let h1 = ST.get() in
  assert (key_to_bytes m (as_seq h1 next0) == ksub_256 m (as_seq h1 keyx) i 2);
  assert (key_to_bytes m (as_seq h1 next1) == ksub_256 m (as_seq h1 keyx) i 3)

val key_expansion256_step_lemma:
   m: m_spec
  -> l0: LSeq.lseq (stelem m) (15 * v (klen m))
  -> l1: LSeq.lseq (stelem m) (15 * v (klen m))
  -> i:size_nat{i < 6} ->
  Lemma 
  (requires (
    let p0 = ksub_256 m l0 i 0 in
    let p1 = ksub_256 m l0 i 1 in
    let a0 = Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p1 in
    let n0 = Spec.key_expansion_step_LE p0 a0 in
    let a1 = Spec.keygen_assist1 n0 in
    let n1 = Spec.key_expansion_step_LE p1 a1 in
    ksub_256 m l1 i 2 == n0 /\ ksub_256 m l1 i 3 == n1))
  (ensures (
    let k0 = keyx_to_bytes m Spec.AES256 l0 in
    let k1 = keyx_to_bytes m Spec.AES256 l1 in
    let p0 = LSeq.sub k0 (2 * i * 16) 16 in
    let p1 = LSeq.sub k0 ((2 * i + 1) * 16) 16 in
    let a0 = Spec.keygen_assist0 (Spec.rcon_spec (i+1)) p1 in
    let n0 = Spec.key_expansion_step_LE p0 a0 in
    let a1 = Spec.keygen_assist1 n0 in
    let n1 = Spec.key_expansion_step_LE p1 a1 in
    LSeq.sub k1 ((2 * i + 2) * 16) 16 == n0 /\
    LSeq.sub k1 ((2 * i + 3) * 16) 16 == n1))

let key_expansion256_step_lemma m l0 l1 i =
  keyx_to_bytes_lemma m Spec.AES256 l0 (2 * i);
  keyx_to_bytes_lemma m Spec.AES256 l0 (2 * i + 1);
  keyx_to_bytes_lemma m Spec.AES256 l1 (2 * i + 2);
  keyx_to_bytes_lemma m Spec.AES256 l1 (2 * i + 3)

val key_expansion256_step_helper1:
   m: m_spec
  -> keyx: keyex m Spec.AES256
  -> h0: mem
  -> h1: mem
  -> i:size_nat{i < 13} ->
  Lemma 
  (requires (live h0 keyx /\
    (let next0 = gsub keyx (size (v (klen m) * i)) (klen m) in
    let next1 = gsub keyx (size (v (klen m) * (i + 1))) (klen m) in
    modifies2 next0 next1 h0 h1)))
  (ensures (
    forall (j:nat{(0 <= j /\ j < i) \/ (i + 1 < j /\ j < 15)}).
      (LSeq.sub (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)) (j*16) 16 ==
        LSeq.sub (keyx_to_bytes m Spec.AES256 (as_seq h1 keyx)) (j*16) 16)))

let key_expansion256_step_helper1 m keyx h0 h1 i =
  let l0 = keyx_to_bytes m Spec.AES256 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) in
  let aux (j:nat{(0 <= j /\ j < i) \/ (i + 1 < j /\ j < 15)}) :
    Lemma (LSeq.sub l0 (j*16) 16 == LSeq.sub l1 (j*16) 16) =
    assert (disjoint (gsub keyx (size (v (klen m) * j)) (klen m)) 
      (gsub keyx (size (v (klen m) * i)) (klen m)));
    assert (disjoint (gsub keyx (size (v (klen m) * j)) (klen m)) 
      (gsub keyx (size (v (klen m) * (i + 1))) (klen m)));
    keyx_to_bytes_lemma m Spec.AES256 (as_seq h0 keyx) j;
    keyx_to_bytes_lemma m Spec.AES256 (as_seq h1 keyx) j in

  Classical.forall_intro aux

val key_expansion256_step_helper2:
   l0: LSeq.lseq uint8 (15 * 16)
  -> l1: LSeq.lseq uint8 (15 * 16)
  -> i:size_nat{i < 13} ->
  Lemma 
  (requires (
    forall (j:nat{(0 <= j /\ j < i) \/ (i + 1 < j /\ j < 15)}).
      (LSeq.sub l0 (j*16) 16 == LSeq.sub l1 (j*16) 16)))
  (ensures (
    LSeq.sub l0 0 (i*16) == LSeq.sub l1 0 (i*16) /\
    LSeq.sub l0 ((i*16) + 32) ((15 * 16) - (i*16) - 32) ==
      LSeq.sub l1 ((i*16) + 32) ((15 * 16) - (i*16) - 32)
  ))

let key_expansion256_step_helper2 l0 l1 i =
  assert (forall (j:nat{(0 <= j /\ j < i) \/ (i + 2 <= j /\ j < 15)}).
    (forall (k:nat{0 <= k /\ k < 16}).
      Seq.index (LSeq.sub l0 (j*16) 16) k == Seq.index (LSeq.sub l1 (j*16) 16) k));
  assert (forall (j:nat{(0 <= j /\ j < i) \/ (i + 2 <= j /\ j < 15)}).
    (forall (k:nat{0 <= k /\ k < 16}).
      Seq.index l0 ((j*16) + k) == Seq.index l1 ((j*16) + k)));
  assert (forall (j:nat{(0 <= j /\ j < i * 16) \/ ((i + 2) * 16 <= j /\ j < 15 * 16)}).
      j == (j / 16) * 16 + j % 16);
  assert (forall (j:nat{(0 <= j /\ j < (i * 16)) \/ ((i + 2) * 16 <= j /\ j < (15 * 16))}).
      LSeq.index l0 j == LSeq.index l1 j);
  LSeq.eq_intro (LSeq.sub l0 0 (i*16)) (LSeq.sub l1 0 (i*16));
  LSeq.eq_intro (LSeq.sub l0 ((i*16) + 32) ((15 * 16) - (i*16) - 32))
    (LSeq.sub l1 ((i*16) + 32) ((15 * 16) - (i*16) - 32))

val key_expansion256_step_helper3:
   l0: LSeq.lseq uint8 (15 * 16)
  -> l1: LSeq.lseq uint8 (15 * 16)
  -> i:size_nat{i < 13} ->
  Lemma (let l1_n = LSeq.sub l1 (i*16) 32 in
    LSeq.sub l1_n 0 16 == LSeq.sub l1 (i*16) 16 /\
    LSeq.sub l1_n 16 16 == LSeq.sub l1 ((i+1)*16) 16 /\
    LSeq.update_sub l0 (i*16) 32 l1_n ==
      LSeq.update_sub (LSeq.update_sub l0 (i*16) 16 
      (LSeq.sub l1 (i*16) 16)) ((i+1)*16) 16 (LSeq.sub l1 ((i+1)*16) 16))

let key_expansion256_step_helper3 l0 l1 i =
  let n0 = LSeq.sub l1 (i*16) 16 in
  let n1 = LSeq.sub l1 ((i+1)*16) 16 in
  let l1_n = LSeq.sub l1 (i*16) 32 in
  assert (LSeq.sub l1_n 0 16 == n0);
  assert (LSeq.sub l1_n 16 16 == n1);
  let upd_n = LSeq.update_sub l0 (i*16) 32 l1_n in
  let upd_n0 = LSeq.update_sub l0 (i*16) 16 n0 in
  let upd_n1 = LSeq.update_sub upd_n0 ((i+1)*16) 16 n1 in
  //lemma_update_sub requirement 1
  LSeq.eq_intro (LSeq.sub upd_n1 0 (i*16)) (LSeq.sub l0 0 (i*16));
  assert (LSeq.sub upd_n1 0 (i*16) == LSeq.sub l0 0 (i*16));
  //lemma_update_sub requirement 2
  LSeq.eq_intro (LSeq.sub upd_n1 (i*16) 16) n0;
  assert (LSeq.sub upd_n1 (i*16) 16 == n0);
  assert (LSeq.sub upd_n1 ((i+1)*16) 16 == n1);
  LSeq.lemma_concat2 16 n0 16 n1 l1_n;
  LSeq.eq_intro (LSeq.sub upd_n1 (i*16) 32) l1_n;
  assert (LSeq.sub upd_n1 (i*16) 32 == l1_n);
  //lemma_update_sub requirement 3
  LSeq.eq_intro (LSeq.sub upd_n1 ((i*16) + 32) ((15 * 16) - (i*16) - 32))
    (LSeq.sub l0 ((i*16) + 32) ((15 * 16) - (i*16) - 32));
  assert (LSeq.sub upd_n1 ((i*16) + 32) ((15 * 16) - (i*16) - 32) ==
    LSeq.sub l0 ((i*16) + 32) ((15 * 16) - (i*16) - 32));
  LSeq.lemma_update_sub l0 (i*16) 32 l1_n upd_n1

inline_for_extraction noextract
val aes256_key_expansion_step:
    #m: m_spec
  -> keyx: keyex m Spec.AES256
  -> rcon: uint8
  -> i:size_nat{i < 6} ->
  Stack unit
  (requires (fun h -> live h keyx /\ rcon == LSeq.index rcon_seq (i+1)))
  (ensures (fun h0 _ h1 -> (
    let next0 = gsub keyx (size (v (klen m) * (2 * i + 2))) (klen m) in
    let next1 = gsub keyx (size (v (klen m) * (2 * i + 3))) (klen m) in
    modifies2 next0 next1 h0 h1 /\
    keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) ==
      Spec.aes256_key_expansion_step_LE i (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)))))

[@ CInline ]
let aes256_key_expansion_step #m keyx rcon i =
  let h0 = ST.get() in
  key_expansion256_step #m keyx rcon i;
  let h1 = ST.get() in
  key_expansion256_step_lemma m (as_seq h0 keyx) (as_seq h1 keyx) i;
  let l0 = keyx_to_bytes m Spec.AES256 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) in
  key_expansion256_step_helper1 m keyx h0 h1 (2 * i + 2);
  key_expansion256_step_helper2 l0 l1 (2 * i + 2);
  key_expansion256_step_helper3 l0 l1 (2 * i + 2);
  LSeq.lemma_update_sub l0 ((2 * i + 2)*16) 32
    (LSeq.sub l1 ((2 * i + 2)*16) 32) l1

noextract
let ksub_256_last (m:m_spec) (keyx:LSeq.lseq (stelem m) (15 * v (klen m)))
  (i:size_nat{i >= 12 /\ i < 15}) : LSeq.lseq uint8 16 =
  key_to_bytes m (LSeq.sub keyx (v (klen m) * i) (v (klen m)))

inline_for_extraction noextract
val key_expansion256_step_last:
    #m: m_spec
  -> keyx: keyex m Spec.AES256 ->
  Stack unit
  (requires (fun h -> live h keyx))
  (ensures (fun h0 _ h1 ->
    (let p0 = ksub_256_last m (as_seq h0 keyx) 12 in
    let p1 = ksub_256_last m (as_seq h0 keyx) 13 in
    let a14 = Spec.keygen_assist0 (Spec.rcon_spec 7) p1 in
    let n14 = Spec.key_expansion_step_LE p0 a14 in
    modifies1 (gsub keyx (size (v (klen m) * 14)) (klen m)) h0 h1 /\
    ksub_256_last m (as_seq h1 keyx) 14 == n14)))

let key_expansion256_step_last #m keyx =
  let klen = klen m in
  assert (v (klen *. size 12) == v klen * 12);
  assert (v (klen *. size 13) == v klen * 13);
  assert (v (klen *. size 14) == v klen * 14);
  let prev0 = sub keyx (klen *. size 12) klen in
  let prev1 = sub keyx (klen *. size 13) klen in
  let next0 = sub keyx (klen *. size 14) klen in
  rcon_spec_lemma 7;
  aes_keygen_assist0 #m next0 prev1 (u8 0x40);
  key_expansion_step #m next0 prev0

val key_expansion256_step_last_helper1:
   m: m_spec
  -> keyx: keyex m Spec.AES256
  -> h0: mem
  -> h1: mem ->
  Lemma 
  (requires (live h0 keyx /\
    modifies1 (gsub keyx (size (v (klen m) * 14)) (klen m)) h0 h1))
  (ensures (
    forall (j:nat{0 <= j /\ j < 14}).
      (LSeq.sub (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)) (j*16) 16 ==
        LSeq.sub (keyx_to_bytes m Spec.AES256 (as_seq h1 keyx)) (j*16) 16)))

let key_expansion256_step_last_helper1 m keyx h0 h1 =
  let l0 = keyx_to_bytes m Spec.AES256 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) in
  let aux (j:nat{0 <= j /\ j < 14}) :
    Lemma (LSeq.sub l0 (j*16) 16 == LSeq.sub l1 (j*16) 16) =
    assert (disjoint (gsub keyx (size (v (klen m) * j)) (klen m)) 
      (gsub keyx (size (v (klen m) * 14)) (klen m)));
    keyx_to_bytes_lemma m Spec.AES256 (as_seq h0 keyx) j;
    keyx_to_bytes_lemma m Spec.AES256 (as_seq h1 keyx) j in

  Classical.forall_intro aux

val key_expansion256_step_last_helper2:
   l0: LSeq.lseq uint8 (15 * 16)
  -> l1: LSeq.lseq uint8 (15 * 16) ->
  Lemma 
  (requires (
    forall (j:nat{0 <= j /\ j < 14}).
      (LSeq.sub l0 (j*16) 16 == LSeq.sub l1 (j*16) 16)))
  (ensures (
    LSeq.sub l0 0 (14*16) == LSeq.sub l1 0 (14*16) /\
    LSeq.sub l0 ((14*16) + 16) ((15 * 16) - (14*16) - 16) ==
      LSeq.sub l1 ((14*16) + 16) ((15 * 16) - (14*16) - 16)
  ))

let key_expansion256_step_last_helper2 l0 l1 =
  assert (forall (j:nat{0 <= j /\ j < 14}).
    (forall (k:nat{0 <= k /\ k < 16}).
      Seq.index (LSeq.sub l0 (j*16) 16) k == Seq.index (LSeq.sub l1 (j*16) 16) k));
  assert (forall (j:nat{0 <= j /\ j < 14}).
    (forall (k:nat{0 <= k /\ k < 16}).
      Seq.index l0 ((j*16) + k) == Seq.index l1 ((j*16) + k)));
  assert (forall (j:nat{0 <= j /\ j < 14 * 16}).
      j == (j / 16) * 16 + j % 16);
  assert (forall (j:nat{0 <= j /\ j < 14 * 16}).
      LSeq.index l0 j == LSeq.index l1 j);
  LSeq.eq_intro (LSeq.sub l0 0 (14*16)) (LSeq.sub l1 0 (14*16));
  LSeq.eq_intro (LSeq.sub l0 ((14*16) + 16) ((15 * 16) - (14*16) - 16))
    (LSeq.sub l1 ((14*16) + 16) ((15 * 16) - (14*16) - 16))

val key_expansion256_step_last_lemma:
   m: m_spec
  -> l0: LSeq.lseq (stelem m) (15 * v (klen m))
  -> l1: LSeq.lseq (stelem m) (15 * v (klen m)) ->
  Lemma 
  (requires (
    let p0 = ksub_256_last m l0 12 in
    let p1 = ksub_256_last m l0 13 in
    let a14 = Spec.keygen_assist0 (Spec.rcon_spec 7) p1 in
    let n14 = Spec.key_expansion_step_LE p0 a14 in
    ksub_256_last m l1 14 == n14))
  (ensures (
    let k0 = keyx_to_bytes m Spec.AES256 l0 in
    let k1 = keyx_to_bytes m Spec.AES256 l1 in
    let p0 = LSeq.sub k0 (12*16) 16 in
    let p1 = LSeq.sub k0 (13*16) 16 in
    let a14 = Spec.keygen_assist0 (Spec.rcon_spec 7) p1 in
    let n14 = Spec.key_expansion_step_LE p0 a14 in
    LSeq.sub k1 (14*16) 16 == n14
  ))

let key_expansion256_step_last_lemma m l0 l1 =
  keyx_to_bytes_lemma m Spec.AES256 l0 12;
  keyx_to_bytes_lemma m Spec.AES256 l0 13;
  keyx_to_bytes_lemma m Spec.AES256 l1 14

inline_for_extraction noextract
val aes256_key_expansion_step_last:
    #m: m_spec
  -> keyx: keyex m Spec.AES256 ->
  Stack unit
  (requires (fun h -> live h keyx))
  (ensures (fun h0 _ h1 -> (
    let p0 = LSeq.sub (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)) (12*16) 16 in
    let p1 = LSeq.sub (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)) (13*16) 16 in
    let a14 = Spec.keygen_assist0 (Spec.rcon_spec 7) p1 in
    let n14 = Spec.key_expansion_step_LE p0 a14 in
    modifies1 (gsub keyx (size (v (klen m) * 14)) (klen m)) h0 h1 /\
    keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) ==
      LSeq.update_sub (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)) (14*16) 16 n14)))

let aes256_key_expansion_step_last #m keyx =
  let h0 = ST.get() in
  key_expansion256_step_last #m keyx;
  let h1 = ST.get() in
  key_expansion256_step_last_lemma m (as_seq h0 keyx) (as_seq h1 keyx);
  let l0 = keyx_to_bytes m Spec.AES256 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) in
  key_expansion256_step_last_helper1 m keyx h0 h1;
  key_expansion256_step_last_helper2 l0 l1;
  let p0 = LSeq.sub l0 (12*16) 16 in
  let p1 = LSeq.sub l0 (13*16) 16 in
  let a14 = Spec.keygen_assist0 (Spec.rcon_spec 7) p1 in
  let n14 = Spec.key_expansion_step_LE p0 a14 in
  LSeq.lemma_update_sub l0 (14*16) 16 n14 l1

val load_key1_2_lemma:
   m: m_spec
  -> l: LSeq.lseq (stelem m) (15 * v (klen m))
  -> key: LSeq.lseq uint8 32 ->
  Lemma 
  (requires (
    u8_16_to_le (key_to_bytes m (LSeq.sub l 0 (v (klen m)))) == LSeq.sub key 0 16 /\
    u8_16_to_le (key_to_bytes m (LSeq.sub l (v (klen m)) (v (klen m)))) == LSeq.sub key 16 16))
  (ensures (
    LSeq.sub (keyx_to_bytes m Spec.AES256 l) 0 16 == u8_16_to_le (LSeq.sub key 0 16) /\
    LSeq.sub (keyx_to_bytes m Spec.AES256 l) 16 16 == u8_16_to_le (LSeq.sub key 16 16)
  ))

let load_key1_2_lemma m l key =
  u8_16_to_le_lemma (key_to_bytes m (LSeq.sub l 0 (v (klen m))));
  u8_16_to_le_lemma (key_to_bytes m (LSeq.sub l (v (klen m)) (v (klen m))));
  keyx_to_bytes_lemma m Spec.AES256 l 0;
  keyx_to_bytes_lemma m Spec.AES256 l 1

val key_u8_16_2_to_le_lemma:
   l: LSeq.lseq uint8 (15 * 16)
  -> key: LSeq.lseq uint8 32 ->
  Lemma
  (requires (
    LSeq.sub l 0 16 == u8_16_to_le (LSeq.sub key 0 16) /\
    LSeq.sub l 16 16 == u8_16_to_le (LSeq.sub key 16 16)))
  (ensures (
    LSeq.sub l 0 32 == u8_16_2_to_le key
  ))

let key_u8_16_2_to_le_lemma l key =
  LSeq.eq_intro (LSeq.sub l 0 32) (u8_16_2_to_le key)

inline_for_extraction noextract
val aes256_load_key1:
    #m: m_spec
  -> keyx: keyex m Spec.AES256
  -> key: lbuffer uint8 32ul ->
  Stack unit
  (requires (fun h -> live h keyx /\ live h key /\ disjoint keyx key))
  (ensures (fun h0 _ h1 -> 
    let next0 = gsub keyx (size 0) (klen m) in
    let next1 = gsub keyx (klen m) (klen m) in
    modifies2 next0 next1 h0 h1 /\
    keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) ==
      LSeq.update_sub (keyx_to_bytes m Spec.AES256 (as_seq h0 keyx)) 0 32 (u8_16_2_to_le (as_seq h0 key))))

let aes256_load_key1 #m keyx key =
  let h0 = ST.get() in
  let klen = klen m in
  let next0 = sub keyx (size 0) klen in
  let next1 = sub keyx klen klen in
  load_key1 next0 (sub key (size 0) (size 16));
  load_key1 next1 (sub key (size 16) (size 16));
  let h1 = ST.get() in
  load_key1_2_lemma m (as_seq h1 keyx) (as_seq h0 key);
  let l0 = keyx_to_bytes m Spec.AES256 (as_seq h0 keyx) in
  let l1 = keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) in
  key_expansion256_step_helper1 m keyx h0 h1 0;
  key_expansion256_step_helper2 l0 l1 0;
  key_u8_16_2_to_le_lemma l1 (as_seq h0 key);
  LSeq.lemma_update_sub l0 0 32 (u8_16_2_to_le (as_seq h0 key)) l1

let aes256_key_expansion_unroll (key:LSeq.lseq uint8 32) : Tot (LSeq.lseq uint8 (15 * 16)) =
  let kex = LSeq.create (15 * 16) (u8 0) in
  let kex = LSeq.update_sub kex 0 32 (u8_16_2_to_le key) in
  let kex = Spec.aes256_key_expansion_step_LE 0 kex in
  let kex = Spec.aes256_key_expansion_step_LE 1 kex in
  let kex = Spec.aes256_key_expansion_step_LE 2 kex in
  let kex = Spec.aes256_key_expansion_step_LE 3 kex in
  let kex = Spec.aes256_key_expansion_step_LE 4 kex in
  let kex = Spec.aes256_key_expansion_step_LE 5 kex in
  let p0 = LSeq.sub kex (12 * 16) 16 in
  let p1 = LSeq.sub kex (13 * 16) 16 in
  let a14 = Spec.keygen_assist0 (Spec.rcon_spec 7) p1 in
  let n14 = Spec.key_expansion_step_LE p0 a14 in
  let kex = LSeq.update_sub kex (14 * 16) 16 n14 in
  kex

val aes256_key_expansion_loop:
  key:LSeq.lseq uint8 32  ->
  Lemma
   (aes256_key_expansion_unroll key == Spec.aes256_key_expansion_LE key)

let aes256_key_expansion_loop key =
  let kex = LSeq.create (15 * 16) (u8 0) in
  let kex = LSeq.update_sub kex 0 32 (u8_16_2_to_le key) in
  eq_repeati0 6 Spec.aes256_key_expansion_step_LE kex;
  unfold_repeati 6 Spec.aes256_key_expansion_step_LE kex 0;
  unfold_repeati 6 Spec.aes256_key_expansion_step_LE kex 1;
  unfold_repeati 6 Spec.aes256_key_expansion_step_LE kex 2;
  unfold_repeati 6 Spec.aes256_key_expansion_step_LE kex 3;
  unfold_repeati 6 Spec.aes256_key_expansion_step_LE kex 4;
  unfold_repeati 6 Spec.aes256_key_expansion_step_LE kex 5

val aes256_modifies1_helper_0:
   m: m_spec
  -> keyx: keyex m Spec.AES256
  -> h0: mem
  -> h1: mem ->
  Lemma 
  (requires (
    let next0 = gsub keyx (size 0) (klen m) in
    let next1 = gsub keyx (klen m) (klen m) in
    modifies2 next0 next1 h0 h1))
  (ensures (modifies1 keyx h0 h1))

let aes256_modifies1_helper_0 m keyx h0 h1 =
  ()

val aes256_modifies1_helper_i:
   m: m_spec
  -> keyx: keyex m Spec.AES256
  -> h0: mem
  -> h1: mem
  -> i:size_nat{i < 6} ->
  Lemma 
  (requires (
    let next0 = gsub keyx (size (v (klen m) * (2 * i + 2))) (klen m) in
    let next1 = gsub keyx (size (v (klen m) * (2 * i + 3))) (klen m) in
    modifies2 next0 next1 h0 h1))
  (ensures (modifies1 keyx h0 h1))

let aes256_modifies1_helper_i m keyx h0 h1 i =
  ()

val aes256_modifies1_helper_last:
   m: m_spec
  -> keyx: keyex m Spec.AES256
  -> h0: mem
  -> h1: mem ->
  Lemma 
  (requires (modifies1 (gsub keyx (size (v (klen m) * 14)) (klen m)) h0 h1))
  (ensures (modifies1 keyx h0 h1))

let aes256_modifies1_helper_last m keyx h0 h1 =
  ()

inline_for_extraction noextract
val key_expansion256:
    #m: m_spec
  -> keyx: keyex m Spec.AES256
  -> key: lbuffer uint8 32ul ->
  Stack unit
  (requires (fun h -> live h keyx /\ live h key /\ disjoint keyx key /\
    keyx_to_bytes m Spec.AES256 (as_seq h keyx) == LSeq.create (15 * 16) (u8 0)))
  (ensures (fun h0 _ h1 -> modifies1 keyx h0 h1 /\
    keyx_to_bytes m Spec.AES256 (as_seq h1 keyx) ==
      Spec.aes256_key_expansion_LE (as_seq h0 key)))

[@ CInline ]
let key_expansion256 #m keyx key =
  let h0_init = ST.get() in  
  aes256_load_key1 #m keyx key;
  let h1 = ST.get() in
  aes256_modifies1_helper_0 m keyx h0_init h1;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step #m keyx (u8 0x01) 0;
  let h1 = ST.get() in
  aes256_modifies1_helper_i m keyx h0 h1 0;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step #m keyx (u8 0x02) 1;
  let h1 = ST.get() in
  aes256_modifies1_helper_i m keyx h0 h1 1;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step #m keyx (u8 0x04) 2;
  let h1 = ST.get() in
  aes256_modifies1_helper_i m keyx h0 h1 2;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step #m keyx (u8 0x08) 3;
  let h1 = ST.get() in
  aes256_modifies1_helper_i m keyx h0 h1 3;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step #m keyx (u8 0x10) 4;
  let h1 = ST.get() in
  aes256_modifies1_helper_i m keyx h0 h1 4;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step #m keyx (u8 0x20) 5;
  let h1 = ST.get() in
  aes256_modifies1_helper_i m keyx h0 h1 5;
  assert (modifies1 keyx h0_init h1);
  let h0 = ST.get() in
  aes256_key_expansion_step_last #m keyx;
  let h1 = ST.get() in
  aes256_modifies1_helper_last m keyx h0 h1;
  aes256_key_expansion_loop (as_seq h0_init key)


inline_for_extraction noextract
val key_expansion:
    #m: m_spec
  -> #v: Spec.variant
  -> keyx: keyex m v
  -> key: skey v ->
  Stack unit
  (requires (fun h -> live h keyx /\ live h key /\ disjoint keyx key /\
    keyx_to_bytes m v (as_seq h keyx) == LSeq.create ((Spec.num_rounds v+1) * 16) (u8 0)))
  (ensures (fun h0 _ h1 -> modifies (loc keyx) h0 h1 /\
    keyx_to_bytes m v (as_seq h1 keyx) ==
      Spec.aes_key_expansion_LE v (as_seq h0 key)))

let key_expansion #m #v keyx key =
  match v with
  | Spec.AES128 -> key_expansion128 #m keyx key
  | Spec.AES256 -> key_expansion256 #m keyx key

inline_for_extraction noextract
val aes_init_:
    #m: m_spec
  -> #a: Spec.variant
  -> ctx: aes_ctx m a
  -> key: skey a
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\
    disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen m a)) (elem_zero m)))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen m)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen m)) ((Spec.num_rounds a+1) * v (klen m)) in
    let state = Spec.aes_ctr32_init_LE a (as_seq h0 key)
      (as_seq h0 nonce) in
    nonce_to_bytes m n == state.block /\
    keyx_to_bytes m a kex == state.key_ex)))

let aes_init_ #m #a ctx key nonce =
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  let h0 = ST.get() in
  assert (v ((nr a +! 1ul) *. klen m) == v (nr a +! 1ul) * v (klen m));
  assert (v (nr a +! 1ul) == v (nr a) + 1);
  assert (v (nr a) == Spec.num_rounds a);
  LSeq.eq_intro (as_seq h0 kex)
    (Seq.create ((Spec.num_rounds a+1) * v (klen m)) (elem_zero m));
  keyx_zero_lemma m a (as_seq h0 kex);
  load_nonce #m n nonce;
  let h1 = ST.get() in
  u8_16_to_le_lemma (nonce_to_bytes m (as_seq h1 n));
  key_expansion #m #a kex key

(* BEGIN STANDARD PATTERN FOR AVOIDING INLINING *)
inline_for_extraction noextract
val aes128_bitslice_init:
    ctx: aes_ctx M32 Spec.AES128
  -> key: skey Spec.AES128
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen M32 Spec.AES128)) (elem_zero M32)))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen M32)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen M32)) ((Spec.num_rounds Spec.AES128+1) * v (klen M32)) in
    let state = Spec.aes_ctr32_init_LE Spec.AES128
      (as_seq h0 key) (as_seq h0 nonce) in
    nonce_to_bytes M32 n == state.block /\
    keyx_to_bytes M32 Spec.AES128 kex == state.key_ex)))

let aes128_bitslice_init ctx key nonce = aes_init_ #M32 #Spec.AES128 ctx key nonce

inline_for_extraction noextract
val aes128_ni_init:
    ctx: aes_ctx MAES Spec.AES128
  -> key: skey Spec.AES128
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen MAES Spec.AES128)) (elem_zero MAES)))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen MAES)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen MAES)) ((Spec.num_rounds Spec.AES128+1) * v (klen MAES)) in
    let state = Spec.aes_ctr32_init_LE Spec.AES128
      (as_seq h0 key) (as_seq h0 nonce) in
    nonce_to_bytes MAES n == state.block /\
    keyx_to_bytes MAES Spec.AES128 kex == state.key_ex)))

let aes128_ni_init ctx key nonce = aes_init_ #MAES #Spec.AES128 ctx key nonce

inline_for_extraction noextract
val aes256_bitslice_init:
    ctx: aes_ctx M32 Spec.AES256
  -> key: skey Spec.AES256
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen M32 Spec.AES256)) (elem_zero M32)))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen M32)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen M32)) ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    let state = Spec.aes_ctr32_init_LE Spec.AES256
      (as_seq h0 key) (as_seq h0 nonce) in
    nonce_to_bytes M32 n == state.block /\
    keyx_to_bytes M32 Spec.AES256 kex == state.key_ex)))

let aes256_bitslice_init ctx key nonce = aes_init_ #M32 #Spec.AES256 ctx key nonce

inline_for_extraction noextract
val aes256_ni_init:
    ctx: aes_ctx MAES Spec.AES256
  -> key: skey Spec.AES256
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\ disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen MAES Spec.AES256)) (elem_zero MAES)))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen MAES)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen MAES)) ((Spec.num_rounds Spec.AES256+1) * v (klen MAES)) in
    let state = Spec.aes_ctr32_init_LE Spec.AES256
      (as_seq h0 key) (as_seq h0 nonce) in
    nonce_to_bytes MAES n == state.block /\
    keyx_to_bytes MAES Spec.AES256 kex == state.key_ex)))

let aes256_ni_init ctx key nonce = aes_init_ #MAES #Spec.AES256 ctx key nonce

inline_for_extraction noextract
val aes_init:
    #m: m_spec
  -> #a: Spec.variant
  -> ctx: aes_ctx m a
  -> key: skey a
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce /\ live h key /\
    disjoint ctx key /\
    as_seq h ctx == Seq.create (size_v (ctxlen m a)) (elem_zero m)))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    (let n = LSeq.sub (as_seq h1 ctx) 0 (v (nlen m)) in
    let kex = LSeq.sub (as_seq h1 ctx)
      (v (nlen m)) ((Spec.num_rounds a+1) * v (klen m)) in
    let state = Spec.aes_ctr32_init_LE a (as_seq h0 key)
      (as_seq h0 nonce) in
    nonce_to_bytes m n == state.block /\
    keyx_to_bytes m a kex == state.key_ex)))

let aes_init #m #a ctx key nonce =
  match m,a with
  | M32,Spec.AES128 -> aes128_bitslice_init ctx key nonce
  | M32,Spec.AES256 -> aes256_bitslice_init ctx key nonce
  | MAES,Spec.AES128 -> aes128_ni_init ctx key nonce
  | MAES,Spec.AES256 -> aes256_ni_init ctx key nonce

(* END INLINING PATTERN *)

inline_for_extraction noextract
val aes_set_nonce:
    #m: m_spec
  -> #a: Spec.variant
  -> ctx: aes_ctx m a
  -> nonce: lbuffer uint8 12ul ->
  Stack unit
  (requires (fun h -> live h ctx /\ live h nonce))
  (ensures (fun h0 b h1 -> modifies (loc ctx) h0 h1 /\
    nonce_to_bytes m (LSeq.sub (as_seq h1 ctx) 0 (v (nlen m))) ==
      u8_16_to_le (LSeq.update_sub
      (LSeq.create 16 (u8 0)) 0 12 (as_seq h0 nonce))))

let aes_set_nonce #m #a ctx nonce =
  let n = get_nonce ctx in
  load_nonce #m n nonce;
  let h0 = ST.get() in
  u8_16_to_le_lemma (nonce_to_bytes m
    (LSeq.sub (as_seq h0 ctx) 0 (v (nlen m))))

inline_for_extraction noextract
val aes_block_cipher0:
    #m: m_spec
  -> #a: Spec.variant
  -> out: lbuffer uint8 16ul
  -> inp: lbuffer uint8 16ul
  -> kex: lbuffer (stelem m) ((nr a +! 1ul) *. klen m)
  -> st: lbuffer (stelem m) (stlen m)
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h kex /\
    live h st /\ disjoint st kex /\ disjoint st inp))
  (ensures (fun h0 _ h1 -> modifies2 out st h0 h1 /\
    as_seq h1 out == u8_16_to_le (Spec.aes_encrypt_block a
      (keyx_to_bytes m a (as_seq h0 kex)) (u8_16_to_le (as_seq h0 inp)))))

let aes_block_cipher0 #m #a out inp kex st =
  load_block0 #m st inp;
  let h0 = ST.get() in
  u8_16_to_le_lemma (state_to_bytes m (as_seq h0 st) 0);
  block_cipher #m #a st kex;
  store_block0 #m out st

inline_for_extraction noextract
val aes_encrypt_block:
    #m: m_spec
  -> #a: Spec.variant
  -> ob: lbuffer uint8 16ul
  -> ctx: aes_ctx m a
  -> ib: lbuffer uint8 16ul ->
  Stack unit
  (requires (fun h -> live h ob /\ live h ctx /\ live h ib))
  (ensures (fun h0 _ h1 -> modifies (loc ob) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)) in
    as_seq h1 ob == u8_16_to_le (Spec.aes_encrypt_block a (keyx_to_bytes m a k)
      (u8_16_to_le (as_seq h0 ib))))))

let aes_encrypt_block #m #a ob ctx ib =
  assert (v ((nr a +! 1ul) *. klen m) == v (nr a +! 1ul) * v (klen m));
  assert (v (nr a +! 1ul) == v (nr a) + 1);
  assert (v (nr a) == Spec.num_rounds a);
  push_frame();
  let kex = get_kex ctx in
  let st = create_state #m in
  assert (kex == gsub ctx (nlen m) ((nr a +! 1ul) *. klen m));
  aes_block_cipher0 #m #a ob ib kex st;
  pop_frame()


inline_for_extraction noextract
val aes_ctr32_key_block:
    #m: m_spec
  -> #a: Spec.variant
  -> out: lbuffer uint8 16ul
  -> kex: lbuffer (stelem m) ((nr a +! 1ul) *. klen m)
  -> nonce: lbuffer (stelem m) (nlen m)
  -> st: lbuffer (stelem m) (stlen m)
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h kex /\ live h nonce /\
    live h st /\ disjoint st kex))
  (ensures (fun h0 _ h1 -> modifies2 out st h0 h1 /\
    as_seq h1 out == u8_16_to_le (Spec.aes_encrypt_block a
      (keyx_to_bytes m a (as_seq h0 kex)) (Spec.aes_ctr32_set_counter_LE
      (nonce_to_bytes m (as_seq h0 nonce)) counter))))

let aes_ctr32_key_block #m #a out kex nonce st counter =
  load_state #m st nonce counter;
  block_cipher #m #a st kex;
  store_block0 #m out st

inline_for_extraction noextract
val aes_key_block:
    #m: m_spec
  -> #a: Spec.variant
  -> kb: lbuffer uint8 16ul
  -> ctx: aes_ctx m a
  -> counter: uint32 ->
  Stack unit
  (requires (fun h -> live h kb /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc kb) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)) in
    as_seq h1 kb == u8_16_to_le (Spec.aes_encrypt_block a
      (keyx_to_bytes m a k) (Spec.aes_ctr32_set_counter_LE
      (nonce_to_bytes m n) counter)))))

let aes_key_block #m #a kb ctx counter =
  assert (v ((nr a +! 1ul) *. klen m) == v (nr a +! 1ul) * v (klen m));
  assert (v (nr a +! 1ul) == v (nr a) + 1);
  assert (v (nr a) == Spec.num_rounds a);
  push_frame();
  let kex = get_kex ctx in
  let n = get_nonce ctx in
  let st = create_state #m in
  assert (kex == gsub ctx (nlen m) ((nr a +! 1ul) *. klen m));
  assert (n == gsub ctx 0ul (nlen m));
  aes_ctr32_key_block #m #a kb kex n st counter;
  pop_frame()


val aes_ctr32_encrypt_block_lemma:
    #m:m_spec
  -> #a: Spec.variant
  -> inp:LSeq.lseq uint8 64
  -> k:LSeq.lseq (stelem m) ((Spec.num_rounds a+1) * v (klen m))
  -> n:LSeq.lseq (stelem m) (v (nlen m))
  -> counter:uint32
  -> i:size_nat{i < 4} ->
  Lemma (
   let k = keyx_to_bytes m a k in
   let n = nonce_to_bytes m n in
   Spec.aes_ctr32_encrypt_block_LE a k n (counter +. u32 i)
    (LSeq.sub inp (i*16) 16) ==
      u8_16_to_le (LSeq.map2 ( ^. ) (u8_16_to_le (LSeq.sub inp (i*16) 16))
        (Spec.aes_encrypt_block a k (Spec.aes_ctr32_set_counter_LE n
        (counter +. u32 i)))))

let aes_ctr32_encrypt_block_lemma #m #a inp k n counter i =
  let k = keyx_to_bytes m a k in
  let n = nonce_to_bytes m n in
  LSeq.eq_intro (Spec.aes_ctr32_encrypt_block_LE a k n (counter +. u32 i)
    (LSeq.sub inp (i*16) 16))
    (u8_16_to_le (LSeq.map2 ( ^. ) (u8_16_to_le (LSeq.sub inp (i*16) 16))
      (Spec.aes_encrypt_block a k (Spec.aes_ctr32_set_counter_LE n
      (counter +. u32 i)))))

val concat_64_lemma:
  l:LSeq.lseq uint8 64 ->
  Lemma (
   let l0 = LSeq.sub l 0 16 in
   let l1 = LSeq.sub l 16 16 in
   let l2 = LSeq.sub l 32 16 in
   let l3 = LSeq.sub l 48 16 in
   l == LSeq.concat (LSeq.concat (LSeq.concat l0 l1) l2) l3)

let concat_64_lemma l =
  let l0 = LSeq.sub l 0 16 in
  let l1 = LSeq.sub l 16 16 in
  let l2 = LSeq.sub l 32 16 in
  let l3 = LSeq.sub l 48 16 in
  LSeq.eq_intro l (LSeq.concat (LSeq.concat (LSeq.concat l0 l1) l2) l3)

val aes_ctr32_encrypt_block_4_lemma:
    #m:m_spec
  -> #a: Spec.variant
  -> out:LSeq.lseq uint8 64
  -> inp:LSeq.lseq uint8 64
  -> k:LSeq.lseq (stelem m) ((Spec.num_rounds a+1) * v (klen m))
  -> n:LSeq.lseq (stelem m) (v (nlen m))
  -> counter:uint32 ->
  Lemma
  (requires (
    let k = keyx_to_bytes m a k in
    let n = nonce_to_bytes m n in
    LSeq.sub out 0 16 == Spec.aes_ctr32_encrypt_block_LE a k n
      counter (LSeq.sub inp 0 16) /\
    LSeq.sub out 16 16 == Spec.aes_ctr32_encrypt_block_LE a k n
      (counter +. u32 1) (LSeq.sub inp 16 16) /\
    LSeq.sub out 32 16 == Spec.aes_ctr32_encrypt_block_LE a k n
      (counter +. u32 2) (LSeq.sub inp 32 16) /\
    LSeq.sub out 48 16 == Spec.aes_ctr32_encrypt_block_LE a k n
      (counter +. u32 3) (LSeq.sub inp 48 16)))
  (ensures (
    let k = keyx_to_bytes m a k in
    let n = nonce_to_bytes m n in
    out == Spec.aes_ctr32_encrypt_block_4_LE a k n counter inp))

let aes_ctr32_encrypt_block_4_lemma #m #a out inp k n counter =
  concat_64_lemma out

inline_for_extraction noextract
val aes_ctr32_encrypt_block:
    #m: m_spec
  -> #a: Spec.variant
  -> out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> kex: lbuffer (stelem m) ((nr a +! 1ul) *. klen m)
  -> nonce: lbuffer (stelem m) (nlen m)
  -> st: lbuffer (stelem m) (stlen m)
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h kex /\
    live h nonce /\ live h st /\ disjoint st kex /\ disjoint st inp))
  (ensures (fun h0 _ h1 -> modifies2 out st h0 h1 /\
    (let k = as_seq h0 kex in
    let n = as_seq h0 nonce in
    as_seq h1 out == Spec.aes_ctr32_encrypt_block_4_LE a 
      (keyx_to_bytes m a k) (nonce_to_bytes m n)
      counter (as_seq h0 inp))))

let aes_ctr32_encrypt_block #m #a out inp kex n st ctr =
  let h0 = ST.get() in
  assert (v ((nr a +! 1ul) *. klen m) == v (nr a +! 1ul) * v (klen m));
  assert (v (nr a +! 1ul) == v (nr a) + 1);
  assert (v (nr a) == Spec.num_rounds a);
  assert (v (ctr +. u32 0) == v ctr);
  aes_ctr32_encrypt_block_lemma #m #a (as_seq h0 inp) (as_seq h0 kex)
    (as_seq h0 n) ctr 0;
  aes_ctr32_encrypt_block_lemma #m #a (as_seq h0 inp) (as_seq h0 kex)
    (as_seq h0 n) ctr 1;
  aes_ctr32_encrypt_block_lemma #m #a (as_seq h0 inp) (as_seq h0 kex)
    (as_seq h0 n) ctr 2;
  aes_ctr32_encrypt_block_lemma #m #a (as_seq h0 inp) (as_seq h0 kex)
    (as_seq h0 n) ctr 3;
  load_state #m st n ctr;
  block_cipher #m #a st kex;
  xor_block #m out st inp;
  let h1 = ST.get() in
  aes_ctr32_encrypt_block_4_lemma #m #a (as_seq h1 out)
    (as_seq h0 inp) (as_seq h0 kex) (as_seq h0 n) ctr

inline_for_extraction noextract
val aes_update4:
    #m: m_spec
  -> #a: Spec.variant
  -> out: lbuffer uint8 64ul
  -> inp: lbuffer uint8 64ul
  -> ctx: aes_ctx m a
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_block_4_LE a 
      (keyx_to_bytes m a k) (nonce_to_bytes m n)
      counter (as_seq h0 inp))))

let aes_update4 #m #a out inp ctx ctr =
  assert (v ((nr a +! 1ul) *. klen m) == v (nr a +! 1ul) * v (klen m));
  assert (v (nr a +! 1ul) == v (nr a) + 1);
  assert (v (nr a) == Spec.num_rounds a);
  push_frame();
  let st = create_state #m in
  let kex = get_kex #m ctx in
  let n = get_nonce #m ctx in
  assert (kex == gsub ctx (nlen m) ((nr a +! 1ul) *. klen m));
  assert (n == gsub ctx 0ul (nlen m));
  aes_ctr32_encrypt_block #m #a out inp kex n st ctr;
  pop_frame()

val copy_update_sub_lemma_helper:
    rem: size_t{v rem < 64}
  -> l0:lbuffer uint8 64ul
  -> l1:lbuffer uint8 rem
  -> h0: mem
  -> h1: mem ->
  Lemma 
  (requires (live h0 l0 /\ live h0 l1 /\ modifies1 (gsub l0 0ul rem) h0 h1 /\
    LSeq.sub (as_seq h1 l0) 0 (v rem) == as_seq h0 l1))
  (ensures (
    as_seq h1 l0 ==
      LSeq.update_sub (as_seq h0 l0) 0 (LSeq.length (as_seq h0 l1)) (as_seq h0 l1)))

let copy_update_sub_lemma_helper rem l0 l1 h0 h1 =
  assert (disjoint (gsub l0 0ul rem) (gsub l0 rem (64ul -. rem)));
  LSeq.lemma_concat2 (v rem) (LSeq.sub (as_seq h1 l0) 0 (v rem)) (64 - v rem)
    (LSeq.sub (as_seq h1 l0) (v rem) (64 - v rem)) (as_seq h1 l0);
  LSeq.eq_intro (as_seq h1 l0) (LSeq.update_sub (as_seq h0 l0) 0
    (LSeq.length (as_seq h0 l1)) (as_seq h0 l1))

inline_for_extraction noextract
val aes_update4_last:
    #m: m_spec
  -> #a: Spec.variant
  -> rem: size_t{v rem < 64}
  -> ob: lbuffer uint8 rem
  -> ib: lbuffer uint8 rem
  -> ctx: aes_ctx m a
  -> ctr: uint32
  -> Stack unit
  (requires (fun h ->  live h ob /\ live h ib /\ live h ctx))
  (ensures (fun h0 _ h1 -> modifies1 ob h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)) in
    as_seq h1 ob == Spec.aes_ctr32_encrypt_last_4_LE a
      (keyx_to_bytes m a k) (nonce_to_bytes m n)
      ctr (v rem) (as_seq h0 ib))))

let aes_update4_last #m #a rem ob ib ctx ctr =
  let h0_init = ST.get() in
  push_frame();
  let last = create 64ul (u8 0) in
  let h0 = ST.get() in
  copy (sub last 0ul rem) ib;
  let h1 = ST.get() in
  copy_update_sub_lemma_helper rem last ib h0 h1;
  aes_update4 #m #a last last ctx ctr;
  copy ob (sub last 0ul rem);
  let h1 = ST.get() in
  assert (modifies2 ob last h0 h1);
  pop_frame();
  let h1 = ST.get() in
  assert (modifies1 ob h0_init h1)

inline_for_extraction noextract
val aes_ctr_:
    #m: m_spec
  -> #a: Spec.variant
  -> len: size_t{v len / 64 <= max_size_t}
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx m a
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE a
      (keyx_to_bytes m a k) (nonce_to_bytes m n)
      counter (as_seq h0 inp))))

let aes_ctr_ #m #a len out inp ctx counter =
  let rem = len %. size 64 in
  let h0 = ST.get() in
  map_blocks h0 len 64ul inp out
    (fun h -> Spec.aes_ctr32_encrypt_block_incr_4_LE a (keyx_to_bytes m a (LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)))) (nonce_to_bytes m (LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)))) counter)
    (fun h -> Spec.aes_ctr32_encrypt_last_incr_4_LE a (keyx_to_bytes m a (LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)))) (nonce_to_bytes m (LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)))) counter)
    (fun i -> (assert (v i == v (to_u32 i));
      aes_update4 #m #a (sub out (i *! size 64) (size 64)) (sub inp (i *! size 64) (size 64)) ctx (counter +. ((to_u32 i) *. u32 4))))
    (fun i -> (assert (v i == v (to_u32 i));
      aes_update4_last #m #a rem (sub out (i *! size 64) rem) (sub inp (i *! size 64) rem) ctx (counter +. ((to_u32 i) *. u32 4))))


(* BEGIN STANDARD PATTERN FOR AVOIDING INLINING *)
val aes128_ctr_bitslice:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx M32 Spec.AES128
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen M32))
      ((Spec.num_rounds Spec.AES128+1) * v (klen M32)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen M32)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES128
      (keyx_to_bytes M32 Spec.AES128 k) (nonce_to_bytes M32 n)
      counter (as_seq h0 inp))))

let aes128_ctr_bitslice len out inp ctx counter = aes_ctr_ #M32 #Spec.AES128 len out inp ctx counter

inline_for_extraction noextract
val aes128_ctr_ni:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx MAES Spec.AES128
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen MAES))
      ((Spec.num_rounds Spec.AES128+1) * v (klen MAES)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen MAES)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES128
      (keyx_to_bytes MAES Spec.AES128 k) (nonce_to_bytes MAES n)
      counter (as_seq h0 inp))))

let aes128_ctr_ni len out inp ctx counter = aes_ctr_ #MAES #Spec.AES128 len out inp ctx counter 


inline_for_extraction noextract
val aes256_ctr_ni:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx MAES Spec.AES256
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen MAES))
      ((Spec.num_rounds Spec.AES256+1) * v (klen MAES)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen MAES)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES256
      (keyx_to_bytes MAES Spec.AES256 k) (nonce_to_bytes MAES n)
      counter (as_seq h0 inp))))

let aes256_ctr_ni len out inp ctx counter = aes_ctr_ #MAES #Spec.AES256 len out inp ctx counter

val aes256_ctr_bitslice:
    len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx M32 Spec.AES256
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen M32))
      ((Spec.num_rounds Spec.AES256+1) * v (klen M32)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen M32)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE Spec.AES256
      (keyx_to_bytes M32 Spec.AES256 k) (nonce_to_bytes M32 n)
      counter (as_seq h0 inp))))

let aes256_ctr_bitslice len out inp ctx counter = aes_ctr_ #M32 #Spec.AES256 len out inp ctx counter


inline_for_extraction noextract
val aes_ctr:
    #m: m_spec
  -> #a: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> ctx: aes_ctx m a
  -> counter: uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h ctx /\
    disjoint out inp /\ disjoint out ctx))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    (let k = LSeq.sub (as_seq h0 ctx) (v (nlen m))
      ((Spec.num_rounds a+1) * v (klen m)) in
    let n = LSeq.sub (as_seq h0 ctx) 0 (v (nlen m)) in
    as_seq h1 out == Spec.aes_ctr32_encrypt_stream_LE a
      (keyx_to_bytes m a k) (nonce_to_bytes m n)
      counter (as_seq h0 inp))))

let aes_ctr #m #a len out inp ctx counter =
  match m,a with
  | M32,Spec.AES128 -> aes128_ctr_bitslice len out inp ctx counter
  | M32,Spec.AES256 -> aes256_ctr_bitslice len out inp ctx counter
  | MAES,Spec.AES128 -> aes128_ctr_ni len out inp ctx counter
  | MAES,Spec.AES256 -> aes256_ctr_ni len out inp ctx counter
(* END INLINING PATTERN *)


inline_for_extraction noextract
val aes_ctr_encrypt:
    #m: m_spec
  -> #a: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey a
  -> n:lbuffer uint8 12ul
  -> counter:uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n /\
    disjoint out inp))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_encrypt_bytes_LE a
    (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 inp)))

inline_for_extraction noextract
let aes_ctr_encrypt #m #a in_len out inp k n c =
  push_frame();
  let ctx = create_ctx m a in
  aes_init #m #a ctx k n;
  aes_ctr #m #a in_len out inp ctx c;
  pop_frame()


inline_for_extraction noextract
val aes_ctr_decrypt:
    #m: m_spec
  -> #a: Spec.variant
  -> len: size_t
  -> out: lbuffer uint8 len
  -> inp: lbuffer uint8 len
  -> k:skey a
  -> n:lbuffer uint8 12ul
  -> counter:uint32
  -> Stack unit
  (requires (fun h -> live h out /\ live h inp /\ live h k /\ live h n /\
    disjoint out inp))
  (ensures (fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.aes_ctr32_decrypt_bytes_LE a
    (as_seq h0 k) (as_seq h0 n) counter (as_seq h0 inp)))

inline_for_extraction noextract
let aes_ctr_decrypt #m #a in_len out inp  k n c =
  aes_ctr_encrypt #m #a in_len out inp k n c
