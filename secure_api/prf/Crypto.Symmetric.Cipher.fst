module Crypto.Symmetric.Cipher

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// Multiplexing and hiding concrete implementations: AES128, AES256, and CHACHA20. 
// Consider also enforcing key abstraction (but quite verbose to code; see Plain.fst).

open FStar.HyperStack
open FStar.Buffer
open Buffer.Utils
module HS = FStar.HyperStack

open FStar.UInt32
open Crypto.Symmetric.Bytes
open Crypto.Indexing

module AES128 = Crypto.Symmetric.AES128
module AES256 = Crypto.Symmetric.AES

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

(* module CHACHA = Hacl.Symmetric.Chacha20 *)
module CHACHA = Hacl.SecureAPI.Chacha20

type alg = cipherAlg
let algi = cipherAlg_of_id

inline_for_extraction let keylen = function
  | AES128   -> 16ul
  | AES256   -> 32ul
  | CHACHA20 -> 32ul

inline_for_extraction let blocklen = function
  | AES128   -> 16ul
  | AES256   -> 16ul
  | CHACHA20 -> 64ul

inline_for_extraction let ivlen (a:alg) = 12ul 

// Initialization function
// AES: S-box (256) + expanded key 4*nb*(nr+1)
// ChaCha20: only the key
inline_for_extraction let statelen = function
  | AES128   -> 432ul // 256 + 176
  | AES256   -> 496ul // 256 + 240
  | CHACHA20 -> 32ul
  (* | CHACHA20 -> 16ul *)

(*17-02-11  why?
inline_for_extraction let stlen = function
  | AES128   -> 432ul // 256 + 176
  | AES256   -> 496ul // 256 + 240
  | CHACHA20 -> 16ul
*)

type ctr = UInt32.t

type key a   = lbuffer (v (keylen a))
type block a = lbuffer (v (blocklen a))

(*
let state_limb = function
  | AES128 -> FStar.UInt8.t
  | AES256 -> FStar.UInt8.t
  | CHACHA20 -> FStar.UInt32.t

unfold inline_for_extraction
type state a = b:Buffer.buffer (state_limb a){Buffer.length b = UInt32.v (stlen a)}
// problematic with Kremlin? Use sum type for now?
*)
unfold inline_for_extraction
type state a = lbuffer (v (statelen a))

// 16-10-02 an integer value, instead of a lbuffer (v (ivlen)),
// so that it can be used both in abstract indexes and in real code.
inline_for_extraction
type iv a = n:UInt128.t { UInt128.v n < pow2 (v (8ul *^ ivlen a)) }

#set-options "--z3rlimit 40"

val init:
  #i:id ->
  k:key (algi i) ->
  st:state (algi i) { disjoint k st } -> Stack unit
    (requires (fun h -> live h k /\ live h st))
    (ensures (fun h0 _ h1 -> live h1 st /\ modifies_1 st h0 h1))
let init #i k st =
  let a = algi i in
  match a with
  | CHACHA20 ->
    (* CHACHA.chacha_keysetup s k *)
    Buffer.blit k 0ul st 0ul (keylen a)

  | AES128 ->
    let sbox = Buffer.sub st 0ul 256ul in
    let w = Buffer.sub st 256ul 176ul in
    begin
    match aesImpl_of_id i with
    | HaclAES ->
      let h0 = ST.get() in
      AES128.mk_sbox sbox;
      let h1 = ST.get() in
      lemma_disjoint_sub st w k;
      AES128.keyExpansion k w sbox;
      let h2 = ST.get() in
      lemma_modifies_1_1 sbox w h0 h1 h2;
      modifies_subbuffer_2_prime h0 h2 sbox w st
    | _ ->
      Vale.AES.keyExpansion k w sbox
    end

  | AES256 ->
    let sbox = Buffer.sub st 0ul 256ul in
    let w = Buffer.sub st 256ul 240ul in
    let h0 = ST.get() in
    AES256.mk_sbox sbox;
    let h1 = ST.get() in
    lemma_disjoint_sub st w k;
    AES256.keyExpansion k w sbox;
    let h2 = ST.get() in
    lemma_modifies_1_1 sbox w h0 h1 h2;
    modifies_subbuffer_2_prime h0 h2 sbox w st


// type ivv a   = lbytes (v (ivlen a))
// let load_iv a (i: iv a) : ivv a = Plain.load_bytes (ivlen a) i

(* Update the counter, replace last 4 bytes of counter with num. *)
(* num is precalculated by the function who calls this function. *)
private val aes_store_counter: counter:lbuffer (v (blocklen AES256)) -> num:ctr -> Stack unit
    (requires (fun h -> live h counter))
    (ensures (fun h0 _ h1 -> live h1 counter /\ modifies_1 counter h0 h1))
let aes_store_counter b x =
  let b0 = FStar.Int.Cast.uint32_to_uint8 (x &^ 255ul) in
  let b1 = FStar.Int.Cast.uint32_to_uint8 ((x >>^ 8ul) &^ 255ul) in
  let b2 = FStar.Int.Cast.uint32_to_uint8 ((x >>^ 16ul) &^ 255ul) in
  let b3 = FStar.Int.Cast.uint32_to_uint8 ((x >>^ 24ul) &^ 255ul) in
  b.(15ul) <- b0;
  b.(14ul) <- b1;
  b.(13ul) <- b2;
  b.(12ul) <- b3


// TODO: These lemmas should be in FStar.Buffer
private val fresh_frame_unused_in: #t:Type -> b:Buffer.buffer t -> h0:mem -> h1:mem -> Lemma
  (requires (fresh_frame h0 h1 /\ b `unused_in` h1))
  (ensures  (b `unused_in` h0))
  [ SMTPat (fresh_frame h0 h1); SMTPat (b `unused_in` h1) ]
let fresh_frame_unused_in #t b h0 h1 = ()

private val modifies_0_unused_in: #t:Type -> b:Buffer.buffer t -> h0:mem -> h1:mem -> Lemma
  (requires (modifies_0 h0 h1 /\ b `unused_in` h1))
  (ensures  (b `unused_in` h0))
  [ SMTPat (modifies_0 h0 h1); SMTPat (b `unused_in` h1) ]
let modifies_0_unused_in #t b h0 h1 =
  lemma_reveal_modifies_0 h0 h1

private val modifies_1_unused_in: #t:Type -> #t':Type
  -> b:Buffer.buffer t -> b':Buffer.buffer t' -> h0:mem -> h1:mem -> Lemma
  (requires (modifies_1 b h0 h1 /\ b' `unused_in` h1 /\ disjoint b b'))
  (ensures  (b' `unused_in` h0))
  [ SMTPat (modifies_1 b h0 h1); SMTPat (b' `unused_in` h1) ]
let modifies_1_unused_in #t #t' b b' h0 h1 =
  lemma_reveal_modifies_1 b h0 h1


val compute:
  i:id ->
  output:buffer -> 
  st:state (algi i) {disjoint output st} ->
  n:iv (algi i) ->
  counter: ctr ->
  len:UInt32.t { len <=^  blocklen (algi i) /\ v len <= length output} -> Stack unit
    (requires (fun h -> live h st /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1))
let compute i output st n counter len = 
  let h0 = ST.get() in 
  let a = algi i in
  begin match a with
  | CHACHA20 -> // already specialized for counter mode
      begin
      push_frame();
      let h1 = ST.get() in
      let nbuf = Buffer.create 0uy (ivlen CHACHA20) in
      let h2 = ST.get() in
      store_uint128 (ivlen CHACHA20) nbuf n;
      let h3 = ST.get() in
      let chacha_state = Buffer.create 0ul 16ul in
      let h4 = ST.get() in
      if len = 64ul then (
        CHACHA.setup chacha_state st nbuf counter;
        let h5 = ST.get() in
        CHACHA.chacha20_stream (Buffer.sub output 0ul 64ul) chacha_state;
        let h6 = ST.get() in
        lemma_modifies_0_1' nbuf h1 h2 h3;
        lemma_modifies_0_1' chacha_state h3 h4 h5;
        lemma_modifies_1_1 chacha_state output h4 h5 h6
        (* CHACHA.chacha_keysetup chacha_state st; *)
        (* CHACHA.chacha_ietf_ivsetup chacha_state nbuf counter; *)
        (* CHACHA.chacha_encrypt_bytes_stream chacha_state output) *)
      ) else (
        CHACHA.setup chacha_state st nbuf counter;
        let h5 = ST.get() in
        CHACHA.chacha20_stream_finish (Buffer.sub output 0ul len) len chacha_state;
        let h6 = ST.get() in
        lemma_modifies_0_1' nbuf h1 h2 h3;
        lemma_modifies_0_1' chacha_state h3 h4 h5;
        lemma_modifies_1_1 chacha_state output h4 h5 h6
        (* CHACHA.chacha_keysetup chacha_state st; *)
        (* CHACHA.chacha_ietf_ivsetup chacha_state nbuf counter; *)
        (* CHACHA.chacha_encrypt_bytes_finish_stream chacha_state output len *)
      );        
      pop_frame()
      end

  // ADL: TODO single parametric AES module
  | AES128 ->
      begin
      push_frame();
      let h1 = ST.get() in
      let sbox = Buffer.sub st 0ul 256ul in
      let w = Buffer.sub st 256ul 176ul in
      let ctr_block = Buffer.create 0uy (blocklen AES128) in
      let h2 = ST.get() in
      store_uint128 (ivlen AES128) (Buffer.sub ctr_block 0ul (ivlen AES128)) n;
      let h3 = ST.get() in
      aes_store_counter ctr_block counter;
      let h4 = ST.get() in
      let output_block = Buffer.create 0uy (blocklen AES128) in
      let h5 = ST.get() in
      begin
      match aesImpl_of_id i with
       | HaclAES -> AES128.cipher output_block ctr_block w sbox
       | ValeAES -> Vale.AES.cipher output_block ctr_block w sbox
      end;
      let h6 = ST.get() in
      blit output_block 0ul output 0ul len; // too much copying!
      let h7 = ST.get() in
      lemma_modifies_1_trans ctr_block h2 h3 h4;
      lemma_modifies_0_1' ctr_block h1 h2 h4;
      lemma_modifies_1_1 output_block output h5 h6 h7;
      modifies_1_unused_in ctr_block output_block h3 h4;
      modifies_1_unused_in ctr_block output_block h2 h3;
      modifies_0_unused_in output_block h1 h2;
      fresh_frame_unused_in output_block h0 h1;
      lemma_modifies_0_2 output output_block h1 h5 h7;
      pop_frame()
      //modifies_popped_1 output h0 h1 h7 h8
      end

  | AES256 ->
      begin
      push_frame();
      let h1 = ST.get() in
      let sbox = Buffer.sub st 0ul 256ul in
      let w = Buffer.sub st 256ul 240ul in
      let ctr_block = Buffer.create 0uy (blocklen AES256) in
      let h2 = ST.get() in
      store_uint128 (ivlen AES256) (Buffer.sub ctr_block 0ul (ivlen AES256)) n;
      let h3 = ST.get() in
      aes_store_counter ctr_block counter;
      let h4 = ST.get() in
      let output_block = Buffer.create 0uy (blocklen AES256) in
      let h5 = ST.get() in
      AES.cipher output_block ctr_block w sbox;
      let h6 = ST.get() in
      blit output_block 0ul output 0ul len; // too much copying!
      let h7 = ST.get() in
      lemma_modifies_1_trans ctr_block h2 h3 h4;
      lemma_modifies_0_1' ctr_block h1 h2 h4;
      lemma_modifies_1_1 output_block output h5 h6 h7;
      modifies_1_unused_in ctr_block output_block h3 h4;
      modifies_1_unused_in ctr_block output_block h2 h3;
      modifies_0_unused_in output_block h1 h2;
      fresh_frame_unused_in output_block h0 h1;
      lemma_modifies_0_2 output output_block h1 h5 h7;
      pop_frame()
      //modifies_popped_1 output h0 h1 h7 h8
      end
  end
