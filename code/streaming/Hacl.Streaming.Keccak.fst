module Hacl.Streaming.Keccak

open FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost
module S = FStar.Seq
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module F = Hacl.Streaming.Functor

module ST = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.Mul
open Hacl.Streaming.Types

inline_for_extraction noextract
let uint8 = Lib.IntTypes.uint8

inline_for_extraction noextract
let uint32 = Lib.IntTypes.uint32

inline_for_extraction noextract
let uint64 = Lib.IntTypes.uint64

open Spec.Hash.Definitions

open Hacl.Streaming.Interface

module D = Hacl.Hash.Definitions
module Agile = Spec.Agile.Hash

let _: squash (inversion hash_alg) = allow_inversion hash_alg

/// This is a dedicated streaming API for the Keccak construction. The reason we
/// are not piggybacking on Hacl.Streaming.MD is that we want a *single* piece
/// of code that can deal with all 6 variants at runtime, as opposed to a
/// meta-programmed version that requires six instantiations each for each one
/// of the Keccak algorithms. Notably, this means that we keep the rate at
/// run-time (relying on the key), and that we request the outputByteLen for the
/// finish function.

inline_for_extraction noextract
let alg = keccak_alg

unfold let coerce (#b #a:Type) (x:a{a == b}) : b = x

inline_for_extraction noextract
let update_multi_s (a : alg) acc (prevlen : nat) input =
  Agile.update_multi a acc () input

noextract
let update_multi_zero (a : alg) acc (prevlen : nat) :
  Lemma(update_multi_s a acc prevlen S.empty == acc) = Spec.Hash.Lemmas.update_multi_zero a acc

// TODO: this is the fourth copy of this lemma!! why?!
#push-options "--ifuel 1"
noextract
let update_multi_associative (a : alg) acc (prevlen1 prevlen2 : nat)
                             (input1 input2 : S.seq uint8) :
    Lemma
    (requires (
      prevlen1 % U32.v (D.block_len a) = 0 /\
      S.length input1 % U32.v (D.block_len a) = 0 /\
      S.length input2 % U32.v (D.block_len a) = 0 /\
      prevlen2 = prevlen1 + S.length input1))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v (D.block_len a) = 0 /\
      prevlen2 % U32.v (D.block_len a) = 0 /\
      update_multi_s a (update_multi_s a acc prevlen1 input1) prevlen2 input2 ==
        update_multi_s a acc prevlen1 input)) =
  Spec.Hash.Lemmas.update_multi_associative a acc input1 input2
#pop-options

inline_for_extraction noextract
let singleton #t (x: t) = y:t { y == x }

// Pretty C name
let hash_buf = hash_alg & B.buffer uint64
let hash_buf2 = hash_buf & hash_buf

inline_for_extraction noextract
let stateful_keccak: stateful alg =
  Stateful
    (* s: *) (fun (a: alg) ->
      singleton a & b:B.buffer uint64 { B.len b == 25ul })
    (* footprint: *) (fun #_ h (_, s) ->
      B.loc_addr_of_buffer s)
    (* freeable: *) (fun #_ h (_, s) ->
      B.freeable s)
    (* invariant: *) (fun #_ h (_, s) ->
      B.live h s)
    (* t: *) (fun _ ->
      s:S.seq uint64 { S.length s == 25 })
    (* v: *) (fun _ h (a, s) ->
       B.as_seq h s)
    (* invariant_loc_in_footprint: *) (fun #_ h (_, s) ->
      ())
    (* frame_invariant: *) (fun #_ l (_, s) h0 h1 ->
      ())
    (* frame_freeable: *) (fun #_ l (_, s) h0 h1 ->
      ())
    (* alloca: *) (fun (a: alg) ->
      a, B.alloca (Lib.IntTypes.u64 0) 25ul)
    (* create_in: *) (fun a r ->
      a, B.malloc r (Lib.IntTypes.u64 0) 25ul)
    (* free: *) (fun _ (_, s) ->
      B.free s)
    (* copy: *) (fun _ (a, s_src) (a', s_dst) ->
      B.blit s_src 0ul s_dst 0ul 25ul)

noextract inline_for_extraction
let is_shake_ a = a = Shake128 || a = Shake256

inline_for_extraction noextract
let hacl_keccak (a: G.erased alg): block alg =
  Block
    Erased
    stateful_keccak (* state *)
    (stateful_unused alg) (* key *)
    Lib.IntTypes.(x:size_t { v x > 0 }) (* output_length_t *)

    (fun _ ->
      [@inline_let]
      let max = Lib.IntTypes.(ones U64 PUB) in
      assert (forall (a: alg). Hacl.Hash.Definitions.max_input_len64 a == max);
      max) (* max_input_len *)
    (fun a l -> if is_shake_ a then Lib.IntTypes.v l else Spec.Hash.Definitions.hash_length a) (* output_length *)
    Hacl.Hash.SHA3.block_len (* block_len *)
    Hacl.Hash.SHA3.block_len (* blocks_state_len *)
    (fun _ -> 0ul) (* init_input_len *)


    (* init_input_s *)
    (fun _ _ -> S.empty)

    (* init_s *)
    (fun a _ -> Spec.Agile.Hash.init a)

    (* update_multi_s *)
    (fun a acc prevlen blocks ->
      update_multi_s a acc prevlen blocks)

    (* update_last_s *)
    (fun a acc prevlen input -> Spec.Hash.Incremental.(update_last a acc () input))

    (* finish_s *)
    (fun a _ acc l -> Spec.Agile.Hash.finish a acc (if is_shake_ a then (Lib.IntTypes.v l) else ()))
    (fun a _ s l -> Spec.Agile.Hash.(hash' a s (if is_shake_ a then (Lib.IntTypes.v l) else ())))

    (* update_multi_zero *)
    (fun a h prevlen -> update_multi_zero a h prevlen)

    (* update_multi_associative *)
    (fun a acc prevlen1 prevlen2 input1 input2 ->
      update_multi_associative a acc prevlen1 prevlen2 input1 input2)

    (* spec_is_incremental *)
    (fun a _ input l ->
      let input1 = S.append S.empty input in
      assert (S.equal input1 input);
      Spec.Hash.Incremental.hash_is_hash_incremental' a input (if is_shake_ a then (Lib.IntTypes.v l) else ()))

    (* index_of_state *)
    (fun _ (a, _) -> a)

    (* init *)
    (fun _ _ _ (a, s) -> Hacl.Hash.SHA3.init a s)

    (* update_multi *)
    (fun _ (a, s) _ blocks len ->
      Hacl.Hash.SHA3.update_multi a s () blocks (len `U32.div` Hacl.Hash.SHA3.(block_len a)))

    (* update_last *)
    (fun _ (a, s) _ last last_len ->
      Hacl.Hash.SHA3.update_last a s () last last_len)

    (* finish *)
    (fun _ _ (a, s) dst l ->
      Hacl.Hash.SHA3.(finish_keccak a s dst l))

// For pretty names in C
let state = F.state_s' (hacl_keccak SHA3_256) SHA3_256

let sha3_state a = singleton a & b:B.buffer uint64 { B.len b == 25ul }

let get_alg (a: G.erased alg) =
  F.index_of_state (hacl_keccak a) a (sha3_state (G.reveal a)) (G.erased unit)

let malloc (a: alg) =
  F.create_in (hacl_keccak a) a (sha3_state a) (G.erased unit)

let free (a: G.erased alg) =
  F.free (hacl_keccak a) a (sha3_state (G.reveal a)) (G.erased unit)

let copy (a: G.erased alg) =
  F.copy (hacl_keccak a) a (sha3_state (G.reveal a)) (G.erased unit)

let reset (a: G.erased alg) =
  F.init (hacl_keccak a) a (sha3_state (G.reveal a)) (G.erased unit)

let update (a: G.erased alg) =
  F.update (hacl_keccak a) a (sha3_state (G.reveal a)) (G.erased unit)

private
let finish_ (a: alg) =
  F.mk_finish #alg (hacl_keccak a) a (sha3_state a) (G.erased unit)

open Hacl.Streaming.Functor

// Unfortunate copy-paste since there are small variations (error code, output length)
val finish:
  a:G.erased alg -> (
  let c = hacl_keccak a in
  let a = G.reveal a in
  let i = a in
  let t = sha3_state a in
  let t' = G.erased unit in
  s:state c i t t' ->
  dst:B.buffer uint8 ->
  Stack error_code
    (requires fun h0 ->
      (not (is_shake a) ==> B.length dst == Spec.Hash.Definitions.hash_length a) /\
      invariant c i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c i h0 s)))
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          not (is_shake a) /\
          invariant c i h1 s /\
          seen c i h0 s == seen c i h1 s /\
          key c i h1 s == key c i h0 s /\
          footprint c i h0 s == footprint c i h1 s /\
          B.(modifies (loc_union (loc_buffer dst) (footprint c i h0 s)) h0 h1) /\ (
          seen_bounded c i h0 s;
          S.equal (B.as_seq h1 dst) (Spec.Agile.Hash.hash a (seen c i h0 s)) /\
          preserves_freeable c i s h0 h1)
      | InvalidAlgorithm ->
          is_shake a
      | _ ->
          False))

let finish a s dst =
  let a = get_alg a s in
  if (a = Shake128 || a = Shake256) then
    InvalidAlgorithm
  else begin
    finish_ a s dst (Hacl.Hash.SHA3.hash_len a);
    Success
  end

// Unfortunate copy-paste since we are returning an error code
val squeeze:
  a:G.erased alg -> (
  let c = hacl_keccak a in
  let a = G.reveal a in
  let i = a in
  let t = sha3_state a in
  let t' = G.erased unit in
  s:state c i t t' ->
  dst:B.buffer uint8 ->
  l:Lib.IntTypes.size_t ->
  Stack error_code
    (requires fun h0 ->
      (is_shake a ==> B.length dst == Lib.IntTypes.v l) /\
      invariant c i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c i h0 s)))
    (ensures fun h0 r h1 ->
      let _  = allow_inversion error_code in
      match r with
      | Success ->
          is_shake a /\
          l <> 0ul /\
          invariant c i h1 s /\
          seen c i h0 s == seen c i h1 s /\
          key c i h1 s == key c i h0 s /\
          footprint c i h0 s == footprint c i h1 s /\
          B.(modifies (loc_union (loc_buffer dst) (footprint c i h0 s)) h0 h1) /\ (
          seen_bounded c i h0 s;
          S.equal (B.as_seq h1 dst) (c.spec_s i (key c i h0 s) (seen c i h0 s) l)) /\
          preserves_freeable c i s h0 h1
      | InvalidAlgorithm ->
          not (is_shake a)
      | InvalidLength ->
          l = 0ul
      | _ ->
          False))

let squeeze a s dst l =
  let a = get_alg a s in
  if not (a = Shake128 || a = Shake256) then
    InvalidAlgorithm
  else if l = 0ul then
    InvalidLength
  else begin
    finish_ a s dst l;
    Success
  end

val block_len: a:G.erased alg -> (
  let c = hacl_keccak a in
  let a = G.reveal a in
  let i = a in
  let t = sha3_state a in
  let t' = G.erased unit in
  s:state c i t t' ->
  Stack Lib.IntTypes.size_t
    (requires fun h0 ->
      invariant c i h0 s)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      Lib.IntTypes.v r == Spec.Hash.Definitions.block_length a /\
      Lib.IntTypes.v r == Spec.Hash.Definitions.rate a / 8))

let block_len a s =
  let a = get_alg a s in
  Hacl.Hash.SHA3.block_len a

val hash_len: a:G.erased alg -> (
  let c = hacl_keccak a in
  let a = G.reveal a in
  let i = a in
  let t = sha3_state a in
  let t' = G.erased unit in
  s:state c i t t' ->
  Stack Lib.IntTypes.size_t
    (requires fun h0 ->
      not (is_shake_ a) /\
      invariant c i h0 s)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      Lib.IntTypes.v r == Spec.Hash.Definitions.hash_length a))

let hash_len a s =
  let a = get_alg a s in
  Hacl.Hash.SHA3.hash_len a

val is_shake: a:G.erased alg -> (
  let c = hacl_keccak a in
  let a = G.reveal a in
  let i = a in
  let t = sha3_state a in
  let t' = G.erased unit in
  s:state c i t t' ->
  Stack bool
    (requires fun h0 ->
      invariant c i h0 s)
    (ensures fun h0 r h1 ->
      B.(modifies loc_none h0 h1) /\
      r == is_shake_ a))

let is_shake a s =
  is_shake_ (get_alg a s)
