module Hacl.Hash.Incremental

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module Tactics = FStar.Tactics
module Lemmas = FStar.Math.Lemmas

open Hacl.Hash.Common
open Hacl.Hash.Lemmas
open Spec.Hash
open Spec.Hash.Helpers
open Spec.Hash.Incremental
open FStar.Mul

inline_for_extraction
let update_last_t (a: hash_alg) =
  s:state a ->
  prev_len:len_t a { len_v a prev_len % size_block a = 0 } ->
  input:B.buffer U8.t { B.length input + len_v a prev_len < max_input8 a } ->
  input_len:U32.t { B.length input = U32.v input_len } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      Seq.equal (B.as_seq h1 s)
        (update_last a (B.as_seq h0 s) (len_v a prev_len) (B.as_seq h0 input))))

inline_for_extraction
let find_update_multi (a: hash_alg): Hacl.Hash.update_multi_t a =
  match a with
  | SHA2_224 -> Hacl.Hash.update_multi_sha2_224
  | SHA2_256 -> Hacl.Hash.update_multi_sha2_256
  | SHA2_384 -> Hacl.Hash.update_multi_sha2_384
  | SHA2_512 -> Hacl.Hash.update_multi_sha2_512
  | _ -> admit ()

noextract
val mk_update_last: a:hash_alg -> update_last_t a

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let padding_round (a: hash_alg) (len: len_t a): Lemma
  (ensures (
    (len_v a len + pad_length a (len_v a len)) % size_block a = 0))
=
  ()

let pad0_length_mod (a: hash_alg) (base_len: nat) (len: nat): Lemma
  (requires (
    base_len % size_block a = 0))
  (ensures (
    pad0_length a (base_len + len) = pad0_length a len))
=
  ()

let pad_length_mod (a: hash_alg) (base_len len: nat): Lemma
  (requires (
    base_len % size_block a = 0))
  (ensures (
    pad_length a (base_len + len) = pad_length a len))
=
  pad0_length_mod a base_len len

let pad_length_bound (a: hash_alg) (len: len_t a): Lemma
  (ensures (pad_length a (len_v a len) <= 2 * size_block a))
=
  ()

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 150"

(* Avoiding an ill-formed pattern error... *)
let len_add32 (a: hash_alg)
  (prev_len: len_t a)
  (input_len: U32.t { U32.v input_len + len_v a prev_len < max_input8 a }):
  x:len_t a { len_v a x = len_v a prev_len + U32.v input_len }
=
  let open FStar.Int.Cast.Full in
  match a with
  | SHA2_224 | SHA2_256 | MD5 | SHA1 ->
      assert_norm (pow2 61 < pow2 64);
      U64.(prev_len +^ uint32_to_uint64 input_len)
  | SHA2_384 | SHA2_512 ->
      assert_norm (pow2 125 < pow2 128);
      U128.(prev_len +^ uint64_to_uint128 (uint32_to_uint64 input_len))

noextract
let mk_update_last a s prev_len input input_len =
  ST.push_frame ();

  (* Get a series of complete blocks. *)
  let blocks_n = U32.(input_len /^ size_block_ul a) in
  let blocks_len = U32.(blocks_n *^ size_block_ul a) in
  assert (U32.v blocks_len % size_block a = 0);
  let blocks = B.sub input 0ul blocks_len in

  (* The rest that doesn't make up a complete block *)
  let rest_len = U32.(input_len -^ blocks_len) in
  assert (U32.v rest_len < size_block a);
  let rest = B.sub input blocks_len rest_len in

  find_update_multi a s blocks blocks_n;

  (* Compute the total number of bytes fed. *)
  let total_input_len: len_t a = len_add32 a prev_len input_len in

  (* Blit the remaining data and the padding together *)
  let pad_len = pad_len a total_input_len in
  let tmp_len = U32.( rest_len +^ pad_len ) in
  assert (len_v a total_input_len = len_v a prev_len + U32.v blocks_len + U32.v rest_len);
  Lemmas.modulo_distributivity (len_v a prev_len) (U32.v blocks_len) (size_block a);
  assert ((len_v a prev_len + U32.v blocks_len) % size_block a = 0);
  pad_length_mod a (len_v a prev_len + U32.v blocks_len) (U32.v rest_len);
  padding_round a total_input_len;
  assert (U32.v tmp_len % size_block a = 0);

  (* Bonus, not strictly necessary, could be useful to get rid of the
     variable-length allocation below. *)
  pad_length_bound a total_input_len;
  assert (U32.v tmp_len <= 2 * size_block a);

  let tmp = B.alloca 0uy tmp_len in
  let tmp_rest = B.sub tmp 0ul rest_len in
  let tmp_pad = B.sub tmp rest_len pad_len in
  B.blit rest 0ul tmp_rest 0ul rest_len;
  Hacl.Hash.Common.pad a total_input_len tmp_pad;

  (* Update multi those last few blocks *)
  find_update_multi a s tmp U32.(tmp_len /^ size_block_ul a);

  ST.pop_frame ();

  admit ()

