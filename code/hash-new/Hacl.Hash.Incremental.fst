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

module Common = Spec.Hash.Common
module Spec = Spec.Hash

open Hacl.Hash.Common
open Hacl.Hash.Lemmas
open Spec.Hash.Helpers
open Spec.Hash.Incremental
open FStar.Mul

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
val mk_update_last: a:hash_alg ->
  Hacl.Hash.update_multi_st a ->
  Hacl.Hash.Common.pad_st a ->
  update_last_st a

noextract
let mk_update_last a update_multi pad s prev_len input input_len =
  ST.push_frame ();
  let h0 = ST.get () in

  (* Get a series of complete blocks. *)
  let blocks_n = U32.(input_len /^ size_block_ul a) in
  let blocks_len = U32.(blocks_n *^ size_block_ul a) in
  assert (U32.v blocks_len % size_block a = 0);
  let blocks = B.sub input 0ul blocks_len in

  (* The rest that doesn't make up a complete block *)
  let rest_len = U32.(input_len -^ blocks_len) in
  assert (U32.v rest_len < size_block a);
  let rest = B.sub input blocks_len rest_len in

  update_multi s blocks blocks_n;

  let h1 = ST.get () in
  assert (B.as_seq h0 input = S.append (B.as_seq h1 blocks) (B.as_seq h1 rest));
  assert (B.as_seq h1 s = Spec.update_multi a (B.as_seq h0 s) (B.as_seq h0 blocks));

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

  let tmp_twoblocks = B.alloca 0uy U32.(2ul *^ size_block_ul a) in
  let tmp = B.sub tmp_twoblocks 0ul tmp_len in
  let tmp_rest = B.sub tmp 0ul rest_len in
  let tmp_pad = B.sub tmp rest_len pad_len in
  B.blit rest 0ul tmp_rest 0ul rest_len;
  pad total_input_len tmp_pad;

  let h2 = ST.get () in
  assert (B.as_seq h2 tmp = S.append (B.as_seq h2 tmp_rest) (B.as_seq h2 tmp_pad));
  assert (B.as_seq h2 tmp_rest = B.as_seq h1 rest);
  assert (B.as_seq h2 tmp_pad = Common.pad a (len_v a total_input_len));

  (* Update multi those last few blocks *)
  update_multi s tmp U32.(tmp_len /^ size_block_ul a);

  let h3 = ST.get () in
  assert (B.as_seq h3 s =
    Spec.update_multi a (Spec.update_multi a (B.as_seq h0 s) (B.as_seq h1 blocks))
      (S.append (B.as_seq h1 rest) (Common.pad a (len_v a total_input_len))));
  assert (
    let s1 = B.as_seq h1 blocks in
    let s2 = B.as_seq h2 rest in
    let s3 = Common.pad a (len_v a total_input_len) in
    S.equal (S.append s1 (S.append s2 s3)) (S.append (S.append s1 s2) s3));

  ST.pop_frame ()


let update_last_sha2_224: update_last_st SHA2_224 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_last SHA2_224 Hacl.Hash.update_multi_sha2_224 Hacl.SHA2.pad_224) [`%mk_update_last]))

let update_last_sha2_256: update_last_st SHA2_256 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_last SHA2_256 Hacl.Hash.update_multi_sha2_256 Hacl.SHA2.pad_256) [`%mk_update_last]))

let update_last_sha2_384: update_last_st SHA2_384 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_last SHA2_384 Hacl.Hash.update_multi_sha2_384 Hacl.SHA2.pad_384) [`%mk_update_last]))

let update_last_sha2_512: update_last_st SHA2_512 =
  Tactics.(synth_by_tactic
    (specialize (mk_update_last SHA2_512 Hacl.Hash.update_multi_sha2_512 Hacl.SHA2.pad_512) [`%mk_update_last]))

