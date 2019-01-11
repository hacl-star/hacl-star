module Hacl.Hash.MD

(** The Merkle-Damgård construction. *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Lemmas = FStar.Math.Lemmas
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Hash.Definitions
open Hacl.Hash.Lemmas
open Spec.Hash.Definitions
open FStar.Mul

(** Auxiliary helpers *)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let padding_round (a: hash_alg) (len: len_t a): Lemma
  (ensures (
    (len_v a len + pad_length a (len_v a len)) % block_length a = 0))
=
  ()

let pad0_length_mod (a: hash_alg) (base_len: nat) (len: nat): Lemma
  (requires (
    base_len % block_length a = 0))
  (ensures (
    pad0_length a (base_len + len) = pad0_length a len))
=
  ()

let pad_length_mod (a: hash_alg) (base_len len: nat): Lemma
  (requires (
    base_len % block_length a = 0))
  (ensures (
    pad_length a (base_len + len) = pad_length a len))
=
  pad0_length_mod a base_len len

let pad_length_bound (a: hash_alg) (len: len_t a): Lemma
  (ensures (pad_length a (len_v a len) <= 2 * block_length a))
=
  ()

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"

(* Avoiding an ill-formed pattern error... *)
noextract inline_for_extraction
let len_add32 (a: hash_alg)
  (prev_len: len_t a)
  (input_len: U32.t { U32.v input_len + len_v a prev_len < max_input_length a }):
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

#push-options "--max_fuel 1 --z3rlimit 128 --using_facts_from '* -FStar.UInt8 -FStar.UInt16 -FStar.UInt32 -FStar.UInt64 -FStar.UInt128'"

(** Iterated compression function. *)
noextract inline_for_extraction
let mk_update_multi a update s blocks n_blocks =
  let h0 = ST.get () in
  let inv (h: HS.mem) (i: nat) =
    let i_block = block_length a * i in
    i <= U32.v n_blocks /\
    B.live h s /\ B.live h blocks /\
    B.(modifies (loc_buffer s) h0 h) /\
    S.equal (B.as_seq h s)
      (Spec.Hash.update_multi a (B.as_seq h0 s) (S.slice (B.as_seq h0 blocks) 0 i_block))
  in
  let f (i:U32.t { U32.(0 <= v i /\ v i < v n_blocks)}): ST.Stack unit
    (requires (fun h -> inv h (U32.v i)))
    (ensures (fun h0 _ h1 -> inv h0 (U32.v i) /\ inv h1 (U32.v i + 1)))
  =
    let h1 = ST.get () in
    let sz = block_len a in
    let blocks0 = B.sub blocks 0ul U32.(sz *^ i) in
    let block = B.sub blocks U32.(sz *^ i) sz in
    update s block;
    let h2 = ST.get () in
    assert (
      let s0 = B.as_seq h0 s in
      let s1 = B.as_seq h1 s in
      let s2 = B.as_seq h2 s in
      let blocks = B.as_seq h0 blocks in
      let block = B.as_seq h0 block in
      let blocks0 = B.as_seq h0 blocks0 in
      let i = U32.v i in
      let n_blocks = U32.v n_blocks in
      block_length a * (i + 1) <= S.length blocks /\
      (block_length a * (i + 1) - block_length a * i) % block_length a = 0 /\
      S.equal block (S.slice blocks (block_length a * i) (block_length a * (i + 1))) /\
      S.equal s2 (Spec.Hash.update_multi a s1 block))
  in
  assert (B.length blocks = U32.v n_blocks * block_length a);
  C.Loops.for 0ul n_blocks inv f

#push-options "--max_fuel 0 --z3rlimit 400"

(** An arbitrary number of bytes, then padding. *)
noextract inline_for_extraction
let mk_update_last a update_multi pad s prev_len input input_len =
  ST.push_frame ();
  let h0 = ST.get () in

  (* Get a series of complete blocks. *)
  let blocks_n = U32.(input_len /^ block_len a) in
  let blocks_len = U32.(blocks_n *^ block_len a) in
  assert (U32.v blocks_len % block_length a = 0);
  let blocks = B.sub input 0ul blocks_len in

  (* The rest that doesn't make up a complete block *)
  let rest_len = U32.(input_len -^ blocks_len) in
  assert (U32.v rest_len < block_length a);
  let rest = B.sub input blocks_len rest_len in

  update_multi s blocks blocks_n;

  let h1 = ST.get () in
  assert (S.equal (B.as_seq h0 input) (S.append (B.as_seq h1 blocks) (B.as_seq h1 rest)));
  assert (S.equal (B.as_seq h1 s) (Spec.Hash.update_multi a (B.as_seq h0 s) (B.as_seq h0 blocks)));

  (* Compute the total number of bytes fed. *)
  let total_input_len: len_t a = len_add32 a prev_len input_len in

  (* Blit the remaining data and the padding together *)
  let pad_len = Hacl.Hash.PadFinish.pad_len a total_input_len in
  let tmp_len = U32.( rest_len +^ pad_len ) in
  assert (len_v a total_input_len = len_v a prev_len + U32.v blocks_len + U32.v rest_len);
  Lemmas.modulo_distributivity (len_v a prev_len) (U32.v blocks_len) (block_length a);
  assert ((len_v a prev_len + U32.v blocks_len) % block_length a = 0);
  pad_length_mod a (len_v a prev_len + U32.v blocks_len) (U32.v rest_len);
  padding_round a total_input_len;
  assert (U32.v tmp_len % block_length a = 0);

  pad_length_bound a total_input_len;
  assert (U32.v tmp_len <= 2 * block_length a);

  let tmp_twoblocks = B.alloca 0uy U32.(2ul *^ block_len a) in
  let tmp = B.sub tmp_twoblocks 0ul tmp_len in
  let tmp_rest = B.sub tmp 0ul rest_len in
  let tmp_pad = B.sub tmp rest_len pad_len in
  B.blit rest 0ul tmp_rest 0ul rest_len;
  pad total_input_len tmp_pad;

  let h2 = ST.get () in
  assert (S.equal (B.as_seq h2 tmp) (S.append (B.as_seq h2 tmp_rest) (B.as_seq h2 tmp_pad)));
  assert (S.equal (B.as_seq h2 tmp_rest) (B.as_seq h1 rest));
  assert (S.equal (B.as_seq h2 tmp_pad) (Spec.Hash.PadFinish.pad a (len_v a total_input_len)));

  (* Update multi those last few blocks *)
  update_multi s tmp U32.(tmp_len /^ block_len a);

  let h3 = ST.get () in
  assert (S.equal (B.as_seq h3 s)
    (Spec.Hash.update_multi a (Spec.Hash.update_multi a (B.as_seq h0 s) (B.as_seq h1 blocks))
      (S.append (B.as_seq h1 rest) (Spec.Hash.PadFinish.pad a (len_v a total_input_len)))));
  assert (
    let s1 = B.as_seq h1 blocks in
    let s2 = B.as_seq h2 rest in
    let s3 = Spec.Hash.PadFinish.pad a (len_v a total_input_len) in
    S.equal (S.append s1 (S.append s2 s3)) (S.append (S.append s1 s2) s3));

  ST.pop_frame ()


#push-options "--max_ifuel 1"

noextract inline_for_extraction
let u32_to_len (a: hash_alg) (l: U32.t): l':len_t a { len_v a l' = U32.v l } =
  match a with
  | SHA2_384 | SHA2_512 ->
      FStar.Int.Cast.Full.(uint64_to_uint128 (uint32_to_uint64 l))
  | _ ->
      FStar.Int.Cast.Full.(uint32_to_uint64 l)

#pop-options


(** Complete hash. *)
noextract inline_for_extraction
let mk_hash a alloca update_multi update_last finish input input_len dst =
  let h0 = ST.get () in
  ST.push_frame ();
  let s = alloca () in
  let blocks_n = U32.(input_len /^ block_len a) in
  let blocks_len = U32.(blocks_n *^ block_len a) in
  let blocks = B.sub input 0ul blocks_len in
  let rest_len = U32.(input_len -^ blocks_len) in
  let rest = B.sub input blocks_len rest_len in
  update_multi s blocks blocks_n;
  update_last s (u32_to_len a blocks_len) rest rest_len;
  finish s dst;
  ST.pop_frame ();
  Spec.Hash.Lemmas.hash_is_hash_incremental a (B.as_seq h0 input)
