module Hacl.Hash.MD

(** The Merkle-Damgård construction. *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Int = Lib.IntTypes
module Lemmas = FStar.Math.Lemmas
module B = LowStar.Buffer
module S = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open Hacl.Hash.Definitions
open Hacl.Hash.Lemmas
open Spec.Hash.Definitions
open FStar.Mul
module HI = Spec.Hash.Incremental
module AH = Spec.Agile.Hash

(** Auxiliary helpers *)

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let padding_round (a: md_alg) (len: len_t a): Lemma
  ((len_v a len + pad_length a (len_v a len)) % block_length a = 0)
=
  ()

private
val mod_sub_add: a:int -> b:int -> c:int -> d:int -> p:pos -> Lemma
  (requires b % p = 0)
  (ensures  (a - ((b + c) + d)) % p == (a - (c + d)) % p)
let mod_sub_add a b c d p =
  calc (==) {
    (a - ((b + c) + d)) % p;
    == { Math.Lemmas.lemma_mod_sub_distr a ((b + c) + d) p }
    (a - ((b + c) + d) % p) % p;
    == { Math.Lemmas.lemma_mod_plus_distr_l (b + c) d p }
    (a - ((b + c) % p + d) % p) % p;
    == { Math.Lemmas.lemma_mod_plus_distr_l b c p }
    (a - ((b % p + c) % p + d) % p) % p;
    == { }
    (a - (c % p + d) % p) % p;
    == { Math.Lemmas.lemma_mod_plus_distr_l c d p }
    (a - (c + d) % p) % p;
    == { Math.Lemmas.lemma_mod_sub_distr a (c + d) p }
    (a - (c + d)) % p;
  }

let pad0_length_mod (a: hash_alg{is_md a}) (base_len: nat) (len: nat): Lemma
  (requires base_len % block_length a = 0)
  (ensures  pad0_length a (base_len + len) = pad0_length a len)
=
  mod_sub_add (block_length a) base_len len (len_length a + 1) (block_length a)

let pad_length_mod (a: hash_alg{is_md a}) (base_len len: nat): Lemma
  (requires base_len % block_length a = 0)
  (ensures  pad_length a (base_len + len) = pad_length a len)
= pad0_length_mod a base_len len

val pad_len_bound :
  a : md_alg ->
  prev_len:len_t a { len_v a prev_len % block_length a = 0 } ->
  input_len:U32.t { (U32.v input_len + len_v a prev_len) `less_than_max_input_length` a} ->
  Lemma(
    (U32.v input_len % block_length a) +
      pad_length a (len_v a prev_len + U32.v input_len) <= 2 * block_length a)

let pad_len_bound a prev_len input_len = ()

(* Avoiding an ill-formed pattern error... *)
noextract inline_for_extraction
let len_add32 a prev_len input_len =
  let open FStar.Int.Cast.Full in
  match a with
  | SHA2_224 | SHA2_256 | MD5 | SHA1 | Blake2S ->
      assert_norm (pow2 61 < pow2 64);
      U64.(prev_len +^ uint32_to_uint64 input_len)
  | SHA2_384 | SHA2_512 | Blake2B ->
      assert_norm (pow2 125 < pow2 128);
      U128.(prev_len +^ uint64_to_uint128 (uint32_to_uint64 input_len))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** Iterated compression function. *)
noextract inline_for_extraction
let mk_update_multi a update s () blocks n_blocks =
  let h0 = ST.get () in
  let inv (h: HS.mem) (i: nat) =
    let i_block = i * block_length a in
    i <= U32.v n_blocks /\
    B.live h s /\ B.live h blocks /\
    B.(modifies (loc_buffer s) h0 h) /\
    as_seq h s ==
      Spec.Agile.Hash.update_multi a (as_seq h0 s) () (S.slice (B.as_seq h0 blocks) 0 i_block)
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
    (**) Spec.Hash.Lemmas.update_multi_update a (as_seq h1 s) (B.as_seq h0 block);
    (**) let h2 = ST.get () in
    (**) let blocks_v : Ghost.erased _ = B.as_seq h0 blocks in
    (**) let block_v : Ghost.erased _ = B.as_seq h0 block in
    (**) let blocks0_v : Ghost.erased _ = B.as_seq h0 blocks0 in
    assert (
      let s1 = B.as_seq h1 s in
      let s2 = B.as_seq h2 s in
      let i = U32.v i in
      let n_blocks = U32.v n_blocks in
      block_length a * (i + 1) <= S.length blocks_v /\
      (block_length a * (i + 1) - block_length a * i) % block_length a = 0 /\
      S.equal block_v (S.slice blocks_v (block_length a * i) (block_length a * (i + 1))) /\
      S.equal s2 (Spec.Agile.Hash.update_multi a s1 () block_v)
      );
    (**) let i_block : Ghost.erased _ = block_length a * (U32.v i) in
    (**) Spec.Hash.Lemmas.update_multi_associative a (as_seq h0 s)
                                                   (S.slice blocks_v 0 i_block)
                                                   block_v
  in
  assert (B.length blocks = U32.v n_blocks * block_length a);
  Spec.Hash.Lemmas.update_multi_zero a (as_seq h0 s);
  C.Loops.for 0ul n_blocks inv f

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** An arbitrary number of bytes, then padding. *)
noextract inline_for_extraction
let mk_update_last a update_multi =
  assert_norm(block_length a > 0);
  fun pad s prev_len input input_len ->
  ST.push_frame ();
  let h0 = ST.get () in

  (* Get a series of complete blocks. *)
  let blocks_n = U32.(input_len /^ block_len a) in
  Math.Lemmas.nat_times_nat_is_nat (UInt32.v blocks_n) (block_length a);
  Math.Lemmas.euclidean_division_definition (U32.v input_len) (block_length a);
  let blocks_len = U32.(blocks_n *^ block_len a) in
  Math.Lemmas.cancel_mul_mod (U32.v blocks_n) (block_length a);
  assert (U32.v blocks_len % block_length a = 0);
  let blocks = B.sub input 0ul blocks_len in

  (* The rest that doesn't make up a complete block *)
  let rest_len = U32.(input_len -^ blocks_len) in
  assert (U32.v rest_len < block_length a);
  let rest = B.sub input blocks_len rest_len in

  assert(B.length blocks = U32.v blocks_len);
  assert(block_length a * U32.v blocks_n = U32.v blocks_n * block_length a);
  update_multi s () blocks blocks_n;

  let h1 = ST.get () in
  assert (S.equal (B.as_seq h0 input) (S.append (B.as_seq h1 blocks) (B.as_seq h1 rest)));
  assert (S.equal (as_seq h1 s) (Spec.Agile.Hash.update_multi a (B.as_seq h0 s) () (B.as_seq h0 blocks)));

  (* Compute the total number of bytes fed. *)
  let total_input_len: len_t a = len_add32 a prev_len input_len in
  (* Blit the remaining data and the padding together *)
  let pad_len = Hacl.Hash.PadFinish.pad_len a total_input_len in
  let tmp_len = U32.( rest_len +^ pad_len ) in
  assert (len_v a total_input_len = len_v a prev_len + U32.v blocks_len + U32.v rest_len);
  Lemmas.modulo_distributivity (len_v a prev_len) (U32.v blocks_len) (block_length a);

  Math.Lemmas.lemma_mod_plus_distr_r (len_v a prev_len) (U32.v blocks_len) (block_length a);
  assert ((len_v a prev_len + U32.v blocks_len) % block_length a = 0);
  pad_length_mod a (len_v a prev_len + U32.v blocks_len) (U32.v rest_len);
  padding_round a total_input_len;
  assert(FStar.UInt32.v tmp_len % Spec.Hash.Definitions.block_length a = 0);
  assert (U32.v tmp_len % block_length a = 0);

  pad_len_bound a prev_len input_len;
  assert (U32.v tmp_len <= 2 * block_length a);

  let tmp_twoblocks = B.alloca (Lib.IntTypes.u8 0) U32.(2ul *^ block_len a) in
  let tmp = B.sub tmp_twoblocks 0ul tmp_len in
  let tmp_rest = B.sub tmp 0ul rest_len in
  let tmp_pad = B.sub tmp rest_len pad_len in
  B.blit rest 0ul tmp_rest 0ul rest_len;
  pad total_input_len tmp_pad;

  let h2 = ST.get () in
  assert (S.equal (B.as_seq h2 tmp) (S.append (B.as_seq h2 tmp_rest) (B.as_seq h2 tmp_pad)));
  assert (S.equal (B.as_seq h2 tmp_rest) (B.as_seq h1 rest));
  assert (S.equal (B.as_seq h2 tmp_pad) (Spec.Hash.MD.pad a (len_v a total_input_len)));

  (* Update multi those last few blocks *)
  Math.Lemmas.cancel_mul_mod (U32.v tmp_len) (block_length a);
  Math.Lemmas.euclidean_division_definition (U32.v tmp_len) (block_length a);
  Math.Lemmas.swap_mul (block_length a) (U32.v U32.(tmp_len /^ block_len a));
  assert(B.length tmp = block_length a * U32.v U32.(tmp_len /^ block_len a));

  update_multi s () tmp U32.(tmp_len /^ block_len a);

  let h3 = ST.get () in
  assert (S.equal (B.as_seq h3 s)
    (Spec.Agile.Hash.update_multi a (Spec.Agile.Hash.update_multi a (B.as_seq h0 s) () (B.as_seq h1 blocks)) ()
      (S.append (B.as_seq h1 rest) (Spec.Hash.MD.pad a (len_v a total_input_len)))));
  assert (
    let s1 = B.as_seq h1 blocks in
    let s2 = B.as_seq h2 rest in
    let s3 = Spec.Hash.MD.pad a (len_v a total_input_len) in
    S.equal (S.append s1 (S.append s2 s3)) (S.append (S.append s1 s2) s3));

  Spec.Hash.Lemmas.update_multi_associative a
    (B.as_seq h0 s)
    (B.as_seq h1 blocks)
    (S.append (B.as_seq h1 rest) (Spec.Hash.MD.pad a (len_v a total_input_len)));

  ST.pop_frame ()

#pop-options

#push-options "--ifuel 1"

noextract inline_for_extraction
let u32_to_len (a: hash_alg{is_md a}) (l: U32.t): l':len_t a { len_v a l' = U32.v l } =
  match a with
  | SHA2_384 | SHA2_512 ->
    FStar.Int.Cast.Full.(uint64_to_uint128 (uint32_to_uint64 l))
  | _ -> FStar.Int.Cast.Full.uint32_to_uint64 l

#pop-options

(** split blocks: utility for the complete hash *)
noextract inline_for_extraction
val split_blocks (a : hash_alg) (input:B.buffer Int.uint8)
                 (input_len : Int.size_t { B.length input = U32.v input_len }) :
  ST.Stack (Int.size_t & Int.size_t & B.buffer Int.uint8 & Int.size_t & B.buffer Int.uint8)
  (requires fun h -> B.live h input /\ B.length input `less_than_max_input_length` a)
  (ensures fun h0 (blocks_n, blocks_len, blocks, rest_len, rest) h1 ->
           h0 == h1 /\
           U32.v blocks_len + U32.v rest_len == U32.v input_len /\
           B.length blocks == U32.v blocks_len /\ B.length rest == U32.v rest_len /\
           B.as_seq h0 input `S.equal` S.append (B.as_seq h0 blocks) (B.as_seq h0 rest) /\
           blocks == Ghost.reveal(B.gsub input 0ul blocks_len) /\
           rest == B.gsub input blocks_len rest_len /\
           (B.as_seq h0 blocks, B.as_seq h0 rest) ==
             Spec.Hash.Incremental.split_blocks a (B.as_seq h0 input) /\
           U32.v blocks_len == U32.v blocks_n * block_length a)

#push-options "--ifuel 1"
let split_blocks a input input_len =
  let blocks_n = U32.(input_len /^ block_len a) in
  let blocks_n = if U32.(input_len %^ block_len a =^ uint_to_t 0) && U32.(blocks_n >^ uint_to_t 0)
                 then U32.(blocks_n -^ uint_to_t 1) else blocks_n in
  let blocks_len = U32.(blocks_n *^ block_len a) in
  let blocks = B.sub input 0ul blocks_len in
  let rest_len = U32.(input_len -^ blocks_len) in
  let rest = B.sub input blocks_len rest_len in
  (blocks_n, blocks_len, blocks, rest_len, rest)
#pop-options

(** Complete hash. *)

/// We need to friend Spec.Agile.Hash to expose the definition of hash
friend Spec.Agile.Hash

#push-options "--ifuel 0 --fuel 0 --z3rlimit 200"
noextract inline_for_extraction
let mk_hash a alloca update_multi update_last finish input input_len dst =
  (**) let h0 = ST.get () in
  ST.push_frame ();
  let s = alloca () in
  let (blocks_n, blocks_len, blocks, rest_len, rest) = split_blocks a input input_len in

  (**) let blocks_v0 : Ghost.erased _ = B.as_seq h0 blocks in
  (**) let rest_v0 : Ghost.erased _ = B.as_seq h0 rest in
  (**) let input_v0 : Ghost.erased _ = B.as_seq h0 input in
  (**) assert(input_v0 `S.equal` S.append blocks_v0 rest_v0);
  update_multi s () blocks blocks_n;

  // AF: Most of these assertions are not needed, but they are good to document
  // the current state of the proof
  (**) let h01 = ST.get () in
  (**) assert (as_seq h01 s == Spec.Agile.Hash.(update_multi a (init a) () blocks_v0));

  update_last s (u32_to_len a blocks_len) rest rest_len;
  (**) let h02 = ST.get () in
  (**) assert (as_seq h02 s == Spec.Agile.Hash.(Spec.Hash.Incremental.update_last a (update_multi a (init a) () blocks_v0) (S.length blocks_v0) rest_v0));

  (**) let padding: Ghost.erased _ = Spec.Hash.MD.pad a (S.length input_v0) in
  // We need to prove that rest_v0 @| padding is a block. We do this using the calc below
  calc (==) {
    S.(length (rest_v0 @| padding)) % block_length a;
    (==) { }
    S.(length rest_v0 + S.length padding) % block_length a;
    (==) { Math.Lemmas.lemma_mod_add_distr (S.length padding) (S.length rest_v0) (block_length a) }
    S.(length rest_v0 % block_length a + S.length padding) % block_length a;
    (==) { }
    S.(length input_v0 % block_length a + S.length padding) % block_length a;
    (==) { Math.Lemmas.lemma_mod_add_distr (S.length padding) (S.length input_v0) (block_length a) }
    S.(length input_v0 + S.length padding) % block_length a;
    (==) { }
    0;
  };
  (**) assert (as_seq h02 s == Spec.Agile.Hash.(update_multi a
    (update_multi a (init a) () blocks_v0) () (rest_v0 `S.append` padding)));
  (**) assert ((blocks_v0 `S.append` (rest_v0 `S.append` padding)) `S.equal` (input_v0 `S.append` padding));
  (**) Spec.Hash.Lemmas.update_multi_associative a (Spec.Agile.Hash.init a) (blocks_v0) (rest_v0 `S.append` padding);
  (**) assert (as_seq h02 s == Spec.Agile.Hash.(update_multi a (init a) () (input_v0 `S.append` padding)));

finish s dst;
  (**) let h03 = ST.get () in
  (**) assert (B.as_seq h03 dst == Spec.Agile.Hash.hash a input_v0);

  ST.pop_frame ()
