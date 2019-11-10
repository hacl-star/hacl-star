module Hacl.HMAC_DRBG

open FStar.HyperStack.ST

open Spec.Hash.Definitions

open Lib.IntTypes
open Lib.Buffer

module HS = FStar.HyperStack
module B = LowStar.Buffer
module LSeq = Lib.Sequence

module HMAC = Hacl.HMAC
module S = Spec.HMAC_DRBG

friend Spec.HMAC_DRBG

unfold
let hash_len (a:supported_alg) = Hacl.Hash.Definitions.hash_len a

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

inline_for_extraction noextract
val update_round: #a:supported_alg
  -> hmac:HMAC.compute_st a
  -> len:size_t
  -> data:lbuffer uint8 len
  -> n:uint8
  -> k:lbuffer uint8 (hash_len a)
  -> v:lbuffer uint8 (hash_len a)
  -> Stack unit
  (requires fun h0 ->
    live h0 k /\ live h0 v /\ live h0 data /\
    disjoint k v /\
    // HMAC input length must fit in size_t
    hash_length a + 1 + uint_v len + block_length a < pow2 32)
  (ensures  fun h0 _ h1 ->
    S.hmac_input_bound a;
    as_seq h1 k == Spec.Agile.HMAC.hmac a
      (as_seq h0 k)
      (Seq.append (as_seq h0 v) (Seq.cons n (as_seq h0 data))) /\
    as_seq h1 v == Spec.Agile.HMAC.hmac a (as_seq h1 k) (as_seq h0 v) /\
    modifies2 k v h0 h1)

let update_round #a hmac len data n k v =
  let h0 = get() in
  push_frame();
  let input_len = hash_len a +! 1ul +! len in
  let input = create input_len (u8 0) in
  let k' = sub input 0ul (hash_len a) in
  copy k' v;
  if len <> 0ul then copy (sub input (hash_len a +! 1ul) len) data;
  input.(hash_len a) <- n;
  let h1 = get() in
  assert (Seq.equal (as_seq h1 input)
                    (Seq.append (as_seq h0 v) (Seq.cons n (as_seq h0 data))));
  S.hmac_input_bound a;
  hmac k' k (hash_len a) input input_len;
  hmac v k' (hash_len a) v (hash_len a);
  copy k k';
  pop_frame()


inline_for_extraction noextract
val update: #a:supported_alg
  -> hmac:HMAC.compute_st a
  -> len:size_t
  -> data:lbuffer uint8 len
  -> k:lbuffer uint8 (hash_len a)
  -> v:lbuffer uint8 (hash_len a)
  -> Stack unit
  (requires fun h0 ->
    live h0 data /\ live h0 k /\ live h0 v /\
    disjoint k v /\ disjoint k data /\ disjoint v data /\
    hash_length a + 1 + uint_v len + block_length a < pow2 32)
  (ensures  fun h0 _ h1 ->
    S.hmac_input_bound a;
    let k', v' = S.update #a (as_seq h0 data) (as_seq h0 k) (as_seq h0 v) in
    modifies2 k v h0 h1 /\
    as_seq h1 k == k' /\
    as_seq h1 v == v')

let update #a hmac len data k v  =
  update_round hmac len data (u8 0) k v;
  if len <> 0ul then
    update_round hmac len data (u8 1) k v


noeq
type state (a:supported_alg) =
| State:
    k:lbuffer uint8 (hash_len a)
  -> v:lbuffer uint8 (hash_len a)
  -> reseed_counter:lbuffer size_t 1ul
    {disjoint k v /\ disjoint k reseed_counter /\ disjoint v reseed_counter}
  -> state a

let freeable #a st =
  let k:B.buffer uint8 = st.k in
  let v:B.buffer uint8 = st.v in
  let ctr:B.buffer size_t = st.reseed_counter in
  B.freeable k /\ B.freeable v /\ B.freeable ctr

let footprint #a st =
  let k:B.buffer uint8 = st.k in
  let v:B.buffer uint8 = st.v in
  let ctr:B.buffer size_t = st.reseed_counter in
  B.loc_addr_of_buffer k |+| B.loc_addr_of_buffer v |+| B.loc_addr_of_buffer ctr

let invariant #a st h =
  live h st.k /\ live h st.v /\ live h st.reseed_counter

let repr #a st h =
  S.State (as_seq h st.k) (as_seq h st.v) (v (bget h st.reseed_counter 0))

let alloca a =
  let k =
    match a with
    | SHA1     -> create (hash_len SHA1)     (u8 0)
    | SHA2_256 -> create (hash_len SHA2_256) (u8 0)
    | SHA2_384 -> create (hash_len SHA2_384) (u8 0)
    | SHA2_512 -> create (hash_len SHA2_512) (u8 0)
  in
  let v =
    match a with
    | SHA1     -> create (hash_len SHA1)     (u8 0)
    | SHA2_256 -> create (hash_len SHA2_256) (u8 0)
    | SHA2_384 -> create (hash_len SHA2_384) (u8 0)
    | SHA2_512 -> create (hash_len SHA2_512) (u8 0)
  in
  let ctr = create 1ul 1ul in
  State k v ctr

let create_in a r =
  let k:B.buffer uint8 =
    match a with
    | SHA1     -> B.malloc r (u8 0) (hash_len SHA1)
    | SHA2_256 -> B.malloc r (u8 0) (hash_len SHA2_256)
    | SHA2_384 -> B.malloc r (u8 0) (hash_len SHA2_384)
    | SHA2_512 -> B.malloc r (u8 0) (hash_len SHA2_512)
  in
  let v:B.buffer uint8 =
    match a with
    | SHA1     -> B.malloc r (u8 0) (hash_len SHA1)
    | SHA2_256 -> B.malloc r (u8 0) (hash_len SHA2_256)
    | SHA2_384 -> B.malloc r (u8 0) (hash_len SHA2_384)
    | SHA2_512 -> B.malloc r (u8 0) (hash_len SHA2_512)
  in
  let ctr:B.buffer size_t = B.malloc r 1ul 1ul in
  State k v ctr

#push-options "--z3rlimit 200"

let mk_instantiate #a hmac st
  entropy_input_len entropy_input
  nonce_len nonce
  personalization_string_len personalization_string
=
  let h0 = get () in
  push_frame();
  let seed_material = create (entropy_input_len +! nonce_len +! personalization_string_len) (u8 0) in
  copy (sub seed_material 0ul entropy_input_len) entropy_input;
  copy (sub seed_material entropy_input_len nonce_len) nonce;
  copy (sub seed_material (entropy_input_len +! nonce_len) personalization_string_len) personalization_string;
  let State k v ctr = st in
  memset k (u8 0) (hash_len a);
  memset v (u8 1) (hash_len a);
  let h1 = get () in
  assert (Seq.equal (as_seq h1 seed_material)
    (Seq.append (as_seq h0 entropy_input) (Seq.append (as_seq h0 nonce)
      (as_seq h0 personalization_string))));
  assert (LSeq.equal (as_seq h1 k) (LSeq.create (hash_length a) (u8 0)));
  assert (LSeq.equal (as_seq h1 v) (LSeq.create (hash_length a) (u8 1)));
  ctr.(0ul) <- 1ul;
  update hmac (entropy_input_len +! nonce_len +! personalization_string_len)
    seed_material k v;
  pop_frame()

#pop-options

let instantiate a st
  entropy_input_len entropy_input
  nonce_len nonce
  personalization_string_len personalization_string
=
  match a with
  | SHA1     ->
    mk_instantiate Hacl.HMAC.legacy_compute_sha1 st
      entropy_input_len entropy_input
      nonce_len nonce
      personalization_string_len personalization_string
  | SHA2_256 ->
    mk_instantiate Hacl.HMAC.compute_sha2_256 st
      entropy_input_len entropy_input
      nonce_len nonce
      personalization_string_len personalization_string
  | SHA2_384 ->
    mk_instantiate Hacl.HMAC.compute_sha2_384 st
      entropy_input_len entropy_input
      nonce_len nonce
      personalization_string_len personalization_string
  | SHA2_512 ->
    mk_instantiate Hacl.HMAC.compute_sha2_512 st
      entropy_input_len entropy_input
      nonce_len nonce
      personalization_string_len personalization_string


let mk_reseed #a hmac st
  entropy_input_len entropy_input
  additional_input_len additional_input
=
  let h0 = get () in
  push_frame();
  let seed_material = create (entropy_input_len +! additional_input_len) (u8 0) in
  copy (sub seed_material 0ul entropy_input_len) entropy_input;
  copy (sub seed_material entropy_input_len additional_input_len) additional_input;
  let h1 = get () in
  LSeq.eq_intro (as_seq h1 seed_material)
                LSeq.(as_seq h0 entropy_input @| as_seq h0 additional_input);
  let State k v ctr: state a = st in
  update hmac (entropy_input_len +! additional_input_len) seed_material k v;
  ctr.(0ul) <- 1ul;
  pop_frame()


let reseed a st
  entropy_input_len entropy_input
  additional_input_input_len additional_input_input =
  match a with
  | SHA1 ->
    mk_reseed Hacl.HMAC.legacy_compute_sha1 st
      entropy_input_len entropy_input
      additional_input_input_len additional_input_input
  | SHA2_256 ->
    mk_reseed Hacl.HMAC.compute_sha2_256 st
      entropy_input_len entropy_input
      additional_input_input_len additional_input_input
  | SHA2_384 ->
    mk_reseed Hacl.HMAC.compute_sha2_384 st
      entropy_input_len entropy_input
      additional_input_input_len additional_input_input
  | SHA2_512 ->
    mk_reseed Hacl.HMAC.compute_sha2_512 st
      entropy_input_len entropy_input
      additional_input_input_len additional_input_input

#push-options "--z3rlimit 300"

let mk_generate #a hmac output st n additional_input_len additional_input =
  if st.reseed_counter.(0ul) >. reseed_interval then
    false
  else
    begin
    S.hmac_input_bound a;
    Math.Lemmas.lemma_div_mod (v n) (hash_length a);
    let State k v ctr = st in
    if additional_input_len >. 0ul then
      update hmac additional_input_len additional_input k v;
    let output:lbuffer uint8 n = output in
    let max = n /. hash_len a in
    let out = sub output 0ul (max *! hash_len a) in
    [@inline_let]
    let a_spec = S.a_spec a in
    [@inline_let]
    let refl h i = as_seq h v in
    [@inline_let]
    let spec h0 = S.generate_loop a (as_seq h0 k) (uint_v max) in
    let h0 = get () in
    fill_blocks h0 (hash_len a) max out a_spec refl (fun i -> loc v) spec
      (fun i ->
        LSeq.unfold_generate_blocks
          (hash_length a) (uint_v max) a_spec (spec h0) (as_seq h0 v) (uint_v i);
        hmac v k (hash_len a) v (hash_len a);
        copy (sub out (i *! hash_len a) (hash_len a)) v
      );
    if max *! hash_len a <. n then
      begin
      let h1 = get () in
      let block = sub output (max *! hash_len a) (n -! (max *! hash_len a)) in
      hmac v k (hash_len a) v (hash_len a);
      copy block (sub v 0ul (n -! (max *! hash_len a)));
      let h2 = get () in
      LSeq.eq_intro (as_seq h2 output)
                    (as_seq h1 out `LSeq.op_At_Bar` as_seq h2 block)
      end;
    update hmac additional_input_len additional_input k v;
    let old_ctr = ctr.(0ul) in
    ctr.(0ul) <- old_ctr +! 1ul;
    true
    end

#pop-options

let generate a output st n additional_input_len additional_input =
  match a with
  | SHA1     ->
    mk_generate Hacl.HMAC.legacy_compute_sha1 output st n
      additional_input_len additional_input
  | SHA2_256 ->
    mk_generate Hacl.HMAC.compute_sha2_256 output st n
      additional_input_len additional_input
  | SHA2_384 ->
    mk_generate Hacl.HMAC.compute_sha2_384 output st n
      additional_input_len additional_input
  | SHA2_512 ->
    mk_generate Hacl.HMAC.compute_sha2_512 output st n
      additional_input_len additional_input
