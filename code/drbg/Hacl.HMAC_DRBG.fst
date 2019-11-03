module Hacl.HMAC_DRBG

open FStar.HyperStack.ST

open Spec.Hash.Definitions

open Lib.IntTypes
open Lib.Buffer

module HS = FStar.HyperStack
module B = LowStar.Buffer

module HMAC = Hacl.HMAC
module S = Spec.HMAC_DRBG
module D = Hacl.Hash.Definitions
module LSeq = Lib.Sequence

/// HMAC-DRBG
///
/// See 10.1.2 and B.2 of
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
///
/// This module implements the hash-algorithm-agile algorithms
/// - HMAC_DRBG_Update
/// - HMAC_DRBG_Instantiate_algorithm
/// - HMAC_DRBG_Reseed_algorithm
/// - HMAC_DRBG_Generate_algorithm
///
/// This is not linked to an appropriate Get_entropy_input function,
/// so these algorithms should be combined to get entropy from Get_entropy_input
/// for instantiation, reseeding, and optionally prediction resistance.
/// 
/// - Supports SHA-1, SHA2-256, SHA2-384 and SHA2-512 hash algorithms
///
/// - Supports reseeding
/// 
/// - Supports optional personalization_string for instantiation
/// 
/// - Does not support optional additional_input for reseeding or generation
///
/// - The internal state is (Key,V,reseed_counter)
///
/// - The security_strength is fixed to the HMAC-strength of the hash algorithm
///   as per p.54 of
///   https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-57pt1r4.pdf
///
/// - The minimum entropy for instantiation is 3/2 * security_strength.
///    - entropy_input must have at least security_strength bits.
///    - nonce must have at least 1/2 security_strength bits.
///    - entropy_input and nonce can have at most max_length = 2^16 bits.
///
/// - At most max_number_of_bits_per_request = 2^16 bits can be generated per request.
///
/// - The reseed_interval is 2^48
///
#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 50"

unfold
let supported_alg = S.supported_alg

let reseed_interval: n:pub_uint64{v n == S.reseed_interval} = 
  assert_norm (S.reseed_interval < pow2 64);
  normalize_term (mk_int S.reseed_interval)

let max_output_length: n:size_t{v n == S.max_output_length} = 
  assert_norm (S.max_output_length < pow2 32);
  normalize_term (mk_int S.max_output_length)

let max_length: n:size_t{v n == S.max_length} = 
  assert_norm (S.max_length < pow2 32);
  normalize_term (mk_int S.max_length)

let max_personalization_string_length: n:size_t{v n == S.max_personalization_string_length} = 
  assert_norm (S.max_personalization_string_length < pow2 32);
  normalize_term (mk_int S.max_personalization_string_length)

let max_additional_input_length: n:size_t{v n == S.max_additional_input_length} = 
  assert_norm (S.max_additional_input_length < pow2 32);
  normalize_term (mk_int S.max_additional_input_length)

let min_length (a:supported_alg) : n:size_t{v n == S.min_length a} =
  assert_norm (S.min_length a < pow2 32);
  match a with
  | SHA1 -> normalize_term (mk_int (S.min_length SHA1))
  | SHA2_256 | SHA2_384 | SHA2_512 -> normalize_term (mk_int (S.min_length SHA2_256))

noeq
type state (a:hash_alg) =
| State: 
    k:lbuffer uint8 (D.hash_len a)
  -> v:lbuffer uint8 (D.hash_len a)
  -> reseed_counter:lbuffer pub_uint64 1ul
    {disjoint k v /\ disjoint k reseed_counter /\ disjoint v reseed_counter}
  -> state a

let live_st (#a:hash_alg) (h:HS.mem) (st:state a) =
  let State k v ctr = st in live h k /\ live h v /\ live h ctr

inline_for_extraction noextract
val update_round: #a:supported_alg 
  -> hmac:HMAC.compute_st a
  -> len:size_t 
  -> data:lbuffer uint8 len
  -> n:uint8
  -> k:lbuffer uint8 (D.hash_len a)
  -> v:lbuffer uint8 (D.hash_len a)
  -> ST unit
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
  let input_len = D.hash_len a +! 1ul +! len in
  let input = create input_len (u8 0) in
  let k' = sub input 0ul (D.hash_len a) in
  copy k' v;
  if len <> 0ul then copy (sub input (D.hash_len a +! 1ul) len) data;
  input.(D.hash_len a) <- n;
  let h1 = get() in
  assert (Seq.equal (as_seq h1 input)  
                    (Seq.append (as_seq h0 v) (Seq.cons n (as_seq h0 data))));
  S.hmac_input_bound a;
  hmac k' k (D.hash_len a) input input_len;
  hmac v k' (D.hash_len a) v (D.hash_len a);
  copy k k';
  pop_frame()

inline_for_extraction noextract
val update: #a:supported_alg 
  -> hmac:HMAC.compute_st a
  -> len:size_t 
  -> data:lbuffer uint8 len
  -> k:lbuffer uint8 (D.hash_len a)
  -> v:lbuffer uint8 (D.hash_len a)
  -> ST unit
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

inline_for_extraction
let instantiate_st (a:supported_alg) =
    st:state a 
  -> entropy_input_len:size_t
  -> entropy_input:lbuffer uint8 entropy_input_len
  -> nonce_len:size_t
  -> nonce:lbuffer uint8 nonce_len
  -> personalization_string_len:size_t
  -> personalization_string:lbuffer uint8 personalization_string_len
  -> ST unit
  (requires fun h0 -> 
    live h0 entropy_input /\ live h0 nonce /\ live h0 personalization_string /\
    live_st h0 st /\
    S.min_length a <= v entropy_input_len /\ v entropy_input_len <= v max_length /\
    S.min_length a / 2 <= v nonce_len /\ v nonce_len <= v max_length /\
    v personalization_string_len <= S.max_personalization_string_length)
  (ensures  fun h0 _ h1 ->
    S.hmac_input_bound a;
    let S.State k v ctr =
      S.instantiate #a (as_seq h0 entropy_input) (as_seq h0 nonce) 
        (as_seq h0 personalization_string)
    in    
    modifies3 st.k st.v st.reseed_counter h0 h1 /\
    as_seq h1 st.k == k /\
    as_seq h1 st.v == v /\
    uint_v (bget h1 st.reseed_counter 0) == ctr)

#push-options "--z3rlimit 200"

inline_for_extraction noextract
val mk_instantiate: #a:supported_alg -> hmac:HMAC.compute_st a -> instantiate_st a
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
  fillT (D.hash_len a) k (fun _ -> u8 0) (fun _ -> u8 0);
  fillT (D.hash_len a) v (fun _ -> u8 1) (fun _ -> u8 1);
  let h1 = get () in
  assert (Seq.equal (as_seq h1 seed_material) 
    (Seq.append (as_seq h0 entropy_input) (Seq.append (as_seq h0 nonce)
      (as_seq h0 personalization_string))));
  assert (LSeq.equal (as_seq h1 k) (LSeq.create (hash_length a) (u8 0)));
  assert (LSeq.equal (as_seq h1 v) (LSeq.create (hash_length a) (u8 1)));
  ctr.(0ul) <- 1uL;
  update hmac (entropy_input_len +! nonce_len +! personalization_string_len) 
    seed_material st.k st.v;
  pop_frame()

#pop-options

val instantiate (a:supported_alg) : instantiate_st a
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


inline_for_extraction
let reseed_st (a:supported_alg) =
    st:state a 
  -> entropy_input_len:size_t
  -> entropy_input:lbuffer uint8 entropy_input_len
  -> additional_input_len:size_t
  -> additional_input:lbuffer uint8 additional_input_len
  -> ST unit
  (requires fun h0 ->
    live_st h0 st /\ live h0 entropy_input /\ live h0 additional_input /\
    disjoint st.k entropy_input /\ disjoint st.v entropy_input /\ 
    disjoint st.reseed_counter entropy_input /\
    disjoint st.k additional_input /\ disjoint st.v additional_input /\ 
    disjoint st.reseed_counter additional_input /\
    S.min_length a <= v entropy_input_len /\ v entropy_input_len <= v max_length /\
    v additional_input_len <= S.max_additional_input_length)
  (ensures  fun h0 _ h1 ->
    S.hmac_input_bound a;
    let S.State k v ctr = 
      S.reseed #a 
        (S.State (as_seq h0 st.k) (as_seq h0 st.v) (v (bget h0 st.reseed_counter 0)))
        (as_seq h0 entropy_input)
        (as_seq h0 additional_input)
    in
    modifies3 st.k st.v st.reseed_counter h0 h1 /\
    as_seq h1 st.k == k /\
    as_seq h1 st.v == v /\
    bget h1 st.reseed_counter 0 == 1uL)

inline_for_extraction noextract
val mk_reseed: #a:supported_alg -> hmac:HMAC.compute_st a -> reseed_st a
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
  update hmac (entropy_input_len +! additional_input_len) seed_material st.k st.v;
  st.reseed_counter.(0ul) <- 1uL;
  pop_frame()

val reseed (a:supported_alg) : reseed_st a
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


inline_for_extraction
let generate_st (a:supported_alg) =
    output:buffer uint8
  -> st:state a 
  -> n:size_t
  -> additional_input_len:size_t
  -> additional_input:lbuffer uint8 additional_input_len
  -> ST bool
  (requires fun h0 ->
    live h0 output /\ live_st h0 st /\ live h0 additional_input /\
    disjoint st.v output /\ disjoint st.k output /\ disjoint st.reseed_counter output /\ disjoint additional_input output /\
    disjoint st.v additional_input /\ disjoint st.k additional_input /\ disjoint st.reseed_counter additional_input /\
    v n = length output /\ 
    0 < v n /\ v n <= S.max_output_length /\
    v additional_input_len <= S.max_additional_input_length)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    let st_ = 
      S.State (as_seq h0 st.k) (as_seq h0 st.v) (uint_v (bget h0 st.reseed_counter 0)) 
    in
    match S.generate #a st_ (v n) (as_seq h0 additional_input) with
    | None -> b = false /\ modifies0 h0 h1
    | Some (out, S.State k v ctr) ->
      b = true /\
      modifies4 output st.k st.v st.reseed_counter h0 h1 /\
      as_seq #MUT #_ #n h1 output == out /\
      as_seq h1 st.k == k /\
      as_seq h1 st.v == v /\
      uint_v (bget h1 st.reseed_counter 0) == ctr)

#push-options "--z3rlimit 200"

inline_for_extraction noextract
val mk_generate: #a:supported_alg -> hmac:HMAC.compute_st a -> generate_st a
let mk_generate #a hmac output st n additional_input_len additional_input =
  if st.reseed_counter.(0ul) >. reseed_interval then
    false
  else
    begin
    S.hmac_input_bound a;
    Math.Lemmas.lemma_div_mod (v n) (hash_length a);
    if additional_input_len >. 0ul then
      update hmac additional_input_len additional_input st.k st.v;
    let output:lbuffer uint8 n = output in
    let max = n /. D.hash_len a in
    let out = sub output 0ul (max *! D.hash_len a) in
    [@inline_let]
    let a_spec = S.a_spec a in
    [@inline_let]
    let refl h i = as_seq h st.v in
    [@inline_let]
    let spec h0 = S.generate_loop a (as_seq h0 st.k) (v max) in
    let h0 = get () in
    fill_blocks h0 (D.hash_len a) max out a_spec refl (fun i -> loc st.v) spec 
      (fun i ->
        LSeq.unfold_generate_blocks 
          (hash_length a) (v max) a_spec (spec h0) (as_seq h0 st.v) (v i);
        hmac st.v st.k (D.hash_len a) st.v (D.hash_len a); 
        copy (sub out (i *! D.hash_len a) (D.hash_len a)) st.v
      );
    if max *! D.hash_len a <. n then
      begin
      let h1 = get () in
      let block = sub output (max *! D.hash_len a) (n -! (max *! D.hash_len a)) in
      hmac st.v st.k (D.hash_len a) st.v (D.hash_len a);      
      copy block (sub st.v 0ul (n -! (max *! D.hash_len a)));
      let h2 = get () in
      LSeq.eq_intro (as_seq h2 output) 
                    (as_seq h1 out `LSeq.op_At_Bar` as_seq h2 block)
      end;
    update hmac additional_input_len additional_input st.k st.v;
    let ctr = st.reseed_counter.(0ul) in
    st.reseed_counter.(0ul) <- ctr +! 1uL;
    true
    end

#pop-options

val generate (a:supported_alg) : generate_st a
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


inline_for_extraction noextract
val alloca_state: a:supported_alg -> StackInline (state a) 
  (requires fun _ -> True)
  (ensures  fun h0 st h1 -> 
    live_st h1 st /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (loc st.k |+| loc st.v |+| loc st.reseed_counter) h0 h1)
let alloca_state a =
  let k = 
    match a with
    | SHA1     -> create (D.hash_len SHA1)     (u8 0)
    | SHA2_256 -> create (D.hash_len SHA2_256) (u8 0)
    | SHA2_384 -> create (D.hash_len SHA2_384) (u8 0)
    | SHA2_512 -> create (D.hash_len SHA2_512) (u8 0)
  in
  let v = 
    match a with
    | SHA1     -> create (D.hash_len SHA1)     (u8 0)
    | SHA2_256 -> create (D.hash_len SHA2_256) (u8 0)
    | SHA2_384 -> create (D.hash_len SHA2_384) (u8 0)
    | SHA2_512 -> create (D.hash_len SHA2_512) (u8 0)
  in
  let ctr = create 1ul 1uL in
  State k v ctr
