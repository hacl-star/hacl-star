module Hacl.HKDF

open FStar.Seq

module B = LowStar.Buffer

open Spec.Hash.Definitions
open Spec.Agile.HKDF

open FStar.HyperStack.ST

open FStar.Mul
open FStar.Integers
open FStar.HyperStack
open Lib.IntTypes
open LowStar.Buffer
open LowStar.BufferOps

friend Spec.Agile.HKDF
friend Lib.IntTypes

// TODO: proofs break mysteriously when not befriending Lib.IntTypes and
// declassifying uint8; investigate
// assume val declassify8: squash (uint8 == UInt8.t)    

module ST = FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 20"

let mk_extract a hmac prk salt saltlen ikm ikmlen =
  hmac prk salt saltlen ikm ikmlen

// [hashed] holds the HMAC text, of the form | hash_len a | infolen | 1 |
// Its prefix is overwritten by HMAC at each iteration.
inline_for_extraction
val hkdf_expand_loop (a:hash_alg) :
  hmac:HMAC.compute_st a ->
  okm     : B.buffer uint8 ->
  prk     : B.buffer uint8 ->
  prklen  : pub_uint32 ->
  infolen : pub_uint32 ->
  len     : pub_uint32 ->
  hashed  : B.buffer uint8 ->
  i       : uint8 ->
  Stack unit
  (requires fun h0 ->
    B.live h0 okm /\ B.live h0 prk /\ B.live h0 hashed /\
    B.disjoint okm prk /\ B.disjoint hashed okm /\ B.disjoint hashed prk /\
    v prklen == B.length prk /\
    v len == B.length okm /\
    B.length hashed == hash_length a + v infolen + 1 /\
    Spec.Agile.HMAC.keysized a (B.length prk) /\    
    hash_length a + v infolen + 1 + block_length a < pow2 32 /\ (* specific to this implementation *)
    hash_length a + pow2 32 + block_length a <= max_input_length a + 1 /\
    v i < 255 /\
    v len <= (255 - Lib.IntTypes.v i) * hash_length a)
  (ensures  fun h0 r h1 ->
    let prk  = B.as_seq h0 prk in
    let info = B.as_seq h0 (B.gsub hashed (Hacl.Hash.Definitions.hash_len a) infolen) in
    let last = if v i = 0 then Seq.empty else B.as_seq h0 (B.gsub hashed 0ul (Hacl.Hash.Definitions.hash_len a)) in
    B.modifies (B.loc_union (B.loc_buffer okm) (B.loc_buffer hashed)) h0 h1 /\
    B.as_seq h1 okm == expand0 a prk info (v len) (v i) last)

#set-options "--max_fuel 1 --max_ifuel 0 --z3rlimit 100"

// TODO: Rewrite as a loop
let rec hkdf_expand_loop a hmac okm prk prklen infolen len hashed i =
  push_frame ();

  let tlen = Hacl.Hash.Definitions.hash_len a in
  let tag = B.sub hashed 0ul tlen in
  let info_counter = offset hashed tlen in
  let info = B.sub info_counter 0ul infolen in
  let counter = offset info_counter infolen in
  assert (disjoint tag info /\ disjoint tag counter /\ disjoint info counter);

  let h0 = ST.get() in  // initial state
  let i' = i +! (u8 1) in
  counter.(0ul) <- i';
  let h1 = ST.get() in // before hashing
  Seq.lemma_eq_intro (as_seq h1 counter) (Seq.create 1 i');

  // derive an extra hash tag
  if i = 0uy then
    begin
    let len1 = infolen + 1ul in
    // the first input is shorter, does not include the chaining block
    hmac tag prk prklen info_counter len1;
    let h2 = ST.get() in
    let info = as_seq h0 info in
    let ctr1 = as_seq h1 counter in
    let prk  = as_seq h0 prk in
    let tag2 = as_seq h2 tag in
    let text = empty @| info @| ctr1 in
    // Seq.lemma_eq_intro (as_seq h1 counter) ctr1;
    // assert(tag2 == HMAC.hmac a v_prk (as_seq h1 hashed1));
    Seq.lemma_eq_intro (as_seq h1 info_counter) text;
    assert (tag2 == Spec.Agile.HMAC.hmac a prk text)
    end
  else
    begin
    hmac tag prk prklen hashed (tlen + infolen + 1ul);
    let h2 = ST.get() in
    let info = as_seq h0 info in
    let ctr1 = as_seq h1 counter in
    let prk  = as_seq h0 prk in
    let tag1 = as_seq h1 tag in
    let tag2 = as_seq h2 tag in
    let text = tag1 @| info @| ctr1 in
    // assert(tag2 == HMAC.hmac (Ghost.hide a) prk (as_seq h1 hashed));
    Seq.lemma_eq_intro (as_seq h1 hashed) text ;
    assert (tag2 == Spec.Agile.HMAC.hmac a prk text)
    end;

  // copy it to the result; iterate if required
  let h2 = ST.get() in
  if len <= tlen then
    begin
    blit tag 0ul okm 0ul len;
    let h3 = ST.get() in
    let prk  = as_seq h0 prk in
    let info = as_seq h0 info in
    let last = if i = 0uy then Seq.empty else as_seq h1 tag in
    let text = last @| info @| Seq.create 1 i' in
    let tag2 = as_seq h2 tag in
    let result = Seq.slice (as_seq h3 okm) 0 (v len) in
    // assert(tag2 == HMAC.hmac (Ghost.hide a) prk text);
    assert(result == Seq.slice tag2 0 (v len));
    assert(result == expand0 a prk info (v len) (v i) last)
    end
  else 
    begin
    blit tag 0ul okm 0ul tlen;
    let h3 = ST.get() in
    let len' = len -! tlen in
    let okm_tag = sub okm 0ul tlen in
    let okm' = offset okm tlen in
    hkdf_expand_loop a hmac okm' prk prklen infolen len' hashed i';
    assert(disjoint okm_tag okm');
    let h4 = ST.get() in
    let info = as_seq h0 info in
    let prk  = as_seq h0 prk in
    let last = if i = 0uy then Seq.empty else as_seq h1 tag in
    let text = last @| info @| Seq.create 1 i' in
    let tag2 = as_seq h2 tag in
    // assert(tag2 == HMAC.hmac (Ghost.hide a) prk text);
    assert(tag2 == as_seq h4 okm_tag);
    let okm' = as_seq h4 okm' in
    Seq.lemma_eq_intro (tag2 @| okm') (as_seq h4 okm);
    assert(okm' == expand0 a prk info (v len') (v i') tag2);
    assert(tag2 @| okm' == expand0 a prk info (v len) (v i) last)    
    end;
  pop_frame()


let mk_expand a hmac okm prk prklen info infolen len =
  push_frame();
  let tlen = Hacl.Hash.Definitions.hash_len a in
  let text = LowStar.Buffer.alloca 0uy (tlen + infolen + 1ul) in
  blit info 0ul text tlen infolen;
  assert (hash_length a <= 64);
  assert (block_length a <= 128);
  assert_norm (64 + pow2 32 + 128 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert (hash_length a + pow2 32 + block_length a <= max_input_length a);
  hkdf_expand_loop a hmac okm prk prklen infolen len text (u8 0);
  pop_frame()


let expand_sha2_256: expand_st SHA2_256 =
  mk_expand SHA2_256 Hacl.HMAC.compute_sha2_256

let extract_sha2_256: extract_st SHA2_256 =
  mk_extract SHA2_256 Hacl.HMAC.compute_sha2_256
