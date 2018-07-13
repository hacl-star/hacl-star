module EverCrypt.HKDF

/// 18-03-04 to be compared to Hashing.HKDF, salvaged as a spec 

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open FStar.Integers

open EverCrypt.Hash 

type alg = EverCrypt.HMAC.ha


//18-03-05 I'd rather verify a simpler implementation, closer to the spec, as outlined below. 
//18-03-05 We could make do with fewer loop variables if it helps with C.Loops
private val hkdf_expand_loop: 
  a       : alg -> (
  okm     : uint8_p ->
  prk     : uint8_p ->
  prklen  : uint8_l prk ->
  infolen : UInt32.t -> 
  len     : uint8_l okm  ->
  hashed  : uint8_pl (tagLength (Ghost.hide a) + v infolen + 1) ->
  i       : UInt8.t {
    let a = Ghost.hide a in 
    let count = v i in 
    let required = v len in 
    HMAC.keysized a (length prk) /\ 
    disjoint okm prk /\
    disjoint hashed okm /\ 
    disjoint hashed prk /\
    tagLength a + v infolen + 1 + blockLength a < pow2 32 /\ (* specific to this implementation *)
    tagLength a + pow2 32 + blockLength a <= maxLength a /\
    count < 255 /\
    required <= (255 - count) * tagLength a } ->
  ST unit
  (requires fun h0 -> 
    live h0 okm /\ live h0 prk /\ live h0 hashed)
  (ensures  fun h0 r h1 -> 
    //live h1 okm /\ 
    LowStar.Modifies.(modifies (loc_union (loc_buffer okm) (loc_buffer hashed)) h0 h1) /\ (
    let prk = as_seq h0 prk in 
    let info = as_seq h0 (gsub hashed (tagLen a) infolen) in 
    let last = if i = 0uy then Seq.empty else as_seq h0 (gsub hashed 0ul (tagLen a)) in 
    let okm = as_seq h1 okm in 
    okm == expand0 (Ghost.hide a) prk info (v len) (v i) last)))

#set-options "--z3rlimit 100"
let rec hkdf_expand_loop a okm prk prklen infolen len hashed i =
  push_frame ();
  let tlen = tagLen a in 
  let tag = sub hashed 0ul tlen in 
  let info_counter = offset hashed tlen in 
  let info = sub info_counter 0ul infolen in
  let counter = offset info_counter infolen in 
  assert(disjoint tag info /\ disjoint tag counter /\ disjoint info counter);

  let i' = i + 1uy in

  let h0 = ST.get() in  // initial state
  counter.(0ul) <- i';

  let h1 = ST.get() in // before hashing
  FStar.Seq.(lemma_eq_intro (upd (as_seq h0 counter) 0 i') (create 1 i'));
  assert(as_seq h1 counter == Seq.create 1 i');

  // derive an extra tag 
  if i = 0uy then (
    // the first input is shorter, does not include the chaining block
    let len1 = infolen + 1ul in 
    HMAC.compute a tag prk prklen info_counter len1;

    let h2 = ST.get() in 
    ( let info1 = as_seq h1 info in 
      let ctr1 = as_seq h1 counter in 
      let prk1 = as_seq h1 prk in 
      let tag2 = as_seq h2 tag in 
      let text = Seq.empty @| info1 @| ctr1 in

      // assert(tag2 == HMAC.hmac a v_prk (as_seq h1 hashed1)); 
      Seq.lemma_eq_intro (as_seq h1 info_counter) text;
      assert(tag2 == HMAC.hmac (Ghost.hide a) prk1 text)  ))
  else (
    HMAC.compute a tag prk prklen hashed (tlen + infolen + 1ul);
    let h2 = ST.get() in 
    ( let info1 = as_seq h1 info in 
      let ctr1 = as_seq h1 counter in 
      let prk1 = as_seq h1 prk in 
      let tag1 = as_seq h1 tag in 
      let tag2 = as_seq h2 tag in 
      let text = tag1 @| info1 @| ctr1 in
      assert(tag2 == HMAC.hmac (Ghost.hide a) prk1 (as_seq h1 hashed)); 
      Seq.lemma_eq_intro (as_seq h1 hashed) text ; 
      assert(tag2 == HMAC.hmac (Ghost.hide a) prk1 text )
    ));

  // copy it to the result, and iterate if required
  if len <= tlen then 
    blit tag 0ul okm 0ul len
  else (
    blit tag 0ul okm 0ul tlen;
    let len = len - tlen in 
    let okm = sub okm tlen len in 
    let h2 = ST.get() in 
    hkdf_expand_loop a okm prk prklen infolen len hashed i';

    let h3 = ST.get() in 
    assert(
      let prk = as_seq h0 prk in 
      let info = as_seq h0 (gsub hashed (tagLen a) infolen) in 
      let last = if i' = 0uy then Seq.empty else as_seq h2 (gsub hashed 0ul (tagLen a)) in 
      let okm = as_seq h3 okm in 
      okm ==  expand0 (Ghost.hide a) prk info (v len) (v i') last)
    );

  // TODO complete functional correctness
  let h3 = ST.get() in 
  assume(
      let prk = as_seq h0 prk in 
      let info = as_seq h0 (gsub hashed (tagLen a) infolen) in 
      let last = if i = 0uy then Seq.empty else as_seq h0 (gsub hashed 0ul (tagLen a)) in 
      let okm = as_seq h3 okm in 
      okm ==  expand0 (Ghost.hide a) prk info (v len) (v i) last);

  pop_frame()

// | tagLen a | infolen | 1 | 
  
let hkdf_extract a prk salt saltlen ikm ikmlen =
    HMAC.compute a prk salt saltlen ikm ikmlen

#set-options "--z3rlimit 20"
let hkdf_expand a okm prk prklen info infolen len = 
  push_frame();
  let tlen = tagLen a in 
  let text = alloca 0uy (tlen + infolen + 1ul) in 
  blit info 0ul text tlen infolen; 
  assert_norm(
    let a = Ghost.hide a in 
    tagLength a + pow2 32 + blockLength a <= maxLength a);
  hkdf_expand_loop a okm prk prklen infolen len text 0uy;
  pop_frame()
