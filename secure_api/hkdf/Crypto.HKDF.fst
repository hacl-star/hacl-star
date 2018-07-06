module Crypto.HKDF

/// 18-03-04 to be compared to Hashing.HKDF, salvaged as a spec 

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32

open Crypto.Hash 

// Definition of base types. Should go elsewhere if we keep using them

let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t
let uint32_p = Buffer.buffer uint32_t
let uint8_p  = Buffer.buffer uint8_t

type alg = Hash.alg13


//18-03-05 I'd rather verify a simpler implementation, closer to the spec, as outlined below. 
//18-03-05 We could make do with fewer loop variables if it helps with C.Loops
private val hkdf_expand_loop: 
  a       : alg13 ->
  okm     : bptr ->
  prk     : bptr ->
  prklen  : bptrlen prk ->
  infolen : UInt32.t -> 
  len     : bptrlen okm  ->
  hashed  : lbptr (tagLength a + v infolen + 1) ->
  i       : UInt8.t {
    let count = UInt8.v i in 
    let required = UInt32.v len in 
    HMAC.keysized a (length prk) /\ 
    disjoint okm prk /\
    disjoint hashed okm /\ 
    disjoint hashed prk /\
    tagLength a + v infolen + 1 + blockLength a < pow2 32 /\ (* specific to this implementation *)
    tagLength a + pow2 32 + blockLength a <= maxLength a /\
    count < 255 /\
    required <= (255 - count) * tagLength a } ->
  Stack unit
  (requires fun h0 -> 
    live h0 okm /\ live h0 prk /\ live h0 hashed)
  (ensures  fun h0 r h1 -> 
    live h1 okm /\ modifies_2 okm hashed h0 h1 /\ (
    let prk = as_seq h0 prk in 
    let info = as_seq h0 (Buffer.sub hashed (tagLen a) infolen) in 
    let last = if i = 0uy then Seq.createEmpty else as_seq h0 (Buffer.sub hashed 0ul (tagLen a)) in 
    let okm = as_seq h1 okm in 
    okm =  expand0 a prk info (v len) (UInt8.v i) last))

#set-options "--z3rlimit 100"
[@"c_inline"]
let rec hkdf_expand_loop a okm prk prklen infolen len hashed i =
  push_frame ();
  let tlen = tagLen a in 
  let tag = Buffer.sub hashed 0ul tlen in 
  let info_counter = Buffer.offset hashed tlen in 
  let info = Buffer.sub info_counter 0ul infolen in
  let counter = Buffer.offset info_counter infolen in 
  assert(disjoint tag info /\ disjoint tag counter /\ disjoint info counter);

  let i' = FStar.UInt8.(i +^ 1uy) in

  let h0 = ST.get() in  // initial state

  // update the counter byte
  Buffer.upd counter 0ul i';

  let h1 = ST.get() in // before hashing
  Seq.lemma_eq_intro (Seq.upd (as_seq h0 counter) 0 i') (Seq.create 1 i');
  assert(as_seq h1 counter == Seq.create 1 i');

  // derive an extra tag 
  if i = 0uy then (
    // the first input is shorter, does not include the chaining block
    let len1 = infolen +^ 1ul in 
    HMAC.compute a tag prk prklen info_counter len1;

    let h2 = ST.get() in 
    ( let info1 = as_seq h1 info in 
      let ctr1 = as_seq h1 counter in 
      let prk1 = as_seq h1 prk in 
      let tag2 = as_seq h2 tag in 
      let text = Seq.createEmpty @| info1 @| ctr1 in

      // assert(tag2 == HMAC.hmac a v_prk (as_seq h1 hashed1)); 
      Seq.lemma_eq_intro (as_seq h1 info_counter) text;
      assert(tag2 == HMAC.hmac a prk1 text)  ))
  else (
    HMAC.compute a tag prk prklen hashed (tlen +^ infolen +^ 1ul);
    let h2 = ST.get() in 
    ( let info1 = as_seq h1 info in 
      let ctr1 = as_seq h1 counter in 
      let prk1 = as_seq h1 prk in 
      let tag1 = as_seq h1 tag in 
      let tag2 = as_seq h2 tag in 
      let text = tag1 @| info1 @| ctr1 in
      assert(tag2 == HMAC.hmac a prk1 (as_seq h1 hashed)); 
      Seq.lemma_eq_intro (as_seq h1 hashed) text ; 
      assert(tag2 == HMAC.hmac a prk1 text )
    ));

  // copy it to the result, and iterate if required
  if len <=^ tlen then 
    Buffer.blit tag 0ul okm 0ul len 
  else (
    Buffer.blit tag 0ul okm 0ul tlen;
    let len = len -^ tlen in 
    let okm = Buffer.sub okm tlen len in 
    hkdf_expand_loop a okm prk prklen infolen len hashed i'
    );

  assume false; // TODO complete functional correctness for the loop
  pop_frame()



// | tagLen a | infolen | 1 | 
  
let hkdf_extract a prk salt saltlen ikm ikmlen =
  HMAC.compute a prk salt saltlen ikm ikmlen

#set-options "--z3rlimit 20"
let hkdf_expand a okm prk prklen info infolen len = 
  push_frame();
  let tlen = tagLen a in 
  let text = Buffer.create 0uy (tlen +^ infolen +^ 1ul) in 
  Buffer.blit info 0ul text tlen infolen; 
  assert_norm(tagLength a + pow2 32 + blockLength a <= maxLength a);
  hkdf_expand_loop a okm prk prklen infolen len text 0uy;
  pop_frame()

(*
// prior implementation, a bit too complicated
// ADL July 4
#set-options "--lax"


[@"c_inline"]
private val hkdf_expand_inner:
  a       : alg ->
  state   : uint8_p ->
  prk     : uint8_p {Hash.tagLength a <= length prk} ->
  prklen  : uint32_t {v prklen = length prk} ->
  info    : uint8_p ->
  infolen : uint32_t {v infolen = length info} ->
  n       : uint32_t {v n <= pow2 8}->
  i       : uint32_t {v i <= v n} ->
  Stack unit
        (requires (fun h0 -> live h0 state /\ live h0 prk /\ live h0 info))
        (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"c_inline"]
let rec hkdf_expand_inner a state prk prklen info infolen n i =

  (* Push a new memory frame *)
  (**) push_frame();

  (* Recompute the sizes and position of the intermediary objects *)
  (* Note: here we favour readability over efficiency *)
  let size_Ti  = Hash.tagLen  a in
  let size_Til = size_Ti +^ infolen +^ 1ul in
  let size_T = U32.mul_mod n size_Ti in

  let pos_Ti = 0ul in
  let pos_Til = size_Ti in
  let pos_T = pos_Til +^ size_Til in

  (* Retrieve the memory for local computations. state =  Ti | Til | T *)
  let ti = Buffer.sub state pos_Ti size_Ti in
  let til = Buffer.sub state pos_Til size_Til in
  let t = Buffer.sub state pos_T size_T in

  if i = 1ul then begin

    Buffer.blit info 0ul til 0ul infolen;
    Buffer.upd til infolen (Int.Cast.uint32_to_uint8 i);

    (* Compute the mac of to get block Ti *)
    HMAC.compute a ti prk prklen til (infolen +^ 1ul);

    (* Store the resulting block in T *)
    Buffer.blit ti 0ul t 0ul size_Ti;

    (* Recursive call *)
    hkdf_expand_inner a state prk prklen info infolen n (i +^ 1ul) end

  else if i <=^ n then begin

    (* Concatenate T(i-1) | Info | i *)
    Buffer.blit ti 0ul til 0ul size_Ti;
    Buffer.blit info 0ul til size_Ti infolen;
    Buffer.upd til (size_Til -^ 1ul) (Int.Cast.uint32_to_uint8 i);

    (* Compute the mac of to get block Ti *)
    HMAC.compute a ti prk prklen til size_Til;

    (* Store the resulting block in T *)
    let pos = U32.mul_mod (i -^ 1ul) size_Ti in
    Buffer.blit ti 0ul t pos size_Ti;

    (* Recursive call *)
    hkdf_expand_inner a state prk prklen info infolen n (i +^ 1ul) end
  else ();

  (* Pop the memory frame *)
  (**) pop_frame()

let hkdf_expand a okm prk prklen info infolen len =
  push_frame ();
  let size_Ti = tagLen a in 
  (* Compute the number of blocks necessary to compute the output *)
  // ceil
  let n_0 = if len %^ size_Ti = 0ul then 0ul else 1ul in
  let n = len /^ size_Ti +^ n_0 in

  (* Describe the shape of memory used by the inner recursive function *)
  let size_Til = size_Ti +^ infolen +^ 1ul in
  let size_T = n *^ size_Ti in

  let pos_Ti = 0ul in
  let pos_Til = size_Ti in
  let pos_T = pos_Til +^ size_Til in

  (* Allocate memory for inner expansion state: Ti @| Til @| T *)
  let state = Buffer.create 0uy (tagLen a +^ size_Til +^ size_T) in

  (* Call the inner expension function *)
  if n >^ 0ul then
    hkdf_expand_inner a state prk prklen info infolen n 1ul;

  (* Extract T from the state *)
  let _T = Buffer.sub state pos_T size_T in

  (* Redundant copy the desired part of T *)
  Buffer.blit _T 0ul okm 0ul len;

  pop_frame()
*)




