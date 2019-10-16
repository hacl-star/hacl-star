module Hacl.HKDF

open FStar.Seq

module B = Lib.Buffer
module LB = LowStar.Buffer

open Spec.Hash.Definitions
open Spec.Agile.HKDF

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST
open Lib.Buffer

friend Spec.Agile.HKDF
friend Lib.IntTypes

module Seq = Lib.Sequence

// TODO: proofs break mysteriously when not befriending Lib.IntTypes and
// declassifying uint8; investigate
// assume val declassify8: squash (uint8 == UInt8.t)    

module ST = FStar.HyperStack.ST

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"

let mk_extract a hmac prk salt saltlen ikm ikmlen =
  hmac prk salt saltlen ikm ikmlen

val hmac_input_fits: a:hash_alg -> Lemma 
  (pow2 32 + block_length a <= max_input_length a)  
let hmac_input_fits a =
  allow_inversion hash_alg;
  match a with
  | MD5 ->
    assert_norm (pow2 32 + block_length MD5 <= max_input_length MD5)  
  | SHA1 -> 
    assert_norm (pow2 32 + block_length SHA1 <= max_input_length SHA1)
  | SHA2_224 ->
    assert_norm (pow2 32 + block_length SHA2_224 <= max_input_length SHA2_224)
  | SHA2_256 -> 
    assert_norm (pow2 32 + block_length SHA2_256 <= max_input_length SHA2_256)
  | SHA2_384 ->
    assert_norm (pow2 32 + block_length SHA2_384 <= max_input_length SHA2_384)
  | SHA2_512 ->
    assert_norm (pow2 32 + block_length SHA2_512 <= max_input_length SHA2_512)

#push-options "--z3rlimit 300"

let mk_expand a hmac okm prk prklen info infolen len =
  let tlen = Hash.Definitions.hash_len a in
  let n = len /. tlen in

  Math.Lemmas.lemma_div_mod (v len) (v tlen);
  //assert (v len - (v len / v tlen) * v tlen == v len % v tlen);
  hmac_input_fits a;

  [@inline_let]
  let okm: B.lbuffer uint8 len = okm in
  [@inline_let]
  let prk: B.lbuffer uint8 prklen = prk in
  [@inline_let]
  let info: B.lbuffer uint8 infolen = info in
  let output: B.lbuffer uint8 (n *! tlen) = B.sub okm 0ul (n *! tlen) in

  push_frame ();
  let text = B.create (tlen +! infolen +! 1ul) (u8 0) in
  let text0: B.lbuffer uint8 (infolen +! 1ul) = B.sub text tlen (infolen +! 1ul) in
  let tag = B.sub text 0ul tlen in
  let ctr = B.sub text (tlen +! infolen) 1ul in
  B.copy (B.sub text tlen infolen) info;
  [@inline_let]
  let a_spec = a_spec a in
  [@inline_let]
  let refl h (i:size_nat{i <= v n}) : GTot (a_spec i) =
    if i = 0 then FStar.Seq.empty #uint8 else B.as_seq h tag
  in
  [@inline_let]
  let footprint (i:size_nat{i <= v n}) :
    GTot LB.(l:loc{loc_disjoint l (B.loc output) /\
                   address_liveness_insensitive_locs `loc_includes` l}) = 
    LB.loc_union (B.loc tag) (B.loc ctr) 
  in
  [@inline_let]
  let spec h0 : GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1) & Seq.lseq uint8 (v tlen)) =
    expand_loop a (B.as_seq h0 prk) (B.as_seq h0 info) (v n)
  in
  let h0 = ST.get () in
  B.fill_blocks h0 tlen n output a_spec refl footprint spec (fun i ->
    ctr.(0ul) <- Lib.IntTypes.cast U8 PUB (i +! 1ul);
    let h1 = ST.get() in
    if i = 0ul then
      begin
      Seq.eq_intro
        (B.as_seq h1 text0)
        (refl h1 (v i) @| B.as_seq h0 info @| Seq.create 1 (u8 (v i + 1)));
      hmac tag prk prklen text0 (infolen +! 1ul)
      // let h2 = ST.get() in
      // assert (B.as_seq h2 tag ==
      //   Spec.Agile.HMAC.hmac a (B.as_seq h0 prk)
      //     (FStar.Seq.empty @| B.as_seq h0 info @| Seq.create 1 (u8 (v i + 1))));
      // assert (let _, t = spec h0 0 (FStar.Seq.empty #uint8) in B.as_seq h2 tag == t)
      end
    else
      begin        
      Seq.eq_intro 
        (B.as_seq h1 text)
        (refl h1 (v i) @| B.as_seq h0 info @| Seq.create 1 (u8 (v i + 1)));
      hmac tag prk prklen text (tlen +! infolen +! 1ul)
      // let h2 = ST.get() in
      // assert (B.as_seq h2 tag ==
      //    Spec.Agile.HMAC.hmac a (B.as_seq h0 prk)
      //      (B.as_seq h1 tag @| B.as_seq h0 info @| Seq.create 1 (u8 (v i + 1))));
      // assert (let _, t = spec h0 (v i) (B.as_seq h tag) in B.as_seq h2 tag == t)
      end;
    Seq.unfold_generate_blocks 
      (v tlen) (v n) a_spec (spec h0) (FStar.Seq.empty #uint8) (v i);
    //assert (v (i *! tlen) + v tlen <= v (n *! tlen));
    B.copy (B.sub output (i *! tlen) tlen) tag
    // let h3 = ST.get() in
    // assert (
    //   footprint (v i + 1) `LB.loc_includes` footprint (v i) /\
    //   LB.modifies (LB.loc_union (footprint (v i + 1)) (B.loc block)) h h3);
    //assert (
    //  let s, b = spec h0 (v i) (refl h (v i)) in
    //  refl h3 (v i + 1) == s /\ as_seq h3 block == b)
  );

  let h1 = ST.get () in
  if n *! tlen <. len then
    begin
    ctr.(0ul) <- Lib.IntTypes.cast U8 PUB (n +! 1ul);
    let h2 = ST.get() in
    if n = 0ul then
      begin
      Seq.eq_intro
        (B.as_seq h2 text0)
        (refl h1 (v n) @| B.as_seq h0 info @| Seq.create 1 (u8 (v n + 1)));
      hmac tag prk prklen text0 (infolen +! 1ul)
      end
    else
      begin
      Seq.eq_intro
        (B.as_seq h2 text)
        (refl h1 (v n) @| B.as_seq h0 info @| Seq.create 1 (u8 (v n + 1)));
      hmac tag prk prklen text (tlen +! infolen +! 1ul)
      end;
    let block = B.sub okm (n *! tlen) (len -! (n *! tlen)) in
    B.copy block (B.sub tag 0ul (len -! (n *! tlen)))
    // let h3 = ST.get() in
    // assert (
    //   B.as_seq h3 tag ==
    //   Spec.Agile.HMAC.hmac a (B.as_seq h0 prk) 
    //     (refl h1 (v n) @| B.as_seq h0 info @| Seq.create 1 (u8 (v n + 1))))
  end;

  let h4 = ST.get() in
  assert (
    let tag', output' =
      Seq.generate_blocks (v tlen) (v n) (v n) a_spec (spec h0) (FStar.Seq.empty #uint8)
    in
    // refl h1 (v n) == tag' /\ B.as_seq h1 output == output' /\
    Seq.equal 
      (B.as_seq h4 okm)
      (output' @| Seq.sub (B.as_seq h4 tag) 0 (v len - v n * v tlen)));
  pop_frame ()

let expand_sha2_256: expand_st SHA2_256 =
  mk_expand SHA2_256 Hacl.HMAC.compute_sha2_256

let extract_sha2_256: extract_st SHA2_256 =
  mk_extract SHA2_256 Hacl.HMAC.compute_sha2_256
