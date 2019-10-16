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

(*
val foo: 
    #t:Type0
  -> len:size_nat
  -> max:nat
  -> n:nat{n <= max}
  -> a:(i:nat{i <= max} -> Type)
  -> f:(i:nat{i < max} -> a i -> a (i + 1) & s:Seq.seq t{Seq.length s == len})
  -> g:(i:nat{i < max} -> a i -> a (i + 1) & s:Seq.seq t{Seq.length s == len})
  -> init:a 0 
  -> Lemma (requires
          forall (i:nat{i < max}) (acc:a i). f i acc == g i acc)
        (ensures Seq.generate_blocks len max n a f init ==
                 Seq.generate_blocks len max n a g init)
let foo #t len max n a f g init = admit()
*)

#push-options "--z3rlimit 500"

let mk_expand a hmac okm prk prklen info infolen len =
  let _h = ST.get () in
  [@inline_let]
  let okm: B.lbuffer uint8 len = okm in
  [@inline_let]
  let prk: B.lbuffer uint8 prklen = prk in
  [@inline_let]
  let info:B.lbuffer uint8 infolen = info in

  let tlen = Hash.Definitions.hash_len a in
  let n = len /. tlen in
  let output: B.lbuffer uint8 (n *! tlen) = 
    B.sub okm 0ul (n *! tlen) in
  Math.Lemmas.lemma_div_mod (v len) (v tlen);
  // provable
  assert (v len - (v len / v tlen) * v tlen == v len % v tlen);
  hmac_input_fits a;

  push_frame();
  let text = B.create (tlen +! infolen +! 1ul) (u8 0) in
  let text0: B.lbuffer uint8 (infolen +! 1ul) = 
    B.sub text tlen (infolen +! 1ul) in
  let tag = B.sub text 0ul tlen in
  let ctr = B.sub text (tlen +! infolen) 1ul in
  B.copy (B.sub text tlen infolen) info;
  [@inline_let]
  let a_spec (i:size_nat{i <= v n}) = 
    Seq.lseq uint8 (if i = 0 then 0 else v tlen)
  in  
  [@inline_let]
  let refl h (i:size_nat{i <= v n}) : GTot (a_spec i) =
    if i = 0 then FStar.Seq.empty #uint8 else B.as_seq h tag
  in
  [@inline_let]
  let footprint (i:size_nat{i <= v n}) :
    GTot LB.(l:loc{
        loc_disjoint l (B.loc output) /\
        address_liveness_insensitive_locs `loc_includes` l})
    = LB.loc_union (B.loc tag) (B.loc ctr) in
  [@inline_let]
  let spec h0 : GTot (i:size_nat{i < v n} -> a_spec i -> a_spec (i + 1) & Seq.lseq uint8 (v tlen)) =
    let prk  = B.as_seq h0 prk in
    let info = B.as_seq h0 info in
    fun i tag ->
      let t = Spec.Agile.HMAC.hmac a prk (tag @| info @| Seq.create 1 (u8 (i + 1))) in
      t, t
  in
  let h0 = ST.get () in    
  B.fill_blocks h0 tlen n output
    a_spec
    refl
    footprint
    spec
    (fun i ->
      admit();
      let h = ST.get() in
      // provable
      // assume (B.as_seq h (B.gsub text tlen infolen) == 
      //        B.as_seq h0 info);
      let j = Lib.IntTypes.cast U8 PUB (i +! 1ul) in
      ctr.(0ul) <- j;
      let h1 = ST.get() in
      assert (LB.modifies (B.loc ctr) h h1);
      if i = 0ul then
        begin
        // provable
        assert (Seq.equal 
         (B.as_seq h1 text0)
         (FStar.Seq.empty @| B.as_seq h0 info @| Seq.create 1 (u8 1)));
        hmac tag prk prklen text0 (infolen +! 1ul);
        let h2 = ST.get() in
        // provable
        assert (B.as_seq h2 tag ==
          Spec.Agile.HMAC.hmac a (B.as_seq h0 prk)
            (FStar.Seq.empty @| B.as_seq h0 info @| Seq.create 1 (u8 1)));
        let _, t = spec h0 0 (FStar.Seq.empty #uint8) in
        // provable
        assert (B.as_seq h2 tag == t)
        end
      else
        begin
        // provable
        assert (Seq.equal 
          (B.as_seq h1 text)
          (B.as_seq h1 tag @| B.as_seq h0 info @| Seq.create 1 j));
        hmac tag prk prklen text (tlen +! infolen +! 1ul);
        let h2 = ST.get() in
        // provable
        assert (B.as_seq h2 tag ==
           Spec.Agile.HMAC.hmac a (B.as_seq h0 prk)
             (B.as_seq h1 tag @| B.as_seq h0 info @| Seq.create 1 j));
        let _, t = spec h0 (v i) (B.as_seq h tag) in
        // provable
        assert (B.as_seq h2 tag == t)
        end;
      Seq.unfold_generate_blocks (v tlen) (v n) a_spec (spec h0) (FStar.Seq.empty #uint8) (v i);
      // provable
      assert (v (i *! tlen) + v tlen <= v (n *! tlen));
      let block = B.sub output (i *! tlen) tlen in
      B.copy block tag
      // let h3 = ST.get() in
      // provable
      // assert (
      //   footprint (v i + 1) `LB.loc_includes` footprint (v i) /\
      //   LB.modifies (LB.loc_union (footprint (v i + 1)) (B.loc block)) h h3);
      // provable
      //assert (
      //  let s, b = spec h0 (v i) (refl h (v i)) in
      //  refl h3 (v i + 1) == s /\ as_seq h3 block == b)
    );

  let h1 = ST.get () in
  if n *! tlen <. len then
    begin
    //provable
    assert (B.as_seq h1 (B.gsub text tlen infolen) == B.as_seq h0 info);
    let j = Lib.IntTypes.cast U8 PUB (n +! 1ul) in
    ctr.(0ul) <- j;
    let h2 = ST.get() in
    //provable
    assert (B.as_seq h1 prk == B.as_seq h0 prk);
    //provable
    assert (v n > 0 ==>
      Seq.equal (B.as_seq h2 text)
      ((refl h1 (v n) @| B.as_seq h0 info @| Seq.create 1 j)));
    assert (v n = 0 ==>
      Seq.equal (B.as_seq h2 text0)
      ((refl h1 (v n) @| B.as_seq h0 info @| Seq.create 1 j)));
    if n = 0ul then
      hmac tag prk prklen text0 (infolen +! 1ul)
    else
      hmac tag prk prklen text (tlen +! infolen +! 1ul);
    let block = B.sub okm (n *! tlen) (len -! (n *! tlen)) in
    B.copy block (B.sub tag 0ul (len -! (n *! tlen)));
    let h2 = ST.get() in
    // provable
    assert (
      B.as_seq h2 tag ==
        Spec.Agile.HMAC.hmac a (B.as_seq h0 prk)
          (refl h1 (v n) @| B.as_seq h0 info @| Seq.create 1 j))
  end;
  let h2 = ST.get() in
  // TODO: prove
  assume (
    let open Spec.Agile.HMAC in
    let prk = B.as_seq h0 prk in
    let info = B.as_seq h0 info in 
    let tlen = v tlen in
    let n = v n in
    let len = v len in
    expand a prk info len ==
    (let tag, output = 
       Seq.generate_blocks tlen n n 
         a_spec
         (spec h0)
         (FStar.Seq.empty #uint8)
     in
     if n * tlen < len then
       let t = hmac a prk (tag @| info @| Seq.create 1 (u8 (n + 1))) in
       output @| Seq.sub #_ #tlen t 0 (len - (n * tlen))
    else output));
  // provable
  assert (
    let open Spec.Agile.HMAC in
    let tlen = v tlen in //hash_length a in
    let n = v n in //len / v tlen in
    let prk = B.as_seq h0 prk in
    let info = B.as_seq h0 info in
    let tag', output' = 
      Seq.generate_blocks tlen n n 
        a_spec
        (spec h0)
        (FStar.Seq.empty #uint8)
    in
    refl h1 n == tag' /\
    B.as_seq h1 output == output' /\
    Seq.equal 
      (B.as_seq h2 okm)
      (output' @| Seq.sub (B.as_seq h2 tag) 0 (v len - n * tlen)));
  pop_frame()
  

let expand_sha2_256: expand_st SHA2_256 =
  mk_expand SHA2_256 Hacl.HMAC.compute_sha2_256

let extract_sha2_256: extract_st SHA2_256 =
  mk_extract SHA2_256 Hacl.HMAC.compute_sha2_256
