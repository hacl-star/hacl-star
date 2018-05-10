module Crypto.AEAD.Encoding

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

// This file defines the encoding of additional data and ciphertext
// authenticated by the one-time MACs, and proves their injectivity properties.

open FStar.UInt32
open FStar.Ghost

open FStar.Math.Lib
open FStar.Math.Lemmas
open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

type region = rgn:HS.rid {is_eternal_region rgn}

let alg (i:id) = cipherAlg_of_id i

type rgn = rgn:HS.rid {is_eternal_region rgn}

// Concrete, somewhat arbitrary bounds on input lengths;
// these should go to some configuration flle
let txtmax = assert_norm (16485 <= pow2 32 - 1); 16485ul // one TLS fragment
let aadmax = assert_norm (2000 <= pow2 32 - 1); 2000ul // more than enough for TLS

// placeholder for additional data
type adata = b:bytes {Seq.length b <= v aadmax}
type cipher (i:id) (l:nat) = lbytes(l + v MAC.taglen)

type aadlen_32 = l:UInt32.t {l <=^ aadmax}
type txtlen_32 = l:UInt32.t {l <=^ txtmax}


//16-09-18 where is it in the libraries?
private let min (a:nat) (b:nat) : nat = if a <= b then a else b


(* * *********************************************)
(* *            Encoding                         *)
(* * *********************************************)

noextract private let pad_0 b l = Seq.append b (Seq.create l 0uy)

// spec for encoding bytestrings into sequences of words. // Note the refined refinement interferes with type instantiation
noextract private val encode_bytes: txt:Seq.seq UInt8.t ->
  GTot (r:MAC.text{Seq.length r = (Seq.length txt + 15)/16})
  (decreases (Seq.length txt))

#reset-options "--z3rlimit 100"
// separated padding case to match imperative code
let rec encode_bytes txt =
  let l = Seq.length txt in
  if l = 0 then
    Seq.createEmpty
  else if l < 16 then
    Seq.create 1 (pad_0 txt (16 - l))
  else
    let txt0, txt = Seq.split txt 16 in
    Seq.snoc (encode_bytes txt) txt0
#reset-options

(* now intrinsic (easier to prove)
let rec lemma_encode_length txt: Lemma
  (ensures (Seq.length(encode_bytes txt) = (Seq.length txt + 15) / 16))
  (decreases (Seq.length txt)) =
  let l = Seq.length txt in
  if l = 0 then ()
  else if l < 16 then assert(Seq.length(encode_bytes txt) = 1)
  else (
    let txt0, txt' = Seq.split txt 16 in
    lemma_encode_length txt';
    assert(Seq.length(encode_bytes txt) = 1 + Seq.length(encode_bytes txt')))
*)

(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

private val lemma_pad_0_injective: b0:Seq.seq UInt8.t -> b1:Seq.seq UInt8.t -> l:nat -> Lemma
  (requires (pad_0 b0 l == pad_0 b1 l))
  (ensures  (b0 == b1))
let lemma_pad_0_injective b0 b1 l =
  Seq.lemma_append_inj b0 (Seq.create l 0uy) b1 (Seq.create l 0uy);
  Seq.lemma_eq_elim b0 b1

(* use the one in Poly1305.Spec:

// prime (do we prove it?)
let p_1305: p:nat{pow2 128 < p} =
  assert_norm (pow2 128 < pow2 130 - 5);
  pow2 130 - 5
val lemma_encode_injective: i:MAC.id -> w0:word -> w1:word -> Lemma
  (requires (length w0 == length w1 /\ MAC.encode i w0 == MAC.encode i w1))
  (ensures  (w0 == w1))
let lemma_encode_injective w0 w1 =
  let open FStar.Mul in
  let l = length w0 in
  lemma_little_endian_is_bounded w0;
  lemma_little_endian_is_bounded w1;
  pow2_le_compat 128 (8 * l);
  lemma_mod_plus_injective p_1305 (pow2 (8 * l))
    (little_endian w0) (little_endian w1);
  assert (little_endian w0 == little_endian w1);
  Seq.lemma_eq_intro (Seq.slice w0 0 l) w0;
  Seq.lemma_eq_intro (Seq.slice w1 0 l) w1;
  lemma_little_endian_is_injective w0 w1 l
*)

private val lemma_encode_bytes_injective: t0:Seq.seq UInt8.t -> t1:Seq.seq UInt8.t -> Lemma
  (requires Seq.length t0 == Seq.length t1 /\ encode_bytes t0 == encode_bytes t1)
  (ensures t0 == t1)
  (decreases (Seq.length t0))
#reset-options "--initial_fuel 1 --max_fuel 1 --z3rlimit 100 --detail_hint_replay"
let rec lemma_encode_bytes_injective t0 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else if l < 16 then
    begin
    let w0 = pad_0 t0 (16 - l) in //w0 == t0 @ (Seq.create (16 - l) 0uy)
    let w1 = pad_0 t1 (16 - l) in //w1 == t1 @ (Seq.create (16 - l) 0uy)
    Seq.lemma_index_create 1 w0 0; // (index (encode_bytes t0) 0 == w0)
    Seq.lemma_index_create 1 w1 0; // (index (encode_bytes t1) 0 == w1)
    assert (Seq.index (encode_bytes t0) 0 == w0);
    assert (Seq.index (encode_bytes t1) 0 == w1);
    lemma_pad_0_injective t0 t1 (16 - l)
    end
  else 
    begin
    let w0, t0' = Seq.split_eq t0 16 in
    let w1, t1' = Seq.split_eq t1 16 in
    Seq.lemma_eq_refl (encode_bytes t0) (encode_bytes t1);
    Seq.lemma_snoc_inj (encode_bytes t0') (encode_bytes t1') w0 w1 ;
    lemma_encode_bytes_injective t0' t1';
    Seq.lemma_eq_elim t0' t1'
    end
#reset-options

// If the length is not a multiple of 16, pad to 16
// (we actually don't depend on the details of the padding)
[@"c_inline"]
inline_for_extraction
val pad_16: b:lbuffer 16 -> len:UInt32.t {0 < v len /\ v len <= 16} -> STL unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 _ h1 ->
    Buffer.live h0 b /\
    Buffer.live h1 b /\
    Buffer.modifies_1 b h0 h1 /\
    Seq.equal (Buffer.as_seq h1 b) (pad_0 (Buffer.as_seq h0 (Buffer.sub b 0ul len)) (16 - v len))))
#reset-options "--max_ifuel 0 --z3rlimit 200 --detail_hint_replay"
let pad_16 b len =
  let h0 = ST.get() in
  Buffer.Utils.memset (Buffer.sub b len (16ul -^ len)) 0uy (16ul -^ len);
  let h1 = ST.get() in
  Seq.lemma_eq_intro (Buffer.as_seq h1 b) (pad_0 (Buffer.as_seq h0 (Buffer.sub b 0ul len)) (16 - v len))

// add variable-length bytes to a MAC accumulator, one 16-byte word at a time
private val add_bytes:
  #i: MAC.id ->
  st: CMA.state i ->
  acc: CMA.accBuffer i ->
  len: UInt32.t ->
  txt: lbuffer (v len) -> Stack unit
  (requires (fun h0 ->
    Buffer.live h0 txt /\
    CMA.acc_inv st acc h0 /\
    Buffer.disjoint (MAC.as_buffer (CMA.abuf acc)) txt /\
    Buffer.disjoint CMA.(MAC.as_buffer st.r) txt /\
    (mac_log ==>
      Buffer.frameOf txt <> HS.frameOf (CMA.alog acc) \/
      Buffer.disjoint_ref_1 txt CMA.(alog acc))))
  (ensures (fun h0 () h1 ->
    let b = CMA.(MAC.as_buffer (CMA.abuf acc)) in
    Buffer.live h1 txt /\
    CMA.acc_inv st acc h1 /\
    (if mac_log then
       let log = CMA.alog acc in
       let l0 = HS.sel h0 log in
       let l1 = HS.sel h1 log in
       Seq.equal l1 (Seq.append (encode_bytes (Buffer.as_seq h1 txt)) l0) /\
       CMA.modifies_buf_and_ref b log h0 h1
     else
       Buffer.modifies_1 b h0 h1)))

#reset-options "--z3rlimit 100 --initial_fuel 2"
// not sure why I need lemmas unfolding encode_bytes; maybe just Z3 complexity
private let lemma_encode_loop (b:_ {Seq.length b >= 16}) : Lemma (
  Seq.equal (encode_bytes b) (Seq.snoc (encode_bytes (Seq.slice b 16 (Seq.length b))) (Seq.slice b 0 16)))
  =  ()

val lemma_encode_final: b:Seq.seq UInt8.t{0 <> Seq.length b /\ Seq.length b < 16} ->
  Lemma (Seq.equal (encode_bytes b) (Seq.create 1 (pad_0 b (16 - Seq.length b))))
let lemma_encode_final b = ()

#reset-options "--z3rlimit 400 --max_fuel 0 --detail_hint_replay"
// 2018.02.22 SZ: Disabled verification to loopify it; see the verified recursive
// version in the comment below.
#set-options "--lax"
let rec add_bytes #i st acc len txt =
  push_frame();
  let bound = len /^ 16ul in
  C.Loops.for 0ul bound (fun _ _ -> True)
  (fun i ->
    let w = Buffer.sub txt (16ul *^ i) 16ul in
    CMA.update st acc w
  );
  let rem = len %^ 16ul in
  if 0ul <^ rem then
  begin
    let w = Buffer.create 0uy 16ul in
    Buffer.blit txt (len -^ rem) w 0ul rem;
    CMA.update st acc w
  end;
  pop_frame()

(*
  // Recursive version with only computationally relevant parts retained
  push_frame();
  if len = 0ul then () else
  if len <^ 16ul then
  begin
    let w = Buffer.create 0uy 16ul in
    Buffer.blit txt 0ul w 0ul len;
    //pad_16 w len; // Unnecessary, since `w` is zero-initialized
    CMA.update st acc w
  end
  else
  begin
    let w = Buffer.sub txt 0ul 16ul in
    CMA.update st acc w;
    let txt' = Buffer.offset txt 16ul in
    add_bytes st acc (len -^ 16ul) txt'
  end;
  pop_frame()
*)

(*
  // Verified recursive version
  let h0 = ST.get() in
  assert(mac_log ==> h0 `HS.contains` (CMA.alog acc));
  push_frame();
  let h1 = ST.get() in
  CMA.frame_acc_inv st acc h0 h1;
  if len = 0ul then () else
  if len <^ 16ul then
      begin
        let w = Buffer.create 0uy 16ul in
        let h2 = ST.get() in
        Buffer.lemma_reveal_modifies_0 h1 h2;
        Buffer.blit txt 0ul w 0ul len;
        pad_16 w len;
        let h3 = ST.get() in
        Buffer.lemma_reveal_modifies_1 w h2 h3;
        CMA.frame_acc_inv st acc h1 h3;
        CMA.update st acc w;
        let h4 = ST.get() in
        if mac_log then
          begin // showing log := padded w :: log
            let txt0 = Buffer.as_seq h0 txt in
            let x = Buffer.as_seq h3 w in
            let log = CMA.alog acc in
            let l0 = HS.sel h0 log in
            let l1 = HS.sel h1 log in
            let l3 = HS.sel h3 log in
            let l4 = HS.sel h4 log in
            assert(Seq.equal x (pad_0 txt0 (16 - v len)));
            assert(Seq.equal l4 (Seq.cons x l0));
            lemma_encode_final txt0;
            assert(Seq.equal l4 (Seq.append (encode_bytes txt0) l0))
          end
        else Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc))  h3 h4
      end
  else
     begin
        let w = Buffer.sub txt 0ul 16ul in
        let txt' = Buffer.offset txt 16ul in
        CMA.update st acc w;
        let h2 = ST.get() in
        add_bytes st acc (len -^ 16ul) txt';
        let h3 = ST.get() in
        if mac_log
        then begin // showing log := encode_bytes txt' @ [w] @ log
          let txt0 = Buffer.as_seq h0 txt in
          let txt1 = Buffer.as_seq h1 txt' in
          let x = Buffer.as_seq h1 w in
          let log = CMA.alog acc in
          let l1 = HS.sel h1 log in
          let l2 = HS.sel h2 log in
          let l3 = HS.sel h3 log in
          assert(Seq.equal txt0 (Seq.append x txt1));
          lemma_encode_loop txt0;
          assert(Seq.equal l2 (Seq.cons x l1));
          assert(Seq.equal l3 (Seq.append (encode_bytes txt1) l2));
          Seq.append_cons_snoc (encode_bytes txt1) x l3;
          assert(Seq.equal l3 (Seq.append (encode_bytes txt0) l1))
        end
        else Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h1 h3
      end;
  let h5 = ST.get() in
  pop_frame();
  let h6 = ST.get() in
  CMA.frame_acc_inv st acc h5 h6;
  MAC.frame_sel_elem h5 h6 (CMA.abuf acc);
  if not mac_log then
Buffer.lemma_intro_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h0 h6
*)

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 100"
private let encode_lengths_poly1305 (aadlen:UInt32.t) (plainlen:UInt32.t) : b:lbytes 16
  { v aadlen = little_endian (Seq.slice b 0 4) /\
    v plainlen = little_endian (Seq.slice b 8 12) } =
  let b0 = Seq.create 4 0uy in
  let ba = uint32_bytes 4ul aadlen in
  let bp = uint32_bytes 4ul plainlen in
  let open FStar.Seq in
  let b = ba @| b0 @| bp @| b0 in
  Seq.append_slices ba (b0 @| bp @| b0);
  Seq.append_slices b0 (bp @| b0);
  Seq.append_slices bp b0;
  b

private val store_lengths_poly1305: aadlen:UInt32.t -> plainlen:UInt32.t -> w:lbuffer 16 ->
  StackInline unit
  (requires (fun h0 -> Buffer.live h0 w /\ Buffer.as_seq h0 w = Seq.create 16 0uy))
  (ensures (fun h0 _ h1 ->
    Buffer.live h1 w /\ Buffer.modifies_1 w h0 h1 /\
    Seq.equal (Buffer.as_seq h1 w) (encode_lengths_poly1305 aadlen plainlen)))
let store_lengths_poly1305 aadlen plainlen w =
  let w0 = Buffer.sub w 0ul 4ul in
  let w1 = Buffer.sub w 4ul 4ul in
  let w2 = Buffer.sub w 8ul 4ul in
  let w3 = Buffer.sub w 12ul 4ul in
  let h0 = ST.get() in
  Seq.lemma_eq_intro (Buffer.as_seq h0 w1) (Seq.create 4 0uy);
  Seq.lemma_eq_intro (Buffer.as_seq h0 w3) (Seq.create 4 0uy);
  store_uint32 4ul w0 aadlen;
  let h = ST.get() in
  store_uint32 4ul w2 plainlen;
  let h1 = ST.get() in
  Buffer.no_upd_lemma_1 h0 h w0 w1;
  Buffer.no_upd_lemma_1 h h1 w2 w1;
  Buffer.no_upd_lemma_1 h0 h w0 w3;
  Buffer.no_upd_lemma_1 h h1 w2 w3;
  lemma_little_endian_inj (uint32_bytes 4ul aadlen) (Buffer.as_seq h1 w0);
  assert(Seq.equal (Buffer.as_seq h1 w1) (Seq.create 4 0uy));
  lemma_little_endian_inj (uint32_bytes 4ul plainlen) (Buffer.as_seq h1 w2);
  assert(Seq.equal (Buffer.as_seq h1 w3) (Seq.create 4 0uy))

open FStar.Mul
//16-10-31 confirm FIPS length formatting for GHASH (inferred from test vectors)
private let encode_lengths_ghash (aadlen:aadlen_32) (txtlen:txtlen_32) : b:lbytes 16
  { 8 * v aadlen = big_endian (Seq.slice b 4 8) /\
    8 * v txtlen = big_endian (Seq.slice b 12 16) } =
  let open FStar.Seq in
  let b0 = create 4 0uy in
  let ba = uint32_be 4ul (8ul *^ aadlen) in
  let bp = uint32_be 4ul (8ul *^ txtlen) in
  let b = b0 @| ba @| b0 @| bp in
  Seq.append_slices b0 (ba @| b0 @| bp);
  Seq.append_slices ba (b0 @| bp);
  Seq.append_slices b0 bp;
  b

private val store_lengths_ghash: aadlen:aadlen_32 ->  txtlen:txtlen_32  -> w:lbuffer 16 ->
  StackInline unit
  (requires (fun h0 -> Buffer.live h0 w /\ Buffer.as_seq h0 w = Seq.create 16 0uy))
  (ensures (fun h0 _ h1 ->
    Buffer.live h1 w /\ Buffer.modifies_1 w h0 h1 /\
    Seq.equal (Buffer.as_seq h1 w) (encode_lengths_ghash aadlen txtlen)))
let store_lengths_ghash aadlen txtlen w =
  let w0 = Buffer.sub w 0ul 4ul in
  let w1 = Buffer.sub w 4ul 4ul in
  let w2 = Buffer.sub w 8ul 4ul in
  let w3 = Buffer.sub w 12ul 4ul in
  let h0 = ST.get() in
  Seq.lemma_eq_intro (Buffer.as_seq h0 w0) (Seq.create 4 0uy);
  Seq.lemma_eq_intro (Buffer.as_seq h0 w2) (Seq.create 4 0uy);
  assert(Buffer.disjoint w0 w1 /\ Buffer.disjoint w0 w3 /\ Buffer.disjoint w2 w1 /\ Buffer.disjoint w2 w3);
  store_big32 4ul w1 (8ul *^ aadlen);
  let h = ST.get() in
  store_big32 4ul w3 (8ul  *^ txtlen);
  let h1 = ST.get() in
  Buffer.no_upd_lemma_1 h0 h w1 w0;
  Buffer.no_upd_lemma_1 h h1 w3 w0;
  Buffer.no_upd_lemma_1 h0 h w1 w2;
  Buffer.no_upd_lemma_1 h h1 w3 w2;
  assert(Seq.equal (Buffer.as_seq h1 w0) (Seq.create 4 0uy));
  lemma_big_endian_inj (uint32_be 4ul (8ul *^ aadlen)) (Buffer.as_seq h1 w1);
  assert(Seq.equal (Buffer.as_seq h1 w2) (Seq.create 4 0uy));
  lemma_big_endian_inj (uint32_be 4ul (8ul *^ txtlen)) (Buffer.as_seq h1 w3)

#set-options "--initial_ifuel 1 --max_ifuel 1"
private let encode_lengths (i:id) (aadlen:aadlen_32) (txtlen:txtlen_32) : lbytes 16 =
  match macAlg_of_id i with
  | POLY1305 -> encode_lengths_poly1305 aadlen txtlen
  | GHASH -> encode_lengths_ghash aadlen txtlen
#reset-options "--z3rlimit 100"

noextract let encode_both (i:id) (aadlen:aadlen_32) (aad:lbytes (v aadlen)) (txtlen:txtlen_32) (cipher:lbytes (v txtlen)) :
  GTot (e:MAC.text {Seq.length e > 0 /\ Seq.head e = encode_lengths i aadlen txtlen}) =
  Seq.cons (encode_lengths i aadlen txtlen)
    (Seq.append
      (encode_bytes cipher)
      (encode_bytes aad))

let lemma_encode_both_inj i (al0:aadlen_32) (pl0:txtlen_32) (al1:aadlen_32) (pl1:txtlen_32)
  (a0:lbytes(v al0)) (p0:lbytes(v pl0)) (a1:lbytes(v al1)) (p1:lbytes (v pl1)) : Lemma
  (requires encode_both i al0 a0 pl0 p0 = encode_both i al1 a1 pl1 p1)
  (ensures al0 = al1 /\ pl0 = pl1 /\ a0 = a1 /\ p0 = p1) =

  let open FStar.Seq in
  let w0 = encode_lengths i al0 pl0 in
  let w1 = encode_lengths i al1 pl1 in
  //assert(encode w0 = encode w1);
  // lemma_encode_injective w0 w1;
  //assert(al0 = al1 /\ pl0 = pl1);
  let ea0 = encode_bytes a0 in
  let ea1 = encode_bytes a1 in
  let ep0 = encode_bytes p0 in
  let ep1 = encode_bytes p1 in
  //assert(length ep0 = length ep1);
  //assert(encode_both al0 pl0 a0 p0 = cons (encode w0) (ep0 @| ea0));
  //assert(encode_both al1 pl1 a1 p1 = cons (encode w1) (ep1 @| ea1));
  lemma_append_inj (create 1 w0) (ep0 @| ea0) (create 1 w1) (ep1 @| ea1);
  //assert( ep0 @| ea0 = ep1 @| ea1);
  lemma_append_inj ep0 ea0 ep1 ea1;
  //assert(ep0 == ep1 /\ ea0 == ea1);
  lemma_encode_bytes_injective p0 p1;
  lemma_encode_bytes_injective a0 a1

#reset-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
private val store_lengths: i:id -> aadlen:aadlen_32 -> txtlen:txtlen_32 -> w:lbuffer 16 ->
  StackInline unit
  (requires (fun h0 -> Buffer.live h0 w /\ Buffer.as_seq h0 w == Seq.create 16 0uy))
  (ensures (fun h0 _ h1 ->
    Buffer.live h1 w /\ Buffer.modifies_1 w h0 h1 /\
    Seq.equal (Buffer.as_seq h1 w) (encode_lengths i aadlen txtlen)))
let store_lengths i aadlen txtlen w =
  assert (macAlg_of_id i == POLY1305 \/ macAlg_of_id i == GHASH);
  match macAlg_of_id i with
  | POLY1305 -> store_lengths_poly1305 aadlen txtlen w
  | GHASH    -> store_lengths_ghash    aadlen txtlen w

let fresh_sref (#a:Type0) h0 h1 (r:ST.reference a) =
  (r `HS.unused_in` h0) /\
  HS.frameOf r == HS.(h1.tip) /\
  h1 `HS.contains` r

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200"
private val frame_modifies_buf_and_ref: #a:Type -> #b:Type -> #c:Type -> h0:mem -> h1:mem ->
  buf:Buffer.buffer a ->
  ref:HS.reference b{Buffer.frameOf buf == HS.frameOf ref} ->
  buf':Buffer.buffer c -> Lemma
  (requires (CMA.modifies_buf_and_ref #a #b buf ref h0 h1 /\
             (Buffer.frameOf buf' <> Buffer.frameOf buf \/
              (Buffer.disjoint buf buf' /\ Buffer.disjoint_ref_1 buf' ref)) /\
              Buffer.live h0 buf'))
  (ensures  (Buffer.live h1 buf' /\ Buffer.equal h0 buf' h1 buf'))
let frame_modifies_buf_and_ref #a #b #c h0 h1 buf ref buf' = ()

private val modifies_0_acc_inv: #i:MAC.id -> st:CMA.state i -> acc:CMA.accBuffer i
  -> h0:mem -> h1:mem -> Lemma
  (requires (CMA.acc_inv st acc h0 /\ Buffer.modifies_0 h0 h1))
  (ensures (CMA.acc_inv st acc h1))
#reset-options "--using_facts_from Prims --using_facts_from FStar --using_facts_from Crypto.Symmetric"
let modifies_0_acc_inv #i st acc h0 h1 =
  Buffer.lemma_reveal_modifies_0 h0 h1;
  CMA.frame_acc_inv #i st acc h0 h1

#reset-options
val accumulate:
  #i:MAC.id -> st:CMA.state i ->
  aadlen:aadlen_32 -> aad:lbuffer (v aadlen) ->
  txtlen:txtlen_32 -> cipher:lbuffer (v txtlen) ->
  StackInline (CMA.accBuffer i)   // StackInline required for stack-allocated accumulator
  (requires (fun h0 ->
     CMA.(MAC.norm_r h0 st.r) /\
     Buffer.live h0 aad /\
     Buffer.live h0 cipher /\
     Buffer.disjoint_2 CMA.(MAC.as_buffer st.r) aad cipher))
  (ensures (fun h0 a h1 ->
    Buffer.modifies_0 h0 h1 /\ // modifies only fresh buffers on the current stack
    // This doesn't seem to work, so inlining it below:
    // fresh_sref h0 h1 (Buffer.content abuf) /\
    ((MAC.as_buffer (CMA.abuf a)) `Buffer.unused_in` h0) /\
    Buffer.frameOf (MAC.as_buffer (CMA.abuf a)) == h1.HS.tip /\
    //h1 `Buffer.contains` (MAC.as_buffer buf) /\
    Buffer.live h1 aad /\
    Buffer.live h1 cipher /\
    CMA.acc_inv st a h1 /\
    (mac_log ==>
       fresh_sref h0 h1 (CMA.alog a) /\
       HS.sel h1 (CMA.alog a) ==
       encode_both (fst i) aadlen (Buffer.as_seq h1 aad) txtlen (Buffer.as_seq h1 cipher))))

#reset-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 200 --detail_hint_replay"
let accumulate #i st aadlen aad txtlen cipher =
  let h = ST.get() in
  let acc = CMA.start st in
  let h0 = ST.get() in
  add_bytes st acc aadlen aad;
  let h1 = ST.get() in
  add_bytes st acc txtlen cipher;
  let h2 = ST.get() in
  assert_norm (16 <= pow2 32 - 1);
  let final_word = Buffer.create 0uy 16ul in
  let h3 = ST.get() in
  let id, _ = i in
  store_lengths id aadlen txtlen final_word;
  let h4 = ST.get() in
  Buffer.lemma_modifies_0_1' final_word h2 h3 h4;
  modifies_0_acc_inv st acc h2 h4;
  CMA.update st acc final_word;
  let h5 = ST.get () in
  if mac_log then
    begin
      let open FStar.Seq in
      let buf = CMA.(MAC.as_buffer (abuf acc)) in
      let log = CMA.alog acc in
      let cbytes = Buffer.as_seq h cipher in 
      let abytes = Buffer.as_seq h aad in 
      Buffer.lemma_reveal_modifies_0 h h0;
      //modifies_buf_and_ref_trans buf log h0 h1 h2;
      Buffer.lemma_reveal_modifies_0 h2 h4;
      //assert HS.(modifies_one h.tip h h0);
      assert HS.(modifies_one h.tip h0 h2);
      //assert HS.(modifies_one h.tip h2 h4);
      assert HS.(modifies_one h.tip h4 h5);
      assert HS.(modifies_one h.tip h h5);
      Buffer.lemma_intro_modifies_0 h h5;
      lemma_eq_intro (HS.sel h0 log) createEmpty;
      Buffer.no_upd_lemma_0 h h0 aad;
      frame_modifies_buf_and_ref h0 h1 buf log aad;
      frame_modifies_buf_and_ref h1 h2 buf log aad;
      Buffer.no_upd_lemma_0 h h0 cipher;
      frame_modifies_buf_and_ref h0 h1 buf log cipher;
      frame_modifies_buf_and_ref h1 h2 buf log cipher;
      append_empty_r (encode_bytes abytes);
      lemma_eq_intro (HS.sel h1 log) (append (encode_bytes abytes) createEmpty);
      lemma_eq_intro (HS.sel h1 log) (encode_bytes abytes);
      lemma_eq_intro (HS.sel h2 log) (encode_bytes cbytes @| encode_bytes abytes)
    end
  else
    begin
      let buf = CMA.(MAC.as_buffer (abuf acc)) in
      Buffer.lemma_modifies_1_trans buf h0 h1 h2;
      Buffer.lemma_modifies_0_1' buf h h0 h2;
      Buffer.lemma_modifies_0_0 h h2 h4;
      Buffer.lemma_modifies_0_1' buf h h4 h5;
      Buffer.lemma_reveal_modifies_0 h h0;
      Buffer.lemma_reveal_modifies_0 h2 h4;
      Buffer.lemma_reveal_modifies_1 buf h0 h1;
      Buffer.lemma_reveal_modifies_1 buf h1 h2;
      Buffer.lemma_reveal_modifies_1 buf h4 h5
    end;
  acc
