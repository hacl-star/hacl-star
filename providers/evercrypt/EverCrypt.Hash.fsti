module EverCrypt.Hash

open EverCrypt.Helpers
open FStar.HyperStack.ST
open FStar.Integers
 
/// ----------agile interface to hash specifications ----------------
/// inlined here since EverCrypt.Hash.fst needs access to
/// the specification implementation
///

/// Agile specification of all supported hash algorithmms.

//open FStar.UInt32
let bytes = Seq.seq UInt8.t
type lbytes (l:nat) = b:bytes{ Seq.length b = l }

/// SUPPORTED ALGORITHMS see e.g. https://en.wikipedia.org/wiki/SHA-1
/// for a global comparison and lengths
///
/// * SHA224 and SHA512 are not yet multiplexed.
/// * MD5 and SHA1 are still required by TLS 1.2, included for legacy
///   purpose only, and not provided by HACL*.
/// * SHA3 will be provided by HACL*.
   
type alg =
  | MD5
  | SHA1
  | SHA224 
  | SHA256
  | SHA384
  | SHA512
//| SHAKE128 of (n:nat{n >= 8})
//| SHAKE256 of (n:nat{n >= 16})

val string_of_alg: alg -> string 


/// HMAC/HKDF ALGORITHMS; secure_api makes security assumptions only
/// for constructions based on those.
/// 
//type alg13 = a:alg {a=SHA256 \/ a=SHA384 \/ a=SHA512}
type alg13 = alg
type e_alg = Ghost.erased alg


/// Lengths for input blocks and output tags, in bytes.

let blockLen = function
  | MD5 | SHA1 | SHA224 | SHA256 ->  64ul
  | SHA384 | SHA512              -> 128ul
//| SHAKE128 _ -> 168 | SHAKE256 _ -> 136
  
noextract 
let blockLength (a: e_alg) = v (blockLen (Ghost.reveal a))

let maxTagLen = 64ul
let tagLen (a:alg) : Tot UInt32.t =
  match a with
  | MD5    -> 16ul
  | SHA1   -> 20ul
  | SHA224 -> 28ul // truncated SHA256
  | SHA256 -> 32ul
  | SHA384 -> 48ul // truncated SHA512
  | SHA512 -> 64ul
noextract 
let tagLength a = v (tagLen (Ghost.reveal a))
let lemma_maxLen (a:alg) = assert_norm(tagLen a <= maxTagLen)

/// Maximal input lengths (from hacl*); this is overly restrictive.

noextract let maxLength: e_alg -> nat = fun a -> pow2 61 - 1 
noextract let lemma_maxLength (a: e_alg) = assert_norm (pow2 32 <= maxLength a) 
noextract let hashable (a: e_alg) = b: bytes{ Seq.length b <= maxLength a }
//TODO in hacl* this was enforced more concretely using the counter.

/// To specify their low-level incremental computations, we assume
/// Merkle-Damgard/sponge-like algorithms:
///
/// The hash state is kept in an accumulator, with
/// - an initial value
/// - an update function, adding a block of bytes;
/// - an extract function, returning a hash tag.
///
/// Before hashing, some algorithm-specific padding and length
/// encoding is appended to the input bytestring.
///
/// This is not a general-purpose incremental specification, which
/// would support adding text fragments of arbitrary lengths.

//18-07-06 switching to ghosts for uniformity, but not great at the pure code actually works concretely.
//18-07-06 a better name than repr_t?
noextract val acc (a: e_alg): Type0 // noeq, but `noeq val` is not supported)

(* sets the initial value of the accumulator *) 
noextract val acc0 (#a:e_alg): GTot (acc a)

(* hashes one block of data into the accumulator *)
noextract val compress: #a:e_alg -> acc a -> b: lbytes (blockLength a) -> GTot (acc a)

(* extracts the tag from the (possibly larger) accumulator *)
noextract val extract: #a:e_alg -> acc a -> lbytes (tagLength a)
 
// val hash2: #a:alg -> acc a -> b:bytes {length b % blockLength a = 0} -> acc a (decreases (length b))
noextract let rec hash2 
  (#a:e_alg) 
  (v:acc a) 
  (b:bytes {Seq.length b % blockLength a = 0}): 
  GTot (acc a) (decreases (Seq.length b))
=  
  if Seq.length b = 0 then v
  else
    let c,b = Seq.split b (blockLength a) in
    hash2 (compress v c) b

let lemma_compress 
  (#a: e_alg) 
  (a0: acc a)
  (c: lbytes (blockLength a)): 
  Lemma (compress a0 c == hash2 a0 c) = ()

let rec lemma_hash2 
  (#a: e_alg) 
  (a0: acc a)
  (b0 b1: (b:bytes{ Seq.length b % blockLength a = 0})): 
  Lemma 
    (ensures hash2 a0 (Seq.append b0 b1) == hash2 (hash2 a0 b0) b1)
    (decreases (Seq.length b0)) 
=
  if Seq.length b0 = 0 then (
    Seq.lemma_empty b0;
    Seq.append_empty_l b1 )
  else (
    let c,b0' = Seq.split b0 (blockLength a) in
    let c',b' = Seq.split (Seq.append b0 b1) (blockLength a) in
    Seq.append_assoc c b0' b1;
    //Seq.lemma_split b0 (blockLength a);
    //Seq.lemma_eq_intro (Seq.append b0 b1) (Seq.append c' b');
    Seq.lemma_eq_intro c c';
    Seq.lemma_eq_intro b' (Seq.append b0' b1);
    lemma_hash2 (hash2 a0 c) b0' b1)

noextract let hash0 (#a:e_alg) (b:bytes {Seq.length b % blockLength a = 0}) = hash2 (acc0 #a) b

/// PADDING AND LENGTH ENCODING
/// for convenience, we treat inputs as sequences of bytes, not bits.
/// but note that the suffix encodes the length in bits.
private noextract
let suffixLength (a:e_alg) (length:nat {length <= maxLength a}): 
  GTot (n:nat{ (length + n) % blockLength a = 0 /\ n <= blockLength a + 9 })
=
  let blocklen = blockLength a in 
  let lenlen = match Ghost.reveal a with | SHA384 | SHA512 -> 8 | _ -> 4 in
  let required =  length + 1 + lenlen in // minimal length after padding and encoding the length
  let zeros = // minimal extra padding for block alignment
    if required % blocklen = 0 
    then 0
    else blocklen - (required % blocklen) in
    //was, harder to prove: required + blockLen a - ((required - 1) % blockLen a + 1) in
  1 + zeros + lenlen

noextract val suffix: a:e_alg -> l:nat {l <= maxLength a} -> GTot (lbytes (suffixLength a l))

// would prefer to name it [hash] but already taken below
noextract let spec (a:e_alg) (b:hashable a): GTot (lbytes (tagLength a)) =
  let blocks = Seq.append b (suffix a (Seq.length b)) in
  let acc = hash0 blocks in
  let tag = extract acc in
  tag

// TODO most users of the spec would prefer a more opaque specification
// can we use [abstract] or something similar to hide the structure?


/// 18-04-07 postponing verified integration with HACL* for now. We
/// provide below a concise definition of the Merkle-Damgard
/// construction. The plan is to integrate it with Benjamin's
/// algorithmic specifications. At that point, we will probably hide
/// the construction behind the provider interface (since we don't
/// care about the construction when using or reasoning about them).

/// 
/// ----------agile interface to hash specifications ----------------





module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

let uint8_p = B.buffer UInt8.t

// abstract implementation state
val state_s: e_alg -> Type0
let state alg = B.pointer (state_s alg)

// NS: note that the state is the first argument to the invariant so that we can
// do partial applications in pre- and post-conditions
val footprint_s: #a:e_alg -> state_s a -> GTot M.loc
let footprint (#a: e_alg) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_buffer s) (footprint_s (deref m s)))

val invariant_s: (#a: e_alg) -> state_s a -> HS.mem -> Type0
let invariant (#a: e_alg) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_buffer s) (footprint_s (deref m s))) /\
  invariant_s (B.get m s 0) m

//18-07-06 as_acc a better name? not really a representation
val repr: #a:e_alg -> s:state a -> h:HS.mem { invariant s h } ->
  GTot (acc a)

// Waiting for these to land in LowStar.Modifies
let loc_in (l: M.loc) (h: HS.mem) =
  M.(loc_not_unused_in h `loc_includes` l)

let loc_unused_in (l: M.loc) (h: HS.mem) =
  M.(loc_unused_in h `loc_includes` l)

let fresh_loc (l: M.loc) (h0 h1: HS.mem) =
  loc_unused_in l h0 /\ loc_in l h1

val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (fresh_loc l1 h0 h1 /\ l2 `loc_in` h0))
  (ensures (M.loc_disjoint l1 l2))

val frame_invariant: #a:e_alg -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: e_alg)
  (l: M.loc)
  (s: state a)
  (h0 h1: HS.mem): Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    footprint s h1 == footprint s h0))
=
  ()

val create: a:alg -> ST (state (G.hide a))
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    fresh_loc (footprint s h1) h0 h1)

val init: #a:e_alg -> s:state a -> ST unit
  (requires (invariant s))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    repr s h1 == acc0 #a))

val well_formed: 
  #a:e_alg -> 
  s: state a ->
  h: HS.mem{invariant s h} -> GTot Type0

val bounded_counter:
  #a:e_alg ->
  s: state a ->
  h: HS.mem{invariant s h} ->
  n: nat { n <= pow2 32 } -> GTot Type0

let well_formed_and_counter (#a:e_alg)
  (s: state a)
  (h: HS.mem{invariant s h})
  (n: nat { n <= pow2 32 }):
  GTot _
=
  well_formed s h /\ bounded_counter s h n

// Note: this function relies implicitly on the fact that we are running with
// code/lib/kremlin and that we know that machine integers and secret integers
// are the same. In the long run, we should standardize on a secret integer type
// in F*'s ulib and have evercrypt use it.
val update: #a:e_alg -> s:state a -> data:uint8_p -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed_and_counter s h0 1 /\
    B.live h0 data /\
    B.length data = blockLength a /\
    M.(loc_disjoint (footprint s h0) (loc_buffer data))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    well_formed_and_counter s h1 0 /\ (
    let r0 = repr s h0 in
    let r1 = repr s h1 in
    r1 == compress r0 (B.as_seq h0 data))))

val update_multi: #a:e_alg -> s:state a -> data:uint8_p -> n:UInt32.t -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed_and_counter s h0 (v n) /\
    B.live h0 data /\
    B.length data = blockLength a * v n /\
    M.(loc_disjoint (footprint s h0) (loc_buffer data))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    well_formed_and_counter s h1 0 /\ (
    let r0 = repr s h0 in 
    let r1 = repr s h1 in
    r1 == hash2 r0 (B.as_seq h0 data))))


(* see suffix and suffixLength 
// The maximum number of bytes for the input.
let max_input_length (a: e_alg): GTot _ =
  match G.reveal a with
  | SHA256 ->
      EverCrypt.Spec.SHA2_256.max_input_len_8
  | SHA384 ->
      EverCrypt.Spec.SHA2_384.max_input_len_8

// The size, in bytes, it takes to encode the number of bytes in the message.
let size_length (a: e_alg): GTot _ =
  match G.reveal a with
  | SHA384 | SHA512 -> 8 
  | _               -> 4

// For the last (possibly partial) block, in so far as I understand, we
// concatenate the last chunk of data, insert a byte 0x01, then encode the length.
let last_data_fits (a: e_alg) (length: nat): GTot _ =
  length + size_length a + 1 < 2 * block_size a
*) 

(*
// Note: conjunction of well_formed and last_data_fits allows deriving the
// specific precondition for update_last.
let update_last_spec (#a:e_alg)
  (s:state a)
  (h0: HS.mem{invariant s h0})
  (h1: HS.mem{invariant s h1})
  (data: bytes{
    well_formed_and_counter s h0 2 /\ 
    last_data_fits a (Seq.length data)}):
  GTot _
=
  let r0 = repr s h0 in
  let r1 = repr s h1 in
  
  let counter0 = r0.counter in
  let len0 = counter0 * block_size a in
  match G.reveal a with
  | SHA256 ->
      r1.hash = EverCrypt.Spec.SHA2_256.update_last r0.hash len0 data
  | SHA384 ->
      r1.hash = EverCrypt.Spec.SHA2_384.update_last r0.hash len0 data
*)

// 18-03-05 note the *new length-passing convention!
// 18-03-03 it is best to let the caller keep track of lengths.
// 18-03-03 the last block is *never* complete so there is room for the 1st byte of padding.
val update_last: 
  #a:e_alg -> 
  s:state a -> 
  last:uint8_p {
    B.length last <= blockLength a } -> 
  total_len:UInt32.t {
    let l = v total_len in 
    l <= maxLength a /\
    B.length last = l % blockLength a } -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed_and_counter s h0 2 /\
    B.live h0 last /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    well_formed s h1 /\ (
    let r0 = repr s h0 in
    let r1 = repr s h1 in
    let last0 = B.as_seq h0 last in 
    let rawbytes = Seq.append last0 (suffix a (v total_len)) in
    Seq.length rawbytes % blockLength a = 0 (*required by hash2; otherwise brittle*) /\ 
    r1 == hash2 #a r0 rawbytes)))

val finish: #a:e_alg -> s:state a -> dst:uint8_p -> Stack unit
  (requires (fun h0 ->
    invariant s h0 /\
    well_formed s h0 /\
    B.live h0 dst /\
    B.length dst = tagLength a /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst))))
  (ensures (fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst) h0 h1) /\
    footprint s h0 == footprint s h1 /\ 
    B.as_seq h1 dst = extract (repr s h0)))

val hash: a:alg -> dst:uint8_p -> input:uint8_p -> len:uint32_t -> Stack unit
  (requires (fun h0 ->
    let a = Ghost.hide a in 
    B.live h0 dst /\
    B.live h0 input /\
    B.length input = v len /\
    v len < maxLength a /\
    B.length dst = tagLength a /\
    M.(loc_disjoint (loc_buffer input) (loc_buffer dst))))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst = spec (Ghost.hide a) (B.as_seq h0 input)))
