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
// 18-07-13 move to EverCrypt.Helpers?
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

// kept only for functional backward compatibility,
// never assumed to be secure.
type broken_alg = a:alg {a = MD5 \/ a = SHA1}

val string_of_alg: alg -> C.String.t


/// HMAC/HKDF ALGORITHMS; secure_api makes security assumptions only
/// for constructions based on those.
///
type alg13 = a:alg {a=SHA256 \/ a=SHA384 \/ a=SHA512}

// do not use as argument of ghost functions
type e_alg = Ghost.erased alg


/// Lengths for input blocks and output tags, in bytes.

let blockLen = function
  | MD5 | SHA1 | SHA224 | SHA256 ->  64ul
  | SHA384 | SHA512              -> 128ul
//| SHAKE128 _ -> 168 | SHAKE256 _ -> 136

let blockLength (a:alg): GTot nat = v (blockLen a)
type block (a:alg) = lbytes (blockLength a)
type blocks (a:alg) = b:bytes {Seq.length b % blockLength a = 0}

let maxTagLen = 64ul
let tagLen (a:alg) : Tot (n:UInt32.t {n <= maxTagLen}) =
  match a with
  | MD5    -> 16ul
  | SHA1   -> 20ul
  | SHA224 -> 28ul // truncated SHA256
  | SHA256 -> 32ul
  | SHA384 -> 48ul // truncated SHA512
  | SHA512 -> 64ul
let tagLength a: GTot nat = v (tagLen a)
let lemma_maxLen (a:alg) = assert_norm(tagLen a <= maxTagLen)

type tag (a:alg) = lbytes (tagLength a) 
type anyTag = lbytes (v maxTagLen)

/// Maximal input lengths (from hacl*); this is overly restrictive.

let maxLength: alg -> GTot nat = fun a -> pow2 61 - 1
noextract let lemma_maxLength (a: alg) = assert_norm (pow2 32 <= maxLength a)
noextract let hashable (a: alg) = b: bytes{ Seq.length b <= maxLength a }
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
noextract val acc (a:alg): Type0

(* sets the initial value of the accumulator *)
noextract val acc0 (#a:alg): acc a

(* hashes one block of data into the accumulator *)
// GTot makes noextract redundant.
noextract val compress: #a:alg -> acc a -> block a -> GTot (acc a)

(* extracts the tag from the (possibly larger) accumulator *)
noextract val extract: #a:alg -> acc a -> GTot (tag a)

// val hash2: #a:alg -> acc a -> b:bytes {length b % blockLength a = 0} -> acc a (decreases (length b))
noextract let rec hash2
  (#a:alg)
  (v:acc a)
  (b:blocks a) :
  GTot (acc a) (decreases (Seq.length b))
=
  if Seq.length b = 0 then v
  else
    let c,b = Seq.split b (blockLength a) in
    assert(Seq.length b % blockLength a = 0);
    hash2 (compress v c) b

//18-07-07 this verified interactively but not on the command line;
//18-07-07 I suspect the hacl* specs make it harder for Z3.
#set-options "--z3rlimit 100"
let lemma_compress
  (#a: alg)
  (a0: acc a)
  (c: block a) :
  Lemma (Seq.length c % blockLength a = 0 ==> compress a0 c == hash2 a0 c) = ()

//18-07-12 moved the proof to the .fst to prevent timeouts on the .fsti; now much slower.
val lemma_hash2: #a: alg -> a0: acc a -> b0: blocks a -> b1: blocks a -> Lemma
  (ensures
    Seq.length b0 % blockLength a = 0 /\
    Seq.length b1 % blockLength a = 0 /\
    Seq.length (Seq.append b0 b1) % blockLength a = 0 /\
    hash2 a0 (Seq.append b0 b1) == hash2 (hash2 a0 b0) b1)
  (decreases (Seq.length b0))

let hash0 (#a:alg) (b:blocks a): GTot (acc a) = hash2 (acc0 #a) b

/// PADDING AND LENGTH ENCODING
/// for convenience, we treat inputs as sequences of bytes, not bits.
/// but note that the suffix encodes the length in bits.
private noextract
let suffixLength (a:alg) (length:nat {length <= maxLength a}):
  GTot (n:nat{ (length + n) % blockLength a = 0 /\ n <= blockLength a + 9 })
=
  let blocklen = blockLength a in
  let lenlen = match a with | SHA384 | SHA512 -> 8 | _ -> 4 in
  let required =  length + 1 + lenlen in // minimal length after padding and encoding the length
  let zeros = // minimal extra padding for block alignment
    if required % blocklen = 0
    then 0
    else blocklen - (required % blocklen) in
    //was, harder to prove: required + blockLen a - ((required - 1) % blockLen a + 1) in
  1 + zeros + lenlen

val suffix: a:alg -> l:nat {l <= maxLength a} -> GTot (lbytes (suffixLength a l))

// would prefer to name it [hash] but already taken below
let spec (a:alg) (b:hashable a): GTot (tag a) =
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
/// ---------agile interface to hash specifications ----------------





module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies
module G = FStar.Ghost

open LowStar.BufferOps

// abstract implementation state
[@CAbstractStruct]
val state_s: alg -> Type0
let state alg = b:B.pointer (state_s alg) { B.freeable b }

// NS: note that the state is the first argument to the invariant so that we can
// do partial applications in pre- and post-conditions
val footprint_s: #a:alg -> state_s a -> GTot M.loc
let footprint (#a:alg) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

// TR: the following pattern is necessary because, if we generically
// add such a pattern directly on `loc_includes_union_l`, then
// verification will blowup whenever both sides of `loc_includes` are
// `loc_union`s. We would like to break all unions on the
// right-hand-side of `loc_includes` first, using
// `loc_includes_union_r`.  Here the pattern is on `footprint_s`,
// because we already expose the fact that `footprint` is a
// `loc_union`. (In other words, the pattern should be on every
// smallest location that is not exposed to be a `loc_union`.)

let loc_includes_union_l_footprint_s
  (l1 l2: M.loc) (#a: alg) (s: state_s a)
: Lemma
  (requires (
    M.loc_includes l1 (footprint_s s) \/ M.loc_includes l2 (footprint_s s)
  ))
  (ensures (M.loc_includes (M.loc_union l1 l2) (footprint_s s)))
  [SMTPat (M.loc_includes (M.loc_union l1 l2) (footprint_s s))]
= M.loc_includes_union_l l1 l2 (footprint_s s)

val invariant_s: (#a:alg) -> state_s a -> HS.mem -> Type0
let invariant (#a:alg) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s (B.get m s 0) m

//18-07-06 as_acc a better name? not really a representation
val repr: #a:alg -> 
  s:state a -> h:HS.mem { invariant s h } -> GTot (acc a)

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

// TR: this lemma is necessary to prove that the footprint is disjoint
// from any fresh memory location.

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant s m))
  (ensures (loc_in (footprint s m) m))
  [SMTPat (invariant s m)]

// TR: frame_invariant, just like all lemmas eliminating `modifies`
// clauses, should have `modifies_inert` as a precondition instead of
// `modifies`, in order to use it in all cases where a modifies clause
// is produced but should not be composed with `modifies_trans` for
// pattern reasons (e.g. push_frame, pop_frame)

// 18-07-12 why not bundling the next two lemmas?
val frame_invariant: #a:alg -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies_inert l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: alg)
  (l: M.loc)
  (s: state a)
  (h0 h1: HS.mem): Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies_inert l h0 h1))
  (ensures (
    footprint s h1 == footprint s h0))
=
  ()

val create: a:alg -> ST (state a)
  (requires fun h0 -> True)
  (ensures fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    fresh_loc (footprint s h1) h0 h1)

// we use exists b. hashing s h b as our stateful abstract
// invariant; the existence of b is used only to reason about the
// internal counter.
let hashing (#a:alg) (s: state a) (h: HS.mem) (b: bytes) =
  invariant s h /\
  Seq.length b % blockLength a = 0 /\
  repr s h == hash0 b

val init: #a:e_alg -> (
  let a = Ghost.reveal a in 
  s: state a -> ST unit
  (requires invariant s)
  (ensures fun h0 _ h1 ->
    hashing s h1 (Seq.empty #UInt8.t) /\ // implies repr s h1 == acc0 #a
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1))

// Note: this function relies implicitly on the fact that we are running with
// code/lib/kremlin and that we know that machine integers and secret integers
// are the same. In the long run, we should standardize on a secret integer type
// in F*'s ulib and have evercrypt use it.
val update:
  #a:e_alg -> 
  b: Ghost.erased bytes -> (
  let a = Ghost.reveal a in
  let b = Ghost.reveal b in 
  s:state a ->
  block:uint8_p {B.length block = blockLength a} ->
  Stack unit
  (requires fun h0 ->
    hashing s h0 b /\
    B.live h0 block /\
    M.(loc_disjoint (footprint s h0) (loc_buffer block)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    hashing s h1 (Seq.append b (B.as_seq h0 block))))
//  repr s h1 == compress (repr s h0) (B.as_seq h0 data)

// new calling convention: we pass the data length in bytes (rather
// than blocks). I also removed the counter invariant, assuming we
// will get rid of it.
val update_multi:
  #a:e_alg ->
  b: Ghost.erased bytes -> (
  let a = Ghost.reveal a in
  let b = Ghost.reveal b in 
  s:state a ->
  blocks:uint8_p {B.length blocks % blockLength a = 0} ->
  len: UInt32.t {v len = B.length blocks} ->
  Stack unit
  (requires fun h0 ->
    hashing s h0 b /\
    B.live h0 blocks /\
    M.(loc_disjoint (footprint s h0) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    hashing s h1 (Seq.append b (B.as_seq h0 blocks))))

// 18-03-05 note the *new* length-passing convention!
// 18-03-03 it is best to let the caller keep track of lengths.
// 18-03-03 the last block is *never* complete so there is room for the 1st byte of padding.
val update_last:
  #a:e_alg ->
  b:Ghost.erased bytes -> (
  let a = Ghost.reveal a in
  let b = Ghost.reveal b in 
  s:state a ->
  last:uint8_p {B.length last < blockLength a } ->
  total_len:UInt32.t {
    let l = v total_len in
    l = Seq.length b + B.length last /\
    l <= maxLength a } ->
  Stack unit
  (requires fun h0 ->
    hashing s h0 b /\
    B.live h0 last /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    let last0 = B.as_seq h0 last in
    let rawbytes = Seq.append last0 (suffix a (v total_len)) in
    Seq.length rawbytes % blockLength a = 0 /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    hashing s h1 (Seq.append b rawbytes)))

val finish:
  #a:e_alg -> (
  let a = Ghost.reveal a in 
  s:state a ->
  dst:uint8_p {B.length dst = tagLength a} ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 dst /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    B.as_seq h1 dst == extract (repr s h0)))

val free: 
  #a:e_alg -> (
  let a = Ghost.reveal a in 
  s:state a -> ST unit
  (requires fun h0 ->
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))

val hash:
  a:alg -> 
  dst:uint8_p {B.length dst = tagLength a} ->
  input:uint8_p ->
  len:uint32_t {B.length input = v len /\ v len <= maxLength a} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 dst /\
    B.live h0 input /\
    M.(loc_disjoint (loc_buffer input) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    M.(modifies (loc_buffer dst) h0 h1) /\
    B.as_seq h1 dst = spec a (B.as_seq h0 input))


