(* Agile HMAC *)
module EverCrypt.HMAC
/// 18-03-03 Do we get specialized extraction of HMAC?

open EverCrypt.Hash

let ha = a:alg {a = SHA1 \/ a = SHA256 \/ a = SHA384 \/ a = SHA512}

//18-07-09 rename to Hash's bytes and lbytes?
noextract
type bseq = Seq.seq UInt8.t
noextract
let lbseq (l:nat) = b:bseq {Seq.length b = l}

let keysized (a:alg) (l:nat) =
  l <= maxLength a /\
  l + blockLength a < pow2 32

(* ghost specification; its algorithmic definition is given in the .fst *)
val hmac:
  a: alg -> //18-07-09 can't mix refinements and erasure??
  key: bseq{ keysized a (Seq.length key) } ->
  data: bseq{ Seq.length data + blockLength a <= maxLength a } ->
  GTot (lbseq (tagLength a))

open FStar.HyperStack.ST
open LowStar.Buffer
open EverCrypt.Helpers

#reset-options "--max_fuel 0  --z3rlimit 20"
(* implementation, relying on 3 variants of SHA2 supported by HACL*;
   we tolerate overlaps between tag and data.
   (we used to require [disjoint data tag])
*)
val compute:
  a: ha ->
  tag: uint8_pl (tagLength a) ->
  key: uint8_p{ keysized a (length key) /\ disjoint key tag } ->
  keylen: UInt32.t{ UInt32.v keylen = length key } ->
  data: uint8_p{ length data + blockLength a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = length data } ->
  ST unit
  (requires fun h0 -> live h0 tag /\ live h0 key /\ live h0 data)
  (ensures fun h0 _ h1 ->
    live h1 tag /\
    live h1 key /\
    live h1 data /\
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\
    length data + blockLength a <= maxLength a /\ (* required for subtyping the RHS below *)
    as_seq h1 tag == hmac a (as_seq h0 key) (as_seq h0 data))

//18-07-13 pick uniform names? hash{spec} vs compute{hmac}
