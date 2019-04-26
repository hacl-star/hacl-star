module Hacl.Impl.HKDF_SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

module SpecSHA2 = Spec.SHA2
module SpecHash = Spec.Hash
module SpecHMAC = Spec.HMAC

module Hash = Hacl.Hash.Definitions
module HMAC = Hacl.HMAC


inline_for_extraction noextract
let a = Spec.Hash.Definitions.SHA2_256

#set-options "--max_fuel 0 --max_ifuel 0"

val hkdf_extract:
    output: lbuffer uint8 (size (Spec.Hash.Definitions.hash_length a))
  -> salt: buffer uint8 {length salt <= Spec.Hash.Definitions.max_input_length a}
  -> slen: size_t{v slen == length salt}
  -> ikm: buffer uint8
  -> ilen: size_t{ v ilen == length ikm
                /\ length salt + length ikm + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a
                /\ Spec.Hash.Definitions.hash_length a + length ikm + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h salt /\ live h ikm
                 /\ disjoint output salt /\ disjoint output ikm))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_extract output salt slen ikm ilen =
  push_frame ();
  let hash_len = normalize_term(size (Spec.Hash.Definitions.hash_length a)) in
  let salt0 = create hash_len  (u8 0) in
  admit();
  (if slen = size 0 then begin
    HMAC.compute_sha2_256 output salt0 hash_len ikm ilen
  end else
    HMAC.compute_sha2_256 output salt slen ikm ilen);
  pop_frame()


#reset-options "--z3rlimit 25"

val hkdf_round0:
    output: lbuffer uint8 (size (Spec.Hash.Definitions.hash_length a))
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk + Spec.Hash.Definitions.block_length a < max_size_t}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.Hash.Definitions.block_length a + 1 < max_size_t
                /\ length prk + length info + 1 + Spec.Hash.Definitions.hash_length a + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_round0 output prk plen info ilen =
  push_frame ();
  let input = create (ilen +! 1ul) (u8 0) in
  update_sub #MUT #uint8 #(ilen +! 1ul) input (size 0) ilen info;
  upd input ilen (u8 1);
  HMAC.compute_sha2_256 output prk plen input (ilen +! 1ul);
  pop_frame ()


val hkdf_round:
    output: lbuffer uint8 (size (Spec.Hash.Definitions.hash_length a))
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk + Spec.Hash.Definitions.block_length a < max_size_t}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.Hash.Definitions.hash_length a +
		  Spec.Hash.Definitions.block_length a + 1 < max_size_t
                /\ length prk + length info + 1 + Spec.Hash.Definitions.hash_length a + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a}
  -> i:size_t{1 < v i /\ v i <= 255}
  -> ti: lbuffer uint8 (size (Spec.Hash.Definitions.hash_length a)) ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info /\ live h ti
                 /\ disjoint output prk /\ disjoint output info /\ disjoint output ti))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_round output prk plen info ilen i ti =
  let hash_len = normalize_term(size (Spec.Hash.Definitions.hash_length a)) in
  push_frame ();
  let input = create (hash_len +! ilen +! 1ul) (u8 0) in
  update_sub input 0ul hash_len ti;
  update_sub #MUT #uint8 #(hash_len +! ilen +! 1ul) input hash_len ilen info;
  upd #uint8 #(hash_len +! ilen +! 1ul) input (hash_len +! ilen) (to_u8 (size_to_uint32 i));
  HMAC.compute_sha2_256 output prk plen input (hash_len +! ilen +! 1ul);
  pop_frame ()


#reset-options "--z3rlimit 500"

val hkdf_expand:
    output: buffer uint8
  -> prk: buffer uint8
  -> plen: size_t{v plen == length prk /\ length prk + Spec.Hash.Definitions.block_length a < max_size_t}
  -> info: buffer uint8
  -> ilen: size_t{ v ilen == length info
                /\ length info + Spec.Hash.Definitions.hash_length a +
		  Spec.Hash.Definitions.block_length a + 1 < max_size_t
                /\ length prk + length info + 1 + Spec.Hash.Definitions.hash_length a + Spec.Hash.Definitions.block_length a <= Spec.Hash.Definitions.max_input_length a}
  -> len: size_t{ v len == length output
               /\ v len + Spec.Hash.Definitions.hash_length a <= max_size_t
               /\ v len / (Spec.Hash.Definitions.hash_length a) + 2 <= 255} ->
  Stack unit
  (requires (fun h -> live h output /\ live h prk /\ live h info
                 /\ disjoint output prk /\ disjoint output info))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_expand output prk plen info ilen len =
  push_frame ();
  let hash_len = normalize_term(size (Spec.Hash.Definitions.hash_length a)) in
  let n : size_t = len /. hash_len +. 1ul in
  let t = create (n *. hash_len) (u8 0) in
  let t0 = sub t (size 0) hash_len in
  (* Compute T(0) *)
  hkdf_round0 t0 prk plen info ilen;
  (* Compute T(1) ... T(N)*)
  assert(v n - 1 + 2 <= 255);
  let h0 = ST.get () in
  loop_range_nospec #h0 (size 2) (n -. 1ul) t
    (fun i ->
       let ti0 = sub t ((i -. 2ul) *. hash_len) hash_len in
       let ti1 = sub t ((i -. 1ul) *. hash_len) hash_len in
       hkdf_round ti1 prk plen info ilen i ti0
    );
  let res = sub t (size 0) len in
  copy output res;
  pop_frame ()



val hkdf_build_label:
    output: buffer uint8
  -> secret: buffer uint8
  -> label: buffer uint8
  -> llen: size_t{length label == v llen}
  -> context: buffer uint8
  -> clen: size_t{length context == v clen}
  -> len: size_t{numbytes U16 + numbytes U8 + v llen + numbytes U8 + v clen <= max_size_t /\
    length output >= numbytes U16 + numbytes U8 + v llen + numbytes U8 + v clen /\
    v len < maxint U16
  } ->
  Stack unit
  (requires (fun h -> live h secret /\ live h label /\ live h context /\ live h output /\
    disjoint output label /\ disjoint output context
  ))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_build_label output secret label llen context clen len =
  let pos_len: size_t = 0ul in
  let sz_len: size_t = size (numbytes U16) in
  let pos_llen: size_t = pos_len +. sz_len in
  let sz_llen: size_t = size (numbytes U8) in
  let pos_label: size_t = pos_llen +. sz_llen in
  let pos_clen: size_t = pos_label +. llen in
  let sz_clen: size_t = size (numbytes U8) in
  let pos_context: size_t = pos_clen +. sz_clen in
  let vout = sz_len +! sz_llen +! llen +! sz_clen +! clen in
  assert(v vout <= length output);
  let output = LowStar.Buffer.sub output (size 0) vout in
  uint_to_bytes_be #U16 #SEC (sub #MUT #uint8 #vout output pos_len sz_len) (to_u16 len);
  uint_to_bytes_be #U8 #SEC (sub #MUT #uint8 #vout output pos_llen sz_llen) (to_u8 llen);
  update_sub #MUT #uint8 #vout output pos_label llen label;
  uint_to_bytes_be #U8 #SEC (sub #MUT #uint8 #vout output pos_clen sz_clen) (to_u8 clen);
  update_sub #MUT #uint8 #vout output pos_context clen context


val hkdf_expand_label:
    output: buffer uint8
  -> secret: lbuffer uint8 (size 32)
  -> label: buffer uint8
  -> llen: size_t{length label == v llen}
  -> context: buffer uint8
  -> clen: size_t{length context == v clen}
  -> len: size_t{numbytes U16 + numbytes U8 + v llen + numbytes U8 + v clen + v len +
    Spec.Hash.Definitions.hash_length a + 1 + Spec.Hash.Definitions.block_length a < max_size_t /\
    length output == v len /\ v len < maxint U16 /\
    v len / (Spec.Hash.Definitions.hash_length a) + 2 <= 255
  } ->
  Stack unit
  (requires (fun h -> live h output /\ live h secret /\ live h label /\ live h context /\
    disjoint output secret /\ disjoint output label /\ disjoint output context
  ))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_expand_label output secret label llen context clen len =
  push_frame();
  let sz_len: size_t = size (numbytes U16) in
  let sz_llen: size_t = size (numbytes U8) in
  let sz_clen: size_t = size (numbytes U8) in
  let ilen = sz_len +! sz_llen +! llen +! sz_clen +! clen in
  let ilabel = create ilen (u8 0) in
  let ilabel : buffer uint8 = ilabel in
  hkdf_build_label ilabel secret label llen context clen len;
  assert_norm(32 + pow2 32 + 1000 < pow2 61);
  hkdf_expand output secret (size 32) ilabel ilen len;
  pop_frame ()


(* let hkdf_expand_derive_secret a secret label context = *)
(*   let loghash = Hash.hash a context in *)
(*   hkdf_expand_label a secret label loghash (Hash.size_hash a) *)
