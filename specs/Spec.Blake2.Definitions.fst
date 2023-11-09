module Spec.Blake2.Definitions

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.Sequence
open Lib.ByteSequence

#set-options "--z3rlimit 50"

type alg =
  | Blake2S
  | Blake2B

let alg_inversion_lemma (a:alg) : Lemma (a == Blake2S \/ a == Blake2B) = ()

inline_for_extraction
let wt (a:alg) : t:inttype{unsigned t} =
  match a with
  | Blake2S -> U32
  | Blake2B -> U64

inline_for_extraction
let rounds (a:alg) =
  match a with
  | Blake2S -> 10
  | Blake2B -> 12

(* Algorithm parameters *)
inline_for_extraction let size_hash_w : size_nat = 8
inline_for_extraction let size_block_w : size_nat = 16
inline_for_extraction let size_word (a:alg) : size_nat = numbytes (wt a)
inline_for_extraction let size_block (a:alg) : size_nat = size_block_w * (size_word a)
inline_for_extraction let size_ivTable : size_nat = 8
inline_for_extraction let size_sigmaTable : size_nat = 160

inline_for_extraction let max_key (a:alg) =
  match a with
  | Blake2S -> 32
  | Blake2B -> 64
inline_for_extraction let max_output (a:alg) =
  match a with
  | Blake2S -> 32
  | Blake2B -> 64


(* Definition of base types *)
inline_for_extraction
unfold let limb_inttype (a:alg) =
  match (wt a) with
  | U32 -> U64
  | U64 -> U128

inline_for_extraction
unfold type word_t (a:alg) = uint_t (wt a) SEC

inline_for_extraction
let zero (a:alg) : word_t a=
  match a with
  | Blake2S -> u32 0
  | Blake2B -> u64 0

inline_for_extraction
unfold let row (a:alg) = lseq (word_t a) 4

inline_for_extraction
let zero_row (a:alg) : row a = create 4 (zero a)

inline_for_extraction
let load_row (#a:alg) (s:lseq (word_t a) 4) : row a =
  createL [s.[0]; s.[1]; s.[2]; s.[3]]

inline_for_extraction
let create_row (#a:alg) x0 x1 x2 x3 : row a =
  createL [x0;x1;x2;x3]

inline_for_extraction
unfold let state (a:alg) = lseq (row a) 4

inline_for_extraction
let salt_length (a:alg) : size_nat =
  match a with
  | Blake2S -> 8
  | Blake2B -> 16

inline_for_extraction
let personal_length (a:alg) : size_nat =
  match a with
  | Blake2S -> 8
  | Blake2B -> 16

noeq
type blake2s_params = {
  digest_length: uint8;
  key_length: uint8;
  fanout: uint8;
  depth: uint8;
  leaf_length: uint32;
  node_offset: uint32;
  xof_length: uint16;
  node_depth: uint8;
  inner_length: uint8;
  salt: lseq uint8 (salt_length Blake2S);
  personal: lseq uint8 (personal_length Blake2S);
}

(* Need these helpers to cleanly work around field shadowing *)

inline_for_extraction
let set_blake2s_digest_length
  (p: blake2s_params)
  (nn: size_nat{1 <= nn /\ nn <= max_output Blake2S})
  : blake2s_params =
  {p with digest_length = u8 nn}

inline_for_extraction
let set_blake2s_key_length
  (p: blake2s_params)
  (kk: size_nat{kk <= max_key Blake2S})
  : blake2s_params =
  {p with key_length = u8 kk}

inline_for_extraction
let get_blake2s_salt (p:blake2s_params) = p.salt

inline_for_extraction
let get_blake2s_personal (p:blake2s_params) = p.personal

noeq
type blake2b_params = {
  digest_length: uint8;
  key_length: uint8;
  fanout: uint8;
  depth: uint8;
  leaf_length: uint32;
  node_offset: uint32;
  xof_length: uint32;
  node_depth: uint8;
  inner_length: uint8;
  // Blake2b also contains 14 reserved bytes here, but they seem
  // unused and to only contain zeros, hence we do not expose them
  salt: lseq uint8 (salt_length Blake2B);
  personal: lseq uint8 (personal_length Blake2B);
}

inline_for_extraction
let blake2_params (a: alg) =
  match a with
  | Blake2S -> blake2s_params
  | Blake2B -> blake2b_params

inline_for_extraction
let set_digest_length (#a: alg)
  (p: blake2_params a)
  (nn: size_nat{1 <= nn /\ nn <= max_output a})
  : blake2_params a =
  match a with
  | Blake2S -> set_blake2s_digest_length p nn
  | Blake2B -> {p with digest_length = u8 nn}

inline_for_extraction
let set_key_length (#a: alg)
  (p: blake2_params a)
  (kk: size_nat{kk <= max_key a})
  : blake2_params a =
  match a with
  | Blake2S -> set_blake2s_key_length p kk
  | Blake2B -> {p with key_length = u8 kk}

inline_for_extraction
let get_salt (#a: alg) (p: blake2_params a) : lseq uint8 (salt_length a) =
  match a with
  | Blake2S -> get_blake2s_salt p
  | Blake2B -> p.salt

inline_for_extraction
let get_personal (#a: alg) (p: blake2_params a) : lseq uint8 (personal_length a) =
  match a with
  | Blake2S -> get_blake2s_personal p
  | Blake2B -> p.personal

let blake2s_default_params: blake2s_params =
  { digest_length = u8 32;
    key_length = u8 0;
    fanout = u8 1;
    depth = u8 1;
    leaf_length = u32 0;
    node_offset = u32 0;
    xof_length = u16 0;
    node_depth = u8 0;
    inner_length = u8 0;
    salt = create 8 (u8 0);
    personal = create 8 (u8 0);
  }

let blake2b_default_params: blake2b_params =
  { digest_length = u8 64;
    key_length = u8 0;
    fanout = u8 1;
    depth = u8 1;
    leaf_length = u32 0;
    node_offset = u32 0;
    xof_length = u32 0;
    node_depth = u8 0;
    inner_length = u8 0;
    salt = create 16 (u8 0);
    personal = create 16 (u8 0);
  }

inline_for_extraction
let blake2_default_params (a: alg) : blake2_params a =
  match a with
  | Blake2S -> blake2s_default_params
  | Blake2B -> blake2b_default_params

inline_for_extraction
type pub_word_t (a:alg) = uint_t (wt a) PUB

inline_for_extraction
type limb_t (a:alg) : Type0 = uint_t (limb_inttype a) SEC

inline_for_extraction
let max_limb (a:alg) = maxint (limb_inttype a)

inline_for_extraction
let nat_to_word (a:alg) (x:size_nat) : word_t a =
  match (wt a) with
  | U32 -> u32 x
  | U64 -> u64 x

inline_for_extraction
let nat_to_limb (a:alg) (x:nat{x <= max_limb a}) : xl:limb_t a{uint_v xl == x} =
  match (wt a) with
  | U32 -> u64 x
  | U64 -> let h = u64 (x / pow2 64) in
	  let l = u64 (x % pow2 64) in
	  (to_u128 h <<. 64ul) +! to_u128 l

inline_for_extraction
let word_to_limb (a:alg) (x:word_t a{uint_v x <= max_limb a}) : xl:limb_t a{uint_v xl == uint_v x} =
  match (wt a) with
  | U32 -> to_u64 x
  | U64 -> to_u128 x

inline_for_extraction
let limb_to_word (a:alg) (x:limb_t a) : word_t a =
  match (wt a) with
  | U32 -> to_u32 x
  | U64 -> to_u64 x

unfold let rtable_t (a:alg) = lseq (rotval (wt a)) 4

type sigma_elt_t = n:size_t{size_v n < 16}
type list_sigma_t = l:list sigma_elt_t{List.Tot.length l == 160}

(* Algorithms types *)
type block_s (a:alg) = lseq uint8 (size_block a)
type block_w (a:alg) = lseq (word_t a) 16
type idx_t = n:size_nat{n < 16}

let row_idx = n:nat {n < 4}

inline_for_extraction
let ( ^| ) (#a:alg) (r1:row a) (r2:row a) : row a =
  map2 ( ^. ) r1 r2

inline_for_extraction
let ( +| ) (#a:alg) (r1:row a) (r2:row a) : row a =
  map2 ( +. ) r1 r2

inline_for_extraction
let ( >>>| ) (#a:alg) (r1:row a) (r:rotval (wt a)) : row a =
  map #(word_t a) (rotate_right_i r) r1

inline_for_extraction
let rotr (#a:alg) (r1:row a) (r:row_idx) : row a =
  createi 4 (fun i -> r1.[(i+r)%4])
