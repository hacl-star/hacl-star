module EverCrypt.Helpers

module B = LowStar.Buffer
module LM = LowStar.Modifies

open FStar.HyperStack.ST

/// Small helpers
inline_for_extraction noextract
let (!$) = C.String.((!$))

/// For the time being, we do not write any specifications and just try to reach
/// agreement on calling conventions. A series of convenient type abbreviations
/// follows.

effect Stack_ (a: Type) = Stack a (fun _ -> True) (fun _ _ _ -> True)

let uint8_t = UInt8.t
let uint16_t = UInt16.t
let uint32_t = UInt32.t
let uint64_t = UInt64.t

let uint8_p = B.buffer uint8_t
let uint16_p = B.buffer uint16_t
let uint32_p = B.buffer uint32_t
let uint64_p = B.buffer uint64_t

let uint8_pl (l:nat) = p:uint8_p {B.length p = l}
let uint8_l (p:uint8_p) = l:UInt32.t {B.length p = UInt32.v l}

let len_of #a (x:B.buffer a) = u:uint32_t{B.length x = UInt32.v u}

/// Some helpers for manipulating buffers, locations and predicates on them

/// An attribute to mark some symbols for reduction
let __reduce__ = ()
let normal #a (x:a) = FStar.Pervasives.norm [zeta; iota; simplify; delta_attr [`%__reduce__]] x

/// Several internal forms that are also supposed to be normalized away during typechecking
/// DO NOT USE THESE DIRECTLY: use their counterparts marked "unfold" below
[@__reduce__]
let rec all_disjoint_from (a:LM.loc) (l:list LM.loc) =
  match l with
  | [] -> True
  | hd::tl -> LM.loc_disjoint a hd /\ all_disjoint_from a tl

[@__reduce__]
let rec pairwise_disjoint (l:list LM.loc) =
  match l with
  | [] -> True
  | hd::tl -> all_disjoint_from hd tl /\ pairwise_disjoint tl

let buf_t = a:Type & B.buffer a
module HS = FStar.HyperStack
[@__reduce__]
let rec all_live_buf (h:HS.mem) (l:list buf_t) =
  match l with
  | [] -> True
  | (|_, b|)::tl -> LM.live h b /\ all_live_buf h tl

[@__reduce__]
let buf (#a:Type) (b:B.buffer a) : buf_t = (|a, b|)

[@__reduce__]
let rec as_buf_t_l' (l:list uint8_p) : list buf_t =
  match l with
  | [] -> []
  | hd::tl -> buf hd :: as_buf_t_l' tl

[@__reduce__]
let rec as_loc_l' (l:list uint8_p) : GTot (list LM.loc) =
  match l with
  | [] -> []
  | hd::tl -> LM.loc_buffer hd :: as_loc_l' tl


[@__reduce__]
let rec loc_union_l' (l:list LM.loc) : GTot LM.loc =
  match l with
  | [] -> LM.loc_none
  | hd::tl -> LM.loc_union hd (loc_union_l' tl)

/// USE THESE WRAPPERS TO ENABLE NORMALIZATION AT TYPECHECKING TME
unfold
let all_live (h:HS.mem) (l:list buf_t) :GTot Type0 = normal (all_live_buf h l)

unfold
let as_buf_t_l (l:list uint8_p) = normal (as_buf_t_l' l)

unfold
let as_loc_l (l:list uint8_p) = normal (as_loc_l' l)

unfold
let all_disjoint (l:list LM.loc) = normal (pairwise_disjoint l)

unfold
let loc_union_l (l:list LM.loc) = normal (loc_union_l' l)
