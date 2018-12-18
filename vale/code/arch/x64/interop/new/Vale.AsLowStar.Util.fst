module Vale.AsLowStar.Util
open Vale.AsLowStar.Signature
module B = LowStar.Buffer
module BV = LowStar.BufferView
module HS = FStar.HyperStack
module IA = Interop_assumptions
module IS = X64.Interop_s
module ME = X64.Memory
module MS = X64.Machine_s
module V = X64.Vale.Decls
module VS = X64.Vale.State

let buf_t = a:Type & B.buffer a

[@IS.reduce]
let buf (#a:Type) (b:B.buffer a) : buf_t = (|a, b|)

/// Several internal forms that are also supposed to be normalized away during typechecking
/// DO NOT USE THESE DIRECTLY: use their counterparts marked "unfold" below
[@IS.reduce]
private
let rec all_disjoint_from (a:B.loc) (l:list B.loc) =
  match l with
  | [] -> True
  | hd::tl -> B.loc_disjoint a hd /\ all_disjoint_from a tl

[@IS.reduce]
private
let rec pairwise_disjoint (l:list B.loc) =
  match l with
  | [] -> True
  | hd::tl -> all_disjoint_from hd tl /\ pairwise_disjoint tl

[@IS.reduce]
private
let rec all_live_buf (h:HS.mem) (l:list buf_t) =
  match l with
  | [] -> True
  | (|_, b|)::tl -> B.live h b /\ all_live_buf h tl

[@IS.reduce]
let rec loc_union_l' (l:list B.loc) : GTot B.loc =
  match l with
  | [] -> B.loc_none
  | hd::tl -> B.loc_union hd (loc_union_l' tl)


/// USE THESE WRAPPERS TO ENABLE NORMALIZATION AT TYPECHECKING TME
unfold
let all_live (h:HS.mem) (l:list buf_t) :GTot Type0 = IS.normal (all_live_buf h l)

unfold
let all_disjoint (l:list B.loc) = IS.normal (pairwise_disjoint l)

unfold
let loc_union_l (l:list B.loc) = IS.normal (loc_union_l' l)

////////////////////////////////////////////////////////////////////////////////

let view_n (x:ME.typ) =
  let open ME in
  match x with
  | TBase TUInt8 -> 1
  | TBase TUInt16 -> 2
  | TBase TUInt32 -> 4
  | TBase TUInt64 -> 8
  | TBase TUInt128 -> 16

let lowstar_buffer (t:ME.typ) = b:B.buffer UInt8.t{B.length b % view_n t == 0}

let buffer_equiv (t:ME.typ)
  : Lemma (ME.buffer t == lowstar_buffer t)
  = admit()

[@IS.reduce]
let coerce (x:'a{'a == 'b}) : 'b = x

[@IS.reduce]
let as_lowstar_buffer (#t:ME.typ) (x:ME.buffer t)
  : Tot (lowstar_buffer t)
  = buffer_equiv t;
    coerce x

[@IS.reduce]
let as_vale_buffer (#t:ME.typ) (x:lowstar_buffer t)
  : Tot (b:ME.buffer t)
  = buffer_equiv t;
    coerce x

let buffer_addr_is_nat64 (#t:ME.typ) (x:ME.buffer t) (s:VS.state)
  : Lemma (0 <= ME.buffer_addr x VS.(s.mem) /\ ME.buffer_addr x VS.(s.mem) < pow2 64)
  = admit()
