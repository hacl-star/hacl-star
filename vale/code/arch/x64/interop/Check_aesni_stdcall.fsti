module Check_aesni_stdcall

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Types_s

open X64.CPU_Features_s

let pre_cond (h:HS.mem) = True

let post_cond (h:HS.mem) (h':HS.mem) (ret_val:UInt64.t) =
  (UInt64.v ret_val) <> 0 ==> aesni_enabled && pclmulqdq_enabled

let full_post_cond (h:HS.mem) (h':HS.mem) (ret_val:UInt64.t) =
  post_cond h h' ret_val /\
  M.modifies (M.loc_none) h h'

[@ (CCConv "stdcall") ]
val check_aesni_stdcall (u:unit) : Stack UInt64.t
	(requires (fun h -> pre_cond h ))
	(ensures (fun h0 ret_val h1 -> full_post_cond h0 h1 ret_val))
