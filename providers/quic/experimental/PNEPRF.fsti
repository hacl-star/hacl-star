module PNEPRF
module HS = FStar.HyperStack

module I = Crypto.Indexing
module U32 = FStar.UInt32
module U128 = FStar.UInt128

open FStar.HyperStack
open FStar.Seq
open FStar.Monotonic.Seq
open FStar.Error
open FStar.Bytes

open FStar.Bytes
open FStar.UInt32
open Mem
open Pkg


//let pnlen = 4

type prfid = Flag.prfid

type sample = lbytes 16

type mask = lbytes 5

let safePNE (j:prfid) = Flag.safePNE j

val table_region : rgn


type entry (j:prfid) =
  | Entry :
    s:sample ->
    m:mask ->
    entry j

val pne_state : (j:prfid) -> Type0

val table : (#j:prfid) -> (st:pne_state j) -> (h:mem) -> GTot (Seq.seq (entry j))

val footprint : #j:prfid -> st:pne_state j -> GTot (subrgn table_region)

val frame_table: #j:prfid -> st:pne_state j -> l:Seq.seq (entry j) ->
  h0:mem -> s:Set.set rid -> h1:mem ->
  Lemma
    (requires
      safePNE j /\
      table st h0 == l /\
      modifies s h0 h1 /\
      Set.disjoint s (Set.singleton (footprint st)))
    (ensures table st h1 == l)

let sample_filter (j:prfid) (s:sample) (e:entry j) : bool =
  Entry?.s e = s

let entry_for_sample (#j:prfid) (s:sample) (st:pne_state j) (h:mem) :
  GTot (option (entry j)) =
  Seq.find_l (sample_filter j s) (table st h)
  
let fresh_sample (#j:prfid) (s:sample) (st:pne_state j) (h:mem) :
  GTot bool =
  None? (entry_for_sample s st h)

let find_sample (#j:prfid) (s:sample) (st:pne_state j) (h:mem) :
  GTot bool =
  Some? (entry_for_sample s st h)


let sample_mask_filter (j:prfid) (s:sample) (m:mask) (e:entry j) : bool =
  Entry?.s e = s && Entry?.m e = m

let entry_for_sample_mask (#j:prfid) (s:sample) (m:mask) (st:pne_state j) (h:mem) :
  GTot (option (entry j)) =
  Seq.find_l (sample_mask_filter j s m) (table st h)
  
let find_sample_mask (#j:prfid) (s:sample) (m:mask) (st:pne_state j) (h:mem) :
  GTot bool =
  Some? (entry_for_sample_mask s m st h)


val create (j:prfid) : ST (pne_state j)
  (requires fun _ -> True)
  (ensures fun h0 st h1 ->
    modifies_none h0 h1 /\
    table st h1 == Seq.empty)

val compute :
  (#j:prfid) ->
  (st:pne_state j) ->
  (s:sample) ->
  ST (mask)
  (requires fun h0 -> True)
  (ensures fun h0 m h1 ->
    modifies_one (footprint st) h0 h1 /\
    (safePNE j ==>
      (match (entry_for_sample s st h0) with
        | None -> table st h1 == Seq.snoc (table st h0) (Entry s m)
        | Some (Entry _ m') -> m = m')))



//let sample_cipher (c:cipher) : s:sample =
//  Bytes.slice c 0ul 16ul
