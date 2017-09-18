module Box.Plain

open FStar.HyperStack.All

module ST = FStar.HyperStack.ST

open FStar.Seq
open FStar.Buffer

open FStar.Monotonic.RRef

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module H8  = Hacl.UInt8
module H32 = Hacl.UInt32
module H64 = Hacl.UInt64

assume val seq8_to_h64: s:seq H8.t{Seq.length s = 8} -> Tot H64.t

type nonce = s:seq H8.t{Seq.length s = 24}
type sid = s:seq H8.t{Seq.length s = 16}
type sn  = H64.t // Sequence number

type msg (n:nonce) = b:buffer H8.t

noeq type entry = | Entry: sid:sid -> fs:FileIO.Types.file_stat -> content:Seq.seq H8.t -> entry

type log = list entry


val contains_entry: log -> sid -> Tot bool
let contains_entry l s =
  match l with
  | 



let rec log_cmp (a:log) (b:log) : GTot Type0 =
  if List.Tot.length a > List.Tot.length b then false
  else if List.Tot.length a = List.Tot.length b then (
    match a, b with
    | hd::tl, hd'::tl' -> hd == hd' /\ log_cmp (List.Tot.tl a) (List.Tot.tl a)
    | _ -> a == b 
  ) else log_cmp a (List.Tot.tl b)

val log_cmp_reflexive: (a:log) -> Lemma
  (requires True)
  (ensures (log_cmp a a))
  [SMTPat (log_cmp a a)]
let rec log_cmp_reflexive a =
  if List.Tot.length a <= 1 then ()
  else log_cmp_reflexive (List.Tot.tl a)

val log_cmp_transitive: a:log -> b:log -> c:log -> Lemma
  (requires True)
  (ensures (log_cmp a b /\ log_cmp b c ==> log_cmp a c))
let log_cmp_transitive a b c = admit() // TODO

val log_cmp_monotonic: unit -> Lemma (Monotonic.RRef.monotonic log log_cmp)
let log_cmp_monotonic () = admit()


let log_ref (r:HyperHeap.rid{HyperStack.is_eternal_region r}) = Monotonic.RRef.m_rref r log log_cmp


(* type valid_msg #nonce h (m:msg nonce) : GTot Type0 = *)
(*   let sid = Seq.slice nonce 0 16 in *)
(*   let sn  = seq8_to_h64 (Seq.slice nonce 16 24) in *)
(*   (witnessed (fun h -> List.Tot.mem (m_sel h log) contains log sid *)

