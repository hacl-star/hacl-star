module Lib.Poly

open Lib.IntTypes
open Lib.Sequence

open FStar.Classical
open FStar.Tactics

open Lib.Arithmetic.Group
open Lib.Arithmetic.Ring

//open Lib.NumericTypes

module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators

type seq (a:Type0) = Seq.seq a
type is_poly (#a:Type0) (p:seq a) = bool

type poly_t (a:Type0) = p:seq a{is_poly p}
//type poly_t_ (a:Type0) = |Poly (seq a)
type poly (a:Type0) (len:size_nat) = p:lseq a len{is_poly p}
#reset-options


let poly_add (#a:Type0) [| ring a |] (#n:size_nat) (#m:size_nat) (x:poly a n) (y:poly a m) : poly_t a =
  let k = if n > m then n else m in
  Loops.repeati m (fun i acc -> upd acc i (plus #a acc.[i] y.[i])) (Loops.repeati n (fun i acc -> upd acc i (plus #a acc.[i] x.[i])) (create k zero))

let poly_mul (#a:Type0) [| ring a |] (#n:size_nat) (#m:size_nat{n+m <= max_size_t}) (x:poly a n) (y:poly a m) : poly a (n+m) =
  Loops.repeati n (fun i acc -> Loops.repeati m (fun j acc -> upd acc (i+j) (plus #a acc.[i+j] (Lib.Arithmetic.Ring.mul #a x.[i] y.[j]))) acc) (create (n+m) zero)

#reset-options
(*let mod_zero (#a:Type0) [| ring a |] (#n:size_nat) : poly a n = 
    let z : lseq a n = create n zero in let b = is_poly z in
    let z2 = z in
 z2
*)
let mod_poly_add (#a:Type0) [| ring a |] (#n:size_nat) (x:poly a n) (y:poly a n) : poly a n =
  Lib.Arithmetic.Ring.Sequence.plus_lseq x y

let lemma_mod_poly_add_assoc (#a:Type0) [| ring a |] (#n:size_nat) (x:poly a n) (y:poly a n) (z:poly a n) : Lemma (mod_poly_add (mod_poly_add x y) z == mod_poly_add x (mod_poly_add y z)) =
  Lib.Arithmetic.Group.Sequence.lemma_assoc_lseq #a #add_ag.g.m x y z

let poly_mul_ (#a:Type0) [| ring a |] (#n:size_nat) (x:poly a n) (y:poly a n) : poly a n & poly a n =
  Loops.repeati n (fun i acc -> Loops.repeati n (fun j acc -> let acc1,acc2 = acc in if (i+j < n) then (upd acc1 (i+j) (plus #a acc1.[i+j] (Lib.Arithmetic.Ring.mul #a x.[i] y.[j]))),acc2 else acc1,(upd acc2 (i+j-n) (plus #a acc2.[i+j-n] (Lib.Arithmetic.Ring.mul #a x.[i] y.[j])))) acc) (create n zero, create n zero)

let mod_poly_mul (#a:Type0) [| ring a |] (#n:size_nat) (x:poly a n) (y:poly a n) : poly a n =
  let z1,z2 = poly_mul_ x y in
  createi n (fun i -> minus #a z1.[i] z2.[i])

