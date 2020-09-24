module Hacl.Test.Leaks

open Lib.IntTypes
open Lib.Sequence


#set-options "--z3rlimit 300"


let felem = lseq uint64 10

noeq
type stateLeak = 
  |Mk:  root: felem -> parts: list felem ->  stateLeak


noeq
type state = 
  |MkState: states: list stateLeak -> state


assume val intro: unit -> state 


(* the general concept tells that out of shades you can get the full a *)
assume val sharesOf: a: felem -> shares: list felem -> Type0

(* only independent? *)
assume val leaks: root: felem -> a: list felem -> Type0


(* The element is independent if it´s was generated in intro_shares code *)
(* Meaning it doesnot bring any dependency *)
assume val isIndependent : #st: state -> a: felem -> Tot (r: bool {r ==> leaks a []})

assume val isFresh: #st: state -> a: felem -> Tot bool



assume val intro_shares: #st: state ->
  num: size_t -> a: felem -> 
  Tot (
    (s: state) & 
    (c: list felem {forall (i: nat). i < (List.Tot.Base.length c) ==> isIndependent #st (List.Tot.Base.index c i)}
  ))



(* if in the expression there is one element that is fresh, than the expression doesnot leak *)
assume val isNotLeaking: unit -> Tot bool

assume val shaded: a: felem -> 
  Tot (r: bool 
      (* at least one is not is the list of shares *))


assume val addition: 
  #s: state -> 
  #basedOnA: list felem -> 
  #basedOnB: list felem ->
  
  a: felem {leaks a basedOnA} -> 
  b: felem {leaks b basedOnB} -> 
  
  Tot (c: felem & 
    l: list felem
    {

      leaks c l /\(
      let lBasic = (List.Tot.Base.append basedOnA basedOnB) in
      let lBasicA : list felem = 
	if isIndependent #s a then 
	  List.Tot.Base.append lBasic [a] 
	else
	  lBasic in 
      let lBasicB : list felem = 
	if isIndependent #s b then 
	  List.Tot.Base.append lBasicA [b]
	else 
	  lBasicA
      in 
	leaks c lBasicB)
    })


(*
assume val leaksLemma: a: felem -> b: felem -> c: felem -> Lemma 
  (requires leaks  [a; b] /\ leaks [a; c])
  (ensures leaks [a; b; c])
*)


val multiplication: a: felem -> b: felem -> Tot (c: felem {shaded a})

let multiplication a b = 
  let state = intro() in 
  let (|state, shareA|) = intro_shares #state 2ul a in 
    assume(List.Tot.Base.length shareA == 2);
    let shareA0 = List.Tot.Base.index shareA 0 in 
    let shareA1 = List.Tot.Base.index shareA 1 in 
  let (|state, shareB|) = intro_shares #state 2ul b in 
    assume(List.Tot.Base.length shareB == 2);
    let shareB0 = List.Tot.Base.index shareB 0 in 
    let shareB1 = List.Tot.Base.index shareB 1 in 
  
  let (|r, leakedR|) = addition #state #[] #[] shareA0 shareB0 in  
  
  let (|r, _|) = addition #state #[] #[] r shareB0 in 

  admit();

  r

