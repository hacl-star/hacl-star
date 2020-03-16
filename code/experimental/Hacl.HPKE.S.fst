module Hacl.HPKE.S

open Lib.IntTypes
open Lib.Sequence

open FStar.Mul

type compression = 
  |Standart
  |NC
  |NN


type algorithm = 
  |One
  |Two

let getCoordinatesSize: algorithm -> size_nat = function
  |One -> 64
  |Two -> 65
  |_ -> 42


type serializedPoint (a: algorithm) = lseq uint64 (getCoordinatesSize a)

val decompressionExample: #x: compression -> #a: algorithm ->len: size_nat ->  input: lseq uint64 len -> Tot (option (serializedPoint a))

let decompressionExample #x #a len input = 
  match x with 
    |Standart -> 
      begin 
	let expectedSize = getCoordinatesSize a in 
	if len = expectedSize then 
	  Some input
	else 
	  None
      end
    |NC -> 
      begin 
	let expectedSize = getCoordinatesSize a in 
	if len = expectedSize + 1 then 
	  begin
	    let identifier = index input 0 in 
	      if uint_v identifier <> 04 then
		None 
	    else
	      Some (sub input 1 expectedSize)
	  end
	else None  
      end
    |_ -> None
	
