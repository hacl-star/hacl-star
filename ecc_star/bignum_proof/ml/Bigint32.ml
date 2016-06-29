
open Stdint
open Prims
       
type template = int  ->  int

type template_const = template
type 'a biginteger =
| Bigint of 'a array * template

let is_Bigint = (fun _discr_ -> (match (_discr_) with
| Bigint (_) -> begin
true
end
| _ -> begin
false
end))

let ___Bigint___data = (fun size projectee -> (match (projectee) with
| Bigint (_19_7, _19_9) -> begin
_19_7
end))

let ___Bigint___t = (fun size projectee -> (match (projectee) with
| Bigint (_19_12, _19_10) -> begin
_19_10
end))

type bigint = Uint32.t biginteger	   
type bigint_wide = Uint64.t biginteger
type serialized = Uint8.t biginteger

let getRef = fun b ->
  match b with | Bigint(r, t) -> r

let live = true
let getLength = (fun h size b ->
    match b with | Bigint(a,_) -> Array.length a)

let getSize = (fun h size b i -> 0)

let getValue = (fun h size b i ->
  match b with | Bigint(a,_) -> a.(i))

let getTemplate = (fun size b ->
    match b with | Bigint(_,t) -> t)

let create_std = (fun size t ->
    let a = Array.make size Uint32.zero in Bigint(a, t))

let create_wide = (fun size t ->
    let a = Array.make size Uint64.zero in Bigint(a, t))

let index = (fun word_size b n ->
  match b with | Bigint(a,_) -> a.(n))

let upd = (fun ws b idx size v ->
  match b with | Bigint(a,_) -> a.(idx) <- v)

let copy = (fun size (a:'a biginteger) ->
    let b = Array.copy (getRef a) in
    let (t:template) = getTemplate size a in
    Bigint(b, getTemplate size a))
	  
let one_bigint = (fun size template ->
    let res = create_std size template in
    upd Parameters.platform_size res 0 Parameters.platform_size Uint32.one;
    res)
		   
let blit = (fun w a b len ->
    let ref_b = getRef b in let ref_a = getRef a in
    Array.blit ref_a 0 ref_b 0 len)

let print_bigint b =
  for i = 0 to Parameters.norm_length-1 do
    print_string (Stdint.Uint32.to_string (index 32 b i));
    print_string " ";
  done;
  print_string "\n"
