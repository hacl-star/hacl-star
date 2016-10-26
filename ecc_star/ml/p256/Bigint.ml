open Prims
open Stdint
open UInt
       
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

type bigint = UInt.limb biginteger	   
type bigint_wide = UInt.wide biginteger
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

let create_limb: int -> bigint = (fun size ->
    let a = Array.make size zero_limb in Bigint(a, Parameters.templ))

let create_wide: int -> bigint_wide = (fun size ->
    let a = Array.make size zero_wide in Bigint(a, Parameters.templ))

let create_wide_templ: int -> template -> bigint_wide = fun size t -> let a = Array.make size zero_wide in Bigint(a, t)
                                        
let index = (fun word_size b n ->
  match b with | Bigint(a,_) -> a.(n))
let index_byte:serialized -> int -> uint8 = (fun b idx -> match b with | Bigint(a,_) -> a.(idx))
let index_limb:bigint -> int -> limb = (fun b idx -> match b with | Bigint(a,_) -> a.(idx))
let index_wide:bigint_wide -> int -> wide = (fun b idx -> match b with | Bigint(a,_) -> a.(idx))

let upd = (fun ws b idx size v ->
  match b with | Bigint(a,_) -> a.(idx) <- v)
let upd_byte:serialized -> int -> uint8 -> unit = (fun b idx v -> match b with | Bigint(a,_) -> a.(idx) <- v)
let upd_limb:bigint -> int -> limb -> unit = (fun b idx v -> match b with | Bigint(a,_) -> a.(idx) <- v)
let upd_wide:bigint_wide -> int -> wide -> unit = (fun b idx v -> match b with | Bigint(a,_) -> a.(idx) <- v)
            
let copy = (fun size (a:'a biginteger) ->
    let b = Array.copy (getRef a) in
    let (t:template) = getTemplate size a in
    Bigint(b, getTemplate size a))

             (*
let one_bigint = (fun size template ->
    let res = create_limb size in
    upd Parameters.platform_size res 0 Parameters.platform_size Uint64.one;
    res)
              *)
	     
let blit = (fun w a b len ->
    let ref_b = getRef b in let ref_a = getRef a in
    Array.blit ref_a 0 ref_b 0 len)

let blit_limb = (fun a b len ->
    let ref_b = getRef b in let ref_a = getRef a in
    Array.blit ref_a 0 ref_b 0 len)
let blit_wide = (fun a b len ->
    let ref_b = getRef b in let ref_a = getRef a in
    Array.blit ref_a 0 ref_b 0 len)

             
let print_bigint' (b:bigint) : unit =
  for i = 0 to Parameters.norm_length-1 do
    print_string (to_string (index 64 b i));
    print_string " ";
  done;
  print_string "\n"
	     
let print_bigint (b:bigint) : unit =
  for i = 0 to Parameters.norm_length-1 do
    let bi = index 64 b i in
    print_string (to_string (log_and_limb bi (of_string "0x3ffffff")));
    print_string " ";
    print_string (to_string (shift_right_limb bi 26));
  done;
  print_string "\n"
