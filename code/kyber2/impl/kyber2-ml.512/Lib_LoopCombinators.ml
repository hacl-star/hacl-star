open Prims
let rec (repeat_left :
  Prims.nat ->
    Prims.nat -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun lo ->
    fun hi ->
      fun a ->
        fun f ->
          fun acc ->
            if lo = hi
            then acc
            else repeat_left (lo + (Prims.parse_int "1")) hi () f (f lo acc)
let rec (repeat_left_all_ml :
  Prims.nat ->
    Prims.nat -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun lo ->
    fun hi ->
      fun a ->
        fun f ->
          fun acc ->
            if lo = hi
            then acc
            else
              (let uu____101 = f lo acc in
               repeat_left_all_ml (lo + (Prims.parse_int "1")) hi () f
                 uu____101)
let rec (repeat_right :
  Prims.nat ->
    Prims.nat -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun lo ->
    fun hi ->
      fun a ->
        fun f ->
          fun acc ->
            if lo = hi
            then acc
            else
              f (hi - (Prims.parse_int "1"))
                (repeat_right lo (hi - (Prims.parse_int "1")) () f acc)
let rec (repeat_right_all_ml :
  Prims.nat ->
    Prims.nat -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun lo ->
    fun hi ->
      fun a ->
        fun f ->
          fun acc ->
            if lo = hi
            then acc
            else
              (let uu____206 =
                 repeat_right_all_ml lo (hi - (Prims.parse_int "1")) () f acc in
               f (hi - (Prims.parse_int "1")) uu____206)




let (repeat_gen :
  Prims.nat -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t) =
  fun n ->
    fun a ->
      fun f -> fun acc0 -> repeat_right (Prims.parse_int "0") n () f acc0
let (repeat_gen_all_ml :
  Prims.nat -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t) =
  fun n ->
    fun a ->
      fun f ->
        fun acc0 -> repeat_right_all_ml (Prims.parse_int "0") n () f acc0


type ('Aa, 'Ai) fixed_a = 'Aa
let fixed_i : 'Auu____399 . 'Auu____399 -> Prims.nat -> 'Auu____399 =
  fun f -> fun i -> f
let repeati : 'Aa . Prims.nat -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun a3 ->
    fun a4 ->
      fun a5 ->
        (fun n ->
           fun f ->
             fun acc0 ->
               Obj.magic
                 (repeat_gen n () (fun a1 -> fun a2 -> (Obj.magic f) a1 a2)
                    (Obj.magic acc0))) a3 a4 a5
let repeati_all_ml :
  'Aa . Prims.nat -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun a8 ->
    fun a9 ->
      fun a10 ->
        (fun n ->
           fun f ->
             fun acc0 ->
               Obj.magic
                 (repeat_gen_all_ml n ()
                    (fun a6 -> fun a7 -> (Obj.magic f) a6 a7)
                    (Obj.magic acc0))) a8 a9 a10



let repeat : 'Aa . Prims.nat -> ('Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun n -> fun f -> fun acc0 -> repeati n (fixed_i f) acc0


let repeat_range :
  'Aa . Prims.nat -> Prims.nat -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun a13 ->
    fun a14 ->
      fun a15 ->
        fun a16 ->
          (fun min1 ->
             fun max ->
               fun f ->
                 fun x ->
                   Obj.magic
                     (repeat_left min1 max ()
                        (fun a11 -> fun a12 -> (Obj.magic f) a11 a12)
                        (Obj.magic x))) a13 a14 a15 a16
let repeat_range_all_ml :
  'Aa . Prims.nat -> Prims.nat -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun a19 ->
    fun a20 ->
      fun a21 ->
        fun a22 ->
          (fun min1 ->
             fun max ->
               fun f ->
                 fun x ->
                   Obj.magic
                     (repeat_left_all_ml min1 max ()
                        (fun a17 -> fun a18 -> (Obj.magic f) a17 a18)
                        (Obj.magic x))) a19 a20 a21 a22
type ('Aa, 'An, 'Apred) repeatable = Prims.nat -> 'Aa -> 'Aa
let repeat_range_inductive :
  'Aa .
    Prims.nat -> Prims.nat -> unit -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa
  =
  fun a25 ->
    fun a26 ->
      fun a27 ->
        fun a28 ->
          fun a29 ->
            (fun min1 ->
               fun max ->
                 fun pred ->
                   fun f ->
                     fun x ->
                       Obj.magic
                         (repeat_left min1 max ()
                            (fun a23 -> fun a24 -> (Obj.magic f) a23 a24)
                            (Obj.magic x))) a25 a26 a27 a28 a29
let repeati_inductive :
  'Aa . Prims.nat -> unit -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun n ->
    fun pred ->
      fun f ->
        fun x0 -> repeat_range_inductive (Prims.parse_int "0") n () f x0

type ('An, 'Aa, 'Af, 'Apred) preserves_predicate = unit
let (repeat_gen_inductive :
  Prims.nat ->
    unit -> unit -> (Prims.nat -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun n ->
    fun a ->
      fun pred ->
        fun f -> fun x0 -> let f' i x = f i x in repeat_gen n () f' x0
type ('Aa, 'An, 'Af, 'Apred) preserves = unit
let repeati_inductive' :
  'Aa . Prims.nat -> unit -> (Prims.nat -> 'Aa -> 'Aa) -> 'Aa -> 'Aa =
  fun a32 ->
    fun a33 ->
      fun a34 ->
        fun a35 ->
          (fun n ->
             fun pred ->
               fun f ->
                 fun x0 ->
                   let f' i x = f i x in
                   Obj.magic
                     (repeat_gen n ()
                        (fun a30 -> fun a31 -> (Obj.magic f') a30 a31)
                        (Obj.magic x0))) a32 a33 a34 a35