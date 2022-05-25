module Lib.Transposition64x8

open Lib.IntTypes

#set-options "--fuel 0 --ifuel 0"

val forall_intro_bool_6
  (#p:bool -> bool -> bool -> bool -> bool -> bool -> Type0)
  ($_: (b0:bool -> b1:bool -> b2:bool -> b3:bool -> b4:bool -> b5:bool -> Lemma (p b0 b1 b2 b3 b4 b5)))
    : Lemma (forall (b0 b1 b2 b3 b4 b5:bool). p b0 b1 b2 b3 b4 b5)
let forall_intro_bool_6 #p pr =
  FStar.Classical.forall_intro_3 (fun (b0 b1 b2:bool) ->
    FStar.Classical.forall_intro_3 (fun (b3 b4 b5:bool) ->
      ( pr b0 b1 b2 b3 b4 b5
      ) <: Lemma (p b0 b1 b2 b3 b4 b5)
    ) <: Lemma (forall (b3 b4 b5:bool). p b0 b1 b2 b3 b4 b5)
  ) <: Lemma (forall (b0 b1 b2 b3 b4 b5:bool). p b0 b1 b2 b3 b4 b5)

val forall_intro_bool_7
  (#p:bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type0)
  ($_: (b0:bool -> b1:bool -> b2:bool -> b3:bool -> b4:bool -> b5:bool -> b6:bool -> Lemma (p b0 b1 b2 b3 b4 b5 b6)))
    : Lemma (forall (b0 b1 b2 b3 b4 b5 b6:bool). p b0 b1 b2 b3 b4 b5 b6)
let forall_intro_bool_7 #p pr =
  FStar.Classical.forall_intro ( fun (b0:bool) -> forall_intro_bool_6 #(p b0) (pr b0))

val forall_intro_bool_8
  (#p:bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type0)
  ($_: (b0:bool -> b1:bool -> b2:bool -> b3:bool -> b4:bool -> b5:bool -> b6:bool -> b7:bool -> Lemma (p b0 b1 b2 b3 b4 b5 b6 b7)))
    : Lemma (forall (b0 b1 b2 b3 b4 b5 b6 b7:bool). p b0 b1 b2 b3 b4 b5 b6 b7)
let forall_intro_bool_8 #p pr =
  FStar.Classical.forall_intro ( fun (b0:bool) -> forall_intro_bool_7 #(p b0) (pr b0))

val forall_intro_bool_9
  (#p:bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type0)
  ($_: (b0:bool -> b1:bool -> b2:bool -> b3:bool -> b4:bool -> b5:bool -> b6:bool -> b7:bool -> b8:bool -> Lemma (p b0 b1 b2 b3 b4 b5 b6 b7 b8)))
    : Lemma (forall (b0 b1 b2 b3 b4 b5 b6 b7 b8:bool). p b0 b1 b2 b3 b4 b5 b6 b7 b8)
let forall_intro_bool_9 #p pr =
  FStar.Classical.forall_intro ( fun (b0:bool) -> forall_intro_bool_8 #(p b0) (pr b0))

module UI = FStar.UInt
module S = FStar.Seq
module BV = FStar.BitVector

let uint64x1 : Type0 = uint64
let uint64x2 : Type0 = uint64x1 * uint64x1
let uint64x4 : Type0 = uint64x2 * uint64x2
let uint64x8 : Type0 = uint64x4 * uint64x4

let aux (i0 i1 i2 i3 i4 i5:bool) : (i:nat{i<64}) =
  assert_norm (pow2 6 == 64);
  let s = S.cons i5 (S.cons i4 (S.cons i3 (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  63-UI.from_vec #6 s

let aux_lemma (#n:pos) (a b:(s:S.seq bool{S.length s == n})) (k:nat{k<n}) :
  Lemma
    (requires (forall (i:nat{i<n /\ i<>k}). S.index a i == S.index b i)
      /\ S.index a k == true /\ S.index b k == false)
    (ensures UI.from_vec #n a == UI.from_vec #n b + pow2 (n-k-1))
  =
  assert_norm(UI.from_vec #1 (S.create 1 true) == 1);
  assert_norm(UI.from_vec #1 (S.create 1 false) == 0);
  if n = 1 then (
    S.lemma_eq_intro a (S.create 1 true);
    S.lemma_eq_intro b (S.create 1 false);
    ()
  ) else if k = 0 then (
    S.lemma_eq_intro (S.tail a) (S.tail b);
    assert(a == S.cons (S.head a) (S.tail a));
    assert(b == S.cons (S.head b) (S.tail b));
    UI.append_lemma #1 #(n-1) (S.create 1 (S.head a)) (S.tail a);
    UI.append_lemma #1 #(n-1) (S.create 1 (S.head b)) (S.tail b);
    ()
  ) else if k = n-1 then (
    let (a0,a1) = S.split a k in
    let (b0,b1) = S.split b k in
    S.lemma_eq_intro a0 b0;
    S.lemma_eq_intro a1 (S.create 1 true);
    S.lemma_eq_intro b1 (S.create 1 false);
    S.lemma_split a k;
    S.lemma_split b k;
    UI.append_lemma #k #(n-k) a0 a1;
    UI.append_lemma #k #(n-k) b0 b1;
    ()
  ) else (
    let (a0,a1) = S.split a k in
    let (b0,b1) = S.split b k in
    S.lemma_eq_intro a0 b0;
    S.lemma_eq_intro (S.tail a1) (S.tail b1);
    S.lemma_split a k;
    S.lemma_split b k;
    assert(a == S.append a0 (S.cons (S.head a1) (S.tail a1)));
    assert(b == S.append b0 (S.cons (S.head b1) (S.tail b1)));
    UI.append_lemma #k #(n-k) a0 a1;
    UI.append_lemma #k #(n-k) b0 b1;
    UI.append_lemma #1 #(n-k-1) (S.create 1 (S.head a1)) (S.tail a1);
    UI.append_lemma #1 #(n-k-1) (S.create 1 (S.head b1)) (S.tail b1);
    ()
  )

let aux_lemma8 (i0 i1 i2 i4 i5:bool) :
  Lemma (aux i0 i1 i2 true i4 i5 == aux i0 i1 i2 false i4 i5 - 8)
  [SMTPat (aux i0 i1 i2 true i4 i5)]
  =
  let s = S.cons i5 (S.cons i4 (S.cons true (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  let t = S.cons i5 (S.cons i4 (S.cons false (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  aux_lemma #6 s t 2

let aux_lemma16 (i0 i1 i2 i3 i5:bool) :
  Lemma (aux i0 i1 i2 i3 true i5 == aux i0 i1 i2 i3 false i5 - 16)
  [SMTPat (aux i0 i1 i2 i3 true i5)]
  =
  let s = S.cons i5 (S.cons true (S.cons i3 (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  let t = S.cons i5 (S.cons false (S.cons i3 (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  aux_lemma #6 s t 1

let aux_lemma32 (i0 i1 i2 i3 i4:bool) :
  Lemma (aux i0 i1 i2 i3 i4 true == aux i0 i1 i2 i3 i4 false - 32)
  [SMTPat (aux i0 i1 i2 i3 i4 true)]
  =
  let s = S.cons true (S.cons i4 (S.cons i3 (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  let t = S.cons false (S.cons i4 (S.cons i3 (S.cons i2 (S.cons i1 (S.cons i0 S.empty))))) in
  aux_lemma #6 s t 0;
  assert_norm(pow2 5 == 32)

let get1 (x:uint64x1) ((i0,i1,i2):bool*bool*bool) ((j0,j1,j2):bool*bool*bool) : bool =
  UI.nth #64 (v x) (aux j0 j1 j2 i0 i1 i2)

let get2 ((x0,x1):uint64x2) (k0:bool) (i j:bool*bool*bool) : bool =
  if k0 then get1 x1 i j else get1 x0 i j

let get4 ((x0,x1):uint64x4) ((k0,k1):bool*bool) (i j:bool*bool*bool) : bool =
  if k1 then get2 x1 k0 i j else get2 x0 k0 i j

let get8 ((x0,x1):uint64x8) ((k0,k1,k2):bool*bool*bool) (i j:bool*bool*bool) : bool =
  if k2 then get4 x1 (k0,k1) i j else get4 x0 (k0,k1) i j

#push-options "--ifuel 1"
let get1_xor (x y:uint64) (i j:bool*bool*bool) :
  Lemma (get1 (x ^. y) i j == (get1 x i j <> get1 y i j))
  [SMTPat (get1 (x ^. y) i j)]
  = logxor_spec x y
let get1_and (x y:uint64) (i j:bool*bool*bool) :
  Lemma (get1 (x &. y) i j == (get1 x i j && get1 y i j))
  [SMTPat (get1 (x &. y) i j)]
  = logand_spec x y
let get1_or (x y:uint64) (i j:bool*bool*bool) :
  Lemma (get1 (x |. y) i j == (get1 x i j || get1 y i j))
  [SMTPat (get1 (x |. y) i j)]
  = logor_spec x y
let get1_not (x:uint64) (i j:bool*bool*bool) :
  Lemma (get1 (lognot x) i j == not (get1 x i j))
  [SMTPat (get1 (lognot x) i j)]
  = lognot_spec x
#pop-options

let shift8_lemma0 (x:uint64) (i1 i2:bool) (j:bool*bool*bool) :
  Lemma (get1 (x <<. size 8) (true,i1,i2) j == get1 x (false,i1,i2) j)
  [SMTPat (get1 (x <<. size 8) (true,i1,i2) j)]
  =
  let (j0,j1,j2) = j in
  assert(get1 (x <<. size 8) (true,i1,i2) j == UI.nth #64 (UI.shift_left (v x) 8) (aux j0 j1 j2 false i1 i2 - 8))
let shift16_lemma0 (x:uint64) (i0 i2:bool) (j:bool*bool*bool) :
  Lemma (get1 (x <<. size 16) (i0,true,i2) j == get1 x (i0,false,i2) j)
  [SMTPat (get1 (x <<. size 16) (i0,true,i2) j)]
  =
  let (j0,j1,j2) = j in
  assert(get1 (x <<. size 16) (i0,true,i2) j == UI.nth #64 (UI.shift_left (v x) 16) (aux j0 j1 j2 i0 false i2 - 16))
let shift32_lemma0 (x:uint64) (i0 i1:bool) (j:bool*bool*bool) :
  Lemma (get1 (x <<. size 32) (i0,i1,true) j == get1 x (i0,i1,false) j)
  [SMTPat (get1 (x <<. size 32) (i0,i1,true) j)]
  =
  let (j0,j1,j2) = j in
  assert(get1 (x <<. size 32) (i0,i1,true) j == UI.nth #64 (UI.shift_left (v x) 32) (aux j0 j1 j2 i0 i1 false - 32))

let shift8_lemma1 (x:uint64) (i1 i2:bool) (j:bool*bool*bool) :
  Lemma (get1 (x >>. size 8) (false,i1,i2) j == get1 x (true,i1,i2) j)
  [SMTPat (get1 (x >>. size 8) (false,i1,i2) j)]
  =
  let (j0,j1,j2) = j in
  assert(get1 (x >>. size 8) (false,i1,i2) j == UI.nth #64 (UI.shift_right (v x) 8) (aux j0 j1 j2 true i1 i2 + 8))
let shift16_lemma1 (x:uint64) (i0 i2:bool) (j:bool*bool*bool) :
  Lemma (get1 (x >>. size 16) (i0,false,i2) j == get1 x (i0,true,i2) j)
  [SMTPat (get1 (x >>. size 16) (i0,false,i2) j)]
  =
  let (j0,j1,j2) = j in
  assert(get1 (x >>. size 16) (i0,false,i2) j == UI.nth #64 (UI.shift_right (v x) 16) (aux j0 j1 j2 i0 true i2 + 16))
let shift32_lemma1 (x:uint64) (i0 i1:bool) (j:bool*bool*bool) :
  Lemma (get1 (x >>. size 32) (i0,i1,false) j == get1 x (i0,i1,true) j)
  [SMTPat (get1 (x >>. size 32) (i0,i1,false) j)]
  =
  let (j0,j1,j2) = j in
  assert(get1 (x >>. size 32) (i0,i1,false) j == UI.nth #64 (UI.shift_right (v x) 32) (aux j0 j1 j2 i0 i1 true + 32))

#push-options "--ifuel 1"
let transpose_aux_aux32 (a b:uint64) :
  Pure uint64x2 (requires True) (ensures fun x ->
    forall (k0 i0 i1 i2:bool) (j:bool*bool*bool). get2 x k0 (i0,i1,i2) j == get2 (a,b) i2 (i0,i1,k0) j
  ) =
  let foo (i:nat{i<64}) : bool =
    assert_norm(pow2 6 == 64);
    UI.nth #6 (63-i) 0
  in
  let m : uint64 = u64 (UI.from_vec #64 (S.init 64 foo)) in
  assert(forall (i0 i1 i2:bool) (j:bool*bool*bool). get1 m (i0,i1,i2) j == i2);
  ( (a &. lognot m) ^. ((b <<. size 32) &. m)
  , ((a >>. size 32) &. lognot m) ^. (b &. m)
  )
#pop-options

#push-options "--ifuel 1"
let transpose_aux_aux16 (a b:uint64) :
  Pure uint64x2 (requires True) (ensures fun x ->
    forall (k0 i0 i1 i2:bool) (j:bool*bool*bool). get2 x k0 (i0,i1,i2) j == get2 (a,b) i1 (i0,k0,i2) j
  ) =
  let foo (i:nat{i<64}) : bool =
    assert_norm(pow2 6 == 64);
    UI.nth #6 (63-i) 1
  in
  let m : uint64 = u64 (UI.from_vec #64 (S.init 64 foo)) in
  assert(forall (i0 i1 i2:bool) (j:bool*bool*bool). get1 m (i0,i1,i2) j == i1);
  ( (a &. lognot m) ^. ((b <<. size 16) &. m)
  , ((a >>. size 16) &. lognot m) ^. (b &. m)
  )
#pop-options

#push-options "--ifuel 1"
let transpose_aux_aux8 (a b:uint64) :
  Pure uint64x2 (requires True) (ensures fun x ->
    forall (k0 i0 i1 i2:bool) (j:bool*bool*bool). get2 x k0 (i0,i1,i2) j == get2 (a,b) i0 (k0,i1,i2) j
  ) =
  let foo (i:nat{i<64}) : bool =
    assert_norm(pow2 6 == 64);
    UI.nth #6 (63-i) 2
  in
  let m : uint64 = u64 (UI.from_vec #64 (S.init 64 foo)) in
  assert(forall (i0 i1 i2:bool) (j:bool*bool*bool). get1 m (i0,i1,i2) j == i0);
  ( (a &. lognot m) ^. ((b <<. size 8) &. m)
  , ((a >>. size 8) &. lognot m) ^. (b &. m)
  )
#pop-options

let transpose_aux32 (x:uint64x8) : Pure uint64x8 (requires True) (ensures fun y -> forall (k0 k1 k2 i0 i1 i2 j0 j1 j2:bool). get8 y (k0,k1,k2) (i0,i1,i2) (j0,j1,j2) == get8 x (k0,k1,i2) (i0,i1,k2) (j0,j1,j2)) =
    let (((x0,x1),(x2,x3)),((x4,x5),(x6,x7))) = x in
    let (y0, y4) = transpose_aux_aux32 x0 x4 in
    let (y1, y5) = transpose_aux_aux32 x1 x5 in
    let (y2, y6) = transpose_aux_aux32 x2 x6 in
    let (y3, y7) = transpose_aux_aux32 x3 x7 in
    let y = (((y0,y1),(y2,y3)),((y4,y5),(y6,y7))) in
    forall_intro_bool_9 (fun k0 k1 k2 i0 i1 i2 j0 j1 j2 ->
      ( match (k0, k1) with
      | (false, false) -> assert (get8 y (k0,k1,k2) (i0,i1,i2) (j0,j1,j2) == get2 (y0,y4) k2 (i0,i1,i2) (j0,j1,j2))
      | (true, false) -> assert (get8 y (k0,k1,k2) (i0,i1,i2) (j0,j1,j2) == get2 (y1,y5) k2 (i0,i1,i2) (j0,j1,j2))
      | (false, true) -> assert (get8 y (k0,k1,k2) (i0,i1,i2) (j0,j1,j2) == get2 (y2,y6) k2 (i0,i1,i2) (j0,j1,j2))
      | (true, true) -> assert (get8 y (k0,k1,k2) (i0,i1,i2) (j0,j1,j2) == get2 (y3,y7) k2 (i0,i1,i2) (j0,j1,j2))
      ) <: Lemma (get8 y (k0,k1,k2) (i0,i1,i2) (j0,j1,j2) == get8 x (k0,k1,i2) (i0,i1,k2) (j0,j1,j2))
    );
    y

let transpose_aux16 (x:uint64x4) : Pure uint64x4 (requires True) (ensures fun y -> forall (k0 k1 i0 i1 i2 j0 j1 j2:bool). get4 y (k0,k1) (i0,i1,i2) (j0,j1,j2) == get4 x (k0,i1) (i0,k1,i2) (j0,j1,j2)) =
    let ((x0,x1),(x2,x3)) = x in
    let (y0, y2) = transpose_aux_aux16 x0 x2 in
    let (y1, y3) = transpose_aux_aux16 x1 x3 in
    let y = ((y0,y1),(y2,y3)) in
    forall_intro_bool_8 (fun k0 k1 i0 i1 i2 j0 j1 j2 ->
      ( match k0 with
      | false -> assert(get4 y (k0,k1) (i0,i1,i2) (j0,j1,j2) == get2 (y0,y2) k1 (i0,i1,i2) (j0,j1,j2))
      | true -> assert(get4 y (k0,k1) (i0,i1,i2) (j0,j1,j2) == get2 (y1,y3) k1 (i0,i1,i2) (j0,j1,j2))
      ) <: Lemma (get4 y (k0,k1) (i0,i1,i2) (j0,j1,j2) == get4 x (k0,i1) (i0,k1,i2) (j0,j1,j2))
    );
    y

let ttranspose_aux8 (x:uint64x2) : Pure uint64x2 (requires True) (ensures fun y -> forall (k0 i0 i1 i2 j0 j1 j2:bool). get2 y k0 (i0,i1,i2) (j0,j1,j2) == get2 x i0 (k0,i1,i2) (j0,j1,j2)) =
    let (x0,x1) = x in
    let (y0,y1) = transpose_aux_aux8 x0 x1 in
    (y0,y1)

let transpose_bits64 (x:uint64) :
  Pure uint64 (requires True)
  (ensures fun y -> forall (i j:bool*bool*bool). get1 y i j == get1 x j i)
  =
  let m0 : uint64 = u64 0x8040201008040201 in
  let m1 : uint64 = u64 0x4020100804020100 in
  let m2 : uint64 = u64 0x2010080402010000 in
  let m3 : uint64 = u64 0x1008040201000000 in
  let m4 : uint64 = u64 0x0804020100000000 in
  let m5 : uint64 = u64 0x0402010000000000 in
  let m6 : uint64 = u64 0x0201000000000000 in
  let m7 : uint64 = u64 0x0100000000000000 in

  let y0 : uint64 = x &. m0 in
  let y1 : uint64 = y0 |. ((x &. m1) >>. size 7) in
  let y2 : uint64 = y1 |. ((x &. m2) >>. size 14) in
  let y3 : uint64 = y2 |. ((x &. m3) >>. size 21) in
  let y4 : uint64 = y3 |. ((x &. m4) >>. size 28) in
  let y5 : uint64 = y4 |. ((x &. m5) >>. size 35) in
  let y6 : uint64 = y5 |. ((x &. m6) >>. size 42) in
  let y7 : uint64 = y6 |. ((x &. m7) >>. size 49) in
  let y8 : uint64 = y7 |. ((x <<. size  7) &. m1) in
  let y9 : uint64 = y8 |. ((x <<. size 14) &. m2) in
  let y10 : uint64 = y9 |. ((x <<. size 21) &. m3) in
  let y11 : uint64 = y10 |. ((x <<. size 28) &. m4) in
  let y12 : uint64 = y11 |. ((x <<. size 35) &. m5) in
  let y13 : uint64 = y12 |. ((x <<. size 42) &. m6) in
  let y14 : uint64 = y13 |. ((x <<. size 49) &. m7) in
  admit ();
  y14

val transpose_bits64x8 (x:uint64x8) : Pure uint64x8 (requires True) (ensures fun y -> forall (k i j:bool*bool*bool). get8 y k i j == get8 x j k i)
#push-options "--ifuel 1 --z3rlimit 8"
let transpose_bits64x8 a =
  let (b0,b1)  = transpose_aux32 a in

  let (c0,c1) = transpose_aux16 b0 in
  let (c2,c3) = transpose_aux16 b1 in

  let (d0,d1) = ttranspose_aux8 c0 in
  let (d2,d3) = ttranspose_aux8 c1 in
  let (d4,d5) = ttranspose_aux8 c2 in
  let (d6,d7) = ttranspose_aux8 c3 in

  let e0 = transpose_bits64(d0) in
  let e1 = transpose_bits64(d1) in
  let e2 = transpose_bits64(d2) in
  let e3 = transpose_bits64(d3) in
  let e4 = transpose_bits64(d4) in
  let e5 = transpose_bits64(d5) in
  let e6 = transpose_bits64(d6) in
  let e7 = transpose_bits64(d7) in

  (((e0,e1),(e2,e3)),((e4,e5),(e6,e7)))
#pop-options

val transpose_bits8x64 (x:uint64x8) : Pure uint64x8 (requires True) (ensures fun y -> forall (k i j:bool*bool*bool). get8 y k i j == get8 x i j k)
#push-options "--ifuel 1 --z3rlimit 8"
let transpose_bits8x64 a =
  let (((a0,a1),(a2,a3)),((a4,a5),(a6,a7))) = a in

  let b0 = transpose_bits64(a0) in
  let b1 = transpose_bits64(a1) in
  let b2 = transpose_bits64(a2) in
  let b3 = transpose_bits64(a3) in
  let b4 = transpose_bits64(a4) in
  let b5 = transpose_bits64(a5) in
  let b6 = transpose_bits64(a6) in
  let b7 = transpose_bits64(a7) in

  let c0 = ttranspose_aux8 (b0, b1) in
  let c1 = ttranspose_aux8 (b2, b3) in
  let c2 = ttranspose_aux8 (b4, b5) in
  let c3 = ttranspose_aux8 (b6, b7) in

  let d0 = transpose_aux16 (c0, c1) in
  let d1 = transpose_aux16 (c2, c3) in

  let e = transpose_aux32 (d0, d1) in
  e
#pop-options

let transpose_transpose (x:uint64x8) :
  Lemma (forall (k i j:bool*bool*bool). get8 (transpose_bits8x64 (transpose_bits64x8 x)) k i j == get8 x k i j)
  [SMTPat (transpose_bits8x64 (transpose_bits64x8 x))]
  = ()
