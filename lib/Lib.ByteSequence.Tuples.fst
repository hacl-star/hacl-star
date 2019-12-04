module Lib.ByteSequence.Tuples

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence


inline_for_extraction
val expand2: #a:Type0 -> lseq a 2 -> ltuple a 2
let expand2 #t x =
  let a = index #t #2 x 0 in
  let b = index #t #2 x 1 in
  a,b

inline_for_extraction
val expand3: #a:Type0 -> lseq a 3 -> ltuple a 3
let expand3 #t x =
  let a = index #t #3 x 0 in
  let b = index #t #3 x 1 in
  let c = index #t #3 x 2 in
  a,b,c

inline_for_extraction
val expand4: #a:Type0 -> lseq a 4 -> ltuple a 4
let expand4 #t x =
  let a = index #t #4 x 0 in
  let b = index #t #4 x 1 in
  let c = index #t #4 x 2 in
  let d = index #t #4 x 3 in
  a,b,c,d

inline_for_extraction
val expand5: #a:Type0 -> lseq a 5 -> ltuple a 5
let expand5 #t x =
  let a = index #t #5 x 0 in
  let b = index #t #5 x 1 in
  let c = index #t #5 x 2 in
  let d = index #t #5 x 3 in
  let e = index #t #5 x 4 in
  a,b,c,d,e

inline_for_extraction
val expand6: #a:Type0 -> lseq a 6 -> ltuple a 6
let expand6 #t x =
  let a = index #t #6 x 0 in
  let b = index #t #6 x 1 in
  let c = index #t #6 x 2 in
  let d = index #t #6 x 3 in
  let e = index #t #6 x 4 in
  let f = index #t #6 x 5 in
  a,b,c,d,e,f

inline_for_extraction
val expand7: #a:Type0 -> lseq a 7 -> ltuple a 7
let expand7 #t x =
  let a = index #t #7 x 0 in
  let b = index #t #7 x 1 in
  let c = index #t #7 x 2 in
  let d = index #t #7 x 3 in
  let e = index #t #7 x 4 in
  let f = index #t #7 x 5 in
  let g = index #t #7 x 6 in
  a,b,c,d,e,f,g

inline_for_extraction
val expand8: #a:Type0 -> lseq a 8 -> ltuple a 8
let expand8 #t x =
  let a = index #t #8 x 0 in
  let b = index #t #8 x 1 in
  let c = index #t #8 x 2 in
  let d = index #t #8 x 3 in
  let e = index #t #8 x 4 in
  let f = index #t #8 x 5 in
  let g = index #t #8 x 6 in
  let h = index #t #8 x 7 in
  a,b,c,d,e,f,g,h

inline_for_extraction
val expand9: #a:Type0 -> lseq a 9 -> ltuple a 9
let expand9 #t x =
  let a = index #t #9 x 0 in
  let b = index #t #9 x 1 in
  let c = index #t #9 x 2 in
  let d = index #t #9 x 3 in
  let e = index #t #9 x 4 in
  let f = index #t #9 x 5 in
  let g = index #t #9 x 6 in
  let h = index #t #9 x 7 in
  let i = index #t #9 x 8 in
  a,b,c,d,e,f,g,h,i

inline_for_extraction
val expand10: #a:Type0 -> lseq a 10 -> ltuple a 10
let expand10 #t x =
  let a = index #t #10 x 0 in
  let b = index #t #10 x 1 in
  let c = index #t #10 x 2 in
  let d = index #t #10 x 3 in
  let e = index #t #10 x 4 in
  let f = index #t #10 x 5 in
  let g = index #t #10 x 6 in
  let h = index #t #10 x 7 in
  let i = index #t #10 x 8 in
  let j = index #t #10 x 9 in
  a,b,c,d,e,f,g,h,i,j

inline_for_extraction
val expand11: #a:Type0 -> lseq a 11 -> ltuple a 11
let expand11 #t x =
  let a = index #t #11 x 0 in
  let b = index #t #11 x 1 in
  let c = index #t #11 x 2 in
  let d = index #t #11 x 3 in
  let e = index #t #11 x 4 in
  let f = index #t #11 x 5 in
  let g = index #t #11 x 6 in
  let h = index #t #11 x 7 in
  let i = index #t #11 x 8 in
  let j = index #t #11 x 9 in
  let k = index #t #11 x 10 in
  a,b,c,d,e,f,g,h,i,j,k

inline_for_extraction
val expand12: #a:Type0 -> lseq a 12 -> ltuple a 12
let expand12 #t x =
  let a = index #t #12 x 0 in
  let b = index #t #12 x 1 in
  let c = index #t #12 x 2 in
  let d = index #t #12 x 3 in
  let e = index #t #12 x 4 in
  let f = index #t #12 x 5 in
  let g = index #t #12 x 6 in
  let h = index #t #12 x 7 in
  let i = index #t #12 x 8 in
  let j = index #t #12 x 9 in
  let k = index #t #12 x 10 in
  let l = index #t #12 x 11 in
  a,b,c,d,e,f,g,h,i,j,k,l

inline_for_extraction
val expand13: #a:Type0 -> lseq a 13 -> ltuple a 13
let expand13 #t x =
  let a = index #t #13 x 0 in
  let b = index #t #13 x 1 in
  let c = index #t #13 x 2 in
  let d = index #t #13 x 3 in
  let e = index #t #13 x 4 in
  let f = index #t #13 x 5 in
  let g = index #t #13 x 6 in
  let h = index #t #13 x 7 in
  let i = index #t #13 x 8 in
  let j = index #t #13 x 9 in
  let k = index #t #13 x 10 in
  let l = index #t #13 x 11 in
  let m = index #t #13 x 12 in
  a,b,c,d,e,f,g,h,i,j,k,l,m


inline_for_extraction
val expand14: #a:Type0 -> lseq a 14 -> ltuple a 14
let expand14 #t x =
  let a = index #t #14 x 0 in
  let b = index #t #14 x 1 in
  let c = index #t #14 x 2 in
  let d = index #t #14 x 3 in
  let e = index #t #14 x 4 in
  let f = index #t #14 x 5 in
  let g = index #t #14 x 6 in
  let h = index #t #14 x 7 in
  let i = index #t #14 x 8 in
  let j = index #t #14 x 9 in
  let k = index #t #14 x 10 in
  let l = index #t #14 x 11 in
  let m = index #t #14 x 12 in
  let n = index #t #14 x 13 in
  a,b,c,d,e,f,g,h,i,j,k,l,m,n

let expand #t #len x =
  match len with
  | 2 -> expand2 #t x
  | 3 -> expand3 #t x
  | 4 -> expand4 #t x
  | 5 -> expand5 #t x
  | 6 -> expand6 #t x
  | 7 -> expand7 #t x
  | 8 -> expand8 #t x
  | 9 -> expand9 #t x
  | 10 -> expand10 #t x
  | 11 -> expand11 #t x
  | 12 -> expand12 #t x
  | 13 -> expand13 #t x
  | 14 -> expand14 #t x



inline_for_extraction
val collapse2: #a:Type0 -> zero:a -> ltuple a 2 -> lseq a 2
let collapse2 #t zero x =
  let x0,x1 = x in
  let z = create 2 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  z

inline_for_extraction
val collapse3: #a:Type0 -> zero:a -> ltuple a 3 -> lseq a 3
let collapse3 #t zero x =
  let x0,x1,x2 = x in
  let z = create 3 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  z

inline_for_extraction
val collapse4: #a:Type0 -> zero:a -> ltuple a 4 -> lseq a 4
let collapse4 #t zero x =
  let x0,x1,x2,x3 = x in
  let z = create 4 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  z

inline_for_extraction
val collapse5: #a:Type0 -> zero:a -> ltuple a 5 -> lseq a 5
let collapse5 #t zero x =
  let x0,x1,x2,x3,x4 = x in
  let z = create 5 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  z


inline_for_extraction
val collapse6: #a:Type0 -> zero:a -> ltuple a 6 -> lseq a 6
let collapse6 #t zero x =
  let x0,x1,x2,x3,x4,x5 = x in
  let z = create 6 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  z

inline_for_extraction
val collapse7: #a:Type0 -> zero:a -> ltuple a 7 -> lseq a 7
let collapse7 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6 = x in
  let z = create 7 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  z

inline_for_extraction
val collapse8: #a:Type0 -> zero:a -> ltuple a 8 -> lseq a 8
let collapse8 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7 = x in
  let z = create 8 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  z

inline_for_extraction
val collapse9: #a:Type0 -> zero:a -> ltuple a 9 -> lseq a 9
let collapse9 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7,x8 = x in
  let z = create 9 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  let z = upd z 8 x8 in
  z

inline_for_extraction
val collapse10: #a:Type0 -> zero:a -> ltuple a 10 -> lseq a 10
let collapse10 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7,x8,x9 = x in
  let z = create 10 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  let z = upd z 8 x8 in
  let z = upd z 9 x9 in
  z

inline_for_extraction
val collapse11: #a:Type0 -> zero:a -> ltuple a 11 -> lseq a 11
let collapse11 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 = x in
  let z = create 11 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  let z = upd z 8 x8 in
  let z = upd z 9 x9 in
  let z = upd z 10 x10 in
  z

inline_for_extraction
val collapse12: #a:Type0 -> zero:a -> ltuple a 12 -> lseq a 12
let collapse12 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11 = x in
  let z = create 12 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  let z = upd z 8 x8 in
  let z = upd z 9 x9 in
  let z = upd z 10 x10 in
  let z = upd z 11 x11 in
  z

inline_for_extraction
val collapse13: #a:Type0 -> zero:a -> ltuple a 13 -> lseq a 13
let collapse13 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12 = x in
  let z = create 13 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  let z = upd z 8 x8 in
  let z = upd z 9 x9 in
  let z = upd z 10 x10 in
  let z = upd z 11 x11 in
  let z = upd z 12 x12 in
  z

inline_for_extraction
val collapse14: #a:Type0 -> zero:a -> ltuple a 14 -> lseq a 14
let collapse14 #t zero x =
  let x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13 = x in
  let z = create 14 zero in
  let z = upd z 0 x0 in
  let z = upd z 1 x1 in
  let z = upd z 2 x2 in
  let z = upd z 3 x3 in
  let z = upd z 4 x4 in
  let z = upd z 5 x5 in
  let z = upd z 6 x6 in
  let z = upd z 7 x7 in
  let z = upd z 8 x8 in
  let z = upd z 9 x9 in
  let z = upd z 10 x10 in
  let z = upd z 11 x11 in
  let z = upd z 12 x12 in
  let z = upd z 13 x13 in
  z


let collapse #t #len x =
  match len with
  | 2 -> collapse2 #t x
  | 3 -> collapse3 #t x
  | 4 -> collapse4 #t x
  | 5 -> collapse5 #t x
  | 6 -> collapse6 #t x
  | 7 -> collapse7 #t x
  | 8 -> collapse8 #t x
  | 9 -> collapse9 #t x
  | 10 -> collapse10 #t x
  | 11 -> collapse11 #t x
  | 12 -> collapse12 #t x
  | 13 -> collapse13 #t x
  | 14 -> collapse14 #t x
