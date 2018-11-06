module Spec.Qdsa

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Spec.SHA2
open Spec.Curve25519

module Hash = Spec.SHA2

let n: elem =
  assert_norm(pow2 252 + 27742317777372353535851937790883648493 < pow2 255 - 19);
  pow2 252 + 27742317777372353535851937790883648493 // Group order

let sha512_modn (len:size_t) (s:lbytes len) : Tot elem =
  (nat_from_bytes_le (Hash.hash512 len s)) % n

let sha512_modn_bar (len:size_t) (s:lbytes len) : Tot elem =
  let h = sha512_modn len s in
  if h % 2 = 0 then h else n - h

let _P = encodePoint (Proj 9 1)
let _A = 486662

let fsub x y =
  if x >= y then
    (x - y) % prime
  else
    (prime + x - y) % prime

#reset-options "--z3rlimit 100 --max_fuel 0"
let sign (public:lbytes 32) (secret:lbytes 64) (len:size_t{len < pow2 32 - 64}) (msg:lbytes len) =
  let d' = slice secret 0 32 in
  let d'_e = nat_from_bytes_le d' in
  let d'' = slice secret 32 64 in
  let _Q = public in
  let msg' = create (len + 32) (u8 0) in
  let msg' = update_slice msg' 0 32 d'' in
  let msg' = update_slice msg' 32 (32+len) msg in
  let r = sha512_modn (len + 32) msg' in
  let rs = nat_to_bytes_le 32 r in
  let _R =  scalarmult' rs _P in
  let msg' = create (len + 64) (u8 0) in
  let msg' = update_slice msg' 0 32 _R in
  let msg' = update_slice msg' 32 64 _Q in
  let msg' = update_slice msg' 64 (len+64) msg in
  let h = sha512_modn_bar (len + 64) msg' in
  let s = (r - (h * d'_e)) in
  let s = if s >= 0 then s % n else (n+s)%n in
  let s_s = nat_to_bytes_le 32 s in
  let sg = create 64 (u8 0) in
  let sg = update_slice sg 0 32 _R in
  let sg = update_slice sg 32 64 s_s in
  sg


let verify (public:lbytes 32) (len:size_t{len < pow2 32 - 64}) (msg:lbytes len) (sg:lbytes 64) =
  let _Q = public in
  let _R = slice sg 0 32 in
  let s = slice sg 32 64 in
  let msg' = create (len + 64) (u8 0) in
  let msg' = update_slice msg' 0 32 _R in
  let msg' = update_slice msg' 32 64 _Q in
  let msg' = update_slice msg' 64 (len+64) msg in
  let h = sha512_modn_bar (len + 64) msg' in
  let h_s = nat_to_bytes_le 32 h in
  IO.print_string "\n_h_s:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (h_s));
  let _T0 = scalarmult' s _P in
  let _T1 = scalarmult' h_s _Q in
  IO.print_string "\n_T0:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (_T0));
  IO.print_string "\n_T1:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (_T1));
  IO.print_string "\n";
  let xR = decodePoint _R in
  let xT0 = decodePoint _T0 in
  let xT1 = decodePoint _T1 in
  let zR = 1 in
  let zT0 = 1 in
  let zT1 = 1 in
  let _Bxx = ((xT0 *. xT1) -. (zT0 *. zT1)) in
  let _Bxx = _Bxx *. _Bxx in
  let _Bzz = ((xT0 *. zT1) -. (zT0 *. xT1)) in
  let _Bzz = _Bzz *. _Bzz in
  let _Bxz = (((xT0 *. xT1) +. (zT0 *. zT1)) *. ((xT0 *. zT1) +. (zT0 *. xT1))) +. (2 *. _A *. xT0 *. zT0 *. xT1 *. zT1) in
  let _Bzz_xR2 = _Bzz *. xR *. xR in
  let _Bxx_zR2 = _Bxx *. zR *. zR in
  let _2Bxz_xR_zR = 2 *. _Bxz *. xR *. zR in
  let left = (_Bzz_xR2 +. _Bxx_zR2) in
  let right = _2Bxz_xR_zR in
  IO.print_string "\n_left:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (nat_to_bytes_le 32 left));
  IO.print_string "\n_right:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (nat_to_bytes_le 32 right));
  IO.print_string "\n";
  left = right


let keygen (d:lbytes 32) =
  let s = Hash.hash512 32 d in
  let d' = slice s 0 32 in
  let d'' = slice s 32 64 in
  let _Q = scalarmult' d' _P in
  (s,_Q)

let d = List.Tot.map u8 [0x9d; 0x61; 0xb1; 0x9d; 0xef; 0xfd; 0x5a; 0x60;
           0xba; 0x84; 0x4a; 0xf4; 0x92; 0xec; 0x2c; 0xc4;
           0x44; 0x49; 0xc5; 0x69; 0x7b; 0x32; 0x69; 0x19;
           0x70; 0x3b; 0xac; 0x03; 0x1c; 0xae; 0x7f; 0x60]

let msg3 = List.Tot.map u8 [0xaf; 0x82]

let test()  =
    let d = createL d in
    let (s,p) = keygen d in
  IO.print_string "\ns:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (s));
  IO.print_string "\np:";
  List.iter (fun i -> IO.print_string (UInt8.to_string (Lib.RawIntTypes.u8_to_UInt8 i))) (as_list (p));
    let m3 = createL msg3 in
    let sg = sign p s 2 m3 in
    let vr = verify p 2 m3 sg in
    if vr then IO.print_string ("Success\n")
    else IO.print_string ("Failure\n")
