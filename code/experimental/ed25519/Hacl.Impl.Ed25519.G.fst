module Hacl.Impl.Ed25519.G

open FStar.Buffer


val make_g:
  g:Hacl.Impl.Ed25519.ExtPoint.point ->
  Stack unit
    (requires (fun h -> live h g))
    (ensures (fun h0 _ h1 -> live h1 g /\ modifies_1 g h0 h1))
let make_g g =
  let gx = Hacl.Impl.Ed25519.ExtPoint.getx g in
  let gy = Hacl.Impl.Ed25519.ExtPoint.gety g in
  let gz = Hacl.Impl.Ed25519.ExtPoint.getz g in
  let gt = Hacl.Impl.Ed25519.ExtPoint.gett g in
  Hacl.Lib.Create64.make_h64_5 gx 0x00062d608f25d51auL 0x000412a4b4f6592auL 0x00075b7171a4b31duL 0x0001ff60527118feuL 0x000216936d3cd6e5uL;
  Hacl.Lib.Create64.make_h64_5 gy 0x0006666666666658uL 0x0004ccccccccccccuL 0x0001999999999999uL 0x0003333333333333uL 0x0006666666666666uL;
  Hacl.Lib.Create64.make_h64_5 gz 0x0000000000000001uL 0x0000000000000000uL 0x0000000000000000uL 0x0000000000000000uL 0x0000000000000000uL;
 Hacl.Lib.Create64.make_h64_5 gt 0x00068ab3a5b7dda3uL 0x00000eea2a5eadbbuL 0x0002af8df483c27euL 0x000332b375274732uL 0x00067875f0fd78b7uL
