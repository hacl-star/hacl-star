module EverCrypt.Cipher

let chacha20 len dst src key iv ctr =
  Hacl.Impl.Chacha20.chacha20_encrypt len dst src key iv ctr
