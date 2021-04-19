#!/usr/bin/env bash

# From: RFC 1321, section A.5 (https://www.ietf.org/rfc/rfc1321.txt)

# On OS X, we need to explicitly use GNU sed
SED=$(if which gsed 2>/dev/null ; then echo gsed ; else echo sed ; fi)

make_byte_sequence () {
  $SED 's!\([0-9a-f][0-9a-f]\)!0x\1uy; !g'
}

{ cat <<EOF
MD5 ("") = d41d8cd98f00b204e9800998ecf8427e
MD5 ("a") = 0cc175b9c0f1b6a831c399e269772661
MD5 ("abc") = 900150983cd24fb0d6963f7d28e17f72
MD5 ("message digest") = f96b697d7cb7938d525a2f31aaf161d0
MD5 ("abcdefghijklmnopqrstuvwxyz") = c3fcd3d76192e4007dfb496cca67e13b
MD5 ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789") = d174ab98d277d9f5a5611c2c9f419d9f
MD5 ("12345678901234567890123456789012345678901234567890123456789012345678901234567890") = 57edf4a22be3c955ac49da2e2107b67a
EOF
} |
tr -d '\r\n' |
$SED 's!MD5 *("\([^"]*\)") *= *\([0-9a-f]*\)!\1\n\2\n!g' |
while read plain
do
  echo -n "(let plain : list FStar.UInt8.t = ["
  echo -n "$plain" | hexdump -e '1/1 "%02x"' | make_byte_sequence
  echo -n "] in let cipher : list FStar.UInt8.t = ["
  read cipher
  echo "$cipher" | make_byte_sequence
  echo "] in Vec MD5 plain cipher);"
done
