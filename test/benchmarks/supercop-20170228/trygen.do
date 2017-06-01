#!/bin/sh

for o in \
core hashblocks hash stream onetimeauth auth secretbox aead \
scalarmult box dh sign encrypt
do
  ./trygen.py $o > crypto_$o/try.c
done
