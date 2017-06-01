#!/bin/bash

# Taken from the FStar repository

for i in 8 16 32 64; do
  f=Hacl.UInt$i.fst
  cat > $f <<EOF
module Hacl.UInt$i
(* This module generated automatically using [mk_int.sh] *)

include FStar.UInt$i

EOF
  cat Hacl.UIntN.fstp >> $f
  if [ $i -eq 8 ]; then
    echo "type byte = t" >> $f
  fi
done
