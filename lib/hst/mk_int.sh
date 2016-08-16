#!/bin/bash

# Taken from the FStar repository

for i in 8 16 32 64 128; do
  f=Hacl.UInt$i.fst
  cat > $f <<EOF
module Hacl.UInt$i
(* This module generated automatically using [mk_int.sh] *)

open FStar.UInt$i
module U = FStar.UInt$i
EOF
  cat Hacl.UIntN.fstp >> $f
  if [ $i -eq 8 ]; then
    echo "type byte = t" >> $f
  fi
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

assume val mul_wide: a:Hacl.UInt64.t -> b:Hacl.UInt64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Hacl.UInt64.v a * Hacl.UInt64.v b))
EOF
  fi
done
