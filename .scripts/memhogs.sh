#!/bin/bash

echo "MEMHOGS := "
# Find all runlim files, extract consumed memory and output files in order of increasing memory
find . -name '*.runlim' | while read fn; do
  M=$(sed -n 's/.*space:[[:space:]]*\([0-9]*\) MB.*/\1/p' $fn)
  echo "$fn $M"
done | sort -nk2 | tail -n 20 | awk ' { print $1 } ' | while read fn; do
  # remove ./ prefix if there, since make doesn't canonicalize paths
  fn=${fn#./}
  echo "    $fn \\"
done
echo ""
