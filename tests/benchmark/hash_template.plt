set terminal svg
set datafile separator ","
set datafile commentschars "//"
set output 'bench_hash_1024.svg'
set xtics rotate
set boxwidth 0.5
set style fill solid
set key on
plot 'bench_hash_1024.csv' using 5:xticlabels(1) with boxes title columnheader