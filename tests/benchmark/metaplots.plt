set terminal svg 1000,500
# set terminal pdfcairo color size 12cm,5cm font "Arial,6pt"
set datafile separator ","
set datafile commentschars "//"
set xtics norotate
set style fill solid
set yrange[0:]
set key off
set boxwidth 0.8
set style histogram clustered gap 3 title
set style data histograms
set bmargin 3

set key right outside
set ylabel "Avg. performance [cycles/byte]"
set yrange [0:16]

set title "EverCrypt Hash Performance (message size 65536 bytes)"
set output 'bench_meta_hash_evercrypt.pdf'
plot \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-gcc-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-gcc-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-8", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-8", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-clang-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-clang-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-clang-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-8", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-clang-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-8"

set title "OpenSSL Hash Performance (message size 65536 bytes)"
set output 'bench_meta_hash_openssl.pdf'
plot \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-gcc-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-gcc-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-8", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-8", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-clang-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-clang-7/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-clang-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-8", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-clang-8/bench_hash_all_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-8"


set key right outside
set ylabel "Avg. performance [cycles/byte]"
set yrange [0:30]
set xrange[-0.5:2.5]

set title "EverCrypt AEAD Performance (message size 65536 bytes)"
set output 'bench_meta_aead_evercrypt.pdf'
plot \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-gcc-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-gcc-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-8", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-8", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-clang-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-clang-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-7", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-default-clang-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-8", \
  '< grep -e "^\"EverCrypt" -e "^\"Provider" evercrypt-openssl-no-asm-clang-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-8"

set title "OpenSSL AEAD Performance (message size 65536 bytes)"
set output 'bench_meta_aead_openssl.pdf'
plot \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-gcc-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-gcc-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-8", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-gcc-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-8", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-clang-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-clang-7/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-7", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-default-clang-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-8", \
  '< grep -e "^\"OpenSSL" -e "^\"Provider" evercrypt-openssl-no-asm-clang-8/bench_aead_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-8"


set ylabel "Avg. performance [cycles/byte]"
unset yrange
unset xrange

set title "Ed25519 Performance (message size 65536 bytes)"
set output 'bench_meta_ed25519.pdf'
plot \
  'evercrypt-openssl-default-gcc-7/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-7", \
  'evercrypt-openssl-no-asm-gcc-7/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-7", \
  'evercrypt-openssl-default-gcc-8/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-8", \
  'evercrypt-openssl-no-asm-gcc-8/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-8", \
  'evercrypt-openssl-default-clang-7/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-7", \
  'evercrypt-openssl-no-asm-clang-7/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-7", \
  'evercrypt-openssl-default-clang-8/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-8", \
  'evercrypt-openssl-no-asm-clang-8/bench_ed25519_65536.csv' using 'Avg Cycles/Byte':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-8"


set ylabel "Avg. performance [cycles/derivation]"
unset yrange

set title "Curve25519 Performance"
set output 'bench_meta_curve25519.pdf'
plot \
  'evercrypt-openssl-default-gcc-7/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-7", \
  'evercrypt-openssl-no-asm-gcc-7/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-7", \
  'evercrypt-openssl-default-gcc-8/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-gcc-8", \
  'evercrypt-openssl-no-asm-gcc-8/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-gcc-8", \
  'evercrypt-openssl-default-clang-7/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-7", \
  'evercrypt-openssl-no-asm-clang-7/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-7", \
  'evercrypt-openssl-default-clang-8/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-default-clang-8", \
  'evercrypt-openssl-no-asm-clang-8/bench_curve25519.csv' using 'Avg':xticlabels(strcol('Algorithm')) title "evercrypt-openssl-no-asm-clang-8"
