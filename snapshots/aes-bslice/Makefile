
CC?=gcc-8
CCOPTS=-O3 -Wall -Wextra -march=native -mtune=native 
#CCOPTS=-O3 -Wall -Wextra -m64 -mtune=generic

aes: aes_generic4_test.exe aes_test.exe tiny_aes_test.exe aes_bslice_test.exe aes_ni_test.exe aes_bslice4_test.exe aes_ni4_test.exe aes_ni_bear_test.exe
gcm: gf128_test.exe gf128_ni_test.exe gf128_ni4_test.exe

all: aes gcm

gf128_test.exe: gf128.c gf128_test.c
	$(CC) $(CCOPTS) gf128.c gf128_test.c -o gf128_test.exe
	./gf128_test.exe

gf128_4_test.exe: gf128_4.c gf128_test.c
	$(CC) $(CCOPTS) gf128_4.c gf128_test.c -o gf128_4_test.exe
	./gf128_4_test.exe

gf128_4x_test.exe: gf128_4x.c gf128_test.c
	$(CC) $(CCOPTS) gf128_4x.c gf128_test.c -o gf128_4x_test.exe
	./gf128_4x_test.exe

gf128_u128_test.exe: gf128_u128.c gf128_test.c
	$(CC) $(CCOPTS) gf128_u128.c gf128_test.c -o gf128_u128_test.exe
	./gf128_u128_test.exe

gf128_bear_test.exe: gf128_bear_ctmul64.c gf128_test.c
	$(CC) $(CCOPTS) gf128_bear_ctmul64.c gf128_test.c -o gf128_bear_test.exe
	./gf128_bear_test.exe

gf128_ni_test.exe: gf128_ni.c gf128_test.c
	$(CC) $(CCOPTS) gf128_ni.c gf128_test.c -o gf128_ni_test.exe
	./gf128_ni_test.exe

gf128_ni4_test.exe: gf128_ni4.c gf128_test.c
	$(CC) $(CCOPTS) gf128_ni4.c gf128_test.c -o gf128_ni4_test.exe
	./gf128_ni4_test.exe


chacha20_test.exe: chacha20.c chacha20_test.c
	$(CC) $(CCOPTS) chacha20.c chacha20_test.c -o chacha20_test.exe
	./chacha20_test.exe

chacha20_old_test.exe: chacha20_old.c chacha20_test.c
	$(CC) $(CCOPTS) chacha20_old.c chacha20_test.c -o chacha20_old_test.exe
	./chacha20_old_test.exe

aes_test.exe: aes.c aes_test.c
	$(CC) $(CCOPTS) aes.c aes_test.c -o aes_test.exe
	./aes_test.exe

aes_generic4_test.exe: aes_generic4.c aes_test.c
	$(CC) $(CCOPTS) aes_generic4.c aes_test.c -o aes_generic4_test.exe
	./aes_generic4_test.exe

tiny_aes_test.exe: tiny-aes.c aes_test.c
	$(CC) $(CCOPTS) tiny-aes.c aes_test.c -o tiny_aes_test.exe
	./tiny_aes_test.exe

aes_ni_test.exe: aes_ni.c aes_test.c
	$(CC) $(CCOPTS) -maes aes_ni.c aes_test.c -o aes_ni_test.exe
	./aes_ni_test.exe

aes_ni_bear_test.exe: aes_ni_bear.c aes_test.c
	$(CC) $(CCOPTS) -maes aes_ni_bear.c aes_test.c -o aes_ni_bear_test.exe
	./aes_ni_bear_test.exe

aes_ni4_test.exe: aes_ni4.c aes_test.c
	$(CC) $(CCOPTS) -maes aes_ni4.c aes_test.c -o aes_ni4_test.exe
	./aes_ni4_test.exe

aes_bslice_test.exe: aes_bslice.c aes_test.c
	$(CC) $(CCOPTS) aes_bslice.c aes_test.c -o aes_bslice_test.exe
	./aes_bslice_test.exe

aes_bslice4_test.exe: aes_bslice4.c aes_test.c
	$(CC) $(CCOPTS) aes_bslice4.c aes_test.c -o aes_bslice4_test.exe
	./aes_bslice4_test.exe

aes_generic4_test.exe: aes_generic4.c aes_test.c
	$(CC) $(CCOPTS) aes_generic4.c aes_test.c -o aes_generic4_test.exe
	./aes_generic4_test.exe

aes_bslice8_test.exe: aes_bslice8.c aes_test.c
	$(CC) $(CCOPTS) aes_bslice8.c aes_test.c -o aes_bslice8_test.exe
	./aes_bslice8_test.exe

clean:
	rm -f *.exe
