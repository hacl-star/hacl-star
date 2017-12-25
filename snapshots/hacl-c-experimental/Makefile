FSTAR_HOME   ?= ../../dependencies/FStar
KREMLIN_HOME ?= ../../dependencies/kremlin
OPENSSL_HOME ?= ../../dependencies/openssl
LIBSODIUM_HOME ?= ../../dependencies/libsodium


CC=gcc-7 -flto

.PHONY: test clean

test: test-random

test-random:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c cpuid.c drng.c Random.c test-random.c -o test-random.exe
	./test-random.exe

clean:
	rm -rf *~ *.exe *.out
