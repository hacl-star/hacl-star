
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9
CFLAGS += -I . -march=native -mtune=native -O2 -Wunused-variable
CProfiling += -pg

export CFLAGS

test.exe: test.c fiat_changed.o Hacl_P256.o 
	$(CC) $(CFLAGS) \
	$^ \
	-o test.exe



profile: test.c Hacl_P256.o
	$(CC) $(CFLAGS) $(CProfiling) \
	$^ \
	-o test.exe	
	./test.exe
	gprof ./test.exe
