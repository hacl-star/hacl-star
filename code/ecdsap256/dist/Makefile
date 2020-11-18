
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1

CFLAGS += -I . -march=native -mtune=native -O3
export CFLAGS

test.exe: Hacl_P256.o
	$(CC) $(CFLAGS) \
	test.c  $^ \
	-o test.exe

