
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1

test.exe: Hacl_P256.o
	$(CC) $(CFLAGS) \
	test.c  $^ \
	-o test.exe

