
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9
CFLAGS += -I . -march=native -mtune=native -O3 -Wunused-variable
CProfiling += -pg

export CFLAGS

test.exe: test.c Hacl_Impl_Sparkle1.o Hacl_Spec.o
	$(CC) $(CFLAGS) \
	$^ \
	-o test.exe
