
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9
CFLAGS += -I . -march=native -mtune=native -O3
export CFLAGS

test.exe: test.c Hacl_P256.c
	$(CC) $(CFLAGS) \
	$^ \
	-o test.exe

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean


