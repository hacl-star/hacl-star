
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1

dist/%.o: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic $(notdir $@)

test.exe: Hacl_P256.o
	$(CC) $(CFLAGS) \
	test.c  $^ \
	-o test.exe

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean


