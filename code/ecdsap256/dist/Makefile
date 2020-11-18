
# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1

# An archive with all the compiled code in this directory.
# We don't want Hacl_Test_ECDSA.o to be included so we redefine OBJS
dist/libecdsa.a:dist/Hacl_P256.o
	$(MAKE) -C dist -f Makefile.basic OBJS=$(notdir $^) $(notdir $@)
	
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


