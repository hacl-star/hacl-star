# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS := ref3 avx avx2

# --------------------------------------------------------------------
.PHONY: default clean

default:
	for i in ref3 avx avx2; do $(MAKE) -C $$i; done

clean:
	for i in ref3 avx avx2; do $(MAKE) -C $$i clean; done
