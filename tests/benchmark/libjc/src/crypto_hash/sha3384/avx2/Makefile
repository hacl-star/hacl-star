# -*- Makefile -*-

.PHONY: default clean

default: sha3384.japp sha3384.s
	@true

clean:
	rm -f sha3384.japp sha3384.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
