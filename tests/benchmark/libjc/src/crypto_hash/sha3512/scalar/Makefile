# -*- Makefile -*-

.PHONY: default clean

default: sha3512.japp sha3512.s
	@true

clean:
	rm -f sha3512.japp sha3512.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
