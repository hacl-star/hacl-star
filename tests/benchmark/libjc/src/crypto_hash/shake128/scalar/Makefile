# -*- Makefile -*-

.PHONY: default clean

default: shake128.japp shake128.s
	@true

clean:
	rm -f shake128.japp shake128.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
