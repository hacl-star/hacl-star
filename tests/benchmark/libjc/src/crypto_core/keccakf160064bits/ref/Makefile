# -*- Makefile -*-

.PHONY: default clean

default: keccak_f1600_export.japp keccak_f1600_export.s
	@true

clean:
	rm -f keccak_f1600_export.japp keccak_f1600_export.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
