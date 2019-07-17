# -*- Makefile -*-

.PHONY: default clean

# extension .specific to not break current benchmark building system
default: shake256.s shake256.s.specific
	@true

clean:
	rm -f shake256.japp shake256.s shake256.japp.specific shake256.s.specific

# shake256
shake256.japp: shake256.jazz
	gpp -I../../../ -o $@ $<

shake256.s: shake256.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

# shake256 with specific implementation of add full block
shake256.japp.specific: shake256.jazz
	gpp -I../../../ -DKECCAK_1600_SPECIFIC_IMPLEMENTATIONS -o $@ $<

shake256.s.specific: shake256.japp.specific
	jasminc -lea -pasm $< > $@ || rm -f $@
