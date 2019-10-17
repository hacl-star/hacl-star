.PHONY: x25519_mul_export.s clean

x25519_mul_export.s: x25519_mul_export.japp
	jasminc -pasm x25519_mul_export.japp > $@

x25519_mul_export.japp: x25519_mul_export.jazz x25519_mul.japp
	gpp -o $@ x25519_mul_export.jazz

x25519_mul.japp: x25519_mul.jazz x25519_reduce.japp
	gpp -o $@ x25519_mul.jazz

x25519_reduce.japp: x25519_reduce.jazz
	gpp -o $@ $<

clean:
	rm -f *.s *.japp

