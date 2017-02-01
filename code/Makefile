all: extract-c verify 

verify:
	$(MAKE) -C salsa-family verify
	$(MAKE) -C bignum verify
	$(MAKE) -C poly1305 verify
	$(MAKE) -C curve25519 verify

extract-c:
	$(MAKE) -C salsa-family extract-c
	$(MAKE) -C poly1305 extract-c
	$(MAKE) -C curve25519 extract-c

clean:
	rm -rf *~ *.exe *.out 
	$(MAKE) -C salsa-family clean
	$(MAKE) -C bignum clean
	$(MAKE) -C poly1305 clean
	$(MAKE) -C curve25519 clean
