all:
	make -C symmetric
	make -C ec
	make -C hash
	make -C hmac
#	make -C hkdf

clean:
	make clean -C symmetric
	make clean -C ec
	make clean -C hash
	make clean -C hmac
	make clean -C hkdf

LIB_DIR=../lib/hst
SYMMETRIC_DIR=symmetric
EC_DIR=ec

top-level-lax:
	fstar.exe --lax Hacl.Box.fst \
		--include $(LIB_DIR) \
		--include $(SYMMETRIC_DIR) \
		--include $(EC_DIR)
