# Linux specific compilation instruction for PneuTube
ifeq ($(UNAME), Linux)
  KREMLIN_ARGS+=-ccopt -D_GNU_SOURCE
endif

extract-c:
	$(MAKE) -C pneutube tube-star.exe

clean:
	$(MAKE) -C pneutube clean
