include ../../../code/Makefile.include

VERIFY= \
  Box.Indexing \
  Box.Plain \
	Box.AE \
  Box.ODH \
	Box.PKAE
LAX=

all: all-ver $(addsuffix .fst-lax, $(LAX))

verify: $(addsuffix .fst-ver, $(filter-out $(LAX), $(VERIFY)))
hints: $(addsuffix .fst.hints, $(VERIFY))
lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))

all-ver: verify
all-hints: hints
all-lax: lax

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) \
	--include /home/markulf/everest/FStar/ucontrib/Platform/fst/ \
  --include /home/markulf/everest/FStar/ucontrib/CoreCrypto/fst/ \
  --include /home/markulf/everest/hacl-star/specs/ \
  --include /home/markulf/everest/hacl-star/specs/experimental/ \
  --include /home/markulf/everest/hacl-star/secure_api/utils/ \
  --include /home/markulf/everest/hacl-star/code/lib/ \
  --include /home/markulf/everest/kremlin/kremlib/ \
	$(basename $@).fst

# (Re-)Generate hints
%.fst.hints:
	$(FSTAR) --record_hints \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Lax verifying one file at a time
%.fst-lax:
	$(FSTAR) --lax \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

all-assumes: $(addsuffix .fst, $(VERIFY) $(LAX))
	grep "\(assume\)\|\(admit\)\|\(lax\)" $^
