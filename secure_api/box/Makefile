include ../../Makefile.include

VERIFY= \
	Box.Index \
	Box.Plain \
	Box.AE \
	Box.ODH \
	Box.PKAE \
	Box.KDF
LAX=

FSTAR_INCLUDES+= \
	--include $(FSTAR_HOME)/ucontrib/Platform/fst/ \
	--include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst/ \
	--include $(HACL_HOME)/specs/ \
	--include $(HACL_HOME)/specs/experimental/ \
	--include $(HACL_HOME)/secure_api/utils/ \
	--include $(HACL_HOME)/code/lib/ \
	--include $(KREMLIN_HOME)/kremlib/


all: all-ver $(addsuffix .fst-lax, $(LAX))

verify: $(addsuffix .fst-verify, $(filter-out $(LAX), $(VERIFY)))
hints: $(addsuffix .fst.hints, $(VERIFY))
lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))R

all-ver: verify
all-hints: hints
all-lax: lax

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) --log_queries $(INCLUDE) \
	$(basename $@).fst

all-assumes: $(addsuffix .fst, $(VERIFY) $(LAX))
	grep "\(assume\)\|\(admit\)\|\(lax\)" $^
