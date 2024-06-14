# Inspired by https://git.app.uib.no/hott/agda-unimath/-/blob/6f6a48c92912da3f1245b846c5439c63d1461792/Makefile
AGDAFILES := $(shell find src -name *.agda)
LAGDAFILES := $(shell find src -name *.lagda.md)
SIMAGDAFILES := $(shell find sim_src -name *.agda)
HSDIR=peras-hs
HSFILES := $(patsubst %.agda,$(HSDIR)/%.hs,$(AGDAFILES))
LHSFILES := $(patsubst %.lagda.md,$(HSDIR)/%.hs,$(LAGDAFILES))
SIMHSFILES := $(patsubst sim_src/%.agda,peras-simulation/src/%.hs,$(SIMAGDAFILES))
BADSIMHSFILES := $(patsubst $(HSDIR)/%.hs,peras-simulation/%.hs,$(HSFILES) $(LHSFILES))
AGDA ?= agda
AGDA2HS ?= agda2hs
AGDA_LIBS ?= $(HOME)/.agda/libraries

.PHONY: typecheck

all: typecheck
	cabal update
	cabal build all

typecheck: $(HSFILES) $(LHSFILES) $(SIMHSFILES)
	@rm -f $(BADSIMHSFILES)

# From https://stackoverflow.com/questions/34621364/makefile-compile-o-from-c-files
$(HSDIR)/%.hs: %.agda
	@$(AGDA2HS) --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^
	@$(AGDA) --compile --ghc-dont-call-ghc --no-main --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^

$(HSDIR)/%.hs: %.lagda.md
	@$(AGDA2HS) --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^
	@$(AGDA) --compile --ghc-dont-call-ghc --no-main --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^

peras-simulation/src/%.hs : sim_src/%.agda
	@$(AGDA2HS) --library-file=$(AGDA_LIBS) --compile-dir=peras-simulation/src $^

.PHONY : clean veryclean
clean:
	@echo "Removing .agdai files"
	@find src -name \*.agdai -delete;

veryclean: clean
	@echo "Removing generated.hs files"
	@rm $(HSFILES) $(LHSFILES)
