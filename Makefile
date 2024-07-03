# Inspired by https://git.app.uib.no/hott/agda-unimath/-/blob/6f6a48c92912da3f1245b846c5439c63d1461792/Makefile
AGDAFILES := $(shell find src -name *.agda -exec grep -l AGDA2HS {} \;)
LAGDAFILES := $(shell find src -name *.lagda.md -exec grep -l AGDA2HS {} \;)
SIMAGDAFILES := $(shell find sim_src -name *.agda -exec grep -l AGDA2HS {} \;)
HSDIR=peras-simulation
HSFILES := $(patsubst %.agda,$(HSDIR)/%.hs,$(AGDAFILES))
LHSFILES := $(patsubst %.lagda.md,$(HSDIR)/%.hs,$(LAGDAFILES))
SIMHSFILES := $(patsubst sim_src/%.agda,peras-simulation/src/%.hs,$(SIMAGDAFILES))
BADSIMHSFILES := $(patsubst $(HSDIR)/%.hs,peras-simulation/%.hs,$(HSFILES) $(LHSFILES))
AGDA ?= agda
AGDA2HS ?= agda2hs
AGDA2HS_CONFIG ?= rewrites.yaml
AGDA_LIBS ?= $(HOME)/.agda/libraries

$(info $(HSFILES))
$(info $(LHSFILES))

.PHONY: typecheck

all: typecheck
	cabal build all

test:
	cabal test all

typecheck: $(HSFILES) $(LHSFILES) $(SIMHSFILES)

$(HSDIR)/%.hs: %.agda
	@$(AGDA) --local-interfaces --library-file=$(AGDA_LIBS) $^
	@$(AGDA2HS) --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src --config $(AGDA2HS_CONFIG) $^

$(HSDIR)/%.hs: %.lagda.md
	@$(AGDA) --local-interfaces --library-file=$(AGDA_LIBS) $^
	@$(AGDA2HS) --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src --config $(AGDA2HS_CONFIG) $^

.PHONY : clean

clean:
	@echo "Removing .agdai files"
	@find src -name \*.agdai -delete;
	@echo "Removing generated .hs files"
	@rm -f $(HSFILES) $(LHSFILES)
