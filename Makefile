# Inspired by https://git.app.uib.no/hott/agda-unimath/-/blob/6f6a48c92912da3f1245b846c5439c63d1461792/Makefile
AGDAFILES := $(wildcard src/**/*.agda)
LAGDAFILES := $(wildcard src/**/*.lagda.md)
HSDIR=peras-hs
HSFILES := $(patsubst %.agda,$(HSDIR)/%.hs,$(AGDAFILES))
LHSFILES := $(patsubst %.lagda.md,$(HSDIR)/%.hs,$(LAGDAFILES))
AGDAFLAGS := -i src
AGDA ?= agda
AGDA2HS ?= agda2hs
AGDA_LIBS ?= $(HOME)/.agda/libraries

$(info $(HSFILES))
$(info $(LHSFILES))

.PHONY: typecheck

all: typecheck
	cabal update
	cabal build all

typecheck: $(HSFILES) $(LHSFILES)

# From https://stackoverflow.com/questions/34621364/makefile-compile-o-from-c-files
$(HSDIR)/%.hs: %.agda
	@$(AGDA2HS) --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^
	@$(AGDA) --compile --ghc-dont-call-ghc --no-main --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^

$(HSDIR)/%.hs: %.lagda.md
	@$(AGDA2HS) --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^
	@$(AGDA) --compile --ghc-dont-call-ghc --no-main --local-interfaces --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^

.PHONY : clean veryclean
clean:
	@echo "Removing .agdai files"
	@find src -name \*.agdai -delete;

veryclean: clean
	@echo "Removing generated.hs files"
	@rm $(HSFILES) $(LHSFILES)
