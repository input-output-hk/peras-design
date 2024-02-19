# Inspired by https://git.app.uib.no/hott/agda-unimath/-/blob/6f6a48c92912da3f1245b846c5439c63d1461792/Makefile
AGDAFILES := $(wildcard src/**/*.agda)
AGDAIFILES := $(patsubst %.agda,%.agdai,$(AGDAFILES))
HSDIR=peras-hs
HSFILES := $(patsubst %.agda,$(HSDIR)/%.hs,$(AGDAFILES))
AGDAFLAGS := -i src
AGDA ?= agda
AGDA2HS ?= agda2hs
AGDA_LIBS ?= $(HOME)/.agda/libraries

.PHONY: typecheck

typecheck: $(AGDAIFILES) $(HSFILES)


# From https://stackoverflow.com/questions/34621364/makefile-compile-o-from-c-files
$(AGDAIFILES): %.agdai: %.agda
	@$(AGDA)  --library-file=$(AGDA_LIBS) $(AGDAFLAGS) $^

$(HSDIR)/%.hs: %.agda
	@$(AGDA2HS) --library-file=$(AGDA_LIBS) --compile-dir=$(HSDIR)/src $^

.PHONY : clean veryclean
clean:
	@echo "Removing .agdai files"
	@find src -name \*.agdai -delete;
