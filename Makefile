# Inspired by https://git.app.uib.no/hott/agda-unimath/-/blob/6f6a48c92912da3f1245b846c5439c63d1461792/Makefile
AGDAFILES := $(wildcard src/**/*.agda)
AGDAIFILES := $(patsubst %.agda,%.agdai,$(AGDAFILES))
HSFILES := $(patsubst %.agda,%.hs,$(AGDAFILES))
AGDAFLAGS := -i src
AGDA ?= agda
AGDA2HS ?= agda2hs
AGDA_LIBS ?=

.PHONY: typecheck

typecheck: $(AGDAIFILES) $(HSFILES)

# From https://stackoverflow.com/questions/34621364/makefile-compile-o-from-c-files
$(AGDAIFILES): %.agdai: %.agda
	@$(AGDA) $(AGDAFLAGS) $^

$(HSFILES): %.hs: %.agda
	@$(AGDA2HS) $(AGDA_LIBS) $^

.PHONY : clean veryclean
clean:
	@echo "Removing .agdai files"
	@find src -name \*.agdai -delete;

veryclean: clean
	@echo "Removing .hs files"
	@find src -name \*.hs -delete;
