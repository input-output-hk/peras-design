# Inspired by https://git.app.uib.no/hott/agda-unimath/-/blob/6f6a48c92912da3f1245b846c5439c63d1461792/Makefile
AGDAFILES := $(wildcard src/**/*.agda)
AGDAIFILES := $(patsubst %.agda,%.agdai,$(AGDAFILES))
AGDAFLAGS := -i src
AGDA ?= agda

.PHONY: typecheck

typecheck: $(AGDAIFILES)

# From https://stackoverflow.com/questions/34621364/makefile-compile-o-from-c-files
$(AGDAIFILES): %.agdai: %.agda
	@$(AGDA) $(AGDAFLAGS) $^

.PHONY : clean
clean:
	@echo "Removing .agdai files"
	@find src -name \*.agdai -exec rm {} \;
