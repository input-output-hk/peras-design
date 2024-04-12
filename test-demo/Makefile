
default : typecheck

typecheck :
	agda2hs src/Overview.lagda.md
	@rm -f src/Overview.hs
	fourmolu -i src/TestModel.hs src/CommonTypes.hs

test : typecheck
	cabal test
