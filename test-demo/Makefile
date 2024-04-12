
default : typecheck

typecheck :
	agda2hs src/Overview.lagda.md
	@rm -f src/Overview.hs
	fourmolu -i src/*.hs

test : typecheck
	cabal test
