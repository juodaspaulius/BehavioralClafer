
all:
	bnfc clafer.cf
	happy -gca Parclafer.y
	alex -g Lexclafer.x
	ghc --make Testclafer.hs -o Testclafer

clean:
	-rm -f Docclafer.* Lexclafer.* Parclafer.* Skelclafer.* Printclafer.* Testclafer.* Absclafer.* ErrM.* Testclafer.hi Testclafer.o


ltl:
	bnfc ltl.cf
	happy -gca Parltl.y
	alex -g Lexltl.x
	ghc --make Testltl.hs -o Testltl
