
all:
	bnfc clafer.cf
	happy -gca Parclafer.y
	alex -g Lexclafer.x
	ghc --make Testclafer.hs -o Testclafer

alt:
	bnfc clafer2.cf
	happy -gca Parclafer2.y
	alex -g Lexclafer2.x
	ghc --make Testclafer2.hs -o Testclafer2

test:
	./Testclafer < test.cfr

testalt:
	./Testclafer2 < test.cfr


clean:
	-rm -f Docclafer.* Lexclafer.* Parclafer.* Skelclafer.* Printclafer.* Testclafer.* Absclafer.* ErrM.* Testclafer.hi Testclafer.o
	-rm -f Docclafer2.* Lexclafer2.* Parclafer2.* Skelclafer2.* Printclafer2.* Testclafer2.* Absclafer2.* ErrM.* Testclafer2.hi Testclafer2.o


ltl:
	bnfc ltl.cf
	happy -gca Parltl.y
	alex -g Lexltl.x
	ghc --make Testltl.hs -o Testltl
