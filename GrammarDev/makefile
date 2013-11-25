

all:
	bnfc clafer.cf
	happy -gca Parclafer.y
	alex -g Lexclafer.x
	ghc --make Testclafer.hs -o Testclafer

test: 
	./runtests.sh


clean:
	-rm -f Docclafer.* Lexclafer.* Parclafer.* Skelclafer.* Printclafer.* Testclafer.* Absclafer.* ErrM.* Testclafer.hi Testclafer.o
	-rm -f Docclafer2.* Lexclafer2.* Parclafer2.* Skelclafer2.* Printclafer2.* Testclafer2.* Absclafer2.* ErrM.* Testclafer2.hi Testclafer2.o


ltl:
	bnfc ltl.cf
	happy -gca Parltl.y
	alex -g Lexltl.x
	ghc --make Testltl.hs -o Testltl
