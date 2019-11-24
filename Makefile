all:
	bnfc codi.cf
	happy -gca ParCodi.y
	alex -g LexCodi.x
	ghc --make TestCodi.hs -o TestCodi
	ghc --make interpreter.hs -o interpreter

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi *.x *.hi *.o AbsCodi.hs DocCodi.hs  ErrM.hs  PrintCodi.hs ParCodi.hs SkelCodi.hs TestCodi.hs DocCodi.txt LexCodi.hs ParCodi.y TestCodi interpreter *.bak

distclean: clean
	-rm -f DocCodi.* LexCodi.* ParCodi.* LayoutCodi.* SkelCodi.* PrintCodi.* TestCodi.* AbsCodi.* TestCodi ErrM.* SharedString.* ComposOp.* codi.dtd XMLCodi.* Makefile*
	

