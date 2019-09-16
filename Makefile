all:
	happy -gca ParLambing.y
	alex -g LexLambing.x
	ghc --make Interpreter.hs -o interpreter

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocLambing.* LexLambing.* ParLambing.* LayoutLambing.* SkelLambing.* PrintLambing.* TestLambing.* AbsLambing.* TestLambing ErrM.* SharedString.* ComposOp.* lambing.dtd XMLLambing.* Makefile*
	

