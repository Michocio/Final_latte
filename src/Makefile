all:
	happy -i -gca ParGrammar.y
	alex -i -g LexGrammar.x
	ghc --make CompilerMain.hs -o ../latc_llvm  -idirs:middle/:frontEnd/:backEnd
	-rm -f middle/*.log middle/*.aux middle/*.hi middle/*.o middle/*.dvi
	-rm -f backEnd/*.log backEnd/*.aux backEnd/*.hi backEnd/*.o backEnd/*.dvi
	-rm -f frontEnd/*.log frontEnd/*.aux frontEnd/*.hi frontEnd/*.o frontEnd/*.dvi
	-rm -f *.log *.aux *.hi *.o *.dvi

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocGrammar.* LexGrammar.* ParGrammar.* LayoutGrammar.* SkelGrammar.* PrintGrammar.* TestGrammar.* AbsGrammar.* TestGrammar ErrM.* SharedString.* ComposOp.* grammar.dtd XMLGrammar.* Makefile*
