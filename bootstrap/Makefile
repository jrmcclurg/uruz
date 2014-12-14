OCAMLC = ocamlopt
CMO = cmx
CMA = cmxa

LIBS = str.$(CMA) unix.$(CMA)

bootstrap:	code.$(CMO) flags.$(CMO) bootstrap_utils.$(CMO) bootstrap_ast.$(CMO) bootstrap_parser.$(CMO) bootstrap_lexer.$(CMO) bootstrap_main.$(CMO) main.$(CMO)
	$(OCAMLC) -o bootstrap $(LIBS) bootstrap_utils.$(CMO) bootstrap_ast.$(CMO) bootstrap_parser.$(CMO) bootstrap_lexer.$(CMO) bootstrap_main.$(CMO) flags.$(CMO) code.$(CMO) main.$(CMO)

main.$(CMO):	main.ml bootstrap_main.$(CMO) bootstrap_parser.$(CMO) bootstrap_lexer.$(CMO) bootstrap_ast.$(CMO) bootstrap_utils.$(CMO) flags.$(CMO) code.$(CMO)
	$(OCAMLC) -c main.ml

flags.$(CMO):	flags.ml bootstrap_utils.$(CMO)
	$(OCAMLC) -c flags.ml

code.$(CMO):	code.ml flags.$(CMO) bootstrap_utils.$(CMO) bootstrap_ast.$(CMO)
	$(OCAMLC) -c code.ml

bootstrap_Makefile:	bootstrap.gra
	pgg -footer-parser bootstrap.gra

clean:	bootstrap_clean
	rm -rf *.o *.cm* *.mli bootstrap_main.ml bootstrap_utils.ml bootstrap_ast.ml bootstrap_parser.ml bootstrap_parser.mly bootstrap_lexer.ml bootstrap_lexer.mll bootstrap_Makefile

include bootstrap_Makefile
