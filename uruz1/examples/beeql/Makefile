OCAMLC = ocamlopt
CMO = cmx
CMA = cmxa

LIBS =

beeql:	flags.$(CMO) beeql_utils.$(CMO) beeql_ast.$(CMO) beeql_parser.$(CMO) beeql_lexer.$(CMO) beeql_main.$(CMO) main.$(CMO)
	$(OCAMLC) -o beeql $(LIBS) flags.$(CMO) beeql_utils.$(CMO) beeql_ast.$(CMO) beeql_parser.$(CMO) beeql_lexer.$(CMO) beeql_main.$(CMO) main.$(CMO)

main.$(CMO):	main.ml beeql_main.$(CMO) beeql_parser.$(CMO) beeql_lexer.$(CMO) beeql_ast.$(CMO) beeql_utils.$(CMO) flags.$(CMO)
	$(OCAMLC) -c main.ml

flags.$(CMO):	flags.ml
	$(OCAMLC) -c flags.ml

beeql_Makefile:	beeql.gra
	uruz beeql.gra

clean:	beeql_clean
	rm -rf *.o *.cm* *.mli beeql_main.ml beeql_utils.ml beeql_ast.ml beeql_parser.ml beeql_parser.mly beeql_lexer.ml beeql_lexer.mll beeql_Makefile

include beeql_Makefile
