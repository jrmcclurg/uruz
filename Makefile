
# use the "-ccopt -static" $(OCAMLC) switch to statically link

#OCAMLC = ocamlcp -p a
#OCAMLC = ocamlopt -p -g

#OCAMLC = ocamlopt -ccopt -O2
#CMO = cmx
#CMA = cmxa

OCAMLC = ocamlc
CMO = cmo
CMA = cma

LIBS = str.$(CMA)
#unix.$(CMA)

pgg:	version.$(CMO) flags.$(CMO) utils.$(CMO) ast.$(CMO) code.$(CMO) parser.$(CMO) lexer.$(CMO) main.$(CMO)
	$(OCAMLC) -o pgg $(LIBS) version.$(CMO) flags.$(CMO) utils.$(CMO) ast.$(CMO) code.$(CMO) parser.$(CMO) lexer.$(CMO) main.$(CMO)

main.$(CMO):	main.ml parser.$(CMO) lexer.$(CMO) code.$(CMO) ast.$(CMO) utils.$(CMO) flags.$(CMO) version.$(CMO)
		$(OCAMLC) -c main.ml

parser.$(CMO):	parser.ml parser.cmi utils.$(CMO)
		$(OCAMLC) -c parser.ml

lexer.$(CMO):	lexer.ml parser.cmi ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c lexer.ml

code.$(CMO):	code.ml ast.$(CMO) utils.$(CMO) flags.$(CMO)
		$(OCAMLC) -c code.ml

parser.cmi:	parser.mli ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c parser.mli

ast.$(CMO):	ast.ml utils.$(CMO)
		$(OCAMLC) -c ast.ml

parser.ml:	parser.mly
		ocamlyacc parser.mly

parser.mli:	parser.mly
		ocamlyacc parser.mly

lexer.ml:	lexer.mll
		ocamllex lexer.mll

utils.$(CMO):	utils.ml flags.$(CMO)
		$(OCAMLC) -c utils.ml

flags.$(CMO):	flags.ml version.$(CMO)
		$(OCAMLC) -c flags.ml

version.$(CMO): version.ml
		$(OCAMLC) -c version.ml

version:
		echo let commit = \"`git log -n 1 --pretty=oneline | sed "s/\s.*//g"`\"\;\; > version.ml
		echo let commit_num = \"`git shortlog -s | sed "s/\s*\([0-9]*\)\s*.*$$/\1/g"`\"\;\; >> version.ml
		echo let commit_date = \"`git log -n 1 --date=rfc | grep Date | sed "s/Date:\s*//g"`\"\;\; >> version.ml
		echo let build_date = \"`date -R`\"\;\; >> version.ml

clean:		
		rm -rf *.o *.cm* *.mli parser.ml lexer.ml

wc:		
		wc -l lexer.mll parser.mly ast.ml utils.ml pp.ml main.ml 
