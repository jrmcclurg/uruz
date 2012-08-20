final:		final.pdf

paper:		paper.pdf

cover:		cover.pdf

final.pdf:	cover.pdf paper.pdf
		gs -q -sPAPERSIZE=letter -dPDFFitPage -dNOPAUSE -dBATCH -sDEVICE=pdfwrite \
		-sOutputFile=final.pdf cover.pdf paper.pdf

paper.pdf:	paper.tex paper.bbl
		pdflatex paper.tex

paper.bbl:	paper.bib
		pdflatex paper.tex
		bibtex paper
		pdflatex paper.tex

cover.pdf:	cover.tex nwu.eps
		./run

clean:
		@rm -rf *.bbl *.aux *.ps *.blg *.log paper.pdf cover.pdf
