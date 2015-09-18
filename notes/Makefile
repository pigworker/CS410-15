default : notes.pdf

notes.tex : notes.lagda Introduction.lagda EmacsCheatSheet.lagda
	lhs2TeX --agda notes.lagda > notes.tex

notes.aux : notes.tex
	latex notes

notes.blg : notes.aux CS410.bib
	bibtex notes

notes.dvi : notes.tex notes.blg
	latex notes
	latex notes

notes.pdf : notes.tex notes.blg
	pdflatex notes
	cp notes.pdf ../CS410-notes.pdf


