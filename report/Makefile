project_report.pdf: *.tex literature.bib
	latexmk -pdf project_report.tex
pvc-force:
	latexmk --pvc --synctex=1 -f --quiet project_report.tex -pdf
clear:
	rm *.aux *.bbl *.blg *.fls *.dvi *.fdb_latexmk *.log *.out *.synctex.gz project_report.pdf
