FILE=main.tex 

all:
	latexmk -pdf -shell-escape ${FILE}

clean:
	rm -rf *.aux *.glg *.glo *.gls *.ist *.listing
	rm -rf *.pdf *.log *.out *.thm *.toc _minted-main
