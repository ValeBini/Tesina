include agda_stdlib.mk

LATEX=latexmk -pdf -use-make
MAIN=main
BIB=bibtex
IDIR=code
CODE=$(wildcard $(IDIR)/*.lagda)
INSTANCES=$(wildcard $(IDIR)/Instances/*.lagda)
STRUCTURES=$(wildcard $(IDIR)/Structures/*.lagda)

all:
	for file in $(CODE) ; do \
	    	agda --latex  $$file --include-path=$(AGDA_STDLIB) --include-path=$(IDIR) ; \
	done	
	for file in $(INSTANCES) ; do \
	    	agda --latex  $$file --include-path=$(AGDA_STDLIB) --include-path=$(IDIR) ; \
	done	
	for file in $(STRUCTURES) ; do \
	    	agda --latex  $$file --include-path=$(AGDA_STDLIB) --include-path=$(IDIR) ; \
	done	
	$(LATEX) $(MAIN).tex

quick:
	$(LATEX) $(MAIN).tex

clean:
	rm -f *.aux *.out *.log *.dvi *.ps *.pdf *~ *.bbl *.blg *.toc *.tdo *.fdb_latexmk *.fls *.ptb
	rm -f code/*.agdai
	rm -f tex/*.aux
	rm -fr latex/
