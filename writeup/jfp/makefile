SRC := tex
SCT := $(SRC)/sections
REF := round1/$(SCT)
DIFF := latexdiff --config="PICTUREENV=(?:picture|DIFnomarkup|code)[\w\d*@]*"

PDFLATEX = pdflatex -output-directory build/ -interaction=nonstopmode -file-line-error
LATEXMK  = latexmk -r $(SRC)/latexmkrc

SOURCES := $(patsubst %.lagda,%.tex,$(wildcard $(SCT)/*.lagda))

all: document.pdf 

document.pdf: build build/document.tex $(SOURCES)
	$(PDFLATEX) build/document.tex
	bibtex build/document
	$(PDFLATEX) build/document.tex
	$(PDFLATEX) build/document.tex
	cp build/document.pdf document.pdf

# Quick 'n dirty build, intended for use with watch script
quick: build build/document.tex $(SOURCES)
	$(PDFLATEX) build/document.tex
	cp build/document.pdf document.pdf

build/document.tex: tex/document.tex
	cp tex/document.tex build/document.tex

build:
	mkdir $@

diff: 

	cp $(SCT)/*.tex diff/
	cp $(REF)/*.tex diff/

	$(DIFF) diff/1-introduction-ref.tex diff/1-introduction.tex > diff/1-introduction.diff.tex
	$(DIFF) diff/2-dtc-ref.tex diff/2-dtc.tex > diff/2-dtc.diff.tex
	$(DIFF) diff/3-composable-intrinsic-ref.tex diff/3-composable-intrinsic.tex > diff/3-composable-intrinsic.diff.tex
	$(DIFF) diff/4-intrinsic-fragments-ref.tex diff/4-intrinsic-fragments.tex > diff/4-intrinsic-fragments.diff.tex
	$(DIFF) diff/5-evaluation-ref.tex diff/5-evaluation.tex > diff/5-evaluation.diff.tex
	$(DIFF) diff/6-related-ref.tex diff/6-related.tex > diff/6-related.diff.tex
	$(DIFF) diff/7-conclusion-ref.tex diff/7-conclusion.tex > diff/7-conclusion.diff.tex

	cp tex/diff.tex build/diff.tex

	$(PDFLATEX) build/diff.tex
	bibtex build/diff
	$(PDFLATEX) build/diff.tex
	$(PDFLATEX) build/diff.tex
	cp build/diff.pdf diff.pdf

%.tex: %.lagda
	agda --latex --latex-dir=. $<

clean:
	$(LATEXMK) -C .
	rm -f document.pdf
	rm -rf build
	rm -r $(SCT)/*.tex
.PHONY: all clean diff
