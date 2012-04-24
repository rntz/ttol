.PHONY: all watch clean

SOURCES=$(wildcard *.tex)
BASES=$(basename $(SOURCES))
PSS=$(addsuffix .ps,$(BASES))
PDFS=$(addsuffix .pdf,$(BASES))
DVIS=$(addsuffix .dvi,$(BASES))

RESULTS=$(PSS) $(PDFS) $(DVIS)
JUNK=$(RESULTS) *.log *.aux *.out
AUXIL=$(wildcard *.sty) $(wildcard *.cls)

all: $(SOURCES)
	rubber --pdf $^

watch: all
	@while inotifywait -e modify *.tex *.sty; do make all; done

%.dvi: %.tex $(AUXIL)
	rubber --dvi $<

%.ps: %.tex $(AUXIL)
	rubber --ps $<

%.pdf: %.tex $(AUXIL)
	rubber --pdf $<

clean:
	rm -f $(JUNK)

notes.tgz: notes.pdf notes.tex hot.sty
	tar czf $@ $^
