PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false
SKIM = skim_revert.sh

all: pdf

pdf : note.pdf

# This preprocesses the main source file (note.tex), and
# produces a new file called note-output.tex with all of the
# Ott commands translated into LaTex.
note-output.tex : note.tex FILL.ott
	$(OTT) $(OTT_FLAGS) -i FILL.ott -o FILL-ott.tex -tex_name_prefix FILL \
		-tex_filter note.tex note-output.tex

# Now this takes the full LaTex translation and compiles it using
# pdflatex.
note.pdf : note-output.tex Makefile
	$(PDFLATEX) -jobname=note note-output.tex
	$(BIBTEX) note
	$(PDFLATEX) -jobname=note note-output.tex
	$(PDFLATEX) -jobname=note note-output.tex
	$(PDFLATEX) -jobname=note note-output.tex
# This is for my private machine.  It forces my PDF reader to reload.
# It should not run unless "skim_revert.sh" is in your PATH.
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/note.pdf
endif

clean :
	rm -f *.aux *.dvi *.ps *.pdf *.log *-ott.tex *-output.tex
