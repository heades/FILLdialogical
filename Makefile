PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false
SKIM = skim_revert.sh

all: pdf

pdf : FILLDialogical.pdf

# This preprocesses the main source file (FILLDialogical.tex), and
# produces a new file called FILLDialogical-output.tex with all of the
# Ott commands translated into LaTex.
FILLDialogical-output.tex : FILLDialogical.tex FILL.ott
	$(OTT) $(OTT_FLAGS) -i FILL.ott -o FILL-ott.tex -tex_name_prefix FILL \
		-tex_filter FILLDialogical.tex FILLDialogical-output.tex

# Now this takes the full LaTex translation and compiles it using
# pdflatex.
FILLDialogical.pdf : FILLDialogical-output.tex Makefile
	$(PDFLATEX) -jobname=FILLDialogical FILLDialogical-output.tex
	$(BIBTEX) FILLDialogical
	$(PDFLATEX) -jobname=FILLDialogical FILLDialogical-output.tex
	$(PDFLATEX) -jobname=FILLDialogical FILLDialogical-output.tex

# This is for my private machine.  It forces my PDF reader to reload.
# It should not run unless "skim_revert.sh" is in your PATH.
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/FILLDialogical.pdf
endif

clean :
	rm -f *.aux *.dvi *.ps *.pdf *.log *-ott.tex *-output.tex
