PDFLATEX = pdflatex
BIBTEX = bibtex
OTT = ott
OTT_FLAGS := -tex_wrap false -tex_show_meta true -picky_multiple_parses false
SKIM = skim_revert.sh

all: noGEN
  # This is for my private machine.  It forces my PDF reader to reload.
  # It should not run unless "skim_revert.sh" is in your PATH.
  ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/main.pdf
  endif

GEN : main.pdf

pdf-report : report.pdf

quick : fast

rquick : rfast

noGEN : main-no-gen
  # This is for my private machine.  It forces my PDF reader to reload.
  # It should not run unless "skim_revert.sh" is in your PATH.
  ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/main.pdf
  endif

main-src-output-no-gen : main-src.tex FILL.ott ref.bib
	$(OTT) $(OTT_FLAGS) -i FILL.ott -tex_name_prefix FILL \
		-tex_filter main-src.tex main-src-output.tex

main-no-gen : main.tex main-src-output-no-gen Makefile
	$(PDFLATEX) -jobname=main main.tex
	$(BIBTEX) main
	$(PDFLATEX) -jobname=main main.tex
	$(PDFLATEX) -jobname=main main.tex
	$(PDFLATEX) -jobname=main main.tex

# This preprocesses the main source file (main.tex), and
# produces a new file called main-output.tex with all of the
# Ott commands translated into LaTex.
main-src-output.tex : main-src.tex FILL.ott ref.bib
	$(OTT) $(OTT_FLAGS) -i FILL.ott -o FILL-ott.tex -tex_name_prefix FILL \
		-tex_filter main-src.tex main-src-output.tex

# Now this takes the full LaTex translation and compiles it using
# pdflatex.
main.pdf : main.tex main-src-output.tex Makefile
	$(PDFLATEX) -jobname=main main.tex
	$(BIBTEX) main
	$(PDFLATEX) -jobname=main main.tex
	$(PDFLATEX) -jobname=main main.tex
	$(PDFLATEX) -jobname=main main.tex
# This is for my private machine.  It forces my PDF reader to reload.
# It should not run unless "skim_revert.sh" is in your PATH.
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/main.pdf
endif

report.pdf : report.tex main-src-output.tex Makefile
	$(PDFLATEX) -jobname=report report.tex
	$(BIBTEX) report
	$(PDFLATEX) -jobname=report report.tex
	$(PDFLATEX) -jobname=report report.tex
	$(PDFLATEX) -jobname=report report.tex
# This is for my private machine.  It forces my PDF reader to reload.
# It should not run unless "skim_revert.sh" is in your PATH.
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/report.pdf
endif

fast : main.tex main-src-output.tex Makefile
	$(PDFLATEX) -jobname=main main.tex
# This is for my private machine.  It forces my PDF reader to reload.
# It should not run unless "skim_revert.sh" is in your PATH.
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/main.pdf
endif

rfast : report.tex main-src-output.tex Makefile
	$(PDFLATEX) -jobname=report report.tex
# This is for my private machine.  It forces my PDF reader to reload.
# It should not run unless "skim_revert.sh" is in your PATH.
ifeq ($(SKIM), skim_revert.sh)
	$(SKIM) $(CURDIR)/report.pdf
endif

clean :
	rm -f *.aux *.dvi *.ps *.log *-ott.tex *-output.tex *.bbl *.blg *.rel 
