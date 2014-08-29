#!/bin/bash
pdflatex Probability_theory.tex && rm -rf *.dvi *.log *.tex.aux *.aux && open Probability_theory.pdf
