(TeX-add-style-hook
 "report"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "biblatex"
    "amsmath"
    "tikz"
    "pgfplots"
    "forest"
    "braket")
   (LaTeX-add-bibliographies
    "Horner's Rule.bib"))
 :latex)

