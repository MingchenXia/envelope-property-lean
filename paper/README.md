# The paper

Yanbo Fang, Jiyuan Han and Mingchen Xia, *The envelope property for unibranch projective varieties,
with an appendix on the singular Yau–Tian–Donaldson conjecture*: LaTeX source (`main.tex`,
`ComplexGeometry.bib`, `cgeometry.sty`) and the compiled `main.pdf`.

To compile: `latexmk -pdf main.tex` (pdfLaTeX + biber), or `tectonic main.tex` with biber on the
`PATH`. The bibliography uses biblatex with the biber backend. With XeTeX (tectonic), run biber with
`--output-safechars`: XeTeX's Latin Modern font has no ţ and ă, which biber then writes as accent
commands.
