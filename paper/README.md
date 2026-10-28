# The paper

Fang–Han–Xia, *The envelope property for unibranch projective varieties, with an appendix on the
singular Yau–Tian–Donaldson conjecture*: the authors' source as supplied on 2026-10-28
(`main.tex`, `ComplexGeometry.bib`, `cgeometry.sty`; sha256 of their concatenation
`915ccc74a2b95ac6…`).

`main.pdf` (42 pages) was compiled on 2026-10-28 with tectonic 0.15.0 and biber 2.17. biber was
run with `--output-safechars`: XeTeX's Latin Modern font (`ec-lmr10`) has no ţ and ă (in
"Mustaţă"), and safe characters make biber write them as LaTeX accent commands.

To compile it yourself: `latexmk -pdf main.tex` (pdfLaTeX + biber), or `tectonic main.tex` with
biber on the `PATH` (with XeTeX use biber's `--output-safechars`). The bibliography uses
biblatex with the biber backend.
