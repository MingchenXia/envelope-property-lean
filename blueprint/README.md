# Mathematical blueprint

This directory contains a curated blueprint for the formalization of Fang–Han–Xia,
*The envelope property for unibranch projective varieties*. It gives the
mathematical statements, proofs and dependencies leading to the main envelope
theorem, the unibranch characterization, local positivity, smooth envelope
properties and the errata certificates.

The chapters under `src/` follow the conventions of
[leanblueprint](https://github.com/PatrickMassot/leanblueprint):
`\lean{…}` attaches Lean declarations to mathematical statements, `\uses{…}`
records dependencies, and `\leanok` marks proved statements. References between
chapters and bibliography citations are included in the PDF. The chapter list is
[`src/content.tex`](src/content.tex); shared notation is in `src/macros/`.

## Build the PDF

With [Tectonic](https://tectonic-typesetting.github.io/) installed:

```sh
cd blueprint/src
tectonic print.tex
```

Alternatively, use `latexmk -xelatex print.tex` with a suitable TeX installation.
The PDF is written to `blueprint/src/print.pdf`; generated TeX files are not part
of the source repository.

For an HTML version and dependency graph, install `leanblueprint` and its plasTeX
and Graphviz dependencies, then run `leanblueprint web` from the repository root.
The Lean project itself is at the repository root; the axiom audit is
`lake env lean scripts/Axioms.lean`.
