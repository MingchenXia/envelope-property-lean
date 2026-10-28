# Blueprint (curated subset)

This directory holds a **curated subset** of the blueprint of the Lean formalization: the informal,
node-by-node account of the mathematics, in the LaTeX conventions of
[leanblueprint](https://github.com/PatrickMassot/leanblueprint) (`\lean{…}`, `\uses{…}`,
`\leanok`). It follows Fang–Han–Xia's paper (`../paper/`) and the literature it cites.

## What is included

The development blueprint has 3241 chapters with 9617 statements.
This subset has the **1286 chapters (4617 statements)** obtained as follows:

1. the nodes attached to the theorems of the release roots (the headline theorems
   `thm:fu-*`, `cor:fu-*`, `thm:var-main`, `cor:var-characterization`, the global theorems
   `thm:gl-*`, the `LocalPositivity` and `SmoothEnvelopeCharZero` instances, and the errata
   certificates `prop:nn-bj-lemma46-false`, `prop:r73-p1-example`, `thm:hm-psh2-hom-majorant`):
   53 nodes;
2. everything they use (`\uses` of statements and proofs): 2873 nodes;
3. the chapters containing these nodes, closed again under the `\uses` and `\ref`/`\cref` of
   every node in an included chapter.

The chapters are unchanged except that comment lines are removed, references to working files of
the development workspace (paths, plans, decisions, internal process notes) are rewritten or
removed, and a few math-mode slips that stopped LaTeX are fixed.
`src/content.tex`, `src/print.tex`, `src/web.tex`, `src/macros/` and `src/plastex.cfg` are
generated.

The `\lean{…}` attachments name the Lean declarations of the formalization: 12449 of the 13180 names occur in the Lean sources of this repository; the others are declarations of the development workspace in modules outside the import closure of the release roots.

## Checks

* Every `\uses`, `\ref`/`\cref` and `\cite` inside the subset resolves to a node, a label or a bibliography entry of the subset (checked by the release tooling).
* The replay of `horizon graph sync`'s blueprint checks on the subset (4617 statements) reports no dangling `\uses`, no unlabeled statements and no label or proof-association problems, and no warning that the full development blueprint does not report as well.
* `print.tex` compiles (tectonic 0.15.0, 1355 pages) without errors and without undefined references or citations.

## Building

* PDF: `cd src && tectonic print.tex` (the check above), or `latexmk -xelatex print.tex`.
* With leanblueprint (`pip install leanblueprint`, which needs plasTeX and Graphviz), from the
  repository root: `leanblueprint pdf` and `leanblueprint web` (the web version and its dependency
  graph are written to `blueprint/web/`). The web build was not tested by the release tooling, and
  `leanblueprint checkdecls` is not set up (the Lean project is in `EnvelopeProperty/`; the
  declarations are checked by `scripts/Axioms.lean` instead).
