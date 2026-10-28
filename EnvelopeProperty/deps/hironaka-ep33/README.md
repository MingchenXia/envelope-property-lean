# Hironaka algebraic principalization for EnvelopeProperty

Frozen minimal algebraic import cone from https://github.com/resolutionorg/hironaka at
`a0d237580a68818b5142b6d404a2670b3fcee697`, backported to Lean/Mathlib v4.33.1.
Copyright (c) 2026 Resolution; Apache-2.0. Original source headers and LICENSE are retained.

Import the concrete modules under
`Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.{Monomial,Centers,IsoLocus}`,
or the small convenience root `Hironaka`. The latter imports only those three roots.
No analytic, example, Challenge, or full-upstream umbrella module is vendored.

The 522-module producer cone passed a direct Lean kernel build and transitive axiom audit.
See VALIDATION.md, audit/principalization-axioms.log, UPSTREAM-CONE.json, and PORT-HASHES.json.
The full source compatibility diff is compatibility.patch, explained in PORTING.md.
No vendored definition/theorem interface was weakened and no hypothesis class was introduced.

The package is named `hironakaEp33`, with Lean library prefix `Hironaka`. Parent integration uses
an ordinary local path dependency `deps/hironaka-ep33`; the parent keeps its existing pinned
Mathlib/TN dependencies. The parent Lake manifest must add this path package explicitly, following
its existing pinned-dependency convention; do not run an unconstrained `lake update`.
After registration, `lake build Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial`
checks the principalization producer under the parent toolchain. From the parent project,
`lake env lean deps/hironaka-ep33/audit/Principalization.lean` runs the actual-import audit;
from this package directory use `lake env lean audit/Principalization.lean`. The same target can be built
independently in this package using the included Mathlib v4.33.1 manifest.

Versioned source contains no .lake directory, binaries, private clone metadata, or network helper.
For this working session only, checked producer oleans were copied (not symlinked) from the isolated
validation workspace to the ignored local `.lake/build/lib/lean` directory. They are not source
artifacts and must not be committed.
The original isolated build remains an external validation artifact; only source, license,
provenance, configuration, and audit evidence are vendored here.

The EP finite chart-tree/etale Jacobian adapter remains separate work; principalization alone is
not a proof of SmoothEnvelopeCharZero or completion of the whole paper.

## Strong resolution extension

The additional 105 modules in `strong-resolution-extension/ADDITIONAL-UPSTREAM.json` extend the same exact upstream commit to the genuine `exists_strong_resolution` theorem for integral algebraic schemes in characteristic zero. The union now contains 626 upstream modules and one proved compatibility helper. Historical principalization hashes/evidence remain unchanged; the extension records its own source hashes, API patch and isolated kernel checks. Its actual parent-project build and audit are recorded by the consuming EP checkpoint. The extension also supplies the actual projectivity theorem for blowups and finite blowup sequences.
