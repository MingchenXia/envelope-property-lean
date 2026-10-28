# Validated algebraic principalization backport

Claim class: **proved external producer, not yet an EP log-chart adapter**.

Selected upstream cone: resolutionorg/hironaka
`a0d237580a68818b5142b6d404a2670b3fcee697`, 521 algebraic/scheme modules and 118,970 source lines.
Port: the same source interfaces, API compatibility patch, and one proved tensor-induction helper.
All **522/522** selected modules compiled successfully under Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` (v4.33.1), using two compiler workers and existing
shared package oleans only as read-only inputs. No Mathlib cache downloads, shared source edits,
project toolchain change, TN pin change, Challenge import, or extra hypothesis class was used.
The final direct build exited 0. Resolved compatibility diagnostics and all adaptations are listed
in PORTING.md; the exact upstream diff is compatibility.patch.

Proof-relevant compiler options:
`-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true`.
Each direct compiler command had the form
`lean OPTIONS -o LOCAL_BUILD/MODULE.olean -i LOCAL_BUILD/MODULE.ilean SOURCE.lean`.
Full environment paths and compiler revision are recorded in audit/BUILD-CONFIG.json.
This direct build does not claim a Lake trace-cache or weak-linter validation.

Actual-import boundary audit command, also exit 0:
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 audit/Principalization.lean`.
The exported `BP` definition and all three principalization clauses each print only
`[propext, Classical.choice, Quot.sound]`. The complete printed types and axiom output are in
`audit/principalization-axioms.log`; their only type-level inputs are a characteristic-zero field
and the natural geometric Triple data.

UPSTREAM-CONE.json records the exact original import cone, including public imports, and original
source hashes. PORT-HASHES.json records the validated ported-source and corresponding olean SHA-256
for every module; PORT-EXTRA.json identifies the one new proved compatibility helper. The original
upstream checkout was checked pristine after compilation. Preserved upstream source headers and
LICENSE identify Copyright (c) 2026 Resolution, Apache-2.0.

The root Hironaka.lean is a new three-import convenience aggregator. It introduces no declaration;
its imports are precisely the three selected producer roots. The producer proof cone has 522
modules; building this convenience aggregator adds one trivial import-only module.

## Relevance and remaining frontier

Consumer: EP finite Rees chart trees / log charts on Spec of a smooth finite-type domain.
The accepted external producer supplies an actual finite sequence of actual Rees-Proj blowups,
SNC monomialization of the total transformed ideal, smooth SNC centres, and the isomorphism locus.
The EP adapter must still identify affine charts inside its fixed fraction field, construct the
finite tree with finite principal-open refinements, produce adapted affine etale coordinates,
monomialize each input factor, and prove the coordinate-relative Jacobian monomial clause.
Multiplier-ideal subadditivity/uniform generation and SmoothEnvelopeCharZero remain downstream.
