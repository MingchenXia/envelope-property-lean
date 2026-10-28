# Isolated Hironaka compatibility port for EnvelopeProperty

Upstream: https://github.com/resolutionorg/hironaka at a0d237580a68818b5142b6d404a2670b3fcee697.
Copyright (c) 2026 Resolution; Apache-2.0. Original headers and LICENSE retained.
The original validation workspace is `/workspace/hironaka-ep33`, outside the EnvelopeProperty
repository. This copy is the vendored local package at `EnvelopeProperty/deps/hironaka-ep33`.
Both contain the same validated Lean sources and import no Challenge files.
Vendoring does not modify the original clone, project toolchain, TN pin, or shared Mathlib sources.

Configuration: Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 (v4.33.1).
The local package manifest mirrors the existing EP Mathlib dependency closure. The original
validation workspace used a .lake/packages symlink to read existing dependency artifacts. That
symlink is not part of the vendored source package. Ordinary parent builds follow the parent's
shared resource discipline; no cache downloads were used.
The library options match upstream, except warningAsError is omitted during compatibility diagnosis.
The root Hironaka.lean is a new three-import aggregator, not upstream's complete umbrella.
In the vendored package the audit source is `audit/Principalization.lean` and its output is
`audit/principalization-axioms.log`; original validation used `AuditPrincipalization.lean` and
`principalization-axioms.log` in the isolated workspace root.

UPSTREAM-CONE.json lists exact roots, all transitive local imports including public imports,
upstream SHA-256 hashes, line counts, and direct Mathlib import paths. Initial source scan after
removing comments found no sorry/admit/sorryAx/axiom/unsafe/implemented_by/extern token in this cone.
This scan is not a kernel axiom audit or a semantic completeness claim.

## Compatibility changes

1. `Hironaka/Scheme/IdealSheaf/Order/Smooth.lean:15`: replace the unavailable
   `Mathlib.Basic.NNReal.Defs` import by the existing v4.33.1 module
   `Mathlib.Data.NNReal.Defs`. No definition, statement, or proof changed.
   Exact source diff is in `compatibility.patch`.

Lean LSP tools are not available in the active tool catalog. The initial narrow fallback
`lake env lean Hironaka/Scheme/IdealSheaf/Order/Smooth.lean` exits with missing local
Hironaka artifacts, as expected before the first dependency build; this does not check its body.
Root subsequently authorized an isolated direct Lean build after the Mathlib umbrella completed,
using only existing shared oleans as read-only inputs and at most two compiler workers. The driver
The original workspace's `build_cone.py` wrote only its own `.lake/build` and log/status files. It invokes no Lake
build and downloads no cache. The exact commands are recorded per module in the original workspace's port-build-status.json.

## Validation

Completed: the isolated direct build accepted all 522 selected modules, and the actual-import
boundary audit passed with only the standard three axioms for BP and all three clauses.
See VALIDATION.md and principalization-axioms.log. The EP log-chart adapter is still open.

2. `Hironaka/Algebra/Local/ChartSubst.lean:156,158,170`: use v4.33.1 core names
   `if_pos` / `if_neg` in place of v4.34 `ite_eq_left` / `ite_eq_right`. First direct build reported
   exactly three unknown-identifier diagnostics there. Statements and proof arguments are unchanged;
   only the theorem names differ. The next direct dependency build rechecks the edited module.

3. Apply the same checked core-lemma renaming to the remaining 146 occurrences in 36 files
   (`core-lemma-renames.json` lists them). The second build accepted ChartSubst with these aliases,
   then stopped at identical missing-name diagnostics in PowerSeries and Derivative. This is a
   mechanical API name correction throughout the selected cone; proof terms, arguments, definitions,
   and theorem statements are otherwise unchanged.

The direct compiler's exact proof-relevant command options are
`-DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true`.
Lake-only weak lint options are not forwarded by this direct compiler driver; full package lint
validation is separate. `AuditPrincipalization.lean` is prepared for a final actual-import type
and transitive-axiom check once all three producer modules have been built.

4. v4.33.1 has `TensorProduct.induction_on` with a zero case; v4.34's two-case
   `TensorProduct.inductionOn` is unavailable. Rather than changing the four upstream induction
   proofs, add `Hironaka.Compat.TensorProductInduction`: a proved two-case eliminator whose zero
   case follows from the pure tensor `0 ⊗ 0`. This helper passed a direct actual-import kernel
   check with the same proof-relevant options. The three using upstream files now import it;
   their existing proofs and statements are unchanged. `PORT-EXTRA.json` distinguishes this new
   local compatibility file from the 521 upstream files. The original diagnostic was
   CompletionCoords.lean:177:22, unknown `TensorProduct.inductionOn`.

5. v4.33.1's `List.TFAE.out` is zero-indexed; upstream uses the newer one-indexed API.
   Adjust all three concrete uses: CompletionMap `.out 1 3` becomes `.out 0 2`, and
   Algebra/Derivative/Extension plus BlowUpSequence/SmoothParameters `.out 1 2` becomes
   `.out 0 1`. The first diagnostic, CompletionMap.lean:148–149, exhibited the wrong list
   propositions explicitly. The selected equivalences are unchanged.

6. `Algebra/Local/OrderSmooth.lean:57,66`: use the existing v4.33.1 theorem
   `Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq` instead of the unavailable shorter
   `Localization.AtPrime.algebraMap_eq`. The localized algebra instance already supplies the
   needed `IsLiesOverAlgebra` witness. No theorem statement or proof argument changed.

OrderSmooth passed its direct actual-import kernel check after compatibility change 6.

7. `Scheme/BlowUp/LinearType.lean:153–154`: use the actual v4.33.1
   `MvPolynomial.coeff m` linear map directly in the coefficientwise congruence, with its
   `MvPolynomial.coeff_zero` rewrite. Upstream's unbundled `AddMonoidAlgebra.coeff` application
   did not match `MvPolynomial.coeff_C_mul` in this Mathlib version. The coefficientwise argument,
   hypotheses, definitions, and theorem statement are unchanged.

   LinearType passed after change 7. Apply that identical coefficient-map correction to the
   three remaining uses in ChartGenericFibre, ChartFibre, and MaximalContact/Transform; these
   are also congruences on an MvPolynomial equality. Their dependency builds check the bodies.

8. The dependent-if counterparts have the same core API rename: `dite_eq_left/right` become
   `dif_pos/neg`. Apply 115 mechanical token replacements across
   32 files, listed in `dependent-if-renames.json`. The first diagnostic was
   Algebra/Local/Chart.lean:787. No proof arguments, definitions, or theorem statements changed.

9. `Scheme/Modules/Sections.lean:293–294`: v4.33.1's `IsBaseChange.inductionOn` requires
   an explicit motive and zero case. Supply the existing span-membership motive and
   `Submodule.zero_mem _` before the unchanged generating/smul/add cases. No definitions or
   theorem statements changed. The first error was an argument-order/type mismatch at these lines.

10. v4.33.1 calls the coproduct composition lemma `Sigma.ι_desc` (and its reassociated
    form `Sigma.ι_desc_assoc`), whereas upstream uses `Sigma.ι_comp_desc`. Apply this exact
    name change at 20 uses across 7 files. First diagnostic:
    Scheme/Smooth/EtaleCover.lean:50. Proof arguments and statements are unchanged.

11. `Resolution/Algebraic/Tuning/Transform.lean:214`: the nonnegative-product comparison
    lemma is named `Finset.prod_le_prod` in v4.33.1, rather than upstream's `prod_le_prod₀`.
    Exact existing proof arguments are retained.
