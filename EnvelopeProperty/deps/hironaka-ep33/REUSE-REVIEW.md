# Scoped reuse review: algebraic principalization

Reviewed upstream https://github.com/resolutionorg/hironaka at
`a0d237580a68818b5142b6d404a2670b3fcee697`. This is source inspection, not yet a successful
compatibility build or kernel axiom audit.

## Concrete producer

Use `Hironaka.Sequence.BP T` from
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization.lean` with:

- `BP_isIdealOfSncDivisor T` in `Principalization/Monomial.lean`;
- `BP_center_smooth_hasSncWith T` (and stronger `BP_isOrderGeSeq_zero T`) in
  `Principalization/Centers.lean`;
- `BP_isIso_restrict T` in `Principalization/IsoLocus.lean`.

These provide the non-functorial geometric input needed for an adapter to EP's finite Rees chart
trees. There is no need to import the larger terminal functoriality theorem, and certainly no
need to import the complete Hironaka umbrella, the analytic library, examples, or Challenge.

For a smooth finite-type domain B over a characteristic-zero field k, construct the triple with
X = Spec B, the ideal sheaf associated to the product of the finitely many nonzero input ideals,
and the empty boundary. Equidimensionality follows from the domain/smooth hypotheses; stalkwise
nonvanishing follows by injectivity of localizations. Separation and finite type are intrinsic
properties of Spec B. The unit ideal is allowed and gives an empty divisor; the zero ideal is
correctly excluded. The extra ordering on the boundary has no consequence for an empty boundary.
For this input, the corrected isomorphism locus is precisely the complement of the ideal's
cosupport, since the boundary singular locus is empty.

## Why this is a genuine producer

`Triple` bundles actual Mathlib schemes, finite-type separated structure morphisms, actual ideal
sheaf data, smoothness of a single relative dimension, stalkwise nonzero ideals, and an SNC
boundary. No resolution-existence premise occurs in it. `BlowUpSequence` is an inductive finite
sequence of the actual blowups of the previous stages. `IdealSheafData.blowUp` is glued from the
Proj of the Rees algebra, and the affine chart algebra is the localization subalgebra R[I/a].
The final `IsIdealOfSncDivisor` predicate is a finite product of actual boundary ideal sheaves,
whose SNC condition states generation by distinct members of an actual regular system of
parameters at every stalk. It does not simply restate existence of a desired model.

The order-reduction package is not left assumed: `BP` invokes `BMO_m 1 k`; that is instantiated at
`stage0`, with a `Nat.rec` tower of successor proofs and an explicit dimension-zero base. The
three root producers have only `[Field k] [CharZero k]` plus a triple as inputs.
A comment-stripped scan of the complete selected local cone found no
sorry/admit/sorryAx/axiom/unsafe/implemented_by/extern token. This is weaker evidence than the
required eventual transitive `#print axioms` audit, and no whole-library semantic audit is claimed.

## Dependency cone and portability

The recursively traversed local import union, including `public import` and private imports, is
**521 Hironaka modules, 118,970 source lines**. Exact module names and upstream source hashes are
in `UPSTREAM-CONE.json`. All local imports exist. The cone is algebraic/scheme-only and has no
analytic or TN dependency. Its only direct Mathlib source path absent from the existing v4.33.1
checkout is `Mathlib.Basic.NNReal.Defs`, imported by
`Hironaka/Scheme/IdealSheaf/Order/Smooth.lean:15`; the corresponding existing v4.33.1 module is
`Mathlib.Data.NNReal.Defs`. The isolated port makes that one import replacement. Existence of the
other import paths does not establish API compatibility. Upstream uses Lean/Mathlib v4.34.0,
so its oleans cannot be imported into v4.33.1; the selected cone must be recompiled and audited.
The original upstream clone remains pristine. No current project toolchain or TN pin is changed.

## Adapter obligations still open

1. Identify the actual scheme affine blowup chart `affineBlowUpAlgebra I a` with EP's subalgebra
   C[g_j/g_i] inside its fixed fraction field, compatibly with the structure maps and ideal maps.
   The upstream `reesAlgebra.chartRingEquiv` supplies the Rees degree-zero chart comparison, and
   the global chart coverage lemmas supply coverage from chosen finite ideal generators.
2. Recursively refine the finite scheme blowup sequence into EP's tree, then use principal-open
   nodes for finitely many affine coordinate refinements. Finiteness and the tree witness are
   essential; a bare existence of a covering set is insufficient for the reduction-mod-p route.
3. Obtain actual affine etale coordinates adapted to the SNC divisor and monomialize each input
   ideal factor. The upstream SNC/EtaleCoordinates machinery is relevant but not already in EP's
   exact finite-global-chart format.
4. Prove the relative Jacobian ideal is a coordinate monomial on those leaves. The principalized
   product and isomorphism off its cosupport imply the relative Jacobian divisor is supported on
   the SNC divisor; the required determinant/coordinate and finite-shrinking argument is still a
   real proof obligation. No algebraic relative-Jacobian producer was located in this inspection.
5. Prove the downstream multiplier-ideal/subadditivity/uniform-generation arguments; resolution
   alone does not prove SmoothEnvelopeCharZero or the paper's whole main theorem.

## Integration recommendation

First validate this isolated source port against the current Mathlib without touching shared
source. If it passes and the adapter is viable, vendor this exact frozen cone as a separate
local Lake package under a project dependency directory, retaining the Hironaka namespace,
upstream Apache-2.0 LICENSE, all copyright headers, commit provenance, source hashes, and an
explicit compatibility patch. Do not upgrade EP or TN merely to consume v4.34 artifacts.
An independently pinned backport repository could replace the vendored package later; depending
on upstream v4.34 directly is not currently compatible. Recompile all selected modules under
v4.33.1 and print transitive axioms of each producer and the adapter before acceptance.
