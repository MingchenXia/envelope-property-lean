/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.LocalRegularization
import EnvelopeProperty.Local.ProjectionPackageProof
import EnvelopeProperty.Local.ProjectionExistenceProof
import EnvelopeProperty.Local.WuReduction

/-!
# Theorem 5.25 with Lemma 5.23 discharged

FHX Theorem 5.25 (`thm:normal-local-regularization`): on a normal affine variety over a countable
algebraically closed field, a weakly psh function of logarithmic growth that is regularizable on
principal opens covering `Y \ Z` (`Z = V(S) ⊊ Y`) is regularizable.

`IsRegularizable.of_isWeaklyPSHOn` (Local/LocalRegularization.lean) assumes the class
`ProjectionPackage`; it follows from FHX Lemma 5.23 (`ProjectionExistence`,
`ProjectionExistence.toProjectionPackage`), which is proved for every algebraically closed field
(`projectionExistence_of_isAlgClosed`). The statement below therefore assumes only the two remaining
explicit hypotheses: `WuRegularization` (FHX Lemma 5.11(5),(6)) and `NonflatNorms` (FHX
Proposition 5.22).

`WuRegularization` follows from the single approximation statement `ConvexPLApproximation`
(`ConvexPLApproximation.toWuRegularization`, Local/WuReduction.lean), and conversely
(`ConvexPLApproximation.of_wuRegularization`); `IsRegularizable.of_isWeaklyPSHOn_of_convexPLApproximation`
states Theorem 5.25 with that hypothesis.
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk

universe u v

/-- **FHX Theorem 5.25** (local regularization), conditional only on `WuRegularization` and
`NonflatNorms`. -/
theorem IsRegularizable.of_isWeaklyPSHOn_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [WuRegularization.{u, v} k] [NonflatNorms.{u, v, u} k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [IsIntegrallyClosed A] (S : Finset A)
    (hS : ∃ f ∈ S, f ≠ 0) {u : Berk k A → EReal} (hu : IsWeaklyPSHOn Set.univ u)
    (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u :=
  IsRegularizable.of_isWeaklyPSHOn S hS hu hlog hcover

/-- **FHX Theorem 5.25**, conditional only on `ConvexPLApproximation` (approximation of convex PL
functions standard at infinity, `thm:wu-pl-approx`) and `NonflatNorms`. -/
theorem IsRegularizable.of_isWeaklyPSHOn_of_convexPLApproximation {k : Type u} [Field k]
    [IsAlgClosed k] [Countable k] [ConvexPLApproximation.{u, v} k] [NonflatNorms.{u, v, u} k]
    {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [IsIntegrallyClosed A] (S : Finset A) (hS : ∃ f ∈ S, f ≠ 0) {u : Berk k A → EReal}
    (hu : IsWeaklyPSHOn Set.univ u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u :=
  IsRegularizable.of_isWeaklyPSHOn_of_isAlgClosed S hS hu hlog hcover

end EnvelopeProperty
