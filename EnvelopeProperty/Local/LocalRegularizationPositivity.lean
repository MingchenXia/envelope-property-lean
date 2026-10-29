/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.LocalRegularizationFinal
import EnvelopeProperty.Local.PositivityReduction

/-!
# Theorem 5.25 from FHX Lemma 5.5

`LocalPositivity k` (Local/PositivityImport.lean) is FHX Lemma 5.5 (`lem:local-PL-positivity`) stated
verbatim in the graded model: on a projectively normal `V(I) ⊆ ℙᴹ`, every locally `O(a)`-convex
function (FHX Definition 5.3) is `a`-psh. The instance `LocalPositivity.toConvexPLApproximation`
(Local/PositivityReduction.lean, of the Wu discharge) and
`ConvexPLApproximation.toWuRegularization` (Local/WuReduction.lean) derive FHX
Lemma 5.11(5),(6) from it. Theorem 5.25 is therefore conditional only on FHX Lemma 5.5 and
`NonflatNorms` (FHX Proposition 5.22).
-/

namespace EnvelopeProperty

open Berk

universe u v

/-- **FHX Theorem 5.25** (local regularization), conditional only on FHX Lemma 5.5
(`LocalPositivity`) and FHX Proposition 5.22 (`NonflatNorms`). -/
theorem IsRegularizable.of_isWeaklyPSHOn_of_localPositivity {k : Type u} [Field k] [IsAlgClosed k]
    [Countable k] [LocalPositivity.{u} k] [NonflatNorms.{u, v, u} k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [IsIntegrallyClosed A] (S : Finset A)
    (hS : ∃ f ∈ S, f ≠ 0) {u : Berk k A → EReal} (hu : IsWeaklyPSHOn Set.univ u)
    (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, (∃ f ∈ S, x.val f ≠ 0) →
      ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧ IsRegularizable fun y => u (awayComap g y)) :
    IsRegularizable u :=
  IsRegularizable.of_isWeaklyPSHOn_of_convexPLApproximation S hS hu hlog hcover

end EnvelopeProperty
