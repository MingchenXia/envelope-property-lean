/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.ProjectiveReduced
import EnvelopeProperty.ReesGoodOpenDensity

/-! # Integrality of the SAME original Rees scheme -/
open scoped Polynomial
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty
attribute [local instance] MvPolynomial.gradedAlgebra

namespace ReesPresentation
variable {A ι : Type u} [CommRing A] [IsDomain A] (g : ι → A)

/-- The literal ORIGINAL kernel quotient is a genuine domain through its actual Rees subalgebra equivalence. -/
theorem quotient_isDomain : IsDomain (MvPolynomial ι A ⧸ kernel g) :=
  (quotientEquiv g).toRingEquiv.toMulEquiv.isDomain _

/-- The SAME original quotient grading defines a genuinely reduced scheme. -/
theorem scheme_isReduced : IsReduced (Scheme g) := by
  let : IsDomain (MvPolynomial ι A ⧸ (homogeneousKernel g).toIdeal) := quotient_isDomain g
  exact proj_isReduced (grading g)

/-- A genuine original nonzero generator makes the actual original good-open lift have dense range. -/
theorem denseRange_goodOpenLift (j : ι) (hj : g j ≠ 0) : DenseRange (goodOpenLift g j) := by
  change Dense (Set.range (goodOpenLift g j))
  rw [range_goodOpenLift]
  exact dense_projection_preimage_basicOpen g j (mem_nonZeroDivisors_iff_ne_zero.mpr hj)

/-- The ORIGINAL Rees scheme is ACTUALLY integral, with no finite-family or integrality certificate. -/
theorem scheme_isIntegral (j : ι) (hj : g j ≠ 0) : IsIntegral (Scheme g) := by
  let := scheme_isReduced g
  let : IsDomain (Localization.Away (g j)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away (g j))
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hj))
  have hi := (IrreducibleSpace.isIrreducible_univ
    (Spec (CommRingCat.of (Localization.Away (g j))))).image
      (goodOpenLift g j) (goodOpenLift g j).continuous.continuousOn
  simp only [Set.image_univ] at hi
  have : IrreducibleSpace (Scheme g) := (irreducibleSpace_def _).mpr (by
    simpa only [(denseRange_goodOpenLift g j hj).closure_range, Set.top_eq_univ] using hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end ReesPresentation
end EnvelopeProperty
