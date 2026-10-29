import EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomialGlobalLaurent
import EnvelopeProperty.Char0.RelativeHomogeneousSectionLiftPolynomialRename

/-! # Every original ambient projective O(e) section comes from an actual homogeneous polynomial

The original ring is an arbitrary commutative ring. The entire original section,
original coordinate-hyperplane line and original polynomial coefficient ring are
retained. All coordinate/frame/localization/representation comparisons are proved
internally; dimension zero and exponent zero are included.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
open Alterations.Geometry.ProperSteinProjectiveCech
variable {R : Type u} [CommRing R] {N : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual native original chart coefficient map is injective in the genuine Laurent algebra, with arbitrary original coefficient torsion retained. -/
theorem chartToLaurent_injective {σ : Type} (i : σ) :
    Function.Injective (chartToLaurent (R := R) i) :=
  (RelativeHomogeneousSectionLift.originalAwayToLaurent_injective (X i)
    (originalPolynomialToLaurent_X_isUnit i)).comp (chartAwayEquiv i).symm.injective

/-- EVERY original whole nonnegative O(e) section on the actual projective space over the ORIGINAL ring is the SAME native homogeneousSection of an actual degree-e original polynomial. Projective dimension zero is included. -/
theorem exists_homogeneous_polynomial (j : Fin (N + 1)) (e : ℕ)
    (s : Γ(coordinateHyperplaneTwist (R := R) j (e : ℤ), ⊤)) :
    ∃ F : MvPolynomial (Fin (N + 1)) R, ∃ hF : F.IsHomogeneous e,
      ProjectiveHomogeneousSections.homogeneousSection j e F hF = s := by
  let l : subsetHomogeneousLaurentModule (K := R) (I := ULift.{u} (Fin (N + 1))) (e : ℤ) ∅ :=
    ⟨sectionLaurent j j e s, sectionLaurent_mem_empty j e s⟩
  obtain ⟨F, hF, hFl⟩ := RelativeHomogeneousSectionLift.exists_original_polynomial_of_empty_laurent e l
  refine ⟨F, hF, ?_⟩
  apply nativeCoefficient_ext j e
  intro i
  apply chartToLaurent_injective i
  apply ((originalPolynomialToLaurent_X_isUnit (R := R) i).pow e).mul_right_cancel
  rw [nativeCoefficient_homogeneousSection, chartToLaurent_coefficient_clear]
  change originalPolynomialToLaurent F = sectionLaurent i j e s
  exact hFl.trans (sectionLaurent_eq j i j e s)

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
