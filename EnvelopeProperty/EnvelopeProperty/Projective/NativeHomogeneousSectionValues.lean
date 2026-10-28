import EnvelopeProperty.AlgGeom.ProjectiveHomogeneousSections
import EnvelopeProperty.Projective.NativeModelIdeals

/-! # Original whole homogeneous-section coefficients have their original analytic values -/
open scoped Classical NNReal Topology
open MvPolynomial AlgebraicGeometry CategoryTheory
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}
private local instance nativeSectionChartAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- The genuine whole O(d) coefficient is the SAME original affine polynomial section. -/
theorem homogeneousSection_coefficient_eq_coordinate (j : Fin (n + 1)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d) :
    ProjectiveHomogeneousSections.coefficient j d F hF =
      (nativeCoordinateSectionsIso j).hom (coordinateDehom j F) := by
  have he := (homogeneousChartEquiv (R := R) j).symm_apply_apply
    (ProjectiveHomogeneousSections.fraction j d F hF)
  have hv : homogeneousChartEquiv (R := R) j
      (ProjectiveHomogeneousSections.fraction j d F hF) = coordinateDehom j F :=
    homogeneousChartDehom_mk j d F (by simpa using hF)
  rw [hv] at he
  rw [nativeCoordinateSectionsIso, Iso.trans_hom, nativeHomogeneousChartSectionsIso_hom]
  exact (congrArg (fun a => (ProjectiveSpectrum.Proj.awayToSection
    (ProjectiveGrading R n) (X j)).hom a) he).symm
end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] (v : Valuation R ℝ≥0) {n : ℕ}

/-- At every value-one chart the actual original homogeneous-section coefficient
has EXACTLY the original full homogeneous seminorm value. -/
theorem nativeHomeomorph_eval_homogeneousSection_coefficient
    (x : RelativeNormalizedProjectiveSpectrum v n) (j : Fin (n + 1))
    (hj : x.1.1.val (X j) = 1) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R)
    (hF : F.IsHomogeneous d) :
    SchemeValuedPoint.eval (nativeHomeomorph v x).1 (ProjBerk.nativeCoordinateOpen j)
      (by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero)
      (ProjectiveHomogeneousSections.coefficient j d F hF) = x.1.1.val F := by
  rw [ProjBerk.homogeneousSection_coefficient_eq_coordinate]
  exact (nativeHomeomorph_val_apply v j
    ⟨x, by change x.1.1.val (X j) ≠ 0; rw [hj]; exact one_ne_zero⟩
    (ProjBerk.coordinateDehom j F)).trans
      (coordinateChart_val_dehom_of_isHomogeneous v x j hj d F hF)
end EnvelopeProperty.Berkovich.RelativeNormalizedProjectiveSpectrum
