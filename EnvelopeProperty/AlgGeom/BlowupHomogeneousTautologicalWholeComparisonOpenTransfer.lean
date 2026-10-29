import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalOpenNaturality

/-! # Open pullback of the same original homogeneous-form lift

The comparison and its section identity are constructed here on abstract schemes.
Actual blowup callers supply only the already proved composite section basis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

/-- The same original homogeneous-form lift remains a basis under open
pullback whenever its actual composite lift is a basis. The comparison is the
canonical one inside original-form naturality, with no matching input. -/
theorem liftedFormSection_isIso_pullback_of_composite
    {R : Type u} [hR : CommRing R] {n : ℕ} {X Z W : Scheme.{u}}
    (μ : Z ⟶ X) (c : W ⟶ Z) [hcOpen : IsOpenImmersion c]
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (hc : IsIso (liftedFormSection (R := R) (n := n) (X := X) (Z := W)
      (c ≫ μ) j J d F hF hFJ)) :
    IsIso (SchemeLineSectionEvaluation.pullbackSectionHom c
      (liftedFormSection (R := R) (n := n) (X := X) (Z := Z) μ j J d F hF hFJ)) := by
  let := hc
  exact IsIso.of_isIso_fac_right
    (@liftedFormSection_openNaturality R hR n X Z W μ c hcOpen j J d F hF hFJ)

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
