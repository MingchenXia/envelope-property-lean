import EnvelopeProperty.Projective.NativeQuotient

/-! # Actual homogeneous ideal sheaves retain original coordinate arithmetic -/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsCore
open ProjBerk
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

/-- The ENTIRE coordinate ideal is the actual forward coordinate image of the
same original homogeneous ideal's dehomogenization. -/
theorem quotientIdealSheaf_coordinateIdeal
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (j : Fin (n + 1)) :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal
      ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩ =
      (J.toIdeal.map (coordinateDehom j).toRingHom).map
        (nativeCoordinateSectionsIso (R := R) j).hom.hom := by
  have h := homogeneousQuotient_coordinateSectionIdeal J j
  have hs : Function.Surjective (nativeCoordinateSectionsIso (R := R) j).hom.hom :=
    (ConcreteCategory.bijective_of_isIso
      (nativeCoordinateSectionsIso (R := R) j).hom).surjective
  exact (Ideal.map_comap_of_surjective _ hs _).symm.trans
    (congrArg (Ideal.map (nativeCoordinateSectionsIso (R := R) j).hom.hom) h)

/-- Inclusion is preserved by the SAME native quotient-kernel ideal sheaves. -/
theorem quotientIdealSheaf_mono
    {I J : HomogeneousIdeal (ProjectiveGrading R n)} (h : I ≤ J) :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) I ≤
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
  apply Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  rw [quotientIdealSheaf_coordinateIdeal, quotientIdealSheaf_coordinateIdeal]
  exact Ideal.map_mono (Ideal.map_mono h)

/-- Products are preserved as WHOLE native ideal sheaves, without saturation
or radical replacement of the actual coordinate ideals. -/
theorem quotientIdealSheaf_mul
    (I J : HomogeneousIdeal (ProjectiveGrading R n)) :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) (I * J) =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) I *
        GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  change (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) (I * J)).ideal _ =
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) I).ideal _ *
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal _
  rw [quotientIdealSheaf_coordinateIdeal, quotientIdealSheaf_coordinateIdeal,
    quotientIdealSheaf_coordinateIdeal]
  change ((I.toIdeal * J.toIdeal).map _).map _ = _
  rw [Ideal.map_mul, Ideal.map_mul]

/-- The actual unit homogeneous ideal gives the actual whole unit ideal sheaf. -/
theorem quotientIdealSheaf_top :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) ⊤ = ⊤ := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  change (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) ⊤).ideal _ = ⊤
  rw [quotientIdealSheaf_coordinateIdeal]
  change ((⊤ : Ideal (MvPolynomial (Fin (n + 1)) R)).map _).map _ = ⊤
  rw [Ideal.map_top, Ideal.map_top]

end EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsCore
