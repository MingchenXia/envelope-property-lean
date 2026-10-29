/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Projective.NativeQuotient

/-!
# Whole coordinate sections of the original projective quotient

The original coordinate ideal comparison and the genuine affine subscheme
section isomorphism identify the whole original kernel scheme's sections
with the literal dehomogenized quotient. Every original polynomial pullback
has its original quotient class. Arbitrary commutative coefficient rings,
nilpotents and empty charts are retained without primeness or relevance.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace EnvelopeProperty.ProjBerk

variable {R : Type u} [CommRing R] {n : ℕ}

private theorem quotientCoordinateIdeal_map
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (j : Fin (n + 1)) :
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal
      ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩ =
        (J.toIdeal.map (coordinateDehom j).toRingHom).map
          (nativeCoordinateSectionsIso j).hom.hom := by
  rw [← homogeneousQuotient_coordinateSectionIdeal J j]
  exact (Ideal.map_comap_of_surjective _
    (nativeCoordinateSectionsIso j).commRingCatIsoToRingEquiv.surjective _).symm

/-- The entire actual native quotient's coordinate section ring is the
literal quotient by the original dehomogenized ideal. -/
def nativeQuotientCoordinateSectionsEquiv
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (j : Fin (n + 1)) :
    Γ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).subscheme,
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).subschemeι ⁻¹ᵁ
        nativeCoordinateOpen j) ≃+*
      CoordinateRing R j ⧸ J.toIdeal.map (coordinateDehom j).toRingHom := by
  let I := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J
  let U : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.trans
    (Ideal.quotientEquiv (J.toIdeal.map (coordinateDehom j).toRingHom) (I.ideal U)
      (nativeCoordinateSectionsIso j).commRingCatIsoToRingEquiv
      (quotientCoordinateIdeal_map J j)).symm

/-- The actual inclusion pullback of every original coordinate polynomial
goes to its original quotient class, including all coefficients. -/
theorem nativeQuotientCoordinateSectionsEquiv_pullback
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (j : Fin (n + 1))
    (p : CoordinateRing R j) :
    nativeQuotientCoordinateSectionsEquiv J j
      (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).subschemeι.app
        (nativeCoordinateOpen j)).hom ((nativeCoordinateSectionsIso j).hom.hom p)) =
      Ideal.Quotient.mk (J.toIdeal.map (coordinateDehom j).toRingHom) p := by
  let I := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J
  let U : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩
  have hι (c : Γ(NativeProjectiveScheme R n, nativeCoordinateOpen j)) :
      (I.subschemeObjIso U).commRingCatIsoToRingEquiv
        ((I.subschemeι.app (nativeCoordinateOpen j)).hom c) =
          Ideal.Quotient.mk (I.ideal U) c := by
    change (I.subschemeι.app U.1 ≫ (I.subschemeObjIso U).hom).hom c = _
    rw [I.subschemeι_app U, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  change (Ideal.quotientEquiv (J.toIdeal.map (coordinateDehom j).toRingHom) (I.ideal U)
    (nativeCoordinateSectionsIso j).commRingCatIsoToRingEquiv
    (quotientCoordinateIdeal_map J j)).symm
      ((I.subschemeObjIso U).commRingCatIsoToRingEquiv
        ((I.subschemeι.app (nativeCoordinateOpen j)).hom
          ((nativeCoordinateSectionsIso j).hom.hom p))) = _
  rw [hι]
  exact (Ideal.quotientEquiv (J.toIdeal.map (coordinateDehom j).toRingHom) (I.ideal U)
    (nativeCoordinateSectionsIso j).commRingCatIsoToRingEquiv
    (quotientCoordinateIdeal_map J j)).symm_apply_apply (Ideal.Quotient.mk _ p)

end EnvelopeProperty.ProjBerk
