import EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsCore
import EnvelopeProperty.Berkovich.SchemeIdealPullback

/-! # Actual original closed extension and homogeneous sums -/

open CategoryTheory AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsClosedExtension
open ProjBerk EnvelopeGradedBaseIdealsCore
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ENTIRE original ideal pulled to a genuine closed immersion and
extended back gains exactly the SAME original whole kernel ideal. -/
theorem map_comap_eq_sup_ker {X Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j]
    (I : Y.IdealSheafData) : (I.comap j).map j = I ⊔ j.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    Scheme.IdealSheafData.comap_ideal_of_affine_opens I j
      ⟨j ⁻¹ᵁ U.1, U.2.preimage j⟩ U le_rfl, Scheme.Hom.appLE_eq_app]
  change ((I.ideal U).map (j.app U).hom).comap (j.app U).hom = I.ideal U ⊔ j.ker.ideal U
  rw [Scheme.Hom.ker_apply]
  exact Ideal.comap_map_of_surjective (j.app U).hom (j.app_surjective U U.2) _

/-- Addition is preserved by the SAME actual original homogeneous ideal sheaves. -/
theorem quotientIdealSheaf_sup {R : Type u} [CommRing R] {n : ℕ}
    (I J : HomogeneousIdeal (ProjectiveGrading R n)) :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) (I ⊔ J) =
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) I ⊔
        GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : Fin (n + 1) => ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  change (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) (I ⊔ J)).ideal _ =
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) I).ideal _ ⊔
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).ideal _
  rw [quotientIdealSheaf_coordinateIdeal, quotientIdealSheaf_coordinateIdeal,
    quotientIdealSheaf_coordinateIdeal]
  change ((I.toIdeal ⊔ J.toIdeal).map _).map _ = _
  rw [Ideal.map_sup, Ideal.map_sup]

end EnvelopeProperty.Char0.EnvelopeGradedBaseIdealsClosedExtension
