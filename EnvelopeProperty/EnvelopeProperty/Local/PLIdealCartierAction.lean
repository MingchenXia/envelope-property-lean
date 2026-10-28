/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealGmAssociativity
import Hironaka.Scheme.BlowUp.ProductCenter

/-!
# Whole group-action invariance of the actual Cartier ideal factors

The true lifted family projection triangle and actual entire original ideal
invariance prove equality of whole ideal-sheaf comaps on the whole group
product. This supplies genuine equivariant Cartier divisor data. Comparing
module-sheaf pullbacks and constructing a linearization remain separate work.
-/

open scoped Classical Polynomial LaurentPolynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ}
variable (J : HomogeneousIdeal (ProjectiveGrading k n))
variable (I L : HomogeneousIdeal (ProjectiveGrading k[X] n))

/-- The actual entire original parameter ideal pulled to the actual product blowup. -/
def nativeClosedPullbackIdeal (A : HomogeneousIdeal (ProjectiveGrading k[X] n)) :
    (nativeClosedProductIdeal J I L).blowUp.IdealSheafData :=
  ((nativeHomogeneousIdealSheaf A).comap (nativeConstantIdeal J).subschemeι).comap
    (nativeClosedProductIdeal J I L).blowUpπ

/-- Both actual original factors are genuine Cartier ideals on this same blowup. -/
theorem nativeClosedCartierIdeals_isInvertible :
    (nativeClosedPullbackIdeal J I L I).IsInvertible ∧
      (nativeClosedPullbackIdeal J I L L).IsInvertible := by
  have h := Scheme.IdealSheafData.blowUp.isInvertible_comap_π (nativeClosedProductIdeal J I L)
  change (((nativeHomogeneousIdealSheaf I).comap (nativeConstantIdeal J).subschemeι *
    (nativeHomogeneousIdealSheaf L).comap (nativeConstantIdeal J).subschemeι).comap
      (nativeClosedProductIdeal J I L).blowUpπ).IsInvertible at h
  rw [Scheme.IdealSheafData.comap_mul] at h
  exact Scheme.IdealSheafData.IsInvertible.of_mul h

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hL : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- The actual lifted family preserves each actual full invariant ideal,
as equality of entire ideal-sheaf comaps along the true whole family maps. -/
theorem nativeClosedPullbackIdeal_comap_familyLift
    (A : HomogeneousIdeal (ProjectiveGrading k[X] n)) {S : Type u} [CommRing S]
    (f : k →+* S) (u : Sˣ)
    (hA : (A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
      (MvPolynomial.map (parameterScaleHom (u : S))) =
        A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) :
    (nativeClosedPullbackIdeal J I L A).comap
        (nativeClosedProductIdealFamilyLift J I L hI hL f u) =
      (nativeClosedPullbackIdeal J I L A).comap
        (pullback.fst (nativeClosedProductIdeal J I L).blowUpπ (nativeClosedParameterFamilyMap J f 1)) := by
  let K := (nativeHomogeneousIdealSheaf A).comap (nativeConstantIdeal J).subschemeι
  change (K.comap (nativeClosedProductIdeal J I L).blowUpπ).comap _ =
    (K.comap (nativeClosedProductIdeal J I L).blowUpπ).comap _
  calc
    _ = K.comap (nativeClosedProductIdealFamilyLift J I L hI hL f u ≫
        (nativeClosedProductIdeal J I L).blowUpπ) :=
      (Scheme.IdealSheafData.comap_comp K _ _).symm
    _ = K.comap (pullback.snd _ _ ≫ nativeClosedParameterFamilyMap J f u) :=
      congrArg K.comap (nativeClosedProductIdealFamilyLift_π J I L hI hL f u)
    _ = (K.comap (nativeClosedParameterFamilyMap J f u)).comap (pullback.snd _ _) :=
      Scheme.IdealSheafData.comap_comp K _ _
    _ = (K.comap (nativeClosedParameterFamilyMap J f 1)).comap (pullback.snd _ _) :=
      congrArg (fun N : (nativeConstantIdeal (J.map (coefficientGradedMap f))).subscheme.IdealSheafData =>
        N.comap (pullback.snd (nativeClosedProductIdeal J I L).blowUpπ
          (nativeClosedParameterFamilyMap J f 1)))
        (nativeClosedIdeal_comap_parameterFamily_eq J A f u hA)
    _ = K.comap (pullback.snd _ _ ≫ nativeClosedParameterFamilyMap J f 1) :=
      (Scheme.IdealSheafData.comap_comp K _ _).symm
    _ = K.comap (pullback.fst _ _ ≫ (nativeClosedProductIdeal J I L).blowUpπ) :=
      congrArg K.comap pullback.condition.symm
    _ = _ := Scheme.IdealSheafData.comap_comp K _ _

/-- The actual entire geometric group action preserves each true original
invariant ideal as a whole nonradical ideal sheaf on the whole group product. -/
theorem nativeClosedPullbackIdeal_comap_gmAction
    (A : HomogeneousIdeal (ProjectiveGrading k[X] n))
    (hA : (A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom
        (LaurentPolynomial.C : k →+* k[T;T⁻¹])))).map
      (MvPolynomial.map (parameterScaleHom ((parameterLaurentUnit k : k[T;T⁻¹]ˣ) : k[T;T⁻¹]))) =
        A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom LaurentPolynomial.C))) :
    (nativeClosedPullbackIdeal J I L A).comap (nativeClosedProductIdealGmAction J I L hI hL) =
      (nativeClosedPullbackIdeal J I L A).comap
        (pullback.fst (nativeClosedBlowupBaseStructure J I L) (nativeMultiplicativeGroup k).hom) := by
  rw [nativeClosedProductIdealGmAction, Scheme.IdealSheafData.comap_comp,
    nativeClosedPullbackIdeal_comap_familyLift J I L hI hL A LaurentPolynomial.C
      (parameterLaurentUnit k) hA, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  change (nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).inv ≫
    pullback.fst (nativeClosedProductIdeal J I L).blowUpπ
      (nativeClosedParameterFamilyMap J LaurentPolynomial.C 1) =
    pullback.fst (nativeClosedBlowupBaseStructure J I L)
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹])))
  apply (cancel_epi (nativeClosedBlowupFamilyProductIso J I L LaurentPolynomial.C).hom).mp
  rw [Iso.hom_inv_id_assoc, nativeClosedBlowupFamilyProductIso_hom_fst]

/-- The actual categorical action preserves the whole true Cartier ideal
on the entire actual categorical group product. -/
theorem nativeClosedPullbackIdeal_comap_gmSmul
    (A : HomogeneousIdeal (ProjectiveGrading k[X] n))
    (hA : (A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom
        (LaurentPolynomial.C : k →+* k[T;T⁻¹])))).map
      (MvPolynomial.map (parameterScaleHom ((parameterLaurentUnit k : k[T;T⁻¹]ˣ) : k[T;T⁻¹]))) =
        A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom LaurentPolynomial.C))) :
    (nativeClosedPullbackIdeal J I L A).comap
        (nativeClosedProductIdealGmSmul J I L hI hL).left =
      (nativeClosedPullbackIdeal J I L A).comap
        (pullback.snd (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L)) := by
  change (nativeClosedPullbackIdeal J I L A).comap
    ((pullbackSymmetry (nativeMultiplicativeGroup k).hom
      (nativeClosedBlowupBaseStructure J I L)).hom ≫
      nativeClosedProductIdealGmAction J I L hI hL) = _
  rw [Scheme.IdealSheafData.comap_comp, nativeClosedPullbackIdeal_comap_gmAction J I L hI hL A hA,
    ← Scheme.IdealSheafData.comap_comp, pullbackSymmetry_hom_comp_fst]

end EnvelopeProperty.ProjBerk
