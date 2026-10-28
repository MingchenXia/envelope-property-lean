/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealGmProduct
import EnvelopeProperty.Projective.NativeMultiplicativeGroupProjections

/-!
# Actual whole double-group source of the constructed blowup action

True coefficient-product and group-product isomorphisms identify the entire
double Laurent source with the actual categorical double-group product.
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

/-- The actual whole double Laurent family source is the entire categorical
double-group product of the same original blowup. -/
def nativeClosedBlowupDoubleProductIso :
    pullback (nativeClosedProductIdeal J I L).blowUpπ
      (nativeClosedParameterFamilyMap J
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹])) 1) ≅
      pullback (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupBaseStructure J I L) :=
  (nativeClosedBlowupFamilyProductIso J I L
    (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))).trans
      ((asIso (pullback.map _ _ _ _ (𝟙 _) (nativeMultiplicativeGroupProductIso k).hom (𝟙 _)
        (by simp) (by simpa only [Category.comp_id] using
          (nativeMultiplicativeGroupProductIso_base k).symm))).trans
        (pullbackSymmetry (nativeClosedBlowupBaseStructure J I L)
          (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom))

/-- The full double-group comparison retains the actual entire group-pair morphism. -/
@[reassoc]
theorem nativeClosedBlowupDoubleProductIso_fst :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫
        nativeClosedBaseStructure (J.map (coefficientGradedMap
          (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹])))) ≫
        (nativeMultiplicativeGroupProductIso k).hom := by
  simp only [nativeClosedBlowupDoubleProductIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullback.lift_snd,
    nativeClosedBlowupFamilyProductIso_hom_snd_assoc]

/-- The full double-group comparison has precisely its original first group coordinate. -/
@[reassoc]
theorem nativeClosedBlowupDoubleProductIso_fst_fst :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫
        nativeClosedBaseStructure (J.map (coefficientGradedMap
          (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹])))) ≫
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k[T;T⁻¹] →+* k[T;T⁻¹][T;T⁻¹])) := by
  simp only [nativeClosedBlowupDoubleProductIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst_assoc, pullback.lift_snd_assoc,
    nativeMultiplicativeGroupProductIso_fst,
    nativeClosedBlowupFamilyProductIso_hom_snd_assoc]

/-- The full double-group comparison has precisely its original second group coordinate. -/
@[reassoc]
theorem nativeClosedBlowupDoubleProductIso_fst_snd :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫
        nativeClosedBaseStructure (J.map (coefficientGradedMap
          (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹])))) ≫
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹]))) := by
  simp only [nativeClosedBlowupDoubleProductIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst_assoc, pullback.lift_snd_assoc,
    nativeMultiplicativeGroupProductIso_snd,
    nativeClosedBlowupFamilyProductIso_hom_snd_assoc]

/-- The full double-group comparison preserves the whole original blowup component. -/
@[reassoc]
theorem nativeClosedBlowupDoubleProductIso_snd :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫ pullback.snd _ _ = pullback.fst _ _ := by
  simp only [nativeClosedBlowupDoubleProductIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullback.lift_fst, Category.comp_id,
    nativeClosedBlowupFamilyProductIso_hom_fst]

end EnvelopeProperty.ProjBerk
