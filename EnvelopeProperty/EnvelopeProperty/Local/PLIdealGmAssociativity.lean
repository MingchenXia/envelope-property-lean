/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealGmModObj
import EnvelopeProperty.Local.PLIdealGmDoubleProduct

/-!
# The existing categorical action structure on the actual constructed blowup

The true whole double-group source isomorphism transports the previously
proved entire universal Laurent action diagrams to the existing `ModObj` laws.
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
variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hL : ∀ (S : Type u) [CommRing S] (f : k →+* S) (u : Sˣ),
  (L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (u : S))) =
      L.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

private theorem mulWhisker_fst :
    ((MonObj.mul (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L).left ≫
        pullback.fst (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L) =
      pullback.fst (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupBaseStructure J I L) ≫
          (MonObj.mul (X := nativeMultiplicativeGroup k)).left :=
  Over.whiskerRight_left_fst (MonObj.mul (X := nativeMultiplicativeGroup k))

private theorem mulWhisker_snd :
    ((MonObj.mul (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L).left ≫
        pullback.snd (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L) =
      pullback.snd (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupBaseStructure J I L) :=
  Over.whiskerRight_left_snd (MonObj.mul (X := nativeMultiplicativeGroup k))

private theorem assoc_fst :
    (α_ (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k)
        (nativeClosedBlowupAsOver J I L)).hom.left ≫
        pullback.fst (nativeMultiplicativeGroup k).hom
          (nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L).hom =
      pullback.fst (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupBaseStructure J I L) ≫
        pullback.fst (nativeMultiplicativeGroup k).hom (nativeMultiplicativeGroup k).hom :=
  Over.associator_hom_left_fst _ _ _

private theorem assoc_snd_fst :
    (α_ (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k)
        (nativeClosedBlowupAsOver J I L)).hom.left ≫
        pullback.snd (nativeMultiplicativeGroup k).hom
          (nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L).hom ≫
        pullback.fst (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L) =
      pullback.fst (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupBaseStructure J I L) ≫
        pullback.snd (nativeMultiplicativeGroup k).hom (nativeMultiplicativeGroup k).hom :=
  Over.associator_hom_left_snd_fst _ _ _

private theorem assoc_snd_snd :
    (α_ (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k)
        (nativeClosedBlowupAsOver J I L)).hom.left ≫
        pullback.snd (nativeMultiplicativeGroup k).hom
          (nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L).hom ≫
        pullback.snd (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L) =
      pullback.snd (nativeMultiplicativeGroup k ⊗ nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupBaseStructure J I L) :=
  Over.associator_hom_left_snd_snd _ _ _

private theorem smulWhisker_fst :
    ((nativeMultiplicativeGroup k) ◁ nativeClosedProductIdealGmSmul J I L hI hL).left ≫
        pullback.fst (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L) =
      pullback.fst (nativeMultiplicativeGroup k).hom
        (nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L).hom :=
  Over.whiskerLeft_left_fst (nativeClosedProductIdealGmSmul J I L hI hL)

private theorem smulWhisker_snd :
    ((nativeMultiplicativeGroup k) ◁ nativeClosedProductIdealGmSmul J I L hI hL).left ≫
        pullback.snd (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L) =
      pullback.snd (nativeMultiplicativeGroup k).hom
        (nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L).hom ≫
        (nativeClosedProductIdealGmSmul J I L hI hL).left :=
  Over.whiskerLeft_left_snd (nativeClosedProductIdealGmSmul J I L hI hL)

/-- The entire categorical multiplication product is precisely the whole
original universal product-unit evaluation product. -/
theorem nativeClosedProductIdealGmSmul_mulProduct :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫
        ((MonObj.mul (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L).left ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure J I L)).hom =
      nativeClosedProductIdealGmEvaluationMap J I L
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
        (parameterLaurentProductUnit k) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      mulWhisker_snd, nativeClosedBlowupDoubleProductIso_snd,
      nativeClosedProductIdealGmEvaluationMap_fst]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      mulWhisker_fst]
    rw [← Category.assoc, nativeClosedBlowupDoubleProductIso_fst]
    simp only [Category.assoc, nativeMultiplicativeGroup_mul,
      nativeClosedProductIdealGmEvaluationMap_snd]
    rfl

/-- The entire inner categorical action product is the actual outer-Laurent
unit evaluation product. -/
theorem nativeClosedProductIdealGmSmul_innerProduct :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫
        (α_ (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k)
          (nativeClosedBlowupAsOver J I L)).hom.left ≫
        pullback.snd (nativeMultiplicativeGroup k).hom
          (nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L).hom ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure J I L)).hom =
      nativeClosedProductIdealGmEvaluationMap J I L
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
        (parameterLaurentUnit k[T;T⁻¹]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      assoc_snd_snd, nativeClosedBlowupDoubleProductIso_snd,
      nativeClosedProductIdealGmEvaluationMap_fst]
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      assoc_snd_fst, nativeClosedBlowupDoubleProductIso_fst_snd,
      nativeClosedProductIdealGmEvaluationMap_snd, nativeLaurent_eval_second]

/-- The full categorical sequential-action product is exactly the original
whole universal sequential Laurent product, with its two complete components. -/
theorem nativeClosedProductIdealGmSmul_thenProduct :
    (nativeClosedBlowupDoubleProductIso J I L).hom ≫
        (α_ (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k)
          (nativeClosedBlowupAsOver J I L)).hom.left ≫
        ((nativeMultiplicativeGroup k) ◁ nativeClosedProductIdealGmSmul J I L hI hL).left ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure J I L)).hom =
      nativeClosedProductIdealGmThenMap J I L hI hL
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
        (parameterLaurentUnit k[T;T⁻¹])
        (Units.map (LaurentPolynomial.C : k[T;T⁻¹] →+* k[T;T⁻¹][T;T⁻¹]).toMonoidHom
          (parameterLaurentUnit k)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      smulWhisker_snd, nativeClosedProductIdealGmThenMap_fst]
    simp only [nativeClosedProductIdealGmSmul, Over.homMk_left]
    calc
      _ = nativeClosedProductIdealGmEvaluationMap J I L
          (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
          (parameterLaurentUnit k[T;T⁻¹]) ≫ nativeClosedProductIdealGmAction J I L hI hL := by
        simpa only [Category.assoc] using congrArg
          (fun f => f ≫ nativeClosedProductIdealGmAction J I L hI hL)
          (nativeClosedProductIdealGmSmul_innerProduct J I L)
      _ = _ := nativeClosedProductIdealGmEvaluationMap_action J I L hI hL _ _
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      smulWhisker_fst, assoc_fst,
      nativeClosedBlowupDoubleProductIso_fst_fst,
      nativeClosedProductIdealGmThenMap_snd, nativeLaurent_eval_first]

/-- The actual constructed whole action satisfies the genuine existing
categorical associativity equation. -/
theorem nativeClosedProductIdealGmSmul_mul :
    ((MonObj.mul (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L) ≫
        nativeClosedProductIdealGmSmul J I L hI hL =
      (α_ (nativeMultiplicativeGroup k) (nativeMultiplicativeGroup k)
        (nativeClosedBlowupAsOver J I L)).hom ≫
        ((nativeMultiplicativeGroup k) ◁ nativeClosedProductIdealGmSmul J I L hI hL) ≫
          nativeClosedProductIdealGmSmul J I L hI hL := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (nativeClosedBlowupDoubleProductIso J I L).hom).mp
  simp only [Over.comp_left, nativeClosedProductIdealGmSmul, Over.homMk_left]
  calc
    _ = nativeClosedProductIdealGmEvaluationMap J I L
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
        (parameterLaurentProductUnit k) ≫ nativeClosedProductIdealGmAction J I L hI hL := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ nativeClosedProductIdealGmAction J I L hI hL)
        (nativeClosedProductIdealGmSmul_mulProduct J I L)
    _ = nativeClosedProductIdealGmThenMap J I L hI hL
        (LaurentPolynomial.C.comp (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
        (parameterLaurentUnit k[T;T⁻¹])
        (Units.map (LaurentPolynomial.C : k[T;T⁻¹] →+* k[T;T⁻¹][T;T⁻¹]).toMonoidHom
          (parameterLaurentUnit k)) ≫ nativeClosedProductIdealGmAction J I L hI hL :=
      (nativeClosedProductIdealGmAction_multiplication J I L hI hL _ _ _).symm
    _ = _ := by
      simpa only [Category.assoc, nativeClosedProductIdealGmSmul, Over.homMk_left] using
        (congrArg (fun f => f ≫ nativeClosedProductIdealGmAction J I L hI hL)
          (nativeClosedProductIdealGmSmul_thenProduct J I L hI hL)).symm

/-- The existing categorical action structure, constructed from the actual
ideal invariance and the proved whole geometric action diagrams. -/
@[instance_reducible]
def nativeClosedProductIdealGmModObj :
    ModObj (nativeMultiplicativeGroup k) (nativeClosedBlowupAsOver J I L) where
  smul := nativeClosedProductIdealGmSmul J I L hI hL
  one_smul := nativeClosedProductIdealGmSmul_one J I L hI hL
  mul_smul := nativeClosedProductIdealGmSmul_mul J I L hI hL

end EnvelopeProperty.ProjBerk
