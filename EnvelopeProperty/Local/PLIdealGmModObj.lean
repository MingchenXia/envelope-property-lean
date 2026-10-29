/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealGmProduct
import EnvelopeProperty.Projective.NativeMultiplicativeGroupProjections
import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Packaging the actual whole group diagrams in the existing categorical interface

All morphisms and laws are derived from the actual constructed blowup action.
No action predicate or hypothesis class is introduced.
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

/-- The actual original blowup as a genuine object over the original field. -/
abbrev nativeClosedBlowupAsOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (nativeClosedBlowupBaseStructure J I L)

/-- The actual categorical action morphism, using the genuine whole product
symmetry and the proved original-field action triangle. -/
def nativeClosedProductIdealGmSmul :
    nativeMultiplicativeGroup k ⊗ nativeClosedBlowupAsOver J I L ⟶
      nativeClosedBlowupAsOver J I L :=
  Over.homMk
    ((pullbackSymmetry (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L)).hom ≫
      nativeClosedProductIdealGmAction J I L hI hL) (by
        change ((pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure J I L)).hom ≫
          nativeClosedProductIdealGmAction J I L hI hL) ≫
            nativeClosedBlowupBaseStructure J I L =
          pullback.fst (nativeMultiplicativeGroup k).hom
            (nativeClosedBlowupBaseStructure J I L) ≫ (nativeMultiplicativeGroup k).hom
        rw [Category.assoc, nativeClosedProductIdealGmAction_over_base,
          ← Category.assoc, pullbackSymmetry_hom_comp_fst]
        exact pullback.condition.symm)

/-- The actual categorical unit product map is the proved genuine whole unit
section, by its two exact entire pullback components. -/
theorem nativeClosedProductIdealGmSmul_unitProduct :
    (λ_ (nativeClosedBlowupAsOver J I L)).inv.left ≫
        ((MonObj.one (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L).left ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom (nativeClosedBlowupBaseStructure J I L)).hom =
      nativeClosedProductIdealGmUnitSection J I L := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst]
    calc
      _ = (λ_ (nativeClosedBlowupAsOver J I L)).inv.left ≫
          pullback.snd (𝟙 _) (nativeClosedBlowupAsOver J I L).hom := by
        exact congrArg (fun f => (λ_ (nativeClosedBlowupAsOver J I L)).inv.left ≫ f)
          (Over.whiskerRight_left_snd (R := nativeClosedBlowupAsOver J I L)
            (MonObj.one (X := nativeMultiplicativeGroup k)))
      _ = 𝟙 _ := Over.leftUnitor_inv_left_snd (nativeClosedBlowupAsOver J I L)
      _ = _ := (nativeClosedProductIdealGmUnitSection_fst J I L).symm
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd]
    calc
      _ = (λ_ (nativeClosedBlowupAsOver J I L)).inv.left ≫
          pullback.fst (𝟙 _) (nativeClosedBlowupAsOver J I L).hom ≫
            (MonObj.one (X := nativeMultiplicativeGroup k)).left := by
        exact congrArg (fun f => (λ_ (nativeClosedBlowupAsOver J I L)).inv.left ≫ f)
          (Over.whiskerRight_left_fst (R := nativeClosedBlowupAsOver J I L)
            (MonObj.one (X := nativeMultiplicativeGroup k)))
      _ = (nativeClosedBlowupAsOver J I L).hom ≫
          (MonObj.one (X := nativeMultiplicativeGroup k)).left :=
        Over.leftUnitor_inv_left_fst_assoc _ _
      _ = _ := (nativeClosedProductIdealGmUnitSection_snd J I L).symm

/-- The actual action satisfies the existing categorical unit equation. -/
theorem nativeClosedProductIdealGmSmul_one :
    ((MonObj.one (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L) ≫
        nativeClosedProductIdealGmSmul J I L hI hL = (λ_ (nativeClosedBlowupAsOver J I L)).hom := by
  apply (cancel_epi (λ_ (nativeClosedBlowupAsOver J I L)).inv).mp
  apply Over.OverMorphism.ext
  calc
    _ = ((λ_ (nativeClosedBlowupAsOver J I L)).inv.left ≫
        ((MonObj.one (X := nativeMultiplicativeGroup k)) ▷ nativeClosedBlowupAsOver J I L).left ≫
        (pullbackSymmetry (nativeMultiplicativeGroup k).hom
          (nativeClosedBlowupBaseStructure J I L)).hom) ≫
        nativeClosedProductIdealGmAction J I L hI hL := by
      simp only [Over.comp_left, nativeClosedProductIdealGmSmul, Over.homMk_left, Category.assoc]
    _ = nativeClosedProductIdealGmUnitSection J I L ≫
        nativeClosedProductIdealGmAction J I L hI hL := by
      rw [nativeClosedProductIdealGmSmul_unitProduct]
    _ = 𝟙 _ := nativeClosedProductIdealGmAction_unit J I L hI hL
    _ = _ := by
      simp only [Iso.inv_hom_id, Over.id_left]
      rfl

end EnvelopeProperty.ProjBerk
