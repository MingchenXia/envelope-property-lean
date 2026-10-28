/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Berkovich.SchemeNormalizationDominantLift
import EnvelopeProperty.AlgGeom.NormalSchemeNormalization
import EnvelopeProperty.Projective.NativeMultiplicativeProductNormality
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory
open scoped CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.IntegralSchemeNormalization
variable {R : Type u} [CommRing R]
variable (B : Over (Spec (CommRingCat.of R))) [IsIntegral B.left]
local notation "G" => ProjBerk.nativeMultiplicativeGroup R
local notation "N" => Over.mk (projection B.left ≫ B.hom)

private def normalizationOverProjection : N ⟶ B := Over.homMk (projection B.left) rfl

private def productUnit (X : Over (Spec (CommRingCat.of R))) : X ⟶ G ⊗ X :=
  (λ_ X).inv ≫ (η[G] ▷ X)

private theorem productUnit_naturality {X Y : Over (Spec (CommRingCat.of R))}
    (p : X ⟶ Y) : productUnit X ≫ (G ◁ p) = p ≫ productUnit Y := by
  simp only [productUnit]
  rw [Category.assoc, ← whisker_exchange]
  simp

private theorem originalAction_unit [ModObj G B] :
    productUnit N ≫ (G ◁ normalizationOverProjection B) ≫ ModObj.smul (M := G) (X := B) =
      normalizationOverProjection B := by
  rw [← Category.assoc, productUnit_naturality]
  simp only [productUnit, Category.assoc, ModObj.one_smul_self, Iso.inv_hom_id, Category.comp_id]

private theorem originalAction_lift [ModObj G B] :
    ∃! a : G ⊗ N ⟶ N,
      a ≫ normalizationOverProjection B =
        (G ◁ normalizationOverProjection B) ≫ ModObj.smul (M := G) (X := B) := by
  let : IsIntegral (normalization B.left) := inferInstance
  let : IsIntegral (N).left := by
    change IsIntegral (normalization B.left)
    infer_instance
  let p := normalizationOverProjection B
  let h : (G ⊗ N).left ⟶ B.left :=
    ((G ◁ p) ≫ ModObj.smul (M := G) (X := B)).left
  let : IsIntegral (G ⊗ N).left :=
    ProjBerk.nativeMultiplicativeGroup_pullback_isIntegral (N).hom
  have hnormal : ∀ z : (G ⊗ N).left,
      IsIntegrallyClosed ((G ⊗ N).left.presheaf.stalk z) :=
    ProjBerk.nativeMultiplicativeGroup_pullback_stalk_isIntegrallyClosed (N).hom
      (stalk_isIntegrallyClosed B.left)
  have hu : (productUnit N).left ≫ h = projection B.left :=
    congrArg (fun a => a.left) (originalAction_unit B)
  let : IsDominant (projection B.left) := ⟨(projection_surjective B.left).denseRange⟩
  have : IsDominant ((productUnit N).left ≫ h) := by rw [hu]; infer_instance
  let : IsDominant h := IsDominant.of_comp (productUnit N).left h
  obtain ⟨a, ha, huniq⟩ := existsUnique_dominant_normalization_lift h hnormal
  have hw : a ≫ (N).hom = (G ⊗ N).hom := by
    change a ≫ (projection B.left ≫ B.hom) = _
    rw [← Category.assoc, ha]
    exact ((G ◁ p) ≫ ModObj.smul (M := G) (X := B)).w
  let a' : G ⊗ N ⟶ N := Over.homMk a hw
  have ha' : a' ≫ p = (G ◁ p) ≫ ModObj.smul (M := G) (X := B) := by
    ext
    exact ha
  refine ⟨a', ha', fun b hb => ?_⟩
  apply Over.OverMorphism.ext
  exact huniq b.left (congrArg (fun t => t.left) hb)

private theorem normalized_hom_ext
    (Q : Over (Spec (CommRingCat.of R))) [IsIntegral Q.left]
    (hQ : ∀ q : Q.left, IsIntegrallyClosed (Q.left.presheaf.stalk q))
    (a b : Q ⟶ N) (hab : a ≫ normalizationOverProjection B = b ≫ normalizationOverProjection B)
    [IsDominant (a ≫ normalizationOverProjection B).left] : a = b := by
  obtain ⟨c, hc, hu⟩ := existsUnique_dominant_normalization_lift
    (a ≫ normalizationOverProjection B).left hQ
  apply Over.OverMorphism.ext
  exact (hu a.left rfl).trans (hu b.left (congrArg (fun t => t.left) hab.symm)).symm

private theorem liftedAction_unit [ModObj G B]
    (a : G ⊗ N ⟶ N)
    (ha : a ≫ normalizationOverProjection B =
      (G ◁ normalizationOverProjection B) ≫ ModObj.smul (M := G) (X := B)) :
    productUnit N ≫ a = 𝟙 N := by
  let : IsIntegral (normalization B.left) := inferInstance
  let : IsIntegral (N).left := by change IsIntegral (normalization B.left); infer_instance
  have he : (productUnit N ≫ a) ≫ normalizationOverProjection B = normalizationOverProjection B := by
    rw [Category.assoc, ha]
    exact originalAction_unit B
  have : IsDominant ((productUnit N ≫ a) ≫ normalizationOverProjection B).left := by
    rw [he]
    exact ⟨(projection_surjective B.left).denseRange⟩
  apply normalized_hom_ext B N (stalk_isIntegrallyClosed B.left) _ _
  simpa using he

private theorem liftedAction_mul_projection [ModObj G B]
    (a : G ⊗ N ⟶ N)
    (ha : a ≫ normalizationOverProjection B =
      (G ◁ normalizationOverProjection B) ≫ ModObj.smul (M := G) (X := B)) :
    ((α_ G G N).inv ≫ (μ[G] ▷ N) ≫ a) ≫ normalizationOverProjection B =
      ((G ◁ a) ≫ a) ≫ normalizationOverProjection B := by
  let p := normalizationOverProjection B
  change (α_ G G N).inv ≫ (μ[G] ▷ N) ≫ a ≫ p =
    (G ◁ a) ≫ a ≫ p
  rw [ha, ← whisker_exchange_assoc, ModObj.mul_smul_self]
  rw [← associator_inv_naturality_right_assoc]
  simp only [Iso.inv_hom_id_assoc]
  conv_rhs => rw [← whiskerLeft_comp_assoc, ha, whiskerLeft_comp_assoc]

private theorem liftedAction_mul [ModObj G B]
    (a : G ⊗ N ⟶ N)
    (ha : a ≫ normalizationOverProjection B =
      (G ◁ normalizationOverProjection B) ≫ ModObj.smul (M := G) (X := B)) :
    (μ[G] ▷ N) ≫ a = (α_ G G N).hom ≫ (G ◁ a) ≫ a := by
  let : IsIntegral (normalization B.left) := inferInstance
  let : IsIntegral (N).left := by change IsIntegral (normalization B.left); infer_instance
  let : IsIntegral (G ⊗ N).left :=
    ProjBerk.nativeMultiplicativeGroup_pullback_isIntegral (N).hom
  let : IsIntegral (G ⊗ (G ⊗ N)).left :=
    ProjBerk.nativeMultiplicativeGroup_pullback_isIntegral (G ⊗ N).hom
  have hQ : ∀ z : (G ⊗ (G ⊗ N)).left,
      IsIntegrallyClosed ((G ⊗ (G ⊗ N)).left.presheaf.stalk z) :=
    ProjBerk.nativeMultiplicativeGroup_pullback_stalk_isIntegrallyClosed (G ⊗ N).hom
      (ProjBerk.nativeMultiplicativeGroup_pullback_stalk_isIntegrallyClosed (N).hom
        (stalk_isIntegrallyClosed B.left))
  have hu := liftedAction_unit B a ha
  let d := productUnit N ≫ productUnit (G ⊗ N)
  have hd : d ≫ ((G ◁ a) ≫ a) = 𝟙 N := by
    dsimp only [d]
    simp only [Category.assoc]
    rw [← Category.assoc (productUnit (G ⊗ N)), productUnit_naturality]
    simp only [← Category.assoc, hu, Category.id_comp]
  have hd' : d ≫ (((G ◁ a) ≫ a) ≫ normalizationOverProjection B) =
      normalizationOverProjection B := by rw [← Category.assoc, hd, Category.id_comp]
  have : IsDominant
      (d.left ≫ (((G ◁ a) ≫ a) ≫ normalizationOverProjection B).left) := by
    change IsDominant (d ≫ (((G ◁ a) ≫ a) ≫ normalizationOverProjection B)).left
    rw [hd']
    exact ⟨(projection_surjective B.left).denseRange⟩
  let : IsDominant (((G ◁ a) ≫ a) ≫ normalizationOverProjection B).left :=
    IsDominant.of_comp d.left _
  have he := normalized_hom_ext B (G ⊗ (G ⊗ N)) hQ
    ((G ◁ a) ≫ a) ((α_ G G N).inv ≫ (μ[G] ▷ N) ≫ a)
    (liftedAction_mul_projection B a ha).symm
  apply (cancel_epi (α_ G G N).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he.symm

/-- The genuine Laurent-group action on the SAME original generic-field normalization. -/
@[instance_reducible]
def normalizationMultiplicativeModObj [ModObj G B] : ModObj G N where
  smul := (originalAction_lift B).choose
  one_smul := by
    change (η[G] ▷ N) ≫ (originalAction_lift B).choose = (λ_ N).hom
    apply (cancel_epi (λ_ N).inv).1
    simpa only [productUnit, Category.assoc, Iso.inv_hom_id] using
      liftedAction_unit B (originalAction_lift B).choose (originalAction_lift B).choose_spec.1
  mul_smul := liftedAction_mul B (originalAction_lift B).choose
    (originalAction_lift B).choose_spec.1

/-- The original normalization projection is equivariant for the constructed action. -/
theorem normalizationMultiplicativeModObj_projection [ModObj G B] :
    (normalizationMultiplicativeModObj B).smul ≫ Over.homMk (projection B.left) rfl =
      (G ◁ (Over.homMk (projection B.left) rfl : N ⟶ B)) ≫ ModObj.smul (M := G) (X := B) :=
  (originalAction_lift B).choose_spec.1

end EnvelopeProperty.IntegralSchemeNormalization
