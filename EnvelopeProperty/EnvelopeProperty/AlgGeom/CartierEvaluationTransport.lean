/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierDualEvaluation
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-! # Actual pulled evaluation and its canonical dual transport -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  symmetricCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Modules.pullback f).Monoidal := pullbackMonoidal f
variable {X Y : Scheme.{u}} {M : Y.Modules}

/-- Pull the ORIGINAL canonical evaluation, with the TRUE tensor and unit
comparisons of the actual module pullback. -/
def IsInvertible.pulledEvaluationIso (hM : IsInvertible M) (f : X ⟶ Y) :
    (Modules.pullback f).obj M ⊗ (Modules.pullback f).obj (dualObj M) ≅ 𝟙_ X.Modules :=
  Functor.Monoidal.μIso (Modules.pullback f) M (dualObj M) ≪≫
    (Modules.pullback f).mapIso hM.monoidalEvaluationIso ≪≫
    (Functor.Monoidal.εIso (Modules.pullback f)).symm

private def tensorLeftFullyFaithful (hM : IsInvertible M) :
    (tensorLeft M).FullyFaithful :=
  hM.tensorRightFullyFaithful.ofIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

/-- Canonical actual pulled-dual transport uniquely preserves the ORIGINAL
pulled evaluations. It is constructed from actual invertibility. -/
def IsInvertible.evaluationDualTransportIso (hM : IsInvertible M)
    (f g : X ⟶ Y) (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M) :
    (Modules.pullback f).obj (dualObj M) ≅ (Modules.pullback g).obj (dualObj M) :=
  (tensorLeftFullyFaithful (hM.pullback g)).preimageIso
    ((e.symm ⊗ᵢ Iso.refl _) ≪≫ hM.pulledEvaluationIso f ≪≫
      (hM.pulledEvaluationIso g).symm)

/-- The exact genuine evaluation identity for the actual constructed map. -/
theorem IsInvertible.evaluationDualTransportIso_pairing (hM : IsInvertible M)
    (f g : X ⟶ Y) (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M) :
    (Modules.pullback g).obj M ◁ (hM.evaluationDualTransportIso f g e).hom ≫
        (hM.pulledEvaluationIso g).hom =
      e.inv ▷ (Modules.pullback f).obj (dualObj M) ≫ (hM.pulledEvaluationIso f).hom := by
  have h := (tensorLeftFullyFaithful (hM.pullback g)).map_preimage
    (((e.symm ⊗ᵢ Iso.refl _) ≪≫ hM.pulledEvaluationIso f ≪≫
      (hM.pulledEvaluationIso g).symm).hom)
  change (Modules.pullback g).obj M ◁ (hM.evaluationDualTransportIso f g e).hom = _ at h
  rw [h]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    tensorHom_id, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original factor map and its true canonical dual transport preserve
actual pulled evaluation together on the whole sheaf. -/
theorem IsInvertible.evaluationDualTransportIso_balanced (hM : IsInvertible M)
    (f g : X ⟶ Y)
    (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M) :
    (e.hom ⊗ₘ (hM.evaluationDualTransportIso f g e).hom) ≫
        (hM.pulledEvaluationIso g).hom = (hM.pulledEvaluationIso f).hom := by
  rw [tensorHom_def, Category.assoc, hM.evaluationDualTransportIso_pairing f g e]
  rw [← Category.assoc, ← comp_whiskerRight]
  simp only [Iso.hom_inv_id, id_whiskerRight, Category.id_comp]

/-- Actual evaluation characterizes the original transport among ALL
morphisms of the original pulled dual sheaves. -/
theorem IsInvertible.evaluationDualTransportIso_unique (hM : IsInvertible M)
    (f g : X ⟶ Y) (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (q : (Modules.pullback f).obj (dualObj M) ⟶ (Modules.pullback g).obj (dualObj M))
    (hq : (Modules.pullback g).obj M ◁ q ≫ (hM.pulledEvaluationIso g).hom =
      e.inv ▷ (Modules.pullback f).obj (dualObj M) ≫ (hM.pulledEvaluationIso f).hom) :
    q = (hM.evaluationDualTransportIso f g e).hom := by
  apply (tensorLeftFullyFaithful (hM.pullback g)).map_injective
  apply (cancel_mono (hM.pulledEvaluationIso g).hom).mp
  exact hq.trans (hM.evaluationDualTransportIso_pairing f g e).symm

/-- The genuine identity original factor map gives the original identity
on the entire actual pulled dual sheaf. -/
theorem IsInvertible.evaluationDualTransportIso_refl (hM : IsInvertible M)
    (f : X ⟶ Y) :
    hM.evaluationDualTransportIso f f (Iso.refl _) = Iso.refl _ := by
  apply Iso.ext
  symm
  apply hM.evaluationDualTransportIso_unique f f (Iso.refl _)
  simp only [Iso.refl_inv, Iso.refl_hom, whiskerLeft_id, id_whiskerRight, Category.id_comp]

/-- Genuine same-source canonical dual transport respects actual factor
composition, with no supplied coherence certificate. -/
theorem IsInvertible.evaluationDualTransportIso_trans (hM : IsInvertible M)
    (f g h : X ⟶ Y) (e : (Modules.pullback f).obj M ≅ (Modules.pullback g).obj M)
    (e' : (Modules.pullback g).obj M ≅ (Modules.pullback h).obj M) :
    hM.evaluationDualTransportIso f g e ≪≫ hM.evaluationDualTransportIso g h e' =
      hM.evaluationDualTransportIso f h (e ≪≫ e') := by
  apply Iso.ext
  apply hM.evaluationDualTransportIso_unique f h (e ≪≫ e')
  rw [Iso.trans_hom, whiskerLeft_comp, Category.assoc,
    hM.evaluationDualTransportIso_pairing g h e']
  rw [← Category.assoc, whisker_exchange,
    Category.assoc, hM.evaluationDualTransportIso_pairing f g e]
  simp only [Iso.trans_inv, comp_whiskerRight, Category.assoc]

end AlgebraicGeometry.Scheme.Modules
