/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelTensorNorms
import EnvelopeProperty.Berkovich.SchemeLineModelHomComposition

/-! # True whole original tensor morphisms multiply actual model norms -/

open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance schemeModelTensorHomMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance schemeModelTensorHomPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

namespace AlgebraicGeometry.Scheme.Modules
private theorem tensorHom_genericSection_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M M' N N' : Y.Modules} (α : M ⟶ M') (β : N ⟶ N')
    (s : Γ((pullback f).obj M, ⊤)) (t : Γ((pullback f).obj N, ⊤)) :
    (((pullback f).map (α ⊗ₘ β)).val.app (op ⊤)).hom
      (((Functor.Monoidal.μIso (pullback f) M N).hom.val.app (op ⊤)).hom
        (ModularCurves.tensorSection _ _ ⊤ s t)) =
      ((Functor.Monoidal.μIso (pullback f) M' N').hom.val.app (op ⊤)).hom
        (ModularCurves.tensorSection _ _ ⊤
          ((((pullback f).map α).val.app (op ⊤)).hom s)
          ((((pullback f).map β).val.app (op ⊤)).hom t)) := by
  have hm := congrArg (fun q => (q.val.app (op ⊤)).hom
    (ModularCurves.tensorSection _ _ ⊤ s t))
    (Functor.LaxMonoidal.μ_natural (pullback f) α β)
  have ht := ModularCurves.tensorSection_map ((pullback f).map α) ((pullback f).map β) ⊤ s t
  exact hm.symm.trans (congrArg
    (fun z => ((Functor.Monoidal.μIso (pullback f) M' N').hom.val.app (op ⊤)).hom z) ht)
end AlgebraicGeometry.Scheme.Modules

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- The TRUE original tensor of whole model-line morphisms has genuine
model norm the product of their ACTUAL original model morphism norms. -/
theorem modelHomNorm_tensorHom {M M' N N' : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (hN : Scheme.Modules.IsInvertible N) (hN' : Scheme.Modules.IsInvertible N')
    (α : M ⟶ M') (β : N ⟶ N') :
    modelHomNorm hb y (hM.monoidalTensor hN) (hM'.monoidalTensor hN') (α ⊗ₘ β) =
      modelHomNorm hb y hM hM' α * modelHomNorm hb y hN hN' β := by
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  obtain ⟨t, ht⟩ := exists_modelLineNorm_eq_one hb y hN
  let st := ((Functor.Monoidal.μIso (Scheme.Modules.pullback
      (X.fromSpecResidueField y.1.point)) M N).hom.val.app (op ⊤)).hom
        (ModularCurves.tensorSection _ _ ⊤ s t)
  have hst : modelLineNorm hb y (hM.monoidalTensor hN) st = 1 := by
    exact (modelLineNorm_tensor hb y hM hN s t).trans (by rw [hs, ht, one_mul])
  have h := modelLineNorm_mapHom_eq hb y (hM.monoidalTensor hN)
    (hM'.monoidalTensor hN') (α ⊗ₘ β) st
  rw [hst, mul_one] at h
  have hm := Scheme.Modules.tensorHom_genericSection_map (X.fromSpecResidueField y.1.point) α β s t
  have hα := modelLineNorm_mapHom_eq hb y hM hM' α s
  have hβ := modelLineNorm_mapHom_eq hb y hN hN' β t
  rw [hs, mul_one] at hα
  rw [ht, mul_one] at hβ
  have hp := modelLineNorm_tensor hb y hM' hN'
    ((((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤)).hom s)
    ((((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map β).val.app (op ⊤)).hom t)
  rw [hα, hβ] at hp
  exact h.symm.trans ((congrArg (modelLineNorm hb y (hM'.monoidalTensor hN')) hm).trans hp)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
