/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelHomNorms

/-! # Actual whole original model morphism norms and composition -/

open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- ACTUAL whole original model-line composition multiplies the
GENUINE original morphism norms on the SAME original generic fiber. -/
theorem modelHomNorm_comp {M N P : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (hP : Scheme.Modules.IsInvertible P) (α : M ⟶ N) (β : N ⟶ P) :
    modelHomNorm hb y hM hP (α ≫ β) =
      modelHomNorm hb y hM hN α * modelHomNorm hb y hN hP β := by
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  have hc := modelLineNorm_mapHom_eq hb y hM hP (α ≫ β) s
  have hα := modelLineNorm_mapHom_eq hb y hM hN α s
  have hβ := modelLineNorm_mapHom_eq hb y hN hP β
    (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤) s)
  rw [hs, mul_one] at hc hα
  rw [hα] at hβ
  have he : modelLineNorm hb y hP
      (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map (α ≫ β)).val.app (op ⊤) s) =
    modelLineNorm hb y hP
      (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map β).val.app (op ⊤)
        (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤) s)) := by
    rw [Functor.map_comp]
    rfl
  exact hc.symm.trans (he.trans (hβ.trans (mul_comm _ _)))

/-- The ACTUAL original identity has genuine model morphism norm one. -/
theorem modelHomNorm_id {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    modelHomNorm hb y hM hM (𝟙 M) = 1 := by
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  have h := modelLineNorm_mapHom_eq hb y hM hM (𝟙 M) s
  rw [(Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map_id] at h
  change modelLineNorm hb y hM s = modelHomNorm hb y hM hM (𝟙 M) * modelLineNorm hb y hM s at h
  rw [hs, mul_one] at h
  exact h.symm

/-- EVERY ACTUAL whole original line-module isomorphism has genuine
model morphism norm one, derived from its true original fiber isometry. -/
theorem modelHomNorm_iso {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (e : M ≅ N) :
    modelHomNorm hb y hM hN e.hom = 1 := by
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  have h := modelLineNorm_mapHom_eq hb y hM hN e.hom s
  rw [← modelLineNorm_mapIso hb y hM hN e s, hs, mul_one] at h
  exact h.symm

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
