/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Whole-open isomorphism from the actual compatible partial inverse

This general separated/reduced-source argument adapts the ordinary proof in
`DeJongAlterations.Geometry.ModificationCenterBirational`, without importing
or assuming an alteration, a modification, or an isomorphism certificate.
It will retain the prescribed noncentral open of genuine common model graphs.

Blueprint: `partial-isomorphism-full-restriction.tex`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace EnvelopeProperty.PartialIsoFullRestriction

universe u

variable {X Y : Scheme.{u}}

/-- The SAME original separated morphism is an isomorphism over the ENTIRE target
open of its genuine compatible dense-open partial isomorphism. -/
theorem isIso_restrict_target (f : Y ⟶ X) [IsReduced Y] [IsSeparated f]
    (e : Y.PartialIso X) (he : e.IsOver f (𝟙 X)) : IsIso (f ∣_ e.target) := by
  have heq : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using he
  have hle : e.source ≤ f ⁻¹ᵁ e.target := by
    intro x hx
    have H := congrArg (fun k : e.source.toScheme ⟶ X => k ⟨x, hx⟩) heq
    have hm := (e.iso.hom ⟨x, hx⟩).2
    change f x ∈ e.target
    simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using H ▸ hm
  let j := Y.homOfLE hle
  have hj : j ≫ f ∣_ e.target = e.iso.hom := by
    apply (cancel_mono e.target.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι, ← heq]
  have hi : e.target.ι = e.iso.inv ≫ e.source.ι ≫ f := by
    rw [← heq, Iso.inv_hom_id_assoc]
  let a : e.target.toScheme ⟶ (f ⁻¹ᵁ e.target).toScheme :=
    (isPullback_morphismRestrict f e.target).lift (𝟙 _) (e.iso.inv ≫ e.source.ι) (by
      simpa only [Category.id_comp, Category.assoc] using hi)
  have ha : a ≫ f ∣_ e.target = 𝟙 _ :=
    (isPullback_morphismRestrict f e.target).lift_fst _ _ _
  have hai : a ≫ (f ⁻¹ᵁ e.target).ι = e.iso.inv ≫ e.source.ι :=
    (isPullback_morphismRestrict f e.target).lift_snd _ _ _
  have hja : e.iso.hom ≫ a = j := by
    apply (cancel_mono (f ⁻¹ᵁ e.target).ι).mp
    rw [Category.assoc, hai, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  have : IsDominant j := AlgebraicGeometry.Opens.isDominant_homOfLE e.dense_source hle
  have hother : (f ∣_ e.target) ≫ a = 𝟙 _ := by
    apply ext_of_isDominant_of_isSeparated (f ∣_ e.target) ?_ j ?_
    · rw [Category.assoc, ha, Category.comp_id, Category.id_comp]
    · rw [← Category.assoc, hj, hja, Category.comp_id]
  exact ⟨⟨a, hother, ha⟩⟩

end EnvelopeProperty.PartialIsoFullRestriction
