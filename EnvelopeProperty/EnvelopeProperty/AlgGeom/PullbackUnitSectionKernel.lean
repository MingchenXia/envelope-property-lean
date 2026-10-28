import EnvelopeProperty.AlgGeom.FlatSectionKernel
import EnvelopeProperty.Berkovich.SchemeFramedSectionFactor

/-! # The SAME original unit morphism and its entire actual pulled affine section kernel -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section
universe u

namespace EnvelopeProperty.PullbackUnitSectionKernel

/-- The actual pullback-unit section of the original value at one is the value
at one of the SAME original morphism pulled through the canonical unit-object comparison. -/
theorem affinePullbackUnitTop_sectionAtOne {Y W : Scheme.{u}} (c : W ⟶ Y)
    {N : Y.Modules} (δ : Scheme.Modules.unitObj Y ⟶ N) :
    Scheme.Modules.affinePullbackUnitTop c N
      (δ.val.app (.op ⊤) (1 : Γ(Y, ⊤))) =
    ((Scheme.Modules.pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map δ).val.app
      (.op ⊤) (1 : Γ(W, ⊤)) := by
  let e := Scheme.Modules.pullbackUnitIso c
  let a := Scheme.Modules.affinePullbackUnitTop c (Scheme.Modules.unitObj Y) (1 : Γ(Y, ⊤))
  have hn := Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_naturality c δ
    (1 : Γ(Y, ⊤))
  have hu : e.hom.app ⊤ a = (1 : Γ(W, ⊤)) := by
    simpa only [map_one] using
      Berkovich.SchemeFramedSectionFactor.affinePullbackUnitTop_unit c (1 : Γ(Y, ⊤))
  have hc : e.inv.app ⊤ (e.hom.app ⊤ a) = a := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun k => k.app (⊤ : W.Opens)) e.hom_inv_id) a
    simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
      ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
  have ha : a = e.inv.app ⊤ (1 : Γ(W, ⊤)) :=
    hc.symm.trans (congrArg (fun z => e.inv.app ⊤ z) hu)
  change _ = ((Scheme.Modules.pullback c).map δ).app ⊤ (e.inv.app ⊤ (1 : Γ(W, ⊤)))
  exact hn.trans (congrArg (fun z => ((Scheme.Modules.pullback c).map δ).app ⊤ z) ha)

/-- EVERY original affine scalar belongs to the intrinsic actual pulled section
kernel exactly when the SAME actual pulled unit morphism kills its canonical section. -/
theorem mem_sectionKernel_iff_pulledUnitHom {Y : Scheme.{u}} (B : CommRingCat.{u})
    (c : Spec B ⟶ Y) {N : Y.Modules} (δ : Scheme.Modules.unitObj Y ⟶ N) (b : B) :
    b ∈ FlatSectionKernel.sectionKernel (R := B) (𝟙 (Spec B))
      ((Scheme.Modules.pullback c).obj N)
      (Scheme.Modules.affinePullbackUnitTop c N
        (δ.val.app (.op ⊤) (1 : Γ(Y, ⊤)))) ↔
    ((Scheme.Modules.pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map δ).val.app
      (.op ⊤) ((Scheme.ΓSpecIso B).inv.hom b) = 0 := by
  rw [FlatSectionKernel.mem_sectionKernel_iff, affinePullbackUnitTop_sectionAtOne c δ]
  let α := (Scheme.Modules.pullbackUnitIso c).inv ≫ (Scheme.Modules.pullback c).map δ
  have hc : ProperBirationalSections.coefficientMap (𝟙 (Spec B)) b =
      (Scheme.ΓSpecIso B).inv.hom b := by
    simp [ProperBirationalSections.coefficientMap]
  rw [hc]
  have h := (α.val.app (.op ⊤)).hom.map_smul ((Scheme.ΓSpecIso B).inv.hom b)
    (1 : Γ(Spec B, ⊤))
  simpa only [smul_eq_mul, mul_one] using (Iff.of_eq (congrArg (fun w => w = 0) h)).symm

end EnvelopeProperty.PullbackUnitSectionKernel
