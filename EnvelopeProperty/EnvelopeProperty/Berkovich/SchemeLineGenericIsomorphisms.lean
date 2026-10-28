/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.CartierModelInclusionNorm

/-! # Actual model-morphism norms detect entire original generic line isomorphisms -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- Nonzero ACTUAL original model norm produces a true WHOLE original
residue-field line isomorphism for the actual pulled module morphism. -/
theorem isIso_genericMap_of_modelHomNorm_ne_zero {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (hn : modelHomNorm hb y hM hN α ≠ 0) :
    IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α) := by
  let e := Classical.choice (exists_centerLineUnitIso hb y hM)
  let d := Classical.choice (exists_centerLineUnitIso hb y hN)
  let a : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) :=
    (centerGenericMap y).appTop.hom (centerHomCoefficient hb y α e d)
  let q := Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))
  have ha : q.hom.hom a = algebraMap (CenterRing y) (X.residueField y.1.point)
      ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom
        (centerHomCoefficient hb y α e d)) :=
    congrArg (fun z => z.hom (centerHomCoefficient hb y α e d))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
        (algebraMap (CenterRing y) (X.residueField y.1.point))))
  have hv : y.1.residueVal (q.hom.hom a) ≠ 0 := by
    rwa [ha, ← modelHomNorm_eq_frames hb y hM hN α e d]
  have hK : IsUnit (q.hom.hom a) := isUnit_iff_ne_zero.mpr (y.1.residueVal.zero_iff.not.mp hv)
  have hΓ : IsUnit a := by
    have h := hK.map q.inv.hom
    have he : q.inv.hom (q.hom.hom a) = a :=
      congrArg (fun z => z.hom a) q.hom_inv_id
    rwa [he] at h
  obtain ⟨u, hu⟩ := hΓ
  have hs : IsIso (ModularCurves.unitEndomorphismOfTopSection a) := by
    rw [← hu, ← ModularCurves.unitAutomorphismOfTopUnit_hom]
    infer_instance
  have hc := centerFrameGenericIso_mapHom hb y α e d
  have ht : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α ≫
      (centerFrameGenericIso hb y d).hom) := by
    rw [hc]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp ht

/-- True WHOLE original generic line isomorphisms have nonzero genuine
model-morphism norm, proved using an ACTUAL norm-one original section. -/
theorem modelHomNorm_ne_zero_of_isIso_genericMap {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (hα : IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α)) :
    modelHomNorm hb y hM hN α ≠ 0 := by
  let := hα
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  intro hn
  have hz := modelLineNorm_mapHom_eq hb y hM hN α s
  rw [hn, zero_mul] at hz
  have himage := (modelLineNorm_eq_zero_iff hb y hN _).mp hz
  have : IsIso (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤)) :=
    inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op ⊤)).map
      ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α)))
  have hsz : s = 0 := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤))).1
      (himage.trans (map_zero _).symm)
  rw [hsz, (modelLineNorm_eq_zero_iff hb y hM 0).mpr rfl] at hs
  exact zero_ne_one hs

/-- Nonzero original model norm is EQUIVALENT to actual WHOLE original
residue-field isomorphy, without an extra generic trivialization certificate. -/
theorem modelHomNorm_ne_zero_iff_isIso_genericMap {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N) :
    modelHomNorm hb y hM hN α ≠ 0 ↔
      IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α) :=
  ⟨isIso_genericMap_of_modelHomNorm_ne_zero hb y hM hN α,
    modelHomNorm_ne_zero_of_isIso_genericMap hb y hM hN α⟩

/-- The intrinsic ACTUAL ideal norm detects isomorphy of the ENTIRE
original Cartier inclusion on the SAME original residue-field line. -/
theorem modelIdealNorm_ne_zero_iff_isIso_genericInclusion
    (I : X.IdealSheafData) (hI : I.IsInvertible) :
    modelIdealNorm I hb y ≠ 0 ↔
      IsIso ((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map I.toModulesInclusion) := by
  rw [← modelHomNorm_idealInclusion I hI hb y, ENNReal.coe_ne_zero]
  exact modelHomNorm_ne_zero_iff_isIso_genericMap hb y hI.isInvertibleModule_toModules
    (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
