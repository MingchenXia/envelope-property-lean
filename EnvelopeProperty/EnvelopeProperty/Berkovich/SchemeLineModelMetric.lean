/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelNorm
import EnvelopeProperty.AlgGeom.UnitModuleAutomorphisms

/-! # Frame independence of the actual original proper-model line norm -/

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

private theorem centerFrameGenericIso_scalar {M : X.Modules}
    (e e' : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤)ˣ)
    (he : e' = e ≪≫ ModularCurves.unitAutomorphismOfTopUnit u) :
    (centerFrameGenericIso hb y e').hom =
      (centerFrameGenericIso hb y e).hom ≫
        ModularCurves.unitEndomorphismOfTopSection ((centerGenericMap y).appTop.hom (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))) := by
  have hsc : (Scheme.Modules.pullback (centerGenericMap y)).map
        (ModularCurves.unitEndomorphismOfTopSection (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))) ≫
      (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom =
    (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom ≫
      ModularCurves.unitEndomorphismOfTopSection ((centerGenericMap y).appTop.hom (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))) := by
    have h := congrArg (fun q => (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom ≫ q)
      (ModularCurves.pullback_unitEndomorphismOfTopSection (centerGenericMap y) (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤)))
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  rw [he]
  simp only [centerFrameGenericIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    ModularCurves.unitAutomorphismOfTopUnit_hom, Category.assoc]
  rw [hsc]

/-- The ACTUAL original generic-line norm is independent of EVERY actual
original valuative frame, using actual unit scalars and actual valuation bounds. -/
theorem centerFrameLineNorm_independent {M : X.Modules}
    (e e' : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s : Γ(genericLineModule y M, ⊤)) :
    centerFrameLineNorm hb y e s = centerFrameLineNorm hb y e' s := by
  obtain ⟨u, hu⟩ := Scheme.Modules.unitIso_eq_globalUnit (e.symm ≪≫ e')
  have he : e' = e ≪≫ ModularCurves.unitAutomorphismOfTopUnit u := by
    have h := congrArg (fun q => e ≪≫ q) hu
    simpa only [Iso.self_symm_id_assoc] using h
  have hframe := centerFrameGenericIso_scalar hb y e e' u he
  let a : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) :=
    (centerGenericMap y).appTop.hom (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))
  have hc : centerFrameCoefficient hb y e' s =
      centerFrameCoefficient hb y e s *
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a := by
    unfold centerFrameCoefficient
    rw [hframe]
    change (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
      ((ModularCurves.unitEndomorphismOfTopSection a).val.app (op ⊤)
        (((centerFrameGenericIso hb y e).hom.val.app (op ⊤)).hom s)) = _
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    simp only [homOfLE_refl, op_id, map_mul]
    rw [(Spec (CommRingCat.of (X.residueField y.1.point))).presheaf.map_id]
    rfl
  have hn : (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a =
      algebraMap (CenterRing y) (X.residueField y.1.point)
        ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))) := by
    have h := congrArg (fun q => q.hom (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤)))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
        (algebraMap (CenterRing y) (X.residueField y.1.point))))
    exact h
  have hunit : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (u : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))) :=
    u.isUnit.map _
  have hv : y.1.residueVal
      ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a) = 1 := by
    rw [hn]
    exact (Valuation.valuationSubring.integers y.1.residueVal).one_of_isUnit hunit
  unfold centerFrameLineNorm
  rw [hc, map_mul, hv, mul_one]

/-- The actual ORIGINAL proper-model norm on the WHOLE original residue-
field generic-line section module, constructed from a derived valuative frame. -/
def modelLineNorm {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : Γ(genericLineModule y M, ⊤)) : ℝ≥0 :=
  centerFrameLineNorm hb y (Classical.choice (exists_centerLineUnitIso hb y hM)) s

/-- Any actual original valuative frame computes the SAME actual model norm. -/
theorem modelLineNorm_eq_frame {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM s = centerFrameLineNorm hb y e s :=
  centerFrameLineNorm_independent hb y _ e s

/-- The actual original model norm detects precisely the original zero section. -/
theorem modelLineNorm_eq_zero_iff {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM s = 0 ↔ s = 0 :=
  centerFrameLineNorm_eq_zero_iff hb y _ s

/-- The true original model-line norm satisfies the genuine nonarchimedean inequality. -/
theorem modelLineNorm_add_le_max {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s t : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM (s + t) ≤ max (modelLineNorm hb y hM s) (modelLineNorm hb y hM t) :=
  centerFrameLineNorm_add_le_max hb y _ s t

/-- Actual scalar multiplication scales the original model norm by the
actual original residue-field valuation. -/
theorem modelLineNorm_smul {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (r : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM (r • s) =
      y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom r) *
        modelLineNorm hb y hM s :=
  centerFrameLineNorm_smul hb y _ r s

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
