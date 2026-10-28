/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelIsometries

/-! # Actual original line morphisms scale genuine proper-model norms -/

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

/-- Actual original valuation-ring scalar of a WHOLE original module
morphism in genuine entire original valuative frames. -/
def centerHomCoefficient {M N : X.Modules} (α : M ⟶ N)
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    Γ(Spec (CommRingCat.of (CenterRing y)), ⊤) :=
  ((e.inv ≫ (Scheme.Modules.pullback (centerLift hb y)).map α ≫ d.hom).val.app (op ⊤)).hom
    (1 : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))

/-- EVERY actual original whole module morphism is literal scalar
multiplication in its original generic frames by its actual center scalar. -/
theorem centerFrameGenericIso_mapHom {M N : X.Modules} (α : M ⟶ N)
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α ≫
        (centerFrameGenericIso hb y d).hom =
      (centerFrameGenericIso hb y e).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          ((centerGenericMap y).appTop.hom (centerHomCoefficient hb y α e d)) := by
  let r := centerHomCoefficient hb y α e d
  have he : (Scheme.Modules.pullback (centerLift hb y)).map α ≫ d.hom =
      e.hom ≫ ModularCurves.unitEndomorphismOfTopSection r := by
    have h := Scheme.Modules.unitHom_eq_globalScalar
      (e.inv ≫ (Scheme.Modules.pullback (centerLift hb y)).map α ≫ d.hom)
    change e.inv ≫ (Scheme.Modules.pullback (centerLift hb y)).map α ≫ d.hom =
      ModularCurves.unitEndomorphismOfTopSection r at h
    have h' := congrArg (fun q => e.hom ≫ q) h
    simpa only [Iso.hom_inv_id_assoc] using h'
  let c : Scheme.Modules.pullback (centerLift hb y) ⋙
      Scheme.Modules.pullback (centerGenericMap y) ≅
      Scheme.Modules.pullback (X.fromSpecResidueField y.1.point) :=
    Scheme.Modules.pullbackComp (centerGenericMap y) (centerLift hb y) ≪≫
      Scheme.Modules.pullbackCongr (centerLift_generic hb y)
  have hnat := c.inv.naturality α
  simp only [Functor.comp_map] at hnat
  have hgen : (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α ≫
        (centerLineGenericIso hb y N).inv ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map d.hom ≫
        (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom =
      (centerLineGenericIso hb y M).inv ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map
          ((Scheme.Modules.pullback (centerLift hb y)).map α) ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map d.hom ≫
        (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom := by
    have h := congrArg (fun q => q ≫ (Scheme.Modules.pullback (centerGenericMap y)).map d.hom ≫
      (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom) hnat
    simpa only [Category.assoc, c, centerLineGenericIso, Iso.trans_inv,
      NatTrans.comp_app, Iso.app_inv] using h
  have hsc : (Scheme.Modules.pullback (centerGenericMap y)).map
        (ModularCurves.unitEndomorphismOfTopSection r) ≫
        (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom =
      (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom ≫
        ModularCurves.unitEndomorphismOfTopSection ((centerGenericMap y).appTop.hom r) := by
    have h := congrArg (fun q => (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom ≫ q)
      (ModularCurves.pullback_unitEndomorphismOfTopSection (centerGenericMap y) r)
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  simp only [centerFrameGenericIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  calc
    _ = (centerLineGenericIso hb y M).inv ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map
          ((Scheme.Modules.pullback (centerLift hb y)).map α) ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map d.hom ≫
        (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom := hgen
    _ = (centerLineGenericIso hb y M).inv ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map
          ((Scheme.Modules.pullback (centerLift hb y)).map α ≫ d.hom) ≫
        (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
    _ = (centerLineGenericIso hb y M).inv ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map e.hom ≫
        (Scheme.Modules.pullback (centerGenericMap y)).map
          (ModularCurves.unitEndomorphismOfTopSection r) ≫
        (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom := by
      rw [he, Functor.map_comp]
      simp only [Category.assoc]
    _ = _ := by rw [hsc]

/-- EVERY genuine original whole line morphism scales the TRUE actual
model norms by its derived original valuation-ring coefficient, including zero. -/
theorem modelLineNorm_mapHom {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hN
        (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤) s) =
      y.1.residueVal (algebraMap (CenterRing y) (X.residueField y.1.point)
        ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (centerHomCoefficient hb y α e d))) *
        modelLineNorm hb y hM s := by
  have hframe := centerFrameGenericIso_mapHom hb y α e d
  let a : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) :=
    (centerGenericMap y).appTop.hom (centerHomCoefficient hb y α e d)
  have hc : centerFrameCoefficient hb y d
      (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤) s) =
      centerFrameCoefficient hb y e s *
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a := by
    unfold centerFrameCoefficient
    change (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
      (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α ≫
        (centerFrameGenericIso hb y d).hom).val.app (op ⊤) s) = _
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
        ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (centerHomCoefficient hb y α e d)) := by
    exact congrArg (fun q => q.hom (centerHomCoefficient hb y α e d))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
        (algebraMap (CenterRing y) (X.residueField y.1.point))))
  rw [modelLineNorm_eq_frame hb y hM e, modelLineNorm_eq_frame hb y hN d]
  unfold centerFrameLineNorm
  rw [hc, map_mul, hn, mul_comm]

/-- The WHOLE actual original generic line has an actual section of
model norm one, derived from an actual valuative frame rather than assumed. -/
theorem exists_modelLineNorm_eq_one {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ s : Γ(genericLineModule y M, ⊤), modelLineNorm hb y hM s = 1 := by
  let e := Classical.choice (exists_centerLineUnitIso hb y hM)
  let E := centerFrameGenericIso hb y e
  let s : Γ(genericLineModule y M, ⊤) :=
    (E.inv.val.app (op ⊤)).hom
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))
  refine ⟨s, ?_⟩
  rw [modelLineNorm_eq_frame hb y hM e]
  unfold centerFrameLineNorm centerFrameCoefficient
  have hE : (E.hom.val.app (op ⊤)).hom s =
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤)) := by
    have h := congrArg (fun q => q.val.app (op ⊤)
      (1 : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))) E.inv_hom_id
    exact h
  rw [show ((centerFrameGenericIso hb y e).hom.val.app (op ⊤)).hom s = _ from hE,
    map_one, map_one]

/-- The actual ORIGINAL morphism coefficient norm is independent of
BOTH original valuative frames, proved by an actual norm-one generic section. -/
theorem centerHomCoefficient_norm_independent {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (e e' : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d d' : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    y.1.residueVal (algebraMap (CenterRing y) (X.residueField y.1.point)
        ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (centerHomCoefficient hb y α e d))) =
      y.1.residueVal (algebraMap (CenterRing y) (X.residueField y.1.point)
        ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (centerHomCoefficient hb y α e' d'))) := by
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  have h := modelLineNorm_mapHom hb y hM hN α e d s
  have h' := modelLineNorm_mapHom hb y hM hN α e' d' s
  rw [hs, mul_one] at h h'
  exact h.symm.trans h'

/-- Genuine frame-free norm of an ACTUAL whole original line-module
morphism, derived on the ACTUAL original proper-center valuation ring. -/
def modelHomNorm {M N : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N) : ℝ≥0 :=
  y.1.residueVal (algebraMap (CenterRing y) (X.residueField y.1.point)
    ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom
      (centerHomCoefficient hb y α (Classical.choice (exists_centerLineUnitIso hb y hM))
        (Classical.choice (exists_centerLineUnitIso hb y hN)))))

/-- Every pair of ACTUAL original center frames computes the SAME
genuine original model-morphism norm. -/
theorem modelHomNorm_eq_frames {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    modelHomNorm hb y hM hN α =
      y.1.residueVal (algebraMap (CenterRing y) (X.residueField y.1.point)
        ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom (centerHomCoefficient hb y α e d))) :=
  centerHomCoefficient_norm_independent hb y hM hN α _ e _ d

/-- The original generic map scales the actual model-line norm by the
GENUINE frame-free original model norm of that actual original morphism. -/
theorem modelLineNorm_mapHom_eq {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hN
        (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤) s) =
      modelHomNorm hb y hM hN α * modelLineNorm hb y hM s :=
  modelLineNorm_mapHom hb y hM hN α _ _ s

/-- Every actual ORIGINAL model morphism has norm at most one, because
its derived true coefficient lies in the actual ORIGINAL valuation ring. -/
theorem modelHomNorm_le_one {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N) :
    modelHomNorm hb y hM hN α ≤ 1 :=
  (Valuation.valuationSubring.integers y.1.residueVal).map_le_one _

/-- Every ACTUAL whole original model-line morphism contracts the genuine
model norms on the ENTIRE actual original generic-line section module. -/
theorem modelLineNorm_mapHom_le {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N) (α : M ⟶ N)
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hN
        (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map α).val.app (op ⊤) s) ≤
      modelLineNorm hb y hM s := by
  rw [modelLineNorm_mapHom_eq hb y hM hN α s]
  exact (mul_le_mul_of_nonneg_right (modelHomNorm_le_one hb y hM hN α) zero_le).trans_eq (one_mul _)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
