/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelMetric
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Actual original line model norms and genuine whole module isomorphisms -/

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

/-- The actual original generic frame is natural in an actual whole
original module isomorphism, with the true valuative/native comparisons. -/
theorem centerFrameGenericIso_natural {M N : X.Modules} (a : M ≅ N)
    (e : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    centerFrameGenericIso hb y ((Scheme.Modules.pullback (centerLift hb y)).mapIso a ≪≫ e) =
      (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).mapIso a ≪≫
        centerFrameGenericIso hb y e := by
  let c : Scheme.Modules.pullback (centerLift hb y) ⋙
      Scheme.Modules.pullback (centerGenericMap y) ≅
      Scheme.Modules.pullback (X.fromSpecResidueField y.1.point) :=
    Scheme.Modules.pullbackComp (centerGenericMap y) (centerLift hb y) ≪≫
      Scheme.Modules.pullbackCongr (centerLift_generic hb y)
  have hc := c.inv.naturality a.hom
  simp only [Functor.comp_map] at hc
  apply Iso.ext
  simp only [centerFrameGenericIso, Functor.mapIso_trans, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  have h := congrArg (fun q => q ≫ (Scheme.Modules.pullback (centerGenericMap y)).map e.hom ≫
    (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom) hc.symm
  simpa only [Category.assoc, c, centerLineGenericIso, Iso.trans_inv,
    NatTrans.comp_app, Iso.app_inv] using h

/-- Every ACTUAL original line-sheaf isomorphism is an isometry on its
WHOLE actual original residue-field pullback generic-line section module. -/
theorem modelLineNorm_mapIso {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (a : M ≅ N) (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM s = modelLineNorm hb y hN
      (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map a.hom).val.app (op ⊤) s) := by
  let e := Classical.choice (exists_centerLineUnitIso hb y hN)
  rw [modelLineNorm_eq_frame hb y hM
    ((Scheme.Modules.pullback (centerLift hb y)).mapIso a ≪≫ e),
    modelLineNorm_eq_frame hb y hN e]
  unfold centerFrameLineNorm centerFrameCoefficient
  rw [centerFrameGenericIso_natural]
  rfl

private theorem centerFrameGenericIso_unit :
    centerFrameGenericIso hb y (Scheme.Modules.pullbackUnitIso (centerLift hb y)) =
      Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point) := by
  apply Iso.ext
  apply (cancel_epi (centerLineGenericIso hb y (Scheme.Modules.unitObj X)).hom).mp
  simp only [centerFrameGenericIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  have hg := ModularCurves.pullbackUnitIso_congr (centerLift_generic hb y)
  have hc := ModularCurves.pullbackUnitIso_compLow (centerGenericMap y) (centerLift hb y)
  change (Scheme.Modules.pullback (centerGenericMap y)).map
      (Scheme.Modules.pullbackUnitIso (centerLift hb y)).hom ≫
      (Scheme.Modules.pullbackUnitIso (centerGenericMap y)).hom =
    (Scheme.Modules.pullbackComp (centerGenericMap y) (centerLift hb y)).hom.app
        (Scheme.Modules.unitObj X) ≫
      (Scheme.Modules.pullbackCongr (centerLift_generic hb y)).hom.app
        (Scheme.Modules.unitObj X) ≫
      (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom
  rw [show (Scheme.Modules.pullbackCongr (centerLift_generic hb y)).hom.app
      (Scheme.Modules.unitObj X) ≫
      (Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom = _ from hg]
  exact hc.symm

/-- The ORIGINAL structure-module line has the ACTUAL residue-field
scalar norm under its genuine native structure-unit pullback comparison. -/
theorem modelLineNorm_unit (s : Γ(genericLineModule y (Scheme.Modules.unitObj X), ⊤)) :
    modelLineNorm hb y (Scheme.Modules.isInvertible_unit (X := X)) s =
      y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
        (((Scheme.Modules.pullbackUnitIso (X.fromSpecResidueField y.1.point)).hom.val.app (op ⊤)).hom s)) := by
  rw [modelLineNorm_eq_frame hb y (Scheme.Modules.isInvertible_unit (X := X))
    (Scheme.Modules.pullbackUnitIso (centerLift hb y))]
  unfold centerFrameLineNorm centerFrameCoefficient
  rw [centerFrameGenericIso_unit]
  rfl

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
