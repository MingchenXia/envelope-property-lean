/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineModelIsometries
import EnvelopeProperty.AlgGeom.CartierTensorPullbackNaturality

/-! # Actual original proper-model line norms respect true tensor products -/

open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance schemeModelTensorMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance schemeModelTensorPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

namespace AlgebraicGeometry.Scheme.Modules
/-- True cover-local invertibility of the original native monoidal tensor,
derived through the ACTUAL coherent-to-explicit tensor comparison. -/
theorem IsInvertible.monoidalTensor {X : Scheme.{u}} {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) : IsInvertible (M ⊗ N) :=
  (hM.tensorObj hN).of_iso (ModularCurves.monoidalTensorObjIso M N)

private theorem modelTensor_pullbackCongr_hom_isMonoidal
    {A B : Scheme.{u}} {g h : A ⟶ B} (he : g = h) :
    (pullbackCongr he).hom.IsMonoidal := by
  subst h
  change NatTrans.IsMonoidal (𝟙 (pullback g))
  infer_instance
end AlgebraicGeometry.Scheme.Modules

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- Genuine ACTUAL original center frame of the ACTUAL original tensor line. -/
def centerTensorFrame {M N : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    centerLineModule hb y (M ⊗ N) ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))) :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback (centerLift hb y)) M N).symm ≪≫
    (e ⊗ᵢ d) ≪≫ ModularCurves.unitObjTensorIso _

/-- The ACTUAL original generic tensor frame is the actual tensor of
original generic frames, with the true original pullback tensorator. -/
theorem centerFrameGenericIso_tensor {M N : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (d : centerLineModule hb y N ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    centerFrameGenericIso hb y (centerTensorFrame hb y e d) =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N).symm ≪≫
        (centerFrameGenericIso hb y e ⊗ᵢ centerFrameGenericIso hb y d) ≪≫
          ModularCurves.unitObjTensorIso _ := by
  let c : Scheme.Modules.pullback (centerLift hb y) ⋙
      Scheme.Modules.pullback (centerGenericMap y) ≅
      Scheme.Modules.pullback (X.fromSpecResidueField y.1.point) :=
    Scheme.Modules.pullbackComp (centerGenericMap y) (centerLift hb y) ≪≫
      Scheme.Modules.pullbackCongr (centerLift_generic hb y)
  have : (Scheme.Modules.pullbackComp (centerGenericMap y) (centerLift hb y)).hom.IsMonoidal :=
    Scheme.Modules.pullbackComp_hom_isMonoidal _ _
  have : (Scheme.Modules.pullbackCongr (centerLift_generic hb y)).hom.IsMonoidal :=
    Scheme.Modules.modelTensor_pullbackCongr_hom_isMonoidal _
  have : c.hom.IsMonoidal := by dsimp only [c, Iso.trans_hom]; infer_instance
  exact (ModularCurves.pullbackComp_tensorTrivialization (centerLift hb y) (centerGenericMap y)
    (X.fromSpecResidueField y.1.point) c M N e d).symm

/-- The TRUE original model norm of the actual native pure generic tensor
section is the product of the model norms on the SAME original line fibers. -/
theorem modelLineNorm_tensor {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (s : Γ(genericLineModule y M, ⊤)) (t : Γ(genericLineModule y N, ⊤)) :
    modelLineNorm hb y (hM.monoidalTensor hN)
      (((Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N).hom.val.app (op ⊤)).hom
        (ModularCurves.tensorSection _ _ ⊤ s t)) =
      modelLineNorm hb y hM s * modelLineNorm hb y hN t := by
  let e := Classical.choice (exists_centerLineUnitIso hb y hM)
  let d := Classical.choice (exists_centerLineUnitIso hb y hN)
  rw [modelLineNorm_eq_frame hb y (hM.monoidalTensor hN) (centerTensorFrame hb y e d),
    modelLineNorm_eq_frame hb y hM e, modelLineNorm_eq_frame hb y hN d]
  unfold centerFrameLineNorm centerFrameCoefficient
  rw [centerFrameGenericIso_tensor]
  have hc : (((Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N).symm ≪≫
        (centerFrameGenericIso hb y e ⊗ᵢ centerFrameGenericIso hb y d) ≪≫
          ModularCurves.unitObjTensorIso _).hom.val.app (op ⊤)).hom
      (((Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N).hom.val.app (op ⊤)).hom
        (ModularCurves.tensorSection _ _ ⊤ s t)) =
      (show Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) from
        (((centerFrameGenericIso hb y e).hom.val.app (op ⊤)).hom s)) *
      (show Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) from
        (((centerFrameGenericIso hb y d).hom.val.app (op ⊤)).hom t)) := by
    have hi := congrArg (fun q => (q.val.app (op ⊤)).hom
      (ModularCurves.tensorSection _ _ ⊤ s t))
      (Iso.hom_inv_id_assoc
        (Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N)
        ((centerFrameGenericIso hb y e ⊗ᵢ centerFrameGenericIso hb y d).hom ≫
          (ModularCurves.unitObjTensorIso _).hom))
    refine hi.trans ?_
    have ht := ModularCurves.tensorSection_map (centerFrameGenericIso hb y e).hom
      (centerFrameGenericIso hb y d).hom ⊤ s t
    exact (congrArg (fun z => (ModularCurves.unitObjTensorIso
      (Spec (CommRingCat.of (X.residueField y.1.point)))).hom.val.app (op ⊤) z) ht).trans
      (ModularCurves.unitObjTensorIso_hom_tensorSection _ ⊤ _ _)
  have hv := congrArg (fun a : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤) =>
    y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom a)) hc
  exact hv.trans ((congrArg y.1.residueVal
    ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom.map_mul _ _)).trans
      (y.1.residueVal.map_mul _ _))

/-- The ACTUAL pure generic section of the original explicit sheafified
tensor, via the TRUE native tensorator and coherent tensor comparison. -/
def genericTensorSection {M N : X.Modules}
    (s : Γ(genericLineModule y M, ⊤)) (t : Γ(genericLineModule y N, ⊤)) :
    Γ(genericLineModule y (Scheme.Modules.tensorObj M N), ⊤) :=
  (((Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).map
      (ModularCurves.monoidalTensorObjIso M N).hom).val.app (op ⊤)).hom
    (((Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N).hom.val.app (op ⊤)).hom
      (ModularCurves.tensorSection _ _ ⊤ s t))

/-- The ACTUAL original explicit sheafified pure tensor section has
genuine model norm the product of the SAME original factor norms. -/
theorem modelLineNorm_genericTensorSection {M N : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (hN : Scheme.Modules.IsInvertible N)
    (s : Γ(genericLineModule y M, ⊤)) (t : Γ(genericLineModule y N, ⊤)) :
    modelLineNorm hb y (hM.tensorObj hN) (genericTensorSection y s t) =
      modelLineNorm hb y hM s * modelLineNorm hb y hN t := by
  have h := modelLineNorm_mapIso hb y (hM.monoidalTensor hN) (hM.tensorObj hN)
    (ModularCurves.monoidalTensorObjIso M N)
    (((Functor.Monoidal.μIso (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)) M N).hom.val.app (op ⊤)).hom
      (ModularCurves.tensorSection _ _ ⊤ s t))
  exact h.symm.trans (modelLineNorm_tensor hb y hM hN s t)

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
