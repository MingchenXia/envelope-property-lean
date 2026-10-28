/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierInvariantLinearization
import EnvelopeProperty.AlgGeom.CartierTensorDualFunctorial
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.Picard.DualPullback.Iso
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Canonical whole pullback of the genuine Cartier tensor-dual ratio -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}}

/-- Canonical whole pullback of the actual explicit sheafified tensor,
using the genuine coherent monoidal tensor and canonical native tensorator. -/
def canonicalTensorPullbackIso (f : X ⟶ Y) (M N : Y.Modules) :
    (pullback f).obj (tensorObj M N) ≅
      tensorObj ((pullback f).obj M) ((pullback f).obj N) := by
  let := monoidalCategory X
  let := monoidalCategory Y
  let := pullbackMonoidal f
  exact (pullback f).mapIso (ModularCurves.monoidalTensorObjIso M N).symm ≪≫
    (Functor.Monoidal.μIso (pullback f) M N).symm ≪≫
      ModularCurves.monoidalTensorObjIso ((pullback f).obj M) ((pullback f).obj N)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- The actual canonical ratio pullback comparison uses the true sheaf dual
and true tensor pullback, without choosing an arbitrary tensor isomorphism. -/
def ratioPullbackIso (I J : Y.IdealSheafData) (hJ : J.IsInvertible) (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (I.ratioModule J) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj I.toModules)
        (Scheme.Modules.dualObj ((Scheme.Modules.pullback f).obj J.toModules)) :=
  Scheme.Modules.canonicalTensorPullbackIso f I.toModules (Scheme.Modules.dualObj J.toModules) ≪≫
    Scheme.Modules.tensorObjCongr (Iso.refl _)
      (Scheme.Modules.dualPullbackIsoOfIsInvertible f J.toModules hJ.isInvertibleModule_toModules)

/-- Two true whole invariant Cartier pullbacks construct the canonical
actual tensor-dual ratio comparison along the original flat morphisms. -/
def IsInvertible.invariantRatioModuleIso {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (f g : X ⟶ Y) [Flat f] [Flat g]
    (hIfg : I.comap f = I.comap g) (hJfg : J.comap f = J.comap g) :
    (Scheme.Modules.pullback f).obj (I.ratioModule J) ≅
      (Scheme.Modules.pullback g).obj (I.ratioModule J) :=
  I.ratioPullbackIso J hJ f ≪≫
    Scheme.Modules.tensorObjCongr (hI.invariantModuleIso f g hIfg)
      (Scheme.Modules.dualIsoObj (hJ.invariantModuleIso f g hJfg).symm) ≪≫
    (I.ratioPullbackIso J hJ g).symm


/-- The actual canonical tensor-dual ratio comparison has the true identity law. -/
theorem IsInvertible.invariantRatioModuleIso_refl {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (f : X ⟶ Y) [Flat f] :
    hI.invariantRatioModuleIso hJ f f rfl rfl = Iso.refl _ := by
  unfold invariantRatioModuleIso
  rw [hI.invariantModuleIso_refl, hJ.invariantModuleIso_refl]
  simp only [Iso.refl_symm, Scheme.Modules.dualIsoObj_refl,
    Scheme.Modules.tensorObjCongr_refl, Iso.refl_trans, Iso.self_symm_id]

/-- The actual original ratio comparisons obey whole transitivity, using
true sheafified tensor functoriality and contravariant dual composition. -/
theorem IsInvertible.invariantRatioModuleIso_trans {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (f g h : X ⟶ Y)
    [Flat f] [Flat g] [Flat h]
    (hIfg : I.comap f = I.comap g) (hIgh : I.comap g = I.comap h)
    (hJfg : J.comap f = J.comap g) (hJgh : J.comap g = J.comap h) :
    hI.invariantRatioModuleIso hJ f g hIfg hJfg ≪≫
        hI.invariantRatioModuleIso hJ g h hIgh hJgh =
      hI.invariantRatioModuleIso hJ f h (hIfg.trans hIgh) (hJfg.trans hJgh) := by
  let Rf := I.ratioPullbackIso J hJ f
  let Rg := I.ratioPullbackIso J hJ g
  let Rh := I.ratioPullbackIso J hJ h
  let Efg := Scheme.Modules.tensorObjCongr (hI.invariantModuleIso f g hIfg)
    (Scheme.Modules.dualIsoObj (hJ.invariantModuleIso f g hJfg).symm)
  let Egh := Scheme.Modules.tensorObjCongr (hI.invariantModuleIso g h hIgh)
    (Scheme.Modules.dualIsoObj (hJ.invariantModuleIso g h hJgh).symm)
  let Efh := Scheme.Modules.tensorObjCongr (hI.invariantModuleIso f h (hIfg.trans hIgh))
    (Scheme.Modules.dualIsoObj (hJ.invariantModuleIso f h (hJfg.trans hJgh)).symm)
  have hm : Efg ≪≫ Egh = Efh := by
    dsimp only [Efg, Egh, Efh]
    rw [← Scheme.Modules.tensorObjCongr_trans, ← Scheme.Modules.dualIsoObj_trans,
      ← Iso.trans_symm, hI.invariantModuleIso_trans, hJ.invariantModuleIso_trans]
  change (Rf ≪≫ Efg ≪≫ Rg.symm) ≪≫ (Rg ≪≫ Egh ≪≫ Rh.symm) = Rf ≪≫ Efh ≪≫ Rh.symm
  calc
    _ = Rf ≪≫ (Efg ≪≫ Egh) ≪≫ Rh.symm := by
      simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = _ := by rw [hm]

end AlgebraicGeometry.Scheme.IdealSheafData
