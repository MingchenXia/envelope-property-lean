/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.IdealModuleOffSupport
import EnvelopeProperty.AlgGeom.CartierRatioSheaves

/-!
# Whole support-complement trivialization of the genuine ratio sheaf

Actual ideal inclusion trivializations, true sheaf duality and genuine open
pullback-tensor compatibility construct the whole original ratio trivialization.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}}

/-- The actual tensor-dual ratio pulls back to the structure module on every
whole original open disjoint from both actual original ideal supports. -/
def ratioPullbackUnitIsoOfLeComplSupport (I J : X.IdealSheafData) (U : X.Opens)
    (hI : U ≤ I.support.compl) (hJ : U ≤ J.support.compl) :
    (Scheme.Modules.pullback U.ι).obj (I.ratioModule J) ≅
      Scheme.Modules.unitObj U.toScheme :=
  Scheme.Modules.pullbackTensorObjIsoOfIsOpenImmersion U.ι I.toModules
      (Scheme.Modules.dualObj J.toModules) ≪≫
    Scheme.Modules.tensorObjCongr (I.pullbackModuleIsoOfLeComplSupport U hI)
      (Scheme.Modules.pullbackIsoOfRestrictIso (Scheme.Modules.dualObj J.toModules) U
        (Scheme.Modules.dualRestrictIsoOfRestrictIso J.toModules U
          (J.restrictModuleIsoOfLeComplSupport U hJ))) ≪≫
    (Scheme.Modules.nonempty_tensorObj_unit_iso (Scheme.Modules.unitObj U.toScheme)).some

end AlgebraicGeometry.Scheme.IdealSheafData
