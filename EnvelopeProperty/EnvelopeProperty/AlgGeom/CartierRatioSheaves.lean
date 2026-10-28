/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierInvertibleSheaves
import ModularCurves.Picard.Dual
import ModularCurves.ForMathlib.PullbackTensorMonoidal

/-!
# Actual tensor-dual ratio line sheaves of effective Cartier ideals

The ratio is the genuine sheafified tensor product of the original ideal
module and the actual O-linear sheaf dual of the other original ideal.
It does not yet carry a proved model metric or O(r) polarization.
-/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}}

/-- The genuine original tensor-dual ratio module of two actual ideal sheaves. -/
def ratioModule (I J : X.IdealSheafData) : X.Modules :=
  Scheme.Modules.tensorObj I.toModules (Scheme.Modules.dualObj J.toModules)

/-- Actual effective Cartier invertibility proves genuine rank-one
invertibility of the actual original tensor-dual ratio sheaf. -/
theorem IsInvertible.isInvertible_ratioModule {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Scheme.Modules.IsInvertible (I.ratioModule J) :=
  hI.isInvertibleModule_toModules.tensorObj hJ.isInvertibleModule_toModules.dual

end AlgebraicGeometry.Scheme.IdealSheafData
