/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierIdealModules
import ModularCurves.Picard.InvertibleSheaf

/-!
# The actual Cartier ideal module as a genuine invertible sheaf

The true regular-generator affine restriction isomorphism is converted through
actual open-immersion restriction/pullback comparisons. This proves the genuine
existing rank-one open-cover invertibility definition for the actual ideal
module sheaf; no line-bundle comparison is an input.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual original regular affine equation gives the true module pullback
trivialization over the corresponding original open subscheme. -/
def regularGeneratorPullbackModuleIso (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    (Scheme.Modules.pullback (U : X.Opens).ι).obj I.toModules ≅
      Scheme.Modules.unitObj (U : X.Opens).toScheme :=
  Scheme.Modules.pullbackIsoOfRestrictIso I.toModules U
    ((I.toModules.restrictιIso U.2).symm ≪≫
      (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
        (I.regularGeneratorModuleIso U g hg hI).symm ≪≫
      Scheme.Modules.restrictUnitIso U.2.isoSpec.hom)

/-- Actual effective Cartier invertibility proves the genuine existing
rank-one module-sheaf invertibility definition through true pullback charts. -/
theorem IsInvertible.isInvertibleModule_toModules (hI : I.IsInvertible) :
    Scheme.Modules.IsInvertible I.toModules := by
  choose U hx g hg hgen using hI
  refine ⟨X, fun x => (U x : X.Opens), ?_, fun x =>
    ⟨I.regularGeneratorPullbackModuleIso (U x) (g x) (hg x) (hgen x)⟩⟩
  exact top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)

end AlgebraicGeometry.Scheme.IdealSheafData
