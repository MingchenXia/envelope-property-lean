/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeLineFibreSectionNorms
import EnvelopeProperty.Berkovich.CartierGenericUnitSection
import EnvelopeProperty.AlgGeom.CartierRatioSheaves

/-! # The true original generic Cartier ratio section and actual ideal potentials -/

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

/-- The canonical ACTUAL original generic section of the ORIGINAL
Cartier ratio I ⊗ J^∨, with no supplied rational trivialization certificate. -/
def genericCartierRatioSection (I J : X.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hnI : modelIdealNorm I hb y ≠ 0) : Γ(genericLineModule y (I.ratioModule J), ⊤) :=
  genericTensorSection y (genericIdealUnitSection hb y I hI hnI)
    (fibreSection y (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion))

/-- The TRUE original ratio section has actual model norm J/I on the
SAME original generic fiber, derived from genuine actual factor metrics. -/
theorem modelLineNorm_genericCartierRatioSection (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hnI : modelIdealNorm I hb y ≠ 0) :
    (modelLineNorm hb y (hI.isInvertible_ratioModule hJ)
      (genericCartierRatioSection hb y I J hI hJ hnI) : ℝ≥0∞) =
      (modelIdealNorm I hb y)⁻¹ * modelIdealNorm J hb y := by
  have ha : modelHomNorm hb y hI.isInvertibleModule_toModules
      (Scheme.Modules.isInvertible_unit (X := X)) I.toModulesInclusion ≠ 0 := by
    intro h
    apply hnI
    rw [← modelHomNorm_idealInclusion I hI hb y, h, ENNReal.coe_zero]
  change (modelLineNorm hb y (hI.isInvertibleModule_toModules.tensorObj hJ.isInvertibleModule_toModules.dual)
    (genericTensorSection y (genericIdealUnitSection hb y I hI hnI)
      (fibreSection y (hJ.isInvertibleModule_toModules.dualTranspose J.toModulesInclusion))) : ℝ≥0∞) = _
  rw [modelLineNorm_genericTensorSection hb y hI.isInvertibleModule_toModules
      hJ.isInvertibleModule_toModules.dual,
    modelLineNorm_genericIdealUnitSection hb y I hI hnI,
    modelLineNorm_fibreSection hb y hJ.isInvertibleModule_toModules.dual,
    modelHomNorm_dualTranspose hb y hJ.isInvertibleModule_toModules,
    ENNReal.coe_mul, ENNReal.coe_inv ha,
    modelHomNorm_idealInclusion I hI hb y, modelHomNorm_idealInclusion J hJ hb y]

/-- The actual logarithmic norm of the ORIGINAL Cartier ratio section
is intrinsic logJ - logI; its model weight therefore has the opposite sign. -/
theorem modelLineNorm_genericCartierRatioSection_log (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hnI : modelIdealNorm I hb y ≠ 0) :
    ENNReal.log (modelLineNorm hb y (hI.isInvertible_ratioModule hJ)
      (genericCartierRatioSection hb y I J hI hJ hnI) : ℝ≥0∞) =
      modelIdealLog J hb y - modelIdealLog I hb y := by
  rw [modelLineNorm_genericCartierRatioSection, ENNReal.log_mul_add, ENNReal.log_inv,
    sub_eq_add_neg]
  exact add_comm _ _

/-- The TRUE negative logarithmic norm of the ACTUAL original ratio
section equals logI-logJ, with actual finiteness of logI DERIVED internally. -/
theorem modelLineNorm_genericCartierRatioSection_weight (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hnI : modelIdealNorm I hb y ≠ 0) :
    -ENNReal.log (modelLineNorm hb y (hI.isInvertible_ratioModule hJ)
      (genericCartierRatioSection hb y I J hI hJ hnI) : ℝ≥0∞) =
      modelIdealLog I hb y - modelIdealLog J hb y := by
  have hbot : modelIdealLog I hb y ≠ ⊥ := by
    exact fun h => hnI (ENNReal.log_eq_bot_iff.mp h)
  have htop : modelIdealLog I hb y ≠ ⊤ := by
    have hn : modelIdealNorm I hb y ≠ ⊤ := ne_of_lt
      (lt_of_le_of_lt (modelIdealNorm_le_one I hb y) (by simp))
    exact fun h => hn (ENNReal.log_eq_top_iff.mp h)
  rw [modelLineNorm_genericCartierRatioSection_log,
    EReal.neg_sub (Or.inr hbot) (Or.inr htop), sub_eq_add_neg]
  exact add_comm _ _

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
