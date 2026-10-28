/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.CartierRatioGenericMetric
import EnvelopeProperty.Local.PLIdealPrincipalization

/-! # Actual PL-only original simultaneous Cartier ratio model metrics -/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
open ProjBerk Berkovich.RelativeSchemeValuedPoint

/-- The ACTUAL original Cartier ratio on the SAME original simultaneous blowup. -/
def simultaneousRatioLine : (X.simultaneousIdealBlowup I J).Modules :=
  (I.comap (X.simultaneousIdealBlowupProjection I J)).ratioModule
    (J.comap (X.simultaneousIdealBlowupProjection I J))

/-- Both Cartier properties of the ACTUAL original ratio line are DERIVED
from the original simultaneous blowup, not supplied model hypotheses. -/
theorem simultaneousRatioLine_isInvertible :
    Scheme.Modules.IsInvertible (X.simultaneousRatioLine I J) :=
  (X.simultaneousIdealBlowup_isInvertible I J).1.isInvertible_ratioModule
    (X.simultaneousIdealBlowup_isInvertible I J).2

private theorem simultaneousRatio_firstNorm_ne_zero (w : X.an)
    (hI : modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    modelIdealNorm (I.comap (X.simultaneousIdealBlowupProjection I J)) gaussModelCoefficient_le_one
      (X.simultaneousIdealBlowupGaussPoint I J w hI hJ) ≠ 0 := by
  intro hn
  apply hI
  rw [← X.modelIdealLog_simultaneousIdealBlowup_comap I J I w hI hJ, modelIdealLog, hn,
    ENNReal.log_zero]

/-- The ACTUAL canonical original ratio section on the SAME original
simultaneous-blowup generic line, with nonvanishing derived from finite Gauss logs. -/
def simultaneousRatioSection (w : X.an)
    (hI : modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    Γ(genericLineModule (X.simultaneousIdealBlowupGaussPoint I J w hI hJ)
      (X.simultaneousRatioLine I J), ⊤) :=
  genericCartierRatioSection gaussModelCoefficient_le_one
    (X.simultaneousIdealBlowupGaussPoint I J w hI hJ)
    (I.comap (X.simultaneousIdealBlowupProjection I J))
    (J.comap (X.simultaneousIdealBlowupProjection I J))
    (X.simultaneousIdealBlowup_isInvertible I J).1
    (X.simultaneousIdealBlowup_isInvertible I J).2
    (X.simultaneousRatio_firstNorm_ne_zero I J w hI hJ)

/-- The genuine negative-log model norm of the ACTUAL original ratio section. -/
def simultaneousRatioWeight (w : X.an)
    (hI : modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) : EReal :=
  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one
    (X.simultaneousIdealBlowupGaussPoint I J w hI hJ) (X.simultaneousRatioLine_isInvertible I J)
      (X.simultaneousRatioSection I J w hI hJ) : ℝ≥0∞)

/-- The ACTUAL original ratio metric weight equals the ORIGINAL intrinsic
ideal difference at the actual variety-product Gauss point. -/
theorem simultaneousRatioWeight_eq (w : X.an)
    (hI : modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hJ : modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    X.simultaneousRatioWeight I J w hI hJ =
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) -
        modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) := by
  have h := modelLineNorm_genericCartierRatioSection_weight gaussModelCoefficient_le_one
    (X.simultaneousIdealBlowupGaussPoint I J w hI hJ)
    (I.comap (X.simultaneousIdealBlowupProjection I J))
    (J.comap (X.simultaneousIdealBlowupProjection I J))
    (X.simultaneousIdealBlowup_isInvertible I J).1
    (X.simultaneousIdealBlowup_isInvertible I J).2
    (X.simultaneousRatio_firstNorm_ne_zero I J w hI hJ)
  exact h.trans (congrArg₂ (fun a b : EReal => a - b)
    (X.modelIdealLog_simultaneousIdealBlowup_comap I J I w hI hJ)
    (X.modelIdealLog_simultaneousIdealBlowup_comap I J J w hI hJ))

/-- ORIGINAL PL input alone produces the actual original simultaneous
Cartier ratio model metric and exact positive-scaled PL weight formula. -/
theorem IsPL.exists_simultaneousRatioMetric_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
      (hfin : ∀ w : X.an,
        modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥),
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        X.simultaneousRatioWeight I J w (hfin w).1 (hfin w).2 + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, J, hfin, heq⟩ := IsPL.exists_nativeProductIdeal_models X hφ
  refine ⟨r, hr, C, I, J, hfin, fun w => ?_⟩
  rw [X.simultaneousRatioWeight_eq I J w (hfin w).1 (hfin w).2]
  exact heq w

end EnvelopeProperty.ProjSubvariety
