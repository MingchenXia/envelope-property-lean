import EnvelopeProperty.Local.PLMonomialFullPointMetrics
import EnvelopeProperty.Local.PLIdealNormalizedRatioMetrics

/-! # True canonical ratio sections at ALL actual normalized-model points -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
include hfin
private theorem actualIntegral : IsIntegral (X.simultaneousIdealBlowup I J) :=
  X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2
private local instance normalizedProper :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin

/-- The entire original product point underlying ANY true normalized-model
valued point, retaining the literal original two projections. -/
def normalizedSimultaneousProductPointAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure :=
  RelativeSchemeValuedPoint.map (X.simultaneousIdealBlowupProjection I J) rfl
    (RelativeSchemeValuedPoint.map (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl y)

/-- The actual SAME original analytic restriction of every true normal-model point. -/
def normalizedSimultaneousBaseRestrictionAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) : X.an :=
  X.nativeProductBaseRestriction (X.normalizedSimultaneousProductPointAt I J hfin y)

/-- Every TRUE pulled original ideal logarithm equals its actual original
product logarithm at the ENTIRE projected point, including infinite values. -/
theorem modelIdealLog_normalizedSimultaneous_comap (K : X.NativeProductModel.IdealSheafData)
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin)) :
    modelIdealLog ((K.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin)) gaussModelCoefficient_le_one y =
    modelIdealLog K gaussModelCoefficient_le_one (X.normalizedSimultaneousProductPointAt I J hfin y) := by
  have hν := modelIdealLog_comap
    (fX := X.normalizedSimultaneousIdealBlowupStructure I J hfin)
    (fY := X.simultaneousIdealBlowupStructure I J)
    (K.comap (X.simultaneousIdealBlowupProjection I J))
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl gaussModelCoefficient_le_one y
  have hμ := modelIdealLog_comap
    (fX := X.simultaneousIdealBlowupStructure I J) (fY := X.nativeProductStructure)
    K (X.simultaneousIdealBlowupProjection I J) rfl gaussModelCoefficient_le_one
    (RelativeSchemeValuedPoint.map (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl y)
  exact hν.trans hμ

private theorem firstNorm_ne_zero
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥) :
    modelIdealNorm ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin)) gaussModelCoefficient_le_one y ≠ 0 := by
  intro hz
  apply hnI
  rw [← X.modelIdealLog_normalizedSimultaneous_comap I J hfin I y,
    modelIdealLog, hz, ENNReal.log_zero]

/-- The actual canonical generic ratio section at ANY original normalized
model point whose first original ideal has nonzero value. This is the SAME
actual ratio line; no rational-section or metric comparison is supplied. -/
def normalizedSimultaneousRatioSectionAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥) :
    Γ(genericLineModule y (X.normalizedSimultaneousRatioLine I J hfin), ⊤) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := actualIntegral X I J hfin
  exact genericCartierRatioSection gaussModelCoefficient_le_one y
    ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    ((J.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).1)
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).2)
    (firstNorm_ne_zero X I J hfin y hnI)

/-- TRUE negative-log norm of the SAME actual canonical ratio section at an
arbitrary original normalized-model point, rather than only at Gauss lifts. -/
def normalizedSimultaneousRatioWeightAt
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥) : EReal :=
  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
    (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)
    (X.normalizedSimultaneousRatioSectionAt I J hfin y hnI) : ℝ≥0∞)

/-- The SAME true actual ratio-section weight at every admissible actual
model point equals the ORIGINAL product ideal-log difference. -/
theorem normalizedSimultaneousRatioWeightAt_eq
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
    (hnI : modelIdealLog I gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt I J hfin y) ≠ ⊥) :
    X.normalizedSimultaneousRatioWeightAt I J hfin y hnI =
      modelIdealLog I gaussModelCoefficient_le_one
        (X.normalizedSimultaneousProductPointAt I J hfin y) -
      modelIdealLog J gaussModelCoefficient_le_one
        (X.normalizedSimultaneousProductPointAt I J hfin y) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := actualIntegral X I J hfin
  have h := modelLineNorm_genericCartierRatioSection_weight gaussModelCoefficient_le_one y
    ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    ((J.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).1)
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).2)
    (firstNorm_ne_zero X I J hfin y hnI)
  exact h.trans (congrArg₂ (fun a b : EReal => a-b)
    (X.modelIdealLog_normalizedSimultaneous_comap I J hfin I y)
    (X.modelIdealLog_normalizedSimultaneous_comap I J hfin J y))
end EnvelopeProperty.ProjSubvariety
