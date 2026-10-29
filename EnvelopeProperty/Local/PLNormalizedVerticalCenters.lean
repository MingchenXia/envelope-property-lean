import EnvelopeProperty.Local.PLIdealNormalizedRatioMetrics
import EnvelopeProperty.Berkovich.SchemeVerticalCenteredPoints
import EnvelopeProperty.Berkovich.SchemePrescribedDominance

/-! # Actual every-vertical-point centers on the SAME original normalized PL models -/
open CategoryTheory AlgebraicGeometry Classical
open scoped NNReal Polynomial
open EnvelopeProperty.Berkovich EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
include hfin

/-- The SAME actual normalization projection is finite over ANY original field,
using actual locally finite type geometry and genuine finite normalization. -/
theorem normalizedSimultaneousProjection_isFinite_anyField :
    IsFinite (X.normalizedSimultaneousIdealBlowupProjection I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2
  let : LocallyOfFiniteType (X.simultaneousIdealBlowupFieldStructure I J) :=
    X.simultaneousIdealBlowupFieldStructure_locallyOfFiniteType I J
  exact IntegralSchemeNormalization.projection_isFinite k (X.simultaneousIdealBlowup I J)
    (X.simultaneousIdealBlowupFieldStructure I J)

/-- TRUE properness of the SAME accepted original normalized PL model requires
no extra perfect-field or proper-model hypothesis. -/
theorem normalizedSimultaneousStructure_isProper_anyField :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  let : IsFinite (X.normalizedSimultaneousIdealBlowupProjection I J hfin) :=
    X.normalizedSimultaneousProjection_isFinite_anyField I J hfin
  dsimp only [normalizedSimultaneousIdealBlowupStructure]
  infer_instance

/-- The SAME actual original normalized structure is dominant, DERIVED from
its genuine original whole Gauss point, with no dominance certificate. -/
theorem normalizedSimultaneousStructure_isDominant (hX : X.IsProjNormal) :
    IsDominant (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  apply isDominant_of_gaussPoint gaussRadius (show 0 < gaussRadius from by
    change (0 : ℝ) < Real.exp (-1)
    exact Real.exp_pos _)
  exact X.normalizedSimultaneousGaussPoint I J hfin hX X.triv

/-- Every ORIGINAL special-fibre point on the SAME original normalized PL
model is the TRUE center of an ACTUAL original prescribed Gauss native point. -/
theorem exists_normalizedSimultaneousGaussPoint_center (hX : X.IsProjNormal)
    (x : X.normalizedSimultaneousIdealBlowup I J hfin)
    (hx : Polynomial.X ∈ (X.normalizedSimultaneousIdealBlowupStructure I J hfin x).asIdeal) :
    letI := X.normalizedSimultaneousStructure_isProper_anyField I J hfin
    ∃ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
      center gaussModelCoefficient_le_one y = x := by
  let : IsIntegral (X.normalizedSimultaneousIdealBlowup I J hfin) :=
    X.normalizedSimultaneousIdealBlowup_isIntegral I J hfin
  let : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousStructure_isProper_anyField I J hfin
  let : IsDominant (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousStructure_isDominant I J hfin hX
  exact exists_gaussPoint_center_of_vertical (X.normalizedSimultaneousIdealBlowupStructure I J hfin) x hx

end EnvelopeProperty.ProjSubvariety
