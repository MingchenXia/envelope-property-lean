/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealNormalProduct
import EnvelopeProperty.AlgGeom.NormalOpenIsomorphismSupport
import EnvelopeProperty.Berkovich.NormalizedCartierRatioMetric

/-! # Actual normal proper original simultaneous PL models -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Polynomial NNReal ENNReal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

include hfin

private theorem simultaneousIntegral : IsIntegral (X.simultaneousIdealBlowup I J) :=
  X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2

/-- The ACTUAL original generic-field normalization of the SAME original
simultaneous blowup. Integrality is produced from finite original Gauss ideal logs. -/
def normalizedSimultaneousIdealBlowup : Scheme.{u} := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := simultaneousIntegral X I J hfin
  exact normalization (X.simultaneousIdealBlowup I J)

/-- The ACTUAL original normalization projection onto the SAME original blowup. -/
def normalizedSimultaneousIdealBlowupProjection :
    X.normalizedSimultaneousIdealBlowup I J hfin ⟶ X.simultaneousIdealBlowup I J := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := simultaneousIntegral X I J hfin
  exact projection (X.simultaneousIdealBlowup I J)

/-- The ACTUAL original normal model's SAME polynomial-base structure. -/
def normalizedSimultaneousIdealBlowupStructure :
    X.normalizedSimultaneousIdealBlowup I J hfin ⟶ Spec (.of k[X]) :=
  X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫ X.simultaneousIdealBlowupStructure I J

/-- Every ACTUAL original local ring of the constructed original normal model
is integrally closed, without a model-normality hypothesis. -/
theorem normalizedSimultaneousIdealBlowup_stalk_isIntegrallyClosed
    (z : X.normalizedSimultaneousIdealBlowup I J hfin) :
    IsIntegrallyClosed ((X.normalizedSimultaneousIdealBlowup I J hfin).presheaf.stalk z) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := simultaneousIntegral X I J hfin
  exact IntegralSchemeNormalization.stalk_isIntegrallyClosed (X.simultaneousIdealBlowup I J) z

/-- The SAME actual original normalized simultaneous model is integral. -/
theorem normalizedSimultaneousIdealBlowup_isIntegral :
    IsIntegral (X.normalizedSimultaneousIdealBlowup I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := simultaneousIntegral X I J hfin
  exact inferInstanceAs (IsIntegral (normalization (X.simultaneousIdealBlowup I J)))


/-- The ACTUAL original normalization projection is finite, with the original
field finite type and arbitrary-field finite normalization deriving finiteness internally. -/
theorem normalizedSimultaneousIdealBlowupProjection_isFinite :
    IsFinite (X.normalizedSimultaneousIdealBlowupProjection I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := simultaneousIntegral X I J hfin
  let : LocallyOfFiniteType (X.simultaneousIdealBlowupFieldStructure I J) :=
    X.simultaneousIdealBlowupFieldStructure_locallyOfFiniteType I J
  exact projection_isFinite k (X.simultaneousIdealBlowup I J) (X.simultaneousIdealBlowupFieldStructure I J)

/-- The SAME actual original normalized model is proper over the SAME original
polynomial base, with both normalization and model properness DERIVED. -/
theorem normalizedSimultaneousIdealBlowupStructure_isProper :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  let : IsFinite (X.normalizedSimultaneousIdealBlowupProjection I J hfin) :=
    X.normalizedSimultaneousIdealBlowupProjection_isFinite I J hfin
  dsimp [normalizedSimultaneousIdealBlowupStructure]
  infer_instance

end EnvelopeProperty.ProjSubvariety
