import EnvelopeProperty.Local.PLIdealNormalizedModels
import EnvelopeProperty.Berkovich.SchemePrescribedDominance
import EnvelopeProperty.Alterations.Geometry.ProperFlatteningDedekind

/-! # Flatness of the same original normalized simultaneous PL model

The actual normalization projection is surjective. The original simultaneous
blowup has a prescribed positive-radius Gauss point, so its structure map is
dominant over the original polynomial line. Their same composite is dominant
and has integral source, hence is flat over the Dedekind domain `k[X]`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial NNReal

universe u

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

/-- The actual same normalization projection is surjective over any field. -/
theorem normalizedSimultaneousProjection_surjective :
    Function.Surjective (X.normalizedSimultaneousIdealBlowupProjection I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv
      (hfin X.triv).1 (hfin X.triv).2
  exact IntegralSchemeNormalization.projection_surjective (X.simultaneousIdealBlowup I J)

/-- Actual dominance of the same original normalized structure follows from
the original blowup Gauss point and surjectivity of its normalization. -/
theorem normalizedSimultaneousStructure_isDominant_anyField :
    IsDominant (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  let : IsDominant (X.normalizedSimultaneousIdealBlowupProjection I J hfin) :=
    ⟨(X.normalizedSimultaneousProjection_surjective I J hfin).denseRange⟩
  let : IsDominant (X.simultaneousIdealBlowupStructure I J) := by
    apply isDominant_of_gaussPoint gaussRadius (show 0 < gaussRadius from by
      change (0 : ℝ) < Real.exp (-1)
      exact Real.exp_pos _)
    exact X.simultaneousIdealBlowupGaussPoint I J X.triv
      (hfin X.triv).1 (hfin X.triv).2
  dsimp only [normalizedSimultaneousIdealBlowupStructure]
  infer_instance

/-- The original normalized model is flat over its same polynomial base,
using only finite original Gauss ideal logarithms, over any field. -/
theorem normalizedSimultaneousStructure_isFlat_anyField :
    Flat (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  let : IsIntegral (X.normalizedSimultaneousIdealBlowup I J hfin) :=
    X.normalizedSimultaneousIdealBlowup_isIntegral I J hfin
  let : IsDominant (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    X.normalizedSimultaneousStructure_isDominant_anyField I J hfin
  exact Alterations.Geometry.ProperFlatteningDedekind.flat_of_dominant_to_spec
    (Polynomial k) (X.normalizedSimultaneousIdealBlowupStructure I J hfin)

end EnvelopeProperty.ProjSubvariety
