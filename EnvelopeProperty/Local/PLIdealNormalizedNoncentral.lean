/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealNormalizedRatioMetrics
import EnvelopeProperty.AlgGeom.NormalizationNormalOpen
import EnvelopeProperty.Local.PLIdealNoncentralSheaves

/-! # Actual normalized simultaneous models are unchanged over the original parameter open -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Classical Polynomial NNReal ENNReal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual original normality and a true whole original open isomorphism
make the normalization projection an ACTUAL whole isomorphism over that source open. -/
theorem normalizedSimultaneousProjection_isIso_on_originalOpen
    (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hX : X.IsProjNormal) (W : X.NativeProductModel.Opens)
    [IsIso (X.simultaneousIdealBlowupProjection I J ∣_ W)] :
    IsIso (X.normalizedSimultaneousIdealBlowupProjection I J hfin ∣_
      (X.simultaneousIdealBlowupProjection I J ⁻¹ᵁ W)) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2
  exact projection_isIso_on_normal_open (X.simultaneousIdealBlowup I J)
    (X.simultaneousIdealBlowupProjection I J ⁻¹ᵁ W)
    ((X.simultaneousIdealBlowupProjection I J).stalk_isIntegrallyClosed_of_restrictIso W
      (X.nativeProductModel_stalk_isIntegrallyClosed hX))

/-- The ACTUAL normalized original simultaneous model still projects as a
WHOLE isomorphism over every original open where the original blowup does. -/
theorem normalizedSimultaneousComposite_isIso_on_originalOpen
    (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hX : X.IsProjNormal) (W : X.NativeProductModel.Opens)
    [IsIso (X.simultaneousIdealBlowupProjection I J ∣_ W)] :
    IsIso ((X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫
      X.simultaneousIdealBlowupProjection I J) ∣_ W) := by
  let := X.normalizedSimultaneousProjection_isIso_on_originalOpen I J hfin hX W
  rw [morphismRestrict_comp]
  infer_instance

/-- Actual original parameter-power ideal membership proves the SAME normalized
model is a WHOLE original product over the ACTUAL original noncentral open. -/
theorem normalizedSimultaneousComposite_isIso_over_parameter
    (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal)
    (hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (hX : X.IsProjNormal) :
    IsIso ((X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≫
      X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J)) ∣_
        (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) := by
  let := X.simultaneousIdealBlowup_isIso_over_parameter_of_power_mem I J A B hA hB
  exact X.normalizedSimultaneousComposite_isIso_on_originalOpen
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin hX _

/-- ORIGINAL PL data on an ORIGINAL projectively-normal variety produce
same actual normal proper ratio models with a WHOLE original noncentral product,
including genuine original parameter powers and the exact actual metric weight. -/
theorem IsPL.exists_normalizedNoncentralRatio_models (hX : X.IsProjNormal)
    {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ J.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) ∧
      let I' := X.nativeProductIdeal I
      let J' := X.nativeProductIdeal J
      ∃ (hfin : ∀ w : X.an,
        modelIdealLog I' gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        modelIdealLog J' gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥),
        IsIso ((X.normalizedSimultaneousIdealBlowupProjection I' J' hfin ≫
          X.simultaneousIdealBlowupProjection I' J') ∣_
            (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) ∧
        ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
          X.normalizedSimultaneousRatioWeight I' J' hfin hX w + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, J, hfgI, hfgJ, hAI, hBJ, hfin, _hMod, _hIso, _hRatio, _hTriv, hlog⟩ :=
    hφ.exists_noncentralInvertibleRatio_models
  obtain ⟨A, hA, hAmem⟩ := hAI
  obtain ⟨B, hB, hBmem⟩ := hBJ
  refine ⟨r, hr, C, I, J, hfgI, hfgJ, ⟨A, hA, hAmem⟩, ⟨B, hB, hBmem⟩, hfin,
    X.normalizedSimultaneousComposite_isIso_over_parameter I J A B hAmem hBmem hfin hX, fun w => ?_⟩
  rw [X.normalizedSimultaneousRatioWeight_eq]
  simpa only [X.modelIdealLog_simultaneousIdealBlowup_comap] using hlog w

end EnvelopeProperty.ProjSubvariety
