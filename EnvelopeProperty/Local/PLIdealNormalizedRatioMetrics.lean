/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealNormalizedModels
import EnvelopeProperty.Local.PLIdealRatioMetrics

/-! # Actual PL weights on SAME original normal proper ratio models -/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Classical Polynomial NNReal ENNReal
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

private theorem blowupIntegral : IsIntegral (X.simultaneousIdealBlowup I J) :=
  X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2

private def normalizationGaussSupport (hX : X.IsProjNormal) (w : X.an) :
    {U : (X.simultaneousIdealBlowup I J).affineOpens //
      (X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2).1.point ∈ U.1 ∧
        IsIntegrallyClosed Γ(X.simultaneousIdealBlowup I J, U.1)} := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := blowupIntegral X I J hfin
  let μ := X.simultaneousIdealBlowupProjection I J
  let W := (I * J).support.compl
  let y := X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2
  have hz : y.1.point ∈ μ ⁻¹ᵁ W := by
    have hm := congrArg (fun z => z.1.point)
      (X.map_simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2)
    change μ y.1.point = (X.nativeProductGaussPoint w).1.point at hm
    change μ y.1.point ∈ W
    rw [hm]
    exact X.nativeProductGaussPoint_notMem_productSupport I J w (hfin w).1 (hfin w).2
  have hn : ∃ U : (X.simultaneousIdealBlowup I J).affineOpens,
      y.1.point ∈ U.1 ∧ IsIntegrallyClosed Γ(X.simultaneousIdealBlowup I J, U.1) := by
    obtain ⟨U, hU, hyU, hNU⟩ := μ.exists_normal_affine_neighborhood_of_restrictIso W
      (X.nativeProductModel_stalk_isIntegrallyClosed hX) y.1.point hz
    exact ⟨⟨U, hU⟩, hyU, hNU⟩
  exact ⟨Classical.choose hn, Classical.choose_spec hn⟩

/-- The true original Gauss point on the SAME actual normalized simultaneous
model; its normal affine support is derived from original projective normality. -/
def normalizedSimultaneousGaussPoint (hX : X.IsProjNormal) (w : X.an) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := blowupIntegral X I J hfin
  let U := normalizationGaussSupport X I J hfin hX w
  let : Nonempty U.1.1 := ⟨⟨_, U.2.1⟩⟩
  let : IsIntegrallyClosed Γ(X.simultaneousIdealBlowup I J, U.1.1) := U.2.2
  exact relativePointLiftOnNormalAffine (X.simultaneousIdealBlowup I J) U.1.1 U.1.2
    (X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2) U.2.1

/-- The normalization lift retains the ENTIRE original simultaneous Gauss
point, including original residue valuation and polynomial base point. -/
theorem map_normalizedSimultaneousGaussPoint (hX : X.IsProjNormal) (w : X.an) :
    RelativeSchemeValuedPoint.map (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl
      (X.normalizedSimultaneousGaussPoint I J hfin hX w) =
        X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2 := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := blowupIntegral X I J hfin
  let U := normalizationGaussSupport X I J hfin hX w
  let : Nonempty U.1.1 := ⟨⟨_, U.2.1⟩⟩
  let : IsIntegrallyClosed Γ(X.simultaneousIdealBlowup I J, U.1.1) := U.2.2
  exact map_relativePointLiftOnNormalAffine (X.simultaneousIdealBlowup I J) U.1.1 U.1.2
    (X.simultaneousIdealBlowupGaussPoint I J w (hfin w).1 (hfin w).2) U.2.1

/-- The SAME actual Cartier ratio line on the SAME original normal model. -/
def normalizedSimultaneousRatioLine : (X.normalizedSimultaneousIdealBlowup I J hfin).Modules :=
  ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin)).ratioModule
      ((J.comap (X.simultaneousIdealBlowupProjection I J)).comap
        (X.normalizedSimultaneousIdealBlowupProjection I J hfin))

/-- Both original Cartier ideals remain Cartier on the actual normalization,
so invertibility of the actual original ratio line is DERIVED. -/
theorem normalizedSimultaneousRatioLine_isInvertible :
    Scheme.Modules.IsInvertible (X.normalizedSimultaneousRatioLine I J hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := blowupIntegral X I J hfin
  exact (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).1).isInvertible_ratioModule
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).2)

private local instance normalizationProjectionFinite :
    IsFinite (X.normalizedSimultaneousIdealBlowupProjection I J hfin) :=
  X.normalizedSimultaneousIdealBlowupProjection_isFinite I J hfin

private local instance normalizedProper : IsProper (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper I J hfin

private theorem normalizedFirstNorm_ne_zero (hX : X.IsProjNormal) (w : X.an) :
    modelIdealNorm ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin)) gaussModelCoefficient_le_one
      (X.normalizedSimultaneousGaussPoint I J hfin hX w) ≠ 0 := by
  intro hn
  apply (hfin w).1
  have hi := modelIdealLog_comap (I.comap (X.simultaneousIdealBlowupProjection I J))
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
  rw [X.map_normalizedSimultaneousGaussPoint] at hi
  rw [X.modelIdealLog_simultaneousIdealBlowup_comap] at hi
  rw [← hi, modelIdealLog, hn, ENNReal.log_zero]

/-- The ACTUAL canonical original generic ratio section on the true original
normal proper model, with all Cartier/nonvanishing facts internally produced. -/
def normalizedSimultaneousRatioSection (hX : X.IsProjNormal) (w : X.an) :
    Γ(genericLineModule (X.normalizedSimultaneousGaussPoint I J hfin hX w)
      (X.normalizedSimultaneousRatioLine I J hfin), ⊤) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := blowupIntegral X I J hfin
  exact genericCartierRatioSection gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    ((J.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).1)
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).2)
    (normalizedFirstNorm_ne_zero X I J hfin hX w)

/-- The TRUE negative-log model norm of the true original ratio section
on the SAME actual original normal proper model. -/
def normalizedSimultaneousRatioWeight (hX : X.IsProjNormal) (w : X.an) : EReal :=
  -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    (X.normalizedSimultaneousRatioLine_isInvertible I J hfin)
    (X.normalizedSimultaneousRatioSection I J hfin hX w) : ℝ≥0∞)

/-- The actual normal proper model's true original ratio weight retains
EXACTLY the ORIGINAL intrinsic ideal-log difference at the ORIGINAL Gauss point. -/
theorem normalizedSimultaneousRatioWeight_eq (hX : X.IsProjNormal) (w : X.an) :
    X.normalizedSimultaneousRatioWeight I J hfin hX w =
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) -
        modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) := blowupIntegral X I J hfin
  have h := modelLineNorm_genericCartierRatioSection_weight gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
    ((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    ((J.comap (X.simultaneousIdealBlowupProjection I J)).comap
      (X.normalizedSimultaneousIdealBlowupProjection I J hfin))
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).1)
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).2)
    (normalizedFirstNorm_ne_zero X I J hfin hX w)
  have hi := modelIdealLog_comap (I.comap (X.simultaneousIdealBlowupProjection I J))
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
  have hj := modelIdealLog_comap (J.comap (X.simultaneousIdealBlowupProjection I J))
    (X.normalizedSimultaneousIdealBlowupProjection I J hfin) rfl gaussModelCoefficient_le_one
    (X.normalizedSimultaneousGaussPoint I J hfin hX w)
  rw [X.map_normalizedSimultaneousGaussPoint, X.modelIdealLog_simultaneousIdealBlowup_comap] at hi hj
  exact h.trans (congrArg₂ (fun a b : EReal => a - b) hi hj)

omit hfin in
/-- ORIGINAL PL data on an ORIGINAL projectively-normal variety alone produce
the SAME actual normal proper ratio model metric and its exact scaled PL formula. -/
theorem IsPL.exists_normalizedSimultaneousRatioMetric_models (hX : X.IsProjNormal)
    {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
      (hfin : ∀ w : X.an,
        modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥),
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeight I J hfin hX w + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, J, hfin, heq⟩ := IsPL.exists_nativeProductIdeal_models X hφ
  refine ⟨r, hr, C, I, J, hfin, fun w => ?_⟩
  rw [X.normalizedSimultaneousRatioWeight_eq I J hfin hX w]
  exact heq w

end EnvelopeProperty.ProjSubvariety
