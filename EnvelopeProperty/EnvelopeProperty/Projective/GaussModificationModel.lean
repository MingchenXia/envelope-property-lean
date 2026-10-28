/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeBaseOpenModification
import EnvelopeProperty.Projective.ProductIdealRepresentation
import EnvelopeProperty.Berkovich.SchemeModelNoetherian

/-!
# Actual Gauss lifts and true intrinsic ideals on genuine modifications

The actual parameter value is nonzero, so the real D(t) scheme isomorphism
gives a continuous unique whole native Gauss lift. Only actual properness
of the modification is used to construct source proper centers, derive real
local Noetherianity, and evaluate arbitrary original source ideals. Geometric
pullback ideals retain their entire original product phi functions. Bounds
are on the MODEL k[t] valuation, not an entire nontrivially valued field.
No source-ideal descent or analytic coherent-sheaf identification is asserted.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry Topology Polynomial
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
variable (μ : Z ⟶ NativePolynomialLineProduct k n)

/-- The original source MODEL structure is the actual entire composite of the given modification and genuine product structure map. -/
def gaussModificationStructure : Z ⟶ Spec (CommRingCat.of k[X]) :=
  μ ≫ nativePolynomialLineProductStructure

private local instance gaussModificationTargetProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := n)) :=
  nativePolynomialLineProductStructure_isProper

/-- Actual properness of the modification derives properness of the original full MODEL structure morphism. -/
theorem gaussModificationStructure_isProper [IsProper μ] : IsProper (gaussModificationStructure μ) := by
  have h : IsProper (μ ≫ nativePolynomialLineProductStructure) := inferInstance
  exact h

private local instance gaussModificationSourceProper [IsProper μ] : IsProper (gaussModificationStructure μ) :=
  gaussModificationStructure_isProper μ

/-- Actual proper finite type over the original Noetherian MODEL k[t] derives real local Noetherianity of the source scheme. -/
theorem gaussModificationSource_isLocallyNoetherian [IsProper μ] : IsLocallyNoetherian Z :=
  LocallyOfFiniteType.isLocallyNoetherian (gaussModificationStructure μ)

variable [IsIso (μ ∣_ (nativePolynomialLineProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (X : k[X])))]

/-- The genuine original parameter has its actual nonzero Gauss value in the bounded MODEL coefficient ring. -/
theorem gaussModel_parameter_ne_zero :
    gaussValuation (1 : Valuation k ℝ≥0) gaussRadius (X : k[X]) ≠ 0 := by
  change gaussFun (1 : Valuation k ℝ≥0) gaussRadius (X : k[X]) ≠ 0
  rw [gaussFun_X]
  exact gaussRadius_ne_zero

/-- The actual whole Gauss product point has a canonical entire native lift through the genuine D(t) isomorphism. -/
def gaussModificationPoint (x : ProjBerk k n) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) (gaussModificationStructure μ) :=
  (RelativeSchemeValuedPoint.principalBaseModificationHomeomorph μ rfl
    (X : k[X]) gaussModel_parameter_ne_zero).symm (gaussProductPoint x)

/-- The original whole native map recovers the complete original Gauss product point. -/
theorem map_gaussModificationPoint (x : ProjBerk k n) :
    RelativeSchemeValuedPoint.map μ rfl (gaussModificationPoint μ x) = gaussProductPoint x := by
  rw [gaussModificationPoint, ← RelativeSchemeValuedPoint.principalBaseModificationHomeomorph_apply
    μ rfl (X : k[X]) gaussModel_parameter_ne_zero, Homeomorph.apply_symm_apply]

/-- Every entire original target section value is preserved by its real scheme pullback at the actual unique Gauss lift. -/
theorem gaussModificationPoint_eval (x : ProjBerk k n)
    (V : (NativePolynomialLineProduct k n).Opens)
    (hx : (gaussProductPoint x).1.point ∈ V) (s : Γ(NativePolynomialLineProduct k n, V)) :
    SchemeValuedPoint.eval (gaussProductPoint x).1 V hx s =
      SchemeValuedPoint.eval (gaussModificationPoint μ x).1 (μ ⁻¹ᵁ V)
        (by
          have h := congrArg (fun z => z.1.point) (map_gaussModificationPoint μ x)
          change μ (gaussModificationPoint μ x).1.point = (gaussProductPoint x).1.point at h
          change μ (gaussModificationPoint μ x).1.point ∈ V
          exact h.symm ▸ hx) (μ.app V s) := by
  have h : ∀ z : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) nativePolynomialLineProductStructure,
      z = RelativeSchemeValuedPoint.map μ rfl (gaussModificationPoint μ x) →
      ∀ hz : z.1.point ∈ V, SchemeValuedPoint.eval z.1 V hz s =
        SchemeValuedPoint.eval (gaussModificationPoint μ x).1 (μ ⁻¹ᵁ V)
          (by
            have he := congrArg (fun z => z.1.point) (map_gaussModificationPoint μ x)
            change μ (gaussModificationPoint μ x).1.point = (gaussProductPoint x).1.point at he
            change μ (gaussModificationPoint μ x).1.point ∈ V
            exact he.symm ▸ hx) (μ.app V s) := by
    intro z hz
    subst z
    intro hzV
    exact SchemeValuedPoint.eval_map μ (gaussModificationPoint μ x).1 V hzV s
  exact h _ (map_gaussModificationPoint μ x).symm hx

/-- Actual inverse native homeomorphism and the genuine Gauss product map make the entire lift continuous. -/
@[fun_prop]
theorem continuous_gaussModificationPoint : Continuous (gaussModificationPoint μ) :=
  (RelativeSchemeValuedPoint.principalBaseModificationHomeomorph μ rfl
    (X : k[X]) gaussModel_parameter_ne_zero).symm.continuous.comp continuous_gaussProductPoint

/-- Every original Gauss product point has exactly one entire prescribed-base native source lift. -/
theorem existsUnique_gaussModificationPoint (x : ProjBerk k n) :
    ∃! z : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) (gaussModificationStructure μ),
      RelativeSchemeValuedPoint.map μ rfl z = gaussProductPoint x :=
  RelativeSchemeValuedPoint.existsUnique_map_eq_of_isIso_over_baseOpen μ rfl
    (PrimeSpectrum.basicOpen (X : k[X]))
    ((RelativeSchemeValuedPoint.basePoint_mem_basicOpen_iff _).mpr gaussModel_parameter_ne_zero)
    (gaussProductPoint x)

/-- The actual original source ideal's intrinsic norm at its true lifted proper center. -/
def gaussModificationIdealNorm [IsProper μ] (I : Z.IdealSheafData) (x : ProjBerk k n) : ℝ≥0∞ :=
  RelativeSchemeValuedPoint.modelIdealNorm I gaussModelCoefficient_le_one (gaussModificationPoint μ x)

/-- The actual original source ideal's intrinsic extended logarithm at its true lifted proper center. -/
def gaussModificationIdealLog [IsProper μ] (I : Z.IdealSheafData) (x : ProjBerk k n) : EReal :=
  RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (gaussModificationPoint μ x)

/-- Every actual source ideal has a continuous intrinsic lifted model norm, with Noetherianity derived from the actual proper map. -/
@[fun_prop]
theorem continuous_gaussModificationIdealNorm [IsProper μ] (I : Z.IdealSheafData) :
    Continuous (gaussModificationIdealNorm μ I) := by
  let : IsLocallyNoetherian Z := gaussModificationSource_isLocallyNoetherian μ
  exact (RelativeSchemeValuedPoint.continuous_modelIdealNorm_of_isLocallyNoetherian I
    gaussModelCoefficient_le_one).comp (continuous_gaussModificationPoint μ)

/-- Every actual source ideal has a continuous intrinsic lifted model logarithm, including zero ideals and negative infinity. -/
@[fun_prop]
theorem continuous_gaussModificationIdealLog [IsProper μ] (I : Z.IdealSheafData) :
    Continuous (gaussModificationIdealLog μ I) :=
  ENNReal.continuous_log.comp (continuous_gaussModificationIdealNorm μ I)

/-- The actual proper center of the entire lifted point maps to the original true Gauss product center. -/
theorem center_gaussModificationPoint [IsProper μ] (x : ProjBerk k n) :
    μ (RelativeSchemeValuedPoint.center gaussModelCoefficient_le_one (gaussModificationPoint μ x)) =
      RelativeSchemeValuedPoint.center gaussModelCoefficient_le_one (gaussProductPoint x) := by
  rw [← map_gaussModificationPoint μ x]
  exact RelativeSchemeValuedPoint.center_map μ rfl gaussModelCoefficient_le_one _

/-- Genuine geometric pullback of an arbitrary original product ideal preserves its entire intrinsic norm at the actual lifted point. -/
theorem gaussModificationIdealNorm_comap [IsProper μ]
    (I : (NativePolynomialLineProduct k n).IdealSheafData) (x : ProjBerk k n) :
    gaussModificationIdealNorm μ (I.comap μ) x =
      RelativeSchemeValuedPoint.modelIdealNorm I gaussModelCoefficient_le_one (gaussProductPoint x) := by
  have h := RelativeSchemeValuedPoint.modelIdealNorm_comap
    (fX := gaussModificationStructure μ) (fY := nativePolynomialLineProductStructure)
    I μ rfl gaussModelCoefficient_le_one (gaussModificationPoint μ x)
  exact h.trans (congrArg (RelativeSchemeValuedPoint.modelIdealNorm I gaussModelCoefficient_le_one)
    (map_gaussModificationPoint μ x))

/-- Genuine geometric pullback preserves the original product ideal's logarithm without any source ideal descent assertion. -/
theorem gaussModificationIdealLog_comap [IsProper μ]
    (I : (NativePolynomialLineProduct k n).IdealSheafData) (x : ProjBerk k n) :
    gaussModificationIdealLog μ (I.comap μ) x =
      RelativeSchemeValuedPoint.modelIdealLog I gaussModelCoefficient_le_one (gaussProductPoint x) :=
  congrArg ENNReal.log (gaussModificationIdealNorm_comap μ I x)

/-- Actual pulled-back product ideals retain their entire original old polynomial Gauss ideal norm on the genuine proper modification. -/
theorem gaussModificationIdealNorm_comap_eq_phiNorm [IsProper μ]
    (I : (NativePolynomialLineProduct k n).IdealSheafData) (x : ProjBerk k n) :
    gaussModificationIdealNorm μ (I.comap μ) x =
      phiNorm ((nativePolynomialLineProductRepresentative I).toIdeal.map
        (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x :=
  (gaussModificationIdealNorm_comap μ I x).trans (modelIdealNorm_gaussProductPoint_eq_phiNorm I x)

/-- Actual pulled-back product ideals retain their entire original old phi logarithm on the genuine proper modification. -/
theorem gaussModificationIdealLog_comap_eq_phiIdeal [IsProper μ]
    (I : (NativePolynomialLineProduct k n).IdealSheafData) (x : ProjBerk k n) :
    gaussModificationIdealLog μ (I.comap μ) x =
      phiIdeal ((nativePolynomialLineProductRepresentative I).toIdeal.map
        (polynomialCoefficientSwap k (Fin (n + 1))).toRingHom) x :=
  (gaussModificationIdealLog_comap μ I x).trans (modelIdealLog_gaussProductPoint_eq_phiIdeal I x)

end EnvelopeProperty.ProjBerk
