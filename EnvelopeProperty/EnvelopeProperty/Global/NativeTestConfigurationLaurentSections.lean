import EnvelopeProperty.Global.NativeTestConfigurationWholeOpenSections
import EnvelopeProperty.Global.NativeTestConfigurationGaussPoint
import EnvelopeProperty.Global.NativeTestConfigurationReduced
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading
import EnvelopeProperty.AlgGeom.SchemeModuleLaurentCoefficients

/-! # Actual whole original Laurent coefficients of every original TC global section -/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial Classical NNReal
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Scheme.Modules CanonicalGeometry
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X)

include C in
private theorem originalCompact : CompactSpace X.left := by
  let : IsProper X.hom := C.original_isProper
  exact QuasiCompact.compactSpace_of_compactSpace X.hom

include C in
private theorem originalSeparated : X.left.IsSeparated := by
  let : IsProper X.hom := C.original_isProper
  rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from X.hom]
  infer_instance

/-- The ACTUAL whole original map from the genuine product into the total TC. -/
def productTotalMap : (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left ⟶ C.total :=
  C.unitOpenIso.inv.left ≫ C.unitOpenInclusion.left

/-- The map sends the WHOLE genuine product Gauss point to the SAME actual total Gauss point. -/
theorem productTotalMap_gaussPoint {v : Valuation k ℝ≥0}
    (x : Berkovich.RelativeSchemeValuedPoint v X.hom) (r : ℝ≥0) (hr : 0 < r) :
    Berkovich.SchemeValuedPoint.map C.productTotalMap
      (Berkovich.SchemePointLaurentGauss.productPoint X.hom x r hr).1 =
      C.totalGaussPoint x r hr :=
  Berkovich.SchemeValuedPoint.map_comp C.unitOpenIso.inv.left C.unitOpenInclusion.left _

variable (M : C.total.Modules) (L : X.left.Modules)
    (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅
      (pullback C.fibreOneIso.hom.left).obj L)

/-- Original action/fibre data construct the WHOLE actual product pullback line-power iso. -/
def productTotalLinePowerIso (n : ℕ) :
    (pullback C.productTotalMap).obj (bundleTensorPower M n) ≅
      (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left).obj
        (bundleTensorPower L n) :=
  ((pullbackComp C.unitOpenIso.inv.left C.unitOpenInclusion.left).app
    (bundleTensorPower M n)).symm ≪≫
  (pullback C.unitOpenIso.inv.left).mapIso (C.unitOpenLinePowerIso M L α e₁ n) ≪≫
  (pullbackComp C.unitOpenIso.inv.left C.unitOpenOriginalProjection.left).app
    (bundleTensorPower L n) ≪≫
  (pullbackCongr C.unitOpenIso_inv_originalProjection).app (bundleTensorPower L n)

/-- Every actual original total-space section transports by the actual native map and line iso. -/
def globalProductPowerSection (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    SchemeModuleLaurentCoefficients.pulledSections X.hom (bundleTensorPower L n) :=
  (C.productTotalLinePowerIso M L α e₁ n).hom.app ⊤
    (affinePullbackUnitTop C.productTotalMap (bundleTensorPower M n) s)

variable (hL : IsInvertible L)


/-- The genuine original action/fibre data derive EVERY original integer Laurent coefficient. -/
def globalPowerLaurentCoefficients (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    ℤ →₀ AffineModuleFlatBaseChange.sections X.hom (bundleTensorPower L n) := by
  letI : CompactSpace X.left := originalCompact C
  letI : X.left.IsSeparated := originalSeparated C
  letI : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  exact SchemeModuleLaurentCoefficients.coefficients X.hom (bundleTensorPower L n)
    (C.globalProductPowerSection M L α e₁ n s)

/-- Every original total section has its actual monomial reconstruction in whole original sections. -/
theorem globalProductPowerSection_eq_sum (n : ℕ) (s : Γ(bundleTensorPower M n, ⊤)) :
    C.globalProductPowerSection M L α e₁ n s =
      (C.globalPowerLaurentCoefficients M L α e₁ hL n s).sum (fun i m =>
        (ProperBirationalSections.coefficientMap
          (FlatGlobalSections.structureMap (S := k[T;T⁻¹]) X.hom)
          (LaurentPolynomial.T i)) • affinePullbackUnitTop
            (FlatGlobalSections.firstProjection (S := k[T;T⁻¹]) X.hom)
            (bundleTensorPower L n) m) :=
by
  let : CompactSpace X.left := originalCompact C
  let : X.left.IsSeparated := originalSeparated C
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  exact SchemeModuleLaurentCoefficients.eq_sum_monomial X.hom (bundleTensorPower L n) _

/-- One actual finite original product-section family is chosen before all points and radii. -/
def globalProductPowerFamily (n : ℕ) (G : Finset Γ(bundleTensorPower M n, ⊤)) :
    Finset (SchemeModuleLaurentCoefficients.pulledSections X.hom (bundleTensorPower L n)) :=
  G.image (C.globalProductPowerSection M L α e₁ n)

/-- One actual finite original coefficient/weight family is chosen before all evaluations. -/
def globalPowerLaurentTerms (n : ℕ) (G : Finset Γ(bundleTensorPower M n, ⊤)) :
    Finset (AffineModuleFlatBaseChange.sections X.hom (bundleTensorPower L n) × ℤ) := by
  letI : CompactSpace X.left := originalCompact C
  letI : X.left.IsSeparated := originalSeparated C
  letI : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  exact SchemeModuleLaurentCoefficients.terms X.hom (bundleTensorPower L n)
    (C.globalProductPowerFamily M L α e₁ n G)

/-- EVERY original coefficient in the original family support occurs in that SAME finite pair family. -/
theorem globalPowerLaurentCoefficient_mem_terms (n : ℕ)
    (G : Finset Γ(bundleTensorPower M n, ⊤)) (s : Γ(bundleTensorPower M n, ⊤)) (hs : s ∈ G)
    (i : ℤ) (hi : i ∈ (C.globalPowerLaurentCoefficients M L α e₁ hL n s).support) :
    (C.globalPowerLaurentCoefficients M L α e₁ hL n s i, i) ∈
      C.globalPowerLaurentTerms M L α e₁ hL n G := by
  let : CompactSpace X.left := originalCompact C
  let : X.left.IsSeparated := originalSeparated C
  let : (bundleTensorPower L n).IsQuasicoherent :=
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n).isQuasicoherent
  apply Finset.mem_biUnion.mpr
  refine ⟨C.globalProductPowerSection M L α e₁ n s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
