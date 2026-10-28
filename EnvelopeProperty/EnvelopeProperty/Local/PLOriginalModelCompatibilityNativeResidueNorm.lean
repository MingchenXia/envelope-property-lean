import EnvelopeProperty.Berkovich.SchemeLineModelResiduePullbackNorm
import EnvelopeProperty.Global.NativeTestConfigurationIntrinsicNormFactor

/-! # The actual native transition factor computes arbitrary original residue vectors -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Scheme.Modules
open scoped NNReal Classical
noncomputable section
universe u

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
open SchemeModuleFrameCoefficients

/-- The unit section of the generic frame induced by a proper-center frame has model norm
one. -/
theorem modelLineNorm_centerFrameGenericIso_unitSection {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Z : Scheme.{u}} {p : Z ⟶ Spec (.of R)} [IsProper p]
    (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v p) {M : Z.Modules}
    (hM : IsInvertible M)
    (e : centerLineModule hb y M ≅ unitObj (Spec (.of (CenterRing y)))) :
    modelLineNorm hb y hM (unitSection (centerFrameGenericIso hb y e)) = 1 := by
  rw [modelLineNorm_eq_frame hb y hM e]
  change y.1.residueVal ((Scheme.ΓSpecIso (Z.residueField y.1.point)).hom
    (coefficient (centerFrameGenericIso hb y e) (unitSection (centerFrameGenericIso hb y e)))) = 1
  rw [coefficient_unitSection, map_one, map_one]

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich Berkovich.RelativeSchemeValuedPoint
open Berkovich.SchemeFramedSectionPullback Berkovich.SchemeResidueFrameComparison
open SchemeModuleFrameCoefficients

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (C : TestConfiguration k X)
private local instance actualTargetProper : IsProper C.projection := C.projection_isProper

variable (M : C.total.Modules) (hM : IsInvertible M)
  (r : ℝ≥0) (hr : 0 < r) (hru : r ≤ 1)
  (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.hom)

/-- The exact proper-center target frame used by the native factor has
true model norm one on its arbitrary original residue-fibre unit vector. -/
theorem gaussCompatibleTargetFrame_residue_unit_norm :
    modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru)
      (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hM
      (unitSection (C.gaussCompatibleTargetFrame M hM r hr hru x)) = 1 :=
  RelativeSchemeValuedPoint.modelLineNorm_centerFrameGenericIso_unitSection
    (Spectrum.trivialGaussValuation_le_one k r hru)
    (RelativeSchemeValuedPoint.map C.productTotalMap rfl (C.productGaussSource x r hr)) hM
    (C.gaussCompatibleCenterFrame M hM r hr hru x)

variable (L : X.left.Modules)
  (α : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
  (e₁ : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
  (U : X.left.Opens)
  (hy : (C.productGaussSource x r hr).1.point ∈
      (fst X (ProjBerk.nativeMultiplicativeGroup k)).left ⁻¹ᵁ U)
  (eU : (pullback U.ι).obj L ≅ unitObj U.toScheme)

/-- The ACTUAL native transition factor computes every arbitrary original
residue vector, with no global section extension or norm-matching premise. -/
theorem gaussCompatibleNormFactor_residue_formula :
    let y := C.productGaussSource x r hr
    let z := RelativeSchemeValuedPoint.map C.productTotalMap rfl y
    ∀ s : Γ(genericLineModule z M, ⊤),
      modelLineNorm (Spectrum.trivialGaussValuation_le_one k r hru) z hM s =
        C.gaussCompatibleNormFactor M hM r hr hru x L α e₁ U hy eU *
          y.1.residueVal ((Scheme.ΓSpecIso
            (.of ((X ⊗ ProjBerk.nativeMultiplicativeGroup k).left.residueField y.1.point))).hom
              ((productReferenceResidueFrame L y.1 U hy eU).hom.app ⊤
                (transportedResidueSection C.productTotalMap
                  (C.productTotalLineIso M L α e₁) y.1 s))) := by
  intro y z s
  let e := C.gaussCompatibleTargetFrame M hM r hr hru x
  have h := modelLineNorm_framedResiduePullback
    (Spectrum.trivialGaussValuation_le_one k r hru) C.productTotalMap y hM
    (C.productTotalLineIso M L α e₁) e s
  rw [C.gaussCompatibleTargetFrame_residue_unit_norm M hM r hr hru x, mul_one] at h
  have ht := transitionUnit_coefficient_value
    (productReferenceResidueFrame L y.1 U hy eU)
    (C.productModelResidueFrame M L α e₁ y.1 e) y.1.residueVal
    (transportedResidueSection C.productTotalMap (C.productTotalLineIso M L α e₁) y.1 s)
  exact h.trans ht

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
