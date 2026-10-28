/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierIdealModules
import EnvelopeProperty.Local.PLIdealGmCategoricalModels
import EnvelopeProperty.Local.PLIdealCentralSupport

/-!
# Actual rank-one Cartier module sheaves on the same original PL model

Both genuine ideal sheaves on the actual product blowup are actual locally
free rank-one sheaves in the existing module interface. Their actual regular
local equations give the intrinsic Gauss model logarithm. The final PL-only
producer retains the same vertical ideals and original categorical group action.

The tensor/dual polarization, linearization, normalization and nefness remain
further geometric obligations.
-/

open scoped Classical Polynomial LaurentPolynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}

/-- The same actual regular equation trivializes the actual module sheaf and
computes the entire intrinsic model logarithm at the actual valued point. -/
theorem exists_regular_generator_moduleIso_modelIdealLog [IsProper f]
    (I : Y.IdealSheafData) (hI : I.IsInvertible) (hb : ∀ r, v r ≤ 1)
    (y : RelativeSchemeValuedPoint v f) :
    ∃ (U : Y.affineOpens) (hc : center hb y ∈ U.1) (g : Γ(Y, U))
      (_hg : g ∈ nonZeroDivisors Γ(Y, U)) (_hgen : I.ideal U = Ideal.span {g}),
      Nonempty (SheafOfModules.unit (Spec Γ(Y, U)).ringCatSheaf ≅
        I.toModules.restrict U.2.fromSpec) ∧
      modelIdealLog I hb y =
        ENNReal.log (SchemeValuedPoint.eval y.1 U.1
          (support_mem_of_center_mem hb y U.1 hc) g : ℝ≥0∞) := by
  obtain ⟨U, hc, g, hg, hgen, hlog⟩ := exists_regular_generator_modelIdealLog I hI hb y
  exact ⟨U, hc, g, hg, hgen, ⟨I.regularGeneratorModuleIso U g hg hgen⟩, hlog⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : X.NativeProductModel.IdealSheafData)

/-- The genuine module sheaf of the first actual ideal on the original blowup. -/
def simultaneousFirstModelSheaf : (X.simultaneousIdealBlowup I J).Modules :=
  (I.comap (X.simultaneousIdealBlowupProjection I J)).toModules

/-- The genuine module sheaf of the second actual ideal on the original blowup. -/
def simultaneousSecondModelSheaf : (X.simultaneousIdealBlowup I J).Modules :=
  (J.comap (X.simultaneousIdealBlowupProjection I J)).toModules

/-- Both actual sheaves are locally free with the actual singleton generator
charts constructed from their regular local equations. -/
theorem simultaneousModelSheaves_isLocallyFree :
    SheafOfModules.IsLocallyFree (R := (X.simultaneousIdealBlowup I J).ringCatSheaf)
        (X.simultaneousFirstModelSheaf I J) ∧
      SheafOfModules.IsLocallyFree (R := (X.simultaneousIdealBlowup I J).ringCatSheaf)
        (X.simultaneousSecondModelSheaf I J) := by
  have hi := X.simultaneousIdealBlowup_isInvertible I J
  exact ⟨hi.1.isLocallyFree_toModules _, hi.2.isLocallyFree_toModules _⟩

private local instance productModelProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper

/-- Original PL data alone produce the same actual finite vertical ideals,
original categorical Gm action, actual rank-one ideal module sheaves, full
nonzero-parameter isomorphism and exact formula on the genuine Gauss lifts. -/
theorem IsPL.exists_verticalLocallyFreeIdeal_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I L : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ L.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ L.toIdeal) ∧
      let I' := X.nativeProductIdeal I
      let L' := X.nativeProductIdeal L
      ∃ (hfin : ∀ w : X.an,
        RelativeSchemeValuedPoint.modelIdealLog I' gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog L' gaussModelCoefficient_le_one
          (X.nativeProductGaussPoint w) ≠ ⊥),
      Nonempty (ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I L)) ∧
      IsIso (X.simultaneousIdealBlowupProjection I' L' ∣_
        (X.nativeProductStructure ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X]))) ∧
      SheafOfModules.IsLocallyFree (R := (X.simultaneousIdealBlowup I' L').ringCatSheaf)
        (X.simultaneousFirstModelSheaf I' L') ∧
      SheafOfModules.IsLocallyFree (R := (X.simultaneousIdealBlowup I' L').ringCatSheaf)
        (X.simultaneousSecondModelSheaf I' L') ∧
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog
          (I'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) -
        RelativeSchemeValuedPoint.modelIdealLog
          (L'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hfin, hlog, hMod, _e, _he⟩ :=
    hφ.exists_verticalIdeal_models_with_categoricalGmAction
  have hfin' : ∀ w : X.an,
      RelativeSchemeValuedPoint.modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      RelativeSchemeValuedPoint.modelIdealLog (X.nativeProductIdeal L) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ := by
    intro w
    simpa only [X.modelIdealLog_nativeProductIdeal] using hfin w
  obtain ⟨A, hA, hAmem⟩ := hAI
  obtain ⟨B, hB, hBmem⟩ := hBL
  have hfree := X.simultaneousModelSheaves_isLocallyFree (X.nativeProductIdeal I) (X.nativeProductIdeal L)
  refine ⟨r, hr, C, I, L, hfgI, hfgL, ⟨A, hA, hAmem⟩, ⟨B, hB, hBmem⟩, hfin', hMod,
    X.simultaneousIdealBlowup_isIso_over_parameter_of_power_mem I L A B hAmem hBmem,
    hfree.1, hfree.2, fun w => ?_⟩
  simpa only [X.modelIdealLog_simultaneousIdealBlowup_comap,
    X.modelIdealLog_nativeProductIdeal] using hlog w

end EnvelopeProperty.ProjSubvariety
