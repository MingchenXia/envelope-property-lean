/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierRatioOffSupport
import EnvelopeProperty.Local.PLIdealRatioModels

/-!
# Actual whole noncentral trivialization of the constructed ratio line sheaf

True parameter powers confine the actual Cartier supports to the central
fibre, and the original ideal inclusions give the genuine entire D(t)
module pullback trivialization. No model metric/polarization is claimed.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The entire actual noncentral open of the same original simultaneous blowup. -/
def simultaneousNoncentralOpen (I L : X.NativeProductModel.IdealSheafData) :
    (X.simultaneousIdealBlowup I L).Opens :=
  X.simultaneousIdealBlowupStructure I L ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : k[X])

/-- Actual parameter powers construct the genuine whole noncentral
pullback-unit trivialization of the original ratio line sheaf. -/
def simultaneousRatioModuleParameterIso
    (I L : HomogeneousIdeal (ProjectiveGrading k[X] M)) (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ L.toIdeal) :
    (Scheme.Modules.pullback (X.simultaneousNoncentralOpen
      (X.nativeProductIdeal I) (X.nativeProductIdeal L)).ι).obj
        (X.simultaneousRatioModelSheaf (X.nativeProductIdeal I) (X.nativeProductIdeal L)) ≅
      Scheme.Modules.unitObj (X.simultaneousNoncentralOpen
        (X.nativeProductIdeal I) (X.nativeProductIdeal L)).toScheme := by
  let π := X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal L)
  refine ((X.nativeProductIdeal I).comap π).ratioPullbackUnitIsoOfLeComplSupport
    ((X.nativeProductIdeal L).comap π)
      (X.simultaneousNoncentralOpen (X.nativeProductIdeal I) (X.nativeProductIdeal L)) ?_ ?_
  · intro y hy
    rw [Scheme.IdealSheafData.support_comap]
    exact X.parameterOpen_le_compl_nativeProductIdeal_support I A hA hy
  · intro y hy
    rw [Scheme.IdealSheafData.support_comap]
    exact X.parameterOpen_le_compl_nativeProductIdeal_support L B hB hy

variable {X} in
/-- Actual PL input produces the same genuine invertible ratio model with an
actual whole D(t) pullback trivialization, retaining all original finite
ideals, action, whole noncentral projection iso and lifted intrinsic log data. -/
theorem IsPL.exists_noncentralInvertibleRatio_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
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
      Scheme.Modules.IsInvertible (X.simultaneousRatioModelSheaf I' L') ∧
      Nonempty ((Scheme.Modules.pullback (X.simultaneousNoncentralOpen I' L').ι).obj
        (X.simultaneousRatioModelSheaf I' L') ≅
          Scheme.Modules.unitObj (X.simultaneousNoncentralOpen I' L').toScheme) ∧
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog
          (I'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) -
        RelativeSchemeValuedPoint.modelIdealLog
          (L'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hfin, hMod, hIso, hratio, hlog⟩ :=
    hφ.exists_verticalInvertibleRatio_models
  obtain ⟨A, hA, hAmem⟩ := hAI
  obtain ⟨B, hB, hBmem⟩ := hBL
  exact ⟨r, hr, C, I, L, hfgI, hfgL, ⟨A, hA, hAmem⟩, ⟨B, hB, hBmem⟩,
    hfin, hMod, hIso, hratio, ⟨X.simultaneousRatioModuleParameterIso I L A B hAmem hBmem⟩, hlog⟩

end EnvelopeProperty.ProjSubvariety
