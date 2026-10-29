/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.CartierRatioSheaves
import EnvelopeProperty.Local.PLIdealModelSheaves

/-!
# Actual ratio line sheaves on the same constructed PL models

The ratio is a genuine invertible module sheaf of the two actual Cartier
factors on the original simultaneous blowup. A model metric, O(r)
polarization, module-sheaf linearization and normality remain further work.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The genuine ratio line sheaf on the actual original simultaneous blowup. -/
def simultaneousRatioModelSheaf (I L : X.NativeProductModel.IdealSheafData) :
    (X.simultaneousIdealBlowup I L).Modules :=
  (I.comap (X.simultaneousIdealBlowupProjection I L)).ratioModule
    (L.comap (X.simultaneousIdealBlowupProjection I L))

/-- The actual simultaneous Cartier factors make their original tensor-dual
ratio a genuine invertible sheaf on this same original model. -/
theorem simultaneousRatioModelSheaf_isInvertible (I L : X.NativeProductModel.IdealSheafData) :
    Scheme.Modules.IsInvertible (X.simultaneousRatioModelSheaf I L) := by
  have h := X.simultaneousIdealBlowup_isInvertible I L
  exact h.1.isInvertible_ratioModule h.2

variable {X} in
/-- Original PL data construct actual same finite vertical ideals, actual
categorical action, whole D(t) isomorphism, genuine invertible ratio sheaf,
and the exact intrinsic Gauss formula on this original actual model. -/
theorem IsPL.exists_verticalInvertibleRatio_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
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
      ∀ w : X.an, (((r : ℝ) * φ w : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog
          (I'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) -
        RelativeSchemeValuedPoint.modelIdealLog
          (L'.comap (X.simultaneousIdealBlowupProjection I' L')) gaussModelCoefficient_le_one
          (X.simultaneousIdealBlowupGaussPoint I' L' w (hfin w).1 (hfin w).2) + ((C : ℝ) : EReal) := by
  obtain ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hfin, hMod, hIso, _hfreeI, _hfreeL, hlog⟩ :=
    hφ.exists_verticalLocallyFreeIdeal_models
  exact ⟨r, hr, C, I, L, hfgI, hfgL, hAI, hBL, hfin, hMod, hIso,
    X.simultaneousRatioModelSheaf_isInvertible _ _, hlog⟩

end EnvelopeProperty.ProjSubvariety
