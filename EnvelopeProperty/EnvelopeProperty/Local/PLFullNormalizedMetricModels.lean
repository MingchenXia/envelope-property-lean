import EnvelopeProperty.Local.PLNormalizedFullPointRatioMetric

/-! # Original PL data construct the whole actual normal ratio-model metric -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- ORIGINAL PL data construct the SAME actual original normal proper ratio
model whose TRUE canonical ratio-section weight recovers the original PL
function at EVERY actual model point. All nonvanishing/finiteness at all
points is derived from retained original monomial ideal generators. -/
theorem IsPL.exists_full_normalizedRatioMetric_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ) (I J : X.NativeProductModel.IdealSheafData)
      (hfinAll : ∀ z : RelativeSchemeValuedPoint
          (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
        modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
        modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥),
      let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
      ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
          (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
        (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
          X.normalizedSimultaneousRatioWeightAt I J hfin y
            (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 +
              ((C : ℝ) : EReal) := by
  obtain ⟨r,hr,C,I,J,_hfgI,_hfgJ,_hvI,_hvJ,_hSI,_hSJ,hAll⟩ :=
    hφ.exists_allProductPoint_monomial_models X
  refine ⟨r,hr,C,X.nativeProductIdeal I,X.nativeProductIdeal J,fun z => (hAll z).1,?_⟩
  intro hfin y
  rw [X.normalizedSimultaneousRatioWeightAt_eq]
  exact (hAll _).2
end EnvelopeProperty.ProjSubvariety
