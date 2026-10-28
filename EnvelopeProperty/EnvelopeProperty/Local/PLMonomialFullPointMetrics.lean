import EnvelopeProperty.Local.PLProductPointRestriction
import EnvelopeProperty.Local.PLIdealMonomialModels

/-! # True original PL ideal metrics at ALL native Gauss-base product points -/
open scoped Classical Polynomial NNReal ENNReal
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
private local instance ambientProductProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper
private local instance polynomialProper :
    IsProper (nativeStructureMap (R := k[X]) (n := M)) := nativeStructureMap_isProper

/-- The TRUE original pulled monomial ideal's logarithm at ANY native
Gauss-base product point equals its value at the actual Gauss lift of the
SAME whole original analytic restriction. No point is assumed monomial. -/
theorem modelIdealLog_nativeProductIdeal_monomial_restriction
    (J : HomogeneousIdeal (ProjectiveGrading k[X] M))
    (S : Finset (MvPolynomial (Fin (M+1)) k × ℕ))
    (hS : J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
      (S : Set (MvPolynomial (Fin (M+1)) k × ℕ))))
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      X.nativeProductStructure) :
    modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one y =
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint (X.nativeProductBaseRestriction y)) := by
  have hleft : modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one y =
      Spectrum.idealLog J.toIdeal (X.nativeProductNormalizedPoint y).1.1 := by
    have h := modelIdealLog_comap
      (fX := X.nativeProductStructure) (fY := nativePolynomialLineProductStructure)
      (nativePolynomialLineProductIdeal J) X.nativeProductInclusion rfl
      gaussModelCoefficient_le_one y
    change modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one y = _ at h
    rw [← X.nativePolynomialLineProductPoint_nativeProductNormalizedPoint,
      modelIdealLog_nativePolynomialLineProductPoint] at h
    exact h
  rw [hleft, X.modelIdealLog_nativeProductIdeal, gaussProductPoint,
    modelIdealLog_nativePolynomialLineProductPoint]
  have h := RelativeNormalizedProjectiveSpectrum.modelIdealLog_parameterMonomial_eq_GaussRestriction
    (1 : Valuation k ℝ≥0) gaussRadius gaussModelCoefficient_le_one J S hS
      (X.nativeProductNormalizedPoint y)
  rw [RelativeNormalizedProjectiveSpectrum.modelIdealLog_quotient_eq_idealLog,
    RelativeNormalizedProjectiveSpectrum.modelIdealLog_quotient_eq_idealLog] at h
  convert h using 1
  dsimp only [gaussModelPoint, nativeProductBaseRestriction]
  rw [Homeomorph.apply_symm_apply]

/-- ORIGINAL PL data alone produce actual finite monomial model ideals whose
TRUE native ideal logarithms recover the SAME original function at EVERY
Gauss-base product point, via its derived original analytic restriction.
Both logarithms are genuinely finite everywhere, not just at Gauss lifts. -/
theorem IsPL.exists_allProductPoint_monomial_models {φ : X.an → ℝ} (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ J.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X^A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X^B) ∈ J.toIdeal) ∧
      (∃ S : Finset (MvPolynomial (Fin (M+1)) k × ℕ),
        (∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
        I.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (S : Set (MvPolynomial (Fin (M+1)) k × ℕ)))) ∧
      (∃ S : Finset (MvPolynomial (Fin (M+1)) k × ℕ),
        (∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
        J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (S : Set (MvPolynomial (Fin (M+1)) k × ℕ)))) ∧
      ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
          X.nativeProductStructure,
        (modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one y ≠ ⊥ ∧
          modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one y ≠ ⊥) ∧
        (((r : ℝ)*φ (X.nativeProductBaseRestriction y) : ℝ) : EReal) =
          modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one y -
          modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one y +
            ((C : ℝ) : EReal) := by
  obtain ⟨r,hr,C,I,J,hfgI,hfgJ,hvI,hvJ,⟨SI,hSI,hspanI⟩,⟨SJ,hSJ,hspanJ⟩,hfin,heq⟩ :=
    hφ.exists_monomial_vertical_productIdeal_models
  refine ⟨r,hr,C,I,J,hfgI,hfgJ,hvI,hvJ,⟨SI,hSI,hspanI⟩,⟨SJ,hSJ,hspanJ⟩,?_⟩
  intro y
  rw [X.modelIdealLog_nativeProductIdeal_monomial_restriction I SI hspanI,
    X.modelIdealLog_nativeProductIdeal_monomial_restriction J SJ hspanJ,
    X.modelIdealLog_nativeProductIdeal, X.modelIdealLog_nativeProductIdeal]
  exact ⟨hfin _, heq _⟩
end EnvelopeProperty.ProjSubvariety
