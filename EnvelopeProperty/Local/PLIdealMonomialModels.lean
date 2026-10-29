import EnvelopeProperty.Local.PLIdealEquivariantData
import EnvelopeProperty.Local.ParameterMonomialPowers

/-! # Original PL model ideals with their true finite parameter-monomial generators -/
open scoped Classical Polynomial NNReal ENNReal
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}
open ProjBerk
private local instance productModelProper :
    AlgebraicGeometry.IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper

/-- ORIGINAL PL data produce actual vertical homogeneous model ideals with
finite ORIGINAL parameter-monomial generators retained after all powers.
Their true Gauss model logarithms are finite and recover the exact scaled
original PL function. No equivariance or monomial presentation is assumed. -/
theorem IsPL.exists_monomial_vertical_productIdeal_models {φ : X.an → ℝ}
    (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ J.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) ∧
      (∃ S : Finset (MvPolynomial (Fin (M + 1)) k × ℕ),
        (∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
        I.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (S : Set (MvPolynomial (Fin (M + 1)) k × ℕ)))) ∧
      (∃ S : Finset (MvPolynomial (Fin (M + 1)) k × ℕ),
        (∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
        J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (S : Set (MvPolynomial (Fin (M + 1)) k × ℕ)))) ∧
      (∀ v : X.an,
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal I)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) ≠ ⊥ ∧
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) ≠ ⊥) ∧
      ∀ v : X.an, (((r : ℝ) * φ v : ℝ) : EReal) =
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal I)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) -
        RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
          gaussModelCoefficient_le_one (gaussProductPoint v.1) + ((C : ℝ) : EReal) := by
  obtain ⟨a, b, α, β, hα, hβ, heq⟩ := isPL_iff.mp hφ
  obtain ⟨r₁, hr₁, C₁, I₀, _hfgI, ⟨A, hA, hAI⟩, ⟨SI, hSI, hspanI⟩, _hscaleI, hI⟩ :=
    hα.exists_parameterInvariant_vertical_productIdeal_model
  obtain ⟨r₂, hr₂, C₂, J₀, _hfgJ, ⟨B, hB, hBJ⟩, ⟨SJ, hSJ, hspanJ⟩, _hscaleJ, hJ⟩ :=
    hβ.exists_parameterInvariant_vertical_productIdeal_model
  refine ⟨r₁ * r₂, Nat.mul_pos hr₁ hr₂, (r₂ : ℤ) * C₁ - (r₁ : ℤ) * C₂,
    homogeneousIdealPow I₀ r₂, homogeneousIdealPow J₀ r₁,
    IsNoetherian.noetherian _, IsNoetherian.noetherian _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨A * r₂, Nat.mul_pos hA hr₂, ?_⟩
    change MvPolynomial.C (Polynomial.X ^ (A * r₂)) ∈ I₀.toIdeal ^ r₂
    simpa only [← map_pow, ← pow_mul] using Ideal.pow_mem_pow hAI r₂
  · refine ⟨B * r₁, Nat.mul_pos hB hr₁, ?_⟩
    change MvPolynomial.C (Polynomial.X ^ (B * r₁)) ∈ J₀.toIdeal ^ r₁
    simpa only [← map_pow, ← pow_mul] using Ideal.pow_mem_pow hBJ r₁
  · obtain ⟨T, hT, hpow⟩ := exists_parameterMonomial_span_pow SI hSI r₂
    exact ⟨T, hT, by change I₀.toIdeal ^ r₂ = _; rw [hspanI]; exact hpow⟩
  · obtain ⟨T, hT, hpow⟩ := exists_parameterMonomial_span_pow SJ hSJ r₁
    exact ⟨T, hT, by change J₀.toIdeal ^ r₁ = _; rw [hspanJ]; exact hpow⟩
  · intro v
    rw [modelIdealLog_homogeneousIdealPow, modelIdealLog_homogeneousIdealPow, hI, hJ,
      ← EReal.coe_mul, ← EReal.coe_mul]
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
  · intro v
    rw [modelIdealLog_homogeneousIdealPow, modelIdealLog_homogeneousIdealPow, hI, hJ,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    rw [heq v]
    push_cast
    ring

end EnvelopeProperty.ProjSubvariety
