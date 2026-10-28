/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.PLIdealParameterScaling
import EnvelopeProperty.Projective.IdealBaseChange

/-!
# Actual invariant product ideals produced by rational FS data

The genuine finite parameter-monomial generators are retained in the output.
Their algebraic scaling identity proves whole-ideal unit invariance for the
very ideals whose intrinsic model logarithms realize the FS function.
-/

open scoped Classical Polynomial NNReal ENNReal Topology
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace EnvelopeProperty.ProjBerk
variable {k : Type u} [Field k] {n : ℕ}
private local instance productModelProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := n)) :=
  nativePolynomialLineProductStructure_isProper
namespace FSData
variable {a : ℚ} (D : FSData k n a)

/-- Rational FS data construct an actual homogeneous finite monomial-generated
product ideal, invariant under every actual coefficient-unit parameter scaling,
with its exact full intrinsic Gauss model logarithm. -/
theorem exists_parameterInvariant_productIdeal_model (hD : D.IsRational) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (J : HomogeneousIdeal (ProjectiveGrading k[X] n)),
      J.toIdeal.FG ∧
      (∃ S : Finset (MvPolynomial (Fin (n + 1)) k × ℕ),
        (∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
        J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (S : Set (MvPolynomial (Fin (n + 1)) k × ℕ)))) ∧
      (∀ (R : Type u) [CommRing R] (φ : k →+* R) (u : Rˣ),
        (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom φ))).map
          (MvPolynomial.map (parameterScaleHom (u : R))) =
          J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom φ))) ∧
      ∀ v : ProjBerk k n,
      RelativeSchemeValuedPoint.modelIdealLog (nativePolynomialLineProductIdeal J)
        gaussModelCoefficient_le_one (gaussProductPoint v) =
        ((r : ℝ) : EReal) * D.eval v - ((C : ℝ) : EReal) := by
  obtain ⟨N, hN, C, e, he⟩ := D.exists_integral_model_weights hD
  let S := D.terms.image fun t => modelMonomial t.1 N (e t)
  have hS : ∀ F ∈ S, ∃ d : ℕ, F.IsHomogeneous d := by
    intro F hF
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hF
    exact ⟨D.deg * N, isHomogeneous_modelMonomial (D.isHomogeneous t ht) N (e t)⟩
  let S₀ := D.terms.image fun t => (t.1 ^ N, e t)
  have himage : (S : Set (MvPolynomial (Fin (n + 1)) k[X])) =
      (fun p => parameterMonomial p.1 p.2) ''
        (S₀ : Set (MvPolynomial (Fin (n + 1)) k × ℕ)) := by
    simp only [S, S₀, Finset.coe_image, Set.image_image]
    rfl
  have hspan : (productIdealOfGenerators S hS).toIdeal =
      Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
        (S₀ : Set (MvPolynomial (Fin (n + 1)) k × ℕ))) := congrArg Ideal.span himage
  refine ⟨D.m * N, Nat.mul_pos D.m_pos hN, C,
    productIdealOfGenerators S hS, productIdealOfGenerators_fg S hS,
    ⟨S₀, ?_, hspan⟩, ?_, fun v => ?_⟩
  · intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨D.deg * N, (D.isHomogeneous t ht).pow N⟩
  · intro R _inst φ u
    rw [hspan]
    exact parameterScale_span_baseChanged_monomials_eq φ u
      (S₀ : Set (MvPolynomial (Fin (n + 1)) k × ℕ))
  ·
    rw [modelIdealLog_productIdealOfGenerators S hS v]
    have hlog (t) (ht : t ∈ D.terms) :
        Berk.logAbs (polynomialCoefficientSwap k (Fin (n + 1))
          (modelMonomial t.1 N (e t))) (gaussExt v) =
        ((N : ℝ) : EReal) * termVal t v - ((C : ℝ) : EReal) := by
      rw [swap_modelMonomial, logAbs_C_mul_X_pow_gaussExt, logAbs_pow,
        termVal_def, ereal_coe_mul_add (Nat.cast_nonneg N)]
      have he' : -((e t : ℝ) : EReal) =
          (((N : ℝ) * t.2 - (C : ℝ) : ℝ) : EReal) := by
        rw [← EReal.coe_neg, he t ht]
        congr 1
        ring
      change ((N : ℝ) : EReal) * logAbs t.1 v - ((e t : ℝ) : EReal) = _
      simp only [sub_eq_add_neg]
      rw [he', EReal.coe_sub, EReal.coe_mul, sub_eq_add_neg]
      ac_rfl
    have hshift : (D.terms.sup fun t =>
        ((N : ℝ) : EReal) * termVal t v - ((C : ℝ) : EReal)) =
        (D.terms.sup fun t => ((N : ℝ) : EReal) * termVal t v) - ((C : ℝ) : EReal) := by
      exact (Finset.apply_sup_eq_sup_comp_of_linearOrder
        (fun x : EReal => x - ((C : ℝ) : EReal))
        (fun _ _ h => by
          simpa only [sub_eq_add_neg] using add_le_add_left h (-((C : ℝ) : EReal)))
        (by simp)).symm
    calc S.sup (fun F => Berk.logAbs (polynomialCoefficientSwap k (Fin (n + 1)) F)
          (gaussExt v)) = D.terms.sup (fun t =>
            ((N : ℝ) : EReal) * termVal t v - ((C : ℝ) : EReal)) := by
          dsimp only [S]
          rw [Finset.sup_image]
          exact Finset.sup_congr rfl hlog
      _ = ((N : ℝ) : EReal) * (D.terms.sup fun t => termVal t v) - ((C : ℝ) : EReal) := by
          rw [hshift, ereal_coe_mul_finset_sup (Nat.cast_pos.mpr hN)]
      _ = ((D.m * N : ℕ) : ℝ) * D.eval v - ((C : ℝ) : EReal) := by
          rw [D.eval_def, ereal_coe_mul_coe_mul]
          have hc : ((D.m * N : ℕ) : ℝ) * (D.m : ℝ)⁻¹ = (N : ℝ) := by
            push_cast
            field_simp [D.m_ne_zero]
          rw [hc]

end FSData
end EnvelopeProperty.ProjBerk

namespace EnvelopeProperty.ProjSubvariety
variable {k : Type u} [Field k] {M : ℕ} {X : ProjSubvariety k M}
open ProjBerk
private local instance productModelProper :
    IsProper (nativePolynomialLineProductStructure (R := k) (n := M)) :=
  nativePolynomialLineProductStructure_isProper

/-- Actual finite FS data construct a genuine vertical homogeneous ideal with
retained finite parameter-monomial generators and universal coefficient-extended
unit-scaling invariance, preserving the exact full Gauss model logarithm. -/
theorem IsFiniteFS.exists_parameterInvariant_vertical_productIdeal_model {a : ℚ} {φ : X.an → ℝ}
    (hφ : X.IsFiniteFS a φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (J : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      J.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ J.toIdeal) ∧
      (∃ S : Finset (MvPolynomial (Fin (M + 1)) k × ℕ),
        (∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
        J.toIdeal = Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (S : Set (MvPolynomial (Fin (M + 1)) k × ℕ)))) ∧
      (∀ (R : Type u) [CommRing R] (f : k →+* R) (u : Rˣ),
        (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
          (MvPolynomial.map (parameterScaleHom (u : R))) =
          J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) ∧
      ∀ v : X.an, RelativeSchemeValuedPoint.modelIdealLog
        (nativePolynomialLineProductIdeal J) gaussModelCoefficient_le_one
        (gaussProductPoint v.1) = (((r : ℝ) * φ v - (C : ℝ) : ℝ) : EReal) := by
  have hφcont := hφ.continuous
  obtain ⟨D, hD, _hfin, heval⟩ := hφ
  obtain ⟨r, hr, C, J, _hfg, ⟨S₀, hS₀, hspan⟩, _hscale, hJ⟩ :=
    D.exists_parameterInvariant_productIdeal_model hD
  have hcont : Continuous fun v : X.an => (r : ℝ) * φ v - (C : ℝ) :=
    (continuous_const.mul hφcont).sub continuous_const
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨A, hA⟩ := exists_nat_gt (max B 0)
  have hApos : 0 < A := by
    have : (0 : ℝ) < A := lt_of_le_of_lt (le_max_right B 0) hA
    exact_mod_cast this
  have hbound (v : X.an) : -(A : ℝ) ≤ (r : ℝ) * φ v - (C : ℝ) := by
    have hb := hB v (Set.mem_univ v)
    rw [Real.norm_eq_abs] at hb
    have hBA : B ≤ (A : ℝ) := (le_max_left B 0).trans hA.le
    exact (neg_le_neg hBA).trans (neg_le_of_abs_le hb)
  let S₁ := insert (1, A) S₀
  have hspan₁ : (verticalTruncation J A).toIdeal =
      Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
        (S₁ : Set (MvPolynomial (Fin (M + 1)) k × ℕ))) := by
    rw [verticalTruncation, HomogeneousIdeal.toIdeal_sup, hspan]
    have hp : (parameterIdeal (k := k) (n := M) A).toIdeal =
        Ideal.span {MvPolynomial.C (Polynomial.X ^ A)} := by
      simp only [parameterIdeal, productIdealOfGenerators, Finset.coe_singleton]
    rw [hp]
    simp only [S₁, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
    have hm : parameterMonomial (1 : MvPolynomial (Fin (M + 1)) k) A =
        MvPolynomial.C (Polynomial.X ^ A) := by
      simp only [parameterMonomial, map_one, one_mul]
    rw [hm]
    exact sup_comm _ _
  refine ⟨r, hr, C, verticalTruncation J A, IsNoetherian.noetherian _,
    ⟨A, hApos, parameterPower_mem_verticalTruncation J A⟩,
    ⟨S₁, ?_, hspan₁⟩, ?_, fun v => ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨0, MvPolynomial.isHomogeneous_one _ _⟩
    · exact hS₀ q hq
  · intro R _inst φ u
    rw [hspan₁]
    exact parameterScale_span_baseChanged_monomials_eq φ u
      (S₁ : Set (MvPolynomial (Fin (M + 1)) k × ℕ))
  · rw [modelIdealLog_verticalTruncation, hJ, ← heval, ← EReal.coe_mul, ← EReal.coe_sub]
    apply max_eq_left
    exact_mod_cast hbound v

/-- The actual PL construction retains universal whole-ideal invariance of
both produced vertical ideals, including after arbitrary coefficient extension.
No equivariance is inferred from the equality of model functions. -/
theorem IsPL.exists_parameterInvariant_vertical_productIdeal_models {φ : X.an → ℝ}
    (hφ : X.IsPL φ) :
    ∃ (r : ℕ) (_ : 0 < r) (C : ℤ)
      (I J : HomogeneousIdeal (ProjectiveGrading k[X] M)),
      I.toIdeal.FG ∧ J.toIdeal.FG ∧
      (∃ A : ℕ, 0 < A ∧ MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal) ∧
      (∃ B : ℕ, 0 < B ∧ MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) ∧
      (∀ (R : Type u) [CommRing R] (f : k →+* R) (u : Rˣ),
        (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
          (MvPolynomial.map (parameterScaleHom (u : R))) =
          I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) ∧
      (∀ (R : Type u) [CommRing R] (f : k →+* R) (u : Rˣ),
        (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
          (MvPolynomial.map (parameterScaleHom (u : R))) =
          J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))) ∧
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
  obtain ⟨r₁, hr₁, C₁, I₀, _hfgI, ⟨A, hA, hAI⟩, _hSI, hscaleI, hI⟩ :=
    hα.exists_parameterInvariant_vertical_productIdeal_model
  obtain ⟨r₂, hr₂, C₂, J₀, _hfgJ, ⟨B, hB, hBJ⟩, _hSJ, hscaleJ, hJ⟩ :=
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
  · intro R _inst f u
    change ((I₀.toIdeal ^ r₂).map _).map _ = (I₀.toIdeal ^ r₂).map _
    simp only [Ideal.map_pow, hscaleI]
  · intro R _inst f u
    change ((J₀.toIdeal ^ r₁).map _).map _ = (J₀.toIdeal ^ r₁).map _
    simp only [Ideal.map_pow, hscaleJ]
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
