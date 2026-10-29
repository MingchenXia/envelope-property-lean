/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroChartTestsEnvelope

/-!
# The original trivial point comes from an actual parameter-adic chart DVR

The parameter-adic valuation is constructed on the original `A_j[t]`.
Its original chart point equals the original trivial analytic point, so
the chart-order estimate also supplies the trivial-point estimate.
-/

open scoped NNReal ENNReal Topology Polynomial

noncomputable section

namespace EnvelopeProperty.ProjSubvariety

open IsDiscreteValuationRing
open ProjBerk (phiIdeal)

universe u

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

private instance chartParameter_prime (j : X.ChartIdx) :
    (Ideal.span {(Polynomial.X : X.ChartRing j.1)}).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

private instance chartParameter_noetherian (j : X.ChartIdx) :
    IsNoetherianRing (X.ChartRing j.1) :=
  Algebra.FiniteType.isNoetherianRing k (X.ChartRing j.1)

/-- The genuine original chart DVR `A_j[t]_(t)` inside its own function field. -/
def chartTAdicDVR (j : X.ChartIdx) : BirationalDVR k (X.ChartRing j.1) where
  ring := atPrimeRange (P := Ideal.span {(Polynomial.X : X.ChartRing j.1)})
    (IsScalarTower.toAlgHom k (X.ChartRing j.1) (FractionRing (X.ChartRing j.1)))
      (IsFractionRing.injective _ _)
  isDVR := isDiscreteValuationRing_atPrimeRange _ _ rfl Polynomial.X_ne_zero
  essFiniteType := essFiniteType_atPrimeRange _ _
  algebraMap_mem g := mem_atPrimeRange _ _ g

/-- The actual chart parameter-adic valuation computes a parameter power
times a polynomial with nonzero original constant term. -/
theorem chartTAdicDVR_ord_X_pow_mul (j : X.ChartIdx) (m : ℕ)
    {Q : X.ChartRing j.1} (hQ : Q.coeff 0 ≠ 0) :
    (X.chartTAdicDVR j).ord (Polynomial.X ^ m * Q) = m := by
  have hQ' : ¬ (Polynomial.X : X.ChartRing j.1) ∣ Q := by
    rw [Polynomial.X_dvd_iff]
    exact hQ
  have : IsDiscreteValuationRing (atPrimeRange (P := Ideal.span {(Polynomial.X : X.ChartRing j.1)})
      (IsScalarTower.toAlgHom k (X.ChartRing j.1) (FractionRing (X.ChartRing j.1)))
      (IsFractionRing.injective _ _)) := (X.chartTAdicDVR j).isDVR
  exact addVal_atPrimeRange _ _ rfl Polynomial.X_ne_zero m hQ'

/-- Every whole nonzero original chart polynomial has the actual order of
its lowest nonzero parameter coefficient. -/
theorem chartTAdicDVR_ord (j : X.ChartIdx) {F : X.ChartRing j.1} (hF : F ≠ 0) :
    (X.chartTAdicDVR j).ord F = F.natTrailingDegree := by
  obtain ⟨Q, hQ⟩ : Polynomial.X ^ F.natTrailingDegree ∣ F :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd =>
      Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hQ0 : Q.coeff 0 ≠ 0 := by
    have h := Polynomial.coeff_X_pow_mul Q F.natTrailingDegree 0
    rw [zero_add, ← hQ] at h
    rw [← h]
    exact mt Polynomial.trailingCoeff_eq_zero.mp hF
  conv_lhs => rw [hQ]
  exact chartTAdicDVR_ord_X_pow_mul X j _ hQ0

/-- Every nonzero original chart coefficient has parameter-adic order zero. -/
theorem chartTAdicDVR_ord_C (j : X.ChartIdx) {a : X.ChartAlg j.1} (ha : a ≠ 0) :
    (X.chartTAdicDVR j).ord (Polynomial.C a) = 0 := by
  have h := chartTAdicDVR_ord_X_pow_mul X j 0 (Q := Polynomial.C a) (by simpa using ha)
  simpa using h

/-- The entire original chart parameter-adic valuation satisfies the actual
torus identity with positive parameter order one, including the zero polynomial. -/
theorem chartTAdicDVR_torus (j : X.ChartIdx) (F : X.ChartRing j.1) :
    (X.chartTAdicDVR j).ord F = F.support.inf fun ℓ =>
      (X.chartTAdicDVR j).ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * 1 : ℕ) : ℕ∞) := by
  by_cases hF : F = 0
  · simp [hF]
  rw [chartTAdicDVR_ord X j hF]
  apply le_antisymm
  · apply Finset.le_inf
    intro ℓ hℓ
    rw [chartTAdicDVR_ord_C X j (Polynomial.mem_support_iff.mp hℓ), zero_add, mul_one]
    exact_mod_cast Polynomial.natTrailingDegree_le_of_mem_supp ℓ hℓ
  · have hmem := Polynomial.natTrailingDegree_mem_support_of_nonzero hF
    refine (Finset.inf_le (f := fun ℓ =>
      (X.chartTAdicDVR j).ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * 1 : ℕ) : ℕ∞)) hmem).trans ?_
    rw [chartTAdicDVR_ord_C X j (Polynomial.mem_support_iff.mp hmem), zero_add, mul_one]

/-- The actual original parameter-adic chart point is the actual original
trivial point of the same projective analytification. -/
theorem chartDivPoint_chartTAdicDVR_eq_triv (j : X.ChartIdx) :
    X.chartDivPoint j.1 (X.chartTAdicDVR j) 1 = X.triv := by
  classical
  apply Subtype.ext
  by_contra hne
  obtain ⟨d, s, hs, hval⟩ := ProjBerk.exists_isHomogeneous_val_ne hne
  apply hval
  by_cases hI : s ∈ X.ideal
  · rw [(X.chartDivPoint j.1 (X.chartTAdicDVR j) 1).2 s hI, X.triv.2 s hI]
  · have hdehom : X.quotDehom j.1 s ≠ 0 := (quotDehom_eq_zero_iff hs).not.mpr hI
    rw [chartDivPoint_val_of_isHomogeneous (X.chartTAdicDVR j) 1 hs,
      chartTAdicDVR_ord_C X j hdehom, expOrd_zero, triv_val_of_notMem X hI]

variable {X}
variable {B : ℕ → Ideal X.ConeRing} {d c : ℕ} {φ : X.an → ℝ}

/-- Actual chart DVR estimates already include the original trivial point;
the parameter-adic chart witness and its exact point identity are produced
internally, rather than supplied as an extra trivial-point hypothesis. -/
theorem isPSH_envelope_of_polynomialConeIdealOnlyChartEstimates [IsAlgClosed k]
    (hgen : ∀ m : ℕ, 0 < m →
      X.HasBoundedPolynomialConeGenerators (B m) (m * d + c))
    (hinc : ∀ m : ℕ, 0 < m → X.coneObstacleIdeal d φ m ≤ B m)
    (hsub : ∀ m l : ℕ, 0 < m → 0 < l → B (m * l) ≤ X.saturation (B m ^ l))
    (hchart : ∀ (j : X.ChartIdx) (V : BirationalDVR k (X.ChartRing j.1)) (b : ℕ),
      0 < b → (∀ F : X.ChartRing j.1, V.ord F = F.support.inf fun ℓ =>
        V.ord (Polynomial.C (F.coeff ℓ)) + ((ℓ * b : ℕ) : ℕ∞)) →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, 0 < m → ∃ q : ℕ, 0 < q ∧
        X.coneIdealPotential (B m) (X.chartDivPoint j.1 V b) ≤
          (((m : ℝ) / q : ℝ) : EReal) *
            phiIdeal (X.obstacleIdeal d φ q) (X.chartDivPoint j.1 V b).1 + (A : EReal))
    (hd : 0 < d) (hφ : X.IsPL φ) (hφ0 : ∀ v, φ v ≤ 0) :
    X.IsPSH (d : ℝ) (X.envelope (d : ℝ) fun v => (φ v : EReal)) := by
  obtain ⟨j, hj⟩ := X.exists_X_notMem
  let j' : X.ChartIdx := ⟨j, hj⟩
  have htriv := hchart j' (X.chartTAdicDVR j') 1 one_pos (chartTAdicDVR_torus X j')
  rw [chartDivPoint_chartTAdicDVR_eq_triv X j'] at htriv
  exact isPSH_envelope_of_polynomialConeIdealChartEstimates hgen hinc hsub htriv hchart
    hd hφ hφ0

end EnvelopeProperty.ProjSubvariety
