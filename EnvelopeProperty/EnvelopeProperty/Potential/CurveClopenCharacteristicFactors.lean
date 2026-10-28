import EnvelopeProperty.Potential.CurveCharacteristicGrowth
import EnvelopeProperty.Potential.CurveClopenGlobalIdempotents

/-! # Whole restriction of actual curve characteristic factors and algebraic descent -/

open scoped NNReal Polynomial TensorProduct Classical
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
  [CommRing B] [Algebra K[X] B] [Fintype ι] {m n : ℕ}
  (U : FCStandardAffinoid w m) (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)

omit [Fintype ι] in
/-- Actual whole idempotent specialization commutes with every original carrier restriction. -/
theorem curveIdempotentSpecialization_restriction (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : V.carrier) :
    V.curveIdempotentSpecialization basis
      (U.curveAnalyticNormedRestriction V hVU basis e) x =
        U.curveIdempotentSpecialization basis e ⟨x.1, hVU x.2⟩ :=
  U.curveAnalyticRestriction_specialization V hVU x (U.curveAnalyticOriginalEquiv basis e)

/-- The entire actual characteristic factor, with all its original analytic
coefficients, commutes with every genuine carrier restriction. -/
theorem curveCharacteristicFactor_restriction (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) :
    Polynomial.map (U.analyticRestriction V hVU) (U.curveCharacteristicFactor basis he b) =
      V.curveCharacteristicFactor basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) b := by
  let := Module.Finite.of_basis basis
  apply Polynomial.ext
  intro i
  apply V.analyticFunctions_eq_of_evaluation_eq
  intro x
  have heval : (V.evaluationToH x).comp (U.analyticRestriction V hVU) =
      U.evaluationToH ⟨x.1, hVU x.2⟩ := by
    apply RingHom.ext
    intro f
    exact U.analyticRestriction_evaluation V hVU x f
  have hp : Polynomial.map (V.evaluationToH x)
      (Polynomial.map (U.analyticRestriction V hVU) (U.curveCharacteristicFactor basis he b)) =
      Polynomial.map (V.evaluationToH x)
        (V.curveCharacteristicFactor basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) b) := by
    rw [Polynomial.map_map, heval, U.map_curveCharacteristicFactor,
      V.map_curveCharacteristicFactor]
    simp only [U.curveIdempotentSpecialization_restriction V hVU basis e x]
  simpa only [Polynomial.coeff_map] using congrArg (fun p => p.coeff i) hp

/-- The actual selected and complementary whole analytic factors multiply to
the original multiplication characteristic polynomial, coefficient by coefficient. -/
theorem curveCharacteristicFactor_mul_one_sub (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) :
    let := Module.Finite.of_basis basis
    let := Module.Free.of_basis basis
    U.curveCharacteristicFactor basis he b * U.curveCharacteristicFactor basis he.one_sub b =
      Polynomial.map U.polynomialAnalyticMap (Algebra.lmul K[X] B b).charpoly := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  apply Polynomial.ext
  intro i
  apply U.analyticFunctions_eq_of_evaluation_eq
  intro x
  have heval : (U.evaluationToH x).comp U.polynomialAnalyticMap =
      algebraMap K[X] (Spectrum.H x.1.1) := by
    apply RingHom.ext
    intro p
    exact (U.polynomialAnalyticEvaluation x).commutes p
  have hsn : U.curveIdempotentSpecialization basis (1-e) x =
      1-U.curveIdempotentSpecialization basis e x := by
    simp only [curveIdempotentSpecialization, map_sub, map_one]
  have hp : Polynomial.map (U.evaluationToH x)
      (U.curveCharacteristicFactor basis he b * U.curveCharacteristicFactor basis he.one_sub b) =
      Polynomial.map (U.evaluationToH x)
        (Polynomial.map U.polynomialAnalyticMap (Algebra.lmul K[X] B b).charpoly) := by
    rw [Polynomial.map_mul, U.map_curveCharacteristicFactor, U.map_curveCharacteristicFactor,
      Polynomial.map_map, heval]
    simp only [hsn]
    rw [IdempotentSummand.characteristicFactor_mul_one_sub,
      lmul_one_tmul_eq_baseChange, LinearMap.charpoly_baseChange]
  simpa only [Polynomial.coeff_map] using congrArg (fun p => p.coeff i) hp

/-- Every actual selected factor has degree at most the original whole finite
free curve rank, derived on all genuine completed fibres. -/
theorem curveCharacteristicFactor_natDegree_le (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) (b : B) :
    (U.curveCharacteristicFactor basis he b).natDegree ≤ Fintype.card ι := by
  let := Module.Finite.of_basis basis
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply U.analyticFunctions_eq_of_evaluation_eq
  intro x
  have hp := U.map_curveCharacteristicFactor basis he b x
  dsimp only at hp
  have hd := (IdempotentSummand.characteristicFactor_eq_charpoly (R := Spectrum.H x.1.1)
    (U.curveIdempotentSpecialization_isIdempotent basis he x)
    ((1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b)).2.2
  have hq : Module.finrank (Spectrum.H x.1.1)
      (IdempotentSummand.Summand (U.curveIdempotentSpecialization basis e x)) ≤ Fintype.card ι := by
    let q := IdempotentSummand.quotient (R := Spectrum.H x.1.1)
      (U.curveIdempotentSpecialization basis e x)
    let := IdempotentSummand.finite (R := Spectrum.H x.1.1)
      (U.curveIdempotentSpecialization basis e x)
    exact (q.toLinearMap.finrank_le_finrank_of_surjective Ideal.Quotient.mk_surjective).trans_eq
      (Module.finrank_eq_card_basis (basis.baseChange (Spectrum.H x.1.1)))
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt ((hd.le.trans hq).trans_lt hi)
  have hc := congrArg (fun P => P.coeff i) hp
  rw [Polynomial.coeff_map, hz] at hc
  simpa only [map_zero] using hc

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsAlgClosed K] [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

/-- Actual global clopen pieces construct original polynomial coefficients of
their characteristic factors on every whole disc, with one uniform degree bound. -/
theorem exists_globalClopenFactor_coefficient_polynomials
    (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C)
    (b : B) :
    ∃ (N : ℕ) (p : ℕ → K[X]), (∀ i, (p i).natDegree ≤ N) ∧
      ∀ (r : ℝ≥0) (i : ℕ),
        ((zeroDisc (K := K) r).curveCharacteristicFactor basis
          ((zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC) b).coeff i =
            (zeroDisc (K := K) r).polynomialAnalyticMap (p i) := by
  let e (r : ℝ≥0) := (zeroDisc (K := K) r).globalClopenIdempotent basis C hC
  have he (r : ℝ≥0) : IsIdempotentElem (e r) :=
    (zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC
  let c (i : ℕ) (r : ℝ≥0) :=
    ((zeroDisc (K := K) r).curveCharacteristicFactor basis (he r) b).coeff i
  have hc (i : ℕ) : ∀ r s (hsr : s ≤ r),
      (zeroDisc (K := K) r).analyticRestriction (zeroDisc (K := K) s)
        (zeroDisc_carrier_subset hsr) (c i r) = c i s := by
    intro r s hsr
    have hp := (zeroDisc (K := K) r).curveCharacteristicFactor_restriction
      (zeroDisc (K := K) s) (zeroDisc_carrier_subset hsr) basis (he r) b
    have hres : (zeroDisc (K := K) r).curveAnalyticNormedRestriction (zeroDisc (K := K) s)
        (zeroDisc_carrier_subset hsr) basis (e r) = e s :=
      (zeroDisc (K := K) r).restriction_globalClopenIdempotent
        (zeroDisc (K := K) s) (zeroDisc_carrier_subset hsr) basis C hC
    simp only [hres] at hp
    simpa only [Polynomial.coeff_map] using congrArg (fun P => P.coeff i) hp
  obtain ⟨M, N, hMN⟩ := exists_curveCharacteristicFactor_disc_growth basis b
  have hp (i : ℕ) : ∃ p : K[X], p.natDegree ≤ N ∧
      ∀ r, c i r = (zeroDisc (K := K) r).polynomialAnalyticMap p :=
    exists_polynomial_of_compatible_growth (c i) (hc i) M N
      (fun r => hMN r (e r) (he r) i)
  choose p hpN hpr using hp
  exact ⟨N, p, hpN, fun r i => hpr i r⟩

/-- A single actual polynomial over the original polynomial base recovers the
whole selected factor of an original global clopen on every disc. -/
theorem exists_globalClopenFactor_polynomial (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C)
    (b : B) :
    ∃ P : K[X][X], P.natDegree ≤ Fintype.card ι ∧ ∀ r : ℝ≥0,
      Polynomial.map (zeroDisc (K := K) r).polynomialAnalyticMap P =
        (zeroDisc (K := K) r).curveCharacteristicFactor basis
          ((zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC) b := by
  classical
  obtain ⟨N, p, _, hp⟩ := exists_globalClopenFactor_coefficient_polynomials basis C hC b
  let P : K[X][X] := ∑ i ∈ Finset.range (Fintype.card ι + 1), Polynomial.monomial i (p i)
  have hcoeff (i : ℕ) : P.coeff i = if i ≤ Fintype.card ι then p i else 0 := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hi : i ≤ Fintype.card ι
    · rw [if_pos hi]
      simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff, hi, ite_true]
    · rw [if_neg hi]
      simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff, hi, ite_false]
  refine ⟨P, ?_, fun r => ?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [hcoeff, if_neg (Nat.not_le.mpr hi)]
  · apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_map, hcoeff]
    by_cases hi : i ≤ Fintype.card ι
    · rw [if_pos hi, ← hp r i]
    · rw [if_neg hi, map_zero]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt
        (((zeroDisc (K := K) r).curveCharacteristicFactor_natDegree_le basis
          ((zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC) b).trans_lt
            (Nat.lt_of_not_ge hi))).symm

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
