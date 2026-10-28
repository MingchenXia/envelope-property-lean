import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Infinite

/-! # Actual arithmetic closed points in characteristic-zero principal opens

For the original finite-type integer domain, every original principal open
contains a closed point with finite residue field of arbitrarily large
characteristic. The specialization map is the original quotient homomorphism.
This is only the arithmetic closed-fibre producer, with no geometric descent,
Witt-vector lifting or cohomological vanishing assertion.
-/

namespace EnvelopeProperty.ArithmeticClosedPoints

/-- The original integer ring is Jacobson; no Jacobson hypothesis is imported as a certificate. -/
theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP0 : P = ⊥
  · subst P
    apply eq_bot_iff.mpr
    intro a ha
    apply Ideal.mem_bot.mpr
    by_contra ha0
    obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (a.natAbs + 1)
    have : Fact p.Prime := ⟨hp⟩
    have hamem : a ∈ Ideal.span {(p : ℤ)} :=
      (Ideal.mem_sInf.mp ha) ⟨bot_le, inferInstance⟩
    have hdiv : p ∣ a.natAbs := Int.natCast_dvd.mp (Ideal.mem_span_singleton.mp hamem)
    have hle : p ≤ a.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) hdiv
    omega
  · have : P.IsPrime := hP
    have : P.IsMaximal := IsPrime.to_maximal_ideal hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- EVERY original closed residue field of a finite-type integer algebra is finite of prime
characteristic. The residue field is the literal original maximal-ideal quotient. -/
theorem quotient_prime_characteristic_and_finite
    {R : Type*} [CommRing R] [Algebra ℤ R] [Algebra.FiniteType ℤ R]
    (m : MaximalSpectrum R) :
    ∃ p : ℕ, p.Prime ∧ CharP (R ⧸ m.asIdeal) p ∧ Finite (R ⧸ m.asIdeal) := by
  let K := R ⧸ m.asIdeal
  let : Field K := Ideal.Quotient.field m.asIdeal
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have := finite_of_finite_type_of_isJacobsonRing ℤ K
  have hp0 : ringChar K ≠ 0 := by
    intro h
    have : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp h
    exact Int.not_isField
      (isField_of_isIntegral_of_isField
        (algebraMap ℤ K).injective_int (Field.toIsField K))
  have hp : (ringChar K).Prime := CharP.char_prime_of_ne_zero K hp0
  have : Fact (ringChar K).Prime := ⟨hp⟩
  let : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
  have := IsScalarTower.of_algebraMap_eq
    (R := ℤ) (S := ZMod (ringChar K)) (A := K) (fun z => by simp)
  have : Algebra.FiniteType (ZMod (ringChar K)) K :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod (ringChar K)) K
  have := finite_of_finite_type_of_isJacobsonRing (ZMod (ringChar K)) K
  exact ⟨ringChar K, hp, inferInstance, Module.finite_of_finite (ZMod (ringChar K))⟩

/-- An actual maximal ideal in the original principal open, with finite original residue field
of characteristic strictly greater than the given bound. -/
theorem exists_large_characteristic_closed_point
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℤ R] [Algebra.FiniteType ℤ R]
    (r : R) (hr : r ≠ 0) (N : ℕ) :
    ∃ (m : MaximalSpectrum R) (p : ℕ),
      p.Prime ∧ N < p ∧ r ∉ m.asIdeal ∧
        CharP (R ⧸ m.asIdeal) p ∧ Finite (R ⧸ m.asIdeal) := by
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  have hfactor : (N.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have ha : r * (N.factorial : R) ∉ (⊥ : Ideal R).jacobson := by
    rw [IsJacobsonRing.out' (⊥ : Ideal R) Ideal.isRadical_bot, Ideal.mem_bot]
    exact mul_ne_zero hr hfactor
  simp only [Ideal.jacobson, Ideal.mem_sInf, Set.mem_ofPred_eq, bot_le, true_and,
    not_forall] at ha
  obtain ⟨m, hm, ham⟩ := ha
  let point : MaximalSpectrum R := ⟨m, hm⟩
  obtain ⟨p, hp, hchar, hfinite⟩ := quotient_prime_characteristic_and_finite point
  have hrm : r ∉ m := fun h => ham (m.mul_mem_right (N.factorial : R) h)
  have hfm : (N.factorial : R) ∉ m := fun h => ham (m.mul_mem_left r h)
  have hNp : N < p := by
    by_contra h
    have hle : p ≤ N := Nat.le_of_not_gt h
    have : CharP (R ⧸ m) p := hchar
    have hz : (N.factorial : R ⧸ m) = 0 :=
      (CharP.cast_eq_zero_iff (R ⧸ m) p N.factorial).mpr (Nat.dvd_factorial hp.pos hle)
    apply hfm
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hz)
  exact ⟨point, p, hp, hNp, hrm, hchar, hfinite⟩

/-- The actual specialization is the surjective original quotient map, and preserves the
specified original nonzero element. No finite-field or closed-point certificate is assumed. -/
theorem exists_large_characteristic_quotient_map
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℤ R] [Algebra.FiniteType ℤ R]
    (r : R) (hr : r ≠ 0) (N : ℕ) :
    ∃ (m : MaximalSpectrum R) (p : ℕ),
      p.Prime ∧ N < p ∧ CharP (R ⧸ m.asIdeal) p ∧ Finite (R ⧸ m.asIdeal) ∧
        Function.Surjective (Ideal.Quotient.mk m.asIdeal) ∧
        Ideal.Quotient.mk m.asIdeal r ≠ 0 := by
  obtain ⟨m, p, hp, hNp, hrm, hchar, hfinite⟩ :=
    exists_large_characteristic_closed_point r hr N
  exact ⟨m, p, hp, hNp, hchar, hfinite, Ideal.Quotient.mk_surjective,
    fun h => hrm (Ideal.Quotient.eq_zero_iff_mem.mp h)⟩

end EnvelopeProperty.ArithmeticClosedPoints
