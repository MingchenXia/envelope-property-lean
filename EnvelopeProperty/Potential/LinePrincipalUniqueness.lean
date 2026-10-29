import EnvelopeProperty.Potential.LineRationalDecomposition

/-! # Uniqueness of actual original rational principal parts -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The original polynomial localization is faithful before taking its separated seminorm completion. -/
theorem rationalPolynomial_injective : Function.Injective (algebraMap K[X] U.RationalFunctions) := by
  intro a b hab
  obtain ⟨c,hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers U.denominatorPolynomial)
    U.RationalFunctions).mp hab
  rcases c.2 with ⟨n,hn⟩
  change U.denominatorPolynomial^n = c.1 at hn
  rw [← hn] at hc
  exact mul_left_cancel₀ (pow_ne_zero n U.denominatorPolynomial_ne_zero) hc

/-- A proper fraction with an arbitrary ORIGINAL centered numerator. -/
def properRationalPart (p : K[X]) (j : Fin m) (n : ℕ) : U.RationalFunctions :=
  algebraMap K[X] U.RationalFunctions (Polynomial.algEquivAevalXAddC (-U.holeCenter j) p)*
    (U.rationalHoleInverse j)^n

theorem properRationalPart_mul_denominator_pow (p : K[X]) (j : Fin m) (n : ℕ) :
    U.properRationalPart p j n*(algebraMap K[X] U.RationalFunctions U.denominatorPolynomial)^n =
      algebraMap K[X] U.RationalFunctions
        (Polynomial.algEquivAevalXAddC (-U.holeCenter j) p*(U.holeComplementPolynomial j)^n) := by
  have hQ := congrArg (algebraMap K[X] U.RationalFunctions) (U.holeCoordinate_mul_complement j)
  rw [map_mul] at hQ
  rw [properRationalPart,← hQ,mul_pow,map_mul,map_pow]
  have hi := congrArg (fun a : U.RationalFunctions => a^n)
    (U.holeCoordinate_mul_rationalHoleInverse j)
  rw [mul_pow,one_pow] at hi
  calc
    _ = algebraMap K[X] U.RationalFunctions
        (Polynomial.algEquivAevalXAddC (-U.holeCenter j) p)*
        (algebraMap K[X] U.RationalFunctions (U.holeComplementPolynomial j))^n *
        ((algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))^n*
          (U.rationalHoleInverse j)^n) := by ring
    _ = _ := by rw [hi,mul_one]

theorem properRationalPart_zero (j : Fin m) (n : ℕ) :
    U.properRationalPart 0 j n = 0 := by simp [properRationalPart]

theorem properRationalPart_add (p q : K[X]) (j : Fin m) (n : ℕ) :
    U.properRationalPart (p+q) j n = U.properRationalPart p j n+U.properRationalPart q j n := by
  simp only [properRationalPart,map_add,add_mul]

theorem properRationalPart_sub (p q : K[X]) (j : Fin m) (n : ℕ) :
    U.properRationalPart (p-q) j n = U.properRationalPart p j n-U.properRationalPart q j n := by
  simp only [properRationalPart,map_sub,sub_mul]

/-- No nonzero ORIGINAL proper fractions can cancel against one another and an original polynomial. -/
theorem properRationalPart_zero_unique (P : K[X]) (R : Fin m → K[X]) (n : ℕ)
    (hR : ∀ j, (R j).degree < n)
    (hz : algebraMap K[X] U.RationalFunctions P+∑ j, U.properRationalPart (R j) j n = 0) :
    P = 0 ∧ ∀ j, R j = 0 := by
  classical
  let t (i : Fin m) := Polynomial.algEquivAevalXAddC (-U.holeCenter i) (R i)*
    (U.holeComplementPolynomial i)^n
  have he : P*U.denominatorPolynomial^n+∑ i, t i = 0 := by
    apply U.rationalPolynomial_injective
    rw [map_zero,map_add,map_mul,map_pow,map_sum]
    dsimp only [t]
    simp_rw [← U.properRationalPart_mul_denominator_pow]
    rw [← Finset.sum_mul,← add_mul,hz,zero_mul]
  have hzero (j : Fin m) : R j = 0 := by
    have hp : (X-C (U.holeCenter j))^n ∣ P*U.denominatorPolynomial^n := by
      have hd : X-C (U.holeCenter j) ∣ U.denominatorPolynomial :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd n) P
    have ho : (X-C (U.holeCenter j))^n ∣ ∑ i ∈ Finset.univ.erase j, t i := by
      apply Finset.dvd_sum
      intro i hi
      have hd : X-C (U.holeCenter j) ∣ U.holeComplementPolynomial i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hi).1.symm,Finset.mem_univ _⟩)
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd n) _
    have ht : t j = -(P*U.denominatorPolynomial^n+∑ i ∈ Finset.univ.erase j, t i) := by
      rw [← Finset.add_sum_erase Finset.univ t (Finset.mem_univ j)] at he
      linear_combination he
    have hc : IsCoprime (X-C (U.holeCenter j)) (U.holeComplementPolynomial j) := by
      apply IsCoprime.prod_right
      intro i hi
      exact Polynomial.pairwise_coprime_X_sub_C U.holeCenter_injective
        (Finset.mem_erase.mp hi).1.symm
    have htdvd : (X-C (U.holeCenter j))^n ∣ t j := by
      rw [ht]
      exact dvd_neg.mpr (dvd_add hp ho)
    have hd : (X-C (U.holeCenter j))^n ∣
        Polynomial.algEquivAevalXAddC (-U.holeCenter j) (R j) :=
      (hc.pow : IsCoprime ((X-C (U.holeCenter j))^n)
        ((U.holeComplementPolynomial j)^n)).dvd_of_dvd_mul_right htdvd
    let e := Polynomial.algEquivAevalXAddC (U.holeCenter j)
    have hm := map_dvd e.toRingHom hd
    have hX : e (X-C (U.holeCenter j)) = X := by
      simp [e,Polynomial.algEquivAevalXAddC]
    have hsymm : Polynomial.algEquivAevalXAddC (-U.holeCenter j) = e.symm :=
      (Polynomial.algEquivAevalXAddC_symm _).symm
    change e ((X-C (U.holeCenter j))^n) ∣
      e (Polynomial.algEquivAevalXAddC (-U.holeCenter j) (R j)) at hm
    rw [map_pow,hX,hsymm,AlgEquiv.apply_symm_apply] at hm
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < n
    · exact Polynomial.X_pow_dvd_iff.mp hm k hk
    · exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp (hR j) k (le_of_not_gt hk)
  refine ⟨?_,hzero⟩
  have hmap : algebraMap K[X] U.RationalFunctions P = 0 := by
    simpa only [hzero,U.properRationalPart_zero,Finset.sum_const_zero,add_zero] using hz
  exact U.rationalPolynomial_injective (hmap.trans (map_zero _).symm)

theorem degree_sub_lt_of_lt (p q : K[X]) (n : ℕ) (hp : p.degree < n) (hq : q.degree < n) :
    (p-q).degree < n := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  rw [Polynomial.coeff_sub,(Polynomial.degree_lt_iff_coeff_zero _ _).mp hp k hk,
    (Polynomial.degree_lt_iff_coeff_zero _ _).mp hq k hk,sub_self]

theorem degree_mul_X_pow_lt (p : K[X]) (n k : ℕ) (hp : p.degree < n) :
    (p*X^k).degree < ((n+k : ℕ) : WithBot ℕ) := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro d hd
  rw [Polynomial.coeff_mul_X_pow']
  split_ifs with hk
  · exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp hp _ (by omega)
  · rfl

/-- Raising the actual common pole order changes no whole original proper fraction. -/
theorem properRationalPart_shift (p : K[X]) (j : Fin m) (n k : ℕ) :
    U.properRationalPart (p*X^k) j (n+k) = U.properRationalPart p j n := by
  have hX : Polynomial.algEquivAevalXAddC (-U.holeCenter j) X = X-C (U.holeCenter j) := by
    simp [Polynomial.algEquivAevalXAddC]
    ring
  rw [properRationalPart,map_mul,map_pow,hX,map_mul,map_pow,pow_add]
  have hi := congrArg (fun a : U.RationalFunctions => a^k)
    (U.holeCoordinate_mul_rationalHoleInverse j)
  rw [mul_pow,one_pow] at hi
  calc
    _ = algebraMap K[X] U.RationalFunctions (Polynomial.algEquivAevalXAddC (-U.holeCenter j) p)*
        (U.rationalHoleInverse j)^n *
        ((algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))^k*
          (U.rationalHoleInverse j)^k) := by ring
    _ = _ := by rw [hi,mul_one]; rfl

/-- Uniqueness of every original proper numerator at a fixed common exponent. -/
theorem properRationalPart_decomposition_unique (P Q : K[X]) (R S : Fin m → K[X]) (n : ℕ)
    (hR : ∀ j, (R j).degree < n) (hS : ∀ j, (S j).degree < n)
    (he : algebraMap K[X] U.RationalFunctions P+∑ j, U.properRationalPart (R j) j n =
      algebraMap K[X] U.RationalFunctions Q+∑ j, U.properRationalPart (S j) j n) :
    P = Q ∧ ∀ j, R j = S j := by
  have hz : algebraMap K[X] U.RationalFunctions (P-Q)+
      ∑ j, U.properRationalPart (R j-S j) j n = 0 := by
    simp_rw [map_sub,U.properRationalPart_sub,Finset.sum_sub_distrib]
    linear_combination he
  obtain ⟨hP,hRS⟩ := U.properRationalPart_zero_unique (P-Q) (fun j => R j-S j) n
    (fun j => degree_sub_lt_of_lt _ _ n (hR j) (hS j)) hz
  exact ⟨sub_eq_zero.mp hP,fun j => sub_eq_zero.mp (hRS j)⟩

/-- Independence of the original pole exponent and of the original rational presentation. -/
theorem properRationalPart_decomposition_independent (P Q : K[X]) (R S : Fin m → K[X]) (n k : ℕ)
    (hR : ∀ j, (R j).degree < n) (hS : ∀ j, (S j).degree < k)
    (he : algebraMap K[X] U.RationalFunctions P+∑ j, U.properRationalPart (R j) j n =
      algebraMap K[X] U.RationalFunctions Q+∑ j, U.properRationalPart (S j) j k) :
    P = Q ∧ ∀ j, U.properRationalPart (R j) j n = U.properRationalPart (S j) j k := by
  have he' : algebraMap K[X] U.RationalFunctions P+
      ∑ j, U.properRationalPart (R j*X^k) j (n+k) =
      algebraMap K[X] U.RationalFunctions Q+
        ∑ j, U.properRationalPart (S j*X^n) j (n+k) := by
    simp_rw [U.properRationalPart_shift,
      show n+k = k+n from Nat.add_comm n k,U.properRationalPart_shift]
    exact he
  obtain ⟨hP,hRS⟩ := U.properRationalPart_decomposition_unique P Q
    (fun j => R j*X^k) (fun j => S j*X^n) (n+k)
    (fun j => degree_mul_X_pow_lt _ n k (hR j))
    (fun j => by simpa only [Nat.add_comm] using degree_mul_X_pow_lt _ k n (hS j)) he'
  refine ⟨hP,fun j => ?_⟩
  calc
    U.properRationalPart (R j) j n = U.properRationalPart (R j*X^k) j (n+k) :=
      (U.properRationalPart_shift _ j n k).symm
    _ = U.properRationalPart (S j*X^n) j (n+k) := congrArg (fun p => U.properRationalPart p j (n+k)) (hRS j)
    _ = U.properRationalPart (S j) j k := by rw [Nat.add_comm n k,U.properRationalPart_shift]
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
