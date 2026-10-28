import EnvelopeProperty.Potential.LinePrincipalUniqueness

/-! # Actual representation-independent sharply bounded original rational projections -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- An ORIGINAL numerator from the actual localization's fraction existence theorem. -/
def rationalPresentationNumerator (f : U.RationalFunctions) : K[X] :=
  (Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f).choose

/-- Its actual common denominator exponent. All resulting projections will be independent of this choice. -/
def rationalPresentationExponent (f : U.RationalFunctions) : ℕ :=
  (Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f).choose_spec.choose

theorem rationalPresentation_eq (f : U.RationalFunctions) :
    f = U.commonRationalFraction (U.rationalPresentationNumerator f) (U.rationalPresentationExponent f) :=
  (Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f).choose_spec.choose_spec

/-- The ORIGINAL polynomial component of the actual rational function. -/
def rationalPolynomialPart (f : U.RationalFunctions) : K[X] :=
  U.principalPolynomial (U.rationalPresentationNumerator f) (U.rationalPresentationExponent f)

/-- The actual chosen proper numerator, still in the ORIGINAL centered polynomial coordinate. -/
def rationalPrincipalNumerator (f : U.RationalFunctions) (j : Fin m) : K[X] :=
  U.holePrincipalNumerator (U.rationalPresentationNumerator f) j (U.rationalPresentationExponent f)

theorem rationalPrincipalNumerator_degree_lt (f : U.RationalFunctions) (j : Fin m) :
    (U.rationalPrincipalNumerator f j).degree < U.rationalPresentationExponent f :=
  U.holePrincipalNumerator_degree_lt _ j _

/-- The WHOLE original hole principal component, rather than a coordinate certificate. -/
def rationalPrincipalProjection (j : Fin m) (f : U.RationalFunctions) : U.RationalFunctions :=
  U.properRationalPart (U.rationalPrincipalNumerator f j) j (U.rationalPresentationExponent f)

/-- The WHOLE original polynomial component in the original localized algebra. -/
def rationalPolynomialProjection (f : U.RationalFunctions) : U.RationalFunctions :=
  algebraMap K[X] U.RationalFunctions (U.rationalPolynomialPart f)

theorem rationalProjections_sum (f : U.RationalFunctions) :
    f = U.rationalPolynomialProjection f+∑ j, U.rationalPrincipalProjection j f := by
  exact (U.rationalPresentation_eq f).trans (U.commonRationalFraction_decomposition _ _)

/-- Identification with ANY proper original decomposition proves genuine representation independence. -/
theorem rationalProjections_eq_of_decomposition (f : U.RationalFunctions)
    (P : K[X]) (R : Fin m → K[X]) (n : ℕ) (hR : ∀ j, (R j).degree < n)
    (hf : f = algebraMap K[X] U.RationalFunctions P+∑ j, U.properRationalPart (R j) j n) :
    U.rationalPolynomialPart f = P ∧
      ∀ j, U.rationalPrincipalProjection j f = U.properRationalPart (R j) j n := by
  apply U.properRationalPart_decomposition_independent (U.rationalPolynomialPart f) P
    (U.rationalPrincipalNumerator f) R (U.rationalPresentationExponent f) n
    (U.rationalPrincipalNumerator_degree_lt f) hR
  exact (U.rationalProjections_sum f).symm.trans hf

theorem nnnorm_rationalPrincipalProjection_le (j : Fin m) (f : U.RationalFunctions) :
    ‖U.normedRationalEquiv.symm (U.rationalPrincipalProjection j f)‖₊ ≤
      ‖U.normedRationalEquiv.symm f‖₊ := by
  have hb := U.nnnorm_holePrincipalPart_le (U.rationalPresentationNumerator f) j
    (U.rationalPresentationExponent f)
  rw [← U.rationalPresentation_eq f] at hb
  exact hb

theorem nnnorm_rationalPolynomialProjection_le (f : U.RationalFunctions) :
    ‖U.normedRationalEquiv.symm (U.rationalPolynomialProjection f)‖₊ ≤
      ‖U.normedRationalEquiv.symm f‖₊ := by
  have hb := U.nnnorm_principalPolynomial_le (U.rationalPresentationNumerator f)
    (U.rationalPresentationExponent f)
  rw [← U.rationalPresentation_eq f] at hb
  exact hb

theorem degree_add_lt_of_lt (p q : K[X]) (n : ℕ) (hp : p.degree < n) (hq : q.degree < n) :
    (p+q).degree < n := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  rw [Polynomial.coeff_add,(Polynomial.degree_lt_iff_coeff_zero _ _).mp hp k hk,
    (Polynomial.degree_lt_iff_coeff_zero _ _).mp hq k hk,add_zero]

/-- The actual common numerator for summing two existing original proper decompositions. -/
def rationalSumNumerator (f g : U.RationalFunctions) (j : Fin m) : K[X] :=
  U.rationalPrincipalNumerator f j*X^(U.rationalPresentationExponent g)+
    U.rationalPrincipalNumerator g j*X^(U.rationalPresentationExponent f)

theorem rationalSumNumerator_degree_lt (f g : U.RationalFunctions) (j : Fin m) :
    (U.rationalSumNumerator f g j).degree <
      ((U.rationalPresentationExponent f+U.rationalPresentationExponent g : ℕ) : WithBot ℕ) := by
  apply degree_add_lt_of_lt
  · exact degree_mul_X_pow_lt _ _ _ (U.rationalPrincipalNumerator_degree_lt f j)
  · simpa only [Nat.add_comm] using degree_mul_X_pow_lt _ _ _
      (U.rationalPrincipalNumerator_degree_lt g j)

theorem properRationalPart_rationalSumNumerator (f g : U.RationalFunctions) (j : Fin m) :
    U.properRationalPart (U.rationalSumNumerator f g j) j
      (U.rationalPresentationExponent f+U.rationalPresentationExponent g) =
      U.rationalPrincipalProjection j f+U.rationalPrincipalProjection j g := by
  rw [rationalSumNumerator,U.properRationalPart_add,U.properRationalPart_shift,
    Nat.add_comm (U.rationalPresentationExponent f),U.properRationalPart_shift]
  rfl

theorem rationalProjections_add (f g : U.RationalFunctions) :
    U.rationalPolynomialPart (f+g) = U.rationalPolynomialPart f+U.rationalPolynomialPart g ∧
      ∀ j, U.rationalPrincipalProjection j (f+g) =
        U.rationalPrincipalProjection j f+U.rationalPrincipalProjection j g := by
  have he : f+g = algebraMap K[X] U.RationalFunctions
      (U.rationalPolynomialPart f+U.rationalPolynomialPart g)+
      ∑ j, U.properRationalPart (U.rationalSumNumerator f g j) j
        (U.rationalPresentationExponent f+U.rationalPresentationExponent g) := by
    simp_rw [map_add,U.properRationalPart_rationalSumNumerator,Finset.sum_add_distrib]
    have hf := U.rationalProjections_sum f
    have hg := U.rationalProjections_sum g
    change f = algebraMap K[X] U.RationalFunctions (U.rationalPolynomialPart f)+_ at hf
    change g = algebraMap K[X] U.RationalFunctions (U.rationalPolynomialPart g)+_ at hg
    linear_combination hf+hg
  obtain ⟨hP,hR⟩ := U.rationalProjections_eq_of_decomposition (f+g) _ _ _
    (U.rationalSumNumerator_degree_lt f g) he
  exact ⟨hP,fun j => (hR j).trans (U.properRationalPart_rationalSumNumerator f g j)⟩

theorem degree_C_mul_lt (a : K) (p : K[X]) (n : ℕ) (hp : p.degree < n) :
    (C a*p).degree < n := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  rw [Polynomial.coeff_C_mul,(Polynomial.degree_lt_iff_coeff_zero _ _).mp hp k hk,mul_zero]

theorem properRationalPart_C_mul (a : K) (p : K[X]) (j : Fin m) (n : ℕ) :
    U.properRationalPart (C a*p) j n =
      algebraMap K[X] U.RationalFunctions (C a)*U.properRationalPart p j n := by
  have hC : Polynomial.algEquivAevalXAddC (-U.holeCenter j) (C a) = C a := by
    exact (Polynomial.algEquivAevalXAddC (-U.holeCenter j)).commutes a
  simp only [properRationalPart,map_mul,hC,mul_assoc]

/-- Original scalar multiplication of every original component is derived by uniqueness. -/
theorem rationalProjections_C_mul (a : K) (f : U.RationalFunctions) :
    U.rationalPolynomialPart (algebraMap K[X] U.RationalFunctions (C a)*f) =
      C a*U.rationalPolynomialPart f ∧
      ∀ j, U.rationalPrincipalProjection j (algebraMap K[X] U.RationalFunctions (C a)*f) =
        algebraMap K[X] U.RationalFunctions (C a)*U.rationalPrincipalProjection j f := by
  have he : algebraMap K[X] U.RationalFunctions (C a)*f =
      algebraMap K[X] U.RationalFunctions (C a*U.rationalPolynomialPart f)+
        ∑ j, U.properRationalPart (C a*U.rationalPrincipalNumerator f j) j
          (U.rationalPresentationExponent f) := by
    simp_rw [map_mul,U.properRationalPart_C_mul,← Finset.mul_sum,← mul_add]
    exact congrArg (fun b => algebraMap K[X] U.RationalFunctions (C a)*b) (U.rationalProjections_sum f)
  obtain ⟨hP,hR⟩ := U.rationalProjections_eq_of_decomposition _ _ _ _
    (fun j => degree_C_mul_lt a _ _ (U.rationalPrincipalNumerator_degree_lt f j)) he
  exact ⟨hP,fun j => (hR j).trans (U.properRationalPart_C_mul a _ j _)⟩

/-- The actual ORIGINAL K-linear principal projection on the whole original rational ring. -/
def rationalPrincipalLinearMap (j : Fin m) : U.RationalFunctions →ₗ[K] U.RationalFunctions where
  toFun := U.rationalPrincipalProjection j
  map_add' f g := (U.rationalProjections_add f g).2 j
  map_smul' a f := by
    simp only [RingHom.id_apply,Algebra.smul_def,
      IsScalarTower.algebraMap_apply K K[X] U.RationalFunctions]
    change U.rationalPrincipalProjection j (algebraMap K[X] U.RationalFunctions (C a)*f) =
      algebraMap K[X] U.RationalFunctions (C a)*U.rationalPrincipalProjection j f
    exact (U.rationalProjections_C_mul a f).2 j

/-- The actual ORIGINAL K-linear polynomial projection on the whole original rational ring. -/
def rationalPolynomialLinearMap : U.RationalFunctions →ₗ[K] U.RationalFunctions where
  toFun := U.rationalPolynomialProjection
  map_add' f g := by
    change algebraMap K[X] U.RationalFunctions (U.rationalPolynomialPart (f+g)) = _
    rw [(U.rationalProjections_add f g).1,map_add]
    rfl
  map_smul' a f := by
    simp only [RingHom.id_apply,Algebra.smul_def,
      IsScalarTower.algebraMap_apply K K[X] U.RationalFunctions]
    change algebraMap K[X] U.RationalFunctions
      (U.rationalPolynomialPart (algebraMap K[X] U.RationalFunctions (C a)*f)) =
        algebraMap K[X] U.RationalFunctions (C a)*
          algebraMap K[X] U.RationalFunctions (U.rationalPolynomialPart f)
    rw [(U.rationalProjections_C_mul a f).1,map_mul]

theorem rationalPolynomialPart_of_polynomial (P : K[X]) :
    U.rationalPolynomialPart (algebraMap K[X] U.RationalFunctions P) = P ∧
      ∀ j, U.rationalPrincipalProjection j (algebraMap K[X] U.RationalFunctions P) = 0 := by
  obtain ⟨hP,hR⟩ := U.rationalProjections_eq_of_decomposition
    (algebraMap K[X] U.RationalFunctions P) P (fun _ => 0) 0
    (fun _ => by simp) (by simp only [U.properRationalPart_zero,Finset.sum_const_zero,add_zero])
  exact ⟨hP,fun j => (hR j).trans (U.properRationalPart_zero j 0)⟩

theorem rationalProjections_of_properRationalPart (p : K[X]) (j : Fin m) (n : ℕ)
    (hp : p.degree < n) :
    U.rationalPolynomialPart (U.properRationalPart p j n) = 0 ∧
      ∀ i, U.rationalPrincipalProjection i (U.properRationalPart p j n) =
        if i = j then U.properRationalPart p j n else 0 := by
  classical
  have hdeg (i : Fin m) : (if i = j then p else (0 : K[X])).degree < n := by
    split_ifs
    · exact hp
    · simp
  have he : U.properRationalPart p j n = algebraMap K[X] U.RationalFunctions 0+
      ∑ i, U.properRationalPart (if i = j then p else 0) i n := by
    simp only [map_zero,zero_add]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp only [if_neg hij,U.properRationalPart_zero]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  obtain ⟨hP,hR⟩ := U.rationalProjections_eq_of_decomposition _ 0 _ n hdeg he
  refine ⟨hP,fun i => ?_⟩
  rw [hR i]
  split_ifs with hij
  · subst i
    rfl
  · exact U.properRationalPart_zero i n

theorem rationalPrincipalProjection_comp (i j : Fin m) (f : U.RationalFunctions) :
    U.rationalPrincipalProjection i (U.rationalPrincipalProjection j f) =
      if i = j then U.rationalPrincipalProjection j f else 0 :=
  (U.rationalProjections_of_properRationalPart _ j _ (U.rationalPrincipalNumerator_degree_lt f j)).2 i

theorem rationalPolynomialProjection_comp (f : U.RationalFunctions) :
    U.rationalPolynomialProjection (U.rationalPolynomialProjection f) = U.rationalPolynomialProjection f := by
  change algebraMap K[X] U.RationalFunctions
    (U.rationalPolynomialPart (algebraMap K[X] U.RationalFunctions (U.rationalPolynomialPart f))) = _
  rw [(U.rationalPolynomialPart_of_polynomial _).1]
  rfl

theorem rationalPolynomialProjection_principal (j : Fin m) (f : U.RationalFunctions) :
    U.rationalPolynomialProjection (U.rationalPrincipalProjection j f) = 0 := by
  change algebraMap K[X] U.RationalFunctions
    (U.rationalPolynomialPart (U.properRationalPart (U.rationalPrincipalNumerator f j) j
      (U.rationalPresentationExponent f))) = 0
  rw [(U.rationalProjections_of_properRationalPart _ j _ (U.rationalPrincipalNumerator_degree_lt f j)).1,map_zero]

theorem rationalPrincipalProjection_polynomial (j : Fin m) (f : U.RationalFunctions) :
    U.rationalPrincipalProjection j (U.rationalPolynomialProjection f) = 0 :=
  (U.rationalPolynomialPart_of_polynomial _).2 j

theorem nnnorm_rationalProjections (f : U.RationalFunctions) :
    ‖U.normedRationalEquiv.symm f‖₊ =
      max ‖U.normedRationalEquiv.symm (U.rationalPolynomialProjection f)‖₊
        (Finset.univ.sup fun j => ‖U.normedRationalEquiv.symm (U.rationalPrincipalProjection j f)‖₊) := by
  have he := U.nnnorm_commonFraction_decomposition (U.rationalPresentationNumerator f)
    (U.rationalPresentationExponent f)
  rw [← U.rationalPresentation_eq f] at he
  exact he

theorem rationalLinearProjections_sum :
    U.rationalPolynomialLinearMap+∑ j, U.rationalPrincipalLinearMap j = LinearMap.id := by
  apply LinearMap.ext
  intro f
  simpa [rationalPolynomialLinearMap,rationalPrincipalLinearMap,LinearMap.sum_apply] using
    (U.rationalProjections_sum f).symm
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
