import EnvelopeProperty.Potential.LinePrincipalParts
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision

/-! # Actual rational Mittag--Leffler decomposition from constructed original principal parts -/
open scoped NNReal Polynomial Topology
open Polynomial Topology UniformSpace
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
variable {K : Type*} [Field K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The actual numerator left after subtracting all constructed original principal parts. -/
def principalResidual (A : K[X]) (n : ℕ) : K[X] :=
  A-∑ j, Polynomial.algEquivAevalXAddC (-U.holeCenter j) (U.holePrincipalNumerator A j n)*
    (U.holeComplementPolynomial j)^n

theorem holeCoordinate_pow_dvd_principalResidual (A : K[X]) (n : ℕ) (j : Fin m) :
    (X-C (U.holeCenter j))^n ∣ U.principalResidual A n := by
  classical
  let t (i : Fin m) := Polynomial.algEquivAevalXAddC (-U.holeCenter i)
    (U.holePrincipalNumerator A i n)*(U.holeComplementPolynomial i)^n
  have hj : (X-C (U.holeCenter j))^n ∣ A-t j := by
    simpa only [t,mul_comm,neg_sub] using dvd_neg.mpr (U.holePrincipalNumerator_congruence A j n)
  have ho : (X-C (U.holeCenter j))^n ∣ ∑ i ∈ Finset.univ.erase j, t i := by
    apply Finset.dvd_sum
    intro i hi
    have hji : j ≠ i := (Finset.mem_erase.mp hi).1.symm
    have hdiv : X-C (U.holeCenter j) ∣ U.holeComplementPolynomial i := by
      exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩)
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdiv n) _
  have hs := Finset.add_sum_erase Finset.univ t (Finset.mem_univ j)
  change _ ∣ A-∑ i, t i
  rw [← hs,← sub_sub]
  exact dvd_sub hj ho

/-- Global denominator cancellation is derived from the actual pairwise coprime original coordinates. -/
theorem denominator_pow_dvd_principalResidual (A : K[X]) (n : ℕ) :
    U.denominatorPolynomial^n ∣ U.principalResidual A n := by
  have hc : Pairwise (fun i j : Fin m =>
      IsCoprime ((X-C (U.holeCenter i))^n) ((X-C (U.holeCenter j))^n)) := by
    intro i j hij
    exact (Polynomial.pairwise_coprime_X_sub_C U.holeCenter_injective hij).pow
  have hd := Fintype.prod_dvd_of_coprime hc (U.holeCoordinate_pow_dvd_principalResidual A n)
  simpa only [denominatorPolynomial,Finset.prod_pow] using hd

/-- An ORIGINAL polynomial part, obtained from the proved divisibility of the constructed residual. -/
def principalPolynomial (A : K[X]) (n : ℕ) : K[X] :=
  (U.denominator_pow_dvd_principalResidual A n).choose

theorem principalResidual_eq (A : K[X]) (n : ℕ) :
    U.principalResidual A n = U.denominatorPolynomial^n*U.principalPolynomial A n :=
  (U.denominator_pow_dvd_principalResidual A n).choose_spec

theorem holePrincipalPart_mul_denominator_pow (A : K[X]) (j : Fin m) (n : ℕ) :
    U.holePrincipalPart A j n*(algebraMap K[X] U.RationalFunctions U.denominatorPolynomial)^n =
      algebraMap K[X] U.RationalFunctions
        (Polynomial.algEquivAevalXAddC (-U.holeCenter j) (U.holePrincipalNumerator A j n)*
          (U.holeComplementPolynomial j)^n) := by
  have hQ := congrArg (algebraMap K[X] U.RationalFunctions) (U.holeCoordinate_mul_complement j)
  rw [map_mul] at hQ
  rw [holePrincipalPart,← hQ,mul_pow,map_mul,map_pow]
  have hi := congrArg (fun a : U.RationalFunctions => a^n)
    (U.holeCoordinate_mul_rationalHoleInverse j)
  rw [mul_pow,one_pow] at hi
  calc
    _ = algebraMap K[X] U.RationalFunctions
        (Polynomial.algEquivAevalXAddC (-U.holeCenter j) (U.holePrincipalNumerator A j n))*
        (algebraMap K[X] U.RationalFunctions (U.holeComplementPolynomial j))^n *
        ((algebraMap K[X] U.RationalFunctions (X-C (U.holeCenter j)))^n*
          (U.rationalHoleInverse j)^n) := by ring
    _ = _ := by rw [hi,mul_one]

/-- Equality of WHOLE original rational elements, with every component constructed from the original numerator. -/
theorem commonRationalFraction_decomposition (A : K[X]) (n : ℕ) :
    U.commonRationalFraction A n = algebraMap K[X] U.RationalFunctions (U.principalPolynomial A n)+
      ∑ j, U.holePrincipalPart A j n := by
  have he : U.commonRationalFraction A n*
      (algebraMap K[X] U.RationalFunctions U.denominatorPolynomial)^n =
      (algebraMap K[X] U.RationalFunctions (U.principalPolynomial A n)+
        ∑ j, U.holePrincipalPart A j n)*
        (algebraMap K[X] U.RationalFunctions U.denominatorPolynomial)^n := by
    have hf := IsLocalization.mk'_spec U.RationalFunctions A
      (⟨U.denominatorPolynomial^n,n,rfl⟩ : Submonoid.powers U.denominatorPolynomial)
    change U.commonRationalFraction A n*algebraMap K[X] U.RationalFunctions (U.denominatorPolynomial^n) = _ at hf
    rw [map_pow] at hf
    rw [hf,add_mul,Finset.sum_mul]
    simp_rw [U.holePrincipalPart_mul_denominator_pow]
    rw [← map_pow,← map_mul,← map_sum,← map_add]
    congr 1
    have hr := U.principalResidual_eq A n
    unfold principalResidual at hr
    linear_combination hr
  have hu := congrArg (fun a : U.RationalFunctions => a^n)
    (IsLocalization.Away.mul_invSelf (S := U.RationalFunctions) U.denominatorPolynomial)
  rw [mul_pow,one_pow] at hu
  have hx := congrArg (fun a : U.RationalFunctions => a*
    (IsLocalization.Away.invSelf U.denominatorPolynomial : U.RationalFunctions)^n) he
  simpa only [mul_assoc,hu,mul_one] using hx

local instance : Fintype U.boundary := U.rationalBoundaryFintype

/-- A boundary value of the ORIGINAL element is bounded by its actual boundary seminorm. -/
theorem rationalValue_boundary_le_nnnorm (f : U.RationalFunctions) (z : U.boundary) :
    U.rationalValue f ⟨z.1,U.boundary_subset z.2⟩ ≤ ‖U.normedRationalEquiv.symm f‖₊ := by
  rw [U.nnnorm_normedRationalFunctions,RingEquiv.apply_symm_apply]
  exact Finset.le_sup (f := fun y : U.boundary =>
    U.rationalValue f ⟨y.1,U.boundary_subset y.2⟩) (Finset.mem_univ z)

theorem nnnorm_rational_le_of_boundary (f : U.RationalFunctions) (c : ℝ≥0)
    (hf : ∀ z : U.boundary, U.rationalValue f ⟨z.1,U.boundary_subset z.2⟩ ≤ c) :
    ‖U.normedRationalEquiv.symm f‖₊ ≤ c := by
  rw [U.nnnorm_normedRationalFunctions,RingEquiv.apply_symm_apply]
  exact Finset.sup_le fun z _ => hf z

theorem nnnorm_rational_add_le_max (f g : U.RationalFunctions) :
    ‖U.normedRationalEquiv.symm (f+g)‖₊ ≤
      max ‖U.normedRationalEquiv.symm f‖₊ ‖U.normedRationalEquiv.symm g‖₊ := by
  apply U.nnnorm_rational_le_of_boundary
  intro z
  exact ((U.rationalPoint ⟨z.1,U.boundary_subset z.2⟩).1.val.map_add f g).trans
    (max_le_max (U.rationalValue_boundary_le_nnnorm f z) (U.rationalValue_boundary_le_nnnorm g z))

theorem nnnorm_rational_sub_le_max (f g : U.RationalFunctions) :
    ‖U.normedRationalEquiv.symm (f-g)‖₊ ≤
      max ‖U.normedRationalEquiv.symm f‖₊ ‖U.normedRationalEquiv.symm g‖₊ := by
  apply U.nnnorm_rational_le_of_boundary
  intro z
  exact ((U.rationalPoint ⟨z.1,U.boundary_subset z.2⟩).1.val.map_sub f g).trans
    (max_le_max (U.rationalValue_boundary_le_nnnorm f z) (U.rationalValue_boundary_le_nnnorm g z))

theorem nnnorm_rational_sum_le {ι : Type*} (s : Finset ι) (f : ι → U.RationalFunctions)
    (c : ℝ≥0) (hf : ∀ i ∈ s, ‖U.normedRationalEquiv.symm (f i)‖₊ ≤ c) :
    ‖U.normedRationalEquiv.symm (∑ i ∈ s, f i)‖₊ ≤ c := by
  apply U.nnnorm_rational_le_of_boundary
  intro z
  apply (U.rationalPoint ⟨z.1,U.boundary_subset z.2⟩).1.val.map_sum_le
  intro i hi
  exact (U.rationalValue_boundary_le_nnnorm (f i) z).trans (hf i hi)

/-- The actual ORIGINAL polynomial part has a derived sharp norm bound. -/
theorem nnnorm_principalPolynomial_le (A : K[X]) (n : ℕ) :
    ‖U.normedRationalEquiv.symm
      (algebraMap K[X] U.RationalFunctions (U.principalPolynomial A n))‖₊ ≤
      ‖U.normedRationalEquiv.symm (U.commonRationalFraction A n)‖₊ := by
  have he : algebraMap K[X] U.RationalFunctions (U.principalPolynomial A n) =
      U.commonRationalFraction A n-∑ j, U.holePrincipalPart A j n := by
    rw [U.commonRationalFraction_decomposition]
    ring
  rw [he]
  exact (U.nnnorm_rational_sub_le_max _ _).trans (max_le le_rfl
    (U.nnnorm_rational_sum_le _ _ _ fun j _ => U.nnnorm_holePrincipalPart_le A j n))

/-- The WHOLE original norm is exactly the maximum of the constructed component norms. -/
theorem nnnorm_commonFraction_decomposition (A : K[X]) (n : ℕ) :
    ‖U.normedRationalEquiv.symm (U.commonRationalFraction A n)‖₊ =
      max ‖U.normedRationalEquiv.symm
        (algebraMap K[X] U.RationalFunctions (U.principalPolynomial A n))‖₊
        (Finset.univ.sup fun j => ‖U.normedRationalEquiv.symm (U.holePrincipalPart A j n)‖₊) := by
  apply le_antisymm
  · conv_lhs => rw [U.commonRationalFraction_decomposition]
    exact (U.nnnorm_rational_add_le_max _ _).trans (max_le_max le_rfl
      (U.nnnorm_rational_sum_le _ _ _ fun j hj => Finset.le_sup
        (f := fun j => ‖U.normedRationalEquiv.symm (U.holePrincipalPart A j n)‖₊) hj))
  · exact max_le (U.nnnorm_principalPolynomial_le A n)
      (Finset.sup_le fun j _ => U.nnnorm_holePrincipalPart_le A j n)

/-- Every actual rational function admits a constructed, sharply bounded ORIGINAL proper-fraction decomposition. -/
theorem exists_bounded_rational_decomposition (f : U.RationalFunctions) :
    ∃ (P : K[X]) (n : ℕ) (R : Fin m → K[X]),
      (∀ j, (R j).degree < n) ∧
      let part := fun j => algebraMap K[X] U.RationalFunctions
        (Polynomial.algEquivAevalXAddC (-U.holeCenter j) (R j))*(U.rationalHoleInverse j)^n
      f = algebraMap K[X] U.RationalFunctions P+∑ j, part j ∧
      ‖U.normedRationalEquiv.symm (algebraMap K[X] U.RationalFunctions P)‖₊ ≤
        ‖U.normedRationalEquiv.symm f‖₊ ∧
      (∀ j, ‖U.normedRationalEquiv.symm (part j)‖₊ ≤ ‖U.normedRationalEquiv.symm f‖₊) ∧
      ‖U.normedRationalEquiv.symm f‖₊ =
        max ‖U.normedRationalEquiv.symm (algebraMap K[X] U.RationalFunctions P)‖₊
          (Finset.univ.sup fun j => ‖U.normedRationalEquiv.symm (part j)‖₊) := by
  obtain ⟨A,n,hf⟩ := Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f
  change f = U.commonRationalFraction A n at hf
  refine ⟨U.principalPolynomial A n,n,fun j => U.holePrincipalNumerator A j n,
    (fun j => U.holePrincipalNumerator_degree_lt A j n),?_⟩
  change f = _ ∧ _ ∧ (∀ j, ‖U.normedRationalEquiv.symm (U.holePrincipalPart A j n)‖₊ ≤ _) ∧ _
  rw [hf]
  exact ⟨U.commonRationalFraction_decomposition A n,U.nnnorm_principalPolynomial_le A n,
    (fun j => U.nnnorm_holePrincipalPart_le A j n),U.nnnorm_commonFraction_decomposition A n⟩
end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
