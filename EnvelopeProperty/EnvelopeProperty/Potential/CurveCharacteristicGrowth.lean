import EnvelopeProperty.Potential.CurveCharacteristicFactors
import EnvelopeProperty.Potential.LineLiouville
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Original characteristic polynomials control actual analytic factor growth -/

open scoped NNReal Polynomial TensorProduct Classical
open Polynomial
noncomputable section

namespace EnvelopeProperty

/-- A genuine complementary monic factor bounds every original coefficient
through actual Gauss multiplicativity, over an arbitrary commutative ring. -/
theorem valuation_coeff_le_gauss_of_monic_complement {R : Type*} [CommRing R]
    (v : Valuation R ℝ≥0) (A D P : R[X]) (hD : D.Monic) (hprod : A * D = P)
    (n : ℕ) : v (A.coeff n) ≤ gaussValuation v 1 P := by
  have h1 : 1 ≤ gaussValuation v 1 D := by
    change 1 ≤ gaussFun v 1 D
    have h := le_gaussFun v 1 D D.natDegree
    simpa only [hD.coeff_natDegree, map_one, one_pow, mul_one] using h
  have hc : v (A.coeff n) ≤ gaussValuation v 1 A := by
    change _ ≤ gaussFun v 1 A
    simpa only [one_pow, mul_one] using le_gaussFun v 1 A n
  apply hc.trans
  calc
    gaussValuation v 1 A ≤ gaussValuation v 1 A * gaussValuation v 1 D :=
      le_mul_of_one_le_right' h1
    _ = gaussValuation v 1 P := by rw [← map_mul, hprod]

/-- Over a field the actual complementary quotient summands derive the full
coefficient bound, retaining nilpotents and arbitrary genuine idempotents. -/
theorem valuation_coeff_characteristicFactor_le {F E : Type*} [Field F] [CommRing E]
    [Algebra F E] [Module.Finite F E] (v : Valuation F ℝ≥0)
    {e : E} (he : IsIdempotentElem e) (b : E) (n : ℕ) :
    v ((IdempotentSummand.characteristicFactor (R := F) he b).coeff n) ≤
      gaussValuation v 1 (Algebra.lmul F E b).charpoly := by
  exact valuation_coeff_le_gauss_of_monic_complement v _ _ _
    (IdempotentSummand.characteristicFactor_eq_charpoly (R := F) he.one_sub b).2.1
    (IdempotentSummand.characteristicFactor_mul_one_sub (R := F) he b) n

end EnvelopeProperty

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- Every actual analytic factor coefficient is controlled by the original
whole multiplication characteristic polynomial in the same completed field. -/
theorem valuation_coeff_curveCharacteristicFactor_le_charpoly
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis}
    (he : IsIdempotentElem e) (b : B) (x : U.carrier) (n : ℕ) :
    let := Module.Finite.of_basis basis
    let := Module.Free.of_basis basis
    NormedField.valuation (U.evaluationToH x ((U.curveCharacteristicFactor basis he b).coeff n)) ≤
      gaussValuation (NormedField.valuation (K := Spectrum.H x.1.1)) 1
        (Polynomial.map (algebraMap K[X] (Spectrum.H x.1.1))
          (Algebra.lmul K[X] B b).charpoly) := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  have h := valuation_coeff_characteristicFactor_le (NormedField.valuation (K := Spectrum.H x.1.1))
    (U.curveIdempotentSpecialization_isIdempotent basis he x)
    ((1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b) n
  rw [← U.map_curveCharacteristicFactor basis he b x, Polynomial.coeff_map,
    lmul_one_tmul_eq_baseChange, LinearMap.charpoly_baseChange] at h
  exact h

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace EnvelopeProperty

/-- Every actual Gauss polynomial has its explicit original degree growth. -/
theorem gaussFun_le_unitRadius_mul_degree {R : Type*} [CommRing R]
    (v : Valuation R ℝ≥0) (r : ℝ≥0) (p : R[X]) :
    gaussFun v r p ≤ gaussFun v 1 p * (max 1 r) ^ p.natDegree := by
  classical
  change p.support.sup (fun i => v (p.coeff i) * r ^ i) ≤ _
  apply Finset.sup_le
  intro i hi
  have hc : v (p.coeff i) ≤ gaussFun v 1 p := by
    simpa only [one_pow, mul_one] using le_gaussFun v 1 p i
  have hp : r ^ i ≤ (max 1 r) ^ p.natDegree :=
    (pow_le_pow_left' (le_max_right 1 r) i).trans
      (pow_le_pow_right₀ (le_max_left 1 r) (Polynomial.le_natDegree_of_mem_supp i hi))
  exact mul_le_mul' hc hp

/-- Actual Gauss valuations respect every original valuation-preserving
coefficient map, whether or not that map is injective. -/
theorem gaussValuation_map_preserving {R S : Type*} [CommRing R] [CommRing S]
    (v : Valuation R ℝ≥0) (q : Valuation S ℝ≥0) (f : R →+* S)
    (hf : ∀ a, q (f a) = v a) (r : ℝ≥0) (P : R[X]) :
    gaussValuation q r (P.map f) = gaussValuation v r P := by
  classical
  change gaussFun q r (P.map f) = gaussFun v r P
  rw [gaussFun_eq_sup_of_subset q r _ (Polynomial.support_map_subset _ _)]
  unfold gaussFun
  apply Finset.sup_congr rfl
  intro i hi
  rw [Polynomial.coeff_map, hf]

end EnvelopeProperty

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The original finitely many polynomial coefficients construct a single
polynomial-growth bound on every actual base disc, including radius zero. -/
theorem exists_disc_polynomial_gauss_growth (P : K[X][X]) :
    ∃ (C : ℝ≥0) (N : ℕ), ∀ (r : ℝ≥0)
      (x : RelativeSpectrum (NormedField.valuation (K := K)) K[X]),
      val x Polynomial.X ≤ r →
        gaussValuation x.1.val 1 P ≤ C * (max 1 r) ^ N := by
  classical
  let C := P.support.sup (fun i => gaussFun (NormedField.valuation (K := K)) 1 (P.coeff i))
  let N := P.support.sup (fun i => (P.coeff i).natDegree)
  refine ⟨C, N, fun r x hx => ?_⟩
  change P.support.sup (fun i => x.1.val (P.coeff i) * 1 ^ i) ≤ _
  apply Finset.sup_le
  intro i hi
  simp only [one_pow, mul_one]
  calc
    x.1.val (P.coeff i) ≤ gaussFun (NormedField.valuation (K := K)) r (P.coeff i) :=
      val_le_gauss_val (fc_proj_eq_self x) hx (P.coeff i)
    _ ≤ gaussFun (NormedField.valuation (K := K)) 1 (P.coeff i) *
        (max 1 r) ^ (P.coeff i).natDegree := gaussFun_le_unitRadius_mul_degree _ _ _
    _ ≤ C * (max 1 r) ^ N := mul_le_mul'
      (Finset.le_sup (f := fun i => gaussFun (NormedField.valuation (K := K)) 1 (P.coeff i)) hi)
      (pow_le_pow_right₀ (le_max_left 1 r) (Finset.le_sup (f := fun i => (P.coeff i).natDegree) hi))

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]
  [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The original whole multiplication polynomial constructs one polynomial
growth bound for every coefficient of every actual selected factor on all
whole discs. No compatible family or bound is an input. -/
theorem exists_curveCharacteristicFactor_disc_growth (basis : Module.Basis ι K[X] B) (b : B) :
    ∃ (C : ℝ≥0) (N : ℕ), ∀ (r : ℝ≥0)
      (e : (zeroDisc (K := K) r).CurveAnalyticAlgebra basis)
      (he : IsIdempotentElem e) (n : ℕ),
      ‖((zeroDisc (K := K) r).curveCharacteristicFactor basis he b).coeff n‖₊ ≤
        C * (max 1 r) ^ N := by
  classical
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  obtain ⟨C, N, hCN⟩ := exists_disc_polynomial_gauss_growth (Algebra.lmul K[X] B b).charpoly
  refine ⟨C, N, fun r e he n => ?_⟩
  let D := zeroDisc (K := K) r
  let _ : Fintype D.boundary := D.rationalBoundaryFintype
  rw [D.nnnorm_eq_boundary_max]
  apply Finset.sup_le
  intro z hz
  let x : D.carrier := ⟨z.1, D.boundary_subset z.2⟩
  change NormedField.valuation (D.evaluationToH x _) ≤ _
  have h := D.valuation_coeff_curveCharacteristicFactor_le_charpoly basis he b x n
  dsimp only at h
  rw [gaussValuation_map_preserving x.1.1.val
    (NormedField.valuation (K := Spectrum.H x.1.1))
    (algebraMap K[X] (Spectrum.H x.1.1))
    (fun p => Spectrum.nnnorm_toH x.1.1 p)] at h
  apply h.trans (hCN r x.1 ?_)
  simpa only [D, zeroDisc, ofDisc, val, Polynomial.C_0, sub_zero] using x.2.1

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
