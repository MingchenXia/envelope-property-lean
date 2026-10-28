import DeJongAlterations.Geometry.ProperSteinProjectiveCechPolynomialLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Actual empty-coordinate Laurent pieces reconstruct original homogeneous polynomials

The original coefficient ring is arbitrary. The native coordinate-product
localization equivalence has denominator one on the empty coordinate set.
The original polynomial embedding is injective, so no field model or
representation certificate is used.
-/

open MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

variable {R σ : Type u} [CommRing R] [LinearOrder σ] [Fintype σ]

omit [LinearOrder σ] in
/-- Original integral weight-one homogeneity at a natural degree is the actual original natural homogeneity. -/
theorem integral_homogeneous_isHomogeneous (F : MvPolynomial σ R) (e : ℕ)
    (hF : F ∈ polynomialIntegralGrading (e : ℤ)) : F.IsHomogeneous e := by
  intro d hd
  have h := hF hd
  simp only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one] at h ⊢
  exact_mod_cast h

/-- The ENTIRE actual empty-coordinate Laurent degree piece has an original homogeneous polynomial preimage, with its original coefficient ring. -/
theorem exists_polynomial_of_empty_laurent (e : ℕ)
    (l : subsetHomogeneousLaurentModule (K := R) (I := σ) (e : ℤ) ∅) :
    ∃ F : MvPolynomial σ R, F.IsHomogeneous e ∧ polynomialToProjectiveLaurent F = l.val := by
  obtain ⟨z, hz⟩ := polynomialCoordinateHomogeneousToLaurent_surjective
    (K := R) (I := σ) (e : ℤ) ∅ l
  obtain ⟨n, F, hF, hden⟩ := z.property
  have hFe : F ∈ polynomialIntegralGrading (e : ℤ) := by simpa using hF
  refine ⟨F, integral_homogeneous_isHomogeneous F e hFe, ?_⟩
  have hv := congrArg Subtype.val hz
  change polynomialCoordinateModuleToLaurent ∅ z.val = l.val at hv
  have hc := polynomialCoordinateModuleToLaurent_clear_polynomial (K := R) (I := σ) ∅ F n
  simp only [polynomialCoordinateProduct, Finset.prod_empty, map_one, one_pow, mul_one] at hc
  exact hc.symm.trans ((congrArg (polynomialCoordinateModuleToLaurent (K := R) (I := σ) ∅) hden).trans hv)

omit [LinearOrder σ] [Fintype σ] in
/-- The reconstructed original homogeneous polynomial is unique, by genuine polynomial/Laurent injectivity. -/
theorem polynomial_unique_of_same_laurent (F G : MvPolynomial σ R)
    (h : polynomialToProjectiveLaurent F = polynomialToProjectiveLaurent G) : F = G :=
  polynomialToProjectiveLaurent_injective h

omit [LinearOrder σ] in
/-- Compatibility with EVERY original singleton chart forces all Laurent exponents nonnegative; a single coordinate is included. -/
theorem compatible_singleton_laurent_mem_empty [Nonempty σ] (e : ℕ)
    (l : projectiveLaurentAlgebra R σ)
    (h : ∀ i : σ, l ∈ subsetHomogeneousLaurentModule (K := R) (I := σ) (e : ℤ) {i}) :
    l ∈ subsetHomogeneousLaurentModule (K := R) (I := σ) (e : ℤ) ∅ := by
  classical
  apply AddMonoidAlgebra.mem_supported.mpr
  intro α hα
  have hzero := AddMonoidAlgebra.mem_supported.mp (h (Classical.arbitrary σ)) hα
  refine ⟨hzero.1, fun j _ => ?_⟩
  rcases subsingleton_or_nontrivial σ with hs | ht
  · have hsum : (∑ i : σ, α i) = α j := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        exact (hij (hs.elim i j)).elim
      · simp
    have he : α j = (e : ℤ) := hsum.symm.trans hzero.1
    rw [he]
    exact Nat.cast_nonneg e
  · let := ht
    obtain ⟨i, hi⟩ := exists_ne j
    exact (AddMonoidAlgebra.mem_supported.mp (h i) hα).2 j (by simpa using hi.symm)

end EnvelopeProperty.Char0.RelativeProjectiveSectionPolynomial
