import EnvelopeProperty.Cartier.Polynomial
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Degree-zero Cartier exactness on the original polynomial cotangent module

Actual standard polynomial partials detect the original coefficients. Their simultaneous
kernel is proved to be the image of actual Frobenius, by constructing the original rootPoly.
The actual universal cotangent basis gives the SAME original universal differential kernel.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.PolynomialDifferentialKernel
open MvPolynomial
open scoped Classical

/-- The SAME actual universal differential vanishes exactly when ALL its original standard
polynomial partial derivatives vanish. This uses the original whole cotangent basis. -/
theorem D_eq_zero_iff_partials_eq_zero {R σ : Type*} [CommRing R]
    (f : MvPolynomial σ R) :
    KaehlerDifferential.D R (MvPolynomial σ R) f = 0 ↔ ∀ i, pderiv i f = 0 := by
  constructor
  · intro hf i
    have h := KaehlerDifferential.mvPolynomialBasis_repr_apply R σ f i
    rw [hf, map_zero, Finsupp.zero_apply] at h
    exact h.symm
  · intro hf
    apply (KaehlerDifferential.mvPolynomialBasis R σ).repr.injective
    apply Finsupp.ext
    intro i
    simpa only [map_zero, Finsupp.zero_apply,
      KaehlerDifferential.mvPolynomialBasis_repr_apply] using hf i

variable {k σ : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [Fintype σ] [DecidableEq σ]

omit [Fact p.Prime] [Fintype σ] in
/-- An original coefficient whose exponent is not divisible by p in one coordinate is forced
zero by the original actual standard partial equations. -/
theorem coeff_eq_zero_of_not_dvd (f : MvPolynomial σ k) (hf : ∀ i, pderiv i f = 0)
    (d : σ →₀ ℕ) (i : σ) (hi : ¬ p ∣ d i) : coeff d f = 0 := by
  have hdi : 0 < d i := Nat.pos_of_ne_zero (fun h => hi (h ▸ dvd_zero p))
  let e : σ →₀ ℕ := d - Finsupp.single i 1
  have hle : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using (Nat.succ_le_iff.mpr hdi)
    · simp only [Finsupp.single_eq_of_ne hji, zero_le]
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hle
  have hei : e i + 1 = d i := by
    have h := DFunLike.congr_fun he i
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
  have hcast : (e i : k) + 1 = (d i : k) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : k)) hei
  have h := congrArg (coeff e) (hf i)
  rw [coeff_pderiv, coeff_zero, he, hcast] at h
  exact (mul_eq_zero.mp h).resolve_right
    (fun hz => hi ((CharP.cast_eq_zero_iff k p (d i)).mp hz))

variable [PerfectRing k p]

/-- Every actual nonzero Frobenius digit coefficient polynomial vanishes; no coefficient
support or Frobenius-image certificate is supplied. -/
theorem rootPoly_nonzero_digit_eq_zero (f : MvPolynomial σ k) (hf : ∀ i, pderiv i f = 0)
    (a : Box σ p) (ha : a ≠ 0) : rootPoly p 1 a.toFinsupp f = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hai : (a i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  ext d
  have hnot : ¬ p ∣ (p • d + a.toFinsupp) i := by
    intro hd
    have hmod := Nat.mod_eq_zero_of_dvd hd
    have he : (p • d + a.toFinsupp) i % p = (a i : ℕ) := by
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Box.toFinsupp_apply,
        Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, zero_add,
        Nat.mod_eq_of_lt (a i).isLt]
    rw [he] at hmod
    exact hai hmod
  rw [coeff_rootPoly, pow_one, coeff_eq_zero_of_not_dvd p f hf _ i hnot, map_zero, coeff_zero]

/-- The actual original zero-digit coefficient polynomial is an actual pth root of the SAME
original polynomial whenever its original standard partials vanish. -/
theorem rootPoly_zero_pow_eq (f : MvPolynomial σ k) (hf : ∀ i, pderiv i f = 0) :
    rootPoly p 1 0 f ^ p = f := by
  have hzero : (0 : Box σ p).toFinsupp = 0 := by ext i; rfl
  have hmono : mono (X : σ → MvPolynomial σ k) (0 : Box σ p).toNat = 1 := by
    simp only [mono, Box.toNat, Pi.zero_apply, Fin.val_zero, pow_zero, Finset.prod_const_one]
  have h := sum_rootPoly p f
  rw [Finset.sum_eq_single (0 : Box σ p)] at h
  · simpa only [hzero, hmono, mul_one] using h
  · intro a _ ha
    rw [rootPoly_nonzero_digit_eq_zero p f hf a ha, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul]
  · intro ha
    exact (ha (Finset.mem_univ _)).elim

/-- Degree-zero Cartier exactness for the ORIGINAL standard polynomial partials: their ENTIRE
simultaneous kernel is the actual Frobenius image, with root existence DERIVED internally. -/
theorem partials_eq_zero_iff_exists_pow (f : MvPolynomial σ k) :
    (∀ i, pderiv i f = 0) ↔ ∃ g : MvPolynomial σ k, g ^ p = f := by
  constructor
  · intro hf
    exact ⟨rootPoly p 1 0 f, rootPoly_zero_pow_eq p f hf⟩
  · rintro ⟨g, rfl⟩ i
    rw [pderiv_pow, CharP.cast_eq_zero (MvPolynomial σ k) p, zero_mul, zero_mul]

/-- The SAME actual universal cotangent differential has exactly the ORIGINAL Frobenius image
as its whole kernel. No p-basis, derivative matching, lift, or exactness premise is added. -/
theorem D_eq_zero_iff_exists_pow (f : MvPolynomial σ k) :
    KaehlerDifferential.D k (MvPolynomial σ k) f = 0 ↔
      ∃ g : MvPolynomial σ k, g ^ p = f :=
  (D_eq_zero_iff_partials_eq_zero f).trans (partials_eq_zero_iff_exists_pow p f)

end EnvelopeProperty.Cartier.PolynomialDifferentialKernel
