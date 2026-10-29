import EnvelopeProperty.Potential.LinePolynomialSubharmonic
import EnvelopeProperty.Potential.LineHarmonicRestriction
import EnvelopeProperty.Potential.LineRationalFunctions

/-! # Actual extended logarithms of localized rational functions -/

open scoped NNReal ENNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] {w : Valuation K ℝ≥0}

theorem IsLineSubharmonicOn.congr {u v : RelativeSpectrum w K[X] → EReal}
    {Ω : Set (RelativeSpectrum w K[X])} (hu : IsLineSubharmonicOn u Ω)
    (heq : ∀ x ∈ Ω, u x = v x) : IsLineSubharmonicOn v Ω where
  upperSemicontinuousOn := by
    intro x hx b hb
    have hbx : u x < b := by rw [heq x hx]; exact hb
    filter_upwards [hu.upperSemicontinuousOn x hx b hbx,self_mem_nhdsWithin] with y hy hyΩ
    rw [← heq y hyΩ]
    exact hy
  ne_top := by
    intro x hx
    rw [← heq x hx]
    exact hu.ne_top x hx
  comparison := by
    intro m U h hU hh hB x
    rw [← heq x.1 (hU x.2)]
    exact hu.comparison U h hU hh (by
      intro z hz
      rw [heq z.1 (hU z.2)]
      exact hB z hz) x

private theorem fc_log_nnreal_div (a b : ℝ≥0) (hb : b ≠ 0) :
    ENNReal.log ((a/b : ℝ≥0) : ℝ≥0∞) =
      ENNReal.log (a : ℝ≥0∞) + ((-Real.log (b : ℝ) : ℝ) : EReal) := by
  by_cases ha : a = 0
  · subst a
    simp
  rw [ENNReal.log_of_nnreal (div_ne_zero ha hb),ENNReal.log_of_nnreal ha,← EReal.coe_add,
    NNReal.coe_div,Real.log_div (by exact_mod_cast ha) (by exact_mod_cast hb),sub_eq_add_neg]

variable [IsAlgClosed K]

theorem isLineSubharmonicOn_logAbs_polynomialRatio (p q : K[X])
    (Ω : Set (RelativeSpectrum w K[X])) (hΩ : IsOpen Ω)
    (hq : ∀ x ∈ Ω, val x q ≠ 0) :
    IsLineSubharmonicOn (fun x => ENNReal.log ((val x p/val x q : ℝ≥0) : ℝ≥0∞)) Ω := by
  have hu := (isLineSubharmonicOn_logAbs_polynomial p Ω).add_harmonic
    (isLineHarmonicOn_polynomialRealLog q Ω hq).neg hΩ
  apply hu.congr
  intro x hx
  exact (fc_log_nnreal_div (val x p) (val x q) (hq x hx)).symm

namespace FCStandardAffinoid

variable {m : ℕ} (U : FCStandardAffinoid w m)

omit [IsAlgClosed K] in
/-- The actual localized-rational logarithm on the carrier, extended by bottom outside it. -/
def rationalLog (f : U.RationalFunctions) (x : RelativeSpectrum w K[X]) : EReal := by
  classical
  exact if hx : x ∈ U.carrier then ENNReal.log (U.rationalValue f ⟨x,hx⟩ : ℝ≥0∞) else ⊥

omit [IsAlgClosed K] in
theorem rationalLog_apply (f : U.RationalFunctions) (x : U.carrier) :
    U.rationalLog f x.1 = ENNReal.log (U.rationalValue f x : ℝ≥0∞) := by
  simp only [rationalLog,dif_pos x.2]

/-- Every element of the actual original localization has an actual subharmonic logarithm on the interior. -/
theorem isLineSubharmonicOn_rationalLog (f : U.RationalFunctions) :
    IsLineSubharmonicOn (U.rationalLog f) (interior U.carrier) := by
  obtain ⟨p,n,hf⟩ := Spectrum.Away.exists_eq_mk' U.RationalFunctions U.denominatorPolynomial f
  have hq : ∀ x ∈ interior U.carrier, val x (U.denominatorPolynomial^n) ≠ 0 := by
    intro x hx
    rw [map_pow]
    exact pow_ne_zero n (U.denominatorPolynomial_val_ne_zero ⟨x,interior_subset hx⟩)
  apply (isLineSubharmonicOn_logAbs_polynomialRatio p (U.denominatorPolynomial^n)
    (interior U.carrier) isOpen_interior hq).congr
  intro x hx
  rw [U.rationalLog_apply f ⟨x,interior_subset hx⟩,hf,U.rationalValue_mk',map_pow]

end FCStandardAffinoid

end EnvelopeProperty.Berkovich.RelativeSpectrum
