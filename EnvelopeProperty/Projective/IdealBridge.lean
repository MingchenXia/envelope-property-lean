/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.Basic
import EnvelopeProperty.Berkovich.IdealFunctions

/-!
# Intrinsic ideal calculus for the normalized projective model

The polynomial Gauss extension of a `ProjBerk` point is bounded on its coefficient ring.
Its existing `phiNorm` and `phiIdeal` functions are exactly the intrinsic `Berk.idealNorm`
and `Berk.idealLog`, and hence the corresponding general spectrum functions.

These representation equalities connect the normalized projective model to the reusable
ideal calculus. They do not identify that model with a canonical projective analytification
or construct the source's coherent ideal sheaf functions.
-/

open scoped NNReal ENNReal Polynomial

noncomputable section

namespace EnvelopeProperty.ProjBerk

variable {k : Type*} [Field k] {n : ℕ}

/-- The normalized polynomial Gauss extension is bounded on every coefficient-ring element. -/
theorem gaussExt_isBounded (v : ProjBerk k n) : Berk.IsBounded (gaussExt v) :=
  gaussExt_val_le_one v

/-- The projective-model ideal norm is the intrinsic affine ideal norm at the Gauss extension. -/
theorem phiNorm_eq_idealNorm (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X])
    (v : ProjBerk k n) : phiNorm I v = Berk.idealNorm I (gaussExt v) := rfl

/-- The projective-model ideal function is the intrinsic logarithmic ideal function. -/
theorem phiIdeal_eq_idealLog (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X])
    (v : ProjBerk k n) : phiIdeal I v = Berk.idealLog I (gaussExt v) := by
  rw [phiIdeal_eq_log_phiNorm, phiNorm_eq_idealNorm]
  rfl

/-- Forgetting the prescribed trivial base values preserves the projective-model ideal norm. -/
theorem phiNorm_eq_spectrumIdealNorm (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X])
    (v : ProjBerk k n) :
    phiNorm I v = Berkovich.Spectrum.idealNorm I (Berk.toSpectrum (gaussExt v)) := rfl

/-- The logarithmic projective-model ideal function also agrees with the generic spectrum API. -/
theorem phiIdeal_eq_spectrumIdealLog (I : Ideal (MvPolynomial (Fin (n + 1)) k)[X])
    (v : ProjBerk k n) :
    phiIdeal I v = Berkovich.Spectrum.idealLog I (Berk.toSpectrum (gaussExt v)) :=
  phiIdeal_eq_idealLog I v

end EnvelopeProperty.ProjBerk
