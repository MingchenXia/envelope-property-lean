import TranscendentalNakamaye.Pending.HironakaActualPolynomialAnalyticFlatness

/-!
# Actual polynomial germs at arbitrary complex centers

The pointwise maps translate globally defined polynomials and evaluate them
in the original whole holomorphic germ ring. Arbitrary origin germs are never
translated to other points. The eventual ideal-detection theorem concerns
original ideals, not their radicals or just their complex zero loci.
-/

set_option autoImplicit false

noncomputable section

namespace TranscendentalNakamaye.Pending.PolynomialPointAnalyticMap

open Set MvPolynomial
open TranscendentalNakamaye.FirstPass
open TranscendentalNakamaye.Pending
open HironakaActualOriginalTaylorPolynomial HironakaRelativeNormalIdeal

variable {n : ℕ}

/-- Translation is defined on global polynomials, with its actual inverse. -/
def polynomialTranslation (x : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  AlgEquiv.ofAlgHom
    (aeval fun i => X i + C (x i))
    (aeval fun i => X i - C (x i))
    (by ext i; simp)
    (by ext i; simp)

/-- The actual germ at the origin of the original polynomial translated by x. -/
def polynomialGermMap (x : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] HolGerm (ComplexModel (0 + n)) :=
  (originalPolynomialEval n).comp (polynomialTranslation x).toAlgHom

/-- Every original variable retains precisely its coordinate germ and point value. -/
theorem polynomialGermMap_X (x : Fin n → ℂ) (i : Fin n) :
    polynomialGermMap x (X i) = normalCoordinate 0 n i + HolGerm.constHom (x i) := by
  change (originalPolynomialEval n) ((aeval fun j => X j + C (x j)) (X i)) = _
  rw [aeval_X, map_add]
  simp only [originalPolynomialEval, aeval_X, aeval_C]
  rfl

/-- The original polynomial value at x is the actual value of its analytic germ. -/
theorem eval_polynomialGermMap (x : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    HolGerm.eval (polynomialGermMap x p) = MvPolynomial.eval x p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show polynomialGermMap x (C c) = HolGerm.constHom c from
      (polynomialGermMap x).commutes c]
    simp only [HolGerm.eval_constHom, eval_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    have hzero : HolGerm.eval (normalCoordinate 0 n i) = 0 := rfl
    simp only [map_mul, polynomialGermMap_X, map_add, hp, HolGerm.eval_constHom,
      hzero, zero_add, eval_X]

/-- Flatness is transported from the existing actual whole origin evaluation. -/
theorem polynomialGermMap_flat (x : Fin n → ℂ) :
    (polynomialGermMap x).toRingHom.Flat := by
  change ((originalPolynomialEval n).toRingHom.comp (polynomialTranslation x).toRingHom).Flat
  exact (RingHom.Flat.of_bijective (polynomialTranslation x).bijective).comp
    (HironakaActualPolynomialAnalyticFlatness.originalPolynomialEval_flat n)

end TranscendentalNakamaye.Pending.PolynomialPointAnalyticMap
