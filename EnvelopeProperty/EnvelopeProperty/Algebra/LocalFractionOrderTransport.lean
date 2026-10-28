import EnvelopeProperty.Algebra.SemilinearPrincipalLengths
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Entire native original fraction orders under the actual original local coefficient isomorphism -/
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.LocalFractionOrderTransport
variable {A D : Type u} [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]

/-- The SAME actual local ring isomorphism retains every native multiplicative principal quotient order. -/
theorem ordMonoidWithZeroHom_ringEquiv (e : A ≃+* D) (a : A) :
    Ring.ordMonoidWithZeroHom D (e a) = Ring.ordMonoidWithZeroHom A a := by
  by_cases ha : a = 0
  · simp [ha]
  have hea : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
  rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr hea),
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr ha),
    ← SemilinearPrincipalLengths.ord_ringEquiv e a]

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [IsNoetherianRing D] [Ring.KrullDimLE 1 D]
  {K L : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra D L] [IsFractionRing D L]

/-- The actual original local coefficient square retains the ENTIRE native fraction-order homomorphism. -/
theorem ordFrac_ringEquiv (e : A ≃+* D) (φ : K →+* L)
    (hcoeff : ∀ a : A, φ (algebraMap A K a) = algebraMap D L (e a)) (f : K) :
    Ring.ordFrac D (φ f) = Ring.ordFrac A f := by
  have hc (a : A) : Ring.ordFrac D (algebraMap D L (e a)) =
      Ring.ordFrac A (algebraMap A K a) := by
    by_cases ha : a = 0
    · simp [ha]
    have hea : e a ≠ 0 := (map_ne_zero_iff _ e.injective).mpr ha
    rw [Ring.ordFrac_eq_ord D hea, Ring.ordFrac_eq_ord A ha]
    exact ordMonoidWithZeroHom_ringEquiv e a
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) f
  rw [map_div₀, hcoeff a, hcoeff b, map_div₀, map_div₀, hc a, hc b]

end EnvelopeProperty.LocalFractionOrderTransport
