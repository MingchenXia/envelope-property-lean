import Mathlib.Algebra.Module.Equiv.Basic

/-! # A genuine whole line frame normalized by the SAME original nonzero element -/

namespace EnvelopeProperty.NormalizedLineFrame
universe u v
noncomputable section
variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]

private theorem originalFrameImageNeZero (e : M ≃ₗ[F] F) (m : M) (hm : m ≠ 0) : e m ≠ 0 :=
  fun h => hm (e.injective (h.trans (e.map_zero).symm))

/-- The SAME entire original line frame, normalized by SAME original nonzero element. -/
def normalize (e : M ≃ₗ[F] F) (m : M) (hm : m ≠ 0) : M ≃ₗ[F] F :=
  e.trans (LinearEquiv.smulOfNeZero F F (e m) (originalFrameImageNeZero e m hm)).symm

/-- EVERY original element retains its exact original normalized coefficient. -/
theorem normalize_apply (e : M ≃ₗ[F] F) (m : M) (hm : m ≠ 0) (x : M) :
    normalize e m hm x = e x / e m := by
  change (e m)⁻¹ * e x = e x / e m
  rw [div_eq_mul_inv, mul_comm]

/-- The original normalizing element has exactly original coefficient one. -/
theorem normalize_generator (e : M ≃ₗ[F] F) (m : M) (hm : m ≠ 0) :
    normalize e m hm m = 1 := by
  rw [normalize_apply, div_self (originalFrameImageNeZero e m hm)]

/-- The ENTIRE original normalized coefficient frame is independent of
EVERY original line frame, with no change-of-frame compatibility premise. -/
theorem normalize_independent (e e' : M ≃ₗ[F] F) (m : M) (hm : m ≠ 0) :
    normalize e m hm = normalize e' m hm := by
  apply LinearEquiv.ext
  intro x
  have hx : x = (e x / e m) • m := by
    apply e.injective
    rw [e.map_smul]
    exact (div_mul_cancel₀ (e x) (originalFrameImageNeZero e m hm)).symm
  rw [hx]
  simp only [map_smul, normalize_generator, smul_eq_mul, mul_one]

end
end EnvelopeProperty.NormalizedLineFrame
