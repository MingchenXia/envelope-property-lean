/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.ArtinianLocalFactors

/-!
# Exact evaluation of genuine Artinian CRT idempotents

The actual maximal-power CRT idempotent has value one under ring maps with its
own maximal kernel and zero under every other genuine maximal kernel. This is
a whole ring-map statement retaining nilpotents and arbitrary coefficient rings.
-/
open scoped Classical
noncomputable section
namespace EnvelopeProperty.ArtinianFactors
/-- The actual Chinese-remainder idempotent evaluates to one exactly at its own maximal kernel, and zero at every other genuine maximal kernel. -/
theorem localIdempotent_map {E C : Type*} [CommRing E] [IsArtinianRing E] [CommRing C]
    (m n : MaximalSpectrum E) (f : E →+* C) (hf : RingHom.ker f = n.asIdeal) :
    f (localIdempotent E m) = if n = m then 1 else 0 := by
  classical
  let t : E := if n = m then 1 else 0
  have hclass : algebraMap E (PowerFactor E n) (localIdempotent E m) =
      algebraMap E (PowerFactor E n) t := by
    by_cases hnm : n = m
    · subst n
      simpa only [t, if_pos rfl, map_one, Pi.single_eq_same, powerEquiv_apply] using
        congrFun (powerEquiv_localIdempotent E m) m
    · simpa only [t, if_neg hnm, map_zero, Pi.single_eq_of_ne hnm, powerEquiv_apply] using
        congrFun (powerEquiv_localIdempotent E m) n
  have hmem : localIdempotent E m - t ∈ n.asIdeal ^ exponent E :=
    Ideal.Quotient.eq.mp hclass
  have hz : f (localIdempotent E m - t) = 0 := by
    rw [← RingHom.mem_ker, hf]
    exact Ideal.pow_le_self (Nat.ne_of_gt (exponent_pos E)) hmem
  rw [map_sub, sub_eq_zero] at hz
  simpa [t] using hz
end EnvelopeProperty.ArtinianFactors
