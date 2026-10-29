/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.MultiplierAwayLocalization
import EnvelopeProperty.Char0.AsymptoticMultiplierIdeal

/-!
# Actual principal localization of the original asymptotic multiplier ideal

The same original sequence is extended term by term. Locality is proved from
locality of the full original-source all-divisorial-DVR multiplier ideals.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- The genuine asymptotic multiplier ideal of the original nonzero sequence
commutes with actual principal localization, without a supplied locality property. -/
theorem map_asymptoticMultiplierIdeal_source_away
    (C E : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (hCE : C ≤ E) (s : C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization.Away s E)
    (J : ℕ → Ideal C) (hne : ∀ q, 0 < q → J q ≠ ⊥) (m : ℕ) :
    letI : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    (asymptoticMultiplierIdeal C J hne m).map (Subalgebra.inclusion hCE).toRingHom =
      asymptoticMultiplierIdeal E (fun q => (J q).map (Subalgebra.inclusion hCE).toRingHom)
        (fun q hq => (Ideal.map_eq_bot_iff_of_injective
          (Subalgebra.inclusion_injective hCE)).mp.mt (hne q hq)) m := by
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  simp only [asymptoticMultiplierIdeal, Ideal.map_iSup]
  apply iSup_congr
  intro q
  apply iSup_congr
  intro hq
  exact map_valuativeMultiplierIdeal_source_away C E hCE s hlocal (J q) (hne q hq) _

end EnvelopeProperty.Char0
