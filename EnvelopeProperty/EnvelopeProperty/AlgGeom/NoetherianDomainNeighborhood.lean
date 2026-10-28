import Hironaka.Scheme.Smooth.Adapted
import Mathlib.RingTheory.Localization.AtPrime.Basic
open AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.NoetherianDomainNeighborhood
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime]

theorem exists_away_injective :
    ∃ (s : R) (_hs : s ∉ p) (φ : Localization.Away s →+* Localization.AtPrime p),
      φ.comp (algebraMap R (Localization.Away s)) = algebraMap R (Localization.AtPrime p) ∧
        Function.Injective φ := by
  let I := RingHom.ker (algebraMap R (Localization.AtPrime p))
  have hI : I.map (algebraMap R (Localization.AtPrime p)) =
      (⊥ : Ideal R).map (algebraMap R (Localization.AtPrime p)) := by
    rw [Ideal.map_bot,Ideal.map_eq_bot_iff_le_ker]
  obtain ⟨s,hsp,hs⟩ := exists_mem_map_eq_map_of_localization p.primeCompl I ⊥
    (IsNoetherian.noetherian _) (IsNoetherian.noetherian _) hI
  have hu : IsUnit (algebraMap R (Localization.AtPrime p) s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hsp
  let φ : Localization.Away s →+* Localization.AtPrime p := IsLocalization.Away.lift s hu
  refine ⟨s,hsp,φ,IsLocalization.Away.lift_comp s hu,?_⟩
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨⟨a,t⟩,ht⟩ := IsLocalization.surj (Submonoid.powers s) x
  have ha : a ∈ I := by
    have h := congrArg φ ht
    rw [map_mul,IsLocalization.Away.lift_eq,IsLocalization.Away.lift_eq,
      (RingHom.mem_ker.mp hx),zero_mul] at h
    exact h.symm
  have haz : algebraMap R (Localization.Away s) a = 0 := by
    apply Ideal.mem_bot.mp
    have hi := hs (Localization.Away s)
    rw [Ideal.map_bot] at hi
    rw [← hi]
    exact Ideal.mem_map_of_mem _ ha
  apply (IsLocalization.map_units (Localization.Away s) t).mul_left_injective
  simpa only [zero_mul] using ht.trans haz

theorem exists_away_isDomain [IsDomain (Localization.AtPrime p)] :
    ∃ s ∉ p, IsDomain (Localization.Away s) := by
  obtain ⟨s,hs,φ,-,hi⟩ := exists_away_injective p
  exact ⟨s,hs,Function.Injective.isDomain φ hi⟩

end EnvelopeProperty.NoetherianDomainNeighborhood
