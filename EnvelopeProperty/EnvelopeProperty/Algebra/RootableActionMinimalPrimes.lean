/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Ring.Aut
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

noncomputable section
namespace EnvelopeProperty

/-- A rootable group action preserving an original ideal fixes each of its
original minimal primes. The inverse action handles noncommutative groups. -/
theorem minimalPrime_comap_eq_self_of_rootable_action
    {E G : Type*} [CommRing E] [IsNoetherianRing E] [Group G] [RootableBy G ℕ]
    (ρ : G →* RingAut E) (I : Ideal E)
    (hI : ∀ s, I.comap (ρ s).toRingHom = I)
    {P : Ideal E} (hP : P ∈ I.minimalPrimes) (s : G) :
    P.comap (ρ s).toRingHom = P := by
  classical
  let M := I.minimalPrimes
  have hM (g : G) (Q : Ideal E) (hQ : Q ∈ M) :
      Q.comap (ρ g).toRingHom ∈ M := by
    have h := Ideal.minimalPrimes_comap_of_surjective
      (f := (ρ g).toRingHom) (ρ g).surjective hQ
    rwa [hI g] at h
  have hcomap (g h : G) (Q : Ideal E) :
      (Q.comap (ρ g).toRingHom).comap (ρ h).toRingHom =
        Q.comap (ρ (g * h)).toRingHom := by
    rw [Ideal.comap_comap]
    congr 1
    ext x
    change (ρ g) ((ρ h) x) = (ρ (g * h)) x
    rw [map_mul, RingAut.mul_apply]
  have hone (Q : Ideal E) : Q.comap (ρ 1).toRingHom = Q := by
    rw [map_one]
    exact Ideal.comap_id Q
  let π : G →* Equiv.Perm M :=
    { toFun := fun g =>
        { toFun := fun Q => ⟨Q.1.comap (ρ g⁻¹).toRingHom, hM g⁻¹ Q.1 Q.2⟩
          invFun := fun Q => ⟨Q.1.comap (ρ g).toRingHom, hM g Q.1 Q.2⟩
          left_inv := fun Q => Subtype.ext (by
            change (Q.1.comap (ρ g⁻¹).toRingHom).comap (ρ g).toRingHom = Q.1
            rw [hcomap, inv_mul_cancel, hone])
          right_inv := fun Q => Subtype.ext (by
            change (Q.1.comap (ρ g).toRingHom).comap (ρ g⁻¹).toRingHom = Q.1
            rw [hcomap, mul_inv_cancel, hone]) }
      map_one' := Equiv.ext fun Q => Subtype.ext (by
        change Q.1.comap (ρ ((1 : G)⁻¹)).toRingHom = Q.1
        rw [inv_one, hone])
      map_mul' := fun g h => Equiv.ext fun Q => Subtype.ext (by
        change Q.1.comap (ρ ((g * h)⁻¹)).toRingHom =
          (Q.1.comap (ρ h⁻¹).toRingHom).comap (ρ g⁻¹).toRingHom
        rw [hcomap, mul_inv_rev]) }
  let : Finite M := (Ideal.finite_minimalPrimes_of_isNoetherianRing E I).to_subtype
  have hN : 0 < Nat.card (Equiv.Perm M) := Nat.card_pos
  have htrivial (g : G) : π g = 1 := by
    obtain ⟨z, hz⟩ := RootableBy.surjective_pow G ℕ hN.ne' g
    rw [← hz, map_pow, pow_card_eq_one']
  have hfix := congrArg Subtype.val (Equiv.ext_iff.mp (htrivial s⁻¹) ⟨P, hP⟩)
  change P.comap (ρ ((s⁻¹)⁻¹)).toRingHom = P at hfix
  simpa only [inv_inv] using hfix

end EnvelopeProperty
