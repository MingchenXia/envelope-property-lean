/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.MultiplierSourceLocalization
import EnvelopeProperty.Char0.FiniteMultiplierValuations
import EnvelopeProperty.Algebra.SubalgebraLocalization

/-!
# Full original multiplier ideals commute with actual principal localization

The reverse inclusion uses the genuine internally produced finite DVR family;
no locality or finite valuation testing certificate is supplied.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- A large enough power of an actual original denominator which is a nonunit
at the actual DVR puts every original numerator into its intrinsic contribution. -/
theorem pow_mul_mem_intrinsicDVRContribution_of_nonunit
    (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCV : C ≤ V) (I : Ideal C) (hI : I ≠ ⊥)
    (q : ℚ) (s c : C) (hs : ¬ IsUnit (Subalgebra.inclusion hCV s)) (N : ℕ)
    (hN : ⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ)⌋₊ ≤ N) :
    s ^ N * c ∈ intrinsicDVRMultiplierContribution C V hCV I hI q := by
  change (Subalgebra.inclusion hCV).toRingHom (s ^ N * c) ∈
    IsLocalRing.maximalIdeal V ^ (⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom)).toNat : ℚ)⌋₊ -
      (dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV)).toNat)
  rw [map_mul, map_pow]
  apply Ideal.mul_mem_right
  apply Ideal.pow_le_pow_right ((Nat.sub_le _ _).trans hN)
  apply Ideal.pow_mem_pow
  change ¬ IsUnit ((Subalgebra.inclusion hCV).toRingHom s) at hs
  exact (IsLocalRing.mem_maximalIdeal _).mpr hs

/-- The FULL original-source all-divisorial-DVR multiplier ideal commutes with
actual principal localization on an arbitrary original smooth characteristic-zero
source; the finite testing family and all locality properties are derived. -/
theorem map_valuativeMultiplierIdeal_source_away
    (C E : Subalgebra k K) [IsFractionRing C K]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (hCE : C ≤ E) (s : C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization.Away s E)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    letI : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    (valuativeMultiplierIdeal C I hI q).map (Subalgebra.inclusion hCE).toRingHom =
      valuativeMultiplierIdeal E (I.map (Subalgebra.inclusion hCE).toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCE)).mp.mt hI) q := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let : IsLocalization.Away s E := hlocal
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  apply le_antisymm
    (map_valuativeMultiplierIdeal_le_source_localization C E hCE (Submonoid.powers s) hlocal I hI q)
  intro e he
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) e
  have hcE : algebraMap C E c ∈ valuativeMultiplierIdeal E
      (I.map (Subalgebra.inclusion hCE).toRingHom)
      ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCE)).mp.mt hI) q := by
    rw [← IsLocalization.mk'_spec E c t]
    exact Ideal.mul_mem_right _ _ he
  obtain ⟨S, hS, htest⟩ := exists_finite_divisorialDVRs_forall_multiplier_exponents C I hI
  let cut (V : divisorialDVRs C) : ℕ := by
    letI := V.property.2.1
    exact ⌊q * ((dvrIdealOrder (I.map (Subalgebra.inclusion V.property.1).toRingHom)).toNat : ℚ)⌋₊
  let N := hS.toFinset.sup cut
  have hc : s ^ N * c ∈ valuativeMultiplierIdeal C I hI q := by
    apply (htest q (s ^ N * c)).mpr
    intro V hVS
    let := V.property.2.1
    let := V.property.2.2.1
    let := V.property.2.2.2
    by_cases hs : IsUnit (Subalgebra.inclusion V.property.1 s)
    · have hu (y : Submonoid.powers s) : IsUnit ((Subalgebra.inclusion V.property.1).toRingHom y.val) := by
        obtain ⟨n, hn⟩ := y.property
        rw [← hn, map_pow]
        exact hs.pow n
      have hEV : E ≤ V.val := le_of_source_localization_units
        C E V.val hCE V.property.1 (Submonoid.powers s) hlocal hu
      have hmemE := valuativeMultiplierIdeal_le_contribution E V.val hEV
        (I.map (Subalgebra.inclusion hCE).toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCE)).mp.mt hI) q hcE
      have hcV : c ∈ intrinsicDVRMultiplierContribution C V.val V.property.1 I hI q := by
        rw [intrinsicDVRMultiplierContribution_source_localization
          C E V.val hCE hEV (Submonoid.powers s) hlocal I hI q]
        exact hmemE
      exact Ideal.mul_mem_left _ (s ^ N) hcV
    · apply pow_mul_mem_intrinsicDVRContribution_of_nonunit C V.val V.property.1 I hI q s c hs N
      exact Finset.le_sup (f := cut) (hS.mem_toFinset.mpr hVS)
  change IsLocalization.mk' E c t ∈ (valuativeMultiplierIdeal C I hI q).map (algebraMap C E)
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  exact ⟨s ^ N, ⟨N, rfl⟩, hc⟩

end EnvelopeProperty.Char0
