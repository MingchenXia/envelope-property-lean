import EnvelopeProperty.Char0.CoefficientUniverseTransport
import EnvelopeProperty.Char0.MixedUniverseDVRJacobian

/-! # Whole all-divisorial multiplier ideals under actual coefficient universe transport -/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.ValuativeUniverseTransport

open IsLocalRing IsDiscreteValuationRing
open CoefficientUniverseTransport

universe u v

variable {k K : Type u} {k' K' : Type v}
    [Field k] [Field K] [Algebra k K] [Field k'] [Field K'] [Algebra k' K']
    [CharZero k] [CharZero k']
    (ek : k ≃+* k') (eK : K ≃+* K')
    (he : ∀ a : k, eK (algebraMap k K a) = algebraMap k' K' (ek a))

/-- BOTH intrinsic coordinate choices are removed using actual internally transported residue bases. -/
theorem intrinsicDVRSourceJacobianIdeal_map
    (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCV : C ≤ V) :
    letI := mapSubalgebra_isDVR ek eK he V
    letI := mapSubalgebra_isFractionRing ek eK he V
    letI := mapSubalgebra_essFiniteType ek eK he V
    (intrinsicDVRSourceJacobianIdeal C V hCV).map (subalgebraEquiv ek eK he V).toRingHom =
      intrinsicDVRSourceJacobianIdeal (mapSubalgebra ek eK he C)
        (mapSubalgebra ek eK he V) ((mapSubalgebra_le_iff ek eK he C V).mpr hCV) := by
  let := mapSubalgebra_isDVR ek eK he V
  let := mapSubalgebra_isFractionRing ek eK he V
  let := mapSubalgebra_essFiniteType ek eK he V
  obtain ⟨m, π, a, hπ, ha⟩ := exists_finite_dvr_coordinates (k := k) V
  let a₀ : ULift.{u} (Fin m) → V := fun i => a i.down
  have ha₀ : IsTranscendenceBasis k (residue V ∘ a₀) := ha.comp_equiv Equiv.ulift
  have ha' : IsTranscendenceBasis k'
      (residue (mapSubalgebra ek eK he V) ∘
        fun i : ULift.{v} (Fin m) => subalgebraEquiv ek eK he V (a i.down)) := by
    have h := (residue_transcendenceBasis ek eK he V a ha).comp_equiv
      (Equiv.ulift : ULift.{v} (Fin m) ≃ Fin m)
    simpa only [Function.comp_def, Equiv.ulift, Equiv.coe_fn_mk] using h
  exact MixedUniverseDVRJacobian.intrinsicDVRSourceJacobianIdeal_equiv_of_coordinates
    ek eK he C V (mapSubalgebra ek eK he C) (mapSubalgebra ek eK he V)
    hCV ((mapSubalgebra_le_iff ek eK he C V).mpr hCV)
    (subalgebraEquiv ek eK he C) (subalgebraEquiv ek eK he V)
    (fun _ => rfl) (fun _ => rfl) hπ ha₀ ha'
    (Fintype.equivFin (Option (ULift.{u} (Fin m)))).symm

omit [CharZero k] [CharZero k'] in
/-- The actual entire restricted coefficient isomorphism preserves every nonzero ideal. -/
theorem mappedIdeal_ne_bot (C : Subalgebra k K) (I : Ideal C) (hI : I ≠ ⊥) :
    I.map (subalgebraEquiv ek eK he C).toRingHom ≠ ⊥ :=
  (Ideal.map_eq_bot_iff_of_injective (subalgebraEquiv ek eK he C).injective).mp.mt hI

/-- The WHOLE intrinsic cutoff condition agrees at every actually corresponding DVR. -/
theorem mem_intrinsicDVRMultiplierContribution_iff
    (C V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCV : C ≤ V) (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (f : C) :
    letI := mapSubalgebra_isDVR ek eK he V
    letI := mapSubalgebra_isFractionRing ek eK he V
    letI := mapSubalgebra_essFiniteType ek eK he V
    f ∈ intrinsicDVRMultiplierContribution C V hCV I hI q ↔
      subalgebraEquiv ek eK he C f ∈ intrinsicDVRMultiplierContribution
        (mapSubalgebra ek eK he C) (mapSubalgebra ek eK he V)
        ((mapSubalgebra_le_iff ek eK he C V).mpr hCV)
        (I.map (subalgebraEquiv ek eK he C).toRingHom)
        (mappedIdeal_ne_bot ek eK he C I hI) q := by
  let := mapSubalgebra_isDVR ek eK he V
  let := mapSubalgebra_isFractionRing ek eK he V
  let := mapSubalgebra_essFiniteType ek eK he V
  let hCV' := (mapSubalgebra_le_iff ek eK he C V).mpr hCV
  let eC := subalgebraEquiv ek eK he C
  let eV := subalgebraEquiv ek eK he V
  have hIeq : (I.map eC.toRingHom).map (Subalgebra.inclusion hCV').toRingHom =
      (I.map (Subalgebra.inclusion hCV).toRingHom).map eV.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  have hIo : dvrIdealOrder ((I.map eC.toRingHom).map (Subalgebra.inclusion hCV').toRingHom) =
      dvrIdealOrder (I.map (Subalgebra.inclusion hCV).toRingHom) := by
    rw [hIeq, dvrIdealOrder_map_ringEquiv]
  have hJo : dvrIdealOrder (intrinsicDVRSourceJacobianIdeal
      (mapSubalgebra ek eK he C) (mapSubalgebra ek eK he V) hCV') =
      dvrIdealOrder (intrinsicDVRSourceJacobianIdeal C V hCV) := by
    rw [← intrinsicDVRSourceJacobianIdeal_map ek eK he C V hCV,
      dvrIdealOrder_map_ringEquiv]
  have hval : addVal (mapSubalgebra ek eK he V) (Subalgebra.inclusion hCV' (eC f)) =
      addVal V (Subalgebra.inclusion hCV f) := by
    rw [← subalgebraEquiv_inclusion ek eK he C V hCV f]
    exact addVal_ringEquiv eV _
  have hz : eC f = 0 ↔ f = 0 := by
    constructor
    · intro h
      exact eC.injective (h.trans (map_zero eC).symm)
    · intro h
      simp [h]
  rw [EnvelopeProperty.Char0.mem_intrinsicDVRMultiplierContribution_iff,
    EnvelopeProperty.Char0.mem_intrinsicDVRMultiplierContribution_iff, hIo, hJo, hval, hz]

private theorem mem_valuative_iff
    (C : Subalgebra k K) [IsFractionRing C K]
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) (f : C) :
    letI := mapSubalgebra_isFractionRing ek eK he C
    f ∈ valuativeMultiplierIdeal C I hI q ↔
      subalgebraEquiv ek eK he C f ∈ valuativeMultiplierIdeal
        (mapSubalgebra ek eK he C) (I.map (subalgebraEquiv ek eK he C).toRingHom)
        (mappedIdeal_ne_bot ek eK he C I hI) q := by
  let := mapSubalgebra_isFractionRing ek eK he C
  let E := divisorialEquiv ek eK he C
  simp only [valuativeMultiplierIdeal, Submodule.mem_iInf]
  constructor
  · intro h D'
    let D := E.symm D'
    let : IsDiscreteValuationRing D.val := D.property.2.1
    let : IsFractionRing D.val K := D.property.2.2.1
    let : Algebra.EssFiniteType k D.val := D.property.2.2.2
    have hmap := (mem_intrinsicDVRMultiplierContribution_iff ek eK he C D.val
      D.property.1 I hI q f).mp (h D)
    let : IsDiscreteValuationRing (E D).val := (E D).property.2.1
    let : IsFractionRing (E D).val K' := (E D).property.2.2.1
    let : Algebra.EssFiniteType k' (E D).val := (E D).property.2.2.2
    change subalgebraEquiv ek eK he C f ∈ intrinsicDVRMultiplierContribution
      (mapSubalgebra ek eK he C) (E D).val (E D).property.1
      (I.map (subalgebraEquiv ek eK he C).toRingHom)
      (mappedIdeal_ne_bot ek eK he C I hI) q at hmap
    simpa only [D, E.apply_symm_apply] using hmap
  · intro h D
    let : IsDiscreteValuationRing D.val := D.property.2.1
    let : IsFractionRing D.val K := D.property.2.2.1
    let : Algebra.EssFiniteType k D.val := D.property.2.2.2
    exact (mem_intrinsicDVRMultiplierContribution_iff ek eK he C D.val
      D.property.1 I hI q f).mpr (h (E D))

/-- The ENTIRE full all-divisorial-DVR multiplier ideal retains actual coefficient
and function-field equivalences across independent universes. -/
theorem valuativeMultiplierIdeal_map
    (C : Subalgebra k K) [IsFractionRing C K] (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    letI := mapSubalgebra_isFractionRing ek eK he C
    (valuativeMultiplierIdeal C I hI q).map (subalgebraEquiv ek eK he C).toRingHom =
      valuativeMultiplierIdeal (mapSubalgebra ek eK he C)
        (I.map (subalgebraEquiv ek eK he C).toRingHom)
        (mappedIdeal_ne_bot ek eK he C I hI) q := by
  let := mapSubalgebra_isFractionRing ek eK he C
  apply Ideal.ext
  intro y
  let eC := subalgebraEquiv ek eK he C
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv eC y).mp hy
    exact (mem_valuative_iff ek eK he C I hI q x).mp hx
  · intro hy
    have hx := (mem_valuative_iff ek eK he C I hI q (eC.symm y)).mpr
      (by simpa only [eC, RingEquiv.apply_symm_apply] using hy)
    have hmap := Ideal.mem_map_of_mem eC.toRingHom hx
    change eC (eC.symm y) ∈ _ at hmap
    rw [eC.apply_symm_apply] at hmap
    exact hmap

end EnvelopeProperty.Char0.ValuativeUniverseTransport
