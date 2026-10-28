/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.DerivationSourceLocalization
import EnvelopeProperty.Char0.ValuativeMultiplierIdeal

/-!
# Actual source localization preserves intrinsic canonical DVR contributions

The actual original-source canonical ideals and multiplier contributions
are retained under genuine literal source-localization maps.
-/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]

/-- Actual source localization leaves the intrinsic actual DVR canonical
Jacobian ideal unchanged, with every original-source function retained. -/
theorem intrinsicDVRSourceJacobianIdeal_source_localization
    (C E V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCE : C ≤ E) (hEV : E ≤ V) (M : Submonoid C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization M E) :
    intrinsicDVRSourceJacobianIdeal C V (hCE.trans hEV) = intrinsicDVRSourceJacobianIdeal E V hEV := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let _ : Algebra E V := (Subalgebra.inclusion hEV).toAlgebra
  have : IsScalarTower k C E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k E V := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsLocalization M E := hlocal
  obtain ⟨m, π, w, hπ, hw⟩ := exists_finite_dvr_coordinates (k := k) V
  let w' : ULift.{u} (Fin m) → V := fun j => w j.down
  have hw' : IsTranscendenceBasis k (residue V ∘ w') := hw.comp_equiv Equiv.ulift
  let e := (Fintype.equivFin (Option (ULift.{u} (Fin m)))).symm
  rw [intrinsicDVRSourceJacobianIdeal_eq C V (hCE.trans hEV) hπ hw' e,
    intrinsicDVRSourceJacobianIdeal_eq E V hEV hπ hw' e]
  have h := derivationSourceJacobianIdeal_source_localization M (dvrLeafPartials E V hEV hπ hw' e)
  rw [dvrSourceJacobianIdeal_through_leaf C V (hCE.trans hEV) E hCE hEV hπ hw' e] at h
  exact h

/-- The actual full intrinsic DVR contribution after genuine source localization
pulls back to precisely its original-source contribution. -/
theorem intrinsicDVRMultiplierContribution_source_localization
    (C E V : Subalgebra k K) [IsDiscreteValuationRing V] [IsFractionRing V K]
    [Algebra.EssFiniteType k V] (hCE : C ≤ E) (hEV : E ≤ V) (M : Submonoid C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization M E)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    intrinsicDVRMultiplierContribution C V (hCE.trans hEV) I hI q =
      (intrinsicDVRMultiplierContribution E V hEV (I.map (Subalgebra.inclusion hCE).toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCE)).mp.mt hI) q).comap
          (Subalgebra.inclusion hCE).toRingHom := by
  have hcomp : (Subalgebra.inclusion hEV).toRingHom.comp (Subalgebra.inclusion hCE).toRingHom =
      (Subalgebra.inclusion (hCE.trans hEV)).toRingHom := rfl
  simp only [intrinsicDVRMultiplierContribution, Ideal.map_map, hcomp, Ideal.comap_comap,
    intrinsicDVRSourceJacobianIdeal_source_localization C E V hCE hEV M hlocal]

/-- Actual localization of the original full multiplier ideal is contained in
the full multiplier ideal of the actually localized source and original ideal. -/
theorem map_valuativeMultiplierIdeal_le_source_localization
    (C E : Subalgebra k K) [IsFractionRing C K] (hCE : C ≤ E) (M : Submonoid C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization M E)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    letI : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
    (valuativeMultiplierIdeal C I hI q).map (Subalgebra.inclusion hCE).toRingHom ≤
      valuativeMultiplierIdeal E (I.map (Subalgebra.inclusion hCE).toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hCE)).mp.mt hI) q := by
  have : IsFractionRing E K := isFractionRing_intermediate_subalgebra C E hCE
  apply le_iInf
  intro V
  let := V.property.2.1
  let := V.property.2.2.1
  let := V.property.2.2.2
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  have hmem := valuativeMultiplierIdeal_le_contribution C V.val (hCE.trans V.property.1) I hI q hf
  rw [intrinsicDVRMultiplierContribution_source_localization C E V.val hCE V.property.1 M hlocal I hI q] at hmem
  exact hmem

end EnvelopeProperty.Char0
