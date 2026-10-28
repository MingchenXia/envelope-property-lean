import EnvelopeProperty.Char0.ValuativeUniverseTransport
import EnvelopeProperty.Char0.FractionFieldModel

/-! # Full intrinsic multiplier ideals on actual specified source-equivalent models -/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.ValuativeSourceEquivalence

open CoefficientUniverseTransport

universe u v

variable {k K : Type u} {k' K' : Type v}
    [Field k] [Field K] [Algebra k K] [Field k'] [Field K'] [Algebra k' K']
    [CharZero k] [CharZero k']
    (ek : k ≃+* k') (eK : K ≃+* K')
    (he : ∀ a : k, eK (algebraMap k K a) = algebraMap k' K' (ek a))

include ek he in
/-- The WHOLE actual intrinsic multiplier ideals commute with the actual source
ring equivalence; the target source is the specified original one. -/
theorem valuativeMultiplierIdeal_equiv
    (C : Subalgebra k K) [IsFractionRing C K]
    (D : Subalgebra k' K') [IsFractionRing D K'] (eC : C ≃+* D)
    (hCcoe : ∀ a : C, eK (a : K) = (eC a : K'))
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    (valuativeMultiplierIdeal C I hI q).map eC.toRingHom =
      valuativeMultiplierIdeal D (I.map eC.toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective eC.injective).mp.mt hI) q := by
  have hD : mapSubalgebra ek eK he C = D := by
    apply Subalgebra.ext
    intro x
    constructor
    · intro hx
      let a : C := ⟨eK.symm x, hx⟩
      have hval : (eC a : K') = x := (hCcoe a).symm.trans (eK.apply_symm_apply x)
      exact hval ▸ (eC a).property
    · intro hx
      obtain ⟨a, ha⟩ := eC.surjective (⟨x, hx⟩ : D)
      have hval : eK (a : K) = x := (hCcoe a).trans (congrArg Subtype.val ha)
      change eK.symm x ∈ C
      rw [← hval, eK.symm_apply_apply]
      exact a.property
  subst D
  have hEC : eC = subalgebraEquiv ek eK he C := by
    ext a
    exact (hCcoe a).symm
  simpa only [hEC] using ValuativeUniverseTransport.valuativeMultiplierIdeal_map ek eK he C I hI q

/-- Canonical actual fraction-field source models preserve the WHOLE multiplier
ideal under every actual scalar-compatible original ring equivalence. -/
theorem valuativeMultiplierIdeal_fractionModel_equiv
    {R : Type u} {R' : Type v} [CommRing R] [IsDomain R] [Algebra k R]
    [CommRing R'] [IsDomain R'] [Algebra k' R'] (E : R ≃+* R')
    (hcoeff : ∀ a : k, E (algebraMap k R a) = algebraMap k' R' (ek a))
    (I : Ideal (AffineFractionFieldModel.subalgebra k R)) (hI : I ≠ ⊥) (q : ℚ) :
    let eC := ((AffineFractionFieldModel.equiv k R).symm.toRingEquiv.trans E).trans
      (AffineFractionFieldModel.equiv k' R').toRingEquiv
    (valuativeMultiplierIdeal (AffineFractionFieldModel.subalgebra k R) I hI q).map eC.toRingHom =
      valuativeMultiplierIdeal (AffineFractionFieldModel.subalgebra k' R') (I.map eC.toRingHom)
        ((Ideal.map_eq_bot_iff_of_injective eC.injective).mp.mt hI) q := by
  intro eC
  let eF : FractionRing R ≃+* FractionRing R' := IsFractionRing.ringEquivOfRingEquiv E
  have hsquare : ∀ a : k, eF (algebraMap k (FractionRing R) a) =
      algebraMap k' (FractionRing R') (ek a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply k R (FractionRing R),
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, hcoeff,
      ← IsScalarTower.algebraMap_apply k' R' (FractionRing R')]
  apply valuativeMultiplierIdeal_equiv ek eF hsquare _ _ eC _ I hI q
  intro c
  have hc := AffineFractionFieldModel.equiv_apply_coe k R
    ((AffineFractionFieldModel.equiv k R).symm c)
  rw [AlgEquiv.apply_symm_apply] at hc
  change eF (c : FractionRing R) =
    ((AffineFractionFieldModel.equiv k' R')
      (E ((AffineFractionFieldModel.equiv k R).symm c)) : FractionRing R')
  rw [AffineFractionFieldModel.equiv_apply_coe, hc]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap E _

end EnvelopeProperty.Char0.ValuativeSourceEquivalence
