import EnvelopeProperty.Char0.ValuativeMultiplierIdeal

/-! # Actual original DVR Jacobians under mixed-universe coefficient equivalences -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.MixedUniverseDVRJacobian

open AlgebraicGeometry IsDiscreteValuationRing IsLocalRing Module Ideal

universe u v w w'

variable {k K : Type u} {k' K' : Type v}
    [Field k] [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k' K']
    (ek : k ≃+* k') (eK : K ≃+* K')
    (he : ∀ a : k, eK (algebraMap k K a) = algebraMap k' K' (ek a))

/-- The actual conjugate derivation; coefficient linearity is derived from the genuine field square. -/
def conjugateDerivation (D : Derivation k K K) : Derivation k' K' K' where
  toFun x := eK (D (eK.symm x))
  map_add' x y := by simp
  map_smul' a x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    obtain ⟨a, rfl⟩ := ek.surjective a
    rw [← he a, map_mul, eK.symm_apply_apply, ← Algebra.smul_def,
      Derivation.map_smul, Algebra.smul_def, map_mul, he a]
  map_one_eq_zero' := by
    change eK (D (eK.symm 1)) = 0
    simp [Derivation.map_one_eq_zero]
  leibniz' x y := by
    change eK (D (eK.symm (x*y))) =
      x * eK (D (eK.symm y)) + y * eK (D (eK.symm x))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, eK.apply_symm_apply]

@[simp] theorem conjugateDerivation_apply (D : Derivation k K K) (x : K) :
    conjugateDerivation ek eK he D (eK x) = eK (D x) := by
  simp [conjugateDerivation]

include ek he in
/-- The actual partial derivatives agree through actual coefficient/basis equivalences. -/
theorem partialDeriv_equiv [CharZero k] [CharZero k']
    {ι : Type w} {ι' : Type w'} (ei : ι ≃ ι')
    {z : ι → K} {z' : ι' → K'}
    (hz : IsTranscendenceBasis k z) (hz' : IsTranscendenceBasis k' z')
    (hcoord : ∀ i, eK (z i) = z' (ei i)) (j : ι) (x : K) :
    eK (partialDeriv hz j x) = partialDeriv hz' (ei j) (eK x) := by
  classical
  have hD : conjugateDerivation ek eK he (partialDeriv hz j) = partialDeriv hz' (ei j) := by
    apply sub_eq_zero.mp
    apply derivation_eq_zero_of_forall hz'
    intro i'
    obtain ⟨i, rfl⟩ := ei.surjective i'
    change conjugateDerivation ek eK he (partialDeriv hz j) (z' (ei i)) -
      partialDeriv hz' (ei j) (z' (ei i)) = 0
    rw [← hcoord i, conjugateDerivation_apply]
    rw [hcoord i, partialDeriv_apply, partialDeriv_apply]
    simp
  have h := congrArg (fun D : Derivation k' K' K' => D (eK x)) hD
  simpa only [conjugateDerivation_apply] using h

section DVR

variable [CharZero k] [CharZero k']
    (C V : Subalgebra k K) (C' V' : Subalgebra k' K')
    [IsDiscreteValuationRing V] [IsFractionRing V K] [Algebra.EssFiniteType k V]
    [IsDiscreteValuationRing V'] [IsFractionRing V' K'] [Algebra.EssFiniteType k' V']
    (hCV : C ≤ V) (hCV' : C' ≤ V')
    (eC : C ≃+* C') (eV : V ≃+* V')
    (hCcoe : ∀ a : C, eK (a : K) = (eC a : K'))
    (hVcoe : ∀ a : V, eK (a : K) = (eV a : K'))

include ek eK he hCcoe hVcoe in
private theorem dvrLeafPartials_equiv
    {ι : Type u} {ι' : Type v} [Fintype ι] [Fintype ι'] (ei : ι ≃ ι')
    {π : V} {π' : V'} {a : ι → V} {a' : ι' → V'}
    (hπ : Irreducible π) (ha : IsTranscendenceBasis k (residue V ∘ a))
    (hπ' : Irreducible π') (ha' : IsTranscendenceBasis k' (residue V' ∘ a'))
    (hπe : eV π = π') (hae : ∀ i, eV (a i) = a' (ei i))
    {n : ℕ} (e : Fin n ≃ Option ι) (j : Fin n) (x : C) :
    eV (dvrLeafPartials C V hCV hπ ha e j x) =
      dvrLeafPartials C' V' hCV' hπ' ha' (e.trans (Equiv.optionCongr ei)) j (eC x) := by
  have hcoords : ∀ i, eK (dvrCoordinates π a i) =
      dvrCoordinates π' a' ((Equiv.optionCongr ei) i) := by
    intro i
    cases i with
    | none =>
      exact (hVcoe π).trans (congrArg (fun y : V' => (y : K')) hπe)
    | some i =>
      exact (hVcoe (a i)).trans (congrArg (fun y : V' => (y : K')) (hae i))
  apply Subtype.ext
  rw [← hVcoe]
  change eK (partialDeriv (isTranscendenceBasis_dvrCoordinates hπ ha) (e j) (x : K)) =
    partialDeriv (isTranscendenceBasis_dvrCoordinates hπ' ha')
      ((Equiv.optionCongr ei) (e j)) (eC x : K')
  rw [← hCcoe x]
  exact partialDeriv_equiv ek eK he (Equiv.optionCongr ei)
    (isTranscendenceBasis_dvrCoordinates hπ ha)
    (isTranscendenceBasis_dvrCoordinates hπ' ha') hcoords (e j) (x : K)

include ek eK he hCcoe hVcoe in
/-- EVERY original source-function determinant is transported; the WHOLE generated ideal is preserved. -/
theorem dvrOriginalSourceJacobianIdeal_equiv
    {ι : Type u} {ι' : Type v} [Fintype ι] [Fintype ι'] (ei : ι ≃ ι')
    {π : V} {π' : V'} {a : ι → V} {a' : ι' → V'}
    (hπ : Irreducible π) (ha : IsTranscendenceBasis k (residue V ∘ a))
    (hπ' : Irreducible π') (ha' : IsTranscendenceBasis k' (residue V' ∘ a'))
    (hπe : eV π = π') (hae : ∀ i, eV (a i) = a' (ei i))
    {n : ℕ} (e : Fin n ≃ Option ι) :
    (dvrOriginalSourceJacobianIdeal C V hCV hπ ha e).map eV.toRingHom =
      dvrOriginalSourceJacobianIdeal C' V' hCV' hπ' ha'
        (e.trans (Equiv.optionCongr ei)) := by
  classical
  have hdet (b : Fin n → C) :
      eV.toRingHom ((Matrix.of fun i j => dvrLeafPartials C V hCV hπ ha e j (b i)).det) =
        (Matrix.of fun i j => dvrLeafPartials C' V' hCV' hπ' ha'
          (e.trans (Equiv.optionCongr ei)) j (eC (b i))).det := by
    rw [eV.toRingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    change eV (dvrLeafPartials C V hCV hπ ha e j (b i)) =
      dvrLeafPartials C' V' hCV' hπ' ha' (e.trans (Equiv.optionCongr ei)) j (eC (b i))
    exact dvrLeafPartials_equiv ek eK he C V C' V' hCV hCV' eC eV hCcoe hVcoe
      ei hπ ha hπ' ha' hπe hae e j (b i)
  change (Ideal.span (Set.range fun b : Fin n → C =>
    (Matrix.of fun i j => dvrLeafPartials C V hCV hπ ha e j (b i)).det)).map eV.toRingHom =
      Ideal.span (Set.range fun b : Fin n → C' =>
        (Matrix.of fun i j => dvrLeafPartials C' V' hCV' hπ' ha'
          (e.trans (Equiv.optionCongr ei)) j (b i)).det)
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨fun i => eC (b i), (hdet b).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨fun i => eC.symm (b i), rfl⟩, ?_⟩
    simpa only [eC.apply_symm_apply] using hdet (fun i => eC.symm (b i))

include ek eK he hCcoe hVcoe in
/-- The actual paired finite DVR coordinates remove BOTH intrinsic coordinate choices. -/
theorem intrinsicDVRSourceJacobianIdeal_equiv_of_coordinates
    {m n : ℕ} {π : V} {a : ULift.{u} (Fin m) → V}
    (hπ : Irreducible π) (ha : IsTranscendenceBasis k (residue V ∘ a))
    (ha' : IsTranscendenceBasis k'
      (residue V' ∘ fun i : ULift.{v} (Fin m) => eV (a ⟨i.down⟩)))
    (e : Fin n ≃ Option (ULift.{u} (Fin m))) :
    (intrinsicDVRSourceJacobianIdeal C V hCV).map eV.toRingHom =
      intrinsicDVRSourceJacobianIdeal C' V' hCV' := by
  let ei : ULift.{u} (Fin m) ≃ ULift.{v} (Fin m) := Equiv.ulift.trans Equiv.ulift.symm
  have hπ' : Irreducible (eV π) := (MulEquiv.irreducible_iff eV.toMulEquiv).2 hπ
  rw [intrinsicDVRSourceJacobianIdeal_eq C V hCV hπ ha e,
    intrinsicDVRSourceJacobianIdeal_eq C' V' hCV' hπ' ha' (e.trans (Equiv.optionCongr ei))]
  exact dvrOriginalSourceJacobianIdeal_equiv ek eK he C V C' V' hCV hCV'
    eC eV hCcoe hVcoe ei hπ ha hπ' ha' rfl (fun _ => rfl) e

end DVR

end EnvelopeProperty.Char0.MixedUniverseDVRJacobian
