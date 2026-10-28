/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.FiniteAlgebraMultiplicity
import EnvelopeProperty.Berkovich.SpectrumFiniteNorm
import Mathlib.Data.EReal.Operations

/-!
# Genuine finite analytic-fibre multiplicity conservation under base change

Actual completed tensor cancellation and whole completion-map functoriality
identify restricted maximal kernels. Full local dimensions, hence genuine
local length times residue-degree weights, are conserved over restriction
fibres. This proves base change for arbitrary function products and sums,
including all EReal functions with Mathlib's extended-real conventions.

Only Module.Finite is required for the original algebra; no freeness,
projectivity, flatness or regularizability is assumed. A base-changed point
is provided. Existence above every original base point is a separate claim.
-/

open scoped NNReal TensorProduct
open Classical
noncomputable section

namespace EnvelopeProperty.Berkovich.Spectrum
private local instance fibreBaseChange_ker_isPrime {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {x : Spectrum R} {y : Spectrum S} (h : comap (algebraMap R S) y = x) :
    (RingHom.ker (fibreHom h)).IsPrime := RingHom.ker_isPrime _
section BaseChange
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable (x' : Spectrum C)

private local instance fibreBaseChange_baseScalarAlgebra : Algebra A (H x') :=
  ((toH x').comp (algebraMap A C)).toAlgebra
private local instance fibreBaseChange_completedScalarAlgebra :
    Algebra (H (comap (algebraMap A C) x')) (H x') :=
  (H.map (algebraMap A C) (rfl : comap (algebraMap A C) x' = _)).toAlgebra
private local instance fibreBaseChange_baseScalarTower : IsScalarTower A C (H x') :=
  IsScalarTower.of_algebraMap_eq' rfl
private local instance fibreBaseChange_completedScalarTower :
    IsScalarTower A (H (comap (algebraMap A C) x')) (H x') :=
  IsScalarTower.of_algebraMap_eq fun a =>
    (H.map_toH (algebraMap A C) (rfl : comap (algebraMap A C) x' = _) a).symm

def fibreBaseChangeEquiv :
    (H x' ⊗[C] (C ⊗[A] B)) ≃ₐ[H x']
      H x' ⊗[H (comap (algebraMap A C) x')] (H (comap (algebraMap A C) x') ⊗[A] B) :=
  (Algebra.TensorProduct.cancelBaseChange A C (H x') (H x') B).trans
    (Algebra.TensorProduct.cancelBaseChange A (H (comap (algebraMap A C) x'))
      (H x') (H x') B).symm

theorem fibreBaseChangeEquiv_one_tmul (b : B) :
    fibreBaseChangeEquiv (A := A) (B := B) x' ((1 : H x') ⊗ₜ[C] ((1 : C) ⊗ₜ[A] b)) =
      (1 : H x') ⊗ₜ[H (comap (algebraMap A C) x')]
        ((1 : H (comap (algebraMap A C) x')) ⊗ₜ[A] b) := by
  simp [fibreBaseChangeEquiv]

abbrev baseChangeFibreRestrict {y' : Spectrum (C ⊗[A] B)}
    (h : comap (algebraMap C (C ⊗[A] B)) y' = x') :
    Fibre (B := B) (comap (algebraMap A C) x') :=
  ⟨comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y', by
    apply ext_val
    intro a
    change y'.val ((1 : C) ⊗ₜ[A] algebraMap A B a) = x'.val (algebraMap A C a)
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
    exact congrArg (fun z : Spectrum C => z.val (algebraMap A C a)) h⟩

theorem fibreBaseChangeEquiv_symm_tmul (c : H (comap (algebraMap A C) x')) (b : B) :
    (fibreBaseChangeEquiv (A := A) (B := B) x').symm
      ((1 : H x') ⊗ₜ[H (comap (algebraMap A C) x')] (c ⊗ₜ[A] b)) =
    H.map (algebraMap A C) (rfl : comap (algebraMap A C) x' = _) c ⊗ₜ[C]
      ((1 : C) ⊗ₜ[A] b) := by
  simp [fibreBaseChangeEquiv, Algebra.smul_def]
  rfl

theorem completedMap_baseChange_comm {y' : Spectrum (C ⊗[A] B)}
    (h : comap (algebraMap C (C ⊗[A] B)) y' = x') :
    (H.map (algebraMap C (C ⊗[A] B)) h).comp
      (H.map (algebraMap A C) (rfl : comap (algebraMap A C) x' = _)) =
    (H.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom
      (rfl : comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y' = _)).comp
        (H.map (algebraMap A B) (baseChangeFibreRestrict x' h).2) := by
  have hr : (algebraMap C (C ⊗[A] B)).comp (algebraMap A C) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom.comp
        (algebraMap A B) := by
    ext a
    change algebraMap A C a ⊗ₜ[A] (1 : B) = (1 : C) ⊗ₜ[A] algebraMap A B a
    exact Algebra.TensorProduct.algebraMap_apply a |>.symm.trans
      (Algebra.TensorProduct.algebraMap_apply' a)
  rw [H.map_comp, H.map_comp]
  congr 1

theorem fibreHom_baseChange_old {y' : Spectrum (C ⊗[A] B)}
    (h : comap (algebraMap C (C ⊗[A] B)) y' = x')
    (q : H (comap (algebraMap A C) x') ⊗[A] B) :
    fibreHom h ((fibreBaseChangeEquiv (A := A) (B := B) x').symm
      ((1 : H x') ⊗ₜ[H (comap (algebraMap A C) x')] q)) =
      H.map (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom
        (rfl : comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y' = _)
        (fibreHom (baseChangeFibreRestrict x' h).2 q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add q q' hq hq' => simp only [TensorProduct.tmul_add, map_add, hq, hq']
  | tmul c b =>
    rw [fibreBaseChangeEquiv_symm_tmul, fibreHom_tmul, fibreHom_tmul, map_mul]
    have hs := congrArg (fun f => f c) (completedMap_baseChange_comm x' h)
    rw [show H.map (algebraMap C (C ⊗[A] B)) h
      (H.map (algebraMap A C) (rfl : comap (algebraMap A C) x' = _) c) = _ from hs]
    rw [H.map_toH]
    rfl

def baseChangeFibreMaximal [Module.Finite A B] {y' : Spectrum (C ⊗[A] B)}
    (h : comap (algebraMap C (C ⊗[A] B)) y' = x') :
    MaximalSpectrum (H x' ⊗[H (comap (algebraMap A C) x')]
      (H (comap (algebraMap A C) x') ⊗[A] B)) :=
  maximalSpectrumAlgEquiv (fibreBaseChangeEquiv (A := A) (B := B) x').symm
    ⟨RingHom.ker (fibreHom h), isMaximal_ker_fibreHom h⟩

theorem baseChangeFibreMaximal_comap [Module.Finite A B] {y' : Spectrum (C ⊗[A] B)}
    (h : comap (algebraMap C (C ⊗[A] B)) y' = x') :
    finiteAlgebraMaximalComap (baseChangeFibreMaximal (A := A) (B := B) x' h) =
      fibreToMaximalSpectrum (comap (algebraMap A C) x') (baseChangeFibreRestrict x' h) := by
  apply MaximalSpectrum.ext
  ext q
  change fibreHom h ((fibreBaseChangeEquiv (A := A) (B := B) x').symm
    ((1 : H x') ⊗ₜ[H (comap (algebraMap A C) x')] q)) = 0 ↔
      fibreHom (baseChangeFibreRestrict x' h).2 q = 0
  rw [fibreHom_baseChange_old]
  have hi := H.map_injective (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom
    (rfl : comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y' = _)
  constructor
  · intro hq
    apply hi
    simpa only [map_zero] using hq
  · intro hq
    rw [hq, map_zero]

theorem fibreNormMult_eq_localFinrank_of_comap [Module.Finite A B]
    {x : Spectrum A} {y : Spectrum B} (h : comap (algebraMap A B) y = x) :
    fibreNormMult A y = Module.finrank (H x)
      (Localization.AtPrime (RingHom.ker (fibreHom h))) := by
  subst h
  exact fibreNormMult_eq_localFinrank (B := A) y

theorem fibreNormMult_baseChange_eq_dim [Module.Finite A B] {y' : Spectrum (C ⊗[A] B)}
    (h : comap (algebraMap C (C ⊗[A] B)) y' = x') :
    fibreNormMult C y' = Module.finrank (H x')
      (Localization.AtPrime (baseChangeFibreMaximal (A := A) (B := B) x' h).asIdeal) := by
  rw [fibreNormMult_eq_localFinrank_of_comap h]
  exact finrank_maximalLocalizationAlgEquiv (fibreBaseChangeEquiv (A := A) (B := B) x').symm
    ⟨RingHom.ker (fibreHom h), isMaximal_ker_fibreHom h⟩

theorem fibreWeightedProduct_baseChange [Module.Finite A B] {M : Type*} [CommMonoid M]
    (f : Spectrum B → M) :
    (∏ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      f (comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y') ^
        fibreNormMult C y') =
    ∏ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A C) x')).toFinset,
      f y ^ fibreNormMult A y := by
  classical
  let x := comap (algebraMap A C) x'
  let E := H x ⊗[A] B
  let F := H x' ⊗[H x] E
  let : IsArtinianRing E := IsArtinianRing.of_finite (H x) E
  let : IsArtinianRing F := IsArtinianRing.of_finite (H x') F
  let : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let : Fintype (MaximalSpectrum F) := Fintype.ofFinite _
  let eOld := pointFibreEquivMaximalSpectrum (A := B) x
  let eNew := pointFibreEquivMaximalSpectrum (A := C ⊗[A] B) x'
  let eF := maximalSpectrumAlgEquiv (fibreBaseChangeEquiv (A := A) (B := B) x').symm
  let yOf : MaximalSpectrum E → Spectrum B := fun m => (eOld.symm m).1
  have hfE : (finiteAlgebraMaximalSpectrumFinite (H x) E).toFinset = Finset.univ := by
    ext m
    simp
  have hfF : (finiteAlgebraMaximalSpectrumFinite (H x') F).toFinset = Finset.univ := by
    ext m
    simp
  have hnew : (∏ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      f (comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y') ^
        fibreNormMult C y') =
      ∏ p : MaximalSpectrum F, f (yOf (finiteAlgebraMaximalComap p)) ^
        Module.finrank (H x') (Localization.AtPrime p.asIdeal) := by
    refine Finset.prod_bij (fun y hy => eF (eNew ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y₁ h₁ y₂ h₂ he
      exact congrArg Subtype.val (eNew.injective (eF.injective he))
    · intro p _
      obtain ⟨m, rfl⟩ := eF.surjective p
      obtain ⟨⟨y, hy⟩, rfl⟩ := eNew.surjective m
      exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, rfl⟩
    · intro y hy
      have hyset : y ∈ comap (algebraMap C (C ⊗[A] B)) ⁻¹' {x'} :=
        (Set.Finite.mem_toFinset _).1 hy
      have hy' : comap (algebraMap C (C ⊗[A] B)) y = x' := Set.mem_singleton_iff.mp hyset
      change f (comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y) ^
        fibreNormMult C y =
        f (yOf (finiteAlgebraMaximalComap (baseChangeFibreMaximal (A := A) (B := B) x' hy'))) ^
          Module.finrank (H x')
            (Localization.AtPrime (baseChangeFibreMaximal (A := A) (B := B) x' hy').asIdeal)
      rw [fibreNormMult_baseChange_eq_dim x' hy']
      have he : finiteAlgebraMaximalComap (baseChangeFibreMaximal (A := A) (B := B) x' hy') =
          eOld ⟨(baseChangeFibreRestrict x' hy').1, (baseChangeFibreRestrict x' hy').2⟩ :=
        baseChangeFibreMaximal_comap x' hy'
      simp only [he, yOf, Equiv.symm_apply_apply]
  rw [hnew, ← hfF]
  rw [finiteAlgebraWeightedProduct_baseChange (H := H x) (K := H x') (E := E)
    (fun m => f (yOf m)), hfE]
  symm
  refine Finset.prod_bij (fun y hy => eOld ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro y₁ h₁ y₂ h₂ he
    exact congrArg Subtype.val (eOld.injective he)
  · intro m _
    obtain ⟨⟨y, hy⟩, rfl⟩ := eOld.surjective m
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, rfl⟩
  · intro y hy
    have hyset : y ∈ comap (algebraMap A B) ⁻¹' {x} := (Set.Finite.mem_toFinset _).1 hy
    have hy' : comap (algebraMap A B) y = x := Set.mem_singleton_iff.mp hyset
    simp only [yOf, Equiv.symm_apply_apply]
    rw [fibreNormMult_eq_localFinrank_of_comap hy']
    rfl

theorem fibreWeightedSum_baseChange [Module.Finite A B] {M : Type*} [AddCommMonoid M]
    (f : Spectrum B → M) :
    (∑ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      fibreNormMult C y' •
        f (comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y')) =
    ∑ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A C) x')).toFinset,
      fibreNormMult A y • f y := by
  simpa using congrArg Multiplicative.toAdd
    (fibreWeightedProduct_baseChange x' (fun y => Multiplicative.ofAdd (f y)))

theorem fibreWeightedERealSum_baseChange [Module.Finite A B]
    (f : Spectrum B → EReal) :
    (∑ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      (fibreNormMult C y' : EReal) *
        f (comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y')) =
    ∑ y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A C) x')).toFinset,
      (fibreNormMult A y : EReal) * f y := by
  simpa only [EReal.nsmul_eq_mul] using fibreWeightedSum_baseChange x' f

theorem sum_fibreNormMult_baseChange [Module.Finite A B] (y : Spectrum B)
    (hy : comap (algebraMap A B) y = comap (algebraMap A C) x') :
    (∑ y' ∈ (finite_preimage_singleton (A := C ⊗[A] B) x').toFinset,
      if comap (Algebra.TensorProduct.includeRight : B →ₐ[A] C ⊗[A] B).toRingHom y' = y then
        fibreNormMult C y' else 0) = fibreNormMult A y := by
  classical
  have h := fibreWeightedSum_baseChange (A := A) (B := B) x' (fun z => if z = y then (1 : ℕ) else 0)
  simp only [nsmul_eq_mul, mul_ite, mul_one, mul_zero] at h
  have hyset : y ∈ (finite_preimage_singleton (A := B) (comap (algebraMap A C) x')).toFinset := by
    apply (Set.Finite.mem_toFinset _).2
    exact Set.mem_singleton_iff.mpr hy
  simpa only [Finset.sum_ite_eq', if_pos hyset, Nat.cast_id] using h

end BaseChange
end EnvelopeProperty.Berkovich.Spectrum
