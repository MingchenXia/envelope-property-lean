/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumFibreBaseChange

/-!
# All finite-fibre function norms on actual scalar extensions

Whole completed-field and tensor functoriality compare actual kernels under
an algebra isomorphism, so genuine local dimensions preserve every finite
fibre weight. Actual scalar tensor cancellation then transports arbitrary
function products and additive sums to the literal scalar-extended algebra,
including all EReal functions with the actual extended-real conventions.

Only module finiteness is required. All statements evaluate at a provided
base-changed point; no unrestricted point-extension existence, flatness,
projectivity or scalar-extension fibre bijection is assumed.
-/

open scoped TensorProduct
open Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]

private local instance equiv_ker_isPrime {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {x : Spectrum R} {y : Spectrum S} (h : comap (algebraMap R S) y = x) :
    (RingHom.ker (fibreHom h)).IsPrime := RingHom.ker_isPrime _

theorem comap_algEquiv_base (e : B ≃ₐ[A] D) (y : Spectrum D) :
    comap (algebraMap A B) (comap e.toRingHom y) = comap (algebraMap A D) y := by
  apply ext_val
  intro a
  change y.val (e (algebraMap A B a)) = y.val (algebraMap A D a)
  rw [e.commutes]

theorem completedMap_algEquiv_comm (e : B ≃ₐ[A] D) (y : Spectrum D) :
    (H.map e.toRingHom (rfl : comap e.toRingHom y = _)).comp
      (H.map (algebraMap A B) (comap_algEquiv_base e y)) =
        H.map (algebraMap A D) (rfl : comap (algebraMap A D) y = _) := by
  have hr : e.toRingHom.comp (algebraMap A B) = algebraMap A D := by
    ext a
    exact e.commutes a
  rw [H.map_comp]
  congr 1

theorem fibreHom_algEquiv (e : B ≃ₐ[A] D) (y : Spectrum D)
    (q : H (comap (algebraMap A D) y) ⊗[A] B) :
    fibreHom (rfl : comap (algebraMap A D) y = _)
      (Algebra.TensorProduct.congr (.refl : H (comap (algebraMap A D) y) ≃ₐ[H (comap (algebraMap A D) y)] H (comap (algebraMap A D) y)) e q) =
    H.map e.toRingHom (rfl : comap e.toRingHom y = _)
      (fibreHom (comap_algEquiv_base e y) q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add q q' hq hq' => simp only [map_add, hq, hq']
  | tmul c b =>
    change fibreHom (rfl : comap (algebraMap A D) y = _) (c ⊗ₜ[A] e b) =
      H.map e.toRingHom (rfl : comap e.toRingHom y = _)
        (fibreHom (comap_algEquiv_base e y) (c ⊗ₜ[A] b))
    rw [fibreHom_tmul, fibreHom_tmul, map_mul]
    have hs := congrArg (fun f => f c) (completedMap_algEquiv_comm e y)
    rw [show H.map (algebraMap A D) (rfl : comap (algebraMap A D) y = _) c = _ from hs.symm]
    rw [H.map_toH]
    rfl

theorem localFinrank_congr {K E : Type*} [Field K] [CommRing E] [Algebra K E]
    {p q : Ideal E} [p.IsPrime] [q.IsPrime] (h : p = q) :
    Module.finrank K (Localization.AtPrime p) = Module.finrank K (Localization.AtPrime q) := by
  subst h
  rfl

theorem fibreNormMult_comap_algEquiv [Module.Finite A B] (e : B ≃ₐ[A] D) (y : Spectrum D) :
    fibreNormMult A (comap e.toRingHom y) = fibreNormMult A y := by
  let : Module.Finite A D := Module.Finite.equiv e.toLinearEquiv
  let x := comap (algebraMap A D) y
  have hz : comap (algebraMap A B) (comap e.toRingHom y) = x := comap_algEquiv_base e y
  let eT : (H x ⊗[A] B) ≃ₐ[H x] (H x ⊗[A] D) :=
    Algebra.TensorProduct.congr (.refl : H x ≃ₐ[H x] H x) e
  let m : MaximalSpectrum (H x ⊗[A] D) :=
    ⟨RingHom.ker (fibreHom (rfl : comap (algebraMap A D) y = x)), isMaximal_ker_fibreHom _⟩
  have hker : (maximalSpectrumAlgEquiv eT m).asIdeal = RingHom.ker (fibreHom hz) := by
    ext q
    change fibreHom (rfl : comap (algebraMap A D) y = x) (eT q) = 0 ↔ fibreHom hz q = 0
    rw [fibreHom_algEquiv]
    have hi := H.map_injective e.toRingHom (rfl : comap e.toRingHom y = _)
    constructor
    · intro hq
      apply hi
      simpa only [map_zero] using hq
    · intro hq
      rw [hq, map_zero]
  rw [fibreNormMult_eq_localFinrank_of_comap hz,
    fibreNormMult_eq_localFinrank_of_comap (rfl : comap (algebraMap A D) y = x)]
  exact (localFinrank_congr (K := H x) hker.symm).trans
    (finrank_maximalLocalizationAlgEquiv eT m).symm

def pointFibreAlgEquiv (e : B ≃ₐ[A] D) (x : Spectrum A) :
    comap (algebraMap A D) ⁻¹' {x} ≃ comap (algebraMap A B) ⁻¹' {x} :=
  ((ringEquivHomeomorph e.toRingEquiv).subtype (fun y => by
    change comap (algebraMap A D) y = x ↔ comap (algebraMap A B) (comap e.toRingHom y) = x
    rw [comap_algEquiv_base])).toEquiv

theorem pointFibreAlgEquiv_apply_val (e : B ≃ₐ[A] D) (x : Spectrum A)
    (y : comap (algebraMap A D) ⁻¹' {x}) :
    (pointFibreAlgEquiv e x y).1 = comap e.toRingHom y.1 := rfl

theorem fibreWeightedSum_algEquiv [Module.Finite A B] (e : B ≃ₐ[A] D)
    {M : Type*} [AddCommMonoid M] (f : Spectrum B → M) (x : Spectrum A) :
    (letI := Module.Finite.equiv e.toLinearEquiv;
      ∑ y ∈ (finite_preimage_singleton (A := D) x).toFinset,
        fibreNormMult A y • f (comap e.toRingHom y)) =
      ∑ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
        fibreNormMult A y • f y := by
  let : Module.Finite A D := Module.Finite.equiv e.toLinearEquiv
  let eF := pointFibreAlgEquiv e x
  classical
  refine Finset.sum_bij (fun y hy => (eF ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩).1) ?_ ?_ ?_ ?_
  · intro y hy
    exact (Set.Finite.mem_toFinset _).2 (eF ⟨y, (Set.Finite.mem_toFinset _).1 hy⟩).2
  · intro y₁ h₁ y₂ h₂ he
    exact congrArg Subtype.val (eF.injective (Subtype.ext he))
  · intro z hz
    obtain ⟨⟨y, hy⟩, he⟩ := eF.surjective ⟨z, (Set.Finite.mem_toFinset _).1 hz⟩
    exact ⟨y, (Set.Finite.mem_toFinset _).2 hy, congrArg Subtype.val he⟩
  · intro y hy
    dsimp only [eF]
    rw [pointFibreAlgEquiv_apply_val, fibreNormMult_comap_algEquiv]

theorem fibreWeightedProduct_algEquiv [Module.Finite A B] (e : B ≃ₐ[A] D)
    {M : Type*} [CommMonoid M] (f : Spectrum B → M) (x : Spectrum A) :
    (letI := Module.Finite.equiv e.toLinearEquiv;
      ∏ y ∈ (finite_preimage_singleton (A := D) x).toFinset,
        f (comap e.toRingHom y) ^ fibreNormMult A y) =
      ∏ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
        f y ^ fibreNormMult A y := by
  simpa using congrArg Additive.toMul (fibreWeightedSum_algEquiv e
    (fun y => Additive.ofMul (f y)) x)

section ScalarExtension
variable {R S : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
private local instance scalarFibre_rightAlgebra : Algebra A (S ⊗[R] A) :=
  Algebra.TensorProduct.rightAlgebra
private local instance scalarFibre_algebra : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
  ScalarExtension.algebra R S A B
private local instance scalarFibre_finite [Module.Finite A B] :
    Module.Finite (S ⊗[R] A) (S ⊗[R] B) := ScalarExtension.moduleFinite R S A B

theorem fibreWeightedSum_scalarExtension [Module.Finite A B]
    {M : Type*} [AddCommMonoid M] (f : Spectrum B → M) (x' : Spectrum (S ⊗[R] A)) :
    (∑ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x').toFinset,
      fibreNormMult (S ⊗[R] A) y' •
        f (comap (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom y')) =
    ∑ y ∈ (finite_preimage_singleton (A := B)
      (comap (algebraMap A (S ⊗[R] A)) x')).toFinset, fibreNormMult A y • f y := by
  let e := ScalarExtension.equiv R S A B
  have hpoint (y : Spectrum (S ⊗[R] B)) :
      comap (Algebra.TensorProduct.includeRight : B →ₐ[A] (S ⊗[R] A) ⊗[A] B).toRingHom
        (comap e.toRingHom y) =
      comap (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom y := by
    apply ext_val
    intro b
    change y.val (e ((1 : S ⊗[R] A) ⊗ₜ[A] b)) = y.val ((1 : S) ⊗ₜ[R] b)
    rw [ScalarExtension.equiv_one_tmul]
  have he := fibreWeightedSum_algEquiv e
    (fun y => f (comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] (S ⊗[R] A) ⊗[A] B).toRingHom y)) x'
  simp only [hpoint] at he
  exact he.trans (fibreWeightedSum_baseChange (A := A) (B := B) x' f)

theorem fibreWeightedERealSum_scalarExtension [Module.Finite A B]
    (f : Spectrum B → EReal) (x' : Spectrum (S ⊗[R] A)) :
    (∑ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x').toFinset,
      (fibreNormMult (S ⊗[R] A) y' : EReal) *
        f (comap (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom y')) =
    ∑ y ∈ (finite_preimage_singleton (A := B)
      (comap (algebraMap A (S ⊗[R] A)) x')).toFinset, (fibreNormMult A y : EReal) * f y := by
  simpa only [EReal.nsmul_eq_mul] using fibreWeightedSum_scalarExtension f x'

theorem fibreWeightedProduct_scalarExtension [Module.Finite A B]
    {M : Type*} [CommMonoid M] (f : Spectrum B → M) (x' : Spectrum (S ⊗[R] A)) :
    (∏ y' ∈ (finite_preimage_singleton (A := S ⊗[R] B) x').toFinset,
      f (comap (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom y') ^
        fibreNormMult (S ⊗[R] A) y') =
    ∏ y ∈ (finite_preimage_singleton (A := B)
      (comap (algebraMap A (S ⊗[R] A)) x')).toFinset, f y ^ fibreNormMult A y := by
  simpa using congrArg Additive.toMul
    (fibreWeightedSum_scalarExtension (fun y => Additive.ofMul (f y)) x')

end ScalarExtension

end EnvelopeProperty.Berkovich.Spectrum
