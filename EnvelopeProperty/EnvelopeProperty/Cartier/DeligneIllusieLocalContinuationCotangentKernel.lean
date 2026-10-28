import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationFlatCotangent
import EnvelopeProperty.Cartier.RelativeFrobeniusCoefficient
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Actual cotangent quotient kernel and individual relative Frobenius divisors

The cotangent base-change property is derived from the genuine ring pushout.
The kernel calculation uses the actual scalar reduction and tensor right exactness.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCotangentKernel

open FrobeniusLiftDifference TensorProduct
open scoped Pointwise

universe u v w z

section ModuleKernel
variable {p : ℕ} {S : Type u} {B : Type v} [CommRing S] [CommRing B] [Algebra S B]

/-- Genuine ring reduction has exactly its original principal ideal as kernel. -/
theorem reduction_kernel (b : Reduction p S B) (hq : algebraMap S B = b.map) :
    RingHom.ker (algebraMap S B) = Ideal.span {(p : S)} := by
  ext s
  change algebraMap S B s = 0 ↔ s ∈ Ideal.span {(p : S)}
  rw [hq, b.kernel_iff, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm⟩

variable {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N] [Module B N] [IsScalarTower S B N]

/-- Tensor right exactness derives divisibility from genuine scalar reduction.
No projectivity, flatness or supplied kernel equation is required. -/
theorem baseChange_eq_zero_iff (b : Reduction p S B) (hq : algebraMap S B = b.map)
    (ρ : M →ₗ[S] N) (hρ : IsBaseChange B ρ) (m : M) :
    ρ m = 0 ↔ ∃ η : M, (p : S) • η = m := by
  have hsurj : Function.Surjective (Algebra.ofId S B) := by
    change Function.Surjective (algebraMap S B)
    rw [hq]
    exact b.surjective
  let e : (S ⧸ RingHom.ker (algebraMap S B)) ≃ₐ[S] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S B) hsurj
  have h₁ : ρ m = 0 ↔ (1 : B) ⊗ₜ[S] m = 0 := by
    constructor
    · intro hm
      apply hρ.equiv.injective
      simpa only [IsBaseChange.equiv_tmul, one_smul, map_zero] using hm
    · intro hm
      have h := congrArg hρ.equiv hm
      simpa only [IsBaseChange.equiv_tmul, one_smul, map_zero] using h
  have h₂ : (1 : B) ⊗ₜ[S] m = 0 ↔
      (1 : S ⧸ RingHom.ker (algebraMap S B)) ⊗ₜ[S] m = 0 := by
    constructor
    · intro hm
      apply (e.toLinearEquiv.rTensor M).injective
      simpa only [LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_one,
        map_zero] using hm
    · intro hm
      have h := congrArg (e.toLinearEquiv.rTensor M) hm
      simpa only [LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_one,
        map_zero] using h
  rw [h₁, h₂]
  change m ∈ LinearMap.ker
    (TensorProduct.mk S (S ⧸ RingHom.ker (algebraMap S B)) M 1) ↔ _
  rw [LinearMap.ker_tensorProductMk, reduction_kernel b hq,
    Submodule.ideal_span_singleton_smul]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

end ModuleKernel

section Cotangent
variable {p : ℕ} {S : Type u} {B : Type v} [CommRing S] [CommRing B]
  (C : Type w) (K : Type v) [CommRing C] [CommRing K]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra K B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]
  [Algebra.IsPushout C K S B]

/-- The original cotangent map is genuine scalar extension, DERIVED from the
actual ring pushout rather than supplied as a differential comparison. -/
theorem cotangent_isBaseChange : IsBaseChange B
    (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) := by
  let e := KaehlerDifferential.tensorKaehlerEquiv C K S B
  apply IsBaseChange.of_equiv e
  intro ω
  have he : (e.toLinearMap.restrictScalars S).comp
      (TensorProduct.mk S B (KaehlerDifferential C S) 1) =
      DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K := by
    apply Derivation.liftKaehlerDifferential_unique
    ext s
    change KaehlerDifferential.tensorKaehlerEquiv C K S B
      ((1 : B) ⊗ₜ[S] KaehlerDifferential.D C S s) =
      KaehlerDifferential.map C K S B (KaehlerDifferential.D C S s)
    rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul,
      KaehlerDifferential.map_D]
  exact LinearMap.congr_fun he ω

/-- The SAME actual native cotangent reduction has kernel precisely pΩ. -/
theorem cotangent_reduction_eq_zero_iff (b : Reduction p S B)
    (hq : algebraMap S B = b.map) (ω : KaehlerDifferential C S) :
    DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K ω = 0 ↔
      ∃ η : KaehlerDifferential C S, (p : S) • η = ω :=
  baseChange_eq_zero_iff b hq
    (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K)
    (cotangent_isBaseChange C K) ω

/-- The elementwise criterion is equality with the actual multiplication-by-p submodule. -/
theorem cotangent_reduction_kernel (b : Reduction p S B) (hq : algebraMap S B = b.map) :
    LinearMap.ker
      (DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K) =
      (p : S) • (⊤ : Submodule S (KaehlerDifferential C S)) := by
  ext ω
  rw [LinearMap.mem_ker, cotangent_reduction_eq_zero_iff C K b hq]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

variable [Fact p.Prime] [CharP K p] [CharP B p]
  {R : Type z} [CommRing R]

/-- An ACTUAL lift of the genuine relative Frobenius has individual differential
p-divisors. The residue source is the original coefficient-preserving Frobenius twist. -/
theorem exists_individual_relativeFrobenius_divisor
    (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
    (b : Reduction p S B) (hq : algebraMap S B = b.map) (f : R →+* S)
    (hf : ∀ x, b.map (f x) =
      (RelativeFrobenius.map (algebraMap K B) p).hom (a.map x)) (x : R) :
    ∃ η : KaehlerDifferential C S, (p : S) • η = KaehlerDifferential.D C S (f x) := by
  apply (cotangent_reduction_eq_zero_iff C K b hq _).mp
  rw [DeligneIllusieLocalContinuationDifferential.reduction_D, hq, hf]
  exact RelativeFrobeniusCoefficient.D_map_eq_zero p (a.map x)

end Cotangent
end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCotangentKernel
