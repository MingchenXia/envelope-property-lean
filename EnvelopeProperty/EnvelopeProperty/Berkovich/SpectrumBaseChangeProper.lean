/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumBaseChange
import EnvelopeProperty.Berkovich.SpectrumFilters
import EnvelopeProperty.Berkovich.SpectrumIntegralImage

/-!
# Proper prescribed scalar restriction and algebraic complete-base existence

Prescribed scalar base-change restriction is proper and closed over arbitrary
commutative rings, by a genuine ultrafilter lifting proof. Surjectivity is proved
in the separate algebraic field-extension case over a complete ultrametric base,
using actual integral point existence and uniqueness of the extending norm.
All coefficient-seminorm compatibility is explicit.
-/

open scoped NNReal Topology TensorProduct
open Topology Filter

noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

section Proper

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}

/-- Scalar base-change restriction is proper by the actual ultrafilter lifting
criterion, over arbitrary rings with explicitly compatible coefficient seminorms. -/
theorem isProperMap_baseChangeRestriction (hwv : ∀ r, w (algebraMap R S r) = v r) :
    IsProperMap (baseChangeRestriction (A := A) hwv) := by
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨continuous_baseChangeRestriction hwv, fun {U} {y} hy => ?_⟩
  have hbound : ∀ t : S ⊗[R] A, ∃ M : ℝ≥0,
      ∀ᶠ z in (U : Filter (RelativeSpectrum w (S ⊗[R] A))), z.1.val t ≤ M := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Eventually.of_forall fun z => by simp only [map_zero, le_refl]⟩
    | tmul s a =>
      have ht : Tendsto (fun z => (baseChangeRestriction hwv z).1.val a) U (𝓝 (y.1.val a)) :=
        ((continuous_val_apply a).tendsto y).comp hy
      obtain ⟨M, hM⟩ := ht.isBoundedUnder_le
      change ∀ᶠ z in (U : Filter (RelativeSpectrum w (S ⊗[R] A))),
        (baseChangeRestriction hwv z).1.val a ≤ M at hM
      refine ⟨w s * M, hM.mono fun z hz => ?_⟩
      rw [baseChange_val_tmul hwv]
      exact mul_le_mul' le_rfl hz
    | add t s ht hs =>
      obtain ⟨M, hM⟩ := ht
      obtain ⟨N, hN⟩ := hs
      exact ⟨max M N, (hM.and hN).mono fun z hz =>
        (z.1.val.map_add t s).trans (max_le_max hz.1 hz.2)⟩
  exact exists_ultrafilter_limit_of_bounded_evaluations U hbound

/-- Arbitrary prescribed scalar base-change restriction is closed. -/
theorem isClosedMap_baseChangeRestriction (hwv : ∀ r, w (algebraMap R S r) = v r) :
    IsClosedMap (baseChangeRestriction (A := A) hwv) :=
  (isProperMap_baseChangeRestriction hwv).isClosedMap

end Proper

section AlgebraicTensor

variable {K S A : Type*} [Field K] [Field S] [CommRing A] [Algebra K S] [Algebra K A]

/-- Tensoring the injective field inclusion with a vector space makes the actual
right tensor inclusion injective, including when the original algebra is zero. -/
theorem tensorIncludeRight_injective_of_fieldExtension :
    Function.Injective (Algebra.TensorProduct.includeRight (R := K) (A := S) (B := A)) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K S).injective

/-- Algebraicity of the new scalar field makes the right tensor inclusion integral. -/
theorem tensorIncludeRight_isIntegral_of_isAlgebraic [Algebra.IsAlgebraic K S] :
    (Algebra.TensorProduct.includeRight (R := K) (A := S) (B := A)).toRingHom.IsIntegral := by
  let : Algebra.IsIntegral K S := ⟨fun s => (Algebra.IsAlgebraic.isAlgebraic s).isIntegral⟩
  let δ := Algebra.TensorProduct.comm K S A
  have hcomp : δ.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := K) (A := S) (B := A)).toRingHom =
      (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := S)).toRingHom := rfl
  intro t
  apply RingHom.IsIntegralElem.of_map (g := δ.toRingHom) δ.injective
  rw [hcomp]
  exact Algebra.IsIntegral.isIntegral (δ t)

end AlgebraicTensor

section AlgebraicCompleteBase

variable {K S A : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [Field S] [CommRing A] [Algebra K S] [Algebra.IsAlgebraic K S] [Algebra K A]
    {w : Valuation S ℝ≥0}

/-- Algebraic field extension over a complete ultrametric base gives actual
surjectivity of prescribed scalar restriction. Compatibility is explicit, and
the new scalar field needs no additional normed or complete structure. -/
theorem baseChangeRestriction_surjective_of_isAlgebraic
    (hw : ∀ c : K, w (algebraMap K S c) = ‖c‖₊) :
    Function.Surjective (baseChangeRestriction (A := A) (v := NormedField.valuation) hw) := by
  intro x
  let φ : A →ₐ[K] S ⊗[K] A := Algebra.TensorProduct.includeRight
  obtain ⟨z, hz⟩ := comap_surjective_of_isIntegral (v := NormedField.valuation (K := K)) φ
    tensorIncludeRight_isIntegral_of_isAlgebraic tensorIncludeRight_injective_of_fieldExtension x
  let wz : Valuation S ℝ≥0 := z.1.val.comap (algebraMap S (S ⊗[K] A))
  have hwz : ∀ c : K, wz (algebraMap K S c) = ‖c‖₊ := by
    intro c
    change z.1.val (algebraMap S (S ⊗[K] A) (algebraMap K S c)) = ‖c‖₊
    rw [← IsScalarTower.algebraMap_apply K S (S ⊗[K] A), z.2]
    rfl
  have heq : wz = w := EnvelopeProperty.Valuation.eq_of_extends_norm hwz hw
  let y : RelativeSpectrum w (S ⊗[K] A) :=
    ⟨z.1, fun s => congrArg (fun u : Valuation S ℝ≥0 => u s) heq⟩
  exact ⟨y, Subtype.ext (congrArg Subtype.val hz)⟩

end AlgebraicCompleteBase

end EnvelopeProperty.Berkovich.RelativeSpectrum
