/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Actual tensor base change of an arbitrary ideal

The canonical map to the actual extended ideal is always surjective and
is an actual linear isomorphism under genuine module flatness.
-/

open TensorProduct
noncomputable section
universe u v
namespace EnvelopeProperty.IdealTensorBaseChange
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable (I : Ideal R)

/-- The canonical actual tensor map to the original extended ideal. -/
def toIdealMap : S ⊗[R] I →ₗ[S] I.map (algebraMap R S) :=
  LinearMap.liftBaseChange S (Algebra.idealMap S I)

/-- The canonical map has the actual multiplication formula on every pure tensor. -/
theorem toIdealMap_tmul (s : S) (x : I) :
    (toIdealMap S I (s ⊗ₜ[R] x) : S) = s * algebraMap R S x := by
  rfl

/-- Its actual whole inclusion is the true base change of the original
ideal inclusion followed by the genuine right-unit tensor isomorphism. -/
theorem toIdealMap_inclusion :
    (I.map (algebraMap R S)).subtype ∘ₗ toIdealMap S I =
      (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ I.subtype.baseChange S := by
  ext s
  simp [toIdealMap_tmul, AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_comm]

/-- Every element of the actual extended ideal comes from the actual tensor map. -/
theorem toIdealMap_surjective : Function.Surjective (toIdealMap S I) := by
  have hrange : I.map (algebraMap R S) ≤
      LinearMap.range ((I.map (algebraMap R S)).subtype ∘ₗ toIdealMap S I) := by
    change Ideal.span ((algebraMap R S) '' (I : Set R)) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨1 ⊗ₜ[R] (⟨x, hx⟩ : I), ?_⟩
    simp [LinearMap.comp_apply, toIdealMap_tmul]
  intro y
  obtain ⟨z, hz⟩ := hrange y.property
  exact ⟨z, Subtype.ext hz⟩

/-- Genuine flatness proves injectivity of the actual canonical ideal tensor map. -/
theorem toIdealMap_injective [Module.Flat R S] :
    Function.Injective (toIdealMap S I) := by
  have hinj : Function.Injective
      ((I.map (algebraMap R S)).subtype ∘ₗ toIdealMap S I) := by
    rw [toIdealMap_inclusion]
    exact (AlgebraTensorModule.rid R S S).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap I.subtype (Submodule.injective_subtype I))
  intro x y hxy
  apply hinj
  exact congrArg Subtype.val hxy

/-- The original canonical ideal tensor map is a genuine linear isomorphism
under actual module flatness, for every original ideal. -/
def equiv [Module.Flat R S] : S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  LinearEquiv.ofBijective (toIdealMap S I)
    ⟨toIdealMap_injective S I, toIdealMap_surjective S I⟩

/-- The genuine flat base-change isomorphism retains the canonical tensor formula. -/
theorem equiv_tmul [Module.Flat R S] (s : S) (x : I) :
    (equiv S I (s ⊗ₜ[R] x) : S) = s * algebraMap R S x :=
  toIdealMap_tmul S I s x

end EnvelopeProperty.IdealTensorBaseChange
