/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Whole scalar-algebra tensor maps are determined by original elements

This arbitrary-ring extensionality producer uses the actual coefficient action
and all entire right-factor elements. No field, scalar injectivity or supplied
comparison is needed.
-/

open scoped TensorProduct
namespace EnvelopeProperty

/-- Whole scalar-algebra tensor maps are determined by every entire original right-factor element. -/
theorem tensorAlgHom_ext_of_one_tmul
    {R K Q C : Type*} [CommRing R] [CommRing K] [CommRing Q] [CommRing C]
    [Algebra R K] [Algebra R Q] [Algebra K C]
    (f g : K ⊗[R] Q →ₐ[K] C)
    (h : ∀ q : Q, f (1 ⊗ₜ[R] q) = g (1 ⊗ₜ[R] q)) : f = g := by
  let : Algebra R C := Algebra.restrictScalars R K C
  let : IsScalarTower R K C := IsScalarTower.restrictScalars R K C
  apply Algebra.TensorProduct.ext
  · ext
  · ext q
    exact h q

end EnvelopeProperty
