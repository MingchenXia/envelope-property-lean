import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # A nonzero scalar fibre detects a free module of arbitrary rank

This applies to coefficient-localized cohomology after generic freeness.
No finiteness over the arithmetic coefficient ring is assumed.
-/
noncomputable section
namespace EnvelopeProperty.FreeFiberDetection
open scoped TensorProduct
universe u v w
set_option autoImplicit false

/-- A free module of arbitrary rank is zero if one nonzero scalar
extension is zero. In particular, this does not require finite rank. -/
theorem subsingleton_of_baseChange
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Nontrivial A] [Algebra R A]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Free R M]
    (h : Subsingleton (A ⊗[R] M)) : Subsingleton M := by
  classical
  let b := Module.Free.chooseBasis R M
  letI : Subsingleton (A ⊗[R] M) := h
  letI : IsEmpty (Module.Free.ChooseBasisIndex R M) :=
    ⟨fun i => (b.baseChange A).ne_zero i (Subsingleton.elim _ 0)⟩
  exact ⟨fun x y => b.repr.injective (Subsingleton.elim _ _)⟩

end EnvelopeProperty.FreeFiberDetection
