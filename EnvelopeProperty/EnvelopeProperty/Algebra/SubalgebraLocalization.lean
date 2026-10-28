/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Literal localization subalgebras are contained in every actual unit target
-/

noncomputable section
namespace EnvelopeProperty
open scoped Classical
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A literal actual source localization lies in every original-field subalgebra
which contains the source and makes all its actual denominators units. -/
theorem le_of_source_localization_units
    (C E V : Subalgebra k K) (hCE : C ≤ E) (hCV : C ≤ V) (M : Submonoid C)
    (hlocal : letI : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
      IsLocalization M E)
    (hu : ∀ y : M, IsUnit ((Subalgebra.inclusion hCV).toRingHom y.val)) : E ≤ V := by
  let _ : Algebra C E := (Subalgebra.inclusion hCE).toAlgebra
  let : IsLocalization M E := hlocal
  let f : E →+* V := IsLocalization.lift (S := E) hu
  have hf : V.val.toRingHom.comp f = E.val.toRingHom := by
    apply IsLocalization.ringHom_ext M
    ext c
    change (f (algebraMap C E c) : K) = (algebraMap C E c : K)
    rw [show f (algebraMap C E c) = (Subalgebra.inclusion hCV).toRingHom c from
      IsLocalization.lift_eq hu c]
    rfl
  intro x hx
  let e : E := ⟨x, hx⟩
  have heq : (f e : K) = x := RingHom.congr_fun hf e
  exact heq ▸ (f e).property

end EnvelopeProperty
