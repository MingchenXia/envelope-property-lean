import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The original pullback congruence for the reverse equality

All functors and original scheme arrows are retained; only equality
elimination identifies the two unchanged inverse maps.
-/
noncomputable section
namespace EnvelopeProperty.SchemePullbackCongrInverse
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pullback along the reverse actual scheme equality is the inverse of
pullback along that same equality, on the same original module. -/
theorem reverse_hom {X Y : Scheme.{u}} (f g : X ⟶ Y) (h : f = g)
    (M : Y.Modules) :
    ((pullbackCongr h.symm).app M).hom = ((pullbackCongr h).app M).inv := by
  cases h
  rfl

end EnvelopeProperty.SchemePullbackCongrInverse
