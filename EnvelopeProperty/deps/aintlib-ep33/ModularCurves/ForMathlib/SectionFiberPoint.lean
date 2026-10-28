/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
universe u
namespace ModularCurves

/-- The point of the fibre `π.fiber s` induced by a section `z : S ⟶ E` of `π`. -/
noncomputable def sectionFiberPoint {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (s : S) : Spec (S.residueField s) ⟶ π.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ z) (𝟙 _)
    (by simp [Category.assoc, hz])

end ModularCurves
