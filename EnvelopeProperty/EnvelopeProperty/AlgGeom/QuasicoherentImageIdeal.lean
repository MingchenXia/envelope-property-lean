/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.AlgGeom.ModuleImageIdealSheaf
import Hironaka.Scheme.Modules.Sections
import ModularCurves.Picard.InvertibleSheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace EnvelopeProperty.QuasicoherentImageIdeal
variable {X : Scheme.{u}} (M : X.Modules) [hM : M.IsQuasicoherent]
  (φ : M ⟶ Scheme.Modules.unitObj X)

private theorem image_localization (U : X.affineOpens) (f : Γ(X, U)) :
    Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      ((φ.val.app (op U.1)).hom.range : Ideal Γ(X, U)) =
    ((φ.val.app (op (X.basicOpen f))).hom.range : Ideal Γ(X, X.basicOpen f)) := by
  simpa only [Scheme.Modules.unitTargetImageIdeal, Scheme.affineBasicOpen] using
    Scheme.Modules.map_unitTargetImageIdeal_basicOpen φ U f

/-- The genuine ideal sheaf image of the original quasi-coherent module morphism. -/
def imageIdeal : X.IdealSheafData where
  ideal U := (φ.val.app (op U.1)).hom.range
  map_ideal_basicOpen U f := image_localization M φ U f

include hM in
/-- Membership uses an actual section of the original module on the same affine open. -/
theorem mem_imageIdeal (U : X.affineOpens) (a : Γ(X, U)) :
    a ∈ (imageIdeal M φ).ideal U ↔ ∃ m : Γ(M, U.1), φ.val.app (op U.1) m = a :=
  Iff.rfl

end EnvelopeProperty.QuasicoherentImageIdeal
