/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.AlgGeom.QuasicoherentImageIdeal
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.QuasicoherentImageIdeal
/-- Corestrict the SAME original morphism to the module of its actual image ideal. -/
def corestriction {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (φ : M ⟶ Scheme.Modules.unitObj X) :
    M ⟶ (QuasicoherentImageIdeal.imageIdeal M φ).toModules where
  val :=
    { app W := ModuleCat.ofHom ((φ.val.app W).hom.codRestrict
        ((QuasicoherentImageIdeal.imageIdeal M φ).toSubmodule.obj W) (by
          intro m U hU
          change X.presheaf.map (homOfLE hU).op (φ.val.app W m) ∈
            (QuasicoherentImageIdeal.imageIdeal M φ).ideal U
          exact ⟨M.val.map (homOfLE hU).op m,
            PresheafOfModules.naturality_apply φ.val (homOfLE hU).op m⟩))
      naturality := by
        intro U V i
        ext m
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply φ.val i m }

/-- The actual corestriction followed by the existing ideal inclusion is the original map. -/
theorem corestriction_inclusion {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (φ : M ⟶ Scheme.Modules.unitObj X) :
    corestriction M φ ≫ (QuasicoherentImageIdeal.imageIdeal M φ).toModulesInclusion = φ := by
  rfl

end EnvelopeProperty.QuasicoherentImageIdeal
