/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.GroupActionProductIso
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual flatness of whole group-scheme actions

The genuine product-action isomorphism identifies the entire action map
with a true product projection. Flatness follows by actual base change.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty

/-- Every action of a genuine flat group scheme has a flat whole action morphism. -/
theorem flat_groupAction {S : Scheme.{u}} (G B : Over S)
    [GrpObj G] [ModObj G B] [Flat G.hom] :
    Flat (ModObj.smul (M := G) (X := B)).left := by
  let e := actionProductIso G B
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have h : Flat (e.hom.left ≫ pullback.snd G.hom B.hom) := inferInstance
  have he : e.hom.left ≫ pullback.snd G.hom B.hom =
      (ModObj.smul (M := G) (X := B)).left :=
    congrArg (fun q : G ⊗ B ⟶ B => q.left) (actionProductIso_snd G B)
  exact he ▸ h

/-- Over an actual field the entire action map of every genuine group scheme
is flat, without any additional group-flatness or model hypothesis. -/
theorem flat_groupAction_over_field {k : Type u} [Field k]
    (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [ModObj G B] :
    Flat (ModObj.smul (M := G) (X := B)).left := by
  have : Flat G.hom := inferInstance
  exact flat_groupAction G B

end EnvelopeProperty
