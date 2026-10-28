import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationDualUnitLocalComparison

/-!
# Literal unit evaluation of actual canonical dual sections

The route is owned `dual-canonical-section-evaluation-route.tex`.
Unit evaluation determines the whole original sheaf morphism; no section,
frame, scalar or norm comparison is assumed.
-/
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace EnvelopeProperty.OriginalDualPullbackCoherence
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Whole actual structure-module morphisms are determined by their literal top-open value on one. -/
theorem unitHom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {α β : unitObj X ⟶ M}
    (h : α.val.app (op ⊤) (1 : Γ(X, ⊤)) = β.val.app (op ⊤) (1 : Γ(X, ⊤))) : α = β := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply α.val i (1 : Γ(X, ⊤))
  have hb := PresheafOfModules.naturality_apply β.val i (1 : Γ(X, ⊤))
  change α.val.app V (X.presheaf.map i (1 : Γ(X, ⊤))) =
    M.presheaf.map i (α.val.app (op ⊤) (1 : Γ(X, ⊤))) at ha
  change β.val.app V (X.presheaf.map i (1 : Γ(X, ⊤))) =
    M.presheaf.map i (β.val.app (op ⊤) (1 : Γ(X, ⊤))) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun q => M.presheaf.map i q) h).trans hb.symm)

/-- The actual canonical dual section is literally the original functional on one over every original open. -/
theorem canonicalDualSection_app_one {X : Scheme.{u}} {M : X.Modules}
    (q : M ⟶ unitObj X) (U : X.Opens) :
    (((dualUnitObjIso (X := X)).inv ≫ dualMapObj q).val.app (op U)) (1 : Γ(X, U)) =
      q.over U := by
  have hone : (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
      (1 : Γ(X, U))).asHom = 𝟙 (SheafOfModules.unit (X.ringCatSheaf.over U)) := by
    let : ∀ W, IsMulCommutative (X.ringCatSheaf.obj.obj W) := fun W => by
      change IsMulCommutative (X.presheaf.obj W)
      exact IsMulCommutative.of_comm fun a b => mul_comm a b
    exact congrArg End.asHom
      ((ModularCurves.SheafOfModules.overUnitScalarEndRingHom X.ringCatSheaf U).map_one)
  change q.over U ≫ (ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
    (1 : Γ(X, U))).asHom = q.over U
  rw [hone]
  exact Category.comp_id (q.over U)

end EnvelopeProperty.OriginalDualPullbackCoherence

#check @EnvelopeProperty.OriginalDualPullbackCoherence.unitHom_ext_top
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.unitHom_ext_top
#check @EnvelopeProperty.OriginalDualPullbackCoherence.canonicalDualSection_app_one
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.canonicalDualSection_app_one
