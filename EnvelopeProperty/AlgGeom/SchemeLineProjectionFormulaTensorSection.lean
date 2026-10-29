import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaComponent
import ModularCurves.EllipticCurve.PullbackTensorSection

/-! # Every native pure tensor under the same original line PF

The coefficient and line section are arbitrary actual sections on their
original opens.  No section-algebra model or local frame is installed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open Scheme.Modules EnvelopeProperty.SchemeLineProjectionFormula
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
private noncomputable local instance originalTensorSectionPullbackMonoidal
    {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (pullback g).Monoidal := Scheme.Modules.pullbackMonoidal g

/-- On every actual open and every original pure tensor, the original
PF keeps its coefficient and applies only the native unit to the line. -/
theorem lineProjectionFormulaObj_hom_tensorSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (hL : IsInvertible L) (N : Y.Modules)
    (U : X.Opens) (b : Γ(N, g ⁻¹ᵁ U)) (m : Γ(L, U)) :
    (lineProjectionFormulaObj g L hL N).hom.val.app (.op U)
      (ModularCurves.tensorSection ((pushforward g).obj N) L U
        (show Γ((pushforward g).obj N, U) from b) m) =
      ModularCurves.tensorSection N ((pullback g).obj L) (g ⁻¹ᵁ U) b
        (((pullbackPushforwardAdjunction g).unit.app L).val.app (.op U) m) := by
  let S := (pushforward g).obj N
  let A := pullbackPushforwardAdjunction g
  have hv := congrArg
    (fun f : S ⊗ L ⟶ (pushforward g).obj (N ⊗ (pullback g).obj L) =>
      f.val.app (.op U) (ModularCurves.tensorSection S L U b m))
    (lineProjectionFormulaObj_hom_component g L hL N)
  change (lineProjectionFormulaObj g L hL N).hom.val.app (.op U)
      (ModularCurves.tensorSection S L U b m) =
    (A.counit.app N ▷ (pullback g).obj L).val.app (.op (g ⁻¹ᵁ U))
      ((Functor.OplaxMonoidal.δ (pullback g) S L).val.app (.op (g ⁻¹ᵁ U))
        ((A.unit.app (S ⊗ L)).val.app (.op U)
          (ModularCurves.tensorSection S L U b m))) at hv
  have hd := ModularCurves.pullback_δ_unit_tensorSection g S L U b m
  dsimp only at hd
  erw [hd] at hv
  have ht := ModularCurves.tensorSection_map (A.counit.app N) (𝟙 ((pullback g).obj L))
    (g ⁻¹ᵁ U) ((A.unit.app S).val.app (.op U) b) ((A.unit.app L).val.app (.op U) m)
  erw [MonoidalCategory.tensorHom_id] at ht
  change (A.counit.app N ▷ (pullback g).obj L).val.app (.op (g ⁻¹ᵁ U))
      (ModularCurves.tensorSection ((pullback g).obj S) ((pullback g).obj L)
        (g ⁻¹ᵁ U) ((A.unit.app S).val.app (.op U) b) ((A.unit.app L).val.app (.op U) m)) =
    ModularCurves.tensorSection N ((pullback g).obj L) (g ⁻¹ᵁ U)
      ((A.counit.app N).val.app (.op (g ⁻¹ᵁ U)) ((A.unit.app S).val.app (.op U) b))
      ((A.unit.app L).val.app (.op U) m) at ht
  have hc := congrArg (fun f : S ⟶ S => f.val.app (.op U) b) (A.right_triangle_components N)
  change (A.counit.app N).val.app (.op (g ⁻¹ᵁ U)) ((A.unit.app S).val.app (.op U) b) = b at hc
  rw [hc] at ht
  exact hv.trans ht

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
