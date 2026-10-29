import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaTensorSection
import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import EnvelopeProperty.AlgGeom.MonoidalProjectionFormulaUnitTransport

/-! # Every local coefficient of the original tensor-induced line trace

The statement spells out the original inverse PF composite. The given
structure-module morphism is arbitrary; no compatibility is assumed.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
namespace EnvelopeProperty.SchemeLineProjectionFormulaUnit
open Scheme.Modules EnvelopeProperty.SchemeLineProjectionFormula
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

private theorem actualLeftUnit_hom_tensorSection {X : Scheme.{u}}
    (M : X.Modules) (W : X.Opens) (r : Γ(X, W)) (m : Γ(M, W)) :
    (transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) M).hom.val.app (.op W)
      (ModularCurves.tensorSection (unitObj X) M W r m) = r • m := by
  simpa only [transportedLeftUnit, SchemeTensorUnitSections.leftUnitIso,
    Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Iso.refl_hom,
    whiskerRightIso_hom, MonoidalCategory.tensorHom_id] using
    SchemeTensorUnitSections.leftUnitIso_hom_tensorSection M W r m

/-- The SAME inverse PF line-trace composite sends every local
coefficient times the native unit of a line section to its actual
structure-module image times that same line section. -/
theorem lineProjectionFormulaObj_unitTrace_app_smul_unit {X Y : Scheme.{u}}
    (g : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L)
    (τ : (pushforward g).obj (unitObj Y) ⟶ unitObj X)
    (W : X.Opens) (b : Γ(Y, g ⁻¹ᵁ W)) (m : Γ(L, W)) :
    ((pushforward g).map
        (transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback g).obj L)).inv ≫
      (lineProjectionFormulaObj g L hL (unitObj Y)).inv ≫
      (tensorRight L).map τ ≫
      (transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) L).hom).app W
        ((· • · : Γ(Y, g ⁻¹ᵁ W) → Γ((pullback g).obj L, g ⁻¹ᵁ W) →
          Γ((pullback g).obj L, g ⁻¹ᵁ W))
          b (((pullbackPushforwardAdjunction g).unit.app L).app W m)) =
      (· • · : Γ(X, W) → Γ(L, W) → Γ(L, W)) (τ.app W b) m := by
  let P := lineProjectionFormulaObj g L hL (unitObj Y)
  let U := transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback g).obj L)
  let A := transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) L
  let T := (pushforward g).map U.inv ≫ P.inv ≫ (tensorRight L).map τ ≫ A.hom
  let S := P.hom ≫ (pushforward g).map U.hom
  let t := ModularCurves.tensorSection ((pushforward g).obj (unitObj Y)) L W b m
  have hS : S.app W t =
      (· • · : Γ(Y, g ⁻¹ᵁ W) → Γ((pullback g).obj L, g ⁻¹ᵁ W) →
        Γ((pullback g).obj L, g ⁻¹ᵁ W))
        b (((pullbackPushforwardAdjunction g).unit.app L).app W m) := by
    change U.hom.val.app (.op (g ⁻¹ᵁ W)) (P.hom.val.app (.op W) t) = _
    erw [lineProjectionFormulaObj_hom_tensorSection g L hL (unitObj Y) W b m]
    exact actualLeftUnit_hom_tensorSection ((pullback g).obj L) (g ⁻¹ᵁ W) b _
  have hc : S ≫ T = (tensorRight L).map τ ≫ A.hom := by
    dsimp only [S, T]
    simp only [Category.assoc]
    erw [← (pushforward g).map_comp_assoc, U.hom_inv_id,
      (pushforward g).map_id, Category.id_comp, P.hom_inv_id_assoc]
  have hv := congrArg (fun f => Scheme.Modules.Hom.app (X := X) f W t) hc
  change T.app W (S.app W t) = A.hom.val.app (.op W) (((tensorRight L).map τ).val.app (.op W) t) at hv
  rw [hS] at hv
  have ht := ModularCurves.tensorSection_map τ (𝟙 L) W b m
  erw [MonoidalCategory.tensorHom_id] at ht
  change ((tensorRight L).map τ).val.app (.op W) t =
    ModularCurves.tensorSection (unitObj X) L W (τ.app W b) m at ht
  rw [ht] at hv
  exact hv.trans (actualLeftUnit_hom_tensorSection L W (τ.app W b) m)

end EnvelopeProperty.SchemeLineProjectionFormulaUnit
