import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceOriginalLineTraceNativeSquare

/-! # Naturality of the original inverse-PF trace in its actual line

The same algebra-valued structure trace induces line traces that commute with
every morphism between the original invertible modules. Its coefficient laws
are proved internally from the original inverse projection formula.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open SchemeLineProjectionFormula SchemeLineProjectionFormulaUnit
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  for (short, mod, original) in [
      (`naturalityOriginalLeftUnit,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit),
      (`naturalityOriginalUnitTensorSection,
        `EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaTraceSection,
        `EnvelopeProperty.SchemeLineProjectionFormulaUnit.actualLeftUnit_hom_tensorSection)] do
    let name := Lean.mkPrivateNameCore mod original
    unless (← Lean.getEnv).contains name do
      throwError "missing original line-trace naturality constructor {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem lineTraceNaturality_of_coefficient_laws {X Y : Scheme.{u}}
    (g : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L) (M : X.Modules)
    (τ : (pushforward g).obj (unitObj Y) ⟶ unitObj X) (a : L ⟶ M)
    (TL : (pushforward g).obj ((pullback g).obj L) ⟶ L)
    (TM : (pushforward g).obj ((pullback g).obj M) ⟶ M)
    (hTL : ∀ (W : X.Opens) (b : Γ(Y, g ⁻¹ᵁ W)) (m : Γ(L, W)),
      TL.app W ((· • · : Γ(Y, g ⁻¹ᵁ W) → Γ((pullback g).obj L, g ⁻¹ᵁ W) →
          Γ((pullback g).obj L, g ⁻¹ᵁ W))
        b (((pullbackPushforwardAdjunction g).unit.app L).app W m)) =
      (· • · : Γ(X, W) → Γ(L, W) → Γ(L, W)) (τ.app W b) m)
    (hTM : ∀ (W : X.Opens) (b : Γ(Y, g ⁻¹ᵁ W)) (m : Γ(M, W)),
      TM.app W ((· • · : Γ(Y, g ⁻¹ᵁ W) → Γ((pullback g).obj M, g ⁻¹ᵁ W) →
          Γ((pullback g).obj M, g ⁻¹ᵁ W))
        b (((pullbackPushforwardAdjunction g).unit.app M).app W m)) =
      (· • · : Γ(X, W) → Γ(M, W) → Γ(M, W)) (τ.app W b) m) :
    (pushforward g).map ((pullback g).map a) ≫ TM = TL ≫ a := by
  let U := transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback g).obj L)
  let P := lineProjectionFormulaObj g L hL (unitObj Y)
  let S := P.hom ≫ (pushforward g).map U.hom
  apply (cancel_epi S).mp
  apply SchemeTensorSectionExt.tensorSection_hom_ext
  intro W b m
  let t := ModularCurves.tensorSection ((pushforward g).obj (unitObj Y)) L W b m
  let r : Γ(Y, g ⁻¹ᵁ W) := b
  let v : Γ((pullback g).obj L, g ⁻¹ᵁ W) :=
    ((pullbackPushforwardAdjunction g).unit.app L).app W m
  let z : Γ((pullback g).obj L, g ⁻¹ᵁ W) := r • v
  have hS : S.app W t = z := by
    change U.hom.val.app (.op (g ⁻¹ᵁ W)) (P.hom.val.app (.op W) t) = _
    erw [lineProjectionFormulaObj_hom_tensorSection g L hL (unitObj Y) W b m]
    exact naturalityOriginalUnitTensorSection ((pullback g).obj L) (g ⁻¹ᵁ W) r v
  have hη := congrArg (fun q => Scheme.Modules.Hom.app (X := X) q W m)
    (((pullbackPushforwardAdjunction g).unit.naturality a).symm)
  change ((pullback g).map a).app (g ⁻¹ᵁ W) v =
    ((pullbackPushforwardAdjunction g).unit.app M).app W (a.app W m) at hη
  have hb := (((pullback g).map a).val.app (.op (g ⁻¹ᵁ W))).hom.map_smul r v
  have hz : ((pullback g).map a).app (g ⁻¹ᵁ W) z =
      (· • · : Γ(Y, g ⁻¹ᵁ W) → Γ((pullback g).obj M, g ⁻¹ᵁ W) →
        Γ((pullback g).obj M, g ⁻¹ᵁ W)) r
        (((pullbackPushforwardAdjunction g).unit.app M).app W (a.app W m)) :=
    hb.trans (congrArg (fun y : Γ((pullback g).obj M, g ⁻¹ᵁ W) => r • y) hη)
  have hLinear := ((a.val.app (.op W)).hom).map_smul (show Γ(X, W) from τ.app W r) m
  change TM.app W (((pullback g).map a).app (g ⁻¹ᵁ W) (S.app W t)) =
    a.app W (TL.app W (S.app W t))
  rw [hS, hz, hTM, hTL]
  exact hLinear.symm

/-- The exact old inverse-PF trace commutes with any morphism of actual
invertible lines; no line-trace naturality or component certificate is input. -/
theorem originalLineTrace_naturality {X Y : Scheme.{u}}
    (g : Y ⟶ X) (L M : X.Modules) (hL : IsInvertible L) (hM : IsInvertible M)
    (τ : (pushforward g).obj (unitObj Y) ⟶ unitObj X) (a : L ⟶ M) :
    let TL := (pushforward g).map (naturalityOriginalLeftUnit ((pullback g).obj L)).inv ≫
      (lineProjectionFormulaObj g L hL (unitObj Y)).inv ≫
      (tensorRight L).map τ ≫ (naturalityOriginalLeftUnit L).hom
    let TM := (pushforward g).map (naturalityOriginalLeftUnit ((pullback g).obj M)).inv ≫
      (lineProjectionFormulaObj g M hM (unitObj Y)).inv ≫
      (tensorRight M).map τ ≫ (naturalityOriginalLeftUnit M).hom
    (pushforward g).map ((pullback g).map a) ≫ TM = TL ≫ a := by
  exact lineTraceNaturality_of_coefficient_laws g L hL M τ a _ _
    (fun W b m => lineProjectionFormulaObj_unitTrace_app_smul_unit g L hL τ W b m)
    (fun W b m => lineProjectionFormulaObj_unitTrace_app_smul_unit g M hM τ W b m)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
