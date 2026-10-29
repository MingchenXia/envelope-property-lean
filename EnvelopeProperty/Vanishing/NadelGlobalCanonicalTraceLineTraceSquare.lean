import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNativeWeightedUnitSquare
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaTraceSection
import EnvelopeProperty.AlgGeom.SchemeTensorSectionExt

/-! # The original line trace inherits an actual structure-trace square

This generic transport lemma uses a structure-module equation, not a
line projection or pullback comparison hypothesis. Its Nadel consumer
supplies the already proved original global structure-trace factor.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open SchemeLineProjectionFormula SchemeLineProjectionFormulaUnit
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory

run_cmd
  for (short, mod, original) in [
      (`originalLineSquare,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap),
      (`originalUnitTensorSection,
        `EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaTraceSection,
        `EnvelopeProperty.SchemeLineProjectionFormulaUnit.actualLeftUnit_hom_tensorSection)] do
    let name := Lean.mkPrivateNameCore mod original
    unless (← Lean.getEnv).contains name do
      throwError "missing original line-trace square helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem nativeComposition_finish {X U V : Scheme.{u}}
    (q : U ⟶ V) (s : V ⟶ X) {D M N : X.Modules} {A B : U.Modules} {C : V.Modules}
    (S : D ⟶ M) (R : M ⟶ N) (j : N ⟶ (pushforward s).obj C)
    (a : M ⟶ (pushforward s).obj ((pushforward q).obj A))
    (e : A ⟶ B) (T : (pushforward q).obj B ⟶ C)
    (W : X.Opens) (x : Γ(D, W)) (z : Γ(M, W))
    (hS : S.app W x = z)
    (hz : j.app W (R.app W z) = T.app (s ⁻¹ᵁ W)
      (e.app (q ⁻¹ᵁ (s ⁻¹ᵁ W)) (a.app W z))) :
    (S ≫ (R ≫ j)).val.app (.op W) x =
      (S ≫ (a ≫ (pushforward s).map ((pushforward q).map e ≫ T))).val.app (.op W) x := by
  change j.app W (R.app W (S.app W x)) = T.app (s ⁻¹ᵁ W)
    (e.app (q ⁻¹ᵁ (s ⁻¹ᵁ W)) (a.app W (S.app W x)))
  rw [hS]
  exact hz

private theorem lineTraceSquare_opaque {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (L : X.Modules) (hL : IsInvertible L)
    (τ : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (ν : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h ≫ (pushforward s).map ν)
    (Tp : (pushforward p).obj ((pullback p).obj L) ⟶ L)
    (Tq : (pushforward q).obj ((pullback q).obj ((pullback s).obj L)) ⟶ (pullback s).obj L)
    (hp : ∀ (W : X.Opens) (b : Γ(Y, p ⁻¹ᵁ W)) (m : Γ(L, W)),
      Tp.app W ((· • · : Γ(Y, p ⁻¹ᵁ W) → Γ((pullback p).obj L, p ⁻¹ᵁ W) →
          Γ((pullback p).obj L, p ⁻¹ᵁ W))
        b (((pullbackPushforwardAdjunction p).unit.app L).app W m)) =
      (· • · : Γ(X, W) → Γ(L, W) → Γ(L, W)) (τ.app W b) m)
    (hq : ∀ (W : V.Opens) (b : Γ(U, q ⁻¹ᵁ W)) (m : Γ((pullback s).obj L, W)),
      Tq.app W ((· • · : Γ(U, q ⁻¹ᵁ W) → Γ((pullback q).obj ((pullback s).obj L), q ⁻¹ᵁ W) →
          Γ((pullback q).obj ((pullback s).obj L), q ⁻¹ᵁ W))
        b (((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj L)).app W m)) =
      (· • · : Γ(V, W) → Γ((pullback s).obj L, W) → Γ((pullback s).obj L, W)) (ν.app W b) m) :
    let e := (pullbackComp g p).app L ≪≫ (pullbackCongr h).app L ≪≫
      (pullbackComp q s).symm.app L
    Tp ≫ (pullbackPushforwardAdjunction s).unit.app L =
      originalLineSquare p q g s h ((pullback p).obj L) ≫
        (pushforward s).map ((pushforward q).map e.hom ≫ Tq) := by
  let e := (pullbackComp g p).app L ≪≫ (pullbackCongr h).app L ≪≫
    (pullbackComp q s).symm.app L
  let Up := transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback p).obj L)
  let P := lineProjectionFormulaObj p L hL (unitObj Y)
  let S := P.hom ≫ (pushforward p).map Up.hom
  let J := CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h
  let left : (pushforward p).obj ((pullback p).obj L) ⟶
      (pushforward s).obj ((pullback s).obj L) :=
    Tp ≫ (pullbackPushforwardAdjunction s).unit.app L
  let right : (pushforward p).obj ((pullback p).obj L) ⟶
      (pushforward s).obj ((pullback s).obj L) :=
    originalLineSquare p q g s h ((pullback p).obj L) ≫
      (pushforward s).map ((pushforward q).map e.hom ≫ Tq)
  change left = right
  apply (cancel_epi S).mp
  change (S ≫ (Tp ≫ (pullbackPushforwardAdjunction s).unit.app L)) =
    (S ≫ (originalLineSquare p q g s h ((pullback p).obj L) ≫
      (pushforward s).map ((pushforward q).map e.hom ≫ Tq)))
  apply SchemeTensorSectionExt.tensorSection_hom_ext
  intro W b m
  let r : Γ(Y, p ⁻¹ᵁ W) := b
  let a : Γ((pullback p).obj L, p ⁻¹ᵁ W) :=
    ((pullbackPushforwardAdjunction p).unit.app L).app W m
  let c : Γ((pullback s).obj L, s ⁻¹ᵁ W) :=
    ((pullbackPushforwardAdjunction s).unit.app L).app W m
  let d : Γ(U, q ⁻¹ᵁ (s ⁻¹ᵁ W)) := J.app W r
  let t := ModularCurves.tensorSection ((pushforward p).obj (unitObj Y)) L W b m
  have hS : S.app W t = r • a := by
    change Up.hom.val.app (.op (p ⁻¹ᵁ W)) (P.hom.val.app (.op W) t) = _
    erw [lineProjectionFormulaObj_hom_tensorSection p L hL (unitObj Y) W r m]
    exact originalUnitTensorSection ((pullback p).obj L) (p ⁻¹ᵁ W) r a
  have hp0 := hp W r m
  change Tp.app W (r • a) = (· • · : Γ(X, W) → Γ(L, W) → Γ(L, W)) (τ.app W r) m at hp0
  have hw := nativeUnit_originalModuleSquare_app_smul p q g s h L W r m
  change e.hom.app (q ⁻¹ᵁ (s ⁻¹ᵁ W))
      ((originalLineSquare p q g s h ((pullback p).obj L)).app W (r • a)) =
    d • (show Γ((pullback q).obj ((pullback s).obj L), q ⁻¹ᵁ (s ⁻¹ᵁ W)) from
      ((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj L)).app (s ⁻¹ᵁ W) c) at hw
  have hq0 := hq (s ⁻¹ᵁ W) d c
  change Tq.app (s ⁻¹ᵁ W)
      (d • (show Γ((pullback q).obj ((pullback s).obj L), q ⁻¹ᵁ (s ⁻¹ᵁ W)) from
        ((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj L)).app (s ⁻¹ᵁ W) c)) =
    (· • · : Γ(V, s ⁻¹ᵁ W) → Γ((pullback s).obj L, s ⁻¹ᵁ W) →
      Γ((pullback s).obj L, s ⁻¹ᵁ W)) (ν.app (s ⁻¹ᵁ W) d) c at hq0
  have hη := (((pullbackPushforwardAdjunction s).unit.app L).val.app (.op W)).hom.map_smul
    (show Γ(X, W) from τ.app W r) m
  have ht := congrArg (fun f : (pushforward p).obj (unitObj Y) ⟶
      (pushforward s).obj (unitObj V) => Scheme.Modules.Hom.app (X := X) f W r) hτ
  change (s.app W) (τ.app W r) = ν.app (s ⁻¹ᵁ W) d at ht
  have hz : ((pullbackPushforwardAdjunction s).unit.app L).app W (Tp.app W (r • a)) =
    Tq.app (s ⁻¹ᵁ W) (e.hom.app (q ⁻¹ᵁ (s ⁻¹ᵁ W))
      ((originalLineSquare p q g s h ((pullback p).obj L)).app W (r • a))) := by
    rw [hp0, hw, hq0]
    exact hη.trans (congrArg (fun z : Γ(V, s ⁻¹ᵁ W) => z • c) ht)
  let z : Γ((pushforward p).obj ((pullback p).obj L), W) := r • a
  have hS0 : S.app W t = z := hS
  have hz0 : ((pullbackPushforwardAdjunction s).unit.app L).app W (Tp.app W z) =
      Tq.app (s ⁻¹ᵁ W) (e.hom.app (q ⁻¹ᵁ (s ⁻¹ᵁ W))
        ((originalLineSquare p q g s h ((pullback p).obj L)).app W z)) := hz
  have hfinish := nativeComposition_finish
    (D := (pushforward p).obj (unitObj Y) ⊗ L)
    (M := (pushforward p).obj ((pullback p).obj L))
    (N := L)
    (A := (pullback g).obj ((pullback p).obj L))
    (B := (pullback q).obj ((pullback s).obj L))
    (C := (pullback s).obj L) q s
    S Tp ((pullbackPushforwardAdjunction s).unit.app L)
    (originalLineSquare p q g s h ((pullback p).obj L)) e.hom Tq W t z hS0 hz0
  dsimp only [t] at hfinish
  exact hfinish

/-- Tensoring the actual structure-trace equation through the SAME
original inverse PF yields the whole native pulled-line equation. -/
theorem lineTrace_nativeSquare_of_structureSquare {X Y U V : Scheme.{u}}
    (p : Y ⟶ X) (q : U ⟶ V) (g : U ⟶ Y) (s : V ⟶ X)
    (h : g ≫ p = q ≫ s) (L : X.Modules) (hL : IsInvertible L)
    (τ : (pushforward p).obj (unitObj Y) ⟶ unitObj X)
    (ν : (pushforward q).obj (unitObj U) ⟶ unitObj V)
    (hτ : τ ≫ SheafOfModules.unitToPushforwardObjUnit s.toRingCatSheafHom =
      CyclicSectionStructuralUnitNaturality.unitSquareMap p q g s h ≫ (pushforward s).map ν) :
    let e := (pullbackComp g p).app L ≪≫ (pullbackCongr h).app L ≪≫
      (pullbackComp q s).symm.app L
    let Tp := (pushforward p).map
      (transportedLeftUnit (ModularCurves.monoidalUnitObjIso Y) ((pullback p).obj L)).inv ≫
      (lineProjectionFormulaObj p L hL (unitObj Y)).inv ≫ (tensorRight L).map τ ≫
      (transportedLeftUnit (ModularCurves.monoidalUnitObjIso X) L).hom
    let Tq := (pushforward q).map
      (transportedLeftUnit (ModularCurves.monoidalUnitObjIso U)
        ((pullback q).obj ((pullback s).obj L))).inv ≫
      (lineProjectionFormulaObj q ((pullback s).obj L) (hL.pullback s) (unitObj U)).inv ≫
      (tensorRight ((pullback s).obj L)).map ν ≫
      (transportedLeftUnit (ModularCurves.monoidalUnitObjIso V) ((pullback s).obj L)).hom
    Tp ≫ (pullbackPushforwardAdjunction s).unit.app L =
      originalLineSquare p q g s h ((pullback p).obj L) ≫
        (pushforward s).map ((pushforward q).map e.hom ≫ Tq) := by
  exact lineTraceSquare_opaque p q g s h L hL τ ν hτ _ _
    (fun W b m => lineProjectionFormulaObj_unitTrace_app_smul_unit p L hL τ W b m)
    (fun W b m => lineProjectionFormulaObj_unitTrace_app_smul_unit q ((pullback s).obj L)
      (hL.pullback s) ν W b m)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
