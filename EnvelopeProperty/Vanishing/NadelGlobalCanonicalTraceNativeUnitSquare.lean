import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange
import ModularCurves.Picard.DualPullback.UnitComp

/-! # The native unit through the original commuting module square

For an arbitrary commuting scheme square, the original f439 module-square
map carries the native pullback unit to the two successive native units.
All pullback and pushforward comparisons are the original ones. No
cartesian-square, base-change, trace or desired comparison certificate is
an input.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Exact existing declarations; only elaborator scope is extended.
run_cmd
  for (short, mod, original) in [
      (`frozenOriginalModuleSquareMap,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.originalModuleSquareMap),
      (`frozenPullbackCongrMate,
        `ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange,
        `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackCongr_hom)] do
    let name := Lean.mkPrivateNameCore mod original
    unless (← Lean.getEnv).contains name do
      throwError "missing original native module-square coherence helper {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      { scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls }

private theorem pullbackCongr_inv_mate
    {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) :
    conjugateEquiv (pullbackPushforwardAdjunction a)
        (pullbackPushforwardAdjunction b) (pullbackCongr h).inv =
      (pushforwardCongr h).hom := by
  have hc : conjugateIsoEquiv (pullbackPushforwardAdjunction b)
      (pullbackPushforwardAdjunction a) (pullbackCongr h) =
        (pushforwardCongr h).symm := by
    apply Iso.ext
    exact frozenPullbackCongrMate h
  exact congrArg Iso.inv hc

private theorem unit_after_mate_iso
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₁ ≅ L₂) (d : R₁ ≅ R₂)
    (hd : conjugateEquiv adj₁ adj₂ e.inv = d.hom) (M : C) :
    adj₁.unit.app M ≫ d.hom.app (L₁.obj M) ≫ R₂.map (e.hom.app M) =
      adj₂.unit.app M := by
  have hu := unit_conjugateEquiv adj₁ adj₂ e.inv M
  rw [hd] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc, ← R₂.map_comp, Iso.inv_hom_id_app, R₂.map_id]
  erw [Category.comp_id]

/-- The original unweighted module-square map sends the actual native
unit to the successive native units, under the actual source comparison.
Only commutativity of the original scheme square is assumed. -/
theorem nativeUnit_originalModuleSquare
    {X Y U V : Scheme.{u}} (p : Y ⟶ X) (q : U ⟶ V)
    (g : U ⟶ Y) (s : V ⟶ X) (h : g ≫ p = q ≫ s) (M : X.Modules) :
    let e := (pullbackComp g p).app M ≪≫ (pullbackCongr h).app M ≪≫
      (pullbackComp q s).symm.app M
    (pullbackPushforwardAdjunction p).unit.app M ≫
      frozenOriginalModuleSquareMap p q g s h ((pullback p).obj M) ≫
      (pushforward s).map ((pushforward q).map e.hom) =
        (pullbackPushforwardAdjunction s).unit.app M ≫
          (pushforward s).map
            ((pullbackPushforwardAdjunction q).unit.app ((pullback s).obj M)) := by
  let adj₀ := (pullbackPushforwardAdjunction p).comp (pullbackPushforwardAdjunction g)
  let adj₁ := pullbackPushforwardAdjunction (g ≫ p)
  let adj₂ := pullbackPushforwardAdjunction (q ≫ s)
  let adj₃ := (pullbackPushforwardAdjunction s).comp (pullbackPushforwardAdjunction q)
  let e := pullbackComp g p ≪≫ pullbackCongr h ≪≫ (pullbackComp q s).symm
  let d := pushforwardComp g p ≪≫ pushforwardCongr h ≪≫ (pushforwardComp q s).symm
  have hC : conjugateEquiv adj₀ adj₁ (pullbackComp g p).inv =
      (pushforwardComp g p).hom := conjugateEquiv_pullbackComp_inv g p
  have hB : conjugateEquiv adj₁ adj₂ (pullbackCongr h).inv =
      (pushforwardCongr h).hom := pullbackCongr_inv_mate h
  have hA : conjugateEquiv adj₂ adj₃ (pullbackComp q s).hom =
      (pushforwardComp q s).inv := ModularCurves.pullbackUnitIso_comp_conjugateLow q s
  have hd : conjugateEquiv adj₀ adj₃ e.inv = d.hom := by
    change conjugateEquiv adj₀ adj₃
      ((pullbackComp q s).hom ≫ (pullbackCongr h).inv ≫ (pullbackComp g p).inv) = _
    simp only [← Category.assoc]
    rw [← conjugateEquiv_comp adj₀ adj₁ adj₃, hC]
    rw [← conjugateEquiv_comp adj₁ adj₂ adj₃, hB, hA]
    rfl
  have hu := unit_after_mate_iso adj₀ adj₃ e d hd M
  simpa only [frozenOriginalModuleSquareMap, e, d, adj₀, adj₃,
    Adjunction.comp_unit_app, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.comp_obj, Functor.comp_map, Category.assoc] using hu

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
