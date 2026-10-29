import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationDualCanonicalSectionEvaluation
import EnvelopeProperty.Berkovich.SchemeLineSectionEvaluation

/-!
# The SAME canonical dual section commutes with actual whole pullback

Proved on literal unit generator one by genuine adjunction naturality and
actual whole-functional pullback. No section/frame/scalar matching input.
Route: owned `dual-canonical-section-pullback-route.tex`.
-/
open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace EnvelopeProperty.OriginalDualPullbackCoherence
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unit-normalized pullback of every canonical dual section is the canonical section of the literal pulled whole functional. -/
theorem canonicalDualSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : X.Modules} (q : M ⟶ unitObj X) :
    SchemeLineSectionEvaluation.pullbackSectionHom f
        ((dualUnitObjIso (X := X)).inv ≫ dualMapObj q) ≫ dualPullbackHom f M =
      (dualUnitObjIso (X := Y)).inv ≫
        dualMapObj ((pullback f).map q ≫ (pullbackUnitIso f).hom) := by
  apply unitHom_ext_top
  let c : unitObj X ⟶ dualObj M := (dualUnitObjIso (X := X)).inv ≫ dualMapObj q
  let qp := (pullback f).map q ≫ (pullbackUnitIso f).hom
  have hc : c.val.app (op ⊤) (1 : Γ(X, ⊤)) = q.over ⊤ :=
    canonicalDualSection_app_one q ⊤
  have hn := (pullbackPushforwardAdjunction f).unit.naturality c
  have hv := congrArg (fun t => t.val.app (op ⊤) (1 : Γ(X, ⊤))) hn.symm
  change ((pullback f).map c).val.app (op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
        (op ⊤) (1 : Γ(X, ⊤))) =
    ((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app (op ⊤)
      (c.val.app (op ⊤) (1 : Γ(X, ⊤))) at hv
  rw [hc, pullback_unit_unit_app_top_apply_oneT, map_one] at hv
  have hl : (dualPullbackHom f M).val.app (op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (((pullbackPushforwardAdjunction f).unit.app (dualObj M)).val.app
        (op ⊤) (q.over ⊤)) = qp.over (f ⁻¹ᵁ (⊤ : X.Opens)) :=
    (dualPullbackHom_unit_appT f M ⊤ (q.over ⊤)).trans
      (localDualPullback_wholeHom f q ⊤)
  have h := (congrArg
    (fun t => (dualPullbackHom f M).val.app (op (f ⁻¹ᵁ (⊤ : X.Opens))) t) hv).trans hl
  have hleft : ((SchemeLineSectionEvaluation.pullbackSectionHom f c ≫
      dualPullbackHom f M).val.app (op ⊤)) (1 : Γ(Y, ⊤)) = qp.over ⊤ := by
    change (dualPullbackHom f M).val.app (op ⊤)
      (((pullback f).map c).val.app (op ⊤)
        ((pullbackUnitIso f).inv.val.app (op ⊤) (1 : Γ(Y, ⊤)))) = _
    exact h
  exact hleft.trans (canonicalDualSection_app_one qp ⊤).symm

end EnvelopeProperty.OriginalDualPullbackCoherence

#check @EnvelopeProperty.OriginalDualPullbackCoherence.canonicalDualSection_pullback
#print axioms EnvelopeProperty.OriginalDualPullbackCoherence.canonicalDualSection_pullback
