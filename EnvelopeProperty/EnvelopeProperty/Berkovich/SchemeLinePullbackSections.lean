import EnvelopeProperty.Berkovich.SchemeLineLocalSectionEvaluation

/-! # Actual original global line sections and frames under whole scheme pullback -/
open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Native pullback of the SAME original whole section commutes with actual composition. -/
theorem pullbackSectionHom_comp {X Y Z : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (α : Scheme.Modules.unitObj Z ⟶ M) :
    pullbackSectionHom i (pullbackSectionHom g α) ≫
        (Scheme.Modules.pullbackComp i g).hom.app M =
      pullbackSectionHom (i ≫ g) α := by
  let c := Scheme.Modules.pullbackComp i g
  have hn := c.hom.naturality α
  simp only [Functor.comp_map] at hn
  have hu := congrArg Iso.inv (show
    c.app (Scheme.Modules.unitObj Z) ≪≫ Scheme.Modules.pullbackUnitIso (i ≫ g) =
      (Scheme.Modules.pullback i).mapIso (Scheme.Modules.pullbackUnitIso g) ≪≫
        Scheme.Modules.pullbackUnitIso i from by
          apply Iso.ext
          exact ModularCurves.pullbackUnitIso_compLow i g)
  change (Scheme.Modules.pullbackUnitIso (i ≫ g)).inv ≫ c.inv.app (Scheme.Modules.unitObj Z) =
      (Scheme.Modules.pullbackUnitIso i).inv ≫
        (Scheme.Modules.pullback i).map (Scheme.Modules.pullbackUnitIso g).inv at hu
  unfold pullbackSectionHom
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simp only [← Category.assoc]
  rw [← hu]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- An ACTUAL original line frame pulled back over its actual inverse-image open. -/
def localPullbackFrame {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens) {M : Y.Modules}
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj M) ≅
      Scheme.Modules.unitObj (g ⁻¹ᵁ U).toScheme :=
  (Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
    Scheme.Modules.frameViaFactor (g ∣_ U) U.ι ((g ⁻¹ᵁ U).ι ≫ g)
      (morphismRestrict_ι g U) e

/-- The SAME original whole local scalar equation is preserved by actual
pullback of the original global section and its original local frame. -/
theorem localPullbackFrame_sectionHom_scalar {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    {M : Y.Modules} (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (α : Scheme.Modules.unitObj Y ⟶ M) (c : Γ(Y, U))
    (hr : pullbackSectionHom U.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U c)) :
    pullbackSectionHom (g ⁻¹ᵁ U).ι (pullbackSectionHom g α) ≫
        (localPullbackFrame g U e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection (g ⁻¹ᵁ U) ((g.app U).hom c)) := by
  simp only [localPullbackFrame, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, pullbackSectionHom_comp,
    frameViaFactor_sectionHom_scalar (g ∣_ U) U.ι ((g ⁻¹ᵁ U).ι ≫ g)
      (morphismRestrict_ι g U) e α _ hr,
    Scheme.Modules.openTopSection_morphismRestrict]
end EnvelopeProperty.SchemeLineSectionEvaluation

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of R)} [IsProper fX]
  (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v fX)

/-- The actual norm of the SAME original globally pulled-back line section
is the actual original local coefficient evaluation on the inverse-image open. -/
theorem modelLineNorm_pullbackSection_eq_localEval (g : X ⟶ Y) {M : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) (U : Y.Opens) (hc : center hb y ∈ g ⁻¹ᵁ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (α : Scheme.Modules.unitObj Y ⟶ M) (c : Γ(Y, U))
    (hr : SchemeLineSectionEvaluation.pullbackSectionHom U.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection (Scheme.Modules.openTopSection U c)) :
    modelLineNorm hb y (hM.pullback g)
        (fibreSection y (SchemeLineSectionEvaluation.pullbackSectionHom g α)) =
      SchemeValuedPoint.eval y.1 (g ⁻¹ᵁ U) (support_mem_of_center_mem hb y _ hc)
        ((g.app U).hom c) :=
  modelLineNorm_fibreSection_eq_localEval hb y (hM.pullback g) _ hc
    (SchemeLineSectionEvaluation.localPullbackFrame g U e)
    (SchemeLineSectionEvaluation.pullbackSectionHom g α) _
    (SchemeLineSectionEvaluation.localPullbackFrame_sectionHom_scalar g U e α c hr)
end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
