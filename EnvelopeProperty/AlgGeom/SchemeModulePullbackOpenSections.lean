import ModularCurves.ForMathlib.AffineModuleBaseChange

/-! # Original module pullback commutes with original open restriction and units -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModulePullbackOpenSections

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens)

/-- The actual entire original pushforward square at the inverse-image open. -/
def pushforwardSquareIso :
    pushforward (g.resLE U (g ⁻¹ᵁ U) le_rfl) ⋙ pushforward U.ι ≅
      pushforward (g ⁻¹ᵁ U).ι ⋙ pushforward g :=
  pushforwardComp _ _ ≪≫
    pushforwardCongr (g.resLE_comp_ι le_rfl) ≪≫ (pushforwardComp _ _).symm

private def restrictedAdjunction :
    restrictFunctor U.ι ⋙ pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl) ⊣
      pushforward (g ⁻¹ᵁ U).ι ⋙ pushforward g :=
  ((restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (g.resLE U (g ⁻¹ᵁ U) le_rfl))).ofNatIsoRight
      (pushforwardSquareIso g U)

/-- Whole original pullback commutes with actual open restriction; the
isomorphism is derived from the genuine original adjunctions. -/
def pullbackRestrictIso (M : X.Modules) :
    (pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).obj (M.restrict U.ι) ≅
      ((pullback g).obj M).restrict (g ⁻¹ᵁ U).ι :=
  ((restrictedAdjunction g U).leftAdjointUniq
    ((pullbackPushforwardAdjunction g).comp (restrictAdjunction (g ⁻¹ᵁ U).ι))).app M

/-- The actual two composite adjunction units retain the SAME whole
original pullback/restriction comparison, with no unit-square premise. -/
theorem unit_square (M : X.Modules) :
    (restrictAdjunction U.ι).unit.app M ≫
        (pushforward U.ι).map
          ((pullbackPushforwardAdjunction (g.resLE U (g ⁻¹ᵁ U) le_rfl)).unit.app
            (M.restrict U.ι)) ≫
        (pushforwardSquareIso g U).hom.app
          ((pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).obj (M.restrict U.ι)) ≫
        (pushforward (g ⁻¹ᵁ U).ι ⋙ pushforward g).map
          (pullbackRestrictIso g U M).hom =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map
          ((restrictAdjunction (g ⁻¹ᵁ U).ι).unit.app ((pullback g).obj M)) := by
  have hh := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictedAdjunction g U)
    ((pullbackPushforwardAdjunction g).comp (restrictAdjunction (g ⁻¹ᵁ U).ι)) M
  simpa only [restrictedAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Adjunction.comp_unit_app, Category.assoc,
    Functor.whiskerLeft_app, pullbackRestrictIso, Iso.app_hom, Functor.comp_obj] using hh

end EnvelopeProperty.SchemeModulePullbackOpenSections
