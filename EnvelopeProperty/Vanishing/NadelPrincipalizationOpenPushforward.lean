import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange
import EnvelopeProperty.AlgGeom.CyclicSectionStructuralUnitRestriction
import EnvelopeProperty.AlgGeom.PushforwardUnitSections
import ModularCurves.Picard.DualPullback.UnitComp

/-! # Actual open Cartesian pushforward comparison and original unit sections

The isomorphism is constructed from the native original Cartesian restriction
comparison and the native restriction--pullback isomorphisms. Its whole section
triangle retains the original structural units and the actual pulled section.
-/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforward
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y X Y' X' : Scheme.{u}} (p : Y ⟶ X) (p' : Y' ⟶ X')
    (h : Y' ⟶ Y) (g : X' ⟶ X) [IsOpenImmersion h] [IsOpenImmersion g]
    (H : IsPullback p' h g p)

/-- The genuine whole open Cartesian natural comparison, for all original modules. -/
def openNatIso : pushforward p ⋙ pullback g ≅ pullback h ⋙ pushforward p' :=
  Functor.isoWhiskerLeft (pushforward p) (restrictFunctorIsoPullback g).symm ≪≫
    restrictPushforwardIsoOfIsPullback p p' h g H ≪≫
    Functor.isoWhiskerRight (restrictFunctorIsoPullback h) (pushforward p')

/-- The actual whole comparison on the given original module. -/
def openIso (M : Y.Modules) :
    (pullback g).obj ((pushforward p).obj M) ≅
      (pushforward p').obj ((pullback h).obj M) :=
  (openNatIso p p' h g H).app M

/-- The whole original module map, including an original rounded inclusion,
commutes with the actual Cartesian comparison. -/
theorem openIso_naturality {M N : Y.Modules} (φ : M ⟶ N) :
    (pullback g).map ((pushforward p).map φ) ≫ (openIso p p' h g H N).hom =
      (openIso p p' h g H M).hom ≫ (pushforward p').map ((pullback h).map φ) :=
  (openNatIso p p' h g H).hom.naturality φ

private theorem open_unit_hom {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] :
    (restrictFunctorIsoPullback j).hom.app (unitObj B) =
      (restrictUnitIso j).hom ≫ (pullbackUnitIso j).inv := by
  apply (cancel_mono (pullbackUnitIso j).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he := ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow j
  rw [← he]
  exact Iso.hom_inv_id_assoc ((restrictFunctorIsoPullback j).app (unitObj B)) _

/-- The SAME whole original structural-unit pushed section is carried to
its SAME actual pulled original section, for every original module section. -/
theorem section_triangle {M : Y.Modules} (δ : unitObj Y ⟶ M) :
    (pullbackUnitIso g).inv ≫
      (pullback g).map
        (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫ (pushforward p).map δ) ≫
      (openIso p p' h g H M).hom =
    SheafOfModules.unitToPushforwardObjUnit p'.toRingCatSheafHom ≫
      (pushforward p').map ((pullbackUnitIso h).inv ≫ (pullback h).map δ) := by
  apply (cancel_epi (restrictUnitIso g).hom).mp
  rw [← Category.assoc (restrictUnitIso g).hom (pullbackUnitIso g).inv,
    ← open_unit_hom g]
  change (restrictFunctorIsoPullback g).hom.app (unitObj X) ≫
      (pullback g).map
        (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫ (pushforward p).map δ) ≫
      (restrictFunctorIsoPullback g).inv.app ((pushforward p).obj M) ≫
      (restrictPushforwardIsoOfIsPullback p p' h g H).hom.app M ≫
      (pushforward p').map ((restrictFunctorIsoPullback h).hom.app M) = _
  rw [← Category.assoc, ← Category.assoc,
    ← (restrictFunctorIsoPullback g).hom.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [(restrictPushforwardIsoOfIsPullback p p' h g H).hom.naturality_assoc δ]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [(restrictFunctorIsoPullback h).hom.naturality, open_unit_hom h]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Category.assoc, restrictPushforwardIsoOfIsPullback, NatIso.ofComponents] using
    congrArg (fun z => z ≫ (pushforward p').map (pullbackUnitIso h).inv ≫
      (pushforward p').map ((pullback h).map δ))
      (CyclicSectionStructuralUnitRestriction.restrictPushforwardUnit_triangle p p' h g H)

/-- The actual pullback--pushforward adjoints of original sections obey the
same whole Cartesian triangle through the internally constructed isomorphism. -/
theorem adjointSection_triangle {M : Y.Modules} (δ : unitObj Y ⟶ M) :
    (pullbackUnitIso g).inv ≫
      (pullback g).map ((pullbackPushforwardAdjunction p).homEquiv _ _
        ((pullbackUnitIso p).hom ≫ δ)) ≫ (openIso p p' h g H M).hom =
    (pullbackPushforwardAdjunction p').homEquiv _ _
      ((pullbackUnitIso p').hom ≫ (pullbackUnitIso h).inv ≫ (pullback h).map δ) := by
  rw [pushforwardUnitSection_homEquiv,
    show (pullbackUnitIso p').hom ≫ (pullbackUnitIso h).inv ≫ (pullback h).map δ =
      (pullbackUnitIso p').hom ≫ ((pullbackUnitIso h).inv ≫ (pullback h).map δ) from rfl,
    pushforwardUnitSection_homEquiv]
  exact section_triangle p p' h g H δ

end EnvelopeProperty.Vanishing.NadelPrincipalizationOpenPushforward
