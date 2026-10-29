import EnvelopeProperty.AlgGeom.PresheafPullbackBraided
import EnvelopeProperty.AlgGeom.LocalizationPullbackBraided
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-! # Braiding of the same original scheme module pullback -/
noncomputable section
namespace EnvelopeProperty.SchemePullbackBraided
open CategoryTheory MonoidalCategory AlgebraicGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

private abbrev ringSheaf (Z : Scheme.{u}) :=
  (⟨Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
    Z.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat Z)

private noncomputable abbrev sheafification (Z : Scheme.{u}) :=
  PresheafOfModules.sheafification.{u} (𝟙 (ringSheaf Z).obj)

private noncomputable abbrev sheafificationW (Z : Scheme.{u}) :=
  PresheafOfModules.sheafificationW.{u} (𝟙 (ringSheaf Z).obj)

noncomputable local instance exactModuleMonoidalCategory (Z : Scheme.{u}) :
    MonoidalCategory (SheafOfModules (ringSheaf Z)) := by
  change MonoidalCategory Z.Modules
  exact Scheme.Modules.monoidalCategory Z

noncomputable local instance exactModuleSymmetricCategory (Z : Scheme.{u}) :
    SymmetricCategory (SheafOfModules (ringSheaf Z)) := by
  change SymmetricCategory Z.Modules
  exact Scheme.Modules.symmetricCategory Z

noncomputable local instance sheafificationWMonoidal (Z : Scheme.{u}) :
    (sheafificationW Z).IsMonoidal :=
  PresheafOfModules.sheafificationW_isMonoidal _

noncomputable local instance sheafificationLocalization (Z : Scheme.{u}) :
    (sheafification Z).IsLocalization (sheafificationW Z) :=
  PresheafOfModules.sheafificationW_isLocalization (ringSheaf Z)

private noncomputable abbrev localizedSheafification (Z : Scheme.{u}) :=
  Localization.Monoidal.toMonoidalCategory
    (L := sheafification Z) (W := sheafificationW Z) (Iso.refl _)

noncomputable local instance presheafPushforwardIsRightAdjoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).IsRightAdjoint := by
  change (PresheafOfModules.pushforward.{u}
    (PresheafOfModules.schemeRingPresheafHom f)).IsRightAdjoint
  exact PresheafOfModules.instIsRightAdjointPushforward
    (PresheafOfModules.schemeRingPresheafHom f)

/-- The original scheme pullback, for every scheme morphism, is braided for
the exact monoidal structure already used by the original projection formula. -/
@[implicit_reducible]
def pullbackBraided {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Braided := by
  let φ := PresheafOfModules.schemeRingPresheafHom f
  let LX := localizedSheafification X
  let LY := localizedSheafification Y
  letI : LX.IsLocalization (sheafificationW X) := by
    dsimp only [LX, localizedSheafification]
    infer_instance
  letI : LX.Braided := by
    dsimp only [LX, localizedSheafification]
    infer_instance
  let G := PresheafOfModules.pullback.{u} φ ⋙ LY
  letI : (PresheafOfModules.pullback.{u} φ).Braided := presheafPullbackBraided f
  letI : LY.Braided := by
    dsimp only [LY]
    infer_instance
  letI : G.Braided := by
    dsimp only [G]
    infer_instance
  letI : Localization.Lifting LX (sheafificationW X)
      G (Scheme.Modules.pullback f) :=
    ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩
  letI h := MonoidalBraidedDescent.localizationBraidedOfComp LX
    (D := SheafOfModules (ringSheaf X))
    (E := SheafOfModules (ringSheaf Y))
    (sheafificationW X)
    (Scheme.Modules.pullback f) G
  exact {
    toMonoidal := Scheme.Modules.pullbackMonoidal f
    braided M N := Functor.LaxBraided.braided (F := Scheme.Modules.pullback f) M N }

/-- The braiding proof keeps the exact native pullback monoidal structure. -/
theorem pullbackBraided_toMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackBraided f).toMonoidal = Scheme.Modules.pullbackMonoidal f := rfl

end EnvelopeProperty.SchemePullbackBraided
